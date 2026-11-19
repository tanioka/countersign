"""Sign インタープリタ(Python) v3

根拠: operator_table.md(優先順位・Unit 規則)、reference.md、function_guide.md、
      pattern_guide.md、list_cheat_sheet.md、string_and_comment.md
使い方: python sign_interp.py [file.sn]   (引数なしで REPL)

実装範囲: 全演算子の優先順位、余積の解決(construct/unshift/concat/apply/compose)、
  Unit 規則(零射・恒等射・短絡)、完全性公理、ポイントフリー([+] [* 2,] [!_] [_!])、
  穴 _ による部分適用、括り仮引数 [x ~xs]、字下げの match_case、get(' @ と ~ の鍵)、デフォルト引数ブロック、構造体。
未実装: # $ の記憶操作(アドレス型)、@ の import、
  型の静的パス、~+ ~- などの数列範囲、字下げ構造体。(NotImplementedError で明示)
"""
import math
import struct
import os, time
import re
import sys

# ============================== 値 ==============================
class _Unit:
    def __repr__(self): return "__"
UNIT = _Unit()
class _Absorbed(_Unit):                        # R62: 関数を指す番地を当てた値の演算子(と番地と数の混ぜ)の答えの `!_`。外の値の演算子と `==`・`!==` は運び(何段でも `!_`)、ほかの所は計算の `!_` と同じ
    def __repr__(self): return "__"
ABS = _Absorbed()

class _Id:                                   # !__ : 評価予定が確定した非Unitの恒等射
    def __repr__(self): return "<Id>"
ID = _Id()

class Char(str): pass
class WInt(int):
    """幅つきの番地 `1x…` `2x…` `4x…` `8x…`(value_representation.md §5)。幅(byte)は w。算術に使うと幅は落ちて普通の Int になる
    (「幅はその 1 回の読み書きに効く」§5.7)【実装の決め】。"""
    w = 0
    def _keep(self, r):
        if r is NotImplemented or isinstance(r, bool): return r
        x = WInt(r); x.w = self.w; return x
    def __add__(self, o): return self._keep(int.__add__(self, o)) if type(o) is int else int.__add__(self, o)
    def __radd__(self, o): return self._keep(int.__radd__(self, o)) if type(o) is int else int.__radd__(self, o)
    def __sub__(self, o): return self._keep(int.__sub__(self, o)) if type(o) is int else int.__sub__(self, o)
WIDTHS = (1, 2, 4, 8)
class Addr(int): pass                                   # Address 型の値(0x…)。型は左辺の域を選ぶ(integer_overflow.md §1.1・operator_table.md の爆発律の欄)。数としては int と同じ
UMASK = (1 << 64) - 1
class UInt(int): pass                                    # UInt 型の値(0r…・0b…)。環 ℤ/2^64ℤ で回る(integer_overflow.md §1)。ビットマスクで済むので速い
ADDR_END = 1 << 64                                       # 番地の域は 0 以上 2^64 未満。0x8000000000000000 は niche(__)で番地になりえない
def mk_addr(v):
    return Addr(v) if (0 <= v < ADDR_END and v != 0x8000000000000000) else UNIT
class Stream(list): pass
class WLen(list): pass                       # R91: 書いた時点で長さの分かる List(書き並べた行・字面・括った物・積)。足りない後ろの名前は木の段でも _
F32 = [False]                                  # --check-f32 : Vector のレーンを 32 ビット(IEEE 754 binary32)に丸める。既定は Python の 64 ビットのまま
def f32(x):
    try: return struct.unpack("<f", struct.pack("<f", x))[0]
    except OverflowError: return math.copysign(float("inf"), x)
def f32_repr(x):                               # binary32 として読み戻せる最短の十進表記
    if x != x or x in (float("inf"), float("-inf")): return repr(x)
    for p_ in range(1, 10):
        t = "%.*g" % (p_, x)
        if f32(float(t)) == x: return repr(float(t))
    return repr(x)
def _float_lit(m):
    """Float の字面(`1.5`、負号つきの `-1.5`)の値。そうでなければ None。"""
    if m[0] == "lit" and isinstance(m[1], float): return m[1]
    if m[0] == "neg" and len(m) == 2 and m[1][0] == "lit" and isinstance(m[1][1], float): return -m[1][1]
    return None

class Vec(tuple):
    def __new__(cls, it=()):
        t = tuple(it)
        return tuple.__new__(cls, tuple(f32(x) if isinstance(x, float) else x for x in t) if F32[0] else t)                       # Vector: 4 レーンの Float(SIMD)。リストではない
LAYER = None                                   # --layer N。未指定なら検査しない。Vector は layer >= 3                      # 後置 ~ で展開した列
class Open(list): pass                        # 括っていない並置の途中経過(次の項で伸びる)。縮約が終われば閉じた器になる
class Struct(dict): pass                      # 名前 → 値 の有限写像(宣言順は観測できない)
class SpreadStruct(Struct): pass              # 後置 ~ で展開した構造体(結合の合図)
class MergedStruct(SpreadStruct): pass     # 撒いた構造体どうしを結合した途中の値(3つ以上の結合が続けて繋がる。並びが閉じたら Struct になる)
_REPR_BUSY = set()
def _rec_repr(self):                              # dataclass の __repr__ と同じ形(入れ子が自分に戻るときは ...)
    k = id(self)
    if k in _REPR_BUSY: return "..."
    _REPR_BUSY.add(k)
    try: return "%s(%s)" % (type(self).__name__, ", ".join("%s=%r" % (f, getattr(self, f)) for f in self._FIELDS))
    finally: _REPR_BUSY.discard(k)
class Ref:                                    # $Lambda : Lambda を Atom へ降格した参照
    _FIELDS = ('value',); __repr__ = _rec_repr
    def __init__(self, value): self.value = value

class VarRef:                                 # $x : 変数のスロット(場所)。@ で読み、# で書く
    _FIELDS = ('env', 'name'); __repr__ = _rec_repr
    def __init__(self, env, name): self.env = env; self.name = name

class LaneRef:                                # $v + 4k : Vector 変数の第 k レーン(4 byte 刻み)の番地
    _FIELDS = ('var', 'lane'); __repr__ = _rec_repr
    def __init__(self, var, lane): self.var = var; self.lane = lane

class Lift:                                   # R99: 先の種類が書いた所で分からない持ち上げ(形の綴り `$?`)。開いても先を読まず、値の演算子の被演算子は level-mismatch(R99)、撒けば G20
    _FIELDS = (); __repr__ = _rec_repr

class Closure:
    _FIELDS = ('params', 'body', 'env', 'args', 'native', 'variadic', 'arity', 'dead', 'lo', 'parts', 'nofold', 'acc', 'pf', 'hof', 'alias', 'dop', 'pd', 'ru',); __repr__ = _rec_repr
    def __init__(self, params=None, body=None, env=None, args=None, native=None, variadic=False, arity=0, dead=False, lo=False, parts=None, nofold=False, acc=None, pf=False, hof=0, alias=False, dop=False, pd=False, ru=False):
        self.params = params                       # [("name", n) | ("destr", [names], rest)]
        self.body = body
        self.env = env
        self.args = [] if args is None else args
        self.native = native                       # 固定: native(*args) / 可変長: native(list)
        self.variadic = variadic
        self.arity = arity
        self.dead = dead                       # Unit を受けた呼び出し(飽和すると __)
        self.lo = lo                       # R59: 定義の中で余る関数があった名前(`$名前` は G20)
        self.parts = parts                       # 合成の段の並び(R51: 名前にした合成も、流れは段に開いて合成全体で受ける)
        self.nofold = nofold                       # 畳まない2項の点なし([<<] [>>] [!=] [!==]): 撒いた流れは G19(R51)
        self.acc = acc                       # --opt: アキュムレータ導入(sign_pe)。(隠れた累積版の関数名, 単位元)
        self.pf = pf                       # ポイントフリー記述([+] [* 2,] ...): 逆適用の対象外
        self.hof = hof                       # R138 holeOf: 既定値のある関数から作った穴の関数の穴の数(穴の口の `_` は値の口で消え、穴を全部埋めた後ろは G5)
        self.alias = alias                       # 別名(al : inc)・括った関数([inc])。逆適用の右にできない(G8、M25)
        self.dop = dop                       # R59: `$` で物にして `@` で開いた括りの関数(呼んだ実体の余りは G20)
        self.pd = pd                       # R107: 既定値の口だけが開いた部分適用(評価する所で既定値で埋まる。それ以外では部分適用のまま運ばれる)
        self.ru = ru                       # R65: 実行時に来た `_` が並びの単位として消え、口を開けたまま残った関数(値の演算子・条件では `_`)

class SignError(Exception): pass
# 門ごとの修正案。(メッセージの一部, 案)の順に先に合ったものを付ける。--strict の断りに「→ 修正案」として添える
FIXES = [
    ("G22: 既定値が `!_`", "既定値を付けずに `y`(値の口)か `[y]`(参照の口)と書く。既定値を使いたいなら、`!_` と分かる値でなく実際の値を書く"),
    ("G22: 既定値に `_`", "既定値を付けずに `y`(値の口)か `[y]`(参照の口)と書く。既定値を使いたいなら `_` でなく実際の値を書く"),
    ("G22:", "残りを受けるのは括りの中だけ: `[x ~xs]`。括りの外の `~xs`・残りの既定値は書かない"),
    ("G20:", "`$` は1つの関数にだけ付ける(`$inc`・`$[x ? x + 1]`・`$!_`)。関数を指す番地を受けた名前は、`$` を付けずにそのまま渡す(`map f t`)。`$` が受けるのは関数だけで、値の名前に付けた `$vs` は `!_` になります。データの番地は `0x…` で書きます(R99・R62)"),
    ("前置 @ は並びの頭", "括って `(@x)` と書く。例: `line @tx y` → `line (@tx) y`、`dx @th` → `dx (@th)`、`@a + 1` はそのままでよい(頭だから)"),
    ("前置 @ の右に関数", "読んだ結果を先に名前へ受けるか、`(@f)` と括って値として渡す。関数を呼ぶなら `f` を直に書く"),
    ("G1:", "並びの頭に値を置かない、または括って `(…)` と書く"),
    ("G2:", "取りかけの関数を括る。`f2 1 g 2` → `(f2 1) (g 2)`"),
    ("G3:", "`,` の左右を括る。`f 1, 2` → `(f 1), 2`"),
    ("G4:", "`~` の項を1つにする、または括る。`~1 2 3` → `~(1 2 3)`"),
    ("G5: 括りの関数", "括りの関数には `!_` を渡さず、`_` を使わない形に書き替える(別名の関数を用意して呼ぶ)"),
    ("G5: アリティ", "点なしの代わりに名前のある関数を定義して渡す(`[+ 1]` → `inc : x ? x + 1`)"),
    ("G5: 末尾の _", "末尾の `_` を外すか、`_` を別の位置へ移して終わりを明示する(括って `(… _)`)"),
    ("G5:", "`_` を外すか、関数に名前を付けて引数を並べて書く"),
    ("G7: !_ は中置", "穴は関数の実引数の位置にだけ置く。`!_ + 1` → `[+ 1]` か `x ? x + 1`"),
    ("G7: !_ は関数の実引数", "`!_` は `add !_ 2` のように関数の実引数にだけ置く。単独なら `[!_]` か名前付きの関数にする"),
    ("G7: !_ のある並び", "末尾の `_` を外す(穴 `!_` と終わりの印は同居できない)"),
    ("G7: 関数は算術", "関数を呼んで値にしてから演算する。`inc + 1` → `(inc 5) + 1` のように引数を渡す"),
    ("G7: 関数を含む器", "`~` の前に値だけの器にする。関数は `$` で包んで入れるか、別に名前を付ける"),
    ("G7: 関数に", "関数を呼んで値にしてから使う。`-inc 5` → `-(inc 5)`、`|inc| 5` → `|inc 5|`"),
    ("G7: 前置・後置の点なし", "`[-_,]` などの代わりに `x ? -x` のような名前付きの関数を書く"),
    ("G7: [~_]", "`x ? ~x` のような名前付きの関数を書く"),
    ("G7:", "関数を名前付きにして、実引数の位置に並べる"),
    ("G13:", "穴 `!_` を前から数えた個数の中に置く。`inc 5 !_` → `inc !_ 5` か `inc 5`"),
    ("G15:", "既定値のある口には `_`(既定値を使う)でなく、穴 `!_` を書く。`gd _ xs` → `gd !_ xs`"),
]
class Gate(SignError):                          # 名指しで断る形(coproduct_spec.md §6.2 の門)
    def __str__(self):
        m = super().__str__()
        for key, fix in FIXES:
            if key in m: return f"{m}\n  → 修正案: {fix}"
        return m

# alpha1 で追加された門(G1 G3 G4 G6 G8 G9 G10 G12 と、逆適用・既定値まわりの G5 G15)。旧 alpha のソース(自己ホストの
# parser.sn・lower.sn など)はこれらに当たる形を使っているので、既定では断らない。--strict か SIGN_STRICT=1 で断る。
STRICT_GATES = os.environ.get("SIGN_STRICT") == "1"
POS = {}                                       # 構文木の節 id → (ファイル, 行, 桁)。エラーの場所を出すための横置きの表
POS_KEEP = []                                  # POS に入れた節を生かしておく(捨てた木の id が別の節に使い回されて、行が食い違うのを防ぐ)
SRC_LINES = {}                                 # ファイル → 原文の行(エラーに該当行を添える)
PARSE_FILE = None

def locate(e, node):                           # 例外に、最も内側の節の場所を付ける(すでにあれば何もしない)
    if getattr(e, "loc", None) is None:
        p = POS.get(id(node)) if node is not None else None
        if p: e.loc = p
    return e

LEFTOVER_MSG = "値の後ろの関数が実引数を受けないまま残り、_ になって消えます(`5 inc` は 5)。当てるつもりなら、実引数を関数の後ろに書きます(逆適用は廃止、R47)"
WARNINGS = []                                  # 警告(--strict): (種類, 文面)。実行の終わりに stderr へ出す
LEFTOVERS = [0]                                # 余ったラムダを見つけた回数(R59: `$[…]` の中で増えたら G20)
CURLINE = [None]                               # 今走らせている行(元のソースの行。R127: 知らせに行を持たせる)
WARN_LINES = {}                                # (種類, 文面) → 最初に知らせた行
def warn(kind, msg, operand=False):
    if STRICT_GATES and kind == "leftover-lambda" and not operand: LEFTOVERS[0] += 1      # R59: 値の上に積まれて余る関数だけを数える(演算子の被演算子の余りは数えない)
    if STRICT_GATES and (kind, msg) not in WARNINGS:
        WARNINGS.append((kind, msg))               # 同じ知らせは1回
        WARN_LINES[(kind, msg)] = CURLINE[0]

INFO_KINDS = {"bare-function-return", "resource-depth", "zero-division", "int-overflow", "no-operation"}           # 警告(warning)でなく知らせ(information)で出す種類
BARE_RETURN_MSG = "本体の返す所に裸の関数が残り、_ を返します(R125)。関数を返すなら `$` を付けて持ち上げます(`$[+ m]`)、入れ子の `?` なら仮引数を並べます(`x y ? x + y`)"
def info(kind, msg):
    INFO_KINDS.add(kind); warn(kind, msg)

UNDEF_MSG = "定義が無い名前は `_` で、使う所で読みます(値の口では書いた `_` と同じ、参照の口では空の器。§4 R21・R111)"
def undef_note(env, nm):
    """R21・R111・R128: 定義の無い名前を使ったら information `undefined-name`(断らない。値は `_`)。書いた `x : _` の x も、定義が無いのと同じ(R113)"""
    if nm == "__" or nm in BUILTINS or env.owner(nm) is not None: return
    if STRICT_GATES: return                                     # R21(2026-11-18 版): strict は読む段の warning name-undefined だけ(static_undefined)
    info("undefined-name", f"`{nm}`: " + UNDEF_MSG)
def static_undefined(nodes, env):
    """R21・R91(--strict): 読む段で、書かれた名前のうち定義の無い物すべてに information `undefined-name`(実行で通らない枝の名前も)。
    取り込みのある範囲(`f@~`)は名前の先が分からないので出さない。裸の名前の鍵(`s'a`・`a@s`・欄の名前)は名前として引かない。
    括りの仮引数を持つ関数の本体は、呼ばれるまで読まない(R25)。名前の有無は、ファイル全体の定義・欄・仮引数の名前の和で見る(出しすぎないための広めの見立て)。"""
    declared, uses = set(), []
    def has_spread(n):
        if isinstance(n, (list, tuple)):
            if isinstance(n, tuple) and n and n[0] == "importspread": return True
            return any(has_spread(c) for c in n)
        return False
    def walk(n, read):
        if isinstance(n, list):
            for c in n: walk(c, read)
            return
        if not isinstance(n, tuple) or not n: return
        k = n[0]
        if not isinstance(k, str):                                  # 枝の行 (条件, 値) の組。条件の名前も引く(R21: `pr : x ?` ⏎ `⇥y : x + 1` は @2)
            for c in n: walk(c, read)
            return
        if k == "id":
            if read: uses.append((n[1], POS.get(id(n))))
            return
        if k == "def":
            declared.add(n[1]); walk(n[2], read); return
        if k == "lam":
            bracket = False
            for sp in n[1]:
                if sp[0] == "name": declared.add(sp[1])
                elif sp[0] == "destr":
                    bracket = True; declared.update(sp[1]); declared.update(sp[4] if len(sp) > 4 else ()) 
                    if sp[2]: declared.add(sp[2])
                    declared.update(sp[3] if isinstance(sp[3], dict) else ())
                    for d_ in (sp[3].values() if isinstance(sp[3], dict) else ()): walk(d_, read)
            walk(n[2], read); return                                  # R21: 括りの関数の本体も、呼ばなくても名前の表を見る
        if k in ("struct", "fieldblock"):
            for key, v in n[1]:
                declared.add(key); walk(v, read)
            if k == "fieldblock": walk(n[2], read)
            return
        if k == "bin" and len(n) > 3 and n[1] in ("'", "@"):
            key, cont = (n[3], n[2]) if n[1] == "'" else (n[2], n[3])
            if not (isinstance(key, tuple) and key and key[0] == "id"): walk(key, read)
            walk(cont, read); return
        for c in n[1:]:
            if isinstance(c, (list, tuple)): walk(c, read)
    if has_spread(nodes): return
    walk(nodes, True)
    for nm, p_ in uses:
        if nm in declared: continue
        if STRICT_GATES and nm not in BUILTINS and nm not in ("__", "_") and env.owner(nm) is None:        # R21(2026-11-18 版): 未定義の名前は `!_` と分かる値。断らず warning name-undefined(書いた所ごとに1つ。呼ばない本体でも)
            old_ = CURLINE[0]
            if p_: CURLINE[0] = p_[1]
            try: warn("name-undefined", f"`{nm}`: 見える範囲に定義の無い名前は `!_` と分かる値で、並びの項としては消えます(R21)。名前の書き間違いなら直します")
            finally: CURLINE[0] = old_
            continue
        if nm in ("__", "_"): continue
        old_ = CURLINE[0]
        if p_: CURLINE[0] = p_[1]                              # R127(寄せ5): 最初に当たった、その名前を書いた行
        try: undef_note(env, nm)
        finally: CURLINE[0] = old_
def _param_names_of(sp):
    if sp[0] == "name": return [sp[1]]
    return list(sp[1]) + list(sp[4] if len(sp) > 4 else []) + ([sp[2]] if sp[2] else [])
def static_shadow(nodes):
    """R133(--strict): 仮引数が、ファイルの定義か外の関数の仮引数と同じ名前なら、仮引数が隠す(内側が勝つ)。断らずに information `name-shadow`。
    読む段の知らせなので、呼ばれない本体・入れ子の関数・既定値の中の関数でも出す。隠す名前1つにつき1つ。両方を隠すなら近い方(外の関数の仮引数)を名指す。
    `x : _`(書いた `_` 1つの定義)は表に入らないので隠す物が無い(R113)。"""
    filedefs = set()
    for n in nodes:
        d = n[1] if n[0] == "export" else n
        if d[0] == "def" and d[2] != ("hole",): filedefs.add(d[1])
    def say(nm, outer, node):
        what = f"外の関数の仮引数 `{nm}`" if outer else f"ファイルの定義 `{nm}`"
        p_ = POS.get(id(node))
        old = CURLINE[0]
        if p_: CURLINE[0] = p_[1]
        try: info("name-shadow", f"仮引数 `{nm}` は{what}を隠します。この関数の中の `{nm}` は仮引数です(内側が勝つ。§4 R133)。")
        finally: CURLINE[0] = old
    def walk(n, scope):
        if isinstance(n, list):
            for c in n: walk(c, scope)
            return
        if not isinstance(n, tuple) or not n: return
        if not isinstance(n[0], str):                           # 印の無い組(`(キー, 値)`・`(条件, 値)`)は、先頭も見る
            for c in n: walk(c, scope)
            return
        if n[0] == "lam":
            seen = set(); inner = set(scope)
            for sp in n[1]:
                for nm in _param_names_of(sp):
                    if nm in seen: continue                     # 同じ関数の仮引数どうしの同名は name-duplicate(別の門)
                    seen.add(nm)
                    if nm in scope: say(nm, True, n)
                    elif nm in filedefs: say(nm, False, n)
                inner |= set(_param_names_of(sp))
                dflt = sp[2] if sp[0] == "name" else (sp[3].values() if len(sp) > 3 and isinstance(sp[3], dict) else ())
                if sp[0] == "name" and dflt is not None: walk(dflt, inner)
                elif sp[0] != "name": walk(list(dflt), inner)
            walk(n[2], inner); return
        for c in n[1:]:
            if isinstance(c, (list, tuple)): walk(c, scope)
    walk(nodes, set())
def static_param_dup(nodes):
    """R133・P2(--strict): 同じ関数の仮引数どうしの同名は name-duplicate でファイルごと断る(括りの中・残り・仮引数のブロックの行・既定値の中の関数も)。
    断りの順 4: `?` ごとに木の順(外の関数の `?` を先に全部、その既定値の中の関数をあと)。深さ→行の順で最初の物を出す。"""
    found = []
    def walk(n, depth):
        if isinstance(n, list):
            for c in n: walk(c, depth)
            return
        if not isinstance(n, tuple) or not n: return
        if not isinstance(n[0], str):                           # 印の無い組(`(キー, 値)`・`(条件, 値)`)は、先頭も見る
            for c in n: walk(c, depth)
            return
        if n[0] == "lam":
            seen = set()
            for sp in n[1]:
                for nm in _param_names_of(sp):
                    if nm in seen:
                        e = locate(Gate(f"name-duplicate: 仮引数 {nm} が同じ関数で2回書かれています(2つ目を断ります。P2。§4 R133)"), n); e.tdepth = depth
                        found.append((depth, (getattr(e, "loc", None) or (0, 10**9))[1], len(found), e)); break
                    seen.add(nm)
        for c in (n[2:] if n[0] == "lam" else n[1:]):         # lam の仮引数の既定値は、下で深さを1つ足して見る
            if isinstance(c, (list, tuple)): walk(c, depth)
        if n[0] == "lam":
            for sp in n[1]:
                d = sp[2] if sp[0] == "name" else None
                if d is not None: walk(d, depth + 1)
                elif sp[0] != "name" and len(sp) > 3 and isinstance(sp[3], dict): walk(list(sp[3].values()), depth + 1)
    walk(nodes, 0)
    if found: raise min(found, key=lambda t: t[:3])[3]
def strict_gate(msg, node=None):
    if STRICT_GATES:
        e = locate(Gate(msg), node)
        if getattr(e, "loc", None) is None and CURLINE[0] and PARSE_FILE is not None: e.loc = (PARSE_FILE, CURLINE[0], 1)      # R127(寄せ5): 節の場所が無い門は、いま走らせている本体の書いた行
        raise e

class Env:
    def __init__(self, parent=None):
        self.vars, self.parent = {}, parent
        self.exports = {}                      # 根(ファイルのスコープ)だけが使う: #name の束縛
    def get(self, name):
        e = self; last = self
        while e:
            if name in e.vars: return e.vars[name]
            last = e; e = e.parent
        pend = last.__dict__.get("pending")
        if pend and name in pend: return force_pending(last, name)
        run_ = last.__dict__.get("running")
        if run_ and name in run_: idle_stop(f"値の定義 {name} が、自分の値を求める途中でもう一度引かれました(値の定義の輪)")      # V9: 先に引かれた値の定義は、その時に1回走る
        return BUILTINS.get(name, UNIT)        # 未定義の識別子はすべて __ に収束する(unit.md §0.1)。__ もその1つ
    def set(self, name, v): self.vars[name] = v
    def owner(self, name):                     # name を持つスコープ(無ければ None)
        e = self
        while e:
            if name in e.vars: return e
            e = e.parent
        return None

class FieldEnv(Env):
    """P2・R133(--strict): 括りと構造体のブロックの欄の範囲。欄は同じ範囲の中から順序に依らず引け(引かれた時に1回読む)、外の同じ名前を隠す。
    欄どうしの値の輪は name-cycle で止める"""
    def __init__(self, parent, fields):
        super().__init__(parent); self.fnodes = dict(fields); self.busy = set()
    def force(self, name):
        if name in self.busy:
            raise Gate(f"name-cycle: 欄 {name} の値を求める途中で、同じ括りの欄がもう一度 {name} を引きました(欄どうしの値の輪。P2。§4 R133)")
        self.busy.add(name)
        try: v = ev_place(self.fnodes[name], self, rhs=True)
        finally: self.busy.discard(name)
        self.vars[name] = v
        return v
    def get(self, name):
        if name in self.vars: return self.vars[name]
        if name in self.fnodes: return self.force(name)
        return super().get(name)
    def owner(self, name):
        if name in self.fnodes and name not in self.vars: self.force(name)
        return super().owner(name)

def is_unit(v):
    if v is UNIT or v is ABS: return True
    t = type(v)
    if t is int or t is float or t is str: return False                    # よくある値は早く抜ける
    return (v is UNIT or (isinstance(v, (list, Struct)) and len(v) == 0)
            or (isinstance(v, Closure) and v.dead))
def is_num(v): return isinstance(v, (int, float)) and not isinstance(v, bool)
def _cp(f, **kw):                              # dataclasses.replace より速い複製(Closure は欄の値をそのまま写すだけ)
    c = object.__new__(Closure)
    c.__dict__.update(f.__dict__)
    c.__dict__.update(kw)
    return c
def parts_of(f):                               # 合成なら段の並び、そうでなければ自分だけ
    return f.parts if f.parts and not f.args else (f,)
def arity(f): return len(f.params) if f.params is not None else f.arity

def norm_hole(args):
    """R27(--strict): `||_||` の口に来た並び全体の長さ。1つだけ来た値は、その器の長さ(`||_|| xs` は `||xs||`)"""
    xs = [a for a in args if not is_unit(a)]
    if len(xs) == 1:
        x = xs[0]
        return len(x) if isinstance(x, (list, str, Vec, Struct)) else 1
    return len(xs)
def show(v):
    if STRICT_GATES and v is ID: return "_"                                   # --strict の綴り: 恒等射は `_`
    if v is UNIT or v is ABS: return "!_" if STRICT_GATES else "__"             # R138: strict の void は `!_`(計算の答えとしてだけ生まれる)
    if STRICT_GATES and is_addr(v): return addr_hex(v)                        # R62: 番地は `0x…` で見せる
    if isinstance(v, OpenRange): return repr(v)
    if isinstance(v, Lift): return "$?"
    if isinstance(v, Vec): return "[" + " ".join((f32_repr(float(x)) if F32[0] else repr(float(x))) for x in v) + "]"
    if isinstance(v, Char): return "\\" + v
    if isinstance(v, str): return f"`{v}`"
    if isinstance(v, Stream): return "~" + show(list(v))
    if isinstance(v, Struct): return "[" + ", ".join(f"{k}: {show(x)}" for k, x in v.items()) + "]"
    if isinstance(v, list): return "[" + ", ".join(show(x) for x in v) + "]"
    if isinstance(v, Closure):
        return ("!_" if STRICT_GATES else "__") if v.dead else ("<fn *>" if v.variadic else f"<fn/{rem(v)}>")
    if isinstance(v, Ref): return "$" + show(v.value)
    if isinstance(v, VarRef): return "$" + v.name
    return str(v)

# ============================== 余積 ==============================
def slot_optional(sp): return (sp[0] == "name" and sp[2] is not None) or (sp[0] == "destr" and len(sp) > 3 and bool(sp[3]))
def has_defaults(f):
    return f.params is not None and any(slot_optional(sp) for sp in f.params)

def required(f):                               # 最後の必須仮引数までの個数(デフォルト引数はアリティ計算から除外)
    if f.params is None: return f.arity
    n = 0
    for i, sp in enumerate(f.params):
        if not slot_optional(sp): n = i + 1
    return n

def rem(f): return required(f) - len(f.args)

def native_fixed(fn, n): return Closure(arity=n, native=fn)
def _vec4(a, b, c, d):                          # 4 つの Float を並べた Vector(Float でなければ __)
    xs = (a, b, c, d)
    return Vec(xs) if all(isinstance(x, float) for x in xs) else UNIT
BUILTINS = {"vec4": native_fixed(_vec4, 4)}      # 利用者の定義が優先する
def native_var(fn): return Closure(native=fn, variadic=True)

class TailCall:                                # 末尾呼び出し: 呼び出しの入れ子を作らず、run_fixed の輪に戻して続ける
    __slots__ = ("g",)
    def __init__(self, g): self.g = g

FAST = [os.environ.get("SIGN_NO_FAST") != "1"]               # 整数の速い道・輪(SIGN_NO_FAST=1 で切って比べられる)
ACC = {}                                        # 構文木の lam の節 id → (隠れた累積版の名前, 単位元)。sign_pe のアキュムレータ導入が置く
TCO = os.environ.get("SIGN_NO_TCO") != "1"      # 末尾再帰の最適化(SIGN_NO_TCO=1 で切って比べられる)

# ---- 整数だけの純粋な関数(fib・アッカーマン・gcd を呼ぶ lcm・相互再帰など)を Python の関数にして走らせる速い道(仕様に無い最適化。既定の道のみ、--strict では使わない) ----
#      対象: 仮引数が名前だけ(既定値・可変長なし)で、本体が「整数の比べ : 式」の行と既定の行だけ(または式 1 つ)の関数。
#      式は 整数・仮引数・外の整数の名前・ + - * / %・同じ条件を満たす別の関数(自分・相互再帰を含む)への呼び出し だけ。
#      この範囲は副作用が無いので、0 で割るなど決まらないことがあれば捨てて、普通の道で最初からやり直す(結果は変わらない)。SIGN_NO_PURE=1 で切って比べられる
PURE = [os.environ.get("SIGN_NO_PURE") != "1"]
PAR = [None]                                  # --par: 純粋な関数の並列実行(sign_par.Par)。None なら使わない
PURE_PLANS = {}
PURE_DEBUG = os.environ.get("SIGN_PURE_DEBUG") == "1"        # 速い道に乗らなかった関数を標準エラーに知らせる(調べる用)
PURE_TRIES = {}
PURE_WHY = {}
class _PureBail(Exception): pass
def _psdiv(a, b):
    if b == 0: raise _PureBail()
    q = abs(a) // abs(b)
    return q if (a < 0) == (b < 0) else -q
def _psmod(a, b):
    if b == 0: raise _PureBail()
    r = abs(a) % abs(b)
    return r if a >= 0 else -r
_PURE_BIN = {"+": "+", "-": "-", "*": "*", "/": "_psdiv", "%": "_psmod", "&&": "&", "||": "|", ";;": "^", "<<": "_psshl", ">>": "_psshr"}
_PURE_OV = {}                                    # 速い道の書き込みの差分表(番地 → 値)。最後まで成功したときだけ MEMORY へ反映し、途中で決まらなければ捨てる
def _allint(v):
    for x in v:
        if type(x) is not int: return False
    return True
def _allgen(v):                                  # 整数・小数・文字だけ(文字が混ざる List の入口の判定)
    for x in v:
        t = type(x)
        if t is not int and t is not float and t is not Char: return False
    return True
def _allstr(v):                                  # 空でない String だけ(Stringの List の入口の判定)
    for x in v:
        if type(x) is not str or not x: return False
    return True
def _allnum(v):                                  # 整数と小数だけ(bool・文字・文字列・入れ子の List は含まない)
    for x in v:
        t = type(x)
        if t is not int and t is not float: return False
    return True
def _psrd(a):                                    # `@a` を整数として読む(装置・未書き込み・整数でない値は決めずに普通の道へ)
    if BOUNDS[0]: raise _PureBail()               # --check-bounds: 番地の検査は普通の道で
    v = _PURE_OV.get(a)
    if v is None:
        if a == UART or device_at(a) is not None: raise _PureBail()
        v = MEMORY.get(a)
    if type(v) is not int: raise _PureBail()
    return v
def _psrdx(a):                                   # `@a` を整数か(空でない)整数だけの List として読む
    if BOUNDS[0]: raise _PureBail()
    v = _PURE_OV.get(a)
    if v is None:
        if a == UART or device_at(a) is not None: raise _PureBail()
        v = MEMORY.get(a)
    t = type(v)
    if t is int: return v
    if t is list and v and _allint(v): return v
    raise _PureBail()
_PURE_LOG = []                                   # 装置への書き込みの記録(装置, 装置の中の位置, 値)。最後まで成功したときだけ順に再生する
def _pswr(a, v):                                 # `a # v`: 普通のメモリへ書く(差分表に)。番地を返す。UART・読み書きを任せられない装置は決めずに普通の道へ
    if a == UART or BOUNDS[0]: raise _PureBail()
    d = device_at(a)
    if d is None: _PURE_OV[a] = v; return a
    if type(v) is not int or not getattr(d, "pure_write_ok", False) or not d.pure_write_safe(a - d.base, v): raise _PureBail()
    _PURE_LOG.append((d, a - d.base, v))         # 装置が申し出た書き込みだけ(描画装置の命令など)。装置の読みは今までどおり普通の道へ
    return a
def _pswrx(a, v):                                # 値が整数か List かまだ分からない `a # v`
    if type(a) is not int or (type(v) is not int and type(v) is not float and not (type(v) is list and v)): raise _PureBail()
    return _pswr(a, v)
def _pswc(a, v):                                 # 行の条件としての `a # v`: 書いて、成り立つ(番地は __ でない)
    _pswr(a, v); return True
def _pswcx(a, v):
    _pswrx(a, v); return True
def _psshl(a, b):
    if b < 0 or b > 100000: raise _PureBail()          # 負・巨大なシフトは決めずに普通の道へ(そちらの扱いに任せる)
    return a << b
def _psshr(a, b):
    if b < 0 or b > 100000: raise _PureBail()
    return a >> b
def _ci(x):                                      # 整数と決まっていない値を整数として使う所の検査
    if type(x) is not int: raise _PureBail()
    return x
def _cl(x):
    if type(x) is not list: raise _PureBail()
    return x
def _cd(x):                                      # 整数か小数(単位・List でない)として使う所の検査
    t = type(x)
    if t is not int and t is not float and t is not Char: raise _PureBail()          # 文字の世界では d は文字も含む(数だけの世界には文字は現れない)
    return x
def _pga(op, a, b):                              # 文字が混ざりうる世界の算術: 評価器と同じ arith に任せる。答えが __ や数・文字でない物(文字列など)なら普通の道へ
    ta = type(a); tb = type(b)
    if (ta is int or ta is float) and (tb is int or tb is float):
        _r = a + b if op == "+" else a - b if op == "-" else a * b if op == "*" else None
        if _r is not None:
            if STRICT_GATES and type(_r) is int and (_r > INT_MAX or _r < -INT_MAX): raise _PureBail()
            return _r
    r = arith(op, a, b); t = type(r)
    if t is not int and t is not float and t is not Char: raise _PureBail()
    return r
def _pddiv(a, b):                                # `/`(型が整数と決まっていない): 整数どうしは 0 へ丸める割り算、小数が混ざれば普通の割り算。0 で割るのは決めずに普通の道へ
    if type(a) is int and type(b) is int: return _psdiv(a, b)
    if b == 0: raise _PureBail()
    return a / b
def _pdmod(a, b):                                # `%`
    if type(a) is int and type(b) is int: return _psmod(a, b)
    if b == 0: raise _PureBail()
    return a % b
def _nn(x):                                      # 単位(None)を実引数・材料にしない(単位の実引数は呼び出しを殺す。普通の道に任せる)
    if x is None: raise _PureBail()
    return x
def _psix(l, k):                                 # `l ' k`(k は 0 以上で範囲内)
    if type(l) is not list or type(k) is not int or k < 0 or k >= len(l): raise _PureBail()
    return l[k]
def _psrest(l, k):                               # `l ' k~`(空になるときは __ なので普通の道へ)
    if type(l) is not list: raise _PureBail()
    r = l[k:]
    if not r: raise _PureBail()
    return r
def _psnormu(x):
    t = type(x)
    if x is None: return 0
    if t is list: return len(x)
    if t is int or t is float or t is Char: return 1
    raise _PureBail()
def _psnorm(x):                                  # `||x||`: List は長さ、整数・小数は 1
    t = type(x)
    if t is list: return len(x)
    if t is int or t is float or t is Char: return 1
    raise _PureBail()
def _psixs(s, k):                                # `s ' k`(String の k 番目。範囲外・負は決めずに普通の道へ)
    if type(s) is not str or type(k) is not int or k < 0 or k >= len(s): raise _PureBail()
    return Char(s[k])
def _psrests(s, k):                              # `s ' k~`(String の k 番目から後ろ。空になるときは __ なので普通の道へ)
    if type(s) is not str or type(k) is not int or k < 0: raise _PureBail()
    r = s[k:]
    if not r: raise _PureBail()
    return r
def _psexp(x):                                   # String の仮引数を Char の List に直す(List はそのまま)
    if type(x) is str: return [Char(c) for c in x]
    if type(x) is list: return x
    raise _PureBail()
def _psjoin(*xs):                                # 値の並びの結合: 単位は無かったことになる。2 つ以上あれば文字・String を 1 本の String に(1 つだけならそのまま)
    items = [x for x in xs if x is not None]
    if not items: return None
    if len(items) == 1: return items[0]
    for x in items:
        t = type(x)
        if t is not str and t is not Char: raise _PureBail()
    return "".join(items)
def _ns(x):
    if x is None: raise _PureBail()
    return x
def _psst(st, key, f):                           # `(S ' key~) ' f`: 鍵が無ければ __(None)
    v = st.get(key)
    return None if v is None else v[f]
def _psixS(l, b, k):                             # Stringの List の位置 b から数えて k 番目(範囲外・負は決めずに普通の道へ)
    if type(k) is not int or k < 0 or b + k >= len(l): raise _PureBail()
    return l[b + k]
def _pstxt(*xs):                                 # 文字・String だけの項を 1 本の String に(数が混ざれば普通の道へ)
    for x in xs:
        t = type(x)
        if t is not str and t is not Char: raise _PureBail()
    return "".join(xs)
def _psrz(p, o):                                 # Stringの List の位置 o からの残り(空なら __)。先頭からなら写さずに同じ list を渡す(Stringの List は書き換えない)
    return p if o == 0 and p else (p[o:] or None)
def _psrS(p, o):
    if o == 0 and p: return p
    r = p[o:]
    if not r: raise _PureBail()
    return r
def _nS(x):
    if x is None: raise _PureBail()
    return x
def _pbail():
    raise _PureBail()
_CHC = {}                                        # 1 文字の Char を作り直さずに使い回す(Char は不変)
def _mkc(c):
    r = _CHC[c] = Char(c)
    return r
def _psixsr(s, b, k):                            # 位置で読む残り(開始 b)の k 番目
    if type(s) is not str or type(k) is not int or k < 0 or b + k >= len(s): raise _PureBail()
    c = s[b + k]
    return _CHC.get(c) or _mkc(c)
def _psrestsr(s, b, k):                          # 位置で読む残り(開始 b)の k 番目から後ろ
    if type(s) is not str or type(k) is not int or k < 0: raise _PureBail()
    r = s[b + k:]
    if not r: raise _PureBail()
    return r
def _pscmps(op, a, b):                           # String(か 1 文字)どうしの比べ
    try: return a < b if op == "<" else a <= b if op == "<=" else a > b if op == ">" else a >= b if op == ">=" else a == b if (op == "=" or op == "==") else a != b
    except TypeError: raise _PureBail()
def _pscmpv(op, a, b):                           # 値としての比べ: 成り立てば左の値(value_spec V6。0・1 の例外なし)、外れれば __(None)
    ta = type(a); tb = type(b)
    if (ta is Char or tb is Char) and ta in (int, float, Char) and tb in (int, float, Char):
        try: ok = a < b if op == "<" else a <= b if op == "<=" else a > b if op == ">" else a >= b if op == ">=" else a == b if (op == "=" or op == "==") else a != b
        except TypeError: ok = False
        return (a if ok else None)
    if (ta is int or ta is float) and (tb is int or tb is float):
        ok = a < b if op == "<" else a <= b if op == "<=" else a > b if op == ">" else a >= b if op == ">=" else a == b if (op == "=" or op == "==") else a != b
        return (a if ok else None)
    if ta is list and tb is list and (op == "=" or op == "==" or op == "!="):
        return a if ((a == b) if op != "!=" else (a != b)) else None
    raise _PureBail()
def _pscmp(op, a, b):                            # 型が静的に決まらない比べ。整数どうし・List どうしの = だけ(ほかは普通の道へ)
    ta = type(a); tb = type(b)
    if (ta is str or tb is str) and (ta is str or ta is Char) and (tb is str or tb is Char): return _pscmps(op, a, b)
    if (ta is Char or tb is Char) and ta in (int, float, Char) and tb in (int, float, Char):
        try: return a < b if op == "<" else a <= b if op == "<=" else a > b if op == ">" else a >= b if op == ">=" else a == b if (op == "=" or op == "==") else a != b
        except TypeError: return False
    if (ta is int or ta is float) and (tb is int or tb is float):
        return a < b if op == "<" else a <= b if op == "<=" else a > b if op == ">" else a >= b if op == ">=" else a == b if (op == "=" or op == "==") else a != b
    if ta is list and tb is list and (op == "=" or op == "==" or op == "!="):
        return (a == b) if op != "!=" else (a != b)
    raise _PureBail()
_PURE_CMP = {"<": "<", "<=": "<=", ">": ">", ">=": ">=", "=": "==", "==": "==", "!=": "!="}
def _pa(v):                                       # 番地の域(0 以上 2^64 未満、0x8000000000000000 を除く)の外へ出たら、決めずに普通の道へ
    if 0 <= v < ADDR_END and v != 0x8000000000000000: return v
    raise _PureBail()
def _pxis(x):                                     # 番地か整数か実行時にしか決まらない値('X'): 番地なら True、整数なら False。__ や他の物は決めずに普通の道へ
    t = type(x)
    if t is Addr: return True
    if t is int: return False
    raise _PureBail()
def _pxi(x):                                      # 'X' を比べに使う: 番地も整数も大小は数のまま(番地の比べは整数の大小。域の規則は算術だけ)
    t = type(x)
    if t is Addr or t is int: return int(x)
    raise _PureBail()
def _pxbin(op, a, b):                             # 'X' の足し引き掛け: 左が番地なら番地の域(+ と - だけ。掛け算は無い射)、左が整数なら整数の域(右が番地でも整数)
    ta, tb = type(a), type(b)
    if (ta is not Addr and ta is not int) or (tb is not Addr and tb is not int): raise _PureBail()
    if ta is Addr:
        if op == "+": return Addr(_pa(a + b))
        if op == "-": return Addr(_pa(a - b))
        raise _PureBail()
    _r = a + b if op == "+" else (a - b if op == "-" else a * b)
    if STRICT_GATES and (_r > INT_MAX or _r < -INT_MAX): raise _PureBail()          # V5: Int の溢れは _(普通の道でやり直す)
    return _r
def _pidk(*xs):                                   # 速い道の輪が同じ状態へ戻ったかの鍵(整数などはそのまま、List は長さと同一性。その場で伸ばす List があるので値では比べない)
    return tuple((len(x), id(x)) if type(x) is list else x for x in xs)
_PURE_NS = {"_R256": range(256), "_pidk": _pidk, "_Addr": Addr, "_pxis": _pxis, "_pxi": _pxi, "_pxbin": _pxbin, "Char": Char, "_pa": _pa, "_pstxt": _pstxt, "_psrz": _psrz, "_psrS": _psrS, "_CHC": _CHC, "_mkc": _mkc, "_psst": _psst, "_psixS": _psixS, "_nS": _nS, "_psdiv": _psdiv, "_psmod": _psmod, "_psshl": _psshl, "_psshr": _psshr, "_psrd": _psrd, "_psrdx": _psrdx, "_pswr": _pswr, "_pswrx": _pswrx,
            "_pswc": _pswc, "_pswcx": _pswcx, "_ci": _ci, "_cl": _cl, "_cd": _cd, "_pga": _pga, "_pddiv": _pddiv, "_pdmod": _pdmod, "_nn": _nn, "_psix": _psix, "_psrest": _psrest, "_psixs": _psixs, "_ns": _ns, "_psixsr": _psixsr, "_psrestsr": _psrestsr, "_psjoin": _psjoin, "_ID": ID, "_psexp": _psexp, "_pbail": _pbail, "_psrests": _psrests, "_psnorm": _psnorm, "_psnormu": _psnormu, "_pscmp": _pscmp, "_pscmpv": _pscmpv, "_PureBail": _PureBail, "mk_addr": mk_addr}
def _pure_plain(f, full=False):                  # 仮引数が名前、または名前だけの括り(残り・既定値・後ろの名前なし)の普通の関数か(full: 実引数が全部そろった入口の関数でもよい。そうでなければ引数の溜まっていない関数だけ)
    if not (isinstance(f, Closure) and f.native is None and not f.variadic and f.params is not None and (full or not f.args) and not f.dead and not f.dop): return False
    seen = set()
    for sp in f.params:
        if sp[0] == "name" and sp[2] is None: ns_ = [sp[1]]
        elif sp[0] == "destr" and (sp[1] or sp[2]) and not (len(sp) > 3 and sp[3]) and not (len(sp) > 4 and sp[4]): ns_ = list(sp[1]) + ([sp[2]] if sp[2] else [])      # [a b]・[a ~r]・[~r](残りの名前つき)
        else: return False
        for x in ns_:
            if x in seen: return False
            seen.add(x)
    return True
_WIDE = ("d", "M", "x", "y")                   # 小数が混ざりうる型。d 整数か小数 / M 整数か小数だけの List / x 単位でない数か数の List / y x か単位
def _coerce(code, ty, want):                     # 型 ty の式 code を want(i 整数 / l 整数だけの List / d 整数か小数 / M 数の List / ? 単位でない整数か List / x 単位でない数か数の List)にする。できなければ None
    if want == "a" or ty == "a": return code if want == ty else None      # Addr の仮引数('a')は 'a' の所にだけ置ける。算術・返り値・他の型へは混ぜない(番地の域の規則を持ち込まないため)
    if want == "i": return code if ty == "i" else ("_ci(%s)" % code if ty in ("?", "u", "d", "x", "y") else None)
    if want == "l": return code if ty == "l" else ("_cl(%s)" % code if ty in ("?", "u") else None)
    if want == "d": return code if ty in ("i", "d") else ("_cd(%s)" % code if ty in ("?", "u", "x", "y") else None)
    if want == "M": return code if ty in ("l", "M") else ("_cl(%s)" % code if ty in ("?", "u", "x", "y") else None)
    if want == "s": return code if ty == "s" else ("_ns(%s)" % code if ty == "z" else None)      # 単位かもしれない String を実引数に: 単位なら呼び出しが死ぬ(決めずに普通の道へ)
    if want == "z": return code if ty in ("s", "z") else None
    if want == "S": return code if ty == "S" else (("_psrS(" + code[6:] if code.startswith("_psrz(") else "_nS(%s)" % code) if ty == "Z" else None)      # 空かもしれない Stringの List を実引数に: 空(単位)なら呼び出しが死ぬ(決めずに普通の道へ)
    if want == "Z": return code if ty in ("S", "Z") else None
    if want == "x": return code if ty in ("i", "l", "?", "d", "M", "x") else ("_nn(%s)" % code if ty in ("u", "y") else None)
    return code if ty in ("i", "l", "?") else ("_nn(%s)" % code if ty == "u" else None)
def _pure_expr(n, nd, nodes, index, depth, want=None):
    """(Python の式, 型)。型: 'i' 整数 / 'l' 整数だけの List / '?' 整数か List(単位でない) / 'u' 単位(None)かもしれない。作れなければ None。want='i' なら整数の読みを優先する。"""
    k = n[0]
    if k == "lit":
        v = n[1]
        if type(v) is Char:                                              # 文字(文字の世界だけ)
            if not nd["gw"] or len(n) != 2: return None
            cd = ("K%d_%d" % (nd["j"], len(nd["klists"])), "d"); nd["klists"].append(v); return cd
        if type(v) is str:                                               # String(文字の世界だけ。空は単位に近いので普通の道へ)
            if len(n) != 2: return None
            if not nd["gw"]: raise _NeedGW()
            if not v: return ("''", "z")                                 # 空の String(結合では無いのと同じ。単位ではない)
            cd = ("K%d_%d" % (nd["j"], len(nd["klists"])), "s"); nd["klists"].append(v); return cd
        if type(v) is float: return ("(%r)" % v, "d") if (len(n) == 2 and v - v == 0) else None       # 小数(inf・nan は除く)
        if type(v) is int and len(n) == 3 and n[2] == "Address":          # 0x… は Address 型の値: 域の中の字面だけ番地('a')として扱う(外は普通の道が __ にする)
            return ("(%d)" % v, "a") if (0 <= v < ADDR_END and v != 0x8000000000000000) else None
        return ("(%d)" % v, "i") if (type(v) is int and len(n) == 2) else None
    if k == "id":
        nm = n[1]
        vr = nd["vars"].get(nm)
        if vr is not None: return vr
        if nm == "__" and nm not in nd["offrest"] and nd["env"].get("__") is UNIT: return ("None", "u")      # 単位
        if nm in nd["offrest"]:                                          # 位置で読む残りを値として使う: その場で切り出す(空なら __ = None)
            pi, nb = nd["offrest"][nm]
            if nd["sg"][pi] == "s": return (("p%d[o%d:]" % (pi, pi), "s") if nb == 0 else ("(p%d[o%d + %d:] or None)" % (pi, pi, nb), "z"))
            if nd["sg"][pi] == "S": return ("_psrz(p%d, o%d + %d)" % (pi, pi, nb), "Z")
            return ("(p%d[o%d + %d:] or None)" % (pi, pi, nb), "y" if nd["sg"][pi] in ("M", "x", "y") else "u")
        for fn_, v, cd in nd["free"]:
            if fn_ == nm: return cd
        v = nd["env"].get(nm)
        if type(v) is int: cd = ("(%d)" % v, "i")
        elif type(v) is float and v - v == 0: cd = ("(%r)" % v, "d")
        elif type(v) is list and v and _allint(v):
            cd = ("K%d_%d" % (nd["j"], len(nd["klists"])), "l"); nd["klists"].append(v)
        elif type(v) is list and v and (_allgen(v) if nd["gw"] else _allnum(v)):
            cd = ("K%d_%d" % (nd["j"], len(nd["klists"])), "M"); nd["klists"].append(v)
        elif type(v) is Char and nd["gw"]:
            cd = ("K%d_%d" % (nd["j"], len(nd["klists"])), "d"); nd["klists"].append(v)
        elif type(v) is str and v and not nd["gw"]: raise _NeedGW()
        elif type(v) is str and v:
            cd = ("K%d_%d" % (nd["j"], len(nd["klists"])), "s"); nd["klists"].append(v)
        else: return None
        nd["free"].append((nm, v, cd)); return cd
    if k == "block":
        return None if isinstance(n[1], list) else _pure_expr(n[1], nd, nodes, index, depth, want)
    if k == "not" and n[1] == ("id", "__") and "__" not in nd["vars"] and nd["env"].get("__") is UNIT: return ("_ID", "k")      # `!__`(非単位の恒等射): 条件に使う印。型 k は呼び出しの条件(単位でないか)にだけ使える
    if k == "input":                             # @番地: 普通のメモリの値を読むだけ(装置・未書き込みは決めずに普通の道へ)
        a = _pure_expr(n[1], nd, nodes, index, depth, "i")
        if a and a[1] == "a": a = (a[0], "i")
        a = a and _coerce(a[0], a[1], "i")
        if a is None: return None
        return ("_psrd(%s)" % a, "i") if want == "i" else ("_psrdx(%s)" % a, "?")
    if k == "bin" and len(n) == 4 and n[1] == "#":      # 書き込み(左の番地を先に、右の値をあとに評価する)
        a = _pure_expr(n[2], nd, nodes, index, depth, "i")
        if a and a[1] == "a": a = (a[0], "i")
        a = a and _coerce(a[0], a[1], "i")
        if a is None: return None
        b = _pure_expr(n[3], nd, nodes, index, depth)
        if b is None: return None
        if b[1] == "i": return ("_pswr(%s, %s)" % (a, b[0]), "i")
        b = _coerce(b[0], b[1], "x" if b[1] in _WIDE else "?")
        if b is None: return None
        return ("_pswrx(%s, %s)" % (a, b), "i")
    if k == "bin" and len(n) == 4 and n[1] == "'" and n[2][0] == "id" and n[2][1] in nd["offrest"] and n[2][1] not in nd["vars"] and nd["sg"][nd["offrest"][n[2][1]][0]] == "s":      # String の残りを位置で読む: 切り出さずに添字で引く
        pi, nb = nd["offrest"][n[2][1]]
        kn = n[3]; rest = kn[0] == "post" and kn[1] == "~" and len(kn) == 3
        if rest:
            kn = kn[2]
            if kn[0] != "lit" or type(kn[1]) is not int or len(kn) != 2 or kn[1] < 0: return None
        if kn[0] in ("post", "input", "neg", "abs", "lift", "addr", "prod", "sec", "proc", "not"): return None
        kx = _pure_expr(kn, nd, nodes, index, depth, "i")
        kx = kx and _coerce(kx[0], kx[1], "i")
        if kx is None: return None
        return ("_psrestsr(p%d, o%d + %d, %s)" % (pi, pi, nb, kx), "s") if rest else ("_psixsr(p%d, o%d + %d, %s)" % (pi, pi, nb, kx), "d")
    if k == "bin" and len(n) == 4 and n[1] == "'" and n[2][0] == "id" and n[2][1] in nd["offrest"] and n[2][1] not in nd["vars"] and nd["sg"][nd["offrest"][n[2][1]][0]] == "S" and not (n[3][0] == "post" and n[3][1] == "~"):      # Stringの List の残りを位置で読む: 切り出さずに添字で引く
        pi, nb = nd["offrest"][n[2][1]]
        kn = n[3]
        if kn[0] in ("post", "input", "neg", "abs", "lift", "addr", "prod", "sec", "proc", "not"): return None
        kx = _pure_expr(kn, nd, nodes, index, depth, "i")
        kx = kx and _coerce(kx[0], kx[1], "i")
        if kx is None: return None
        return ("_psixS(p%d, o%d + %d, %s)" % (pi, pi, nb, kx), "s")
    if k == "bin" and len(n) == 4 and n[1] == "'" and n[3][0] == "id":      # 構造体を String の鍵で引き、その欄を読む: `(S ' key~) ' F`(S は外の構造体、欄 F は全部の鍵で整数)
        X_ = _strip_blk(n[2]); F_ = n[3][1]
        if X_[0] == "bin" and len(X_) == 4 and X_[1] == "'" and X_[2][0] == "id" and X_[3][0] == "post" and X_[3][1] == "~" and len(X_[3]) == 3:
            S_ = X_[2][1]
            st_ = nd["env"].get(S_) if (S_ not in nd["vars"] and S_ not in nd["offrest"] and F_ not in nd["vars"] and F_ not in nd["offrest"]) else None
            if isinstance(st_, Struct) and st_ and all(isinstance(v_, Struct) and type(v_.get(F_)) is int for v_ in st_.values()) and all(type(k_) is str or type(k_) is Char for k_ in st_):
                key_ = _pure_expr(X_[3][2], nd, nodes, index, depth)
                key_ = key_ and _coerce(key_[0], key_[1], "s")
                if key_ is None: return None
                cd_ = None
                for fn_, v_, c_ in nd["free"]:
                    if fn_ == S_: cd_ = c_
                if cd_ is None:
                    cd_ = ("K%d_%d" % (nd["j"], len(nd["klists"])), "T"); nd["klists"].append(st_); nd["free"].append((S_, st_, cd_))
                return ("_psst(%s, %s, %r)" % (cd_[0], key_, F_), "u")
    if k == "bin" and len(n) == 4 and n[1] == "'":      # 取り出し: `l ' k`(k は 0 以上の整数)・`l ' k~`(k 番目から後ろ)
        l = _pure_expr(n[2], nd, nodes, index, depth)
        if l is None: return None
        if l[1] == "S":                                                  # Stringの List: `l ' k` は String、`l ' k~` は後ろの List
            kn = n[3]
            if kn[0] == "post" and kn[1] == "~" and len(kn) == 3:
                kn = kn[2]
                if kn[0] != "lit" or type(kn[1]) is not int or len(kn) != 2 or kn[1] < 0: return None
                return ("_psrest(%s, %d)" % (l[0], kn[1]), "S")
            if kn[0] in ("post", "input", "neg", "abs", "norm", "not", "lift", "addr", "prod", "sec", "proc"): return None
            kx = _pure_expr(kn, nd, nodes, index, depth, "i")
            kx = kx and _coerce(kx[0], kx[1], "i")
            return None if kx is None else ("_psixS(%s, 0, %s)" % (l[0], kx), "s")
        if l[1] == "s":                                                  # String: `s ' k` は文字、`s ' k~` は後ろの String
            kn = n[3]; rest = kn[0] == "post" and kn[1] == "~" and len(kn) == 3
            if rest:
                kn = kn[2]
                if kn[0] != "lit" or type(kn[1]) is not int or len(kn) != 2: return None      # `s ' i~`・`s ' (i + 1)~` のような名前・式の撒きは評価器では 1 要素の撒き(`s ' i` と同じ)で読みが違うので、整数の字面だけ
            if kn[0] in ("post", "input", "neg", "abs", "norm", "not", "lift", "addr", "prod", "sec", "proc") and not (kn[0] == "norm"): return None
            kx = _pure_expr(kn, nd, nodes, index, depth, "i")
            kx = kx and _coerce(kx[0], kx[1], "i")
            if kx is None: return None
            return ("_psrests(%s, %s)" % (l[0], kx), "s") if rest else ("_psixs(%s, %s)" % (l[0], kx), "d")
        lt = "M" if l[1] in ("M", "x", "y") else "l"                     # 小数が混ざりうる List の要素は d、整数だけなら i
        et = "d" if lt == "M" else "i"
        l = _coerce(l[0], l[1], lt)
        if l is None: return None
        kn = n[3]
        if kn[0] == "post" and kn[1] == "~":
            if kn[2][0] != "lit" or type(kn[2][1]) is not int or len(kn[2]) != 2 or kn[2][1] < 0: return None
            return ("_psrest(%s, %d)" % (l, kn[2][1]), lt)
        if kn[0] == "lit" and type(kn[1]) is int and len(kn) == 2:
            return None if kn[1] < 0 else ("%s[%d]" % (l, kn[1]), et)
        if kn[0] in ("post", "input", "neg", "abs", "norm", "not", "lift", "addr", "prod", "sec", "proc"): return None
        kx = _pure_expr(kn, nd, nodes, index, depth, "i")
        kx = kx and _coerce(kx[0], kx[1], "i")
        return None if kx is None else ("_psix(%s, %s)" % (l, kx), et)
    if k == "norm":
        if n[1][0] == "id" and n[1][1] in nd["offrest"]:                 # 位置で読む残り: 長さ = 全体 - 位置 - 名前の数
            pi, nb = nd["offrest"][n[1][1]]
            return ("(len(p%d) - o%d - %d)" % (pi, pi, nb), "i")
        x = _pure_expr(n[1], nd, nodes, index, depth)
        if x is None: return None
        if x[1] in ("u", "y"): return ("_psnormu(%s)" % x[0], "i")       # 残りが空なら __(None)。数えると 0
        if x[1] in ("l", "M", "s", "S"): return ("len(%s)" % x[0], "i")
        x = _coerce(x[0], x[1], "x" if x[1] in _WIDE else "?")
        return ("_psnorm(%s)" % x, "i")
    if k == "neg" or k == "abs":
        x = _pure_expr(n[1], nd, nodes, index, depth, "i")
        if x is None: return None
        wd = x[1] in ("d", "x", "y")
        x = _coerce(x[0], x[1], "d" if wd else "i")
        if x is None: return None
        return (("(-%s)" if k == "neg" else "abs(%s)") % x, "d" if wd else "i")
    if k == "bin" and len(n) == 4 and n[1] == "|":                       # 値の `a | b`: a が単位でなければ a、単位なら b(b は必要なときだけ評価する)
        a = _pure_expr(n[2], nd, nodes, index, depth); b = _pure_expr(n[3], nd, nodes, index, depth)
        if a is None or b is None or a[1] in ("s", "k") or b[1] in ("s", "k"): return None
        if a[1] not in ("u", "y"): return a if b[1] != "" else None
        wd = a[1] in _WIDE or b[1] in _WIDE
        nd["tmp"] = nd.get("tmp", 0) + 1; tv = "_w%d" % nd["tmp"]
        return ("(%s if (%s := %s) is not None else %s)" % (tv, tv, a[0], b[0]), ("y" if b[1] in ("u", "y") else "x") if wd else ("u" if b[1] in ("u", "y") else "?"))
    if k == "bin" and len(n) == 4:
        op = n[1]
        if op not in _PURE_BIN: return None
        a = _pure_expr(n[2], nd, nodes, index, depth, "i")
        b = _pure_expr(n[3], nd, nodes, index, depth, "i")
        if a is None or b is None: return None
        if "X" in (a[1], b[1]):                                          # 番地か整数か実行時に決まる値との足し引き掛け: 実行時に型で域を選ぶ(結果もまた X)
            if op not in ("+", "-", "*") or a[1] not in ("i", "a", "X") or b[1] not in ("i", "a", "X"): return None
            ca = "_Addr(%s)" % a[0] if a[1] == "a" else a[0]; cb = "_Addr(%s)" % b[0] if b[1] == "a" else b[0]
            return ("_pxbin(%r, %s, %s)" % (op, ca, cb), "X")
        if a[1] == "a" or b[1] == "a":                                   # 番地: `p + 整数`・`p - 整数` だけ(外へ出たら普通の道が __ にする)
            if a[1] == "i" and b[1] == "a" and op in ("+", "-", "*"):         # 左が整数なら整数の域(integer_overflow.md「左辺が Int なら Int の域」): `n - p` は整数の引き算
                return ("(%s %s %s)" % (a[0], op, b[0]), "i")
            return ("_pa(%s %s %s)" % (a[0], op, b[0]), "a") if (op in ("+", "-") and a[1] == "a" and b[1] in ("i", "a")) else None
        if a[1] in ("d", "x", "y") or b[1] in ("d", "x", "y"):           # 小数が混ざりうる: 整数どうしなら整数の、小数が混ざれば小数の計算(Python の型の通りに決まる)
            if op not in ("+", "-", "*", "/", "%"): return None
            a = _coerce(a[0], a[1], "d"); b = _coerce(b[0], b[1], "d")
            if a is None or b is None: return None
            if nd["gw"]: return ("_pga(%r, %s, %s)" % (op, a, b), "d")
            return ("(%s %s %s)" % (a, op, b) if op in ("+", "-", "*") else "%s(%s, %s)" % ("_pddiv" if op == "/" else "_pdmod", a, b), "d")
        a = _coerce(a[0], a[1], "i"); b = _coerce(b[0], b[1], "i")
        if a is None or b is None: return None
        py = _PURE_BIN[op]
        return ("(%s %s %s)" % (a, py, b) if py in ("+", "-", "*", "&", "|", "^") else "%s(%s, %s)" % (py, a, b), "i")
    if k == "cmp" and len(n[2]) == 1 and n[2][0] in _PURE_CMP:       # 値としての比べ: 成り立てば左の値(witness)、外れれば __
        a = _pure_expr(n[1][0], nd, nodes, index, depth); b = _pure_expr(n[1][1], nd, nodes, index, depth)
        if a is None or b is None or a[1] == "s" or b[1] == "s": return None
        wd = a[1] in _WIDE or b[1] in _WIDE
        a = _coerce(a[0], a[1], "x" if wd else "?"); b = _coerce(b[0], b[1], "x" if wd else "?")
        if a is None or b is None: return None
        return ("_pscmpv(%r, %s, %s)" % (n[2][0], a, b), "y" if wd else "u")
    if k == "seq" and isinstance(n[1], list) and len(n[1]) >= 2:
        items = n[1]
        h = items[0]
        f = nd["env"].get(h[1]) if (h[0] == "id" and h[1] not in nd["vars"]) else None
        if isinstance(f, Closure):                                      # 関数の呼び出し
            if not _pure_plain(f) or len(f.params) != len(items) - 1: return None
            args = []
            for a in items[1:]:
                x = _pure_expr(a, nd, nodes, index, depth)
                if x is None: return None
                args.append(x)
            def _do_call(args):                                          # 実引数(コード, 型)の並びから呼びを作る((コード, 答えの型) か None)
                sig = "".join(t if t in ("i", "l", "d", "M", "s", "S", "a") else "s" if t == "z" else "S" if t == "Z" else "x" if t in ("x", "y") else "?" for _, t in args)
                call = _pure_build(f, sig, nodes, index, depth + 1)
                if call is None: return None
                j, ret = call
                for sp, (cd, t), sc in zip(f.params, args, sig):
                    if sp[0] == "destr" and sc == "d": return None      # 括りに小数を直に渡す形は普通の道へ(整数は先頭で [x] にする。String は文字の並びとして読む)
                xs = [_coerce(cd, t, sc) for (cd, t), sc in zip(args, sig)]
                if any(x is None for x in xs): return None
                kws = []
                for ai, (sp, a_) in enumerate(zip(f.params, items[1:])):          # 実引数が自分の Stringの List の残りそのもの(か `rest ' k~`)なら、写さずに元の list と位置を渡す
                    if sp[0] == "destr" and sp[2] and sig[ai] == "S":
                        a2 = _strip_blk(a_); kk = 0
                        if a2[0] == "bin" and len(a2) == 4 and a2[1] == "'" and a2[2][0] == "id" and a2[3][0] == "post" and a2[3][1] == "~" and len(a2[3]) == 3 and a2[3][2][0] == "lit" and type(a2[3][2][1]) is int and len(a2[3][2]) == 2 and a2[3][2][1] >= 0:
                            kk = a2[3][2][1]; a2 = a2[2]
                        if a2[0] == "id" and a2[1] in nd["offrest"] and a2[1] not in nd["vars"] and nd["sg"][nd["offrest"][a2[1]][0]] == "S":
                            pi_, nb_ = nd["offrest"][a2[1]]
                            xs[ai] = "p%d" % pi_; kws.append("o%d=o%d + %d" % (ai, pi_, nb_ + kk))
                        else: kws.append("o%d=0" % ai) if False else None
                if (h[1], j) not in nd["calls"]: nd["calls"].append((h[1], j))
                nd["ncalls"] += 1; nd["xcalls"] += 1
                return ("F%d(%s)" % (j, ", ".join(xs + kws)), ret)
            xi_ = [q for q, (_, t_) in enumerate(args) if t_ == "X"]
            if not xi_: return _do_call(args)
            # 答えの型が番地か整数か実行時にしか決まらない実引数('X')が 1 つ: 番地の版と整数の版を作って、実行時に型で選ぶ(その実引数より前は副作用の無い名前か数だけ)
            q = xi_[0]
            if len(xi_) != 1 or not all(re.fullmatch(r"\(?-?\w+\)?", args[k][0]) for k in range(q)): return None
            nd["tmp"] = nd.get("tmp", 0) + 1; tv = "_x%d" % nd["tmp"]
            va = _do_call([(tv, "a") if k == q else a for k, a in enumerate(args)])
            vi = _do_call([("int(%s)" % tv, "i") if k == q else a for k, a in enumerate(args)])
            if va is None or vi is None: return None
            ra, ri = va[1], vi[1]
            ca = "_Addr(%s)" % va[0] if ra == "a" else va[0]
            ci = "_Addr(%s)" % vi[0] if ri == "a" else vi[0]
            if not (ra in ("a", "i", "X") and ri in ("a", "i", "X")): 
                if ra != ri: return None
                rt = ra
            else: rt = "X"
            return ("(%s if _pxis(%s:=%s) else %s)" % (ca, tv, args[q][0], ci), rt)
        if f is not None and not (type(f) is Char or (type(f) is str and f)): return None      # 頭が外の文字・String の値の並び(`ms_open ms_nl … f x`)は続ける
        if any(it[0] == "post" and it[1] == "~" for it in items):       # 撒き `x~`: List の連結(`x~ y~`・`x~ 5`・`5 x~ 6`)。ふつうの List を撒かずに置いた項は入れ子になるので対象外
            cc = _pure_concat(items, nd, nodes, index, depth)
            return cc
        j_ = 1
        if items[0][0] != "id" or items[0][1] in nd["vars"] or items[0][1] in nd["offrest"] or not isinstance(nd["env"].get(items[0][1]), Closure):
            vs_ = None
            while j_ < len(items):                                       # 値の並びの途中から関数の呼び出し: `c1 c2 f x y c3 g z`(関数は右の値を口の数だけ取る。呼びの答えと値を左から結合する)
                it_ = items[j_]
                if it_[0] == "id" and it_[1] not in nd["vars"] and it_[1] not in nd["offrest"] and isinstance(nd["env"].get(it_[1]), Closure):
                    vs_ = vs_ if vs_ is not None else [_pure_expr(a, nd, nodes, index, depth) for a in items[:j_]]
                    break
                j_ += 1
            if vs_ is not None:
                f_ = nd["env"].get(items[j_][1])
                if not _pure_plain(f_): return None
                allv = list(vs_); i_ = j_
                while i_ < len(items):
                    it_ = items[i_]
                    if it_[0] == "id" and it_[1] not in nd["vars"] and it_[1] not in nd["offrest"] and isinstance(nd["env"].get(it_[1]), Closure):
                        g_ = nd["env"].get(it_[1])
                        if not _pure_plain(g_) or i_ + len(g_.params) > len(items) - 1: return None
                        allv.append(_pure_expr(("seq", items[i_:i_ + 1 + len(g_.params)]), nd, nodes, index, depth)); i_ += 1 + len(g_.params)
                    else: allv.append(_pure_expr(it_, nd, nodes, index, depth)); i_ += 1
                if any(v is None for v in allv): return None
                _fix_hint([(v[0], v[1]) for v in allv], nodes)
                if not all(v[1] in ("d", "s", "z", "y") for v in allv) or not any(v[1] in ("s", "z") for v in allv): return None
                return ("_psjoin(%s)" % ", ".join(v[0] for v in allv), "z")
        xs = []                                                          # 値の並び: 整数どうしは List に積まれる(小数が混ざりうれば数の List)
        ys = [_pure_expr(a, nd, nodes, index, depth, "i") for a in items]
        if any(y is None for y in ys): return None
        _fix_hint([(y[0], y[1]) for y in ys], nodes)
        if any(y[1] in ("s", "z") for y in ys):                          # String・文字の並び: 結合して 1 本の String に
            if not all(y[1] in ("d", "s", "z", "y") for y in ys): return None
            return ("_psjoin(%s)" % ", ".join(y[0] for y in ys), "z")
        wd = any(y[1] in ("d", "x", "y") for y in ys)
        if wd and nd["gw"]: return None                                  # 文字が混ざりうる並びは文字列に結合されうる: 普通の道へ
        for y in ys:
            x = _coerce(y[0], y[1], "d" if wd else "i")
            if x is None: return None
            xs.append(x)
        return ("[%s]" % ", ".join(xs), "M" if wd else "l")
    if PURE_DEBUG: PURE_WHY[(k, n[1] if k == "bin" and len(n) > 1 else "")] = PURE_WHY.get((k, n[1] if k == "bin" and len(n) > 1 else ""), 0) + 1
    return None
def _runs_ok(kinds):                             # 文字の世界: 文字が混ざりうる項(整数でない項)があるなら、(1) 撒きでない項はそれ 1 つだけ、(2) その前の撒きは 1 つまで。ほかにも項がある・撒きが 2 つ続いた後ろに来ると、評価器は文字列に結合する(`[a~ \\c \\d]`・`[a~ 1 \\c]`・`[1 n~ \\c]`・`[a~ n~ \\c]`。`[a~ \\c n~]`・`[\\c n~ m~]` は List)ので普通の道へ
    es = [t for k, t in kinds if k == "e"]
    if len(es) <= 1 or all(t == "i" for t in es):
        if all(t == "i" for t in es): return True
        before = 0
        for k, t in kinds:
            if k == "e": break
            before += 1
        return before <= 1
    return False
def _fix_hint(items_cd, nodes):                  # 文字列を作る並びに、答えの型がまだ見込み(整数)のままの作りかけの関数の呼び出しがあれば、見込みを String の可能性に直して作り直す
    if not any(t in ("s", "z") or c.startswith("_psix") for c, t in items_cd): return
    for c, t in items_cd:
        m = re.match(r"F(\d+)\(", c)
        if m and t == "i":
            n2 = nodes[int(m.group(1))]
            if n2["ret"] is None and n2["hint"] == "i": PURE_HINT[n2["key"]] = "z"; raise _Rebuild()
def _pure_parts(items, nd, nodes, index, depth):
    """連結の項の並び → ([('s', List の式) / ('e', 要素の式)], 数の List になりうるか)。作れなければ None。文字が混ざりうる世界では整数だけの項に限る(文字は文字列に結合されうる)。"""
    parts = []; wide = False; kinds = []
    for it in items:
        if it[0] == "post" and it[1] == "~" and len(it) == 3:
            y = _pure_expr(it[2], nd, nodes, index, depth)
            if y is None: return None
            lt = "M" if y[1] in ("M", "x", "y") else "l"
            c = _coerce(y[0], y[1], lt)
            if c is None: return None
            parts.append(("s", c)); wide = wide or lt == "M"; kinds.append(("s", None))
        else:
            y = _pure_expr(it, nd, nodes, index, depth, "i")
            if y is None: return None
            w = y[1] in ("d", "x", "y")
            c = _coerce(y[0], y[1], "d" if w else "i")
            if c is None: return None
            parts.append(("e", c)); wide = wide or w; kinds.append(("e", y[1]))
    if nd["gw"] and not _runs_ok(kinds): return None
    return parts, wide
def _parts_code(parts):
    out = []; run = []
    for k, c in parts:
        if k == "e": run.append(c)
        else:
            if run: out.append("[%s]" % ", ".join(run)); run = []
            out.append(c)
    if run: out.append("[%s]" % ", ".join(run))
    if len(out) == 1 and not out[0].startswith("["): out.insert(0, "[]")      # 撒きが 1 つだけでも新しい List にする(元を共有しない)
    return " + ".join(out)
def _pure_concat(items, nd, nodes, index, depth):
    r = _pure_parts(items, nd, nodes, index, depth)
    if r is None: return None
    parts, wide = r
    return ("(%s)" % _parts_code(parts), "M" if wide else "l")
def _pure_cond(c, nd, nodes, index, depth):
    """行の条件(真か偽か)の Python 式。比べ・それを `&`(両方成り立つ)・`|`(どちらか成り立つ)でつないだ物・括り・書き込み・値か単位を返す関数の呼び出し。"""
    k = c[0]
    if k == "bin" and len(c) == 4 and c[1] == "==": return _pure_cond(("cmp", (c[2], c[3]), ("==",)), nd, nodes, index, depth)      # 二項の `==` は `=` と同じ比べ
    if k == "cmp":
        if len(c[2]) != 1 or c[2][0] not in _PURE_CMP: return None
        op = c[2][0]
        a = _pure_expr(c[1][0], nd, nodes, index, depth); b = _pure_expr(c[1][1], nd, nodes, index, depth)
        if a is None or b is None: return None
        if a[1] == "a": a = (a[0], "i")                              # 番地の比べは整数の大小(域の規則は算術だけ)
        if b[1] == "a": b = (b[0], "i")
        if a[1] == "X": a = ("_pxi(%s)" % a[0], "i")                 # 番地か整数か実行時に決まる値: 数として比べる(__ なら普通の道へ)
        if b[1] == "X": b = ("_pxi(%s)" % b[0], "i")
        if a[1] == "s" or b[1] == "s":                               # String(か文字)どうしの比べ
            if a[1] not in ("s", "d") or b[1] not in ("s", "d"): return None
            return "_pscmp(%r, %s, %s)" % (op, a[0], b[0])
        if a[1] in ("i", "d") or b[1] in ("i", "d"):
            w_ = "d" if (a[1] in _WIDE or b[1] in _WIDE) else "i"
            a = _coerce(a[0], a[1], w_); b = _coerce(b[0], b[1], w_)
            return None if a is None or b is None else "(%s %s %s)" % (a, _PURE_CMP[op], b)
        if a[1] in ("l", "M") and b[1] in ("l", "M"):
            return "(%s %s %s)" % (a[0], _PURE_CMP[op], b[0]) if op in ("=", "==", "!=") else None
        w_ = "x" if (a[1] in _WIDE or b[1] in _WIDE) else "?"
        a = _coerce(a[0], a[1], w_); b = _coerce(b[0], b[1], w_)
        if a is None or b is None: return None
        return "_pscmp(%r, %s, %s)" % (op, a, b)
    if k == "block":
        return None if isinstance(c[1], list) else _pure_cond(c[1], nd, nodes, index, depth)
    if k == "not" and c[1][0] == "id" and c[1][1] in nd["offrest"] and c[1][1] not in nd["vars"]:      # `!s`(残りが空か)。位置で読む残りに限る
        pi, nb = nd["offrest"][c[1][1]]
        return "(len(p%d) - o%d - %d <= 0)" % (pi, pi, nb)
    if k == "bin" and c[1] == "#" and len(c) == 4:
        e = _pure_expr(c, nd, nodes, index, depth)
        if e is None: return None
        return "(%s, True)[1]" % e[0]
    if k == "bin" and c[1] in ("&", "|") and len(c) == 4:
        l = _pure_cond(c[2], nd, nodes, index, depth)
        if l is None: return None
        r = _pure_cond(c[3], nd, nodes, index, depth)
        return None if r is None else "(%s %s %s)" % (l, "and" if c[1] == "&" else "or", r)
    if k == "seq" and isinstance(c[1], list) and len(c[1]) >= 2 and c[1][0][0] == "id":      # 関数の呼び出し: 単位でなければ成り立つ
        e = _pure_expr(c, nd, nodes, index, depth)
        if e is None or e[1] == "z" or isinstance(nd["env"].get(c[1][0][1]), Closure) is False: return None
        return "(%s is not None)" % e[0]
    return None
def _strip_blk(e):
    while e[0] == "block" and not isinstance(e[1], list): e = e[1]
    return e
def _acc_safe(n, name, me, i, nparams):
    """List の仮引数 name を、輪の中で『足す』ときに元の list を書き換えてよいか(別の所に渡されていないか)。
    name の出方が、`||name||`・`name ' k`・答えの行の name そのもの・自分への末尾呼び出しの i 番目(`name` / `name~ …`)だけなら書き換えてよい。"""
    if isinstance(n, list): return all(_acc_safe(x, name, me, i, nparams) for x in n)
    if not isinstance(n, tuple) or not n: return True
    if n[0] == "id": return len(n) < 2 or n[1] != name
    if n[0] == "norm" and n[1] == ("id", name): return True
    if n[0] == "bin" and len(n) == 4 and n[1] == "'" and n[2] == ("id", name): return _acc_safe(n[3], name, me, i, nparams)
    if n[0] == "seq" and isinstance(n[1], list) and len(n[1]) == nparams + 1 and n[1][0] == ("id", me):
        for k, a in enumerate(n[1][1:]):
            c = _strip_blk(a)
            if k == i:
                if c == ("id", name): continue
                if c[0] == "seq" and isinstance(c[1], list) and len(c[1]) >= 2 and c[1][0] == ("post", "~", ("id", name)) and all(_acc_safe(x, name, me, i, nparams) for x in c[1][1:]): continue
            if not _acc_safe(a, name, me, i, nparams): return False
        return True
    if n[0] == "cases":
        for c, e in n[1]:
            if c is not None and not _acc_safe(c, name, me, i, nparams): return False
            if _strip_blk(e) == ("id", name): continue                    # 答えの行(輪が終わるので、書き換えのあとに誰も触らない)
            if not _acc_safe(e, name, me, i, nparams): return False
        return True
    return all(_acc_safe(x, name, me, i, nparams) for x in n)
def _has_rest(n, name):                          # name ' k~ (後ろを取る形)が本体のどこかにあるか
    if isinstance(n, list): return any(_has_rest(x, name) for x in n)
    if not isinstance(n, tuple) or not n: return False
    if n[0] == "bin" and len(n) == 4 and n[1] == "'" and n[2] == ("id", name) and isinstance(n[3], tuple) and n[3][:2] == ("post", "~"): return True
    return any(_has_rest(x, name) for x in n[1:])
PURE_HINT = {}                                   # 関数(本体・環境・型)ごとの答えの型の見込み(外れたら直して作り直す)
_GW = [False]                                    # いま作っている計画が文字の世界か(入口の実引数に文字がある)
PURE_WIDEN = {}                                  # 関数(本体・環境・型)ごとに、輪の中で小数が混ざる仮引数の番号(型を i→d・l→M・?→x に広げて作り直す)
_WID = {"i": "d", "l": "M", "?": "x", "s": "M"}      # s は `acc~ …` で足される String の仮引数(Char の List に直して持つ。_psexp)
class _Rebuild(Exception): pass
class _NeedGW(Exception): pass                   # 外の String・String の字面を読む計画は、文字の世界で作り直す
def _pure_build(cl, sig, nodes, index, depth):
    """cl を型 sig(各引数 'i' 整数 / 'l' List / '?')で Python の関数にする。(番号, 答えの型) か、作れなければ None"""
    key = (id(cl.body), id(cl.env), sig)
    if key in index:
        n2 = nodes[index[key]]
        return index[key], (n2["ret"] if n2["ret"] is not None else n2["hint"])      # 作り終えた関数は本当の答えの型、作りかけ(再帰)は見込み
    if len(nodes) >= 64 or depth > 30 or not _pure_plain(cl, True) or len(sig) != len(cl.params):
        if PURE_DEBUG: PURE_WHY[("build", len(nodes) >= 64, depth > 30, _pure_plain(cl, True))] = PURE_WHY.get(("build", len(nodes) >= 64, depth > 30, _pure_plain(cl, True)), 0) + 1
        return None
    hint = PURE_HINT.get(key, "i")
    j = len(nodes)
    wset = PURE_WIDEN.get(key, ())
    sg = "".join(_WID.get(c, c) if i in wset else c for i, c in enumerate(sig))       # 実際に作るときの型(呼ぶ側は元の型で渡してよい: i ⊂ d・l ⊂ M・? ⊂ x)
    dconv = {i for i, sp in enumerate(cl.params) if sp[0] == "destr" and sg[i] == "i"}      # 括りの仮引数に整数が渡される(1 要素の器 ≅ スカラー): 関数の先頭で [x] にして List として読む
    if dconv: sg = "".join("l" if i in dconv else c for i, c in enumerate(sg))
    conv = {i for i, c in enumerate(sig) if c == "s" and sg[i] == "M"}       # String で渡され、輪の中で `acc~ …` で足されて Char の List になる仮引数
    nd = {"cl": cl, "body": cl.body, "env": cl.env, "sig": sig, "sg": sg, "gw": _GW[0], "vars": {}, "offrest": {}, "free": [], "klists": [], "calls": [], "ncalls": 0, "xcalls": 0, "src": None, "j": j, "hint": hint, "key": key, "ret": None}
    nodes.append(nd); index[key] = j
    pro = []                                     # 括りの仮引数を、名前ごとの変数にほどく
    offs = set()                                 # 残りを位置で読む括りの仮引数の番号
    for i, sp in enumerate(cl.params):
        if sp[0] == "name": nd["vars"][sp[1]] = ("p%d" % i, sg[i])
        else:
            if sg[i] in ("i", "d"): return None
            if sg[i] == "a":                                          # 番地は 1 要素の器と同じ: `[x]` の x が番地そのもの(名前が 1 つだけの括りに限る)
                if len(sp[1]) != 1 or sp[2]: return None
                nd["vars"][sp[1][0]] = ("p%d" % i, "a"); continue
            names = sp[1]; rest = sp[2]; nb = len(names)
            et = "s" if sg[i] == "S" else "d" if sg[i] in ("M", "x", "y", "s") else "i"            # 括りの中の要素の型(String の中は文字、Stringの List の中は String)
            if sg[i] not in ("l", "M", "s", "S"): pro.append("p%d = _cl(p%d)" % (i, i))
            unpack = ", ".join("q%d_%d" % (i, t) for t in range(nb)) + ("," if nb == 1 else "")
            if rest:                                                  # 残りは位置で読む(毎回切り出さない。名前で読まれたときだけ、その場で切り出す)
                offs.add(i); nd["offrest"][rest] = (i, nb)
                pro.append("if len(p%d) - o%d <= 0: return None" % (i, i))          # 残りが空 = 単位の実引数(呼び出しは死んで __)
                if nb: pro.append("if len(p%d) - o%d < %d: raise _PureBail()" % (i, i, nb))
                if nb and sg[i] == "s": pro.append("%s = [Char(c) for c in p%d[o%d:o%d + %d]]" % (unpack, i, i, i, nb))
                elif nb: pro.append("%s = p%d[o%d:o%d + %d]" % (unpack, i, i, i, nb))
            else:
                pro.append("if len(p%d) < %d: raise _PureBail()" % (i, nb))
                pro.append("%s = %sp%d[:%d]%s" % (unpack, "[Char(c) for c in " if sg[i] == "s" else "", i, nb, "]" if sg[i] == "s" else ""))
                if rest:
                    pro.append("r%d = p%d[%d:] or None" % (i, i, nb)); nd["vars"][rest] = ("r%d" % i, "u")          # 残りが空なら __(None)
            for t, nm in enumerate(names): nd["vars"][nm] = ("q%d_%d" % (i, t), et)
    body = cl.body; rows_out = []; loop = False; rtypes = []
    tail_name = [None]
    def tail_self(e):                            # 値が自分への呼び出しそのもの(末尾呼び出し)なら、その実引数の式の並び
        while e[0] == "block" and not isinstance(e[1], list): e = e[1]
        if e[0] == "seq" and isinstance(e[1], list) and len(e[1]) == len(cl.params) + 1 and e[1][0][0] == "id" and e[1][0][1] not in nd["vars"]:
            f = nd["env"].get(e[1][0][1])
            if isinstance(f, Closure) and f.body is cl.body and f.env is cl.env and not f.args and not f.dead and f.native is None: tail_name[0] = e[1][0][1]; return e[1][1:]
        return None
    owned = set()                                # 足しても元の list を書き換えてよい仮引数の番号
    def widen(i):                                # 輪の中で i 番目の仮引数に小数が混ざる: 型を広げて最初から作り直す
        w = PURE_WIDEN.setdefault(key, set())
        if i in w: return None
        w.add(i); raise _Rebuild()
    def fit(i, x):                               # 自分への末尾呼び出しの i 番目の実引数 x を、仮引数の型に合わせる(合わなければ None。小数が混ざるなら型を広げる)
        c = sg[i]; t = x[1]
        if (c == "i" and t in ("d", "x", "y")) or (c == "l" and t in ("M", "x", "y")) or (c == "?" and t in _WIDE): return widen(i)
        return _coerce(x[0], t, c)
    def value(e):
        nonlocal loop
        t = tail_self(e)
        if t is not None:
            stmts = []; later = []
            for i, a in enumerate(t):
                c = _strip_blk(a); nm = cl.params[i][1] if cl.params[i][0] == "name" else None
                if cl.params[i][0] == "destr" and sg[i] in ("i", "d"): return None
                if cl.params[i][0] == "destr" and sg[i] == "a":          # 番地を括りに渡し直す輪: 仮引数は番地そのもの(上の `[x]` の読み)
                    x = _pure_expr(a, nd, nodes, index, depth)
                    x = x and _coerce(x[0], x[1], "a")
                    if x is None: return None
                    stmts.append("_a%d = %s" % (i, x)); later.append("p%d = _a%d" % (i, i)); continue
                if nm and sg[i] == "s" and c[0] == "seq" and isinstance(c[1], list) and len(c[1]) >= 3 and c[1][0] == ("post", "~", ("id", nm)) and not any(x[0] == "post" and x[1] == "~" for x in c[1][1:]) and i not in conv:
                    ys_ = [_pure_expr(x, nd, nodes, index, depth) for x in c[1][1:]]      # String の `acc~ c1 c2 …`(足す項が 2 つ以上の文字・String)は String のまま後ろに足す
                    if any(y is None or y[1] not in ("d", "s") for y in ys_): return None
                    stmts.append("_a%d = _pstxt(%s)" % (i, ", ".join(y[0] for y in ys_))); later.append("p%d = p%d + _a%d" % (i, i, i))
                    continue
                if nm and sg[i] == "s" and c[0] == "seq" and isinstance(c[1], list) and len(c[1]) >= 2 and c[1][0] == ("post", "~", ("id", nm)): widen(i)      # String の `acc` に足す: Char の List に直して作り直す
                if i in conv:
                    if not (c == ("id", nm) or (c[0] == "seq" and isinstance(c[1], list) and len(c[1]) >= 2 and c[1][0] == ("post", "~", ("id", nm)))): return None
                    if not _acc_safe(body, nm, tail_name[0], i, len(cl.params)) or _has_rest(body, nm): return None
                if i in offs:                                        # 残りを位置で読む括り: 残りそのものを渡すなら位置を進めるだけ
                    if c == ("id", cl.params[i][2]): later.append("o%d += %d" % (i, len(cl.params[i][1]))); continue
                    if c[0] == "bin" and len(c) == 4 and c[1] == "'" and c[2] == ("id", cl.params[i][2]) and c[3][0] == "post" and c[3][1] == "~" and len(c[3]) == 3 and c[3][2][0] == "lit" and type(c[3][2][1]) is int and len(c[3][2]) == 2 and c[3][2][1] >= 0:
                        later.append("o%d += %d" % (i, len(cl.params[i][1]) + c[3][2][1])); continue      # `rest ' k~`: 位置を k 進めるだけ
                    x = _pure_expr(a, nd, nodes, index, depth)
                    if x is None: return None
                    if sg[i] in ("M", "x", "y"): x = _coerce(x[0], x[1], "M")
                    elif x[1] in ("M", "x", "y"): x = widen(i)
                    else: x = _coerce(x[0], x[1], "s" if sg[i] == "s" else "S" if sg[i] == "S" else "l")
                    if x is None: return None
                    stmts.append("_a%d = %s" % (i, x)); later.append("p%d = _a%d" % (i, i)); later.append("o%d = 0" % i)
                    continue
                if nm and sg[i] in ("l", "?", "M", "x") and c[0] == "seq" and isinstance(c[1], list) and len(c[1]) >= 2 and c[1][0] == ("post", "~", ("id", nm)):
                    its = []                                         # `acc~ a b …`: acc の後ろに整数(小数が混ざりうる List なら数)・撒いた List `y~` を足す
                    kinds_ = [("s", None)]
                    for x in c[1][1:]:
                        if x[0] == "post" and x[1] == "~" and len(x) == 3:
                            r_ = _pure_parts([x], nd, nodes, index, depth)
                            if r_ is None: return None
                            if r_[1] and sg[i] in ("l", "?"): widen(i)
                            its.append(r_[0][0]); kinds_.append(("s", None)); continue
                        y = _pure_expr(x, nd, nodes, index, depth, "i")
                        if y is None: return None
                        kinds_.append(("e", y[1]))
                        if sg[i] in ("l", "?") and y[1] in ("d", "x", "y"): y = widen(i)
                        else: y = _coerce(y[0], y[1], "d" if sg[i] in ("M", "x") else "i")
                        if y is None: return None
                        its.append(("e", y))
                    if nd["gw"] and not _runs_ok(kinds_): return None
                    if i in conv: later.append("_ch%d = True" % i)
                    stmts.append("_a%d = %s" % (i, _parts_code(its) if any(k == "e" for k, _ in its) or len(its) > 1 else "[] + " + its[0][1]))
                    if i not in owned and _acc_safe(body, nm, tail_name[0], i, len(cl.params)): owned.add(i)
                    if i in owned:
                        later.append("if _o%d: p%d.extend(_a%d)" % (i, i, i)); later.append("else: p%d = _cl(p%d) + _a%d; _o%d = True" % (i, i, i, i))
                    else: later.append("p%d = _cl(p%d) + _a%d" % (i, i, i))
                    continue
                x = _pure_expr(a, nd, nodes, index, depth, "i" if sg[i] == "i" else None)
                x = x and fit(i, x)
                if x is None: return None
                stmts.append("_a%d = %s" % (i, x)); later.append("p%d = _a%d" % (i, i))
                if i in owned: later.append("_o%d = False" % i)
            loop = True; nd["ncalls"] += 1
            return stmts + later + ["continue"]
        ee = _strip_blk(e)
        if conv and ee[0] == "id" and any(cl.params[i][0] == "name" and cl.params[i][1] == ee[1] for i in conv):      # String の `acc` をそのまま答えにする: 1 度も足していなければ String のままのはずなので、普通の道に任せる
            ci = [i for i in conv if cl.params[i][1] == ee[1]][0]
            rtypes.append("M"); return ["return (p%d if _ch%d else _pbail())" % (ci, ci)]
        v = _pure_expr(e, nd, nodes, index, depth)
        if v is None: return None
        rtypes.append(v[1])                                      # 番地('a')を答えにしてもよい(番地だけを返す関数は run_pure が最後に Addr にする。整数や __ と混ざる関数 'X' は、番地の行を mk_addr で包む)
        return ["return " + ("_MKA_(%s)" % v[0] if v[1] == "a" else v[0])]
    pre = []                                     # 局所の定義(式の前に 1 行ずつ代入する)
    if body[0] == "cases":
        rows = body[1]
        names = [c[1] for c, _ in rows if c is not None and c[0] == "id"]
        branchy = any(c is not None and c[0] != "id" for c, _ in rows)
        if False and names and not branchy:      # R128 で廃止(R80): 枝の無い本体の `名前 : 右辺` は局所の定義(外の名前・仮引数・組み込みと重ならず、重複しないときだけ。そうでなければ条件の行で、ここでは扱わない)
            if rows[-1][0] is not None or any(c is None for c, _ in rows[:-1]) or len(set(names)) != len(names): return None
            if any(nm in nd["vars"] or nd["env"].owner(nm) is not None or nm in BUILTINS for nm in names): return None
            for c, v in rows[:-1]:
                if v[0] == "lam": return None
                x = _pure_expr(v, nd, nodes, index, depth)
                if x is None: return None
                cd = _coerce(x[0], x[1], "x" if x[1] in _WIDE else "?")
                if cd is None: return None
                ty = x[1] if x[1] not in ("u", "y") else ("?" if x[1] == "u" else "x")
                n_loc = len([1 for vv in nd["vars"].values() if vv[0].startswith("l")])
                nd["vars"][c[1]] = ("l%d" % n_loc, ty); pre.append("l%d = %s" % (n_loc, cd))
            rows = rows[-1:]
        if not rows or any(c is None for c, _ in rows[:-1]): return None       # 既定の行は最後だけ
        for c, e in rows:
            cond = None
            if c is not None:
                cond = _pure_cond(c, nd, nodes, index, depth)
                if cond is None: return None
            v = value(e)
            if v is None: return None
            rows_out.append((cond, v))
    else:
        v = value(body)
        if v is None: return None
        rows_out.append((None, v))
    pad = "            " if loop else "    "
    lines = [pad + p for p in pro + pre]                       # 括りの分解・局所の定義は、輪なら回ごとにやり直す
    for cond, v in rows_out:
        if cond is not None: lines.append("%sif %s:" % (pad, cond)); lines += ["%s    %s" % (pad, x) for x in v]
        else: lines += [pad + x for x in v]
    implicit_unit = rows_out[-1][0] is not None
    if implicit_unit: lines.append(pad + "return None")                   # どの行も当たらなければ __(単位)
    if loop:
        lines.insert(0, "    while True:"); lines.insert(1, "        for _k in _R256:")
        _ids = ["p%d" % i for i in range(len(cl.params))] + ["o%d" % i for i in sorted(offs)]
        # 止まらない輪の検出(既定。V10): 256 回ごとに輪の状態を調べ、前に(2 の冪の番に)控えた状態と同じなら普通の道へ回す(速い道は効果を持たない。内側の for は C で数えるので、回ごとの費用が無い)
        lines += ["        _st = _pidk(%s)" % ", ".join(_ids), "        if _st == _sv: raise _PureBail()", "        _ic += 1", "        if not _ic & (_ic - 1): _sv = _st"]
    lines[0:0] = (["    _ic = 0; _sv = None"] if loop else []) + ["    p%d = [p%d]" % (i, i) for i in sorted(dconv)] + ["    _o%d = False" % i for i in sorted(owned)] + ["    o%d = 0" % i for i in sorted(offs) if sg[i] != "S"] + ["    _ch%d = False\n    p%d = _psexp(p%d)" % (i, i, i) for i in sorted(conv)]
    if len(nd["free"]) > 10: return None
    ts = set(rtypes)
    if "a" in ts or "X" in ts:
        if not ts <= {"a", "i", "X"}: return None                # 番地・整数・(番地か整数か __ の関数の呼び)以外が混ざる物は普通の道
        ret = "a" if (ts == {"a"} and not implicit_unit) else "X"      # X: 番地か整数か __ のどれかを実行時に返す。式の中には置けず(_coerce が断る)、答えの行にだけ置ける
        lines = [l.replace("_MKA_(", "mk_addr(" if ret == "X" else "(") for l in lines]
    elif "k" in ts:
        if ts != {"k"}: return None
        ret = "k"
    elif ts & {"s", "z"}:
        if not ts <= {"s", "z", "u", "d", "y"}: return None      # 文字(d)も混ざってよい(実行時に数なら、使う所が型を検めて普通の道へ)
        ret = "z" if (ts & {"z", "u"} or implicit_unit) else "s"
    elif ts & set(_WIDE):                          # 小数が混ざりうる答え
        ret = "y" if (implicit_unit or ts & {"u", "y"}) else ("d" if ts <= {"i", "d"} else "M" if ts <= {"l", "M"} else "x")
    else: ret = "u" if (implicit_unit or "u" in ts) else ("i" if ts == {"i"} else "l" if ts == {"l"} else "?" if ts else "i")
    nd["ret"] = ret
    kwo = [i for i in sorted(offs) if sg[i] == "S"]                         # Stringの List の残りは、位置を呼び側から受け取る(写さない)
    nd["src"] = "def F%d(%s):\n%s\n" % (j, ", ".join(["p%d" % i for i in range(len(cl.params))] + (["*"] + ["o%d=0" % i for i in kwo] if kwo else [])), "\n".join(lines))
    return j, ret
PURE_BODYSTAT = {}                               # 本体ごとの (本体, 計画が作れなかった数, 作れた数)。作れた例が 1 つもなく何度も外れた本体は、入口の実引数の型を調べる(長い List を毎回なめる)前に普通の道へ回す
def pure_plan(g, sig, gw=False):
    """g(型 sig の実引数が全部そろった)の計画 (nodes, 入口の関数, 数え)。作れなければ False。本体ごとに覚え、呼ぶたびに『名前が同じ物を指し、外の値が同じか』を見直す。"""
    pk = (id(g.body), sig, gw)
    ent = PURE_PLANS.get(pk)
    if ent is not None and ent[0] is g.body:
        plan = ent[1]
        if plan is False:
            if ent[2] is g.env or PURE_TRIES.get(pk, 0) >= 8:      # 同じ環境で作れなかった物は作り直さない
                bs = PURE_BODYSTAT.get(id(g.body))
                if bs is not None and bs[0] is g.body: bs[1] += 1
                return False
        elif plan[0][0]["env"] is g.env and _pure_valid(plan[0]): return plan
    tries = PURE_TRIES[pk] = PURE_TRIES.get(pk, 0) + 1
    plan = False
    tried_l = False
    if tries <= 8 and _pure_plain(g, True):
        for _round in range(8):                  # 答えの型の見込みが外れた物・輪で小数が混ざる物は、直して作り直す
            nodes, index = [], {}
            _GW[0] = gw
            try:
                try: r = _pure_build(g, sig, nodes, index, 0)
                except _Rebuild: continue
                except _NeedGW: gw = True; continue
                if r is None and not tried_l:            # 自分(の再帰)の答えを整数と見込んで作れなかった物は、List と見込んで 1 回だけやり直す
                    tried_l = True; rk = (id(g.body), id(g.env), sig)
                    if PURE_HINT.get(rk, "i") == "i": PURE_HINT[rk] = "l"; continue
                if r is None or r[0] != 0: break
                bad = [nd for nd in nodes if nd["ret"] != nd["hint"]]
                if bad:
                    for nd in bad: PURE_HINT[nd["key"]] = nd["ret"]
                    continue
                ns = dict(_PURE_NS)
                for nd in nodes:
                    for i, v in enumerate(nd["klists"]): ns["K%d_%d" % (nd["j"], i)] = v
                exec("\n".join(nd["src"] for nd in nodes), ns)
                _pure_memo(nodes, ns)
                plan = (nodes, ns["F0"], [0, 0, 0])
            except (IndexError, TypeError, ValueError, SyntaxError): plan = False
            break
    PURE_PLANS[pk] = (g.body, plan, g.env)
    bs = PURE_BODYSTAT.get(id(g.body))
    if bs is None or bs[0] is not g.body: bs = PURE_BODYSTAT[id(g.body)] = [g.body, 0, 0]
    if plan is False: bs[1] += 1
    else: bs[2] += 1
    if PURE_DEBUG and plan is False:
        e = g.env; nm = "?"
        while e is not None and nm == "?":
            for k_, v_ in e.vars.items():
                if isinstance(v_, Closure) and v_.body is g.body: nm = k_; break
            e = e.parent
        print("[pure] 速い道に乗らない:", nm, g.body[0], len(g.params), sig, file=sys.stderr)
        print("[why]", dict(PURE_WHY), file=sys.stderr); PURE_WHY.clear()
    return plan
_PURE_IMPURE = ("_psrd", "_pswr", "_pswc")           # メモリを読む・書く関数の印(`_psrd` `_psrdx` `_pswr` `_pswrx` `_pswc` `_pswcx` は頭がこれ)
def _pure_memo(nodes, ns):
    """メモリに触れず(読みも書きもせず)、触れる関数も呼ばない関数のうち、自分以外を呼ぶ・二重に呼ぶ物は、答えを覚える(同じ実引数なら同じ答え)。
    覚えた答えは計画ごと(外の値や呼ぶ先が変われば計画ごと作り直す)。実引数が List の関数は対象外。覚えるのは成功した答えだけ。"""
    bad = [any(m in nd["src"] for m in _PURE_IMPURE) for nd in nodes]
    changed = True
    while changed:                                  # 触れる関数を(間接にでも)呼ぶ物も除く
        changed = False
        for i, nd in enumerate(nodes):
            if not bad[i] and any(bad[j] for _, j in nd["calls"]): bad[i] = changed = True
    for i, nd in enumerate(nodes):
        if bad[i] or nd["xcalls"] == 0 or nd["sig"].strip("i"): continue          # 実引数が全部整数の物だけ(1 と 1.0 は同じ鍵になるので小数は覚えない)
        ns["F%d" % i] = _memo_wrap(ns["F%d" % i])
def _memo_wrap(f):
    cache = {}
    def w(*a):
        try: return cache[a]
        except KeyError: pass
        r = f(*a)
        if len(cache) > 200000: cache.clear()
        cache[a] = r
        return r
    return w
def _pure_valid(nodes):
    for nd in nodes:
        env = nd["env"]
        for nm, v, _ in nd["free"]:
            x = env.get(nm)
            if type(v) is int:
                if type(x) is not int or x != v: return False
            elif type(v) is float:
                if type(x) is not float or repr(x) != repr(v): return False
            elif type(v) is Char:
                if type(x) is not Char or x != v: return False
            elif x is not v: return False
        for nm, j in nd["calls"]:
            f = env.get(nm); t = nodes[j]
            if not (isinstance(f, Closure) and f.body is t["body"] and f.env is t["env"] and not f.args and not f.dead and f.native is None): return False
    return True
def _pure_same_reentry(tb):
    """速い道の再帰が Python の上限で止まったとき、積まれた呼びの中に、同じ関数が同じ実引数で入れ子になっている所があるか(あれば、同じ呼びを答えの途中でもう一度呼ぶ止まらない輪)。List は長さと同一性で見る。"""
    seen = set()
    while tb is not None:
        fr = tb.tb_frame; co = fr.f_code
        if co.co_name[:1] == "F" and co.co_filename.startswith("<"):
            loc = fr.f_locals
            key = (co, tuple((len(v), id(v)) if type(v) is list else v for v in (loc.get(n) for n in co.co_varnames[:co.co_argcount])))
            if key in seen: return True
            seen.add(key)
        tb = tb.tb_next
    return False
_PROBE_FREE = 2                                 # 同じ入れ子が見つからないまま深い再帰を 2 回見た計画は、以後ためさない
def _pure_probe(plan, g, st, ov, lg):
    """速い道を呼ぶ。再帰が止まらない輪だと Python の上限(約 20 万段)まで潜って時間を使うので、まず浅い上限(今の深さ + 4000 段)で走らせ、超えたときだけ積まれた呼びに同じ入れ子があるかを見る。あれば普通の道へ回す(そこで止まる輪が見つかる)。なければ上限を戻して走らせ直す。"""
    rl = sys.getrecursionlimit(); nl = DEPTH[0] * 40 + 4000
    if st[2] >= _PROBE_FREE or nl >= rl: return plan[1](*g.args)
    try: sys.setrecursionlimit(nl)
    except RecursionError: return plan[1](*g.args)
    try:
        try: return plan[1](*g.args)
        finally: sys.setrecursionlimit(rl)
    except RecursionError as e:
        same = _pure_same_reentry(e.__traceback__)
        e.__traceback__ = None
        ov.clear(); lg.clear()
        if same: raise _PureBail()
        st[2] += 1
    return plan[1](*g.args)
def run_pure(g):
    """g(整数か整数だけの List の実引数が全部そろった)を Python の関数で計算する。対象外・決まらないときは None(呼び側が普通の道で最初から)。
    書き込みは差分表に溜め、最後まで成功したときだけメモリへ反映する(決まらなければ全部捨てて、普通の道が最初から)。"""
    bs = PURE_BODYSTAT.get(id(g.body))
    if bs is not None and bs[0] is g.body and bs[1] >= 3 and not bs[2]: return None
    sig = ""; gw = False
    for a in g.args:
        t = type(a)
        if t is int: sig += "i"
        elif t is Addr: sig += "a"
        elif t is float:
            if a - a != 0: return None                # inf・nan は普通の道へ
            sig += "d"
        elif t is Char: sig += "d"; gw = True
        elif t is str and a: sig += "s"; gw = True
        elif t is list and a:
            if _allint(a): sig += "l"
            elif _allnum(a): sig += "M"
            elif _allgen(a): sig += "M"; gw = True
            elif _allstr(a): sig += "S"; gw = True
            else: return None
        else: return None
    plan = pure_plan(g, sig, gw)
    if not plan: return None
    ov = _PURE_OV; ov.clear(); lg = _PURE_LOG; lg.clear(); st = plan[2]
    try:
        r = _pure_probe(plan, g, st, ov, lg)
    except (_PureBail, RecursionError, ArithmeticError, TypeError, IndexError):
        ov.clear(); lg.clear(); st[1] += 1
        if st[1] > 16 and st[1] > 4 * st[0]: PURE_PLANS[(id(g.body), sig, gw)] = (g.body, False, g.env)      # 外れてばかりの物は諦める
        return None
    except BaseException:
        ov.clear(); lg.clear(); raise
    st[0] += 1
    if plan[0][0]["ret"] == "a" and r is not None: r = mk_addr(r)          # 番地を返す関数: 答えは Addr(域は _pa が見ている)
    if ov: MEMORY.update(ov); ov.clear()
    if lg:
        todo = lg[:]; lg.clear()
        for d, off, v in todo: d.write(off, v)           # 装置への書き込みは、書いた順にここで再生する
    return UNIT if r is None else r

class OutOfFuel(BaseException): pass            # sign_pe の静的評価が燃料を使い切った(SignError ではないので、途中で握りつぶされない)
FUEL = [None]                                   # None なら数えない。静的評価の間だけ整数

DOP = [False]                                   # R59: いま走らせている本体が `$` で開いた括りの関数か
def ends_with_stream(body):
    """本体の根(単一の値の行)が、撒いた流れ(`t~`)で終わる並びか"""
    n = body
    if n[0] == "cases":
        rows = [v for c, v in n[1] if c is None]
        if len(rows) != 1: return False
        n = rows[0]
    if n[0] == "block" and False: return False
    return n[0] == "seq" and bool(n[1]) and n[1][-1][0] == "post" and n[1][-1][1] == "~"

# ---- 整数だけの自己末尾再帰の輪(--opt なしでも効く。意味は同じで、Env・条件の行・TailCall を作らない) ----
LOOP_PLANS = {}
def loop_plan(g):
    """本体が (整数の比べ : 整数式 / 整数の比べ : 自分への呼び出し / 既定の行) だけなら、(仮引数名, 自分の名前, 行の表) を返す。違えば False。"""
    ent = LOOP_PLANS.get(id(g.body))
    if ent is not None and ent[0] is g.body: return ent[1]
    plan = False
    body = g.body
    try:
        if body[0] == "cases" and g.params and all(sp[0] == "name" and sp[2] is None for sp in g.params) and not g.variadic:
            ps = [sp[1] for sp in g.params]; rows = body[1]; me = None; table = []
            ok = bool(rows) and rows[-1][0] is None and all(c is not None for c, _ in rows[:-1])
            for c, e in (rows if ok else []):
                if c is not None and not (c[0] == "cmp" and len(c[2]) == 1): ok = False; break
                while e[0] == "block" and not isinstance(e[1], list): e = e[1]
                if e[0] == "seq" and len(e[1]) == len(ps) + 1 and e[1][0][0] == "id" and e[1][0][1] not in ps:
                    if me not in (None, e[1][0][1]): ok = False; break
                    me = e[1][0][1]; table.append((c, "call", e[1][1:]))
                else: table.append((c, "val", e))
            if ok and me is not None: plan = (ps, me, table)
    except (IndexError, TypeError): plan = False
    LOOP_PLANS[id(g.body)] = (g.body, plan)
    return plan

def ei(n, vals, env):
    """loop_plan の式の値(整数)。整数と決まらなければ None。"""
    k = n[0]
    if k == "lit":
        v = n[1]
        return v if (type(v) is int and len(n) == 2) else None
    if k == "id":
        nm = n[1]
        if nm in vals: return vals[nm]
        e = env
        while e:
            if nm in e.vars:
                v = e.vars[nm]
                if type(v) is not int: return None
                return v
            e = e.parent
        return None
    if k == "block":
        return None if isinstance(n[1], list) else ei(n[1], vals, env)
    if k == "norm":                              # ||rest|| : 括りの残りの長さ(括りの輪が vals に置く)
        return vals.get("||" + n[1][1] + "||") if n[1][0] == "id" else None
    if k == "bin":
        op = n[1]
        if op == "+" or op == "-" or op == "*":
            a = ei(n[2], vals, env)
            if a is None: return None
            b = ei(n[3], vals, env)
            if b is None: return None
            _r = a + b if op == "+" else a - b if op == "-" else a * b
            if STRICT_GATES and type(_r) is int and (_r > INT_MAX or _r < -INT_MAX): return None        # V5: 溢れは _ なので普通の道へ
            return _r
    return None

def run_loop(g):
    """g(整数の実引数が全部そろった自己末尾再帰)を輪で走らせる。決まらなければ (None, 今の実引数) を返し、呼び側が普通の道で続ける。"""
    plan = loop_plan(g)
    if not plan: return None, None
    ps, me, table = plan
    f = g.env.get(me)
    if not (isinstance(f, Closure) and f.body is g.body and f.env is g.env and not f.args and not f.dead): return None, None
    vals = dict(zip(ps, g.args))
    idle = Idle() if FUEL[0] is None else None
    ic = 0
    while True:
        if STRICT_GATES: work_tick()
        ic += 1
        if idle is not None and (STRICT_GATES or ic & 63 == 0) and idle.step(tuple(vals[p] for p in ps)): idle_stop()      # 既定は 16 回に 1 回だけ調べる(同じ状態へ戻る輪は周期があるので、間引いても必ず見つかる。速さの費用を抑える)
        if FUEL[0] is not None:
            FUEL[0] -= 1
            if FUEL[0] < 0: raise OutOfFuel()
        for c, kind, x in table:
            if c is not None:
                a = ei(c[1][0], vals, g.env); b = ei(c[1][1], vals, g.env)
                if a is None or b is None: return None, [vals[p] for p in ps]
                op = c[2][0]
                ok = a < b if op == "<" else a <= b if op == "<=" else a > b if op == ">" else a >= b if op == ">=" else a == b if (op == "=" or op == "==") else a != b
                if not ok: continue
            if kind == "val":
                v = ei(x, vals, g.env)
                if v is None: return None, [vals[p] for p in ps]
                return v, None
            nv = [ei(a, vals, g.env) for a in x]
            if any(v is None for v in nv): return None, [vals[p] for p in ps]
            vals = dict(zip(ps, nv)); break
        else:
            return None, [vals[p] for p in ps]

# ---- 整数を ~ で足していく累積の輪: `build (n - 1) (acc~ n)` のように、器 acc が「自分への呼び出しの `acc~ 項…` の位置」と「答えとしての裸の acc」でしか現れない線形の自己末尾再帰 ----
#      acc は呼び出しごとに作り直さず、入口で1回だけ写した Python の list に足していく(2 乗が O(n) になる)。整数・空でない・普通の list でなければ普通の道へ戻る
LIST_PLANS = {}
def _mentions(n, name):
    if isinstance(n, tuple):
        if len(n) == 2 and n[0] == "id": return n[1] == name
        return any(_mentions(x, name) for x in n)
    if isinstance(n, list): return any(_mentions(x, name) for x in n)
    return False
def list_plan(g):
    ent = LIST_PLANS.get(id(g.body))
    if ent is not None and ent[0] is g.body: return ent[1]
    plan = False
    body = g.body
    try:
        if body[0] == "cases" and g.params and all(sp[0] == "name" and sp[2] is None for sp in g.params) and not g.variadic:
            ps = [sp[1] for sp in g.params]; rows = body[1]; me = None; table = []; ai = None
            ok = bool(rows) and rows[-1][0] is None and all(c is not None for c, _ in rows[:-1])
            for c, e in (rows if ok else []):
                if c is not None and (not (c[0] == "cmp" and len(c[2]) == 1)):
                    ok = False; break
                while e[0] == "block" and not isinstance(e[1], list): e = e[1]
                if e[0] == "seq" and len(e[1]) == len(ps) + 1 and e[1][0][0] == "id" and e[1][0][1] not in ps:
                    if me not in (None, e[1][0][1]): ok = False; break
                    me = e[1][0][1]; args = []
                    for k, a in enumerate(e[1][1:]):
                        while a[0] == "block" and not isinstance(a[1], list): a = a[1]
                        if a[0] == "seq" and len(a[1]) >= 2 and a[1][0][0] == "post" and a[1][0][1] == "~" and a[1][0][2] == ("id", ps[k]) and ai in (None, k):
                            ai = k; args.append(a[1][1:])
                        else: args.append(a)
                    table.append((c, "call", args))
                elif e[0] == "id" and e[1] in ps: table.append((c, "ret", e[1]))
                else: table.append((c, "val", e))
            if ok and me is not None and ai is not None:
                A = ps[ai]
                for c, kind, x in table:                  # acc は、足す位置と答えの位置にしか出ない
                    if c is not None and _mentions(c, A): ok = False
                    if kind == "val" and _mentions(x, A): ok = False
                    if kind == "ret" and x != A: ok = False       # 別の仮引数を答えにする行は、この輪では扱わない
                    if kind == "call":
                        for k, a in enumerate(x):
                            if k == ai:
                                if any(_mentions(t, A) for t in a): ok = False
                            elif _mentions(a, A): ok = False
                if ok: plan = (ps, me, table, ai)
    except (IndexError, TypeError): plan = False
    LIST_PLANS[id(g.body)] = (g.body, plan)
    return plan

def run_list_loop(g):
    plan = list_plan(g)
    if not plan: return None, None
    ps, me, table, ai = plan
    f = g.env.get(me)
    if not (isinstance(f, Closure) and f.body is g.body and f.env is g.env and not f.args and not f.dead): return None, None
    L = g.args[ai]
    if type(L) is list:
        if not L or set(map(type, L)) != {int}: return None, None
        L = list(L)                                       # 呼び側の list は触らない
    elif type(L) is not int: return None, None            # 1 つの整数は [x] ≅ x。最初に足す時に list になる
    for k, a in enumerate(g.args):
        if k != ai and type(a) is not int: return None, None
    A = ps[ai]
    vals = {p: a for p, a in zip(ps, g.args) if p != A}
    def cur(): return [L if p == A else vals[p] for p in ps]
    while True:
        if FUEL[0] is not None:
            FUEL[0] -= 1
            if FUEL[0] < 0: raise OutOfFuel()
        for c, kind, x in table:
            if c is not None:
                a = ei(c[1][0], vals, g.env); b = ei(c[1][1], vals, g.env)
                if a is None or b is None: return None, cur()
                op = c[2][0]
                ok = a < b if op == "<" else a <= b if op == "<=" else a > b if op == ">" else a >= b if op == ">=" else a == b if (op == "=" or op == "==") else a != b
                if not ok: continue
            if kind == "ret": return L, None
            if kind == "val":
                v = ei(x, vals, g.env)
                if v is None: return None, cur()
                return v, None
            nv = {}
            for k, a in enumerate(x):
                if k == ai: continue
                v = ei(a, vals, g.env)
                if v is None: return None, cur()
                nv[ps[k]] = v
            ts = [ei(t, vals, g.env) for t in x[ai]]
            if any(t is None for t in ts): return None, cur()
            if type(L) is int: L = [L]
            L.extend(ts); vals = nv; break
        else:
            return None, cur()

# ---- 括りの残りを舐める自己末尾再帰の輪: `sumx : [x ~xs] acc ? ||xs|| = 0 : acc + x ⏎ sumx xs (acc + x)` ----
#      残り xs を毎回切り出さず、元の list の上の位置を進める(2 乗が O(n) になる)。要素が整数でなければ、その位置からの切り出しで普通の道へ戻る
DESTR_PLANS = {}
def destr_plan(g):
    ent = DESTR_PLANS.get(id(g.body))
    if ent is not None and ent[0] is g.body: return ent[1]
    plan = False
    body = g.body
    try:
        di = [i for i, sp in enumerate(g.params) if sp[0] == "destr"] if g.params else []
        if (body[0] == "cases" and len(di) == 1 and not g.variadic
                and all(sp[0] == "destr" or (sp[0] == "name" and sp[2] is None) for sp in g.params)):
            di = di[0]; sp = g.params[di]
            names, rest = sp[1], sp[2]
            if rest and names and not sp[3] and not (len(sp) > 4 and sp[4]):
                ps = [q[1] if q[0] == "name" else None for q in g.params]
                rows = body[1]; me = None; table = []
                ok = bool(rows) and rows[-1][0] is None and all(c is not None for c, _ in rows[:-1])
                for c, e in (rows if ok else []):
                    if c is not None and not (c[0] == "cmp" and len(c[2]) == 1): ok = False; break
                    while e[0] == "block" and not isinstance(e[1], list): e = e[1]
                    if e[0] == "seq" and len(e[1]) == len(ps) + 1 and e[1][0][0] == "id" and e[1][0][1] not in ps and e[1][0][1] not in names and e[1][0][1] != rest:
                        if me not in (None, e[1][0][1]): ok = False; break
                        args = []
                        for k, a in enumerate(e[1][1:]):
                            while a[0] == "block" and not isinstance(a[1], list): a = a[1]
                            if k == di:
                                if a != ("id", rest): ok = False
                            elif _mentions(a, rest): ok = False
                            args.append(a)
                        me = e[1][0][1]; table.append((c, "call", args))
                    else:
                        if _mentions_bare(e, rest): ok = False
                        table.append((c, "val", e))
                    if c is not None and _mentions_bare(c, rest): ok = False
                if ok and me is not None: plan = (ps, me, table, di, list(names), rest)
    except (IndexError, TypeError): plan = False
    DESTR_PLANS[id(g.body)] = (g.body, plan)
    return plan

def _mentions_bare(n, name):                   # `||name||` の外で name が現れるか
    if isinstance(n, tuple):
        if len(n) == 2 and n[0] == "norm" and n[1] == ("id", name): return False
        if len(n) == 2 and n[0] == "id": return n[1] == name
        return any(_mentions_bare(x, name) for x in n)
    if isinstance(n, list): return any(_mentions_bare(x, name) for x in n)
    return False

def run_destr_loop(g):
    plan = destr_plan(g)
    if not plan: return None, None
    ps, me, table, di, names, rest = plan
    f = g.env.get(me)
    if not (isinstance(f, Closure) and f.body is g.body and f.env is g.env and not f.args and not f.dead): return None, None
    L = g.args[di]
    if type(L) is not list or not L: return None, None
    for k, a in enumerate(g.args):
        if k != di and type(a) is not int: return None, None
    nb, key = len(names), "||" + rest + "||"
    pos = 0
    vals = {p: a for p, a in zip(ps, g.args) if p is not None}
    def cur(): return [L[pos:] if i == di else vals[p] for i, p in enumerate(ps)]
    while True:
        if FUEL[0] is not None:
            FUEL[0] -= 1
            if FUEL[0] < 0: raise OutOfFuel()
        left = len(L) - pos
        if left < nb: return None, cur()
        es = L[pos:pos + nb]
        if set(map(type, es)) != {int}: return None, cur()
        for nm, e in zip(names, es): vals[nm] = e
        vals[key] = left - nb
        for c, kind, x in table:
            if c is not None:
                a = ei(c[1][0], vals, g.env); b = ei(c[1][1], vals, g.env)
                if a is None or b is None: return None, cur()
                op = c[2][0]
                ok = a < b if op == "<" else a <= b if op == "<=" else a > b if op == ">" else a >= b if op == ">=" else a == b if (op == "=" or op == "==") else a != b
                if not ok: continue
            if kind == "val":
                v = ei(x, vals, g.env)
                if v is None: return None, cur()
                return v, None
            nv = {}
            for k, a in enumerate(x):
                if k == di: continue
                v = ei(a, vals, g.env)
                if v is None: return None, cur()
                nv[ps[k]] = v
            pos += nb
            if pos >= len(L): return UNIT, None           # 残りが空 = _ を渡す呼び出し(完全性公理で _)
            vals = nv; break
        else:
            return None, cur()

class WorkLimit(BaseException):                # value_spec V10: 1行の計算の量の上限(実装の都合で `_` にせず、重かった行を名指しして止める。途中で握りつぶされない BaseException)
    pass
WORK = [0]
EFFECTS = [0]                                  # 副作用(組み込みの呼び出し・メモリの書き込み・`@` の読み)の回数。数が動いた間は「同じ状態へ戻った」と言わない
class Idle:
    """value_spec V10: 末尾の輪が前に通った状態(関数と実引数)へ戻れば止まらない輪(アイドル)。Brent の方法で、メモリ O(1) で見つける。"""
    __slots__ = ("saved", "eff", "power", "lam")
    def __init__(self): self.saved = None; self.eff = -1; self.power = 1; self.lam = 0
    def step(self, state):
        if self.saved is not None and self.eff == EFFECTS[0] and self.saved == state: return True
        self.lam += 1
        if self.saved is None or self.lam >= self.power or self.eff != EFFECTS[0]:
            self.saved, self.eff = state, EFFECTS[0]
            if self.lam >= self.power: self.power *= 2
            self.lam = 0
        return False
class _IdRef:
    """同じ物かどうか(同一性)だけで等しい鍵。物への参照を持つので、解放された物の id が別の物に使い回されて偶然等しくなることがない"""
    __slots__ = ("o",)
    def __init__(self, o): self.o = o
    def __eq__(self, other): return type(other) is _IdRef and other.o is self.o
    def __hash__(self): return id(self.o)
def state_key(x):
    t = type(x)
    if t in (int, float, str, bool): return (t, x)
    if x is UNIT: return "_"
    if t is list or t is tuple: return tuple(state_key(y) for y in x)
    if isinstance(x, list) and not isinstance(x, Vec) and len(x) <= 256: return ("L",) + tuple(state_key(y) for y in x)      # 長さを持つ器(WLen など)も中身で比べる
    return _IdRef(x)
ACTIVE = {}                                    # 答えを出している途中の呼び出し: 鍵 → そのときの EFFECTS
def idle_stop(what="末尾の輪が前に通った状態(同じ関数・同じ実引数)へ戻りました。止まらない輪(アイドル)です"):
    ln = ROW_LINE[0]
    raise WorkLimit(f"interpret-not-yet: {str(ln) + ' 行目の' if ln else ''}{what}。この実装は輪を回さずに止めます(V10・V12。`_` は返しません)")
ROW_LINE = [None]                             # 走らせているファイルのいちばん外の行(V10: 重かった行はこれを名指しする)
WORK_LIMIT = [int(os.environ.get("SIGN_WORK_LIMIT", "5000000"))]
def work_tick():
    if STRICT_GATES and FUEL[0] is None:
        WORK[0] += 1
        if WORK[0] > WORK_LIMIT[0]:
            ln = ROW_LINE[0]
            raise WorkLimit(f"interpret-work-limit: {str(ln) + ' 行目の' if ln else ''}計算の量が上限({WORK_LIMIT[0]:,} 回)に届きました。止まらない輪かもしれません(末尾の輪が同じ状態へ戻らない形。V10)")
DEPTH = [0]                                    # 末尾でない呼び出しの入れ子の深さ(--strict。value_spec V10)
DEPTH_LIMIT = [0]                              # 上限(実装の都合。再帰の上限から決める)。0 は未計算
def depth_limit():
    if not DEPTH_LIMIT[0]: DEPTH_LIMIT[0] = max(40, (sys.getrecursionlimit() - 400) // 32)
    return DEPTH_LIMIT[0]
def run_fixed(g):
    _saved = DOP[0]; DOP[0] = g.dop
    _nf = NOFILL[0]; NOFILL[0] = False                       # 本体の根は評価する所(R107)
    if STRICT_GATES:
        d = DEPTH[0]
        if d >= depth_limit():                               # V10: 入れ子の深さが上限に届けば、その呼び出しは _ と information(Python のスタックの溢れに頼らない)
            DOP[0] = _saved; NOFILL[0] = _nf
            info("resource-depth", f"入れ子の深さが上限({depth_limit()} 段)に届いたので、この呼び出しは _ です(V10・V11)。再帰は末尾の呼び出しにすると深さを使いません")
            return UNIT
        akey = None
        if FUEL[0] is None and not g.native:                 # V10: 答えを出している途中の呼び出しを、同じ関数・同じ実引数でもう一度呼ぶ輪(呼び出しは関数と実引数で決まる)
            akey = (id(g.body), id(g.env), state_key(g.args))
            if ACTIVE.get(akey) == EFFECTS[0]: idle_stop("答えを出している途中の呼び出しを、同じ関数・同じ実引数でもう一度呼びました")
            if akey not in ACTIVE: ACTIVE[akey] = EFFECTS[0]
            else: akey = None
        DEPTH[0] = d + 1
        _cl = CURLINE[0]; pb_ = POS.get(id(g.body))
        if pb_: CURLINE[0] = pb_[1]                          # R127: 関数の本体の中で生まれた知らせは本体の行
        try: return run_fixed_(g)
        finally:
            DEPTH[0] = d; DOP[0] = _saved; NOFILL[0] = _nf; CURLINE[0] = _cl
            if akey is not None: ACTIVE.pop(akey, None)
    akey = None                                              # 既定でも V10 の「止まらない輪の検出」は同じ(答えを出している途中の呼び出しを、同じ関数・同じ実引数・同じ効果の数でもう一度呼んだら止める)。ただし入れ子の深さが 8 の倍数の呼び出しだけを控える(同じ呼び出しは周期で深さを下りながら戻るので、8 周期のうちに必ず見つかる。呼び出しごとの費用を抑える)
    d = DEPTH[0]; DEPTH[0] = d + 1
    if not d & 7 and FUEL[0] is None and not g.native:
        akey = (id(g.body), id(g.env), state_key(g.args))
        if ACTIVE.get(akey) == EFFECTS[0]: DEPTH[0] = d; idle_stop("答えを出している途中の呼び出しを、同じ関数・同じ実引数でもう一度呼びました")
        if akey not in ACTIVE: ACTIVE[akey] = EFFECTS[0]
        else: akey = None
    try: return run_fixed_(g)
    finally:
        DEPTH[0] = d; DOP[0] = _saved; NOFILL[0] = _nf
        if akey is not None: ACTIVE.pop(akey, None)

def _argkind(ga):
    k = 0
    for a in ga:
        t = type(a)
        if t is not int:
            if t is list: k = 1
            else: return 2
    return k
def run_fixed_(g):
    hops = 0
    pg = None
    tried = False
    tried2 = False
    idle = Idle() if FUEL[0] is None else None
    while True:
        if STRICT_GATES: work_tick()
        if FUEL[0] is not None:
            FUEL[0] -= 1
            if FUEL[0] < 0: raise OutOfFuel()
        if g.native: EFFECTS[0] += 1; r = g.native(*g.args)
        else:
            if g.acc is not None and len(g.args) == len(g.params) and all(type(a) is int for a in g.args):     # アキュムレータ導入: 整数だけなら累積版の末尾再帰へ(結合律が確かに成り立つ所だけ)
                e2 = Env(g.env); hl = g.acc[0]
                h = Closure(params=hl[1], body=hl[2], env=e2); e2.set(g.acc[1], h)       # 累積版は呼ぶ時に作る(自分への再帰は名前で戻る)
                for a in list(g.args) + [g.acc[2]]: h = apply(h, a)
                return h
            if FAST[0] and g.params and not DECL_USED[0] and not OVERRIDES and not g.dop and len(g.args) == len(g.params):
                kd = _argkind(g.args)                         # 実引数が全部整数なら 0、整数と list だけなら 1、それ以外は 2(1回の走査で3つの検査を済ませる)
                if kd <= 1 and not tried2 and not STRICT_GATES:
                    tried2 = True                             # 整数を ~ で足していく累積の輪(list は入口で1回だけ写す)
                    for _lp in (run_list_loop, run_destr_loop):
                        v, cur = _lp(g)
                        if v is not None: return v
                        if cur is not None: g = _cp(g, args=cur); kd = _argkind(g.args); break
                if kd == 0 and not tried and len(g.args) == len(g.params):
                    tried = True
                    v, cur = run_loop(g)
                    if v is not None: return v
                    if cur is not None: g = _cp(g, args=cur); kd = _argkind(g.args)        # 輪の途中で整数と決まらなくなった所から、普通の道で続ける
                if kd <= 2 and PURE[0] and g is not pg and not STRICT_GATES and FUEL[0] is None and len(g.args) == len(g.params):
                    pg = g
                    v = PAR[0].run_pure(g) if PAR[0] is not None else run_pure(g)
                    if v is not None: return v
            env = Env(g.env)
            for i, spec in enumerate(g.params):
                a = g.args[i] if i < len(g.args) else UNIT
                if spec[0] == "name":
                    if spec[2] is not None and is_unit(a):   # 省略 or __ → デフォルト式を評価(let*: 先行引数が見える)
                        a = ev(spec[2], env)
                        if isinstance(a, OpenRange) and i == len(g.params) - 1 and not g.dop:       # stack_abi §3.3: 既定値が開端レンジのカウンタ口。本体が繰り返され、c は回ごとに次の値。値を返した回で抜ける(再帰の底と同じ)
                            x = a.start
                            while True:
                                r = run_fixed(_cp(g, args=list(g.args[:i]) + [x]))
                                if not is_unit(r) and not (isinstance(r, Stream) and not r): return r
                                x = a.next(x)
                    env.set(spec[1], a)
                    if STRICT_GATES and not isinstance(a, (Ref, VarRef, LaneRef, Lift)): env.__dict__.setdefault("bare", set()).add(spec[1])      # 裸の仮引数は形を見ない(R24・R81)
                else:
                    if STRICT_GATES and spec[1] and isinstance(a, (list, str)) and not isinstance(a, Char) and len(a) == 0 and (i == len(g.params) - 1 or spec[2]):
                        if i in g.__dict__.get("uidx", ()): trial_read_body(g, spec, env)
                        return UNIT                      # R64・R122: 空の器で本体を読まないのは、最後の括りと残りを受ける括りだけ。ほかは空で席を取り、名前は全部 _
                    if STRICT_GATES and DEPTH_GATE[0]: depth_gate(a)
                    bind_destr(spec, a, env)         # 括り仮引数: 1個の実引数を分割代入
                    if STRICT_GATES and g.__dict__.get("hid") and i in g.hid: env.__dict__.setdefault("hid", set()).update(g.hid[i])        # R99・R100: 形の見えない値を受けた名前
            body = local_defs_body(g.body) if g.body[0] == "cases" else g.body
            _nw = len(WARNINGS)
            try: r = ev_place(body, env, TCO)
            except SignError as e: raise locate(e, g.body)
            if STRICT_GATES and ((len(WARNINGS) > _nw and any(w[0] == "leftover-lambda" for w in WARNINGS[_nw:])) or (isinstance(r, Closure) and not r.dead and r.params is not None and (r.variadic or len(r.args) < len(r.params)))) and any(sp[0] == "destr" for sp in g.params) and ends_with_stream(g.body):
                if g.__dict__.get("uidx") and isinstance(r, Closure) and r.params is not None and len(r.params) - len(r.args) >= 3: strict_gate("G19: 撒いた並び x~ を受ける関数の口が1つか2つに決まりません(計算の `!_` を撒いた流れは、読む段では空と分からず流れの1項。R84・R51)。要素を書き並べるか、括りの関数の最後の口で受けてください")
                strict_gate("G16: 括りの関数の実体の本体の根が、空の流れ(書いた `_` と同じ)で口の開いた関数のままです(`k2 : [~t] ? inc t~` ⏎ `k2 []`。R84)。関数を返すなら `$` を明示します。空の List は `[]` と書かずに `_` と書きます。すぐ List にしたいなら `,` で組みます(R109)", g.body)
        if type(r) is TailCall:
            g, hops = r.g, hops + 1
            if STRICT_GATES:
                _pb = POS.get(id(g.body))
                if _pb: CURLINE[0] = _pb[1]                       # R127: 末尾の呼びで本体が替わったら、その本体の書いた行
            if idle is not None and (STRICT_GATES or hops & 63 == 0) and idle.step((id(g.body), id(g.env), state_key(g.args))): idle_stop()
            continue
        if STRICT_GATES and isinstance(r, Closure) and r.ru:
            if g.dop: strict_gate("G20: `$` で開いた関数を呼んだ形で、本体に値の上に積まれて余る関数があります。1つの関数と言い切れません(R59)。関数を値として並べる・渡すなら `$inc` のように `$` を付けて表明します(ほかは `$[…]`)", g.body)
            warn("leftover-lambda", LEFTOVER_MSG); r = UNIT       # R42・R65: 本体の根で口を開けたまま残った関数は _
        if STRICT_GATES and not g.native and isinstance(r, Closure) and not r.dead and r is not ID:        # R125: 本体の返す所に残った裸の関数は _(G16 は廃止)
            info("bare-function-return", BARE_RETURN_MSG); r = UNIT
        if STRICT_GATES and not g.native and (isinstance(r, Struct) or (isinstance(r, list) and not isinstance(r, str) and any(isinstance(x, Struct) for x in r))) and r:
            root_ = g.env                                              # R125: 返す値に運ばれる構造体の欄に、呼ぶごとに作られた関数(仮引数を中で使う区間・`?` の括りほか)が残れば `!_`
            while root_ is not None and root_.parent is not None: root_ = root_.parent
            named_ = {id(v) for v in (root_.vars.values() if root_ is not None else ())}
            vf_ = VARY_FIELDS.get(id(g.body))
            vary_ = vf_[1] if vf_ is not None and vf_[0] is g.body else set()
            def strip_(st_):
                bad_ = [k_ for k_, v_ in st_.items() if isinstance(v_, Closure) and not v_.dead and v_ is not ID and id(v_) not in named_ and not const_closure(v_)]
                quiet_ = [k_ for k_, v_ in st_.items() if k_ in vary_ and k_ not in bad_ and isinstance(v_, Closure)]      # 読む段が知らせた欄(R125)
                if not bad_ and not quiet_: return st_
                if bad_: info("bare-function-return", BARE_RETURN_MSG + f"(返す構造体の欄 {', '.join(bad_)})")
                st2_ = Struct((k_, v_) for k_, v_ in st_.items() if k_ not in bad_ and k_ not in quiet_); return st2_ if st2_ else UNIT
            if isinstance(r, Struct): r = strip_(r)
            else:
                r2_ = [strip_(x) if isinstance(x, Struct) else x for x in r]
                r2_ = [x for x in r2_ if not is_unit(x)]
                r = type(r)(r2_) if r2_ else UNIT
        if STRICT_GATES and not g.native and isinstance(r, RowList):          # R125(2026-11-17 の仕様): 本体に書いた List の行に1つだけ残った裸の関数は、仮引数を使わず1つの関数に決まるなら(定数の点)関数のまま返り、使うなら `!_`
            bad_rows_ = [x for x in r if isinstance(x, Closure) and not x.dead and x is not ID and not const_closure(x)]
            if id(g.body) in VARY_ROWS:
                r = type(r)(x for x in r if not (isinstance(x, Closure) and not x.dead)); r = r if r else UNIT
            elif bad_rows_:
                info("bare-function-return", BARE_RETURN_MSG + "(本体に書いた List の行。仮引数を中で使う関数は `!_`)")
                r = type(r)(x for x in r if not any(x is b_ for b_ in bad_rows_)); r = r if r else UNIT
        return finalize(r) if hops else r

_SI = {}
def seq_special(n):                            # 並びに書いた _・!_・取り込みが混ざるか(節ごとに1度だけ数える。id の使い回しは節そのものの同一性で防ぐ)
    ent = _SI.get(id(n))
    if ent is None or ent[0] is not n:
        items = n[1]
        ent = (n, len(items) < 2 or any(m == MARK or m == HOLE or m[0] == "input" for m in items)); _SI[id(n)] = ent
    return ent[1]
def _has_fn_stream(vals):                       # 先頭以外に関数か流れがあるか(生成式を作らず走査する)
    for i in range(1, len(vals)):
        if isinstance(vals[i], (Closure, Stream)): return True
    return False
def _tail_chain_ok(n, env):
    """`,` の鎖の最後が呼び出し(口が足りる)で、前が2つ以上ありそうか(評価はしない)"""
    if n[0] == "block": n = n[1]
    return n[0] == "prod" and len(n[1]) >= 3 and n[1][-1][0] in ("seq", "block")
def _tail_comma_chain(n, env):
    """value_spec V10(2026-11-17 21:30): `,` の鎖に前の関数が2つ以上あれば、呼んだ答えが `!_` でも行の答えは呼んだ答えそのもの。
    なので最後の呼び出しは返す所で、末尾呼び出し(`lq : n ? (n < 1 & 9) | (inc , double , (add 1 , lq (n - 1)))` は何段でも 9)。
    最後の項が括った `,` の鎖ならその最後の呼び出しまで平らに見る。前の辺は今までどおり評価して、消える関数の知らせを出す。"""
    items = list(n[1]); chain = []
    while True:
        last = items[-1]
        if last[0] == "block" and last[1][0] == "prod" and len(last[1][1]) >= 2:
            chain += items[:-1]; items = list(last[1][1]); continue
        if last[0] == "block" and last[1][0] == "seq" and len(last[1][1]) >= 2:
            last = last[1]
        chain += items[:-1]; break
    if last[0] != "seq" or len(last[1]) < 2 or last[1][0][0] != "id" or any(m in (MARK, HOLE) for m in last[1]): return None
    try: f = env.get(last[1][0][1])
    except Exception: return None
    if not (isinstance(f, Closure) and f.native is None and not f.variadic and f.params is not None and not f.dead
            and len(f.args) + len(last[1]) - 1 == len(f.params)): return None
    if any(m[0] == "post" or m == MARK or m == HOLE or m == ("not", ("hole",)) for m in chain): return None
    edges = []
    for m in chain:
        v = ev(m, env)
        if not isinstance(v, Closure) or v is ID or v.dead: return None
        edges.append(v)
    if len(edges) < 2: return None
    for v in edges: drop_fn_edge("(`,` の被演算子。関数を積の要素にするなら `$inc , 2`、当てるなら `(inc 1) , 2`。R61)", FnEdge(v))
    NOREG[0] = False
    r = ev_tail(last, env)
    return r

def ev_tail(n, env):
    """本体を、末尾の位置だけ「呼ぶ代わりに TailCall を返す」形で評価する。
    末尾の位置: cases の選ばれた行の値・括り・並び。並びは、先頭が仮引数を持つ関数で、値の実引数がちょうど口の数だけのときだけ。"""
    k = n[0]
    if STRICT_GATES:
        if NOREG[0]: NOREG[0] = False                       # 括りを通った中の並びは評価する所に数えない(R110、括りの中は G7)
        else: eval_place(n)
    if k == "cases":
        rows_ = n[1]
        for i_, (cond, expr) in enumerate(rows_):
            if STRICT_GATES:
                _p = POS.get(id(cond)) if cond is not None else None
                _p = _p or POS.get(id(expr))
                if _p: CURLINE[0] = _p[1]                          # R127
            if cond is None or not is_unit(cond_value(cond, env)):
                expr, e2 = field_block(expr, env)
                if cond is None or i_ == len(rows_) - 1: return ev_tail(expr, e2)       # 既定の行と最後の枝の値は末尾
                v = ev(expr, e2)                                                         # R128: 最後でない枝の値は末尾でない(`c & v | 次の行` の v)。`_` なら消えて次へ進む
                if STRICT_GATES and (is_unit(v) or branch_bare(v)): continue
                return v
        return UNIT
    if k == "bin" and STRICT_GATES and len(n) == 4 and n[1] == "|" and (n[3][0] == "prod" or (n[3][0] == "block" and n[3][1][0] == "prod")) and _tail_chain_ok(n[3], env):
        lv = ev(n[2], env)                                        # 左が単位でなければ左(右は評価しない)。単位なら右の `,` の鎖の最後の呼び出しが返す所
        if is_unit(lv):
            r_ = _tail_comma_chain(n[3][1] if n[3][0] == "block" else n[3], env)
            if r_ is not None: return r_
        elif not isinstance(lv, (Closure, Stream)) and lv is not ABS: return lv
    if k == "prod" and STRICT_GATES and len(n[1]) >= 3:
        r_ = _tail_comma_chain(n, env)
        if r_ is not None: return r_
    if k == "proc": return ev_proc(n[1], env, True)
    if k == "block" and n[1][0] != "id":
        if STRICT_GATES and n[1][0] == "seq": NOREG[0] = True
        return ev_tail(n[1], env)
    if k == "seq":
        items = n[1]
        if STRICT_GATES and any(m[0] == "post" and m[1] == "~" for m in items):
            if STRICT_GATES: r90_stream_gate(items, env)
            _w = r84_whole(items, env)
            if _w is not None: return ev(("seq", _w), env)
            _it = empty_streams_to_marks(items, env)                  # R84: 空の流れは書いた `_` と同じ印(本体の根でも)
            if _it != list(items): return ev(("seq", _it), env)
        if seq_special(n): return ev(n, env)
        vals = [ev_head(m, env) if i == 0 else ev(m, env) for i, m in enumerate(items)]
        f = vals[0]
        if STRICT_GATES and type(f) is Closure and not any(m == MARK or m == HOLE for m in items): f = vals[0] = hid_tag(f, items, env)
        if (isinstance(f, Closure) and f.native is None and not f.variadic and f.params is not None
                and len(f.args) + len(vals) - 1 == len(f.params)
                and not _has_fn_stream(vals)):
            if STRICT_GATES and not f.dead and any(is_unit(x) for x in vals[1:]) and not any(slot_optional(sp) for sp in f.params):
                # R83: 値の口に来た `!_` は消えて口を使わない(`f !_` は f)。口が残った関数は返す所の裸の関数で `!_`(R125・R136)。評価した実引数は読み直さない
                info("bare-function-return", BARE_RETURN_MSG + "(実引数が `!_` で消え、関数が口を開けたまま返る所に残りました。R83・R136)")
                return UNIT
            dead, got = f.dead, list(f.args)
            for x in vals[1:]:
                spec = f.params[len(got)]
                optional = slot_optional(spec)
                dead = dead or (is_unit(x) and not optional); got.append(x)
            return UNIT if dead else TailCall(_cp(f, args=got, dead=dead))
        if not STRICT_GATES and len(vals) == 2 and not isinstance(f, (Closure, Stream)) and not is_unit(f):           # 逆適用 `x f` の末尾も末尾呼び出し(10 万段でも溢れない)
            g = vals[1]
            if (isinstance(g, Closure) and g.native is None and not g.variadic and g.params is not None and not g.pf and not g.alias and not g.dead
                    and len(g.args) + 1 == len(g.params) and not slot_optional(g.params[len(g.args)])):
                return TailCall(_cp(g, args=list(g.args) + [f]))
        try: return ev_seq(items, env, vals)
        except SignError as e:
            if getattr(e, "empty_stream", False) and not hasattr(e, "node"): e.node = n
            raise locate(e, n)
    return ev(n, env)

STREAM_FEED = [False]                       # R91: 撒いた流れの要素を1つずつ当てている最中(長さは書いた時点では分からない)
def hid_of_node(m, env):
    """R99・R100(2026-11-07): 括りの関数の実体に渡された物の「形が見えない」か。True / False / 要素ごとの list。
    形の見えない値 = 適用の結果・計算・形の見えない仮引数を受けた名前。字面・形の見える名前・`$` の項は見える。括った並びは要素ごと。"""
    k = m[0]
    if k in ("lit", "hole", "addr", "lift", "not"): return False
    if k == "post" and m[1] == "~" and isinstance(m[2], tuple): return hid_of_node(m[2], env)          # 流れに撒く `t~`: 要素の形は t と同じ
    if k == "id":
        e = env.owner(m[1])
        if e is None: return False
        d = e.__dict__
        return m[1] in d.get("hid", ()) or m[1] in d.get("bare", ())
    if k == "block":
        inner = m[1]
        if isinstance(inner, tuple) and inner and inner[0] == "prod": return [hid_of_node(x, env) for x in inner[1]]
        if isinstance(inner, tuple) and inner and inner[0] == "seq":
            its = inner[1]
            if its and its[0][0] == "id":
                try:
                    if isinstance(env.get(its[0][1]), Closure): return True           # 適用(関数が頭): 結果の形は見えない
                except Exception: return True
            return [hid_of_node(x, env) for x in its]
        return hid_of_node(inner, env) if isinstance(inner, tuple) and inner and inner[0] in ("id", "lit") else True
    return True
def hid_names(spec, h):
    """括りの仮引数 spec(("destr", names, rest, ...))のうち、形が見えない名前の集まり。h は hid_of_node の結果"""
    names, rest = list(spec[1]), spec[2]
    if h is False: return set()
    if h is True: return set(names) | ({rest} if rest else set())
    out = {nm for i, nm in enumerate(names) if i < len(h) and h[i]}
    if rest and any(h[len(names):]): out.add(rest)
    return out

def hid_tag(f, items, env):
    """括りの仮引数に、形の見えない値を渡す並び(`q x`・`p [(inc 5) (inc 5)]`)なら、どの名前が形の見えない値かを実体に持たせる(R99・R100)"""
    if f.params is None or f.variadic: return f
    old = f.__dict__.get("hid") or {}; hd = dict(old)
    for j in range(1, len(items)):
        pi = len(f.args) + j - 1
        if pi < len(f.params) and f.params[pi][0] == "destr":
            nm = hid_names(f.params[pi], hid_of_node(items[j], env))
            if nm: hd[pi] = nm
    return _cp(f, hid=hd) if hd and hd != old else f
def trial_read_body(g, spec, env):
    """R122: 計算の `!_` を空の器で受けた括りの関数は、値の段が本体を読まずに `!_` にするが、読む段(木の段)は空と分からず本体を読む。
    本体を、括りの名前を値(頭)と空の器(残り)として読み、書いた行の知らせだけを出す(値は捨てる。書き込みの無い本体だけ)"""
    if "#" in repr(g.body) or "input" in repr(g.body): return
    try:
        e2 = Env(g.env)
        for j, sp_ in enumerate(g.params):
            if j == len(g.args) - 1 or sp_ is spec: pass
        names = list(spec[1])
        for j, sp_ in enumerate(g.params):
            if sp_[0] == "name": e2.set(sp_[1], g.args[j] if j < len(g.args) else UNIT)
            elif sp_ is spec: bind_destr(sp_, [0] * len(names), e2)
            else: bind_destr(sp_, g.args[j] if j < len(g.args) else [], e2)
        _nf = NOFILL[0]; NOFILL[0] = False
        try: ev(g.body, e2)
        finally: NOFILL[0] = _nf
    except Exception: pass
def bind_destr(spec, a, env):
    names, rest = spec[1], spec[2]
    if STRICT_GATES and not rest and isinstance(a, list) and not isinstance(a, Struct) and len(a) > len(names) + len(spec[4] if len(spec) > 4 else []):
        warn("bracket-excess", "括りの名前の数より多い要素は受けません(積み直しません)。残りが欲しければ `[a b ~c]` と書きます(R64)")
    defaults = spec[3] if len(spec) > 3 else {}
    after = spec[4] if len(spec) > 4 else []
    if isinstance(a, Struct):                  # 構造体: 名前で束縛(順序は問わない)
        for n in names + after:
            v = a.get(n, UNIT)
            if is_unit(v) and n in defaults: v = ev(defaults[n], env)
            env.set(n, v)
        if rest:
            r = Struct(a)                                  # ~obj は渡した器そのもの(名前を挙げても減らない。list_model.md §5.2)
            env.set(rest, r if r else UNIT)
        return
    is_text = isinstance(a, str)                                  # String は文字のリスト(1文字の String ≅ Char)
    items = a if is_text else (a if type(a) is list else list(a) if isinstance(a, list) else [a])      # 普通の list は写さずに読む(items は書き換えない)。String も写さず、要る文字だけ Char にする
    nb, na, n_all = len(names), len(after), len(items)
    for k, n in enumerate(names):                                 # ~rest より前: 先頭から
        v = (Char(items[k]) if is_text else items[k]) if k < n_all else UNIT
        if is_unit(v) and n in defaults: v = ev(defaults[n], env)
        elif STRICT_GATES and k >= n_all and not is_text and (isinstance(a, WLen) or (isinstance(a, (int, float)) and not STREAM_FEED[0])):
            env.__dict__.setdefault("zeronames", set()).add(n)          # R91: 書いた時点で長さの分かる List(と数=長さ1)で足りない後ろの名前は木の段でも `_`(印 zero、R63)
        env.set(n, v)
    for k, n in enumerate(after):                                 # ~rest より後: 末尾から(pop / 両端)
        idx = n_all - na + k
        v = (Char(items[idx]) if is_text else items[idx]) if nb <= idx < n_all else UNIT
        env.set(n, v)
    if rest and isinstance(a, ZList) and not names: env.__dict__.setdefault("uncount", set()).add(rest)       # R90 残り
    if rest:
        mid = items[nb:n_all - na] if na else items[nb:]
        env.set(rest, mid if mid else UNIT)

def _hof_inner_mark(items, hof):               # R138: 穴を全部埋めた後ろの内側の `_`(後ろに値が続く)。並びの終わりの `_` は消えて通る
    n = 0
    for k, m in enumerate(items[1:], 1):
        if m == MARK:
            if n >= hof and any(x != MARK for x in items[k + 1:]): return True
        else: n += 1
    return False

def apply(f, x):
    if isinstance(x, Stream):                  # 後置 ~ は実引数として撒かれる
        items, i = list(x), 0
        if items and isinstance(f, Closure) and f.variadic:        # 可変長(`[+]` など)へ流れを撒くときは、1つずつ足さず(毎回 args を写して 2 乗になる)まとめて渡す
            g = _cp(f, args=f.args + items); g.sf = True; return g
        while i < len(items) and isinstance(f, Closure) and needs_more(f):
            _sf = STREAM_FEED[0]; STREAM_FEED[0] = True
            try: f = apply(f, items[i])
            finally: STREAM_FEED[0] = _sf
            i += 1
        if i < len(items): return close(join(f, Stream(items[i:])))      # 余りの実引数は値の右へ並ぶ([+ 1] 1 2 3 = [2 2 3])
        return f
    if f.variadic and STRICT_GATES and is_unit(x) and f.pf and not getattr(f, "foldsec", False) and not getattr(f, "nofold", False) and not f.args:
        return f                                                    # R137・R95: 点なしの可変長の口が受けた `!_` は項として消え、何も受けていない関数のまま残る(`[* 2,] w`)
    if f.variadic:
        g = _cp(f, args=f.args + [x]); g.sf = getattr(f, 'sf', False) or STREAM_FEED[0]; return g       # sf: 撒いた流れから来た実引数が混ざる(R91)
    spec = f.params[len(f.args)] if f.params is not None else None
    optional = spec is not None and slot_optional(spec)
    if STRICT_GATES and is_unit(x) and not optional and not isinstance(x, (list, Stream)):     # R65: 実行時に来た `_`
        if spec is not None and spec[0] == "destr":
            x = []                                                          # 参照の口には空の器で入る(位置はずれない)
            if not KNOWN_UNIT[0]: _uidx = len(f.args)
        else: return f if f.ru else _cp(f, ru=True)                         # 値の口では並びの単位として消える(口は開いたまま)
    g = _cp(f, args=f.args + [x], dead=f.dead or (is_unit(x) and not optional and not (STRICT_GATES and spec is not None and spec[0] == "destr")))
    if STRICT_GATES and "_uidx" in locals(): g.__dict__["uidx"] = set(f.__dict__.get("uidx", ())) | {_uidx}      # 計算の `!_` が空の器で入った口(木の段では空と分からず本体を読む。R122)
    if len(g.args) < arity(g): return g        # アリティ不足 → Lambda のまま(デフォルトは finalize で補う)
    return UNIT if g.dead else run_fixed(g)    # 完全性公理: __ を受けた呼び出しは __

def finalize(v):                               # 可変長・デフォルト引数付きは列の終わりで実行
    if isinstance(v, Closure):
        if v.variadic and v.args:
            _sf = STREAM_FEED[0]; STREAM_FEED[0] = _sf or getattr(v, 'sf', False)
            EFFECTS[0] += 1
            try: return v.native(v.args)
            finally: STREAM_FEED[0] = _sf
        if has_defaults(v) and v.args and len(v.args) >= required(v):
            if STRICT_GATES and NOFILL[0] and not v.dead and len(v.args) < len(v.params): return v if v.pd else _cp(v, pd=True)       # R107: 評価する所の外では埋めずに、部分適用のまま運ぶ
            return UNIT if v.dead else run_fixed(v)
    return v

NOFILL = [False]                                 # R107: いま畳んでいる並びが、評価する所の外か(外なら既定値を埋めない)
KEEP = [None]                                    # R107: この節の値は、既定値の部分適用のまま運ぶ(並びの頭・値の定義の右辺)
def fill_pd(v):
    g = _cp(v, pd=False)
    _nf = NOFILL[0]; NOFILL[0] = False
    try: return UNIT if g.dead else run_fixed(g)
    finally: NOFILL[0] = _nf

def run_with(f, args):
    for x in args: f = apply(f, x)
    return finalize(f)

def compose(f, g):                             # f g = 「f してから g」(左から実行)
    def second(r):
        if g.variadic: return run_with(g, list(r) if isinstance(r, list) else [r])
        return finalize(apply(g, r))
    c = (native_var(lambda args: second(run_with(f, args))) if f.variadic
         else native_fixed(lambda *xs: second(run_with(f, list(xs))), rem(f)))
    c.pf = f.pf or g.pf                                    # 点なしを含む合成は、点なしとして扱う
    c.parts = tuple(parts_of(f)) + tuple(parts_of(g))
    return c

def join(a, b):                                # Atom|List ⊙ Atom|List
    ea = is_unit(a) or a is ID or (isinstance(a, Stream) and not a)
    eb = is_unit(b) or b is ID or (isinstance(b, Stream) and not b)
    if ea: return b
    if eb: return a
    if isinstance(a, SpreadStruct) and isinstance(b, SpreadStruct): return MergedStruct({**a, **b})  # 構造体の結合(後勝ち。3つ以上も続けて繋がる)
    if isinstance(a, str) and isinstance(b, str): return "%s%s" % (a, b)                    # String は吸収元
    if isinstance(a, str) and is_num(b): return "%s%s" % (a, b)
    if isinstance(b, str) and is_num(a): return "%s%s" % (a, b)
    if isinstance(a, Open) and isinstance(b, str) and all(isinstance(x, str) or is_num(x) for x in a):
        return "".join("%s" % x for x in a) + str(b)                                         # 1 2 `34` = `1234`
    # list_model.md §2.2: 後置 ~ が付いた側だけが段を下ろして流れ込む。付いていない側は(器でも)1項。
    o = Open(a) if isinstance(a, (Stream, Open)) else Open((a,))        # 左を1回だけ写して、右を足す(left+right の組み立てで何度も写さない)
    if isinstance(b, Stream): o.extend(b)
    else: o.append(b)
    o.fs = isinstance(a, Stream) or isinstance(b, Stream) or getattr(a, "fs", False)       # R91: 撒いた流れが混ざった並びは長さが書いた時点では分からない
    return o

def close(v):
    if type(v) is MergedStruct: return Struct(v)
    if isinstance(v, Open):
        return list(v) if (not STRICT_GATES or getattr(v, "fs", False) or not v) else WLen(v)       # R91: 書き並べた行は書いた時点で長さが分かる
    return v          # 並置の途中経過を閉じた器にする

def couple(a, b):
    if STRICT_GATES: a, b = ru_unit(a), ru_unit(b)
    if isinstance(a, Closure) and isinstance(b, Closure): return compose(a, b)
    if isinstance(a, Closure): return apply(a, b)
    if isinstance(b, Closure): return UNIT if is_unit(a) else apply(b, a)   # 逆適用
    return close(join(a, b))

def last_is_group(f):                          # 残りの仮引数が、括りの1つだけか
    return (isinstance(f, Closure) and not f.variadic and f.params is not None
            and len(f.params) - len(f.args) == 1 and f.params[len(f.args)][0] == "destr")

def needs_more(f):                             # この1つを取ってもまだ要るか(デフォルト引数も数える)
    return f.variadic or arity(f) - len(f.args) >= 1

def reverse_apply(a, b):                       # x f : f が単項の素の関数のときだけ(R12)。それ以外は名指しで断る
    if isinstance(a, Stream): strict_gate("G9: 撒いた項 x~ を逆適用の左に置けません(`xs~ inc`)")
    return UNIT if is_unit(a) else apply(b, a)

def slots_left(f): return None if f.variadic else arity(f) - len(f.args)

def collector(f):                              # 最後の仮引数が括りの関数: 後ろの値を並びの終わりまで束ねて、1つの括りで受ける(R24・R41)
    def go(args):
        arg = args[0]
        for a in args[1:]: arg = join(arg, a)
        ca = close(arg)
        if STREAM_FEED[0] and type(ca) is WLen: ca = list(ca)
        return finalize(apply(f, ca))
    c = native_var(go); c.pf = f.pf
    return c

def empty_stream_gate(msg):
    g = Gate(msg); g.empty_stream = True; return g            # R84: 評価する所の根の並びの最後の項なら、余ったラムダで _ にする目印

DECL_USED = [False]                              # R80: 断る局所の名前(local-branch・local-shadow・local-twice・local-cycle)を使い始めたか
DECL_TEXT = {"local-branch": "枝のある本体の中の局所の定義の行で、枝の本体では局所の定義にならない",
             "local-shadow": "仮引数・外の定義と同じ名前の行で、局所の定義にならない",
             "local-twice": "同じ範囲に2つ定義されている",
             "local-field": "括り・ブロックの中の名前で、欄かもしれず、局所の定義にならない",
             "local-cycle": "局所の関数の再帰(自分を指す輪)の中の名前で、その中では未知になる"}
def declined_reason(env, name):
    e = env
    while e:
        d = getattr(e, "decl", None)
        if d and name in d: return d[name]
        if name in e.vars: return None
        e = e.parent
    return None
def decline(env, names, reason):
    d = env.__dict__.setdefault("decl", {})
    for nm in names: d[nm] = reason
    DECL_USED[0] = True
def local_refs(n, out, dollar):
    """局所の定義の輪を見るための参照集め: 名前 -> `$` で入った辺があるか"""
    if isinstance(n, list):
        for c in n: local_refs(c, out, dollar)
    elif isinstance(n, tuple) and n:
        if n[0] == "id": out.setdefault(n[1], False)
        elif n[0] == "addr" and n[1][0] == "id": out[n[1][1]] = True
        elif n[0] == "addr":                                  # R103: 持ち上げの中身を通る局所の輪も `$` の辺(局所の `$名前` の輪と同じ G20、§5 Q78 (b))
            inner = {}; local_refs(n[1], inner, dollar)
            for k2 in inner: out[k2] = True
        elif n[0] == "lam":
            inner = {}; local_refs(n[2], inner, dollar)
            ps = set()
            for sp in n[1]: ps |= {sp[1]} if sp[0] == "name" else set(sp[1]) | ({sp[2]} if sp[2] else set())
            for k2, v2 in inner.items():
                if k2 not in ps: out[k2] = out.get(k2, False) or v2
        else:
            for c in n[1:]: local_refs(c, out, dollar)
def addr_core(t):
    """R54・R101: `$` の項の囲み `[N]`・`(N)` と、`,` の単位(書いた `_`・`!_`・`~_`)を外した芯。1項に縮まなければそのまま返す。"""
    while isinstance(t, tuple) and t and t[0] == "block" and not isinstance(t[1], str): t = t[1]
    if isinstance(t, tuple) and t and t[0] == "prod":
        rest = [x for x in t[1] if not (x in (("hole",), ("not", ("hole",))) or (isinstance(x, tuple) and x and x[0] == "lift" and x[1] in (("hole",), ("not", ("hole",)))))]
        if len(rest) == 1 and len(rest) < len(t[1]): return addr_core(rest[0])
    return t
def has_addr_of(n, name):
    if isinstance(n, list): return any(has_addr_of(c, name) for c in n)
    if isinstance(n, tuple) and n:
        if n[0] == "addr" and (n[1] == ("id", name) or addr_core(n[1]) == ("id", name)): return True      # R54: `$[N]`・`$(N)` は `$N` と同じ先。`$[sq , _]` も(R101 の単位律で `$sq`)
        return any(has_addr_of(c, name) for c in n[1:])
    return False
def as_proc(rows):
    """R76: 枝の行の無い2行以上の本体は手続き `l1 & … & ln`。各行は評価する所(余った関数は _ で知らせる・括らない !_ だけの行は G7)"""
    if len(rows) >= 2 and all(c is None for c, _ in rows): return ("proc", [v for _, v in rows])      # 既定のモードも手続き(最初の行を黙って返さない)
    return ("cases", rows)
def ev_proc(lines, env, last_tail=False):
    for i, ln in enumerate(lines):
        if STRICT_GATES:
            _p = POS.get(id(ln))
            if _p: CURLINE[0] = _p[1]                            # R127
        # R29: 手続きの `_` だけの行は `i : _` の i を置いた行と同じ(最後でない行は R48 の leftover-lambda で `!_`)
        if last_tail and i == len(lines) - 1:
            r_ = ev_tail(ln, env)
            if STRICT_GATES and r_ is ID and len(lines) >= 2:         # R125・R29: 2行以上の手続きの最後の行に残った恒等射は返す所の裸の関数で `!_`
                info("bare-function-return", "手続きの最後の行(返す所)に恒等射が残り、`!_` を返します(§4 R125・R29)。値を返すなら値を書きます")
                return UNIT
            return r_
        v = id_operand(leftover_operand(ru_unit(ev(ln, env))), "手続きの最後でない行")
        if is_unit(v): return UNIT
    return v
def local_defs_body(body):
    """R128(2026-11-04 の寄せ1。R80 は廃止): 関数の本体の字下げのブロックの `:` の行は、左が名前1つでも条件の行(枝)で、名前を定義しない。
    本体に局所の定義は無い。局所の値は仮引数のブロック(既定値)へ置く。本体の中の名前は、仮引数・ファイルの定義・未定義の名前(`_`)のどれか。"""
    r = _LDB.get(id(body))
    if r is None or r[0] is not body:
        rows = body[1]
        r = _LDB[id(body)] = (body, any(c is not None for c, _ in rows))       # 本体の形だけで決まるので、本体ごとに 1 回だけ調べる
    if not r[1]: return as_proc(body[1])
    return body
_LDB = {}

def value_stacked(n, env):
    """R84: 並びの頭が値(関数でない)なら「値の上に積まれた所」。"""
    if n[0] != "seq": return False
    items = [m for m in n[1] if m != MARK]
    if len(items) < 2: return False
    h = items[0]
    if h[0] == "id":
        try: return not isinstance(env.get(h[1]), Closure)
        except Exception: return False
    return h[0] in ("lit", "block", "prod", "num", "str") or h[0] not in ("paren", "post", "lam", "hole")

NOREG = [False]
SECB = [None]
EVAL_ITEMS = {}                              # R107・R110: 評価する所(行の根・本体の根・枝の値・比べと論理の被演算子)の並びの項の表(id)
EVAL_PRODS = set()
KNOWN_UNIT = [False]                             # R122: いま畳んでいる並びに、`!_` と分かる実引数がある
def eval_place(n):
    if n[0] == "seq": EVAL_ITEMS[id(n[1])] = n[1]
    elif n[0] == "prod": EVAL_PRODS.add(id(n))
    elif n[0] == "bin" and n[1] in ("|", ";") and len(n) == 4: EVAL_PRODS.add(id(n))       # R137・V7: 評価する所の `|`・`;` の辺に1つだけ残った関数は `_`
def ev_place(n, env, tail=False, rhs=False):
    """評価する所(行の根・値の定義の右辺・本体の根)。R84: 空の流れを口が1つの関数へ渡して何も当たらずラムダが余ったら _(知らせる)。"""
    if STRICT_GATES and not rhs: eval_place(n)
    try:
        r = ev_tail(n, env) if tail else ev(n, env)
        return r
    except Gate as e:
        node = getattr(e, "node", None)
        if STRICT_GATES and getattr(e, "empty_stream", False) and node is not None and node[0] == "seq" and [m for m in node[1] if m != MARK][-1][:2] == ("post", "~") \
                and (node is n or n[0] == "cases") and (not rhs or value_stacked(n, env)):
            warn("leftover-lambda", LEFTOVER_MSG); return UNIT
        raise

def stream_feed(f, st):
    """撒いた並び x~ を、関数 f の残りの口の数で受ける(R51、2026-10-25 に決定): 口が2つなら左からの畳み込み、
    口が1つなら書き下し(頭を当てて段を閉じ、残りは後ろに積む。`inc vs~` は `(inc 1) 2 3`)。
    写像は `[f,]`(可変長の口)だけ。ほか(3つ以上・口の数が分からない・空の流れの書き下し)は G19。"""
    xs = list(st)
    n = slots_left(f)
    if n == 1:
        if not xs: raise empty_stream_gate("G19: 空の流れ x~ は、口が1つの関数に当てるか決まりません(`inc []~`)。書き並べるか、`[f,]` の写像にします")
        r = finalize(apply(f, xs[0]))
        for e in xs[1:]: r = join(r, e)                         # 残りは後ろに積む(書き並べと同じ並び)
        return r
    if n == 2:
        if not xs: return UNIT
        acc = xs[0]
        for e in xs[1:]: acc = finalize(apply(apply(f, acc), e))
        return acc
    raise Gate("G19: 撒いた並び x~ を受ける関数の口が1つか2つに決まりません(口が3つ以上か口の数が分からない)。要素を書き並べるか、括りの関数の最後の口で受けてください")

def whole_feed(stages, st):
    """R51(2026-10-25): 撒いた流れが合成に来たら、合成は1つの関数なので、段から後ろの合成全体の口の数で受ける。
    合成全体の口 = 最初の段の残りの口 + 後ろの段ごとの(口 - 1)。2つなら左からの畳み込み、1つなら書き下し、
    ほか(3つ以上・可変長の口・恒等射・口の数が分からない)は G19。"""
    mouths = slots_left(stages[0])
    for g in stages[1:]:
        m = slots_left(g)
        if m is None or m < 1 or last_is_group(g): mouths = None; break
        mouths += m - 1
    if stages[0].variadic or last_is_group(stages[0]): mouths = None
    if mouths not in (1, 2):
        raise Gate("G19: 撒いた並び x~ を受ける合成の口が1つか2つに決まりません(口が3つ以上か口の数が分からない)。要素を書き並べるか、括りの関数の最後の口で受けてください")
    xs = list(st)
    def run_whole(*args):                                  # 合成全体を、書き並べた実引数で流す(inc add 1 2 は add (inc 1) 2)
        p = Pipe(stages[0]); p.stages = list(stages)
        out = None
        for a in args:
            out = p.feed(a)
        return out[1] if out is not None else UNIT
    if mouths == 2:
        if any(g.nofold for g in stages):
            raise Gate("G19: 畳まない2項の点なし(`[<<]` `[>>]` `[!=]` `[!==]`)は、撒いた並びを畳めません")
        if not xs: return UNIT
        acc = xs[0]
        for e in xs[1:]: acc = run_whole(acc, e)
        return acc
    if not xs: raise empty_stream_gate("G19: 空の流れ x~ は、口が1つの合成に当てるか決まりません。書き並べるか、`[f,]` の写像にします")
    r = run_whole(xs[0])
    for e in xs[1:]: r = join(r, e)
    return r

class Pipe:
    """合成した関数の段の並び。後から来る値は、最初の開いた段から順に流れ込む(R40)。
    可変長の段(最後の括り・畳む点なし)は並びの終わりまで開いたまま受け、閉じた結果が次の段へ入る(R41)。"""
    def __init__(self, f): self.stages, self.cur = list(parts_of(f)), 0

    def feed(self, v):                                   # 値を入れる。全部の段が閉じて値になったら ("done", 値)、まだなら None
        while True:
            s = self.stages[self.cur]
            if s.variadic and s.nofold and isinstance(v, Stream):
                raise Gate("G19: 畳まない2項の点なし(`[<<]` `[>>]` `[!=]` `[!==]`)は、撒いた並びを畳めません")
            if s.variadic: self.stages[self.cur] = apply(s, v); return None
            if last_is_group(s): self.stages[self.cur] = apply(collector(s), v); return None
            if isinstance(v, Stream) and self.cur + 1 < len(self.stages):     # R51: 合成に来た流れは、合成全体の口の数で受ける
                r = whole_feed(self.stages[self.cur:], v)
                self.cur = len(self.stages)
                return ("done", r)
            if isinstance(v, Stream) and not last_is_group(s):       # R51: 撒いた並びは流れの1項。段の残りの口の数で受ける
                r = stream_feed(s, v)
            else: r = apply(s, v)
            if isinstance(r, Closure): self.stages[self.cur] = r; return None
            self.cur += 1
            if self.cur == len(self.stages): return ("done", r)
            v = r                                        # 閉じた結果が次の段の最初の口へ
            nxt = self.stages[self.cur]
            if nxt.variadic and isinstance(v, list) and not isinstance(v, Stream):      # 可変長へは並びとして渡す(compose と同じ)
                for e in v[:-1]: self.stages[self.cur] = apply(self.stages[self.cur], e)
                v = v[-1] if v else UNIT

    def close(self):                                     # 並びの終わり: 値になればその値、足りなければ関数のまま
        while True:
            s = finalize(self.stages[self.cur])
            if isinstance(s, Closure):
                for g in self.stages[self.cur + 1:]: s = compose(s, g)
                return s
            self.cur += 1
            if self.cur == len(self.stages): return s
            out = self.feed(s)
            if out is not None: return out[1]

    def mouths(self):                                    # 最初の開いた段の口の数(可変長は None)
        return slots_left(self.stages[self.cur])

def resolve_fold(vs):
    """alpha1 の芯(coproduct_spec.md §3.3、R40〜R43・R47、2026-10-24): 余積は1つの演算子で左結合。
    並びは左から1項ずつ畳み、次の項はいちばん上の項とだけ結ぶ。
      値·値は積む / 関数·値は口を1つ埋める / 関数·関数は合成 / 値·関数は積む(関数は右からだけ受ける。逆適用は廃止)
    可変長の口は並びの終わりまで受ける。値の上に積まれて口の開いたまま閉じた関数は余ったラムダで、消えて警告する(R48・R52)。"""
    items = list(vs)
    acc, pre = items[0], None                            # pre: 積まれた関数の下に残る値
    if isinstance(acc, Closure): acc = Pipe(acc)
    def settle(out):                                     # 値になったら、下に残した値と並べる
        nonlocal acc, pre
        acc, pre = (join(pre, out) if pre is not None else out), None
    for x in items[1:]:
        if isinstance(acc, Pipe):
            if STRICT_GATES and x is ID and acc.cur == 0 and not getattr(acc.stages[0], "args", None): continue     # R74: 関数の後ろの恒等射は合成の単位(`fp i` は `fp`)
            if isinstance(x, Closure): acc.stages.extend(parts_of(x))
            else:
                out = acc.feed(x)
                if out is not None: settle(out[1])
        elif STRICT_GATES and acc is ID and x is UNIT: continue      # V3・R48: 値の口に来た計算の `!_` は消える。恒等射は恒等射のまま残る(`1 & (i w)` は `1 & (i)`)
        elif isinstance(x, Closure):                     # R47: 値の後ろの関数は積む。いちばん上の値は取らない
            pre, acc = acc, Pipe(x)
        else: acc = join(acc, x)
    if isinstance(acc, Pipe):
        v = acc.close()
        if pre is not None:
            if STRICT_GATES and type(v) is Closure and v.pd: v = fill_pd(v)       # R124: 値の後ろに積まれた、既定値の口だけが開いた部分適用は既定値で埋める
            if isinstance(v, Closure):                   # 値の上に積まれて口の開いたまま閉じた関数: 余ったラムダ(R48・R52)
                if STRICT_GATES and DOP[0]: strict_gate("G20: `$` で開いた関数を呼んだ形で、本体に値の上に積まれて余る関数があります。1つの関数と言い切れません(R59)。関数を値として並べる・渡すなら `$inc` のように `$` を付けて表明します(ほかは `$[…]`)", None)
                warn("leftover-lambda", LEFTOVER_MSG)
                return close(pre)
            return close(join(pre, v))
        return v
    return close(acc)

def resolve(vs):                               # coproduct_resolver.md §3.0・§4: 段の順に縮約し、毎回最初から走査し直す
    if STRICT_GATES: return resolve_fold(vs)   # alpha1(--strict)は左からの畳み込み。既定は旧 alpha の互換
    items = list(vs)
    if not any(isinstance(v, Closure) for v in items):          # 値だけの並び: 左から join(phase 3 と同じ)
        acc = items[0]
        for v in items[1:]: acc = join(acc, v)
        return finalize(close(acc))
    a0 = items[0]
    if isinstance(a0, Closure) and not any(isinstance(v, Closure) for v in items[1:]):
        rest, k = items[1:], 0                                    # 関数 + 値だけ: 口が埋まるまで左から apply(phase 2 と同じ)
        if FAST[0] and not a0.variadic and a0.params is not None:        # 速い道: 最後の口の手前までを1回で埋める(1つずつ複製を作らない。単位・流れが混じれば普通の道)
            nb = len(a0.params) - len(a0.args) - 1
            if nb >= 2 and nb <= len(rest):
                xs = rest[:nb]
                if not any(type(x) is Stream or is_unit(x) for x in xs):
                    a0 = _cp(a0, args=a0.args + xs); k = nb
        while k < len(rest) and needs_more(a0):
            if last_is_group(a0):                                  # R24: 最後の括りは残りの値の並び全体を受ける
                arg = rest[k]
                for x in rest[k + 1:]: arg = join(arg, x)
                a0, k = apply(a0, close(arg)), len(rest)
                break
            a0 = apply(a0, rest[k]); k += 1
            if not isinstance(a0, Closure): break
        if isinstance(a0, Closure) and a0.variadic and a0.args: a0 = finalize(a0)
        if k >= len(rest): return finalize(close(a0))
        items = [a0] + rest[k:]
    L = lambda v: isinstance(v, Closure)
    phases = [
        (lambda a, b: L(a) and L(b), compose),                                           # 1 compose
        (lambda a, b: L(a) and not L(b) and needs_more(a), apply),                       # 2 未飽和の apply
        (lambda a, b: not L(a) and not L(b), join),                                      # 3 concat / unshift / construct
        (lambda a, b: L(a) and not L(b), apply),                                         # 4 飽和済みの apply
        (lambda a, b: not L(a) and L(b) and not b.pf, reverse_apply),                    # 5 逆適用(ポイントフリーは除外)
    ]
    for pi, (pred, red) in enumerate(phases):
        again = True
        while again and len(items) > 1:
            again = False
            for i in range(len(items) - 1):
                if pred(items[i], items[i + 1]):
                    a = items[i]
                    if pi == 1 and last_is_group(a):          # R24: 最後の仮引数が括りなら、残りの値の並び全体を受ける
                        j = i + 1
                        while j < len(items) and not isinstance(items[j], Closure): j += 1
                        run = items[i + 1:j]
                        arg = run[0]
                        for x in run[1:]: arg = join(arg, x)
                        items[i:j] = [apply(a, close(arg))]
                    else:
                        if (pi == 1 and isinstance(a, Closure) and not a.variadic and not has_defaults(a)
                                and a.params is not None and len(a.params) - len(a.args) == 1
                                and i + 2 < len(items) and not isinstance(items[i + 2], Closure)):
                            tail = items[i + 2:]
                            if i > 0 or any(isinstance(x, Closure) for x in tail):       # 余りは、列の根(頭)にだけ置ける
                                strict_gate("G12: 余りの実引数が左の項か右の関数と並びます(`5 inc 3 4`・`inc 1 2 inc`)")
                        res = red(a, items[i + 1])
                        if pi == 1 and isinstance(a, Closure):
                            nxt = items[i + 2] if i + 2 < len(items) else None
                            if isinstance(res, Closure) and res.args and isinstance(nxt, Closure):
                                strict_gate("G2: 実引数を取りかけの関数が、別の関数と並びます(`f2 1 g 2`・`[+] 5 g 3`)。括ります")
                            if (isinstance(res, Closure) and not a.variadic and nxt is not None and not isinstance(nxt, Closure)
                                    and not has_defaults(a) and a.params is not None and len(a.params) - len(a.args) == 1):
                                strict_gate("G12: 本体の根が関数の関数に、余りの実引数が並びます(`adder 5 3`)")
                        items[i:i + 2] = [res]
                    again = True
                    break
        if pi == 1:                                           # 可変長は、右の値を取り終えたところで値になる
            items = [finalize(x) if isinstance(x, Closure) and x.variadic and x.args else x for x in items]
    acc = items[0]
    for v in items[1:]:
        if not isinstance(acc, Closure) and isinstance(v, Closure) and v.pf:
            strict_gate("G10: 逆適用の右が点なしです(`5 [+ 1]`・`5 inc [* 2]`)")
        acc = couple(acc, v)                   # 縮約しきれない並び(ポイントフリーの右など)は左から
    return finalize(close(acc))

DROPPED = object()
class FnEdge:
    """R137・V4・V7(2026-11-07): `,`・`|`・`;` の辺に丸ごと残った関数。辺が2つ以上残ればあとで `_` に落とし(知らせる)、1つだけ残れば `,` ごと消えて関数のまま。"""
    __slots__ = ("v",)
    def __init__(self, v): self.v = v
class PdEdge(FnEdge):
    """R124: 既定値の口だけが開いた部分適用の辺。1つだけ残れば関数のまま、2つ以上残れば既定値で埋めた値"""
    __slots__ = ()
def drop_fn_edge(msg, e=None):
    if isinstance(e, FnEdge) and e.v is ID: return                    # 2026-11-17 仕様(R61・R48): 恒等射の因子が `!_` になるときは知らせない
    warn("leftover-lambda", LEFTOVER_MSG + msg)
def comma_edge(v, keep=False):
    """R121・R61・R124: `,` の辺に残った値。既定値の口だけが開いた部分適用は既定値で埋め、口の開いた関数が丸ごと残れば `_`(warning leftover-lambda)。
    keep なら、丸ごと残った関数は FnEdge で返す(知らせない。R137: 辺が1つだけ残るなら関数のまま)。"""
    if v is ID and keep: return FnEdge(ID)                               # 2026-11-17 仕様(R61): 恒等射は単位でなく関数の因子(`,` が残れば一斉に `!_`、消えれば鎖の所に立つ)
    if isinstance(v, Closure) and v is not ID and not v.dead:
        if keep and STRICT_GATES and type(v) is Closure and v.pd: return PdEdge(v)          # R124: 単位が消えて1つだけ残れば関数のまま(`(gq 1 , w) 5` は 6)
        w = finalize(v)
        if isinstance(w, Closure) and w is not ID and not w.dead:
            if keep: return FnEdge(w)
            warn("leftover-lambda", LEFTOVER_MSG + "(`,` の被演算子。関数を積の要素にするなら `$inc , 2`、当てるなら `(inc 1) , 2`。R61)")
            return DROPPED                                                 # `_ , x` は x(R61)。`,` の単位で消える
        return w
    return v

def fold_couple(vs): return resolve(vs)

# ============================== 演算 ==============================
# ---- R62・R99(--strict): 関数を指す番地(`$inc`)と、その演算の答え(運ばれる `!_`、ABS)
def is_fn_target(v):
    if isinstance(v, Ref): return isinstance(v.value, Closure) or v.value is ID
    if isinstance(v, VarRef): return isinstance(v.env.vars.get(v.name), Closure) or v.env.vars.get(v.name) is ID
    return False
LEVEL_MSG = "値の演算子 `{op}` の被演算子に関数を指す番地があります。値の演算子は関数の番地に射を持たないので、答えは `!_` です(§4 R62・R119)。関数を呼んだ値を使うなら `$` を外して実引数を渡します(`(inc 5) + 1`)。番地どうしを比べるなら `==`・`!==` です"
MIX_MSG = "`{op}` で関数を指す番地と、番地でない値を並べています。番地と数の混ぜで、答えは `!_` です(§4 R62)。関数どうしを比べるなら両方を `$` の番地にします(`$inc == $f`)"
def fn_same(a, b):                                   # R62: 関数を指す番地どうしは木の同一性
    fa, fb = a.value if isinstance(a, Ref) else a.env.vars.get(a.name), b.value if isinstance(b, Ref) else b.env.vars.get(b.name)
    return fn_tree_same(fa, fb)
def _eta_fn(f):
    """R62: `r : x ? p x`(仮引数をそのまま渡すだけの本体)は p と同じ木(η)"""
    seen = 0
    while isinstance(f, Closure) and f.params is not None and not f.args and len(f.params) == 1 and f.params[0][0] == "name" and f.params[0][2] is None and seen < 20:
        b = f.body
        if isinstance(b, tuple) and b and b[0] == "seq" and len(b[1]) == 2 and b[1][0][0] == "id" and b[1][1] == ("id", f.params[0][1]):
            try: g = f.env.get(b[1][0][1])
            except Exception: return f
            if isinstance(g, Closure) and g is not f and g.params is not None: f = g; seen += 1; continue
        break
    return f
def bisim_fn(fa, fb, assume):
    """R62: 輪(再帰)を持つ関数の木の同一性。名前の先の関数どうしを、同じ仮定のもとで入れ子に比べる(輪をいくつの名前で切ったかは同一性に入らない)"""
    fa, fb = _eta_fn(fa), _eta_fn(fb)
    if fa is fb: return True
    if not (isinstance(fa, Closure) and isinstance(fb, Closure)) or fa.params is None or fb.params is None: return False
    if fa.native is not None or fb.native is not None or fa.args or fb.args or fa.params != fb.params: return False
    key = (id(fa), id(fb))
    if key in assume: return True
    assume.add(key)
    pn = {sp[1] for sp in fa.params if sp[0] == "name"}
    def teq(x, y):
        if isinstance(x, tuple) and isinstance(y, tuple):
            if len(x) == 2 and len(y) == 2 and x[0] == "id" and y[0] == "id":
                if x[1] == y[1] and (x[1] in pn or fa.env is fb.env and fa.env.get(x[1]) is fb.env.get(y[1])): return True
                if x[1] in pn or y[1] in pn: return False
                try: gx, gy = fa.env.get(x[1]), fb.env.get(y[1])
                except Exception: return False
                if isinstance(gx, Closure) and isinstance(gy, Closure): return bisim_fn(gx, gy, assume)
                return x == y
            return len(x) == len(y) and all(teq(p, q) for p, q in zip(x, y))
        if isinstance(x, list) and isinstance(y, list): return len(x) == len(y) and all(teq(p, q) for p, q in zip(x, y))
        return x == y
    try: return teq(fa.body, fb.body)
    except Exception: return False
def fn_tree_same(fa, fb):
    """R62: 関数の木が同じか。同じ実体のほか、仮引数と本体の木が同じで、当てた実引数が同じ関数も同じ(`inc` と `[x ? x + 1]` は同じ木。§3 の R128 の例)。
    本体の名前の先が違いうる物(違う呼び出しの中で作った関数)は、同じ範囲で作った時だけ同じと見る(実装の判断)"""
    if fa is fb: return True
    if not (isinstance(fa, Closure) and isinstance(fb, Closure)): return False
    if fa.dead or fb.dead or fa.variadic != fb.variadic: return False
    if fa.native is not None or fb.native is not None:
        if fa.native is not fb.native: return False
    elif fa.params != fb.params: return False
    elif fa.body != fb.body and not (STRICT_GATES and not fa.args and not fb.args and bisim_fn(fa, fb, set())): return False
    if len(fa.args) != len(fb.args): return False
    for x, y in zip(fa.args, fb.args):
        if isinstance(x, Closure) or isinstance(y, Closure):
            if not fn_tree_same(x, y): return False
        elif type(x) is not type(y) or x != y: return False
    def root(e): return e is None or e.parent is None
    return fa.env is fb.env or (root(fa.env) and root(fb.env)) or (const_closure(fa) and const_closure(fb))
def fn_addr_op(op, a, b, hex_a=False, hex_b=False):
    """R62: 関数を指す番地を被演算子に持つ演算(--strict)。`==`・`!==` は番地の比べ(番地どうしは木の同一性、`0x…` とは番地の比べ、証人は左)、
    数ほかと並べた `==`・`!==` は番地と数の混ぜ(address-number-mix)、ほかの値の演算子は level-mismatch。答えの `!_` は運ばれる(ABS)。"""
    if a is ABS or b is ABS: return ABS
    if op in ("==", "!=="):
        fa, fb = is_fn_target(a), is_fn_target(b)
        if fa and fb: eq = fn_same(a, b)
        elif (fa and hex_b) or (fb and hex_a): eq = False             # 関数の番地は `0x…` の字面の番地と同じ所にない(実装の判断。番地の値は持たない)
        else:
            warn("address-number-mix", MIX_MSG.format(op=op)); return ABS
        return a if (eq if op == "==" else not eq) else UNIT
    for x_ in (a, b):                                             # R87: 番地の隣に丸ごと残った裸の関数は、値の演算子の被演算子として `!_`(leftover-lambda。`inc + $inc`)
        if isinstance(x_, Closure) and x_ is not ID and not x_.dead: warn("leftover-lambda", LEFTOVER_MSG + "(値の演算子の被演算子。関数を値として置くなら `$` を付けます。R87)", operand=True)
    warn("level-mismatch", LEVEL_MSG.format(op=op)); return ABS
# ---- R62・R98(--strict): `0x…` の番地は1つの種類 Address。番地どうしの +・-・ビットは番地、番地 * 数は番地、番地どうしの / は数・% は番地。
# 射の無い演算(番地どうしの *・番地でずらす <<・>>・番地の冪・前置 -・後置 !)は address-without-arrow、番地と数のほかの組は address-number-mix で、
# どちらも答えは運ばれる `!_`(ABS)。番地の算術とビットは `!_` を吸う(ABS)。幅つきの番地(`04x…`)が幅の倍数の外へ出た所は知らせる(名前は仮、§5 Q66 (6))
def is_addr(v): return isinstance(v, (Addr, WInt)) and not isinstance(v, bool)
def addr_w(v): return v.w if type(v) is WInt else 0
def mk_addr_w(v, w=0):
    if not (0 <= v <= UMASK): return UNIT                     # 負と溢れは値の段で `!_`(R62)
    if w:
        x = WInt(v); x.w = w; return x
    return Addr(v)
def addr_hex(v): return "0x%X" % int(v)
WIDTH_KIND = "address-width-multiple"                        # 名前は仮(§5 Q66 (6)。仕様の表は「幅の倍数でない差の warning」)
def width_warn(a, w, how, hint):
    warn(WIDTH_KIND, f"(名前は仮)幅 {w} byte の番地 {addr_hex(a)} が、{how}幅の倍数の外へ出ました(§4 R62)。{hint}。幅の倍数の外の番地を `@`・`#` に置くと `!_` です")
NUM_HINT = {"+": "`0x10 + 1` → `0x10 + 0x1`", "-": "`0x10 - 1` → `0x10 - 0x1`", "/": "`(q - p) / 8` → `(q - p) / 0x8`", "%": "`p % 4096` → `p % 0x1000`",
            ">>": "`0x10 >> 1` → `0x10 / 0x2`", "*": "`2 * 0x10` → `0x10 * 2`"}
def addr_mix(op, a, b, num=True):
    h = NUM_HINT.get(op, "数の相手は `0x…` の番地で書きます") if num else "番地は番地か関数を指す番地とだけ比べます"
    warn("address-number-mix", f"`{op}` で番地と{'数' if num else '番地でも数でもない値'}を並べています。番地と数の混ぜで、答えは `!_` です(§4 R62・R98)。{h}")
    return ABS
def addr_noarrow(op, what):
    hint = "番地を足すなら `b + q`、引くなら `b - q` と書きます" if op == "-" else "番地を数で何倍かするなら `0x4 * 2` のように右に数を置きます"
    warn("address-without-arrow", f"{what}は、番地の域に射が無いので、答えは `!_` です(§4 R62)。{hint}")
    return ABS
def numlike(v): return is_num(v) and not is_addr(v)
def addr_r62(op, a, b):
    """R62・R98: 番地を被演算子に持つ算術とビット(--strict)。決まらない組(並び・文字列・文字との算術、範囲)は None で、今の道へ返す。"""
    if a is ABS or b is ABS: return ABS
    for x in (a, b):
        if x is ID: warn("leftover-lambda", ID_MSG.format(where=f"番地を被演算子に持つ `{op}`")); return ABS     # R48
        if isinstance(x, Closure) and not x.dead:
            warn("leftover-lambda", LEFTOVER_MSG + "(番地を被演算子に持つ値の演算子。R87・R62)"); return ABS
    if is_unit(a) or is_unit(b): return ABS                     # 番地の算術とビットは `!_` を吸う(R62。`$vs + 0x10` は `!_`)
    A, B = is_addr(a), is_addr(b)
    if A and B:
        x, y, w = int(a), int(b), addr_w(a)
        if op in ("+", "-", "&&", "||", ";;"):
            r = {"+": x + y, "-": x - y, "&&": x & y, "||": x | y, ";;": x ^ y}[op]
            if w and x % w == 0 and 0 <= r <= UMASK and r % w:
                width_warn(a, w, f"`{op}` で", "`+`・`-` なら幅の倍数の `0x…` か `' k~`、ビットなら幅を書かない `0x…` か `01x…` で書きます")
            return mk_addr_w(r, w)
        if op == "/": return UNIT if (y == 0 or x % y) else (x // y if x // y <= INT_MAX else UNIT)      # R98: 番地どうしの / は数(割り切れない・0x0 で割る・Int に入らない は `!_`)
        if op == "%": return UNIT if y == 0 else Addr(x % y)
        if op in ("*", "<<", ">>", "^"): return addr_noarrow(op, f"番地どうしの `{op}`")
        return None
    if A and numlike(b):
        if op in ("*", "<<"):
            if isinstance(b, float): return addr_mix(op, a, b)
            k = int(b)
            if k < 0: return UNIT
            return mk_addr_w(int(a) * k if op == "*" else int(a) << k if k < 64 else UMASK + 1, addr_w(a))
        if op == "^": return addr_noarrow(op, "番地の冪")
        return addr_mix(op, a, b)
    if B and numlike(a): return addr_mix(op, a, b)
    return None
def addr_cmp(op, a, b):
    """R62: 番地どうしは符号なしで比べ、証人は左。番地と数は混ぜ。`==`・`!==` で番地と番地でも数でもない値も混ぜ(--strict)。"""
    A, B = is_addr(a), is_addr(b)
    if A and B:
        x, y = int(a), int(b)
        ok = {"<": x < y, "<=": x <= y, ">": x > y, ">=": x >= y, "=": x == y, "==": x == y, "!=": x != y, "!==": x != y}[op]
        return a if ok else UNIT
    o = b if A else a
    if numlike(o): return addr_mix(op, a, b)
    if op in ("==", "!==") and not isinstance(o, Char): return addr_mix(op, a, b, num=False)
    return None
STORE_KIND = "address-stored"                                 # 名前は仮(§5 Q66 (6)。仕様の表は「番地をしまう行の warning」)
STORE_ROWS = set()
def holds_addr(v, depth=0):
    """R62: 番地(`0x…` と関数を指す番地)か、それを要素に持つ並び・積(構造体の欄は欄の行が知らせるので見ない)"""
    if is_addr(v) or is_fn_target(v): return True
    if depth < 8 and isinstance(v, (list, tuple)) and not isinstance(v, (str, Struct)): return any(holds_addr(x, depth + 1) for x in v)
    return False
def store_warn(line, how):
    """R62: 番地が `:` か `#` で場所(名前・器の要素・欄・番地の先)に入る行。行ごとに1つ(--strict)"""
    if not line: line = CURLINE[0]
    key = (PARSE_FILE, line)
    if key in STORE_ROWS: return
    STORE_ROWS.add(key)
    src_ = (SRC_LINES.get(PARSE_FILE) or [])
    txt = src_[line - 1].strip() if line and 0 < line <= len(src_) else ""
    old = CURLINE[0]; CURLINE[0] = line
    try: warn(STORE_KIND, f"(名前は仮)番地を{how}でしまう行です" + (f": `{txt[:60]}`" if txt else "") + "(§4 R62)。番地は名前・器・欄に入れても使えますが、しまった所を指して知らせます")
    finally: CURLINE[0] = old
def node_line(n): p_ = POS.get(id(n)); return p_[1] if p_ else None
CROSS_KIND = "address-cross-kind"                              # 名前は仮(§5 Q66 (6)。仕様の表は「種類を跨ぐ書き込みの warning」)
def kind_of(v):
    """R62: 場所と値の種類(関数を指す番地・番地・値)。器は要素ごと"""
    if is_fn_target(v): return "fn"
    if is_addr(v): return "addr"
    if isinstance(v, Struct): return tuple(kind_of(x) for x in v.values())
    if isinstance(v, list) and not isinstance(v, (str, Places)): return tuple(kind_of(x) for x in v)
    return "val"
def place_of(ln, env):
    """`#` の左の場所(--strict)。番地を運ばない名前と、`'` で引いた器の要素・欄だけ。番地の先(`0x…` とそれを運ぶ名前)は種類を持たないので None"""
    m = ln
    while m[0] == "block" and isinstance(m[1], tuple): m = m[1]
    if m[0] == "id":
        o = env.owner(m[1])
        v = o.vars.get(m[1]) if o is not None else None
        if v is None or isinstance(v, Closure) or is_addr(v) or is_fn_target(v) or is_unit(v): return None
        return v
    if m[0] == "bin" and m[1] == "'" and len(m) == 4:
        c = ev(m[2], env)
        if is_addr(c) or isinstance(c, (Places, Closure)) or is_unit(c) or not isinstance(c, (list, Struct)): return None
        v = do_get(c, m[3], env)
        return None if is_unit(v) else v
    return None
def cross_kind_write(n, env):
    """R62: 場所の生まれた種類と違う値を書く `#` の行は、何も書かず `!_` で、warning(名前は仮)を行に1つ(番地をしまう行の warning と重なれば1つ)"""
    pv = place_of(n[2], env)
    if pv is None: return False
    r = ev(n[3], env)
    if is_unit(r) or isinstance(r, Closure): return False
    kp, kr = kind_of(pv), kind_of(r)
    same = kp == kr or (not isinstance(kp, tuple) and isinstance(kr, tuple) and len(kr) == 1 and kr[0] == kp) or (isinstance(kp, tuple) and len(kp) == 1 and kp[0] == kr)
    if same:
        if holds_addr(r): store_warn(None, "`#`")                # R62: 器の要素・欄へ番地を書く行(同じ種類の書き込み)
        return False
    line = CURLINE[0]; key = (PARSE_FILE, line)
    if key not in STORE_ROWS:
        STORE_ROWS.add(key)
        src_ = SRC_LINES.get(PARSE_FILE) or []
        txt = src_[line - 1].strip() if line and 0 < line <= len(src_) else ""
        warn(CROSS_KIND, "(名前は仮)場所の生まれた種類と違う値を `#` で書く行です" + (f": `{txt[:60]}`" if txt else "") + "(§4 R62)。関数を指す番地・番地・値は、生まれた種類の場所にだけ書けます。何も書かず、答えは `!_` です")
    return True
def addr_operand_gate(a, b, what):
    """R62・R99(--strict): 関数を指す番地・その演算の答え(ABS)・先の分からない持ち上げ(`$?`)を被演算子に持つ値の演算子は、fn_addr_op が答えを決める"""
    for x in (a, b):
        if is_fn_target(x) or x is ABS: return True          # 呼ぶ側が fn_addr_op で答えを決める
        if isinstance(x, Lift):                               # R99: 先の分からない持ち上げを値の演算子に置いた形は level-mismatch
            warn("level-mismatch", f"値の{what}の被演算子に、先の種類の分からない持ち上げ(`$f`・`$@f`・取り込む前の名前の `$`)があります。関数の番地なら答えは `!_` です(§4 R99・R62)")
            return True
    return False
def addr_face(v):
    if is_fn_target(v): return "fn"
    return "hex" if is_addr(v) else "other"
ARITH_ADDR = {"+", "-", "*", "/", "%", "^", "<<", ">>", "&&", ";;", "><", "!!", "||", "~+", "~-", "~*", "~/", "~^"}
CMP_ADDR = {"==", "!==", "<", "<=", "=", ">=", ">", "!="}
ABS_OPS = ARITH_ADDR | CMP_ADDR | {"~"}
R48_OPS = {"&", "==", "!==", "<", "<=", "=", ">=", ">", "!=", "~", "~+", "~-", "~*", "~/", "~^", "'", "@", "#"}
def addr_op(op, l, r, ln, rn, node, env):
    """R62(--strict): 関数を指す番地か、その演算の答え(ABS)を被演算子に持つ演算は fn_addr_op。ほか(`0x…` の番地も)は値の演算子の道(addr_r62・addr_cmp)"""
    if "fn" in (addr_face(l), addr_face(r)) or l is ABS or r is ABS:
        return fn_addr_op(op, l, r, is_addr(l), is_addr(r))
    return binop(op, l, lambda: r)
def strict_addr_bin(n, op, env):
    ln, rn = n[2], n[3]
    l = ev(ln, env)
    if addr_face(l) == "other" and is_unit(l) and not isinstance(l, Closure) and l is not ABS:
        r0 = ev(rn, env)                                          # 書いた `_` と番地の組は左右どちらでも同じ答え
        if addr_face(r0) == "fn": return addr_op(op, l, r0, ln, rn, n, env)
        return binop(op, l, lambda: r0)
    if addr_face(l) != "fn":
        rn_val = None
        if l is not ABS and op in ABS_OPS:
            r0 = ev(rn, env)
            if r0 is ABS or addr_face(r0) == "fn": return addr_op(op, l, r0, ln, rn, n, env)
            rn_val = r0
        if OVERRIDES:
            o = env.owner("[" + op + "]")
            if o is not None and isinstance(o.vars["[" + op + "]"], Closure):
                return run_with(o.vars["[" + op + "]"], [l, ev(rn, env) if rn_val is None else rn_val])
        return binop(op, l, lambda: ev(rn, env) if rn_val is None else rn_val)
    return addr_op(op, l, ev(rn, env), ln, rn, n, env)

CMP = {"<", "<=", "=", "==", ">=", ">", "!=", "!=="}

def witness(a, b): return a        # value_spec V6: 0/1 の例外なし(成り立てばいつも左。`0 < 5` は 0。既定も --strict も同じ)

def compare(op, a, b):
    if STRICT_GATES and addr_operand_gate(a, b, "比べ"): return fn_addr_op(op, a, b)
    if STRICT_GATES and (is_addr(a) or is_addr(b)):
        r_ = addr_cmp(op, a, b)
        if r_ is not None: return r_
    if op in ("=", "=="):                                          # 1要素の器 ≅ その要素(狭い側を持ち上げて比べる)
        if isinstance(a, list) and len(a) == 1 and not isinstance(b, list): a = a[0]
        if isinstance(b, list) and len(b) == 1 and not isinstance(a, list): b = b[0]
    if (isinstance(a, Vec) or isinstance(b, Vec)) and op not in ("=", "==", "!=", "!=="):
        return UNIT                                                 # Vector に大小は無い
    try:
        ok = {"<": lambda: a < b, "<=": lambda: a <= b, ">": lambda: a > b, ">=": lambda: a >= b,
              "=": lambda: a == b, "==": lambda: a == b, "!=": lambda: a != b, "!==": lambda: a != b}[op]()
    except TypeError: ok = False
    return witness(a, b) if ok else UNIT

_INF, _NAN = float("inf"), float("nan")
def f_div(a, b):                                   # Float は IEEE 754 倍精度のまま(integer_overflow.md「`1.0 / 0.0` は +∞、`0.0 / 0.0` は NaN」)。Python は 0 で割ると例外なので、IEEE の答えを返す
    try: return a / b
    except ZeroDivisionError:
        if a != a or a == 0: return _NAN
        return math.copysign(_INF, a) * math.copysign(1.0, b)
def f_mod(a, b):
    try: return a % b
    except ZeroDivisionError: return _NAN              # x % 0.0 は NaN
def f_pow(a, b):
    try: r = a ** b
    except OverflowError: return -_INF if (a < 0 and float(b).is_integer() and int(b) % 2) else _INF      # 桁あふれは ±∞
    except ZeroDivisionError: return _INF                                                               # 0.0 の負の冪は +∞
    return _NAN if isinstance(r, complex) else r                                                          # 負の数の小数冪は NaN
def _arith_core(op, a, b):
    if type(a) is int and type(b) is int and not STRICT_GATES:       # 素の整数どうし(番地・UInt・bool は型が違う)の四則は、長い型の判定を通らず直に(結果は下の道と同じ)
        if op == "+": return a + b
        if op == "-": return a - b
        if op == "*": return a * b
        if b:
            if op == "%": return abs(a) % abs(b) if a >= 0 else -(abs(a) % abs(b))
            if op == "/":
                q = abs(a) // abs(b)
                return q if (a < 0) == (b < 0) else -q
    if STRICT_GATES and addr_operand_gate(a, b, "演算"): return fn_addr_op(op, a, b)
    if STRICT_GATES and (is_addr(a) or is_addr(b)):
        r_ = addr_r62(op, a, b)
        if r_ is not None: return r_
    if STRICT_GATES and (a is ID or b is ID):                                    # R87: 恒等射も丸ごと残った関数と同じく _(知らせない)
        a = UNIT if a is ID else a; b = UNIT if b is ID else b
    if STRICT_GATES and (isinstance(a, Closure) or isinstance(b, Closure)):      # R87: 値の演算子の被演算子に丸ごと残った関数は _ (恒等射でなければ知らせる)
        def lo(x):
            if isinstance(x, Closure) and not x.dead:
                if x is not ID: warn("leftover-lambda", LEFTOVER_MSG + "(値の演算子の被演算子。関数を値として置くなら `$` を付けます。R87)", operand=True)
                return UNIT
            return x
        a, b = lo(a), lo(b)
    if isinstance(a, Closure) or isinstance(b, Closure):
        strict_gate("G7: 関数は算術演算子の被演算子になれません(読みが決まらない)"); return UNIT
    if isinstance(a, Vec) or isinstance(b, Vec):
        if is_unit(a): return b
        if is_unit(b): return a
        if isinstance(a, list) or isinstance(b, list): return UNIT       # List と Vector の演算は型エラー
        if op not in ("+", "-", "*", "/", "%", "^"): return UNIT
        if isinstance(a, Vec) and isinstance(b, Vec): pairs = zip(a, b)
        elif isinstance(a, Vec) and is_num(b): pairs = ((x, f32(float(b)) if F32[0] else float(b)) for x in a)   # スカラーは全レーンへ(--check-f32 では 32 ビットに丸めてから)
        elif isinstance(b, Vec) and is_num(a): pairs = ((f32(float(a)) if F32[0] else float(a), y) for y in b)
        else: return UNIT
        out = [UNIT if (op in ("/", "%") and y == 0) else arith(op, float(x), float(y)) for x, y in pairs]
        return Vec(out) if all(is_num(r) for r in out) else UNIT           # 0 で割った枠があれば全体が __
    if isinstance(a, VarRef) and op == "+" and isinstance(a.env.vars.get(a.name), Vec):    # $v + 4k
        if isinstance(b, int) and not isinstance(b, bool) and b % 4 == 0 and 0 <= b < 16: return LaneRef(a, b // 4)
        return UNIT
    if isinstance(a, Addr) or (is_unit(a) and isinstance(b, Addr)):      # 番地の域(左辺。左辺が __ なら相手): __ は両側で吸収し、外へ出た番地は存在しない
        if is_unit(a) or is_unit(b): return UNIT
        if isinstance(b, bool) or not isinstance(b, int): return UNIT if not isinstance(b, Char) else arith(op, a, ord(b))
        if op == "+": return mk_addr(a + b)
        if op == "-": return mk_addr(a - b)
        if op in ("/", "%"):                                  # 0 以下で割れば __(Int の 0 以下・番地の 0)
            if b <= 0: return UNIT
            return mk_addr(a // b if op == "/" else a % b)
        if op in ("*", "^", "<<"): return UNIT                # 番地の域に掛け算・冪・左シフトの射は無い
        if op == ">>": return mk_addr(a >> b) if b >= 0 else UNIT
        if op == "&&": return mk_addr(a & b)
        if op == "||": return mk_addr(a | b)
        if op == ";;": return mk_addr(a ^ b)
        return UNIT
    if (isinstance(a, UInt) or (is_unit(a) and isinstance(b, UInt))) and not isinstance(a, Addr):     # UInt の域(左辺。左辺が __ なら相手): 環 ℤ/2^64ℤ。__ は単位元
        if is_unit(a): return b
        if is_unit(b): return a
        if isinstance(b, int) and not isinstance(b, (bool, Addr)):
            if op == "+": return UInt((a + b) & UMASK)
            if op == "-": return UInt((a - b) & UMASK)
            if op == "*": return UInt((a * b) & UMASK)
            if op in ("/", "%"):                              # 0 でも負の数でも割れない(ビットで読むと 2^64 − n で割ることになる)
                if b <= 0: return UNIT
                return UInt(a // b if op == "/" else a % b)
            if op == "^": return UInt(pow(int(a), int(b), 1 << 64)) if b >= 0 else UNIT
            if op == "<<": return UInt((a << b) & UMASK) if 0 <= b < 64 else (UInt(0) if b >= 64 else UNIT)
            if op == ">>": return UInt(a >> b) if b >= 0 else UNIT
            if op == "&&": return UInt(a & b & UMASK)
            if op == "||": return UInt((a | b) & UMASK)
            if op == ";;": return UInt((a ^ b) & UMASK)
    if is_unit(a): return b if is_num(b) else UNIT           # Int では __ は単位元
    if is_unit(b): return a if is_num(a) else UNIT
    if isinstance(a, (str, list)) and not isinstance(a, Char) and isinstance(b, int):
        if op in ("*", "^") and b > 0 and len(a) * b > SIZE_LIMIT: raise SignError(f"結果が大きすぎます(実装の上限は {SIZE_LIMIT:,} 要素)")    # 実装の守り: 並べきれない大きさで異常終了しない
        if op == "*": return a * b                             # 繰り返し
        if op == "^" and isinstance(a, list): return [list(a) for _ in range(b)]
        if op == "/" and isinstance(a, list) and b > 0:
            k = len(a) // b                                    # 丈は ||list|| / r。余りは最後の群に残る(type_system.md §3.2)
            if k == 0: return a                                # 丈が 0 なら空の群は消え、元の器が残る
            return [a[i * k:(i + 1) * k] for i in range(b - 1)] + [a[(b - 1) * k:]]
    if isinstance(a, Char) or isinstance(b, Char):             # 文字の域(type_system.md §3.6): 量ではなく位置
        def in_domain(r): return Char(chr(r)) if (0 <= r <= 127 if CHARSET[0] == "ascii" else (0 <= r <= 0x10FFFF and not 0xD800 <= r <= 0xDFFF)) else UNIT    # U+0000〜charset の上限(ascii は U+007F、utf32 は U+10FFFF でサロゲートを除く。alpha1: U+0000 はただの文字)
        if isinstance(a, Char) and isinstance(b, Char):
            if op == "-": return ord(a) - ord(b)               # 隔たり(Int。負でよい)
            if op == "+": return in_domain(ord(a) + ord(b))    # 符号位置の和
            return UNIT                                        # c * d・c / d などは射が無い
        if isinstance(a, Char) and isinstance(b, int):
            if op == "*" and b > SIZE_LIMIT: raise SignError(f"結果が大きすぎます(実装の上限は {SIZE_LIMIT:,} 要素)")
            if op == "*": return "%s" % a * b if b >= 1 else UNIT          # 連結の n 乗(n が 0 以下なら __)
            if op == "+": return in_domain(ord(a) + b)                      # ずらす
            if op == "-": return in_domain(ord(a) - b)
            return UNIT                                                      # c / n・c % n・c ^ n は射が無い
        if is_num(a) and isinstance(b, Char): return arith(op, a, ord(b))   # n + c : 数として読む(Int)
        return UNIT
    if not (is_num(a) and is_num(b)): return UNIT              # 文字列は算術の代数に居ない
    if op == "+": return a + b
    if op == "-": return a - b
    if op == "*": return a * b
    if op == "/":
        if isinstance(a, int) and isinstance(b, int):           # Int / Int は整数除算(0 へ丸める。sdiv と同じ)
            if b == 0:
                if STRICT_GATES: info("zero-division", "0 で割ったので _ です(V5・V11)")
                return UNIT                                     # 0 で割れば商も剰余も __
            q = abs(a) // abs(b)
            return q if (a < 0) == (b < 0) else -q
        return f_div(float(a), float(b))
    if op == "%":
        if not (isinstance(a, int) and isinstance(b, int)): return f_mod(float(a), float(b))
        if b == 0:
            if STRICT_GATES: info("zero-division", "0 で割ったので _ です(V5・V11)")
            return UNIT
        if isinstance(a, int) and isinstance(b, int):          # 剰余は被除数の符号(sdiv と対)
            r = abs(a) % abs(b)
            return r if a >= 0 else -r
        return a % b
    if op == "^":
        if isinstance(a, int) and isinstance(b, int) and b > 0 and abs(a) > 1 and b * a.bit_length() > BIT_LIMIT: raise SignError(f"結果が大きすぎます(実装の上限は {BIT_LIMIT:,} ビット)")
        if isinstance(a, float) or isinstance(b, float): return f_pow(float(a), float(b))      # Float は IEEE 754: 桁あふれ ±∞・0.0 の負の冪 +∞・負の数の小数冪 NaN
        if STRICT_GATES and isinstance(a, int) and isinstance(b, int) and b < 0:      # V5・V11: 負の指数の冪は当たる演算が無く _
            info("no-operation", "負の指数の冪は当たる演算が無いので _ です(V5・V11)")
            return UNIT
        try: r_ = a ** b
        except (OverflowError, ZeroDivisionError): return UNIT         # Int の 0 の負の冪は射が無いので __(処理系は落ちない)
        return UNIT if isinstance(r_, complex) else r_
    if isinstance(a, int) and isinstance(b, int):
        if op == "&&": return a & b                     # 選んだ演算だけ計算する(以前は 5 つ全部を先に計算していて、`x && (0 - 1)` が負のシフトで落ち、`x && 0xFFFFFFFFFFFF` が巨大なシフトで止まらなかった)
        if op == "||": return a | b
        if op == ";;": return a ^ b
        if op == "<<" or op == ">>":
            if b < 0: return UNIT                      # 負のシフト量: 仕様は未決(type_system.md「k が負の形は未決」)。Python の ValueError で落とさず、決まらない値 __ にする(判断。仕様で決まれば合わせる)
            if op == "<<" and b > BIT_LIMIT: raise SignError(f"結果が大きすぎます(実装の上限は {BIT_LIMIT:,} ビット)")
            return a << b if op == "<<" else a >> b
        raise KeyError(op)
    return UNIT

INTCHK = [False]                               # --check-int : Int の値域(integer_overflow.md §1.2)の検査。既定は Python の整数のまま(桁数に制限なし)
INT_MAX = (1 << 63) - 1
_arith_plain = _arith_core
def arith(op, a, b):
    r = _arith_core(op, a, b)
    if STRICT_GATES and type(r) is int and (r > INT_MAX or r < -INT_MAX):        # V5: Int(64 bit)の溢れは _。生まれた行に information `int-overflow`
        info("int-overflow", f"Int(64 bit)の溢れなので _ です: {show(a)} {op} {show(b)} の答え {r} は -{INT_MAX} 〜 {INT_MAX} の外です(V5・V11)")
        return UNIT
    return r
def arith_checked(op, a, b):
    r = _arith_plain(op, a, b)
    if type(r) is int and (r > INT_MAX or r < -INT_MAX):
        raise SignError(f"Int の溢れ(罠): {show(a)} {op} {show(b)} の答え {r} は Int の値域 -{INT_MAX} 〜 {INT_MAX} の外です(integer_overflow.md §1.1・§1.2)")
    return r

class IterList(list):                          # stack_abi §4.6: 規則(レンジ・Iterator)。{start, step, end} を持つ値で、要素は List と同じに読める。Reader(`$` の関数の番地)を右に並べるとループ
    start = step = end = None; op = "~+"
class OpenRange:                               # stack_abi §1.3: 開端レンジ `[start ~+ step]`。上界は持たず、終わりは呼び出し元の責任(添字で取り出すか `~ end` で閉じる)
    def __init__(self, start, op, step): self.start, self.op, self.step = start, op, step
    def next(self, x):
        o, s = self.op, self.step
        return x + s if o == "~+" else x - s if o == "~-" else x * s if o == "~*" else x // s if o == "~/" and isinstance(x, int) and isinstance(s, int) else x / s if o == "~/" else x ** s
    def at(self, k):
        x = self.start
        for _ in range(k): x = self.next(x)
        return x
    def __repr__(self): return f"[{show(self.start)} {self.op} {show(self.step)}]"
def iterate_loop(it, fnref):
    f = fnref.value if isinstance(fnref, Ref) else fnref.env.vars.get(fnref.name)
    if isinstance(it, OpenRange):              # stack_abi §1.3: 終了条件は呼び出し元の責任(言語は保証しない)。結果は集めない。抜けるのは本体のエラー・終了だけ
        x = it.start
        while True:
            run_with(f, [x])
            x = it.next(x)
    out = []
    for x in it:
        r = run_with(f, [x])
        if isinstance(r, Stream): out.extend(r)
        elif not is_unit(r): out.append(r)
    return out
def make_open_range(op, l, r):
    if is_unit(l) or is_unit(r): return UNIT
    num = lambda v: isinstance(v, (int, float)) and not isinstance(v, bool)
    if not (num(l) and num(r)): return UNIT
    if op == "~/" and r == 0: raise SignError("派生範囲 ~/ の刻みが 0 です")
    return OpenRange(l, op, r)
BIT_LIMIT = 10_000_000                        # 実装の守り: 整数の冪・シフトの結果のビット数の上限
SIZE_LIMIT = 50_000_000                       # 実装の守り: 繰り返し・n 乗で作る器の要素数の上限
def make_range(l, r):
    if is_unit(l) or is_unit(r): return UNIT
    if isinstance(l, OpenRange):                               # [start ~+ step ~ end] : 刻み付きレンジ
        if not isinstance(r, (int, float)) or isinstance(r, bool): return UNIT
        out, x = IterList(), l.start
        up = l.next(x) >= x
        if l.next(x) == x: raise SignError("派生範囲が進みません(刻みが単位元です)")
        while (x <= r) if up else (x >= r):
            out.append(x)
            if len(out) > 10_000_000: raise SignError("派生範囲が長すぎます")
            x = l.next(x)
        out.start, out.op, out.step, out.end = l.start, l.op, l.step, r
        return out
    if not (isinstance(l, int) and isinstance(r, int)): return UNIT
    if abs(r - l) >= 10_000_000: raise SignError("範囲が長すぎます(実装の上限は 10,000,000 要素)")      # 実装の守り: 並べきれない長さで異常終了しない(刻み付きの範囲と同じ上限)
    out = IterList(range(l, r + 1) if l <= r else range(l, r - 1, -1))
    out.start, out.op, out.step, out.end = l, "~+", (1 if l <= r else -1), r
    return out

def as_container(v):                           # 1要素の器 ≅ スカラー
    return v if isinstance(v, (list, str)) else [v]

def get_value(obj, key):
    EFFECTS[0] += 1                             # 読みも効果とみなす(`@STD_UART` など、読むと状態が動く番地がある)
    if is_unit(obj) or is_unit(key): return UNIT
    if isinstance(obj, Vec):                    # レーン添字(0..3)
        return obj[key] if isinstance(key, int) and not isinstance(key, bool) and 0 <= key < 4 else UNIT
    if isinstance(obj, Struct):                # 構造体は名前で引く。位置アクセスは持たない
        if isinstance(key, int) and not isinstance(key, bool):         # 連番(宣言順)で引く。負の連番は末尾から(type_system.md §3.2 の `point ' 0`・`point ' -1`)
            ks = list(obj.values())
            return ks[key] if -len(ks) <= key < len(ks) else UNIT
        return obj.get(key, UNIT) if isinstance(key, str) else UNIT
    if isinstance(obj, OpenRange):                              # 開端レンジの要素: k 番目、範囲の添字ならその要素の並び
        if isinstance(key, int) and not isinstance(key, bool) and key >= 0: return obj.at(key)
        if isinstance(key, list) and all(isinstance(i, int) and i >= 0 for i in key): return [obj.at(i) for i in key]
        return UNIT
    if not isinstance(obj, Closure): obj = as_container(obj)
    try:
        if isinstance(key, list):                              # [a ~ b] による範囲取得
            part = [obj[i] for i in key]
            return "".join(part) if isinstance(obj, str) else part   # String の範囲は String
        if isinstance(key, float) and isinstance(obj, (list, str)):   # type_system.md §4.1: 添字に Float が来たら常に四捨五入(最近接、タイは 0 から遠ざける)。補間ではない
            if key != key or key in (float("inf"), float("-inf")): return UNIT
            key = int(math.floor(abs(key) + 0.5)) * (1 if key >= 0 else -1)
        if isinstance(key, int) and isinstance(obj, (list, str)):
            v = obj[key]
            return Char(v) if isinstance(obj, str) else v
    except (IndexError, TypeError): pass                   # 添字の並びに整数でない物(関数など)があれば引けないので `_`(仕様は黙っている。処理系は落ちない)
    return UNIT

OPT = False                                    # --opt : sign_pe.py の最適化を使う
OVERRIDES = False                              # [op] : ... の定義が1つでもあれば真(通常は検索を省く)
MEMORY = {}                                    # 番地 → 値(普通のメモリ)
UART = 0x9000000                               # この番地への書き込みは標準出力へ出る(QEMU virt の PL011)
def uart_read():                                # `@uart` : 標準入力から 1 バイト読んで 0〜255 の Int。入力の終わりは __
    b = sys.stdin.buffer.read(1)
    return b[0] if b else UNIT

BOUNDS = [False, 0x100, []]                    # --check-bounds: [有効か, 帯の外側で見張る幅(番地), --ram で宣言した範囲 [(始まり, 大きさ)]]
def bounds_error(addr, op):
    """--check-bounds: 番地 addr への読み(op="読み")・書き(op="書き")が、装置の帯・宣言した範囲の外ならエラー。UART と帯の中は通す。
    --ram を宣言していれば、宣言した範囲と帯の外はすべてエラー。宣言が無ければ、帯の手前・終端の先の見張る幅の中(はみ出し)だけエラー。"""
    if addr == UART: return None
    for d in DEVICES:
        if d.base <= addr < d.base + d.size: return None
    for s, z in BOUNDS[2]:
        if s <= addr < s + z: return None
    if BOUNDS[2]:
        return f"境界: {op}の番地 0x{addr:x} は、装置の帯と --ram で宣言した範囲のどれにも入っていません"
    g = BOUNDS[1]
    for d in DEVICES:
        end = d.base + d.size; nm = type(d).__name__
        if end <= addr < end + g: return f"境界: {op}の番地 0x{addr:x} は {nm} の帯 [0x{d.base:x}, 0x{end:x}) の終端から {addr - end + 1} 番地先です(はみ出し)"
        if d.base - g <= addr < d.base: return f"境界: {op}の番地 0x{addr:x} は {nm} の帯 [0x{d.base:x}, 0x{end:x}) の手前 {d.base - addr} 番地です(はみ出し)"
    return None
DEVICES = []                                   # メモリマップド装置(sign_gfx.Display など)。base/size/read/write を持つ

_DEV_RANGE = [0, 1 << 62, 0]                    # [装置の数, 最小の番地, 最大の番地(の次)]。帯の外の読み書きは装置を探さない

def device_at(addr):
    r = _DEV_RANGE
    if r[0] != len(DEVICES):
        r[0] = len(DEVICES)
        r[1] = min((d.base for d in DEVICES), default=1 << 62); r[2] = max((d.base + d.size for d in DEVICES), default=0)
    if addr < r[1] or addr >= r[2]: return None
    for d in DEVICES:
        if d.base <= addr < d.base + d.size: return d
    return None

def write_addr(addr, data):                    # アドレスにデータを入れ、成功したらアドレスを返す
    if is_unit(addr) or is_unit(data): return UNIT                  # __ # X も X # __ も __(/dev/null 相当)
    if isinstance(addr, LaneRef):                                    # ($v + 4k) # f : 第 k レーンへ。Float だけ
        if not isinstance(data, float): return UNIT
        cur = addr.var.env.vars[addr.var.name]
        addr.var.env.vars[addr.var.name] = Vec(data if i == addr.lane else x for i, x in enumerate(cur))
        return addr
    if isinstance(addr, VarRef):                                     # $x # y : x のスロットへ書く
        cur = addr.env.vars.get(addr.name)
        if isinstance(cur, Vec):                                     # Vector の型は固定: Float は第 0 レーン、Vector は全体、他は __
            if isinstance(data, float): data = Vec((data,) + tuple(cur[1:]))
            elif not isinstance(data, Vec): return UNIT
        addr.env.vars[addr.name] = data
        return addr
    if STRICT_GATES and isinstance(addr, Places):                   # R26・R62: 語の場所の List へは、語ごとに書く(`(0x10 ' [1 ~ 3]) # [7 8 9]`)
        vals_ = list(data) if isinstance(data, list) and not isinstance(data, str) else [data]
        if len(vals_) != len(addr): return UNIT
        for a_, x_ in zip(addr, vals_): write_addr(a_, x_)
        return addr
    if not isinstance(addr, int) or isinstance(addr, bool): return UNIT
    if BOUNDS[0] and (m_ := bounds_error(addr, "書き込み")) is not None: raise SignError(m_)
    ret = addr
    if STRICT_GATES and type(addr) is WInt and addr % addr.w: return UNIT      # R62: 生まれた幅の倍数でない番地の `#` は `!_`(何も書かない)
    if type(addr) is WInt:                                           # 幅つきの番地: 値をその幅(byte)へ切る(`1x… # 0x1234` は下位 1 byte だけ)。§5.9
        if isinstance(data, int) and not isinstance(data, bool): data = data & ((1 << (8 * addr.w)) - 1)
        addr = int(addr)
    if addr == UART:
        if is_num(data) and not isinstance(data, str) and (int(data) & 0xFF) >= 0x80 and hasattr(sys.stdout, "buffer"):
            sys.stdout.flush(); sys.stdout.buffer.write(bytes([int(data) & 0xFF]))                  # UART は 1 バイトの口: Int の 0x80 以上は生のバイトのまま(UTF-8 の続きもそのまま通る)
        else: sys.stdout.write(data if isinstance(data, str) else chr(int(data) & 0xFF) if is_num(data) else show(data))
        sys.stdout.flush()
    elif (d := device_at(addr)) is not None: d.write(addr - d.base, data)
    else: MEMORY[addr] = data
    return ret

def r93_apply(m, n, i, env):
    """R93: `F … x , R` は `F … (x , R)` を、`,` のすぐ左の項の並び x(最後の括りに入る項。前の裸の口を埋めた後ろの2項以上も、書いた `_` も)に広げる。
    最後の括りに入る形は、書いた形のまま実引数(`fp 1 2 , 3` は `fp (1 2 , 3)` の `[[1 2] 3]`)。"""
    items = m[1]
    vals = {}
    j = None
    for idx, x in enumerate(items):
        if x in (MARK, HOLE): 
            if j is None: return None
            continue
        v = ev(x, env); vals[idx] = v
        if isinstance(v, (Closure, Stream)) and j is None: j = idx
        elif j is None and (is_unit(v)): return None
    if j is None: return None
    f = vals[j]
    if not (isinstance(f, Closure) and not f.variadic and f.native is None and f.params is not None and not f.dead and not has_defaults(f)): return None
    rem = len(f.params) - len(f.args)
    if rem < 1 or f.params[-1][0] != "destr" or any(sp[0] != "name" for sp in f.params[len(f.args):-1]): return None
    b = rem - 1
    tail = list(range(j + 1, len(items)))
    nm = [t for t in tail if items[t] not in (MARK, HOLE)]
    if len(nm) < b: return None
    if any(isinstance(vals[t], (Closure, Stream)) or is_unit(vals[t]) or vals[t] is ID for t in nm): return None       # 恒等射は関数(compose)
    first_x = nm[b] if len(nm) > b else ((nm[b - 1] if b else j) + 1)
    # 裸の口を埋める部分に書いた _ は混ぜない
    if any(items[t] in (MARK, HOLE) for t in tail if t < first_x): return None
    x_items = items[first_x:]
    if not x_items: return None
    xn = x_items[0] if len(x_items) == 1 else ("seq", x_items)
    xv = ev(("prod", [xn] + list(n[1][i + 1:])), env)
    res = finalize(run_with(f, [vals[t] for t in nm[:b]] + [xv]))
    if j:
        acc = vals[0]
        for v in [vals[t] for t in range(1, j) if t in vals] + [res]: acc = join(acc, v)
        res = acc
    return res
def r66_ok(vs):
    j = 0
    while j < len(vs) and not isinstance(vs[j], (Closure, Stream)): j += 1       # 値の後ろに積まれた F(`5 f 1 , 2` は `5 (f (1 , 2))`)
    if j >= len(vs) or any(is_unit(v) for v in vs[:j]): return False
    return r66_head(vs[j:])
def r66_head(vs):
    f = vs[0]
    if not (isinstance(f, Closure) and not f.variadic and f.native is None and f.params is not None and not f.dead): return False
    rem = len(f.params) - len(f.args)
    return rem >= 1 and f.params[-1][0] == "destr" and len(vs) - 1 == rem \
        and not any(isinstance(v, (Closure, Stream)) or is_unit(v) or v is ID for v in vs[1:])      # 恒等射は関数(`fp i , 1 , 2` は compose fp i)
def dop_mark(c):
    """R59: `$` を通して `@` で開いた括りの関数(仮引数を持つ物)に印を付ける。呼んだ実体の本体に余りがあれば G20。"""
    if STRICT_GATES and isinstance(c, Closure) and not c.dop and not c.native and c.params is not None and not c.variadic:
        return _cp(c, dop=True)
    return c
def ru_unit(v): return UNIT if isinstance(v, Closure) and v.ru else v
def leftover_operand(v):
    """R76: 比べと論理(段5〜8)の被演算子に丸ごと残った関数は _ になり、恒等射でなければ知らせる(R42・R48)"""
    if isinstance(v, Closure) and not v.dead:
        warn("leftover-lambda", LEFTOVER_MSG + "(比べ・論理の被演算子。関数を値として置くなら `$` を付けます)", operand=True)
        return UNIT
    return v
ID_MSG = "恒等射が、`!_` が答えを `!_` にする所({where})に残り、`!_` になります(§4 R48)。値を置くつもりなら値を書き、関数を当てるなら実引数を後ろに書きます"
def fn_operand(v, where):
    """R87(--strict): 引く器の側(`'` の左・`@` の右)に丸ごと残った関数は `!_` で、leftover-lambda で知らせる(`inc ' 0`)"""
    if STRICT_GATES and isinstance(v, Closure) and not v.dead and v is not ID:
        warn("leftover-lambda", LEFTOVER_MSG + f"({where}。器でない関数からは引けません。R87)", operand=True); return UNIT
    return v
def id_operand(v, where):
    """R48: 恒等射(`i : _` の i など)が、`!_` が答えを `!_` にする所(`&` の両辺・比べ・`==`・`!==`・範囲・引く器の側・`#` の左・手続きの最後でない行・枝の条件)に残れば、
    ほかの関数と同じに leftover-lambda で知らせて `!_`(--strict)"""
    if STRICT_GATES and v is ID:
        warn("leftover-lambda", ID_MSG.format(where=where), operand=True); return UNIT
    return v
def ev_unit_op(n, env):
    """R137・V7(2026-11-07): `|`・`;` の辺は関数のまま読む。`_` の辺(出どころに依らず)は演算子ごと消え、1つだけ残れば行の置かれた所のまま
    (括りの中・定義の右辺なら関数、評価する所なら `_` で知らせる)。2つ以上残れば `,` と同じく丸ごとの関数の辺は `_` で消える。
    `|`: 左が(関数でない)値なら右を読まずに左。`;`: 両側を読み、片方だけが値ならその値、両方値か両方 `_` なら `_`。"""
    op = n[1]; here = id(n) in EVAL_PRODS
    def edge(m):
        v = ru_unit(ev(m, env))
        if v is ID: return FnEdge(ID)                             # 2026-11-17 仕様(R61・V7): 恒等射は単位でなく丸ごとの関数の辺
        return comma_edge(v, keep=True) if isinstance(v, Closure) else v
    def lone(e):                                                  # 1つだけ残った辺
        if isinstance(e, FnEdge):
            if here: drop_fn_edge("(`%s` の被演算子。関数を値として置くなら `$` を付けます)" % op, e); return UNIT
            return e.v
        return e
    l = edge(n[2])
    if op == "|":
        if not isinstance(l, FnEdge) and not is_unit(l):
            if n[2][0] == "lit" and n[3][0] == "id":                  # R76・V7: 左が `!_` でありえない書いた値なら、右の関数はいつも余る(`(3 | inc) 5`)
                r0 = edge(n[3])
                if isinstance(r0, FnEdge): drop_fn_edge("(`|` の被演算子。関数を値として置くなら `$` を付けます)", r0)
            return l
        r = edge(n[3])
        if is_unit(l): return lone(r)
        if is_unit(r): return lone(l)
        drop_fn_edge("(`|` の被演算子。関数を値として置くなら `$` を付けます)", l)           # 左が丸ごとの関数
        if isinstance(r, FnEdge): drop_fn_edge("(`|` の被演算子。関数を値として置くなら `$` を付けます)", r); return UNIT
        return r
    r = edge(n[3])
    live = [x for x in (l, r) if not is_unit(x)]
    if not live: return UNIT
    if len(live) == 1: return lone(live[0])
    vals = []
    for x in live:
        if isinstance(x, FnEdge): drop_fn_edge("(`;` の被演算子。関数を値として置くなら `$` を付けます)", x)
        else: vals.append(x)
    return vals[0] if len(vals) == 1 else UNIT
def binop(op, l, rt):                                          # rt: 右辺の thunk(継続の規則)
    if STRICT_GATES:                                           # R65・Q73: 実行時の _ で口を開けたまま残った関数は、演算子の被演算子では _
        l = ru_unit(l); _rt = rt; rt = lambda: ru_unit(_rt())
        if op in (";", "|", "&", "==", "!==", "<", "<=", "=", ">=", ">"):     # 法則48: `=` `<` なども `==` と同じ知らせ(段13 の値の演算子の被演算子にも関数が残れば _)
            l = leftover_operand(l); _rt2 = rt; rt = lambda: leftover_operand(_rt2())
    if STRICT_GATES and op in R48_OPS:                          # R48: 恒等射が `!_` が答えを `!_` にする所の被演算子に残れば知らせて `!_`
        if op in ("'", "#"): l = id_operand(l, f"`{op}` の左")
        elif op != "@": l = id_operand(l, f"`{op}` の被演算子")
        if op != "#":
            _rt3 = rt; _wh = "`@` の右" if op == "@" else ("`'` の右" if op == "'" else f"`{op}` の被演算子")
            rt = (lambda: _rt3()) if op == "'" else (lambda: id_operand(_rt3(), _wh))
    if STRICT_GATES and op in ABS_OPS:                          # R62: 関数を指す番地を当てた値の演算子の答え(ABS)は、外の値の演算子と `==`・`!==` で運ばれる
        if l is ABS: rt(); return ABS
        if not (is_unit(l) and op in ("<", "<=", "=", "==", ">=", ">")):
            r_ = rt()
            if r_ is ABS: return ABS
            rt = lambda: r_
    if op == "#":
        EFFECTS[0] += 1
        r = rt()
        if STRICT_GATES and isinstance(r, Closure) and not r.dead:       # R116: 書き込む値は評価する所。裸の関数は _ になり、`$inc` を案内する
            warn("leftover-lambda", "`#` の右(書き込む値)は評価する所なので、裸の関数は _ になって消えます。関数の番地を書き込むなら `$inc` と書きます(R116)")
            r = UNIT
        if STRICT_GATES and isinstance(l, Closure) and not l.dead and l is not ID:      # R87: `#` の左に丸ごと残った関数は場所でなく `!_`(leftover-lambda)
            rt(); warn("leftover-lambda", LEFTOVER_MSG + "(`#` の左。関数は書く場所になりません。R87)", operand=True); return UNIT
        if STRICT_GATES and is_fn_target(l):                           # R62: 関数は場所でない。関数を指す番地を `#` の左に置いた行は level-mismatch で、何も書かない
            warn("level-mismatch", LEVEL_MSG.format(op="#") + "(関数を指す番地は書く場所になりません)"); return UNIT
        if STRICT_GATES and holds_addr(r) and (is_addr(l) or isinstance(l, (VarRef, LaneRef))): store_warn(None, "`#`")     # R62: 番地の先・場所へ番地を書く行
        return write_addr(l, r)
    if op == "&":
        if is_unit(l): return UNIT
        r = rt(); return UNIT if is_unit(r) else r
    if op == "|": return l if not is_unit(l) else rt()
    if op in ("<", "<=", "=", "==", ">=", ">"):
        if is_unit(l): return UNIT                             # 零射: 右辺は評価しない
        r = rt(); return UNIT if is_unit(r) else compare(op, l, r)
    r = rt()
    if op in ("!=", "!=="):                                    # 両辺とも恒等射
        if STRICT_GATES and (is_unit(l) or is_unit(r)): return UNIT          # R48: `!=`・`!==` も `!_` が答えを `!_` にする所
        if is_unit(l) or is_unit(r):
            return UNIT if is_unit(l) and is_unit(r) else (r if is_unit(l) else l)
        return compare(op, l, r)
    if op == ";":                                              # 短絡しない。両方非Unitなら相殺
        return UNIT if is_unit(l) == is_unit(r) else (r if is_unit(l) else l)
    if op == ",": return product([l, r])
    if op == "~":
        return make_range(l, r)
    if op in ("~+", "~-", "~*", "~/", "~^"): return make_open_range(op, l, r)
    if op == "'": return get_value(l, r)
    if op == "@": return get_value(r, l)
    return arith(op, l, r)

def product(vals):                             # 直積: Unit は落ち、後置 ~ の列はその場で展開される
    out = []
    for x in vals:
        if isinstance(x, Stream): out.extend(x)
        elif not is_unit(x): out.append(x)
    return out

def logical_not(v): return ID if is_unit(v) else UNIT
FACT_LIMIT = 100_000                           # 実装の守り: 階乗の引数の上限(超えると結果が大きすぎて計算を終えられない)
def factorial(v):
    if isinstance(v, int) and not is_unit(v) and v > FACT_LIMIT: raise SignError(f"結果が大きすぎます(実装の上限は {FACT_LIMIT:,} の階乗まで)")
    return math.factorial(v) if isinstance(v, int) and v >= 0 and not is_unit(v) else UNIT
_NOFN = frozenset([Closure])                  # 型の集合どうしの isdisjoint は C で回る(要素ごとの isinstance の生成式より桁違いに速い)
_NOFN2 = frozenset([Closure, Stream])
def expand(v):
    if STRICT_GATES and isinstance(v, list) and not _NOFN.isdisjoint(map(type, v)):                  # 関数を含むか(C の速さで型を見る。Closure に派生は無い)
        strict_gate("G7: 関数を含む器は撒けません(`fs~`)")
    if isinstance(v, Struct) and v: return SpreadStruct(v)
    if is_unit(v): return Stream()
    if isinstance(v, str) and not isinstance(v, Char): return Stream(Char(c) for c in v)   # (String)~ は文字へ撒かれる
    if isinstance(v, Stream): return v
    if isinstance(v, list):
        if v and all(isinstance(e, list) and not isinstance(e, Stream) and e for e in v):
            return Stream(x for e in v for x in e)          # 多次元: 内側を1段階展開([1 2 , 3 4]~ = 1 2 3 4)
        return Stream(v)
    return Stream([v])

# --- ポイントフリー ---
CMP_FOLD = ("<", "<=", ">", ">=", "==", "=")
def fold_cmp(op, args):
    """R31(2026-11-05 の寄せ4、--strict): 比べの点なしはその比べの圏の積。`[<]`・`[<=]` は min、`[>]`・`[>=]` は max(2項の値は `(a < b) | b | a` と同じ)、
    `[==]`・`[=]` は全部等しければその値(一番左の項)で、どこかが違えば `_`。`_` はどれでも単位で消える。項が1つならその値、`_` を除いて項が残らなければ `_`。"""
    if len(args) == 1 and isinstance(args[0], list): args = list(args[0])
    if any(a is ABS for a in args): return ABS                  # R62: 関数を指す番地を当てた答えの `!_` は、比べの点なしの項に来ても消えずに運ばれる(`[<] ($inc + 1) 3` は `!_`)
    xs = [a for a in args if not is_unit(a)]
    if not xs: return UNIT
    if op in ("==", "="):                                       # `_` を除いた並び全体を一度に見る(2つずつ畳まない)
        first = xs[0]
        return first if all(not is_unit(binop(op, first, lambda a=a: a)) for a in xs[1:]) else UNIT
    acc = xs[0]
    for b in xs[1:]:
        r = binop(op, acc, lambda b=b: b)                       # 成り立てば左(acc)。外れたら b(単位の b は上で除いてある)
        if r is ABS: return ABS                                  # R62: 関数を指す番地・番地と数の混ぜの比べは `!_`(畳まずに運ぶ)
        acc = acc if not is_unit(r) else b
    return acc

def fold_args(op, args):
    if STRICT_GATES and op in CMP_FOLD: return fold_cmp(op, args)
    if len(args) == 1 and isinstance(args[0], list): args = list(args[0])      # [+] ([< 3,] 1 5 2) = 3(利用者の回答 2026-10-07)
    if op == "|":
        return next((a for a in args if not is_unit(a)), UNIT)
    if STRICT_GATES:                                           # R31(--strict): `[op] x1 … xn` は `x1 op … op xn` を結合の向きどおりに並べた物と同じ。`_` は中置の被演算子と同じに読む(`[+] 1 _ 3` は 4、`[&] 1 _ 3` は `_`)
        if not args: return UNIT
        if op == "^":                                          # 右から(`[^] 2 3 2` は 2 ^ (3 ^ 2) で 512)
            acc = args[-1]
            for a in reversed(args[:-1]): acc = binop(op, a, lambda acc=acc: acc)
            return acc
        acc = args[0]
        for a in args[1:]: acc = binop(op, acc, lambda a=a: a)
        return acc
    if not args or any(is_unit(a) for a in args): return UNIT   # 完全性公理
    if op == "&": return args[-1]
    if op == "^":                                              # 冪は右結合(operator_table の中置※。alpha の参照実装も `[^] 2 3 2` は 512)。既定も --strict と同じに右から畳む
        acc = args[-1]
        for a in reversed(args[:-1]): acc = binop(op, a, lambda acc=acc: acc)
        return acc
    acc = args[0]
    for a in args[1:]: acc = binop(op, acc, lambda a=a: a)
    return acc

def map_args(op, kind, v, args):
    text = len(args) == 1 and isinstance(args[0], str) and not isinstance(args[0], Char)
    if text: args = [Char(c) for c in args[0]]                                  # 文字列は文字の並び
    elif len(args) == 1 and isinstance(args[0], list): args = list(args[0])
    if STRICT_GATES and op != "|":                              # R137・R95: 並びの項の `!_` は単位で消える(`[* 2,] 1 w 3` は `[2, 6]`)。何も残らなければ何も受けていない関数
        args = [x for x in args if not is_unit(x)]
        if not args:
            warn("leftover-lambda", LEFTOVER_MSG + "(写像の点なしが `!_` だけを受け、何も受けていません。R95)"); return UNIT
    out = []
    for x in args:
        if is_unit(x) and op != "|": return UNIT
        r = binop(op, x, lambda: v) if kind == "right" else binop(op, v, lambda: x)
        if op in CMP:                                           # 選択写像: 真なら要素を残す
            if not is_unit(r): out.append(x)
        else: out.append(r)
    if text and out and all(isinstance(r, str) for r in out): return "".join(out)   # 文字列に写せば、String が吸収して1本になる
    return out

def map_unary(f, args):                                         # 席の写像(§2): 並び全体を受け、要素ごとに値の印を当てる。文字列は文字の並び
    text = len(args) == 1 and isinstance(args[0], str) and not isinstance(args[0], Char)
    if text: args = [Char(c) for c in args[0]]
    elif len(args) == 1 and isinstance(args[0], list): args = list(args[0])
    out = []
    for x in args:
        if is_unit(x): return UNIT
        r = f(x)
        if not is_unit(r): out.append(r)                          # 並びの要素の `!_` は消える(R83)
    return out if out else UNIT

def map_fn(f, args):
    while isinstance(f, (Ref, VarRef)): f = f.value if isinstance(f, Ref) else f.env.vars.get(f.name, UNIT)
    if STRICT_GATES and not isinstance(f, Closure): return UNIT          # §2: F が要素1つに当てて閉じる関数でない `[F,]`(`[$_,]` ほか)は種類の分からない普通の括り(断らない)
    if not isinstance(f, Closure) or f.dead: return UNIT
    if STRICT_GATES and slots_left(f) != 1:        # R50: F は要素1つに当てて閉じる関数。口が2つ以上・分からない関数は決まらない
        raise Gate("G7: `[F,]` の F は口が1つの関数にします(口が2つ以上か口の数が分からない関数は写せません)")
    if len(args) == 1 and isinstance(args[0], str) and not isinstance(args[0], Char): args = [Char(c) for c in args[0]]
    elif len(args) == 1 and isinstance(args[0], list): args = list(args[0])
    out = []
    for x in args:
        if is_unit(x): return UNIT
        out.append(finalize(apply(f, x)))
    return out

def make_section(kind, op, v, comma):
    c = _make_section(kind, op, v, comma)
    c.pf = True
    return c

def _make_section(kind, op, v, comma):
    if kind == "fold":
        c = native_var(lambda args: fold_args(op, args))
        c.foldsec = op != ","                                    # 畳む2項の点なし [+]: 末尾の _ は `1 + _`(R31)で、R138 の消える印の外
        c.foldop = op
        if op in ("<<", ">>", "!=", "!=="):
            c.nofold = True
            if STRICT_GATES: info("pointfree-not-folded", f"畳まない2項の点なし `[{op}]` は、素の2引数の関数として読みます(k = 2 は適用、k = 1 は部分適用、k > 2 は余りを積みます。R32)")
        return c
    if kind == "mapf": return native_var(lambda args: map_fn(v, args))              # [F,] : F は口が1つの関数。要素ごとの写像(R50)
    one = {"not": logical_not, "neg": lambda x: -x if is_num(x) else UNIT,
           "bnot": lambda x: ~x if isinstance(x, int) and not isinstance(x, bool) else UNIT, "fact": factorial}.get(kind)
    if one is not None:
        if comma: return native_var(lambda args: map_unary(one, args))          # 席の写像 `[-_,]`・`[!_,]`・`[!!_,]`・`[_!,]`: 要素ごとに当てる貪欲な単項(§2 の表)
        return native_fixed(one, 1)
    if comma: return native_var(lambda args: map_args(op, kind, v, args))
    if kind == "right": return native_fixed(lambda x: binop(op, x, lambda: v), 1)
    return native_fixed(lambda x: binop(op, v, lambda: x), 1)

# ============================== 字句 ==============================
class LStr(str):                               # 論理行の本文。始まりの行と字下げを持つ(エラーの場所のため)
    lineno = 0; indent = 0
def lstr(text, lineno, indent):
    r = LStr(text); r.lineno, r.indent = lineno, indent
    return r

class Tok:
    _FIELDS = ("kind", "text", "start", "end", "pos", "node", "line", "col"); __repr__ = _rec_repr
    __hash__ = None
    def __init__(self, kind, text, start, end, pos="", node=None, line=0, col=0):
        self.kind = kind; self.text = text; self.start = start; self.end = end; self.pos = pos; self.node = node; self.line = line; self.col = col
    def __eq__(self, o): return o.__class__ is self.__class__ and all(getattr(self, f) == getattr(o, f) for f in self._FIELDS)

PATTERNS = [
    ("STR", r"`[^`\r\n]*`"), ("CHAR", r"\\[^\r]"),
    ("ADDR", r"[0-9]+x[0-9A-Fa-f]+"), ("UNI", r"0u[0-9A-Fa-f]+"), ("REG", r"0r[0-9A-Fa-f]+"),
    ("BIN", r"0b[01]+"), ("OCT", r"0o[0-7]+"), ("NUM", r"\d+(?:\.\d+)?"),
    ("HOLE", r"_(?![A-Za-z0-9_])"), ("ID", r"[A-Za-z_][A-Za-z0-9_]*"),
    ("OPEN", r"[(\[{]"), ("CLOSE", r"[)\]}]"), ("SP", r"[ \t]+"), ("NODE", r"\x01"), ("ROWSEP", r"\x02"),
    ("OP2", r"###|##|!==|<<|>>|\|\||;;|&&|!!|<=|>=|!=|==|><|~\+|~-|~\*|~/|~\^"), ("OP", r"[^\sA-Za-z0-9_()\[\]{}`\\]"),
]
RX = re.compile("|".join(f"(?P<{k}>{p})" for k, p in PATTERNS))
ATOMS = {"NUM", "STR", "CHAR", "ADDR", "UNI", "REG", "BIN", "OCT", "HOLE", "ID", "NODE"}

BINARY_ONLY = {"~+", "~-", "~*", "~/", "~^", ",", ";", "&", "==", "!==", "+", "*", "/", "%", "^", "<<", ">>", "&&", ";;",
               "<", ">", "<=", ">=", "=", "!=", "?", ":", "'"}

def r138_gate(reason, text, t, line, ind):
    msgs = {"void-written": f"void-written: 手で書いた `!_` の項 `{text}` があります。`!_`(void)は手で書きません。何も無い所には何も書かず、`!_` は計算の答えとしてだけ生まれます(§4 R138)。恒等射と穴は `_`、否定の点なしは `[!_]` のように括って書きます。",
            "empty-written": f"empty-written: 書いた空の器 `{text}` があります。空の器は手で書きません。空は計算の答えとしてだけ生まれます(§4 R138)。"}
    e = Gate(msgs[reason])
    if line: e.loc = (PARSE_FILE, line, ind + t.start + 1)
    return e
def r138_spelling(toks, line, ind):
    """R138(§7.61、2026-11-08〜09): `_` は id、`!_` は void。内部の木は前の綴り(`_` が void、`!_` が id)のままなので、綴りをここで写す。
    核 `_` のいちばん内側の前置が `!` なら、手で書いた void として断る(void-written)。ただし点なしの席(`[!_]`・`[-_]`・`[!!_]`・`[_!]`)の括りの中の2語の行は綴りのまま。
    ほかの `_` は id(NODE の葉 `!_`)。書いた空の器(`[]`・`()`・`{}`・``` `` ```)は断る(empty-written)。"""
    out = []; n = len(toks)
    adj = lambda a, b: a.end == b.start
    close_of = {"[": "]", "(": ")", "{": "}"}
    for i, t in enumerate(toks):
        if t.kind == "STR" and t.text == "``": raise r138_gate("empty-written", "``", t, line, ind)
        if t.kind == "OPEN" and i + 1 < n and toks[i + 1].kind == "CLOSE" and close_of.get(t.text) == toks[i + 1].text:
            raise r138_gate("empty-written", t.text + toks[i + 1].text, t, line, ind)
        if t.kind != "HOLE": out.append(t); continue
        a = toks[i - 2] if i >= 2 else None; b = toks[i - 1] if i >= 1 else None
        c = toks[i + 1] if i + 1 < n else None; d = toks[i + 2] if i + 2 < n else None
        e_ = d.kind == "OP" and d.text == "," and i + 3 < n and toks[i + 3].kind == "CLOSE" if d is not None else False   # `[-_,]`
        seat = (a is not None and a.kind == "OPEN" and b.kind == "OP" and b.text in SEAT_PRE and c is not None and (c.kind == "CLOSE" or (c.kind == "OP" and c.text == "," and d is not None and d.kind == "CLOSE"))) \
            or (b is not None and b.kind == "OPEN" and c is not None and c.kind == "OP" and c.text in SEAT_POST and d is not None and (d.kind == "CLOSE" or e_))
        if seat: out.append(t); continue
        if out and out[-1].kind == "OP" and out[-1].text == "!" and adj(out[-1], t) and not (len(out) >= 2 and adj(out[-2], out[-1]) and (out[-2].kind in ATOMS or out[-2].kind == "CLOSE")):
            raise r138_gate("void-written", "!_", out[-1], line, ind)
        nt = Tok("NODE", "_", t.start, t.end, node=("not", ("hole",)), line=t.line, col=t.col)     # 書いた `_` は id(内部は前の綴りの `!_`)
        out.append(nt)
    return out

SEAT_PRE = {"-", "!", "!!", "~", "@", "#"}      # 席の点なし `[-_]`・`[!_]`・`[!!_]`・`[$_]`・`[~_]`・`[@_]`・`[#_]` の前置(§2 の表)。中置の区間 `[< _]` の `_` は恒等射(R29)
SEAT_POST = {"!", "@", "~"}                          # 後置の席 `[_!]`・`[_@]`
def tokenize(src, nodes=None):                 # \x01 は括りブロックの差し込み位置(nodes を順に割り当てる)
    i, toks = 0, []
    line, ind = getattr(src, "lineno", 0), getattr(src, "indent", 0)
    while i < len(src):
        m = RX.match(src, i)
        if not m:
            err = SyntaxError(f"字句エラー: {i} 文字目 {src[i]!r}")
            if line: err.loc = (PARSE_FILE, line, ind + i + 1)
            raise err
        k = "OP" if m.lastgroup == "OP2" else m.lastgroup
        if k != "SP": toks.append(Tok(k, m.group(), m.start(), m.end(), line=line, col=ind + m.start() + 1))
        i = m.end()
    pending = list(nodes or [])
    for t in toks:
        if t.kind == "NODE":
            if not pending: raise SyntaxError("ブロックの差し込み位置が不正です")
            t.node = pending.pop(0)
    if STRICT_GATES: toks = r138_spelling(toks, line, ind)
    if STRICT_GATES:                                                 # R26・R79: 前に空白か開き括りがあり、後ろに続けて書いた `~-1` は前置 `~` と `-1`(`5 ' ~-1` は `5 ' [-1]`)
        out_ = []
        for n, t in enumerate(toks):
            q = toks[n + 1] if n + 1 < len(toks) else None
            p = out_[-1] if out_ else None
            if (t.kind == "OP" and t.text in ("~-", "~+") and q is not None and q.start == t.end and q.kind in ATOMS
                    and (p is None or p.end < t.start or p.kind == "OPEN")):
                out_.append(Tok("OP", "~", t.start, t.start + 1, line=t.line, col=t.col))
                out_.append(Tok("OP", t.text[1], t.start + 1, t.end, line=t.line, col=t.col + 1)); continue
            out_.append(t)
        toks = out_
    for n, t in enumerate(toks):               # 空白の位置で 前置/後置/中置 を決める
        if t.kind != "OP": continue
        p = toks[n - 1] if n else None
        q = toks[n + 1] if n + 1 < len(toks) else None
        pt = bool(p) and p.end == t.start and (p.kind in ATOMS or p.kind == "CLOSE"
                                              or (p.kind == "OP" and p.pos == "postfix"))
        nt = bool(q) and q.start == t.end and q.kind != "CLOSE"
        if t.text in ("~", "@") and q and q.kind == "OP" and q.text == "~" and q.start == t.end and pt: nt = False   # i~~ / `f`@~
        t.pos = {(0, 1): "prefix", (1, 0): "postfix", (0, 0): "infix", (1, 1): "infix_tight"}[(pt, nt)]
        if t.pos in ("prefix", "postfix") and t.text in BINARY_ONLY: t.pos = "infix"
    if STRICT_GATES:                                                 # 2026-11-17 仕様 P1: 演算子の表の外・演算を持たない綴り・結合の向きが違う中置の混ぜは、読む段で止める
        def _refuse(t, msg):
            e = SyntaxError(msg)
            if t.line: e.loc = (PARSE_FILE, t.line, t.col)
            raise e
        for n, t in enumerate(toks):
            if t.kind != "OP": continue
            q = toks[n + 1] if n + 1 < len(toks) else None
            if t.text == "==" and q is not None and q.kind == "OP" and q.text == "=" and q.start == t.end:
                _refuse(t, "operator-removed: `===` は演算子の表に演算がありません(表は1語として切ります)。等しさは `==`(深い比べ)か `=`(Int)で書きます(P1)")
            if t.text in ("!", "!!", "$") and t.pos in ("infix", "infix_tight"):
                _refuse(t, f"operator-unknown: `{t.text}` は演算子の表に中置の語がありません(前置・後置の印は被演算子に付けて書きます。`!x`・`x!`・`$f`。P1)")
        _qs = [t for t in toks if t.kind == "OP" and t.text == "'" and t.pos in ("infix", "infix_tight")]
        _as = [t for t in toks if t.kind == "OP" and t.text == "@" and t.pos in ("infix", "infix_tight")]
        if _qs and _as:
            _refuse(max(_qs[0], _as[0], key=lambda t: t.start), "infix-mixed-assoc: 同じ行に中置の `'`(左結合)と `@`(右結合)があります(括っても止めます)。一方の綴りに揃える(`vs ' 0 ' 1`・`1 @ 0 @ vs`)か、行を分けます(P1)")
    return toks

# ============================== 構文解析 ==============================
SP = 105                                       # 余積(空白)の段
INFIX = {"#": (40, True), ";": (50, False), "|": (60, False), "&": (70, False), "==": (80, False), "!==": (80, False),
         ",": (90, True), "~": (110, False), "~+": (110, False), "~-": (110, False), "~*": (110, False), "~/": (110, False), "~^": (110, False),
         "+": (130, False), "-": (130, False),
         "*": (140, False), "/": (140, False), "%": (140, False), "^": (150, True),
         "'": (170, False), "@": (170, True), "<<": (180, False), ">>": (180, False),
         "||": (190, False), ";;": (200, False), "&&": (210, False)}
CMPCHAIN = {"<", "<=", "=", ">=", ">", "!="}   # 120
POSTP = {"!": 220, "~": 220, "@": 240}
PREFIX_START = {"!", "-", "!!", "$", "@", "~", "|", "||"}
SECTION_OPS = set(INFIX) | CMPCHAIN

def uint_lit(v, s):
    if v > UMASK and INTCHK[0]: raise SignError(f"字面 {s} は UInt の値域(0 〜 2^64 − 1)の外です(コンパイルエラー。integer_overflow.md §1.1 末)")
    return v & UMASK                                     # 既定は環の上の値として 2^64 で回す【実装】
def atom_node(t):
    k, s = t.kind, t.text
    if k == "NUM":
        if "." in s: return ("lit", float(s))
        v = int(s)
        if INTCHK[0] and v > INT_MAX: raise SignError(f"十進の字面 {s} は Int の値域(-{INT_MAX} 〜 {INT_MAX})の外です(コンパイルエラー。integer_overflow.md §1.1 末。回したい数は 0r で書く)")
        return ("lit", v)
    if k == "STR": return ("lit", UNIT if s == "``" else s[1:-1])
    if k == "CHAR": return ("lit", Char(s[1:]))
    if k == "ADDR":
        nw, hx = s.split("x", 1); v = int(hx, 16)
        if int(nw) == 0: return ("lit", v, "Address")
        w = int(nw)
        if w not in WIDTHS: raise SignError(f"幅 {w} byte の読み書きの命令は機械にありません(`{s}`。幅は 1・2・4・8 byte。16 byte は layer 3 の SIMD で未対応。value_representation.md §5.2)")
        x = WInt(v); x.w = w
        return ("lit", x, "Address")
    if k == "REG": return ("lit", uint_lit(int(s[2:], 16), s), "UInt")
    if k == "UNI": return ("lit", Char(chr(int(s[2:], 16))))
    if k == "BIN": return ("lit", uint_lit(int(s[2:], 2), s), "UInt")
    if k == "OCT": return ("lit", int(s[2:], 8))
    if k == "HOLE": return ("hole",)
    if k == "NODE": return t.node
    return ("id", s)

def no_hole(node):                             # 書いた _ はいつも印(値)。中置の被演算子でも値の段が読む(2026-10-21)
    if node == ("not", ("hole",)) and not STRICT_GATES:      # 既定のモード: 穴 !_ は、関数の実引数の位置にしか置けない(--strict では門にしない)
        strict_gate("G7: !_ は中置演算子の被演算子に置けません(穴の位置の外)")
    return node                                # --strict: 中置の被演算子の `_` 1つは `i : _` の i と同じ恒等射(R29。知らせは R48)

def leftover_tok_msg(t):
    if t.kind == "OP" and t.text == "#": return "export-mark-position: 使う所に前置 `#` は書けません。`#` は定義の行の頭で、定義する名前に付ける公開の印です(§4 R119)。使う所では `#` を外して名前だけを書きます"
    return f"解釈できないトークン: {t.text!r}"

class Parser:
    def __init__(self, toks, block=None): self.t, self.i, self.block = toks, 0, block
    def at(self, j): return self.t[j] if j < len(self.t) else None
    def peek(self): return self.at(self.i)
    def next(self): t = self.t[self.i]; self.i += 1; return t
    def is_op(self, t, g): return t is not None and t.kind == "OP" and t.text == g

    def parse_top(self):
        if self.is_op(self.peek(), "#") and self.peek().pos == "prefix" and not (STRICT_GATES and self.lambda_ahead()):     # 前置 # : export(`#x ? x` は仮引数の param-not-name)
            self.next()
            node = self.parse_top()
            if node[0] != "def": raise SyntaxError("export-mark-position: # は定義(名前 : 値)の前に置きます。使う所に書いた `#zq` は文法に無い形なので、読む段で止めます(§4 R119)。使う所では `#` を外して `zq` と書きます")
            return ("export", node)
        if (self.peek() and self.peek().kind == "OPEN" and self.at(self.i + 1) and self.at(self.i + 1).kind == "OP"
                and self.at(self.i + 2) and self.at(self.i + 2).kind == "CLOSE" and self.is_op(self.at(self.i + 3), ":")):
            op = self.at(self.i + 1).text               # [+] : a b ? ...  演算子のスコープ付き上書き
            self.i += 4
            return ("opdef", "[" + op + "]", self.parse_top())
        t, u = self.peek(), self.at(self.i + 1)
        if t and t.kind == "ID" and self.is_op(u, ":"):
            self.i += 2
            return ("def", t.text, self.parse_top())
        if self.lambda_ahead(): return self.parse_lambda()
        return self.parse_expr(0)

    def parse_row(self):                       # match_case の1行: 条件 : 値 / 既定値
        e = self.parse_expr(0)
        if self.is_op(self.peek(), ":"):
            self.next(); return (e, self.parse_top())
        return (None, e)

    # ---- ラムダ ----
    def lambda_ahead(self):
        j, n = self.i, 0
        while True:
            t = self.at(j)
            if t and t.kind == "OPEN":
                k, ok, dflt, depth = j + 1, True, False, 0
                while self.at(k) and (self.at(k).kind != "CLOSE" or depth > 0):
                    u = self.at(k)
                    if u.kind == "OPEN": depth += 1
                    elif u.kind == "CLOSE": depth -= 1
                    if u.kind == "OP" and u.text == ":": dflt = True     # `[~y : 5]`(G22 で断る綴り)・`[x : 1]`(括りの中の既定値。parse_param が読む)
                    elif not dflt and not (u.kind == "ID" or u.kind in ("OPEN", "CLOSE") or (u.kind == "HOLE" and not STRICT_GATES) or (STRICT_GATES and u.kind in ATOMS) or (u.kind == "OP" and (u.text == "~" or (STRICT_GATES and u.text == "#")))): ok = False      # `[[y : _]]` の重ねた括り([x] ≅ x)も仮引数の綴り
                    k += 1
                if not ok and dflt and STRICT_GATES: self.r131_ahead(j)
                if not ok or not self.at(k) or k == j + 1: break
                j, n = k + 1, n + 1
            elif t and (t.kind == "ID" or (t.kind == "HOLE" and not STRICT_GATES)): j, n = j + 1, n + 1      # 既定: 仮引数の `_` は使わない位置(preprocessor.md §1 の `R : [_ ~x] ? x`)
            elif STRICT_GATES and t and t.kind in ATOMS and n > 0: j, n = j + 1, n + 1       # R119: 名前でない項は parse_param が param-not-name で止める
            elif self.is_op(t, "~") and self.at(j + 1) and self.at(j + 1).kind == "ID": j, n = j + 2, n + 1
            elif STRICT_GATES and self.is_op(t, "#") and self.at(j + 1) and self.at(j + 1).kind == "ID": j, n = j + 2, n + 1      # R119: `gg : #x ? x` は param-not-name(parse_param が止める)
            elif STRICT_GATES and ((self.is_op(t, ",") and n > 0) or self.is_op(t, "~")) and self.at(j + 1) and self.at(j + 1).kind == "OPEN":
                self.r131_ahead(j + 1); break
            else: break
        return n > 0 and self.is_op(self.at(j), "?")

    def r131_ahead(self, j):                   # R131: 括りの中に `:` があり、閉じた先が `?` なら仮引数の括り。読む段で param-default-bracket(`x , [y : 1] ? x`・`x ~[y : 5] ? x`・`[a, b : 1, ~c] ? a`)
        depth, k, colon = 0, j, None
        while self.at(k):
            u = self.at(k)
            if u.kind == "OPEN": depth += 1
            elif u.kind == "CLOSE":
                depth -= 1
                if depth == 0: break
            elif colon is None and self.is_op(u, ":"): colon = k
            k += 1
        if colon is None or not self.at(k) or not self.is_op(self.at(k + 1), "?"): return
        ids = [self.at(x).text for x in range(j, colon) if self.at(x).kind == "ID"]
        raise r131_error(ids[-1] if ids else None, tok=self.at(colon))

    def parse_param(self):
        t = self.next()
        if t.kind == "OPEN" and self.peek() is not None and self.peek().kind == "OPEN":      # `[[y : _]]`・`([y : _])` : 重ねた括りは中の括りと同じ([x] ≅ x)
            inner = self.parse_param()
            if self.peek() is None or self.peek().kind != "CLOSE": raise SyntaxError("仮引数の閉じ括弧がありません")
            self.next(); return inner
        if t.kind == "OPEN":
            names, rest, after, dflts = [], None, [], {}
            while self.peek() is not None and self.peek().kind != "CLOSE":
                u = self.next()
                if self.is_op(u, "~"):
                    r_ = self.next(); rest = r_.text
                    if STRICT_GATES and r_.kind != "ID": raise SyntaxError(f"param-not-name: 括りの仮引数の中は名前で書きます(`~{rest}` は名前でない。§4 R119)")
                elif STRICT_GATES and self.is_op(u, ":") and u.kind == "OP":      # R131: 括りの中の `:` の行は、読む段で止める(G22 より先)
                    nm_ = (names[-1] if names else rest) or None
                    try: d_ = self.parse_expr(240)
                    except SyntaxError: d_ = None
                    raise r131_error(nm_, unit=(d_ in (("hole",), ("lit", []))))
                elif self.is_op(u, ":") and not rest and names and u.kind == "OP":      # `[x : 1]` : 括りの中の既定値(§3.4。1項だけ)
                    dflts[names[-1]] = self.parse_expr(240)
                    unit_default_gate(names[-1], dflts[names[-1]])
                    nx = self.peek()
                    if nx is not None and nx.kind not in ("CLOSE", "ID") and not self.is_op(nx, "~"): raise SyntaxError("括りの中の既定値は1項で書きます(`[x : 1]`)。式なら括ります(`[x : (1 + 1)]`)")
                elif self.is_op(u, ":") and rest: raise Gate("G22: 残りを受ける名前に既定値は付けられません(R67。既定値の括りは残りを受ける括り(参照の口)ではなく、括りの外の ~x と同じ廃止の綴り)。`[x ~xs]` と括って書きます")
                elif STRICT_GATES and u.kind != "ID":                      # R119: 括りの仮引数の中の名前でない項(`[#a]`・`[a 3]`・`[~#a]`)
                    raise SyntaxError(f"param-not-name: 括りの仮引数の中は名前で書きます(`{u.text}` は名前でない。§4 R119)。仮引数は外へ渡す名前でないので `#` は付けません。外へ渡すなら定義の行の頭に `#` を付けます")
                else: (after if rest else names).append(f"_{self.i}" if u.kind == "HOLE" else u.text)      # ~rest より後ろの名前は末尾から対応する
            if self.peek() is None: raise SyntaxError("仮引数の閉じ括弧がありません")
            self.next(); return ("destr", names, rest, dflts, after)
        if self.is_op(t, "~"):
            raise Gate("G22: 括りの外の ~x は仮引数に書けません(2026-10-04 に廃止、R67)。`[x ~xs]` と括って書きます")
        if t.kind == "HOLE" and not STRICT_GATES: return ("name", f"_{self.i}", None)      # 使わない位置(名前は付けない)
        if t.kind != "ID": raise SyntaxError(f"param-not-name: 仮引数は名前か括りで書きます(§3.4・R24・R119): {t.text!r}" + ("。仮引数は外へ渡す名前でないので `#` は付けません。外へ渡すなら定義の行の頭に `#` を付けます" if t.text == "#" else ""))
        return ("name", t.text, None)

    def parse_lambda(self):
        params = []
        while not self.is_op(self.peek(), "?"): params.append(self.parse_param())
        self.next()
        if self.peek() is None:
            if self.block is None: raise SyntaxError("ラムダの本体がありません")
            return ("lam", params, ("cases", check_body_rows(self.block, True)))
        if self.lambda_ahead(): return ("lam", params, self.parse_lambda())      # x ? y ? ... (入れ子。G16 が断る対象)
        return ("lam", params, self.parse_expr(0))

    # ---- 式(優先順位クライミング。空白 = 余積 は段 SP) ----
    def starts_operand(self, t):
        if t.kind in ATOMS or t.kind == "OPEN": return True
        return t.kind == "OP" and t.pos == "prefix" and t.text in PREFIX_START

    def parse_expr(self, minp):
        left = self.parse_prefix()
        while True:
            t = self.peek()
            if t is None: break
            if self.starts_operand(t):
                if SP < minp: break
                rhs = self.parse_expr(SP + 1)
                left = ("seq", left[1] + [rhs]) if left[0] == "seq" else ("seq", [left, rhs])
                continue
            if t.kind != "OP": break
            g = t.text
            if t.pos == "postfix":
                p = POSTP.get(g)
                if p is None or p < minp: break
                self.next()
                if g == "~" and left[0] == "post" and left[1] == "@": left = ("importspread", left[2])
                else: left = ("post", g, left)
                continue
            if t.pos == "prefix": break
            if g in CMPCHAIN:
                if 120 < minp: break
                if STRICT_GATES and left[0] == "bin" and left[1] in ("==", "!=", "!=="):
                    raise SyntaxError("compare-chain: 比べの連鎖で通すのは、向きの揃った3項の範囲と、`=` だけ・`==` だけの連鎖(何項でも)です(R119)。`=` と `==` の混ぜ・範囲と等しさの混ぜ・`!=` `!==` の連鎖は、括りで分けて書きます")
                operands, ops = [left], []
                while self.peek() and self.peek().kind == "OP" and self.peek().text in CMPCHAIN \
                        and self.peek().pos in ("infix", "infix_tight"):
                    ops.append(self.next().text); operands.append(self.parse_expr(130))
                for o in operands: no_hole(o)
                if STRICT_GATES and len(ops) >= 2 and not (len(ops) == 2 and (all(o in ("<", "<=") for o in ops) or all(o in (">", ">=") for o in ops))) and not all(o == "=" for o in ops):
                    raise SyntaxError("compare-chain: 比べの連鎖で通すのは、向きの揃った3項の範囲(`a < b < c`・`a <= b < c`・`a > b >= c` など。`<` と `<=`、`>` と `>=` は混ぜてよい)と、`=` だけ・`==` だけの連鎖(何項でも)です(R119)。4項以上の範囲・向きの揃わない物・`=` と `==` の混ぜ・範囲と等しさの混ぜ・`!=` `!==` の連鎖は、括りで分けて書きます(`(a < b) < c`)")
                left = ("cmp", operands, ops); continue
            info = INFIX.get(g)
            if info is None: break
            p, right = info
            if p < minp: break
            self.next()
            rhs = self.parse_expr(p if right else p + 1)
            if STRICT_GATES and g in ("==", "!=", "!==") and (rhs[0] == "cmp" or left[0] == "cmp" or (rhs[0] == "bin" and rhs[1] in ("==", "!=", "!==")) or (left[0] == "bin" and left[1] in ("==", "!=", "!==") and not (g == "==" and left[1] == "=="))):
                raise SyntaxError("compare-chain: 比べの連鎖で通すのは、向きの揃った3項の範囲と、`=` だけ・`==` だけの連鎖(何項でも)です(R119)。`=` と `==` の混ぜ・範囲と等しさの混ぜ・`!=` `!==` の連鎖は、括りで分けて書きます")
            if g == "," and STRICT_GATES and ("not", ("hole",)) in ([left] + (rhs[1] if rhs[0] == "prod" else [rhs])) + (left[1] if left[0] == "prod" else []):
                pass                                   # R63: `$[s , !_]` は単位律で縮む(評価の所で `$s` と同じに読む)
            elif g == "," and STRICT_GATES and ("hole",) in ([left] + (rhs[1] if rhs[0] == "prod" else [rhs])) + (left[1] if left[0] == "prod" else []):
                pass                                   # R71: `_ , !_` は _ に落ちる(`!_` の G7 は積の評価で、書いた `_` が無い形だけに当てる)
            elif g in ("|", ";") and STRICT_GATES: pass       # §7.60(2026-11-08): `|`・`;` の被演算子の恒等射(`5 | _`・`_ | 5`)は i と同じに読む。値の段が決める
            else: no_hole(left); no_hole(rhs)
            if g == ",": left = ("prod", [left] + (rhs[1] if rhs[0] == "prod" else [rhs]))
            else: left = ("bin", g, left, rhs)
        return left

    def parse_prefix(self):
        t = self.peek()
        if t is None: raise SyntaxError("式が必要です")
        if t.kind == "OP":
            g = t.text
            if t.pos != "prefix":
                if g in (":", "?"): raise SyntaxError(f"pointfree-tree-notation: 片側の欠けた {g!r} の点なし(木を書く記法)は文法に無い形なので、読む段で止めます(§2・§4 R119)。名前の付いた関数で書きます")
                raise SyntaxError(f"infix-missing-operand: 前置できない演算子 {g!r}(中置は前後に空白が必要。点なしなら `[+ 1]`。R119)")
            self.next()
            if g == "!": return ("not", self.parse_expr(230))
            if g == "!!": return ("bnot", self.parse_expr(230))
            if g == "-": return ("neg", self.parse_expr(230))
            if g == "$":
                self.addr_depth = getattr(self, "addr_depth", 0) + 1
                try: return ("addr", self.parse_expr(230))
                finally: self.addr_depth -= 1
            if g == "@": return ("input", self.parse_expr(230))
            if g == "~": return ("lift", self.parse_expr(230 if STRICT_GATES else SP))      # R79: 前置の印は単一の対象に係る(`~1 2 3` は `(~1) 2 3`)
            if g in ("|", "||"):
                inner = self.parse_expr(0)
                if not (g == "||" and inner == ("not", ("hole",))): no_hole(inner)   # ||!_|| はノルムの口の穴(R27)
                if not self.is_op(self.peek(), g): raise SyntaxError(f"閉じの {g} がありません")
                self.next(); return ("abs" if g == "|" else "norm", inner)
            raise SyntaxError(f"未対応の前置演算子 {g!r}")
        return self.parse_primary()

    def parse_primary(self):
        t = self.next()
        if t.kind == "OPEN":
            rows_ = self.bracket_rows()
            if rows_ is not None: return rows_
            sec = self.try_section()
            if sec: return sec
            if self.peek() and self.peek().kind == "CLOSE": self.next(); return ("lit", [])
            node = self.parse_top()
            if self.peek() and self.is_op(self.peek(), ":"):             # 括りの中の `:`
                if not (node[0] == "lit" and isinstance(node[1], str)):   # 左辺が鍵(文字列・文字)でない `:` は枝。枝は `?` の直後の字下げブロックの行にしか居ない(match_case.md 概要。#94)
                    raise branch_outside_error("括りの中")
                self.next()
                val = self.parse_top()
                node = ("cases", [(node, val)])
            if not (self.peek() and self.peek().kind == "CLOSE"): raise SyntaxError("閉じ括弧がありません")
            self.next()
            if STRICT_GATES and node[0] == "def": return ("struct", [(node[1], node[2])])     # R26・R133: 1行の括りの `名前 : 値` は欄1つの構造体(`pw : [a : 1]`)
            return ("block", node)
        if t.kind in ATOMS: return atom_node(t)
        pv = self.at(self.i - 2) if self.i > 1 else None
        if t.kind == "CLOSE" and pv is not None and pv.kind == "OP":
            if pv.text in (":", "?"): raise SyntaxError(f"pointfree-tree-notation: 片側の欠けた {pv.text!r} の点なし(木を書く記法)は文法に無い形なので、読む段で止めます(§2・§4 R119)。名前の付いた関数で書きます")
            raise SyntaxError(f"infix-missing-operand: 中置 {pv.text!r} の右の被演算子がありません(点なしなら `[+ 1]`。R119)")
        raise SyntaxError(f"予期しないトークン {t.text!r}")

    def bracket_rows(self):
        """--strict: 改行で行に割った括り(`[inc : 5` ⏎ `r : inc + 1]`・`[1 2` ⏎ `3 4]`)。行ごとに読み、字下げのブロックの括りと同じに組む"""
        j, depth, rows, cur = self.i, 1, [], []
        while (u := self.at(j)) is not None:
            if u.kind == "OPEN": depth += 1
            elif u.kind == "CLOSE":
                depth -= 1
                if depth == 0: break
            if depth == 1 and u.kind == "ROWSEP": rows.append(cur); cur = []
            else: cur.append(u)
            j += 1
        if u is None or not rows: return None
        rows.append(cur)
        rows = [r for r in rows if r]
        items = []
        for r in rows:
            if r[-1].kind == "OP" and r[-1].text == ",": raise trailing_comma_error(lstr(" ".join(x.text for x in r), r[-1].line, 0), False)
            if len(r) >= 2 and r[0].kind in ("ID", "STR", "CHAR") and r[1].kind == "OP" and r[1].text == ":":
                if len(r) == 2: raise SyntaxError(f"{key_name(r[0])} : の値がありません")
                items.append((key_name(r[0]), finish(r[2:])))
            else:
                if any(x.kind == "OP" and x.text == ":" for x in r): raise branch_outside_error("括り")
                items.append((None, finish(r)))
        self.i = j + 1
        return block_items_value(items, True)

    def try_section(self):                     # [+] [* 2,] [7 -] [!_] [_!]
        j, depth, inner = self.i, 1, []
        while (t := self.at(j)):
            depth += (t.kind == "OPEN") - (t.kind == "CLOSE")
            if depth == 0: break
            inner.append(t); j += 1
        if depth != 0: return None
        comma = len(inner) > 1 and self.is_op(inner[-1], ",")
        if comma: inner = inner[:-1]
        isop = lambda t: t.kind == "OP" and t.text in SECTION_OPS
        sec = None
        if STRICT_GATES and len(inner) >= 3 and inner[-1].kind == "HOLE":      # R119・R22: 点なしの区間(`+ 1`・`<< _`)の後ろに書いた `_` だけが続く1行の括りは infix-missing-operand(`(+ 1 _)`・`(<< _ _)`。§5 Q81 は閉じた)
            k_ = len(inner)
            while k_ > 0 and inner[k_ - 1].kind == "HOLE": k_ -= 1
            lead = inner[:k_]
            if ((len(lead) == 1 and isop(lead[0]) and lead[0].pos != "prefix")
                    or (len(lead) == 2 and isop(lead[0]) and lead[0].pos != "prefix" and lead[1].kind in ATOMS)):
                raise SyntaxError("infix-missing-operand: 1行の括りの中で、点なしの区間の後ろに `_` が続いています(`(+ 1 _)`・`(<< _ _)`)。区間を当てる読みと中置の読みに割れるので、読む段で止めます(§4 R119・R22)。区間なら `[+ 1]`、中置なら `x ? x + 1` と書きます")
        if len(inner) == 2 and ((inner[0].kind == "OP" and inner[1].kind == "HOLE") or (inner[0].kind == "HOLE" and inner[1].kind == "OP")):
            if comma and inner[0].kind == "OP" and inner[0].text == "$": pass       # `[$_,]` は種類の分からない普通の括り(§2 の表。断らない)
            pass                                                      # §2 の表: `[~_]` は恒等射の括り(`~_` は `[_]`、R79)、`[@_]`・`[_@]`・`[$_,]` は種類の分からない普通の括り、`[#_]` は export-mark-position(R119)
        if (STRICT_GATES and len(inner) >= 3 and isop(inner[0]) and inner[0].pos != "prefix" and inner[1].kind == "OP" and inner[1].pos == "prefix"
                and inner[1].text in ("$", "@", "~", "-", "!", "!!")):        # §2: 片側の欠けた中置の点なしの被演算子は1項(`[+ $inc]`・`[== -1]`)
            try:
                sp_ = Parser(inner[1:]); sub_ = sp_.parse_top(); ok_ = sp_.i == len(inner) - 1 and sub_[0] in ("addr", "input", "lift", "neg", "not", "bnot")
            except SyntaxError: ok_ = False
            if ok_:
                self.i = j + 1
                return ("sec", "right", inner[0].text, sub_, comma)
        if (len(inner) >= 3 and isop(inner[0]) and inner[0].pos != "prefix" and inner[1].kind == "OPEN" and inner[-1].kind == "CLOSE"):
            save = self.i; self.i += 2                       # [+ [uu x]] : 括りを被演算子にする
            try: sub = self.parse_top(); ok = self.peek() is not None and self.peek().kind == "CLOSE" and self.i == j - 1
            except SyntaxError: ok = False
            self.i = save
            if ok:
                self.i = j + 1
                return ("sec", "right", inner[0].text, ("block", sub), comma)
        if len(inner) == 1 and isop(inner[0]): sec = ("sec", "fold", inner[0].text, None, comma)
        elif len(inner) == 2 and isop(inner[0]) and inner[0].pos != "prefix" and inner[1].kind in ATOMS:
            sec = ("sec", "right", inner[0].text, atom_node(inner[1]), comma)
        elif len(inner) == 2 and inner[0].kind in ATOMS and isop(inner[1]):
            sec = ("sec", "left", inner[1].text, atom_node(inner[0]), comma)
        elif len(inner) == 2 and self.is_op(inner[0], "!") and inner[1].kind == "HOLE":
            sec = ("sec", "not", "!", None, comma)
        elif len(inner) == 2 and self.is_op(inner[0], "-") and inner[1].kind == "HOLE":
            sec = ("sec", "neg", "-", None, comma)                       # [-_] : 単項の点なし(符号反転)
        elif len(inner) == 2 and self.is_op(inner[0], "!!") and inner[1].kind == "HOLE":
            sec = ("sec", "bnot", "!!", None, comma)
        elif len(inner) == 2 and inner[0].kind == "HOLE" and self.is_op(inner[1], "!"):
            sec = ("sec", "fact", "!", None, comma)
        if sec is None and comma and len(inner) >= 1:                     # [F,] : F は名前・@f・括りなどの式。要素ごとの写像(R50)
            save, saved_t = self.i, self.t
            self.t = self.t[:j - 1] + self.t[j:]                 # 末尾の , を除いて、中身を1つの式として読む
            try: sub = self.parse_top(); ok = self.peek() is not None and self.peek().kind == "CLOSE" and self.i == j - 1
            except SyntaxError: ok = False
            self.t, self.i = saved_t, save
            if ok:
                self.i = j + 1
                return ("sec", "mapf", None, ("block", sub), True)
        if sec: self.i = j + 1
        return sec

def _with_pos(fn):                             # 節を作ったら、最初のトークンの場所を表に残す
    def w(self, *a, **k):
        t = self.peek()
        node = fn(self, *a, **k)
        if t is not None and t.line and isinstance(node, tuple) and node != ("hole",) and id(node) not in POS:
            POS[id(node)] = (PARSE_FILE, t.line, t.col); POS_KEEP.append(node)
        return node
    return w
for _name in ("parse_top", "parse_expr", "parse_primary", "parse_prefix"):
    setattr(Parser, _name, _with_pos(getattr(Parser, _name)))

# ============================== 評価 ==============================
class Places(list): pass
class RowList(list): pass                      # --strict: 行に割った括りの List(行の関数は要素のまま。本体の返す所では bare-function-return で `!_`、R125)                        # R26・R62: 番地を範囲の鍵で引いた、語の場所を並べた List(`0x10 ' [1 ~ 3]`)。`' k` は k 番目の場所の中身、`#` は語ごとに書く
WORD = 8                                       # 幅を書かない番地の語(option.ms の語幅。64 ビット)
def addr_shift(a, k):                          # R26: k 語ずらした番地(生まれた幅で進む。幅は保つ)
    w = addr_w(a)
    return mk_addr_w(int(a) + k * (w or WORD), w)
def mem_read(a, env): return ev(("input", ("lit", a)), env)
def addr_get(obj, key_node, env):
    """R26・R62(--strict): 番地の先を引く。`a ' k`(0 以上の字面の整数)は k 語先の中身、`a ' k~` は k 語ずらした番地、`a ' ~k` は場所1つの List、
    字面の範囲の鍵は語の場所を並べた List(Places)。名前の鍵と負の鍵は `!_` と分かる値。Places は場所の並びとして引く。"""
    kn = key_node
    while kn[0] == "block" and isinstance(kn[1], tuple): kn = kn[1]
    pl = isinstance(obj, Places)
    def at(k):                                 # k 番目の場所(番地)
        if pl: return obj[k] if 0 <= k < len(obj) else UNIT
        return addr_shift(obj, k)
    def lit_int(x):
        if x[0] == "lit" and type(x[1]) is int: return x[1]
        if x[0] == "neg" and x[1][0] == "lit" and type(x[1][1]) is int: return -x[1][1]
        return None
    if kn[0] == "id": return UNIT                                   # 名前の鍵: 番地は欄を持たない
    if kn[0] == "post" and kn[1] == "~":                            # k~ : ずらした番地(Places なら k から後ろの場所)
        k = lit_int(kn[2])
        if k is None:
            kv = ev(kn[2], env); k = kv if type(kv) is int else None
        if k is None or k < 0: return UNIT
        if pl: return Places(obj[k:]) if obj[k:] else UNIT
        return at(k)
    if kn[0] == "lift":                                             # ~k : 位置 k の場所1つの List
        k = lit_int(kn[1])
        if k is None or k < 0: return UNIT
        a = at(k); return UNIT if is_unit(a) else Places([a])
    kv = ev(key_node, env)
    if isinstance(kv, list) and not isinstance(kv, str) and kv and all(type(x) is int for x in kv):      # 範囲の鍵: 語の場所の List
        if any(x < 0 for x in kv): return UNIT
        ps = [at(x) for x in kv]
        return UNIT if any(is_unit(x) for x in ps) else Places(ps)
    if type(kv) is int:
        if kv < 0: return UNIT                                      # 番地の先には終わりが無いので、負の鍵は `!_`
        a = at(kv); return UNIT if is_unit(a) else mem_read(a, env)
    return UNIT

NOKEY = object()
def strict_key_get(obj, key_node, env):
    """R26(--strict): 鍵は字面で読む。裸の名前(綴り `_` も)は欄の名前で、名前の表から引かない(欄の無い物は `!_`)。`~k` は `[k]` と同じ鍵で位置 k の切り出し、
    字面の整数の `k~` と範囲は切り出しで、構造体の切り出しは欄の名前を保つ。ほかの鍵(式の鍵)は今の道(NOKEY)"""
    kn = key_node
    if kn[0] == "id" and kn[1] != "__":
        return obj.get(kn[1], UNIT) if isinstance(obj, Struct) else UNIT
    if kn in (("hole",), ("not", ("hole",))): return UNIT              # 綴り `_` の名前の鍵: 欄 `_` はどこにも無い(R138)
    if is_unit(obj): return UNIT
    def lit_int(x):
        if x[0] == "lit" and type(x[1]) is int: return x[1]
        if x[0] == "neg" and x[1][0] == "lit" and type(x[1][1]) is int: return -x[1][1]
        return None
    def positions(ps):                                              # 位置の並びで切り出す(構造体は欄の名前を保つ。空の切り出しは `!_`)
        if isinstance(obj, Struct):
            its = list(obj.items()); n_ = len(its)
            got = [its[p if p >= 0 else n_ + p] for p in ps if -n_ <= p < n_]
            return Struct(got) if got and len(got) == len(ps) else UNIT
        c = as_container(obj) if not isinstance(obj, (list, str)) else obj
        n_ = len(c)
        if not all(-n_ <= p < n_ for p in ps) or not ps: return UNIT
        part = [c[p] for p in ps]
        return "".join(part) if isinstance(c, str) else part
    m = kn
    while m[0] == "block" and isinstance(m[1], tuple) and m[1][0] in ("lift", "lit", "neg"): m = m[1]
    if m[0] == "lift":
        k = lit_int(m[1])
        if k is not None: return positions([k])
    if kn[0] == "post" and kn[1] == "~":
        k = lit_int(kn[2])
        if k is not None:
            if isinstance(obj, Struct):
                its = list(obj.items()); k = k if k >= 0 else len(its) + k
                return Struct(its[k:]) if 0 <= k < len(its) else UNIT
            if k < 0: return UNIT
            return NOKEY
    return NOKEY

def ctor_of(node, env):
    """type_system.md §6.2: 右辺を静的に遡れるときのコンストラクタ名。`C a b`(C は本体が構造体の括りの関数で、引数の数が合う)か、由来の分かる名前(`q : p`)。それ以外は None(= `!_`)"""
    def def_of(name):
        e = env
        while e is not None:
            if name in e.__dict__.get("defnodes", {}): return e, e.__dict__["defnodes"][name]
            e = e.parent
        return None, None
    if node[0] == "id":
        e = env
        while e is not None:
            if node[1] in e.__dict__.get("origins", {}): return e.__dict__["origins"][node[1]]
            if node[1] in getattr(e, "vars", {}): return None
            e = e.parent
        return None
    if node[0] == "seq" and node[1] and node[1][0][0] == "id":
        _, d = def_of(node[1][0][1])
        if d and d[0] == "lam" and d[2][0] == "struct" and len(d[1]) == len(node[1]) - 1: return node[1][0][1]
    return None

def do_get(obj, key_node, env):                # 鍵の字面で読みが決まる(~ の個数)
    EFFECTS[0] += 1
    if STRICT_GATES and (is_addr(obj) or isinstance(obj, Places)): return addr_get(obj, key_node, env)
    if STRICT_GATES and key_node[0] != "input":
        r_ = strict_key_get(obj, key_node, env)
        if r_ is not NOKEY: return r_
    kv, mode = None, "index"
    at_key = key_node[0] == "input"
    if key_node[0] == "input":                 # 前置 @ : 単値の鍵。名前付きスロットには使えない
        if isinstance(obj, Struct):
            raise SignError("名前付きスロットへ前置 @ では引けません(鍵の中身で引くなら ' k~)")
        key_node = key_node[1]
    elif key_node[0] == "id" and isinstance(obj, Struct):
        return obj.get(key_node[1], UNIT)      # 印の無い識別子: 左辺が構造体なら名前
    if key_node[0] == "post" and key_node[1] == "~":
        inner = key_node[2]
        if inner[0] == "lit" or (inner[0] == "neg" and inner[1][0] == "lit"): mode, kv = "rest", ev(inner, env)
        elif inner[0] == "post" and inner[1] == "~": mode, kv = "rest", ev(inner[2], env)
        else: kv = ev(inner, env)              # 識別子 i~ は中身で1つ引く
    else: kv = ev(key_node, env)
    if at_key and isinstance(kv, list): raise SignError("前置 @ は単値の鍵にだけ書けます(並びで引くなら ' vs と書きます)")      # type_system.md「前置 @ は同じ射。単値のときだけ書ける」
    if is_unit(obj) or is_unit(kv): return UNIT
    if mode == "rest":
        if isinstance(obj, Struct): return get_value(obj, kv)   # k~~ は k~ と同じ値
        if not isinstance(kv, int) or isinstance(obj, Closure): return UNIT
        r = as_container(obj)[kv:]
        return r if r else UNIT
    return get_value(obj, kv)

def field_block(expr, env):
    """R80: 枝の値の字下げのブロックの中の `名前 : 関数` の行は、局所の定義でなく欄かもしれず、同じブロックの行から指せない(local-field)"""
    if STRICT_GATES and expr[0] == "cases":
        fr = [c[1] for c, v in expr[1] if c is not None and c[0] == "id" and v[0] == "lam"]
        if fr:
            e2 = Env(env); decline(e2, fr, "local-field")
            return ("cases", [(c, v) for c, v in expr[1] if not (c is not None and c[0] == "id" and v[0] == "lam")]), e2
    return expr, env
def check_body_rows(rows, body=False):
    """R130: 枝の行が1つでもある本体(と枝の値のブロック)で、最後の行でない裸の行(条件の無い行)があれば、ファイルごと止める(match_case.md §5)。
    枝の無い本体は手続き(R76。最後でない行は評価する所、最後の行が返す値)。枝の無い枝の値のブロックは要素の列。body は呼ぶ所の印(今は同じ扱い)"""
    if any(c is not None for c, _ in rows):
        for k, (c, _) in enumerate(rows[:-1]):
            if c is None:
                e = SyntaxError("body-bare-row-between: 枝の行のある本体で、最後の行でない裸の行(条件の無い行)があります。枝のある本体の条件の無い行は、最後の1行(既定の行)だけです(match_case.md §5、§4 R130)。"
                                "直し方: 裸の行を最後へ移すか、条件を付けます。順に行うことは枝の無い関数(手続き、R76)に分けます")
                p = getattr(rows, "pos", ())
                if k < len(p) and p[k] and p[k][0]: e.loc = (PARSE_FILE, p[k][0], p[k][1] + 1)
                raise e
    return rows
def cond_value(cond, env):
    """R128: 枝の条件は `&` の左と同じに読む。条件に残った関数(`⇥inc : 1` の inc)は評価する所の関数で `_`、知らせも `&` の左と同じ(V4)"""
    c = ev(cond, env)
    if STRICT_GATES: c = id_operand(leftover_operand(ru_unit(c)), "枝の条件")
    return c
BARE_BRANCH_MSG = "枝の値に裸の関数が残り、この枝は消えて次へ進みます(R125・R128)。関数を返すなら `$` を付けて持ち上げます(`$[+ m]`)、入れ子の `?` なら仮引数を並べます(`x y ? x + y`)"
def branch_bare(v):
    """R128: 最後でない枝の値に残った裸の関数は `_`(R125)で、その枝は消えて次へ進む。知らせは「この枝は消えて次へ進みます」"""
    if STRICT_GATES and v is ID:                                   # R125・R29: 枝の値に残った恒等射も返す所の裸の関数で `!_`(この枝は消えて次へ)
        info("bare-function-return", BARE_BRANCH_MSG); return True
    if STRICT_GATES and isinstance(v, Closure) and not v.dead and v is not ID:
        info("bare-function-return", BARE_BRANCH_MSG); return True
    return False
def cases(rows, env):
    for i_, (cond, expr) in enumerate(rows):
        if STRICT_GATES:
            _p = POS.get(id(cond)) if cond is not None else None
            _p = _p or POS.get(id(expr))
            if _p: CURLINE[0] = _p[1]                            # R127: 知らせはその行を持つ
            eval_place(expr)
        if cond is None:
            expr, e2 = field_block(expr, env); return ev(expr, e2)
        if not is_unit(cond_value(cond, env)):
            expr, e2 = field_block(expr, env)
            v = ev(expr, e2)
            if STRICT_GATES and (is_unit(v) or (i_ < len(rows) - 1 and branch_bare(v))): continue                              # R128: 値が `_` の枝は消えて次の枝へ進む(書いた `_`・名前の `_`・計算の `_`)
            return v
    return UNIT

# ---- 書いた _ と穴 !_ (coproduct_spec.md §3.5、R15・R16・R138) ----
MARK = ("hole",)                               # 書いた _ : 印(単位)
HOLE = ("not", ("hole",))                      # !_ : 穴(口に置いた恒等射)


def written_empty(n, v, env):
    """R85: 書いた `[]`(`e0 : []` の e0・`[[]]`・`~[]`・括った物)。空の文字列は含まない"""
    if not empty_value(v) or isinstance(v, (str, Stream)): return False
    k = n[0]
    if k == "lit": return isinstance(n[1], list)
    if k == "block": return written_empty(n[1], v, env) if not isinstance(n[1], list) else False
    if k == "seq" and len(n[1]) == 1: return written_empty(n[1][0], v, env)
    if k == "lift" and n[1] != ("hole",): return True
    if k == "id":
        o = env.owner(n[1])
        return o is not None and o.parent is None
    return False
def r90_stream_gate(items, env):
    for k, m in enumerate(items):                               # 数えられない流れ(`[~xs]` が `_` と分かる値を受けた xs)の後ろに項が続けば G2(a)
        if m[0] == "post" and m[1] == "~" and m[2][0] == "id":
            o = env.owner(m[2][1])
            if o is not None and m[2][1] in getattr(o, "uncount", ()) and any(x != MARK and x != HOLE for x in items[k + 1:]):
                pass                                                   # R120: G2(a) は廃止。後ろの項を当てるか積むかは値の段が決める
class ZList(list): pass                      # R90 残り: 書いた `_` と分かる値(`un`・`[_]`・`~_`)が `[~xs]` の口に直に来た物(中身の見えない A)
def zero_node(n, env):
    if n == ("hole",): return False
    if n[0] == "lift": return n[1] == ("hole",)
    if n[0] == "block" and not isinstance(n[1], list) and n[1][0] == "lift": return zero_node(n[1], env)
    return only_hole(n, env)
def r90_uncount(items, vals, env):
    f = vals[0]
    if isinstance(f, Closure) and f.native is None and not f.variadic and f.params is not None:
        for k in range(1, len(items)):
            idx = len(f.args) + k - 1
            if idx >= len(f.params): break
            sp = f.params[idx]
            if sp[0] == "destr" and not sp[1] and sp[2] and not (len(sp) > 4 and sp[4]) and zero_node(items[k], env): vals[k] = ZList()
def r94_empty(n, env):
    """R138: 書いた `[]` と、中身が連結の単位で詰まって `[]` になる書いた括り(`[[]]`・`~[]`・`[_]`・`~_`・`[_ _]`・`[~_]`・`([])`・長さ 0 の流れ入りの `[_~]`・`[e0~]`)。名前には当てない"""
    k = n[0]
    if k == "lit": return isinstance(n[1], list) and not n[1] and len(n) == 2
    if k == "hole": return True
    if k == "block": return (not isinstance(n[1], list)) and r94_empty(n[1], env)
    if k == "seq": return bool(n[1]) and all(r94_empty(x, env) for x in n[1])
    if k == "lift": return r94_empty(n[1], env)
    if k == "post" and n[1] == "~":
        x = n[2]
        if x[0] == "id":
            if declined_reason(env, x[1]): return False
            try: v = ev(x, env)
            except SignError: return False
            return empty_value(v) or (is_unit(v) and not isinstance(v, (int, str)))
        return r94_empty(x, env)
    return False

def unit_law(items, vals, env):
    """R138(R138・R95・R106 を含む): 値の口に置いた書いた `_`(と、`_` と同じ書いた `[]`・長さ 0 の流れ)は、適用の単位として消え、口を使わない。
    括りの口の `_` も R15 で消える。残るのは既定値のある口の `_`(R83 の既定値)だけ。消す物を除いた (items, vals) を返す。消す物が無ければ None。
    既定値のある関数は前から左に数える(消えた `_` は口を使わない)。関数の項は口を数えない(合成は先頭の関数の口で受ける)。"""
    f = vals[0]
    if not (isinstance(f, Closure) and not f.variadic and not getattr(f, "foldsec", False)): return None
    if f.params is not None: specs = f.params[len(f.args):]
    elif f.native is not None: specs = [("name", "_", None)] * max(0, f.arity - len(f.args))
    else: return None
    defaulted = has_defaults(f)
    # R16(カリー化): 既定値の無い素の関数で、k = n(口が全部名前)・他の実引数が全部値・最後の項が `_` でなければ、`_` は消さず仮引数にする(`sub _ 2` は `a ? sub a 2`)
    if (not defaulted and f.params is not None and len(items) - 1 == len(specs) and specs
            and all(sp[0] == "name" and sp[2] is None for sp in specs)
            and items[-1] != MARK and any(it == MARK for it in items[1:])
            and not any(isinstance(vals[i], (Closure, Stream)) for i in range(1, len(items)) if items[i] != MARK and items[i] != HOLE)):
        return None
    if STRICT_GATES and f.params is not None and len(specs) == 1 and specs[0][0] == "destr" and not specs[0][2] and not defaulted:
        gsz_ = len(specs[0][1]) + len(specs[0][4] if len(specs[0]) > 4 else [])           # R46・R69: 前から n 個(括りの名前の数)の中の `_` は括りの口の穴(`fp 1 _` は G5)。n 個の外の `_` は閉じた後ろの恒等射
        for k_ in range(1, min(len(items), gsz_ + 1)):
            if items[k_] in (MARK, HOLE) and not any(isinstance(vals[q], (Closure, Stream)) for q in range(1, len(items)) if q < len(vals) and vals[q] is not None):
                raise Gate("G5: 括りの関数の口(名前 %d 個)に書いた `_` は、括りの口の穴で読みが決まりません(`fp 1 _`。R46・R69)" % gsz_)
    drops, conv, slot, seen_fn = [], {}, 0, False
    for i in range(1, len(items)):
        it, v = items[i], vals[i]
        if isinstance(v, Stream): break
        if isinstance(v, Closure): seen_fn = True; continue
        if it == HOLE: slot += 1; continue
        is_m = it == MARK
        is_e = (not is_m) and v is not None and r94_empty(it, env) and (empty_value(v) or is_unit(v))
        if not (is_m or is_e): slot += 1; continue
        spec = specs[slot] if slot < len(specs) else None
        if spec is None:
            if is_m and not defaulted: drops.append(i)          # 口が尽きた後の `_` は値の隣で消える(R138・R43)。既定値のある関数は今の門(G15)
            continue
        if defaulted and seen_fn: continue                         # 位置が数えられない(G15 は今の門)
        if spec[0] == "name":
            if spec[2] is None: drops.append(i)
            else:
                if is_e: conv[i] = True                            # 既定値の口の書いた `[]` は、書いた `_` と同じ(既定値)
                slot += 1
        elif slot_optional(spec): slot += 1                        # 既定値のある括り `[x : 1]` の口: 書いた `_` は既定値(R83)。`[]` は器のまま
        else:                                                      # 括りの口
            if is_m: drops.append(i)                               # R15: 消えて詰まる
            else: slot += 1                                        # 書いた `[]` は括りの口では器のまま
    if not drops and not conv: return None
    keep = [i for i in range(len(items)) if i not in drops]
    ni = [MARK if i in conv else items[i] for i in keep]
    nv = [None if i in conv else vals[i] for i in keep]
    return ni, nv
def empty_value(v):
    """長さ 0 の器(`[]`・`[[]]`・空の文字列でない)"""
    if isinstance(v, list) and not isinstance(v, (Struct, Vec)):
        return all(isinstance(e, list) and not isinstance(e, (Struct, Vec)) and empty_value(e) for e in v)
    return False
def r84_whole(items, env):
    """R84(Q75 (b)): 可変長の口・恒等射・括りの関数の最後の括りが、まだ何も受けていない所で長さ 0 の流れ1つだけを受け、
    後ろに書いた `_` か関数しか続かなければ、元の流れを丸ごと受ける(`[* 2,] []~` は `[* 2,] []`、`i []~` は `i []`)。"""
    if len(items) < 2 or not (items[1][0] == "post" and items[1][1] == "~"): return None
    if not all(m == MARK or m[0] in ("id", "block") for m in items[2:]): return None
    if empty_streams_to_marks(items[:2], env)[1] != MARK: return None
    try:
        f = ev(items[0], env)
        if not all(m == MARK or isinstance(ev(m, env), Closure) for m in items[2:]): return None
    except SignError: return None
    if not (isinstance(f, Closure) and f.native is None and not f.variadic and f.params is not None and len(f.params) == len(f.args) + 1 and f.params[-1][0] == "destr"): return None     # R95: 点なしの可変長の口・恒等射は書いた `_` と同じ(元の流れで受けるのは括りの関数の最後の括りだけ)
    return [items[0], ("lit", [])] + list(items[2:])
def empty_streams_to_marks(items, env):
    out = list(items)
    for i, m in enumerate(items):
        if not (m[0] == "post" and m[1] == "~"): continue
        x = m[2]
        while x[0] in ("block", "seq") and isinstance(x[1], list) and len(x[1]) == 1 and isinstance(x[1][0], tuple): x = x[1][0]
        if x == MARK: out[i] = MARK; continue
        if x[0] not in ("block", "id", "lit", "prod"): continue
        if x[0] == "id" and declined_reason(env, x[1]): continue
        try: v = ev(m[2], env)
        except SignError: continue
        if empty_value(v) or (is_unit(v) and x[0] in ("block", "id") and not isinstance(v, (int, str))): out[i] = MARK
    return out
def ev_head(m, env):                              # R107: 並びの頭は、既定値の部分適用のまま受ける
    if not STRICT_GATES or m[0] not in ("block", "id"): return ev(m, env)
    _k = KEEP[0]; KEEP[0] = m
    try: return ev(m, env)
    finally: KEEP[0] = _k
def is_id_head(m, env):
    """恒等射と分かる頭(`i : _` の i・`@[$_]`・`@q`(`q : $_`))。評価せずに見る"""
    if m[0] == "id":
        try: return env.get(m[1]) is ID
        except Exception: return False
    if m[0] == "input":
        x = m[1]
        while x[0] == "block" and isinstance(x[1], tuple): x = x[1]
        if x == ("addr", ("not", ("hole",))): return True
        if x[0] == "id":
            try: v = env.get(x[1])
            except Exception: return False
            return isinstance(v, Ref) and v.value is ID
    return False
def ev_seq(items, env, pre=None):
    if STRICT_GATES and items and items[0] == ("norm", ("not", ("hole",))) and len(items) >= 2 and any(m[0] == "post" and m[1] == "~" for m in items[1:]) and not any(m in (("hole",), ("not", ("hole",))) for m in items[1:]):
        got_ = []                                                    # R27: `||_|| w~` は空の器で本体を読んで 0(何も受けていない関数にしない)。撒く項と並ぶ項(`||_|| w~ 3`)も、`||_|| w 3` と同じ数え方(法則53)
        for m_ in items[1:]:
            v_ = ev(m_, env)
            if not (m_[0] == "post" and m_[1] == "~"):
                if not is_unit(v_): got_.append(v_)
            elif isinstance(v_, (list, Stream)): got_.extend(v_)
            elif not is_unit(v_): got_.append(v_)
        return len(got_)
    if STRICT_GATES and len(items) >= 2 and items[1] == ("not", ("hole",)) and is_id_head(items[0], env):
        strict_gate("G7: 恒等射の口に `_` を書いた形は断ります(`i _`・`@[$_] _`。口は並び全体を受けるので、穴の規則が読みません。§4 R46・§6.4)", items[0])
    if STRICT_GATES and len(items) >= 2 and items[0][0] == "lift" and any(x in (("hole",), ("not", ("hole",))) for x in items[1:]) \
            and (items[0][1] in (("hole",), ("not", ("hole",))) or (items[0][1][0] == "id" and env.get(items[0][1][1]) is ID)):
        strict_gate("G7: 恒等射を持ち上げた `~_`・`~i` を頭に、`_` を実引数に並べる形は断ります(`~_ _`。§4 R79・R138、§6.4)", items[0])      # §6.4: 仕様も `~_ _` は G7
    if not STRICT_GATES:
        if len(items) == 2 and items[0][0] == "post" and items[0][1] == "~" and items[0][2][0] == "id" and items[1][0] == "post" and items[1][1] == "~" and items[1][2][0] == "struct":
            tgt = ev(items[0][2], env)                          # list_model.md §5.3: 左が名前なら既にある器なので上書き(`p~ [ foo : 99 ]~` は p 自身が変わる。後の行が勝つ)
            if type(tgt) is Struct:
                new = ev(items[1][2], env)
                if isinstance(new, Struct): tgt.update(new); return Struct(tgt)
        return _ev_seq(items, env, pre)
    _nf = NOFILL[0]; NOFILL[0] = id(items) not in EVAL_ITEMS          # R107: 評価する所の外の並びは既定値を埋めない
    _ku = KNOWN_UNIT[0]
    try: KNOWN_UNIT[0] = any(m not in (MARK, HOLE) and m[0] != "lit" and unit_like(m, env, set()) for m in items[1:])      # R49・R122: `!_` と分かる実引数は本体を読まない(計算の `!_` だけが本体を読む)
    except Exception: KNOWN_UNIT[0] = False
    try:
        r = _ev_seq(items, env, pre)
        if type(r) is list and any(type(x) is Closure and x.pd for x in r):         # R124: 器の要素に残った既定値の口だけが開いた部分適用は、並びを畳んだ後に既定値で埋める
            r = [fill_pd(x) if (type(x) is Closure and x.pd) else x for x in r]
        return r
    finally: NOFILL[0] = _nf; KNOWN_UNIT[0] = _ku
def _known_at(m, env):                                           # R78: `$` の印で指す先が分かる `@x` は位置に依らない
    if m[0] != "input": return False
    try: return isinstance(ev(m[1], env), (Ref, VarRef, LaneRef))
    except SignError: return False
def _ev_seq(items, env, pre=None):
    has_in = False
    for m in items:
        if m[0] == "input": has_in = True; break
    if has_in:
        bad = next((m for m in items[1:] if m[0] == "input" and not _known_at(m, env)), None)
        if bad is not None:
            pass                                                       # R126: G6 は廃止。先の分からない `@x` は種類の未知な項(R120)として値の段が畳む
    if STRICT_GATES and pre is None and any(m[0] == "post" and m[1] == "~" for m in items):
        r90_stream_gate(items, env)
        _w = r84_whole(items, env)
        items = _w if _w is not None else empty_streams_to_marks(items, env)               # R83・R84: 長さ 0 の流れ(`[]~`・`e0~`・`_~`)は書いた `_` と同じ印
    marks = []; holes = []
    for i, m in enumerate(items):
        if m == MARK: marks.append(i)
        elif m == HOLE: holes.append(i)
    if pre is None and PAR[0] is not None and not marks and not holes and not has_in: pre = PAR[0].seq_vals(items, env)       # --par: 実引数の呼び出しどうしを同時に
    vals = pre if pre is not None else [None if (i in marks or i in holes) else ev_head(m, env) for i, m in enumerate(items)]
    if not STRICT_GATES and not marks and not holes and not has_in:       # 速い道(既定): 印も穴も前置 @ もない並びは、残りの検査がすべて素通り
        if len(items) == 2 and isinstance(vals[0], (IterList, OpenRange)) and isinstance(vals[1], (Ref, VarRef)) and is_fn_target(vals[1]):
            return iterate_loop(vals[0], vals[1])
        return fold_couple(vals)
    if len(items) == 2 and isinstance(vals[0], (IterList, OpenRange)) and isinstance(vals[1], (Ref, VarRef)) and is_fn_target(vals[1]):
        return iterate_loop(vals[0], vals[1])                              # stack_abi §3.1: Iterator に Reader(関数の番地)を並置するとループ(返値の並び)
    if STRICT_GATES and len(items) >= 2 and isinstance(vals[0], Closure) and vals[0].pd:      # R107・R110: 既定値の口だけが開いた部分適用の後ろ
        if all(m == MARK for m in items[1:]): return fill_pd(vals[0])     # R110・R120: 種類の未知な項の後ろが `_` だけなら既定値で埋める。値が続けば値の段が左から畳む(`(gq 1) 5` は 6)
    if STRICT_GATES and len(items) >= 2 and not holes:
        r90_uncount(items, vals, env)
    if STRICT_GATES and len(items) >= 2 and items[-1] == MARK and all(m == MARK for m in items[1:]) and isinstance(vals[0], Closure) and not vals[0].pd \
            and vals[0].args and has_defaults(vals[0]) and vals[0].params is not None and items[0][0] in ("block", "id") and id(items) not in EVAL_ITEMS:
        strict_gate("G7: 既定値のある関数の部分適用の後ろの `_` は、消える印(R138)か既定値のある口の既定値(R83)か決まりません(`(gq 1) _`)。評価する所(行の根・比べの被演算子)の外では読みが割れます(R110、§5 Q80 (a))")
    if STRICT_GATES and len(items) >= 3 and isinstance(vals[0], Closure) and vals[0].hof and _hof_inner_mark(items, vals[0].hof):
        strict_gate("G5: 既定値のある関数から作った穴の関数の穴を全部埋めた後ろに書いた `_` は、着く口が数えられません(R138。穴の口の `_` は値の口で消えます)")
    if STRICT_GATES and len(items) >= 2:
        _u = unit_law(items, vals, env)                                  # R138: 値の口の書いた `_`・`[]` は単位律で消える(穴は `!_` だけ)
        if _u is not None:
            return ev_seq(_u[0], env, _u[1]) if len(_u[0]) >= 2 else _u[1][0]
    if STRICT_GATES and len(items) >= 2 and not holes:                  # R74: 恒等射で始まる合成は単位律で恒等射が消える(`i inc` は inc)
        k0 = 0
        while k0 < len(items) - 1 and vals[k0] is ID: k0 += 1
        if k0 and isinstance(vals[k0], Closure) and vals[k0] is not ID and not getattr(vals[k0], "foldsec", False):
            return ev_seq(items[k0:], env, vals[k0:]) if len(items) - k0 >= 2 else vals[k0]
    if STRICT_GATES and len(items) >= 3 and not holes and not marks and any(vals[q] is ID for q in range(1, len(items))):
        keep = [q for q in range(len(items)) if not (q > 0 and vals[q] is ID)]       # R126: 恒等射を途中に置いた並びは、恒等射を消した並びで畳み直す(単位律。G18 は廃止)
        return ev_seq([items[q] for q in keep], env, [vals[q] for q in keep]) if len(keep) >= 2 else vals[0]
    if len(items) >= 3 and marks and not holes and isinstance(vals[0], Closure) and not getattr(vals[0], 'foldsec', False):
        # R138: 後ろが並びの終わりまで関数(と書いた `_`)だけの `_` も、引数の並びの終わりで消える(`add _ inc` は `add inc`)
        keep = []
        for i in range(len(items)):
            if items[i] == MARK and i > 0 and all(items[j] == MARK or isinstance(vals[j], Closure) for j in range(i + 1, len(items))): continue
            keep.append(i)
        if len(keep) < len(items) and len(keep) >= 2:
            return ev_seq([items[i] for i in keep], env, [vals[i] for i in keep])
    if len(items) >= 2 and items[-1] == MARK and vals[0] is not None:
        # R138(2026-10-26): 末尾の書いた `_` は消える印。口を埋めず、頭が何でも関数のまま残る(`(add 3 _) 5` は 8)。
        # 既定値のある関数は右から見て、既定値のある口に当たる `_` まで残す(R83・R68)。可変長の点なし(R31)は今のまま。
        f = vals[0]; cut = len(items)
        if isinstance(f, Closure) and f.args and has_defaults(f) and f.params is not None and items[0][0] in ("block", "id") and id(items) not in EVAL_ITEMS:
            strict_gate("G7: 既定値のある関数の部分適用の後ろの `_` は、消える印(R138)か既定値のある口の既定値(R83)か決まりません(`(gq 1) _`)。評価する所(行の根・比べの被演算子)の外では読みが割れます(R110、§5 Q80 (a))")
        if isinstance(f, Closure) and f.variadic and getattr(f, 'foldsec', False): cut = 0
        elif isinstance(f, Closure) and has_defaults(f) and f.params is not None:
            while cut > 1 and items[cut - 1] == MARK:
                idx = len(f.args) + cut - 2
                spec = f.params[idx] if idx < len(f.params) else None
                if spec is not None and slot_optional(spec): break
                cut -= 1
        else:
            while cut > 1 and items[cut - 1] == MARK: cut -= 1
        if cut and cut < len(items):
            return ev_seq(items[:cut], env, vals[:cut]) if cut >= 2 else vals[0]
    if items[0][0] == "input" and any(isinstance(v, Closure) for v in vals[1:]) and not _known_at(items[0], env):
        pass                                                           # R126: G6 は廃止
    if STRICT_GATES and holes and not marks:                       # R69・R72: 閉じた後ろの恒等射(口の外の `!_`・値の上の `!_`)は消える
        r = closed_identity(items, vals, holes)
        if r is not None: return r
    if STRICT_GATES and not marks and not holes and len(items) >= 2 and type(vals[0]) is Closure:
        vals = [hid_tag(vals[0], items, env)] + list(vals[1:])
    if not marks and not holes: return fold_couple(vals)
    head = vals[0]
    if isinstance(head, Closure) and (head.params is not None or head.variadic):
        return apply_marks(head, items, vals, marks, holes)
    if holes:
        for v in vals:                          # 括りの関数に向けた !_ (`5 io1 !_`)は G5
            if isinstance(v, Closure) and not v.variadic and v.params is not None and v.params[len(v.args):] \
               and all(sp[0] == "destr" for sp in v.params[len(v.args):]):
                raise Gate("G5: 括りの関数の実引数の !_ は断ります(`s !_ 2 3`・`5 io1 !_`)")
        f_ = vals[-2] if len(vals) >= 2 else None
        if (STRICT_GATES and list(holes) == [len(items) - 1] and isinstance(f_, Closure) and f_.args and f_.params is not None
                and has_defaults(f_) and all(slot_optional(sp) for sp in f_.params[len(f_.args):])):
            return ev_seq(items[:-1], env, vals[:-1]) if len(items) >= 3 else f_      # R120・R46: 既定値の口だけが開いた部分適用(`(gq 1)`)の後ろの `_` は、口が1つの段の恒等射として合成(`[5 (gq 1) _]` は `[5 (gq 1)]`、R124 で既定値で埋まる)
        raise Gate("G7: !_ は関数の実引数の位置にだけ置けます(穴の位置の外)")
    kept = [v for i, v in enumerate(vals) if i not in marks]        # R15・R43: 値と空の所で _ は消える(`_ inc 5` は inc 5、`5 _ inc` は inc 5。`(_ f) 3` は f 3)
    return fold_couple(kept) if kept else UNIT

def closed_identity(items, vals, holes):
    """`inc 5 !_`・`pq 1 2 !_`・`5 inc 7 !_`(口の数ちょうどの後ろの1つの `!_`)と、値だけの並びの中の `!_`(`5 !_`・`$[5 !_]`)は、
    何も受けずに閉じた恒等射なので消える(R44・R69・R72)。`!_ !_`・外に値もある形・既定値のある頭・可変長は対象外。"""
    if any(b - a == 1 for a, b in zip(holes, holes[1:])): return None           # `!_ !_` は G7(R46)
    lead = 0
    while lead in holes: lead += 1                                             # R74: 先頭の恒等射は、次が恒等射でない関数なら単位律で消える
    if lead and holes == list(range(lead)) and lead < len(vals) and isinstance(vals[lead], Closure) and vals[lead] is not ID:
        return fold_couple(vals[lead:])
    fs = [i for i, v in enumerate(vals) if isinstance(v, Closure)]
    if not fs:
        if 0 in holes: return None
        return fold_couple([v for i, v in enumerate(vals) if i not in holes])
    j = fs[0]; f = vals[j]
    if any(i in holes for i in range(j + 1)) or f.variadic or has_defaults(f): return None
    if f.params is None and f.native is None: return None
    remain = arity(f) - len(f.args)
    if remain >= 1 and holes and min(holes) > j + remain and f.params is not None and not any(isinstance(v, Stream) for v in vals if v is not None) \
            and not any(i in holes for i in range(j + 1, j + remain + 1)) and holes != [len(items) - 1]:
        # R89: 閉じた頭の後ろの口の外の `!_` は恒等射(`inc 5 !_ 6` は `(inc 5) 6`)
        return fold_couple([ID if i in holes else v for i, v in enumerate(vals)])
    if holes != [len(items) - 1] or len(items) - 1 - j - 1 != remain or remain < 1: return None
    return fold_couple(vals[:-1])
def apply_marks(f, items, vals, marks, holes):
    k = len(items) - 1                                           # 頭の実引数の数(_ と !_ も数える)
    if f.variadic:
        if STRICT_GATES and getattr(f, "foldsec", False) and not holes and not any(isinstance(v, (Closure, Stream)) for v in vals[1:]):
            # R31: 畳む2項の点なしの実引数の `_` は中置の被演算子と同じ(`[+] 1 _ 3` は 4。比べは積の単位で消える: 寄せ4)。関数・流れが混ざる形(合成の頭)は下の G5 のまま
            return fold_args(f.foldop, [UNIT if i in marks else v for i, v in enumerate(vals[1:], 1)])
        if STRICT_GATES and getattr(f, "foldsec", False) and not holes:
            # R31(合成の頭): `[+] inc 1 _` は `inc ([+] 1 _)`(畳む点なしの後ろに続く関数は合成。合成は左から実行する、R11)。関数が頭の後ろに続き、その後ろが値(と `_`)だけのとき
            c = 1
            while c < len(vals) and isinstance(vals[c], Closure) and not getattr(vals[c], "foldsec", False) and c not in marks: c += 1
            rest = list(range(c, len(vals)))
            if c > 1 and any(q not in marks for q in rest) and not any(isinstance(vals[q], (Closure, Stream)) for q in rest):
                r = fold_args(f.foldop, [UNIT if q in marks else vals[q] for q in rest])
                for g in vals[1:c]: r = fold_couple([g, r])
                return r
        raise Gate("G7: アリティの数えられない点なしの実引数に _ は書けません(読みが決まらない位置。R46)" if STRICT_GATES else "G5: アリティの数えられない点なしの実引数に _ は書けません(読みが決まらない位置)")
    remain = arity(f) - len(f.args)
    defaulted = has_defaults(f)
    only_groups = all(sp[0] == "destr" for sp in f.params[len(f.args):]) and not defaulted
    r68 = []                                                     # R68: 既定値の無い口に当たった内側の _ はカリー化の穴
    if defaulted and marks:                                      # R83: 既定値のある口に書いた _ は既定値。ほかは G15
        for m in marks:
            idx = len(f.args) + m - 1
            spec = f.params[idx] if idx < len(f.params) else None
            if m == len(items) - 1 and not holes:                    # 末尾の _ は「ここで終わる」(R138)
                if STRICT_GATES and spec is not None and spec[0] == "name" and spec[2] is None:   # (括りの口は対象外)
                    pass                                                  # R126: G15 は廃止。`gd _` の `_` は終わり(R138)と読む
                continue
            if not (spec is not None and slot_optional(spec)):
                if STRICT_GATES and not f.alias and spec is not None and spec[0] == "name" and not any(isinstance(v, (Closure, Stream)) for v in vals[1:] if v is not None):
                    r68.append(m); continue
                r68.append(m); continue                                   # R126: G15 は廃止。既定値のある口に当たらない `_` は値の口で消える(R138)
        if r68: pass
        elif not holes and (items[-1] != MARK or (len(f.args) + len(items) - 2 < len(f.params) and slot_optional(f.params[len(f.args) + len(items) - 2]))):
            return fold_couple([f] + [UNIT if i in marks else vals[i] for i in range(1, len(items))])      # 末尾の _ が既定値のある口なら、その口は既定値(R83)
    if marks and not holes and items[-1] != MARK and all(m > remain for m in marks):     # 口が埋まった後の _ は値の隣で消える(`inc 5 _ inc`)
        return fold_couple([f] + [vals[i] for i in range(1, len(items)) if i not in marks])
    others = [i for i in range(1, len(items)) if i not in marks and i not in holes]
    if STRICT_GATES and (marks or holes) and any(isinstance(vals[i], Stream) for i in others) and not has_defaults(f):
        raise Gate("G13: 撒く項のある並びの穴は読みません(R16・R34。`go _ vs~`)。穴を実引数で埋めるか、撒く項を外します")
    if any(isinstance(vals[i], (Closure, Stream)) for i in others):
        raise Gate("G7: 関数や撒く項が混ざった並びの _ / !_ は読みが決まりません" if holes else "G5: 書いた _ の読みが決まらない位置")
    def curry(pos, tail=False, limit=None):
        def fn(*xs):
            vs = list(vals)[:limit]
            for p, x in zip(pos, xs): vs[p] = x
            return fold_couple(vs)
        if not tail: return native_fixed(fn, len(pos))
        def fnv(args):                                           # 足りない口は、後ろから来る実引数を全部受ける(R34: a [~c] ? f a 2 c~)
            if len(args) < len(pos): return UNIT
            vs = list(vals)
            for p, x in zip(pos, args): vs[p] = x
            return fold_couple(vs + list(args[len(pos):]))
        return native_var(fnv)
    def holed(pos):                                              # 穴(と、既定値の無い関数の内側の _)を仮引数にした関数 (R34・R38)
        k = len(items) - 1
        out_holes = [p for p in holes if p > remain]
        if any(b - a == 1 for a, b in zip(out_holes, out_holes[1:])): raise Gate("G7: 外の `!_` が2つ並んでいます(`inc 5 !_ !_`。閉じた後ろの恒等射は1つだけ、R69・R46)")
        if out_holes: raise Gate("G13: 前から n 個の外に穴があります(`inc 5 !_`)")
        inside = [p for p in pos if p <= remain]                 # 前から n 個の外の書いた _ は、値の隣で消える(`inc 5 _ inc`)
        if not inside: return fold_couple([f] + [vals[i] for i in range(1, len(items)) if i not in marks])
        if k < remain: return curry(inside, tail=True)
        g = curry(inside, limit=1 + remain)
        if STRICT_GATES and defaulted and isinstance(g, Closure): g = _cp(g, hof=len(inside))
        rest = [vals[i] for i in range(1 + remain, len(items)) if i not in marks]
        return fold_couple([g] + rest) if rest else g           # 余った実引数は、前から穴に入る(`go !_ xs` は go xs)
    if r68:                                                      # R68: カリー化(`gd _ 3` は `gd !_ 3`)。既定値の口の _ は既定値のまま
        for i in marks:
            if i not in r68: vals[i] = UNIT
        return holed(sorted(holes + r68))
    if holes:                                                    # 穴 !_(既定値があっても穴)
        if only_groups: raise Gate("G5: 括りの関数の実引数の !_ は断ります(`s !_ 2 3`・`5 io1 !_`)")
        if items[-1] == MARK: raise Gate("G7: !_ のある並びの末尾に _ は置けません")
        return holed(sorted(holes + marks))
    if only_groups:                                              # 括りの関数: _ は受ける並びの中の印で、消える
        given = [vals[i] for i in range(1, len(items)) if i not in marks]
        if items[-1] == MARK and len(given) < remain: raise Gate("G5: 末尾の _ の「終わり」と括りの消える印とで読みが割れます")
        return fold_couple([f] + given)
    if items[-1] == MARK:                                        # 末尾の _ は「ここで終わる」(R138)
        if any(i in marks for i in range(1, len(items) - 1)): raise Gate("G5: 末尾の _ とほかの _ が混ざった並びは断ります")
        given = [vals[i] for i in range(1, len(items) - 1)]
        if len(given) < remain: return UNIT                      # 足りなければ _
        return fold_couple([f] + given)                          # 飽和なら評価する
    return holed(marks)                                          # 既定値の無い関数の内側の _ は、穴と同じ(R38)

def fast_int(n, env):
    """副作用なしに整数と決まる式(整数リテラル・整数の名前・その + - *)の値。決まらなければ None(呼び側は普通の道で評価し直す)。
    strict では `0x…` の顔(番地)を持つ物は除く(番地の対表の道へ回す)。"""
    k = n[0]
    if k == "lit":
        v = n[1]
        return v if (type(v) is int and len(n) == 2) else None
    if k == "id":
        if DECL_USED[0]: return None
        e = env
        name = n[1]
        while e:
            vs = e.vars
            if name in vs:
                v = vs[name]
                if type(v) is not int: return None
                return v
            e = e.parent
        return None
    if k == "bin":
        op = n[1]
        if (op == "+" or op == "-" or op == "*") and not OVERRIDES:
            l = fast_int(n[2], env)
            if l is None: return None
            r = fast_int(n[3], env)
            if r is None: return None
            _v = l + r if op == "+" else l - r if op == "-" else l * r
            if STRICT_GATES and (_v > INT_MAX or _v < -INT_MAX): return None        # V5: 溢れは _ なので、普通の道(arith)へ回す
            return _v
    return None

def erased_shadow(n, env):                    # R113: 括りの中で消した欄の名前が、外の関数の本体の局所の定義を指すようになる所だけ知らせる(仮引数・ファイルの定義は前から数えない)
    for nm in n.erased:
        o = env.owner(nm)
        if o is not None and nm in getattr(o, "localdefs", ()):
            warn("erased-unit-shadow", f"欄 `{nm} : _` は書かなかったことと同じなので、括りの中の `{nm}` は外の局所の `{nm}` が見えます(R113)")

def ev(n, env):
    k = n[0]
    if k == "id":                                # 速い道: 名前の引き当て(宣言された名前の読みが要る時だけ遅い道)
        if not DECL_USED[0]:
            v = env.get(n[1])
            if STRICT_GATES:
                if v is UNIT: undef_note(env, n[1])
                elif type(v) is Closure and v.pd and KEEP[0] is not n: v = fill_pd(v)       # R107
            return v
    elif k == "lit":
        v = n[1]
        if type(v) is not list and len(n) == 2: return v
    elif k == "bin" and FAST[0]:                 # 速い道: 整数どうしの + - *
        v = fast_int(n, env)
        if v is not None: return v
    elif k == "cmp" and FAST[0] and len(n[2]) == 1 and not OVERRIDES:      # 速い道: 整数どうしの比べ(compare と同じ。成り立てば witness、外れれば __)
        a = fast_int(n[1][0], env)
        if a is not None:
            b = fast_int(n[1][1], env)
            if b is not None:
                op = n[2][0]
                ok = a < b if op == "<" else a <= b if op == "<=" else a > b if op == ">" else a >= b if op == ">=" else a == b if (op == "=" or op == "==") else a != b
                return a if ok else UNIT
    if not STRICT_GATES:                          # 既定: 厳密な検査は全部素通りなので、評価して返すだけ
        try: return _ev(n, env)
        except SignError as e:
            if getattr(e, "empty_stream", False) and not hasattr(e, "node"): e.node = n
            raise locate(e, n)
    try:
        v = _ev(n, env)
        if STRICT_GATES and type(v) is Closure and v.pd and KEEP[0] is not n: v = fill_pd(v)       # R107: 頭・値の定義の右辺の外では、既定値で埋める
        if STRICT_GATES and type(v) is list and n[0] in ("block", "seq", "prod", "lit") and v and _NOFN2.isdisjoint(map(type, v)):
            v = WLen(v)                                                 # R91: 書いた形の List の長さは書いた時点で分かる
        return v
    except SignError as e:
        if getattr(e, "empty_stream", False) and not hasattr(e, "node"): e.node = n
        raise locate(e, n)

def _ev(n, env):
    global OVERRIDES
    k = n[0]
    if k == "lit":
        if STRICT_GATES and type(n) is ErasedNode: erased_shadow(n, env)
        if len(n) == 3 and type(n[1]) is int:
            if n[2] == "UInt": return UInt(n[1])
            if n[2] == "Address": return mk_addr(n[1])     # 2^64 以上・0x8000000000000000 の字面は __(存在しない番地)
        if STRICT_GATES and type(n[1]) is WInt and n[1] % n[1].w:      # R62: 倍数の外に書いた幅つきの字面
            width_warn(n[1], n[1].w, "字面のまま", "幅を書かない `0x…` か `01x…` で書きます")
        return n[1]
    if k == "id":
        if DECL_USED[0]:
            r = declined_reason(env, n[1])
            if r:
                if STRICT_GATES: strict_gate(f"G7: `{n[1]}` は{DECL_TEXT[r]}ため、裸では使えません(未知の名前)", n)
                return UNIT                                  # 既定でも、輪の中の局所の名前は未知(__)
        v = env.get(n[1])
        if STRICT_GATES and v is UNIT: undef_note(env, n[1])
        return v
    if k == "bin":
        op = n[1]
        if STRICT_GATES and op in ("|", ";") and len(n) == 4 and not OVERRIDES: return ev_unit_op(n, env)       # R137・V7: 辺は関数のまま読み、`_` の辺は消える
        if STRICT_GATES and (op in CMP_ADDR or op in ("&", "|") or op == "#"): eval_place(n[3]); (eval_place(n[2]) if op != "#" else None)      # R76・R107: 比べと論理の被演算子は評価する所
        if STRICT_GATES and op == "#" and len(n) == 4 and cross_kind_write(n, env): return UNIT      # R62: 種類を跨ぐ書き込みは何も書かず `!_`
        if op == "'":
            if STRICT_GATES and n[3] in (("hole",), ("not", ("hole",))) and (c_ := ctor_of(n[2], env)):      # §6.2: `p ' _` は遡れるとき `$Constructor`、遡れなければ(下の通常の道で)`!_`
                return ev_addr_strict(("addr", ("id", c_)), env)
            _l = fn_operand(id_operand(ev(n[2], env), "`'` の左(引く器の側)"), "`'` の左(引く器の側)")
            if STRICT_GATES and isinstance(_l, (Ref, VarRef)) and n[3][0] == "lit" and type(n[3][1]) is int and len(n[3]) == 2:     # R102: `$x ' 0` は x を下ろしたもの(`@[$x]`)、`' k≠0` は領域の外で `_`
                return _l if n[3][1] in (0, -1) else UNIT      # R102・R26: 関数の番地の `' 0`(と長さ1の `' -1`)は同じ番地。ほかの位置は領域の外で `!_`
            return do_get(_l, n[3], env)
        if op == "@": return do_get(fn_operand(id_operand(ev(n[3], env), "`@` の右(引く器の側)"), "`@` の右(引く器の側)"), n[2], env)
        if STRICT_GATES and (op in ARITH_ADDR or op in CMP_ADDR): return strict_addr_bin(n, op, env)
        if (op == "+" or op == "-" or op == "*") and not OVERRIDES:       # 整数どうしの + - * は直に計算する
            _pr = PAR[0].pair(n, env) if PAR[0] is not None else None        # --par: 両辺が純粋な関数の呼び出しなら、左を別のプロセスで(sign_par.py。値は同じ)
            if _pr is not None: l, r = _pr
            else: l = ev(n[2], env); r = ev(n[3], env)
            if type(l) is int and type(r) is int and not INTCHK[0]:
                _r = l + r if op == "+" else l - r if op == "-" else l * r
                if STRICT_GATES and (_r > INT_MAX or _r < -INT_MAX): return arith(op, l, r)        # V5: 溢れは _(information)
                return _r
            if type(l) is UInt and (type(r) is int or type(r) is UInt):      # UInt の速い道: 2^64 で回すのはビットマスク 1 つ
                return UInt((l + r if op == "+" else l - r if op == "-" else l * r) & UMASK)
            return binop(op, l, lambda: r)
        if OVERRIDES:                                              # 上書きがあれば、そのスコープでは上書きが勝つ
            o = env.owner("[" + op + "]")
            if o is not None and isinstance(o.vars["[" + op + "]"], Closure):
                return run_with(o.vars["[" + op + "]"], [ev(n[2], env), ev(n[3], env)])
        if PAR[0] is not None and op in ("/", "%", "&&", "||", ";;", "<<", ">>"):       # --par: 割る・ビット・シフトでも、両辺が純粋な呼び出しなら左を別のプロセスで
            _pr = PAR[0].pair(n, env)
            if _pr is not None: return binop(op, _pr[0], lambda: _pr[1])
        return binop(op, ev(n[2], env), lambda: ev(n[3], env))
    if k == "block":
        inner = n[1]
        if STRICT_GATES and inner[0] == "def" and inner[2] == ("hole",):       # R113: 1行の `[s : _]` は `[]` と同じ(欄 s は席を取らない)
            erased_shadow(erased_node(("lit", []), [inner[1]]), env)
            return []
        if (inner[0] == "seq" and len(inner[1]) == 4 and (LAYER is None or LAYER >= 3)
                and all(_float_lit(m) is not None for m in inner[1])):
            return Vec(_float_lit(m) for m in inner[1])     # 4 つの Float リテラル(負号つきも。type_system.md §2: Float の字面は `-0.5` も含む) → Vector
        if STRICT_GATES and inner[0] == "seq" and len(inner[1]) >= 2 and inner[1][-1] == MARK and all(m == MARK for m in inner[1][1:]) \
                and (inner[1][0] == HOLE or (inner[1][0][0] in ("neg", "bnot", "not") and inner[1][0][1] == ("hole",))) \
                and not (inner[1][0][0] == "not" and len(inner[1]) == 2 and SECB[0] != id(n)):                  # R138: `(!_ _)` は書いた項どおり恒等射の括り
            strict_gate("G7: 1行の括りの中の点なしの形の項の後ろに書いた `_` だけが続く並びは、末尾の `_` を消すと点なし、書いた項で見ると中の並びで、読みが割れます(`(!_ _)`・`(-_ _)`。§5 Q74)", n)
        if STRICT_GATES and SECB[0] != id(n) and inner[0] == "seq" and len(inner[1]) == 2 and inner[1][0] == HOLE and empty_streams_to_marks(inner[1], env)[1] == MARK:
            return ID                                                           # R138: `(!_ _)`・`[!_ []~]` は書いた項どおり恒等射の括り
        _kp = KEEP[0] is n
        if _kp: KEEP[0] = n[1]
        try:
            try: v = ev(n[1], env)
            finally:
                if _kp: KEEP[0] = n
        except Gate as e:
            nd = getattr(e, "node", None)
            if STRICT_GATES and getattr(e, "empty_stream", False) and nd is n[1] and value_stacked(nd, env) and [m for m in nd[1] if m != MARK][-1][:2] == ("post", "~"):
                warn("leftover-lambda", LEFTOVER_MSG); return UNIT
            raise
        if isinstance(v, Closure) and n[1][0] == "id" and not v.alias: v = _cp(v, alias=True)   # [inc] は逆適用の右にできない
        return v
    if k == "hole": return UNIT                          # 書いた _ は印(単位)
    if k == "seq": return ev_seq(n[1], env)
    if k == "def":
        _lo = LEFTOVERS[0]
        if STRICT_GATES: KEEP[0] = n[2]
        v = ev_place(n[2], env, rhs=True)
        if STRICT_GATES and LEFTOVERS[0] != _lo and isinstance(v, Closure) and not v.lo: v = _cp(v, lo=True)
        if isinstance(v, Closure) and n[2][0] == "id" and not v.alias: v = _cp(v, alias=True)   # al : inc は別名
        if STRICT_GATES:
            env.__dict__.setdefault("defnodes", {})[n[1]] = n[2]
            og_ = env.__dict__.setdefault("origins", {})                      # type_system.md §6.2 `' _`: 束縛の右辺を静的に遡れるときだけ、コンストラクタの名前を覚える
            (og_.__setitem__(n[1], ctor_of(n[2], env)) if ctor_of(n[2], env) else og_.pop(n[1], None))
            zs = env.__dict__.setdefault("zeronames", set())
            (zs.add if only_hole(n[2], env) else zs.discard)(n[1])
            vn_ = env.__dict__.setdefault("voidnames", set())                  # R49・R139: 無い欄を引いた `w : pw ' zz` は `!_` と分かる名前(`$w` は零射の番地でなく、値に当てた `$`)
            (vn_.add if (n[2][0] == "bin" and n[2][1] == "'" and unit_like(n[2], env, set())) else vn_.discard)(n[1])
            if n[1] in PROVISIONAL:                                # R103: A と仮置きして読んだのに関数になった(仮置きで不動点の無い輪)
                PROVISIONAL.discard(n[1])
                if isinstance(v, Closure) and not v.dead and v is not ID:
                    e_ = Gate(f"name-cycle: 定義 {n[1]} が `${n[1]}` を通って自分を引き、値と仮置きすると関数になる輪です(不動点が無い。§4 R103)")
                    raise locate(e_, n)
            if holds_addr(v):                                      # R62: 番地を名前・欄にしまう行(複数行の括りの要素は §5 Q66 (10) の未決で、今は知らせ無し)
                ln_ = node_line(n) or node_line(n[2])
                its = n[2][1] if n[2][0] in ("prod", "list", "rows") and isinstance(n[2][1], list) else []
                if not any(node_line(x) not in (None, ln_) for x in its if isinstance(x, tuple)): store_warn(ln_, "`:`")
        env.set(n[1], v); return v
    if k == "opdef":
        OVERRIDES = True
        v = ev(n[2], env); env.set(n[1], v); return v
    if k == "export":
        v = ev(n[1], env)
        root = env
        while root.parent: root = root.parent
        root.exports[n[1][1]] = v
        return v
    if k == "struct":
        if STRICT_GATES and type(n) is ErasedNode: erased_shadow(n, env)
        if STRICT_GATES:                                           # P2・R133: 欄は同じ範囲から順序に依らず引け、外の名前を隠す
            seen_ = set()
            for key, vn in n[1]:
                if key in seen_:
                    e_ = Gate(f"name-duplicate: 欄 {key} が同じ括りで2回書かれています(2つ目を断ります。P2。§4 R133)")
                    if node_line(vn): e_.loc = (PARSE_FILE, node_line(vn), 1)
                    raise e_
                seen_.add(key)
            fe_ = FieldEnv(env, n[1])
            for key, vn in n[1]:
                if env.owner(key) is not None or key in BUILTINS:
                    old_ = CURLINE[0]; CURLINE[0] = node_line(vn) or old_
                    try: info("name-shadow", f"欄 `{key}` は外の同じ名前を隠します。この括りの中の `{key}` は欄です(内側が勝つ。§4 R133)。")
                    finally: CURLINE[0] = old_
            st_ = Struct((key, fe_.get(key)) for key, vn in n[1])
        else:
            st_ = Struct((key, ev(vn, env)) for key, vn in n[1])
        if STRICT_GATES:
            for key, vn in n[1]:
                if holds_addr(st_.get(key)): store_warn(node_line(vn), "`:`")     # R62: 欄の行(`ob :` ⏎ `⇥run : $inc` は run の行)
        if len(n) > 2:                                            # 撒く行: 書かれなかった欄だけを足す
            for sn_ in n[2]:
                sv_ = ev(sn_, env)
                if isinstance(sv_, Struct):
                    for kk_, vv_ in sv_.items(): st_.setdefault(kk_, vv_)
        return st_
    if k == "fieldblock":                                         # P2・R133(R80 は使わない番号): 欄でない行も、同じ括りの欄を順序に依らず引ける(`[sq : z ? z * z` ⏎ `$sq]`)
        fe_ = FieldEnv(env, n[1])
        st_ = Struct((key, fe_.get(key)) for key, _ in n[1])
        for m_ in n[2]: ev(m_, fe_)                                # 欄でない行の値は、構造体に席を持たない(実装の判断。仕様は通ると言うだけ)
        return st_
    if k == "lam":
        if STRICT_GATES: lam_leftover(n, env); unit_defaults_gate(n, env); branch_unit_gate(n, env); lam_static(n, env)
        return Closure(params=n[1], body=n[2], env=env, acc=ACC.get(id(n)))
    if k == "cases": return cases(n[1], env)
    if k == "rows":                                                # --strict: 行に割った括りの List(R133・list_model)
        out_ = []
        for m_ in n[1]:
            v_ = ev(m_, env)
            if isinstance(v_, Stream): out_.extend(v_)
            elif v_ is ID or is_unit(v_): continue                    # 行の `!_` と恒等射は要素にならない(R83・R61)
            else: out_.append(v_)
        return RowList(out_) if out_ else UNIT
    if k == "proc": return ev_proc(n[1], env)
    if k == "prod":
        if STRICT_GATES and id(n) in EVAL_PRODS:                       # R107: 評価する所の `,` が恒等射か書いた `_` で消えて適用の並び1つだけが残れば、その並びも評価する所の並びとして解く
            _rest = [m for m in n[1] if m != ("not", ("hole",)) and m != ("hole",)]
            if len(_rest) == 1 and len(_rest) < len(n[1]) and _rest[0][0] == "seq" and _rest[0][1] and _rest[0][1][0][0] in ("id", "block") and not (_rest[0][1][0][0] == "id" and not isinstance(env.get(_rest[0][1][0][1]), Closure)):
                eval_place(_rest[0]); return ev(_rest[0], env)
        out = []; dropped = False
        holes = STRICT_GATES and any(m == ("hole",) for m in n[1])       # R61: , の被演算子の書いた _ は積の単位(消える)
        pre_ids = holes and any(m == ("not", ("hole",)) for m in n[1])   # R71: `_ , !_` は _ に落ちる(恒等射が消えて _ が残る)
        for i, m in enumerate(n[1]):
            if holes and m == ("hole",): continue
            if pre_ids and m == ("not", ("hole",)): continue
            if STRICT_GATES and m[0] == "seq" and len(m[1]) >= 2 and i + 1 < len(n[1]):
                r = r93_apply(m, n, i, env)
                if r is not None:
                    if not out: return r
                    out.append(r); break
            if STRICT_GATES and m[0] == "seq" and len(m[1]) >= 2 and m[1][-1] == MARK and i + 1 < len(n[1]) \
                    and any(isinstance(ev(x, env), Closure) for x in m[1][:-1] if x not in (MARK, HOLE)):
                strict_gate("G3: `,` のすぐ左が書いた `_` の形は、積の頭の `_`(R61)と並びの中で消える `_`(R15)で読みが割れます(`fp _ , 1 , 2`。R66)", n)
            if STRICT_GATES and m[0] == "seq" and len(m[1]) >= 2 and m[1][-1] == HOLE and i + 1 < len(n[1]) \
                    and not any(x in (MARK, HOLE) for x in m[1][:-1]) and not out:
                _vs = [ev(x, env) for x in m[1][:-1]]                        # R66: `pb 1 _ , 2` は `pb 1 (_ , 2)`。最後の口に書いた `_` は `(x , R)` の中で積の単位として消える
                _j = next((t for t, v in enumerate(_vs) if isinstance(v, (Closure, Stream))), None)
                if _j is not None and r66_ok(_vs + [0]) and not any(q[0] == "seq" and len(q[1]) >= 2 for q in n[1][i + 1:]):
                    _rest = [ev(q, env) for q in n[1][i + 1:] if q != ("hole",)]
                    return finalize(run_with(_vs[_j], _vs[_j + 1:] + [product(_rest)]))
            if m[0] == "seq" and len(m[1]) >= 2 and not any(x in (MARK, HOLE) for x in m[1]):
                vs = [ev(x, env) for x in m[1]]
                if STRICT_GATES and r66_ok(vs) and i + 1 < len(n[1]):          # R66: 最後の口が参照の口なら `f x , …` は `f (x , …)`
                    if any(q[0] == "seq" and len(q[1]) >= 2 for q in n[1][i + 1:]):
                        strict_gate("G3: `,` の右の要素に2項以上の並びがあります。参照の口では構造を保つ読み(`[1 [2 3]]`)と平らな読み(`[1 2 3]`)が割れるので、括ります(`fab 1 , (2 3)`。R66)", n)
                    rest = [ev(q, env) for q in n[1][i + 1:] if q != ("hole",)]
                    j = next(t for t, v in enumerate(vs) if isinstance(v, (Closure, Stream)))
                    res = finalize(run_with(vs[j], vs[j + 1:-1] + [product([vs[-1]] + rest)]))
                    if j:
                        acc = vs[0]
                        for v in vs[1:j] + [res]: acc = join(acc, v)
                        res = acc
                    if not out: return res
                    out.append(res)
                    break
                if STRICT_GATES and any(isinstance(v, Closure) for v in vs):
                    _nf_ = NOFILL[0]; NOFILL[0] = True                         # R124: `,` の辺は、2つ以上残るまで既定値を埋めない
                    try: _fc = fold_couple(vs)
                    finally: NOFILL[0] = _nf_
                    _e = comma_edge(_fc, keep=True)                            # R121: 辺の並びも左から畳む。口が足りた呼び出しは `,` と空白で同じ
                    if _e is DROPPED: dropped = True
                    else: out.append(_e)
                elif any(isinstance(v, Closure) for v in vs) and not (holes and sum(1 for q in n[1] if q != ("hole",) and not (pre_ids and q == ("not", ("hole",)))) == 1):
                    strict_gate("G3: 関数を含む括らない並びを , の直の被演算子にできません(括ります)")
                    out.append(fold_couple(vs))
                else: out.append(fold_couple(vs))
            elif STRICT_GATES:                                                     # R61・R124: 丸ごと残った関数は `_`(既定値の口だけが開いていれば埋める)
                _e = comma_edge(ev(m, env), keep=True)
                if _e is DROPPED: dropped = True
                else: out.append(_e)
            else: out.append(ev(m, env))
        if STRICT_GATES: out = [FnEdge(ID) if v is ID else v for v in out]      # 恒等射の辺は関数の因子(2026-11-17 仕様 R61)
        if STRICT_GATES and any(isinstance(v, FnEdge) for v in out):       # R137・V4 の 1〜3: `_` の辺は消え、1つだけ残れば `,` ごと消えてその辺のまま(括りの中・定義の右辺なら関数)。2つ以上なら関数の辺は `_`
            _others = [v for v in out if not is_unit(v) and v is not ID]
            if len(_others) == 1 and id(n) not in EVAL_PRODS: return _others[0].v
            if len(_others) != 1 or id(n) in EVAL_PRODS: out = [fill_pd(v.v) if isinstance(v, PdEdge) else v for v in out]      # R124: 2つ以上残る(評価する所)なら既定値で埋めた値
            _nout = []
            for v in out:
                if isinstance(v, FnEdge): drop_fn_edge("(`,` の被演算子。関数を積の要素にするなら `$inc , 2`、当てるなら `(inc 1) , 2`。R61)", v); dropped = True
                else: _nout.append(v)
            out = _nout
        if STRICT_GATES and len(out) > 1:                                      # V4 の 4: `_` で `,` が消えて辺が1つだけ残れば、その辺のまま(`1 2 , (3 < 2)` は `1 2`)
            _non = [v for v in out if not is_unit(v)]
            if len(_non) == 1 and not isinstance(_non[0], Stream) and not any(isinstance(v, Stream) for v in out) and not any(v is ID for v in out): return _non[0]
        if holes or dropped or (STRICT_GATES and any(v is ID for v in out)):
            _had_id = any(v is ID for v in out)
            out = [v for v in out if v is not ID]                          # R71: 名前の恒等射(`i : !_`)も _ に吸われる。R61: 恒等射は `,` の単位(`i , 5` は 5)
            if not out: return UNIT       # R61(2026-11-13): 単位だけの鎖は空の積で `,` の単位の `!_`(`_ , _ ; 7` は 7)。前は R45 の「両方とも恒等射なら恒等射」。 R45: 両方とも恒等射なら恒等射(1 × 1 ≅ 1)。`_` が混ざれば R71 のとおり `_`
            if len(out) == 1 and not isinstance(out[0], Stream): return out[0]
        return product(out)
    if k == "cmp":
        if STRICT_GATES: eval_place(n[1][0]); eval_place(n[1][1])
        vals, ops = [ev(n[1][0], env)], n[2]
        if STRICT_GATES and len(ops) > 1: vals[0] = leftover_operand(ru_unit(vals[0]))     # 法則48: 連鎖の項に残った関数も `==` と同じ知らせ
        if STRICT_GATES and len(ops) == 1 and addr_face(vals[0]) != "other":
            if is_unit(vals[0]): return UNIT
            return addr_op(ops[0], vals[0], ev(n[1][1], env), n[1][0], n[1][1], n, env)
        if STRICT_GATES and len(ops) == 1 and not is_unit(vals[0]):         # R62: 右が関数を指す番地か、その演算の答え(ABS)なら番地の比べ
            r0 = ev(n[1][1], env)
            if r0 is ABS or addr_face(r0) == "fn": return addr_op(ops[0], vals[0], r0, n[1][0], n[1][1], n, env)
            return binop(ops[0], vals[0], lambda: r0)
        if len(ops) == 1: return binop(ops[0], vals[0], lambda: ev(n[1][1], env))
        for i, op in enumerate(ops):           # 零射に落ちた時点で以降は評価しない
            if is_unit(vals[i]): return UNIT
            nxt = ev(n[1][i + 1], env)
            if STRICT_GATES: nxt = leftover_operand(ru_unit(nxt))
            if is_unit(nxt) or is_unit(compare(op, vals[i], nxt)): return UNIT
            vals.append(nxt)
        return vals[len(vals) // 2] if len(vals) > 2 else compare(ops[0], vals[0], vals[1])
    if k == "not": return logical_not(ev(n[1], env))
    if k == "neg":
        v = ev(n[1], env)
        if STRICT_GATES and (v is ABS or is_fn_target(v)):            # R62: 値の印・絶対値も関数を指す番地に射を持たない(level-mismatch、答えは運ばれる `!_`)
            if v is not ABS: warn("level-mismatch", LEVEL_MSG.format(op="-"))
            return ABS
        if STRICT_GATES and is_addr(v): return addr_noarrow("-", "番地の前置 `-`(番地は負を持たない)")      # R62
        if isinstance(v, Closure):
            if not STRICT_GATES: strict_gate("G7: 関数に前置 - は使えません(`-inc 5`)")
            elif not v.dead:
                if v is not ID: warn("leftover-lambda", LEFTOVER_MSG + "(前置 - の核。R87)")
                v = UNIT
        return -v if is_num(v) else UNIT
    if k == "bnot":
        v = ev(n[1], env)
        if STRICT_GATES and (v is ABS or is_fn_target(v)):            # R62: 値の印・絶対値も関数を指す番地に射を持たない(level-mismatch、答えは運ばれる `!_`)
            if v is not ABS: warn("level-mismatch", LEVEL_MSG.format(op="!!"))
            return ABS
        if STRICT_GATES and is_addr(v):                                  # R62: 番地の `!!` は番地(符号なしの語のビット)
            w_, r_ = addr_w(v), ~int(v) & UMASK
            if w_ and int(v) % w_ == 0 and r_ % w_: width_warn(v, w_, "`!!` で", "幅を書かない `0x…` か `01x…` で書きます")
            return mk_addr_w(r_, w_)
        if not isinstance(v, int): return UNIT
        if isinstance(v, UInt): return UInt(~v & UMASK)
        r = ~v
        if INTCHK[0] and type(r) is int and (r > INT_MAX or r < -INT_MAX): raise SignError(f"Int の溢れ(罠): !!{v} の答え {r} は Int の値域 -{INT_MAX} 〜 {INT_MAX} の外です(integer_overflow.md §1.2)")
        return r
    if k == "abs":
        if STRICT_GATES and n[1] == ("not", ("hole",)):          # R27: `|_|` は `||_||` と同じ口の穴(並び全体を受けて絶対値)
            def abs_hole(args):
                xs = [a for a in args if not is_unit(a)]
                if len(xs) != 1: return UNIT
                x = xs[0]
                if is_addr(x): return x
                return abs(x) if is_num(x) else UNIT
            return native_var(abs_hole)
        v = ev(n[1], env)
        if STRICT_GATES and (v is ABS or is_fn_target(v)):            # R62: 値の印・絶対値も関数を指す番地に射を持たない(level-mismatch、答えは運ばれる `!_`)
            if v is not ABS: warn("level-mismatch", LEVEL_MSG.format(op="|.|"))
            return ABS
        if STRICT_GATES and is_addr(v): return v                         # R62: 番地は負を持たないので、絶対値は恒等(`|0x10|` は `0x10`)
        if isinstance(v, Closure):
            if STRICT_GATES and not v.dead:                  # R27: `|f|` は関数に演算子を直接当てた解なし。囲みごと `!_`(leftover-lambda。R87・R61 と同じ線)
                warn("leftover-lambda", LEFTOVER_MSG + "(`|f|` の中が関数。R27)"); return UNIT
            strict_gate("G7: 関数に |.| は使えません(`|inc| 5`)")
        return abs(v) if is_num(v) else UNIT
    if k == "norm":
        def count(x):                                    # 器・文字列は長さ、単位は 0、ほかの1つの値は 1(1要素の器 ≅ 要素)
            return len(x) if isinstance(x, (list, str, Vec, Struct)) else (0 if is_unit(x) else 1)      # 名前付きスロットの数(type_system.md §3.2 の `|point|`)
        if n[1] == ("not", ("hole",)):                   # ||!_|| : 受けた並び全体を数える関数(R27)
            if STRICT_GATES: return native_var(norm_hole)     # R27: 並び全体を1つの器として数える(`!_` と分かる値・長さ 0 の流れは空の器で 0)
            return native_var(lambda args: len(args))
        if n[1][0] == "addr" and n[1][1] in (("hole",), ("not", ("hole",))): return 1   # ||$_||・||$!_|| はどちらも1つの値
        v = ev(n[1], env)
        if STRICT_GATES and v is ID and n[1] != ("not", ("hole",)):       # R27(coproduct_spec 表): `||i||`・`||(_)||` は恒等射(関数)を囲んだ物で、囲みごと `!_`(leftover-lambda)。括らない `_` だけが口の穴
            warn("leftover-lambda", LEFTOVER_MSG + "(`||i||` の中が恒等射。R27)"); return UNIT
        if isinstance(v, Closure) and not v.dead:
            if STRICT_GATES:                             # R27: `||f||` も関数に演算子を直接当てた解なし。囲みごと `!_`(leftover-lambda)
                warn("leftover-lambda", LEFTOVER_MSG + "(`||f||` の中が関数。R27)"); return UNIT
            return compose(v, native_fixed(count, 1))   # 既定のモード: ||f|| は f の後にノルムを当てる合成
        return count(v)
    if k == "lift":
        if n[1][0] == "seq" and len(n[1][1]) >= 2:                       # G4: 前置 ~ の項が2項以上の並び
            strict_gate("G4: 前置 ~ の項が2項以上の並びです(`~1 2 3`)。括るか、1項にします")
        v = ev(n[1], env)
        if STRICT_GATES: return v                                         # R79: `~x` は書いた `[x]` と同じ項([x] ≅ x)
        return v if isinstance(v, list) else [v]
    if k == "post":
        if STRICT_GATES and n[1] == "~" and n[2][0] == "addr" and r104_empty(n[2][1], env):
            return Ref(native_fixed(lambda x: UNIT, 1))                     # R104: 長さ 0 と分かる流れの `$` は `$_`(零射の番地。知らせない)
        if STRICT_GATES and n[1] in ("~", "!") and n[2][0] == "addr":         # R57: 後置の印の付いた `$` の項は、どちらの結び方でも1つの関数でない
            strict_gate("G20: 後置の印(`~` `!`)の付いた `$` の項は、1つの関数と言い切れません(`$inc~`・`$vs~`・`$inc!`)", n)
        v = ev(n[2], env)
        if STRICT_GATES and n[1] == "~" and (v is ID or n[2] in (("hole",), ("not", ("hole",)))):
            strict_gate("G7: 恒等射に後置の `~` は付けられません(中身に関数の見える器を撒く形。`inc _~`・`i~`。R138・§5 Q20)", n)
        if n[1] == "!":
            if STRICT_GATES and v is ABS: return ABS
            if STRICT_GATES and is_addr(v): return addr_noarrow("!", "番地の後置 `!`")     # R62
            return factorial(v)
        if n[1] == "~": return expand(v)
        return import_file(v)
    if k == "importspread":
        return SpreadStruct(import_file(ev(n[1], env), True))
    if k == "addr":
        if n[1][0] == "id" and n[1][1] == "__": return UNIT           # $__ = __
        if STRICT_GATES: return ev_addr_strict(n, env)               # R99〜R102: $ は1つの関数だけを運ぶ
        if n[1][0] == "id":                                          # $x : 変数のスロットのアドレス
            owner = env.owner(n[1][1])
            return VarRef(owner or env, n[1][1]) if owner or n[1][1] else UNIT
        v = ev(n[1], env)
        if is_unit(v): return UNIT                                    # $__ = __
        if isinstance(v, Closure): return Ref(v)
        return Ref(v)                                                 # $5・$[1 2] : 値を読む参照(R60。字面は値そのものを指す)
    if k == "input":
        EFFECTS[0] += 1
        _pv = set(PROVISIONAL)
        v = ev(n[1], env)
        if STRICT_GATES and is_unit(v) and (PROVISIONAL - _pv or (PROVISIONAL and n[1][0] == "addr")):
            _nm = next(iter(PROVISIONAL - _pv or PROVISIONAL))              # R103: 値と仮置きした `$v` を `@` で下ろす輪は、持ち上げだけを通らない(`f9 : x ? @[$v]`)
            raise locate(Gate(f"name-cycle: 定義 {_nm} が `${_nm}` を `@` で下ろして自分を引く輪です(持ち上げだけを通る輪ではない。§4 R103)"), n)
        if is_unit(v): return UNIT                                    # @__ = __
        if isinstance(v, Lift): return UNIT                           # R99: 先の種類の分からない持ち上げは開いても先を読まない
        if isinstance(v, Ref): return dop_mark(v.value)
        if isinstance(v, LaneRef): return v.var.env.vars[v.var.name][v.lane]
        if isinstance(v, VarRef): return dop_mark(v.env.vars.get(v.name, UNIT))
        if isinstance(v, Char): return UNIT                           # @0u00 : 文字はアドレスにならない
        if isinstance(v, float):                                      # @1.5 : 四捨五入して参照外し(type_system.md の Float → Address の強制。0 から遠い側へ丸める)
            if v != v or v in (float("inf"), float("-inf")): return UNIT
            v = int(math.floor(abs(v) + 0.5)) * (-1 if v < 0 else 1)
        if isinstance(v, int) and not isinstance(v, bool):            # @0x00 : 番地から読む。未準備(未書き込み)は __
            if BOUNDS[0] and (m_ := bounds_error(v, "読み込み")) is not None: raise SignError(m_)
            vw = v.w if type(v) is WInt else 0                        # 幅つきの番地は、読んだ値をその幅(byte)へ切る(`ldrb` `ldrh` `ldr w`)
            if STRICT_GATES and vw and v % vw: return UNIT              # R62: 生まれた幅の倍数でない番地の `@` は `!_`(何も読まない)
            v = int(v)
            if v == UART: return uart_read()                          # 標準入力から 1 バイト(終わりは __)
            if (d := device_at(v)) is not None:
                x = d.read(v - d.base); x = UNIT if x is None else x
            else: x = MEMORY.get(v, UNIT)
            if vw and isinstance(x, int) and not isinstance(x, bool): x = x & ((1 << (8 * vw)) - 1)
            return x
        if isinstance(v, Closure): return UNIT                        # 印の無い関数名は番地ではない(`$` の印が届かない入力の項)。未定義の名前・印の無い実引数の `@g` と同じに `_`
        return UNIT                                                   # `@i`(i が文字列)・`@[1 2]` : アドレスとして読めない値は解なしの `_`(reference.md「`@i = __`。iがhexでないため、解なし」)
    if k == "sec":
        _, kind, op, a, comma = n
        SECB[0] = id(a) if a else None                          # R138: `,` を付けた `[!_ _ ,]` は G7(§5 Q81 は R138・R119 で閉じた)
        av = ev(a, env) if a else None
        if STRICT_GATES and av is not None and op not in ("'", "@") and kind != "mapf":   # R50: `[F,]` の F は写像の関数(被演算子ではない)
                 # R87: 区間に書いた被演算子に丸ごと残った関数は `!_`。書いた行(区間を作った行)で知らせる。恒等射は知らせない
            if isinstance(av, Closure) and not av.dead and av is not ID:
                warn("leftover-lambda", LEFTOVER_MSG + "(区間の被演算子。関数を値として置くなら `$` を付けます。R87)", operand=True); av = UNIT
        return make_section(kind, op, av, comma)
    raise NotImplementedError(f"未実装の構文: {k}")

# ============================== プログラム ==============================
def depth_of(s):
    d, instr, i = 0, False, 0
    while i < len(s):
        c = s[i]
        if c == "\\" and not instr: i += 2; continue      # 文字リテラル \[ \` などは数えない
        if c == "`": instr = not instr
        elif not instr: d += (c in "([{") - (c in ")]}")
        i += 1
    return d

def is_comment_line(text):                     # 行頭の ` の先読みルール
    if not text.startswith("`"): return False
    m = text.find("`", 1)
    if m == -1: return True
    after = text[m + 1:m + 2]
    return not (after != "" and after in "@~! ")

def ends_with_opener(text):
    t = text.rstrip()
    return t[-1:] in ("(", "[", "{") and not t.endswith("\\" + t[-1:])

def next_indent(merged, j):
    while j < len(merged) and not merged[j].strip(): j += 1
    if j >= len(merged): return -1
    ln = merged[j]; return len(ln) - len(ln.lstrip("\t"))

def check_unclosed_string(merged, starts):
    """R127 の断りの順 0(前処理 classifyNewlines): 文字列の `…` が行の終わりまでに閉じていなければ、その行を名指してファイルごと止める。
    文字列の外の `\\` は次の1字を文字にし、中の `\\` は文字そのもの。コメントの行は見ない。"""
    for ln, lno in zip(merged, starts):
        body = ln.lstrip("\t")
        if not body.strip() or is_comment_line(body.lstrip(" ")): continue
        inside = False; k = 0
        while k < len(body):
            ch = body[k]
            if ch == "\\" and not inside: k += 2; continue          # 文字列の外の `\` は次の1字を文字にする(`\``)。中の `\` は文字そのもの
            if ch == "`": inside = not inside
            k += 1
        if inside:
            e = SyntaxError("unclosed-string: 閉じていない文字列があります(行の終わりまでに、文字列の終わりの `` ` `` がありません)。文字列は `` `…` `` で閉じます。文法に無い形なので、前処理で止めます(R127)")
            e.loc = (PARSE_FILE, lno, body.index("`") + 1 + (len(ln) - len(body)))
            raise e

def check_param_block_position(merged, starts):
    """R134(--strict): 字下げの仮引数のブロック(`?` で始まる行と、その上の1段深い仮引数の行)は、関数の本体と既定値の外の `名前 :` の行の下にだけ置ける。
    `名前 :` でない行(`o : 5 ,`・`f : x ?`)の下か、関数の本体(`?` のある行)の中に置いたら、その行を名指して止める(param-block-position)"""
    rows = []
    for ln, lno in zip(merged, starts):
        if not ln.strip() or is_comment_line(ln.lstrip("\t").lstrip(" ")): continue
        rows.append((len(ln) - len(ln.lstrip("\t")), ln.strip(), lno))
    name_row = re.compile(r"^#?[\w']+\s*:\s*$")
    for k, (e, t, lno) in enumerate(rows):
        if not t.startswith("?") or k == 0: continue
        if rows[k - 1][0] < e + 1: continue                         # 上が1段深い仮引数の行でなければ仮引数のブロックではない
        own = next((j for j in range(k - 1, -1, -1) if rows[j][0] < e), None)
        if own is None or rows[own][1].rstrip()[-1:] in ("[", "(", "{"): continue      # 括りの中の `?` の行は R135(param-block-bracket)が先
        bad = None
        if not name_row.match(rows[own][1]): bad = own              # `名前 :` でない行の下(被演算子・`?` の行の下)
        else:
            d = rows[own][0]
            for j in range(own - 1, -1, -1):                        # 祖先に関数の本体(`?` のある行)があれば、本体の中。名指すのはブロックを下に置いた行(R134 の例の @)
                if rows[j][0] < d:
                    d = rows[j][0]
                    if re.search(r"\?\s*$|\s\?\s", rows[j][1]) and "`" not in rows[j][1]: bad = own
                    if d == 0: break
        if bad is not None:
            e_ = SyntaxError(f"param-block-position: 字下げの仮引数のブロックで書いた関数を、`名前 :` の定義の行の下でない所(関数の本体の中・被演算子)に置いています(§4 R134)。関数をファイルの名前の定義にして、ここではその名前を書きます(欄なら、その名前を欄に置きます)")
            e_.loc = (PARSE_FILE, rows[bad][2], rows[bad][0] + 1)
            raise e_

def check_definition_end_blank(merged, starts):
    """alpha1/README.md「定義の終わりの空行」(前処理): いちばん外の定義が字下げのブロックで終わったら、続きの行でない次の行の前に空行を1行置く(無ければ definition-end-blank-line)。
    定義かどうかは、いちばん外の行に括りの外の `:` があるか。空行が要らない所: ブロックの途中・ブロックの中・1行で書き終えた定義・括りで行をまたいだ定義・ファイルの終わり。コメントの行は空行に数えない。"""
    def delta_colon(t):
        depth = 0; inside = False; k = 0; colon = False
        while k < len(t):
            ch = t[k]
            if ch == "\\" and not inside: k += 2; continue
            if ch == "`": inside = not inside
            elif not inside:
                if ch in "([{": depth += 1
                elif ch in ")]}": depth -= 1
                elif ch == ":" and depth == 0: colon = True
            k += 1
        return depth, colon
    cur_def = block_seen = blank_after = False; bdepth = 0
    for ln, lno in zip(merged, starts):
        if not ln.strip():
            if block_seen: blank_after = True
            continue
        if bdepth > 0:                                               # 括りで行をまたぐ定義の途中
            bdepth += delta_colon(ln)[0]; continue
        if ln[0] == "\t":
            if cur_def: block_seen = True; blank_after = False
            continue
        if ln[0] == " ": continue                                    # 続きの行
        if is_comment_line(ln.strip()): continue
        if cur_def and block_seen and not blank_after:
            e = SyntaxError("definition-end-blank-line: いちばん外の定義が字下げのブロックで終わった後、次の行の前に空行がありません。定義の後に空行を1行置きます(alpha1/README.md「定義の終わりの空行」)")
            e.loc = (PARSE_FILE, lno, 1); raise e
        d, colon = delta_colon(ln.strip())
        bdepth = max(d, 0); cur_def = colon and d <= 0; block_seen = blank_after = False

def check_question_row_indent(merged, starts):
    """§6.2 の表(前処理): `?` の行の置き場の誤り(括りを閉じた後ろの `?` ほか)。行をまたぐ括りを閉じた同じ行の後ろに `?` が来る形(`f : [x` ⏎ `⇥y] ? x + y`)は、
    その行を名指して question-row-indent で止める(仕様書に規則と見本は無く、表の1行と設計者の試験(@2)による)"""
    depth = 0; opened_line = None
    for ln, lno in zip(merged, starts):
        if not ln.strip(): continue
        if depth == 0 and (ln[0] in " \t" or is_comment_line(ln.strip())): continue
        inside = False; k = 0
        while k < len(ln):
            ch = ln[k]
            if ch == "\\" and not inside: k += 2; continue
            if ch == "`": inside = not inside
            elif not inside:
                if ch in "([{":
                    if depth == 0: opened_line = lno
                    depth += 1
                elif ch in ")]}":
                    depth -= 1
                    if depth == 0 and opened_line is not None and opened_line != lno and ln[k + 1:].lstrip().startswith("?"):
                        e = SyntaxError("question-row-indent: 行をまたぐ括りを閉じた後ろに `?` があります。`?` の行の置き場の誤りです(前処理)。括りは1行で書くか、`?` を括りを閉じた次の行の字下げに置きます(`⇥? x + y`)")
                        e.loc = (PARSE_FILE, lno, k + 2); raise e
                    if depth < 0: depth = 0
            k += 1
        if depth == 0: opened_line = None

PBP_PENDING = []
def logical_lines(src):
    raw = src.replace("\r\n", "\n").replace("\r", "\n").split("\n")
    merged, starts, i = [], [], 0
    while i < len(raw):
        ln = raw[i]; starts.append(i + 1); i += 1
        while (len(ln) - len(ln.rstrip("\\"))) % 2 == 1 and i < len(raw):   # `\` + 改行 = 文字LF
            ln += "\n" + raw[i]; i += 1
        merged.append(ln)
    if STRICT_GATES: check_unclosed_string(merged, starts)       # R127 の断りの順 0: 閉じていない文字列はファイル全体を先に読むので、どの行にあっても先
    if STRICT_GATES: check_definition_end_blank(merged, starts)    # 前処理: 定義の終わりの空行(alpha1/README.md)
    if STRICT_GATES: check_question_row_indent(merged, starts)       # 前処理: `?` の行の置き場の誤り(§6.2 の表)
    if STRICT_GATES:                                               # R134: 仮引数のブロックの置き場(名前の定義の行の下だけ)。R127: 仮引数の段なので、外の同名(P2)より後に出す(集めて、_parse_source の段の整理へ)
        try: check_param_block_position(merged, starts)
        except SyntaxError as e_: PBP_PENDING.append(e_)
    out = []                                   # (字下げ, 本文)
    j = 0
    while j < len(merged):
        ln = merged[j]; lno = starts[j]; j += 1
        if not ln.strip(): continue
        indent = len(ln) - len(ln.lstrip("\t"))
        body = ln[indent:]
        if body.startswith(" ") and out and (indent == 0 or indent >= out[-1][0]):   # 空白始まり = 前の行の続き(TAB の後の空白も。今の深さ以上の TAB は揃えとして読み捨てる。preprocessor.md §0)
            prev = out[-1][1]
            out[-1] = (out[-1][0], lstr(prev + " " + body.strip(), prev.lineno, prev.indent)); continue
        if indent == 0 and is_comment_line(body): continue
        opener_ = body
        while depth_of(body) > 0 and j < len(merged):                       # 括りが閉じるまで続く
            if ends_with_opener(body) and next_indent(merged, j) > indent: break   # ブロック形式の括り
            if STRICT_GATES and merged[j].strip().startswith("?"): raise bracket_question_error(opener_, starts[j], len(merged[j]) - len(merged[j].lstrip("\t")), indent, out, [(len(merged[j]) - len(merged[j].lstrip("\t")), merged[j].strip())])
            body += ("\x02" if STRICT_GATES else " ") + merged[j].strip(); j += 1      # --strict: 括りの中の改行は行の区切り(list_model §3.1・R133。`[inc : 5` ⏎ `r : inc + 1]`)
        out.append((indent, lstr(body, lno, indent)))
    if STRICT_GATES: check_bracket_question_rows(out)
    return out

def _last_open_pos(t):
    """行の中で閉じていない最後の開き括りの位置(文字列の中は数えない)。なければ -1"""
    st = []; q = False; k = 0
    while k < len(t):
        ch = t[k]
        if ch == "\\": k += 2; continue
        if ch == "`": q = not q
        elif not q:
            if ch in "([{": st.append(k)
            elif ch in ")]}" and st: st.pop()
        k += 1
    return st[-1] if st else -1

def bracket_advice(opener, ind, prev, inner):
    """R135 の言い分の書き直し先を置き場で出し分ける(断る・通すには使わない)。prev: 開いた行より前の行 (字下げ, 本文)、inner: 括りの中の行の本文。(案内, R134 を名指すか)"""
    t = str(opener).strip(); p = _last_open_pos(t); pre = t[:p].rstrip() if p >= 0 else t
    rows = [str(x[1]).strip() for x in inner]; rind = [x[0] for x in inner]
    qi = next((k for k, x in enumerate(rows) if x.startswith("?")), len(rows))
    q = rows[qi] if qi < len(rows) else "?"
    nodef = (q.strip() != "?" and q.rstrip().endswith("?")) or any(re.match(r"^[\w']+\s*:\s*\S", x) for x in rows[:qi])
    one = "" if nodef else "1行の括り(`[x y ? x + y]`)に、長いか既定値・行に割った枝を使うなら"
    # 前の行が定義の行
    if qi >= 1 and re.match(r"^[\w']+\s*:\s*\S", rows[qi - 1]) and not rows[qi - 1].startswith("?") and not re.match(r"^[\w']+\s*:\s*$", rows[qi - 1]) and rind[qi - 1] <= rind[qi]:
        return "`?` は前の行の終わりに続けて書きます(`m : x ? x + 1`)", False
    infield = any(re.match(r"^[\w']+\s*:\s*$", x) for x in rows[:qi])
    parent = next((x for x in reversed(prev) if x[0] < ind), None)
    in_body = parent is not None and str(parent[1]).rstrip().endswith("?")
    if infield:
        if in_body or re.search(r"\?\s*$|\?\s*[\[({]", pre) or re.match(r"^[\w']+\s*:\s*.*\S", pre) and ind > 0 and in_body:
            return "欄の1行(`m : x ? x + 1`)か、ファイルの名前の定義にしてここではその名前を書きます", False
        return "欄の1行(`m : x ? x + 1`)か、字下げの欄のブロック(`m :` ⏎ `⇥⇥x` ⏎ `⇥? x + 1`。字下げは欄の行から数える)に書きます", False
    if re.match(r"^[\w']+\s*:\s*$", pre) and ind > 0:                  # `⇥c : [`・`⇥m : [`
        if in_body: return ("" if nodef else "1行の括りか、") + "ファイルの名前の定義にしてここではその名前を書きます(R134 と同じ言い方)", True
        return ("" if nodef else "1行の括り(`m : [x ? x + 1]`)か、") + "字下げの欄のブロック(`m :` ⏎ `⇥⇥x` ⏎ `⇥? x + 1`。字下げは欄の行から数える)に書きます", False
    if pre == "" and ind > 0 and prev and re.match(r"^[\w']+\s*:\s*$", str(prev[-1][1]).strip()):   # `⇥c :` ⏎ `⇥⇥[`
        return ("" if nodef else "1行の括りか、") + "ファイルの名前の定義にしてここではその名前を書きます(R134 と同じ言い方)", False
    if ind == 0 and (pre == "" or re.match(r"^[\w']+\s*:\s*\$?$", pre)):
        if pre == "": return (("" if nodef else "短ければ1行の括り(`[x y ? x + y]`)に、長いか既定値・行に割った枝を使うなら") + "ファイルの名前の定義にして、その名前を書きます"), False
        return one + "名前の定義(`g :` ⏎ `⇥⇥x` ⏎ `⇥⇥y` ⏎ `⇥? x + y`)に書きます", False
    return ("" if nodef else "1行の括りか、") + "ファイルの名前の定義に書きます", False

def bracket_question_error(opener, lineno, tabs, ind=0, prev=(), inner=()):
    """R135(2026-11-06 の寄せ5): 複数行の括りの中の `?` で始まる行は、TAB の数に依らず前処理で断る(reason `param-block-bracket`、名指す行は `?` の行)。言い分の書き直し先は置き場で出し分ける"""
    o = str(opener).strip()
    adv, r134 = bracket_advice(opener, ind, list(prev), list(inner))
    e = SyntaxError("param-block-bracket: 複数の行に書いた括り(`%s` の行で開いた括り)の中に、`?` で始まる行(TAB %d 個)があります。括りの中は字下げを数えないので、括りの中に `?` の行は置けません(名前の無い関数に仮引数のブロックの綴りは無い、§4 R131 の帰結1)。%s。文法に無い形なので、読む段で止めます(§4 R135%s)" % (o if len(o) <= 30 else o[:30] + "…", tabs, adv, "・§4 R134" if r134 else ""))
    e.loc = (PARSE_FILE, lineno, tabs + 1)
    return e

def param_block_position_error(row, what="枝の値"):
    """R134(2026-11-06 の寄せ5): 字下げの仮引数のブロックで書いた関数は名前の定義(ファイルの定義と構造体の欄)の綴り。枝の値・既定値の値に置いたら読む段でファイルごと止める(reason `param-block-position`、名指す行はそのブロックを持つ `:` の行)"""
    ln = getattr(row, "lineno", 0)
    e = SyntaxError("param-block-position: %sに、字下げの仮引数のブロックで書いた関数があります。仮引数のブロックは名前の定義(ファイルの定義と構造体の欄)の綴りです。関数をファイルの名前の定義にして、その名前を書きます(既定値が無ければ、1行の括り `[x ? …]` でも書けます)。文法に無い形なので、読む段で止めます(§4 R134)" % what)
    if ln: e.loc = (PARSE_FILE, ln, getattr(row, "indent", 0) + 1)
    return e

def check_bracket_question_rows(rows):
    """ブロック形式の括り(行末が開きで、下に字下げの行が続き、同じ深さの閉じ行がある)の中の、`?` で始まる行を探す(どの深さでも)"""
    n = len(rows); best = None                                          # 最初の `?` の行(行の順)。その行を囲む括りは、いちばん内側(あとに開いた物)
    for i in range(n):
        ind, text = rows[i]
        if not ends_with_opener(text): continue
        j = i + 1
        while j < n and rows[j][0] > ind: j += 1
        if j == i + 1 or j >= n or rows[j][0] != ind or rows[j][1][:1] not in (")", "]", "}"): continue
        for k in range(i + 1, j):
            if str(rows[k][1]).lstrip().startswith("?"):
                if best is None or k < best[0] or (k == best[0] and i > best[1]): best = (k, i, j)
                break
    if best:
        k, i, j = best; ind, text = rows[i]
        raise bracket_question_error(text, getattr(rows[k][1], "lineno", 0), rows[k][0], ind, rows[:i], [(rows[m][0], rows[m][1]) for m in range(i + 1, j)])

def take_block(rows, i):                       # rows[i] の子(より深い行)と、括りの閉じ行を取り出す
    ind, text = rows[i]
    j, children = i + 1, []
    while j < len(rows) and rows[j][0] > ind:
        children.append(rows[j]); j += 1
    tail = None
    if ends_with_opener(text):
        if j < len(rows) and rows[j][0] == ind and rows[j][1][:1] in (")", "]", "}"):
            t0 = rows[j][1]
            if not STRICT_GATES and ends_with_opener(t0):                   # `]~ [` : 閉じた行がそのまま次の括りを開く(list_model.md §5.3.2 の `[…]~ […]~`)
                ch2, tail2, j2 = take_block(rows, j)
                tail = t0[1:].rstrip()[:-1] + "\x01" + (tail2 or "")
                children = ChainRows(children); children.more = [ch2] + list(getattr(ch2, "more", ())); j = j2
            else:
                tail = t0[1:]; j += 1
        else: raise SyntaxError("閉じ括弧の行がありません(開きと同じ深さに置きます)")
    return children, tail, j

class ChainRows(list):
    more = ()

SEAT_ROW = re.compile(r"^(?:-_|!_|!!_|_!)(?:,)?$")
def spliced(text, children, tail):             # 括りのブロックを1つの値(NODE)として行へ差し込む
    if STRICT_GATES and len(children) == 1 and not getattr(children, "more", ()) and SEAT_ROW.match(children[0][1].strip()) \
           :
        # R138(§7.61): 1つの行を割った `[` ⏎ `!_` ⏎ `]`(`(…)` も)は、1行の括りと同じ点なしの席(`[!_]`・`[-_]`・`[!!_]`・`[_!]`、後ろに `,` も)。1行へ戻して読む
        tk = text.rstrip()
        if tk[-1:] in "[(":
            return tokenize(lstr(tk + children[0][1].strip() + {"[": "]", "(": ")"}[tk[-1]] + (tail or ""), getattr(text, "lineno", 0), getattr(text, "indent", 0)))
    head = text.rstrip()[:-1] + "\x01" + (tail or "")         # 開きを \x01 に替えても桁は動かない
    return tokenize(lstr(head, getattr(text, "lineno", 0), getattr(text, "indent", 0)), [make_block_value(children, True, True)] + [make_block_value(c, True, True) for c in getattr(children, "more", ())])

POSTFIX_ONLY = {"$", "!!", "!", "##", "###"}
def ends_infix(text):                          # 行末が中置の意味を持つ演算子(`+`・`,`・`==` など)か。値・語・前置/後置だけの演算子で終われば字下げのブロックは置けない
    t = text.rstrip()
    if not t or t[-1] in "[({`\"'": return False
    try: toks = tokenize(lstr(t, 0, 0))
    except Exception: return False
    return bool(toks) and toks[-1].kind == "OP" and toks[-1].text not in POSTFIX_ONLY and toks[-1].text not in ("?", ":")
def op_spliced(text, children):                # 行末の中置演算子の右に、字下げのブロックを1つの値として置く
    return tokenize(lstr(text.rstrip() + " \x01", getattr(text, "lineno", 0), getattr(text, "indent", 0)), [make_block_value(children, True)])

def key_name(t): return t.text[1:-1] if t.kind == "STR" else (t.text[1:] if t.kind == "CHAR" else t.text)

def syntax_at(e, p):                           # 構文エラーに、解析が止まったトークンの場所を付ける
    t = p.at(p.i) or (p.t[-1] if p.t else None)
    if t is not None and t.line and getattr(e, "loc", None) is None: e.loc = (PARSE_FILE, t.line, t.col)
    return e

def finish(toks, block=None):
    p = Parser(toks, block)
    try:
        node = p.parse_top()
        if p.i != len(p.t): raise SyntaxError(leftover_tok_msg(p.t[p.i]))
    except SyntaxError as e: raise syntax_at(e, p)
    return node

def is_branch_block(rows):
    """字下げの行のうち、先頭が名前でない `条件 : 値`(欄の `名前 : 値` ではない行)を含めば、枝で選ぶ括り"""
    base = rows[0][0]
    for ind, text in rows:
        if ind != base: continue
        try: toks = tokenize(text)
        except Exception: return False
        if len(toks) >= 3 and not (toks[0].kind in ("ID", "STR", "CHAR") and toks[1].kind == "OP" and toks[1].text == ":"):
            depth = 0
            for t in toks:
                if t.kind == "OPEN": depth += 1
                elif t.kind == "CLOSE": depth -= 1
                elif depth == 0 and t.kind == "OP" and t.text == ":": return True
    return False
class ErasedNode(tuple):                       # R113: `s : _` の欄を除いた構造体の木(除いた名前を持つ。外の局所の名前が見える所で information)
    erased = ()
def erased_node(node, names):
    e = ErasedNode(node); e.erased = tuple(names); return e

def branch_outside_error(where, text=None):     # 左辺が鍵でない `:`(枝)を、`?` の直後の字下げブロックの外に書いた
    e = SyntaxError(f"branch-outside-match-case: {where}に、左辺が鍵(名前か文字列)でない `:` があります。今の仕様書にこの形の決まりが無いので、実装だけの止めとして断ります(仕様に書かれたら外します)。"
                    "枝を書くなら、関数の本体にして `?` の直後の字下げブロックに並べます(`f : x ?` ⏎ `⇥x > 0 : 1` ⏎ `⇥0`)。値だけが要るなら、論理演算で書きます(`x > 0 & 1`)")
    ln_ = getattr(text, "lineno", 0) if text is not None else 0
    if ln_: e.loc = (PARSE_FILE, ln_, getattr(text, "indent", 0) + 1)
    return e

def branch_row_text(rows):                     # 枝の行(左辺が鍵でない `:` を含む行)の最初の1つ
    base = rows[0][0]
    for ind, text in rows:
        if ind == base and is_branch_block([(ind, text)]): return text
    return None

def ends_comma(toks): return bool(toks) and toks[-1].kind == "OP" and toks[-1].text == ","

def trailing_comma_error(text, body):
    """行末の `,` は書かない(list_model.md §3.1。2026-08-22 に行末カンマを落とした)。行は改行と字下げだけで並ぶ"""
    msg = ("trailing-comma-row: 行末の `,` は書きません。ブロックの行は改行と字下げだけで並びます(list_model.md §3.1)。直し方: 行末の `,` を消します")
    if body: msg += ("。関数の本体の行は、枝の行か、順に評価する手続きの行です(R76・R130)。List を返すなら1つの式にします"
                     "(`[x <= 0 & \\1], [x > 0 & \\0], x`)")
    e = SyntaxError(msg)
    ln_ = getattr(text, "lineno", 0)
    if ln_: e.loc = (PARSE_FILE, ln_, getattr(text, "indent", 0) + len(str(text).rstrip()))
    return e

def make_block_value(rows, in_brackets=False, real_bracket=False):  # 字下げ/括りの中身: 構造体 or 余積で並べた式(real_bracket: 複数行の括りの中。そこに `?` の行は置けない、R135)
    if not rows: return ("lit", [])
    if is_branch_block(rows): raise branch_outside_error("括りか `名前 :` の下のブロック", branch_row_text(rows))
    base, i, items = rows[0][0], 0, []
    while i < len(rows):
        ind, text = rows[i]
        if ind != base:
            q87_ = str(text).lstrip().startswith("?")         # 揃わなかった行が `?` の行: 複数行の括りの中の `?` の行(R135 の param-block-bracket。§5 Q87 は閉じた)
            e_ = SyntaxError(("param-block-bracket: 複数の行に書いた括りの中に、`?` で始まる行は置けません(§4 R135)。名前の無い関数は1行の括り(`[x ? x + 1]`)で書くか、ファイルの名前の定義(`名前 :` の下に仮引数の行と `?` の行)にして、その名前を書きます") if q87_ else "ブロックの行は字下げを揃えます")
            ln_ = getattr(text, "lineno", 0)
            if ln_: e_.loc = (PARSE_FILE, ln_, getattr(text, "indent", 0) + 1)       # 揃わなかった行の場所(R135 の param-block-bracket)
            raise e_
        children, tail, nxt = take_block(rows, i)
        bracket = tail is not None
        toks = spliced(text, children, tail) if bracket else tokenize(text)
        if (bracket or not children) and ends_comma(toks):      # 行末の `,` は書かない(list_model.md §3.1)
            raise trailing_comma_error(rows[nxt - 1][1] if bracket else text, False)
        key, rest = None, toks
        if len(toks) >= 2 and toks[0].kind in ("ID", "STR", "CHAR") \
                and toks[1].kind == "OP" and toks[1].text == ":":
            key, rest = key_name(toks[0]), toks[2:]
        if bracket or not children:
            if key is not None and not rest: raise SyntaxError(f"{key} : の値がありません")
            if key is not None and len(rest) == 1 and rest[0].kind == "OP":   # 演算子そのもの(例: div : /)→ 文字(推測)
                items.append((key, ("lit", Char(rest[0].text)))); i = nxt; continue
            items.append((key, finish(rest)))
        elif key is not None and rest and text.rstrip().endswith("?"):      # `名前 : 仮引数 ?` の下の字下げの本体(欄の関数)
            items.append((key, finish(rest, parse_rows(children))))
        else:                                  # `key :` の下に字下げした入れ子
            if key is None or rest: raise NotImplementedError("入れ子の字下げは `名前 :`・`名前 : 仮引数 ?` の下だけ実装")
            if not real_bracket and own_question_row(children):          # R134: 欄の `名前 :` の下の仮引数のブロック(`obj :` ⏎ `⇥m :` ⏎ `⇥⇥⇥y : 2` ⏎ `⇥⇥? y`)は欄の関数
                rel = [(d - ind, r) for d, r in children]
                items.append((key, build_block_def(lstr(f"{key} :", getattr(text, "lineno", 0), getattr(text, "indent", 0)), rel)[2])); i = nxt; continue
            items.append((key, make_block_value(children, real_bracket=real_bracket)))
        i = nxt
    return block_items_value(items, in_brackets)

def block_items_value(items, in_brackets=False):
    """行の (鍵, 節) の並びから、構造体か行の列の節を組む(字下げのブロック・括りのブロック・改行で割った括りに共通)"""
    if any(k is not None for k, _ in items):   # 1つでも `名前 : 値` があれば構造体
        fields, extras, spreads = [], [], []
        for k, node in items:
            if k is not None: fields.append((k, node))
            elif node[0] == "id" and not STRICT_GATES: fields.append((node[1], node))      # 既定: 裸の識別子は名前も値もそれ(--strict では欄でない行、R133)
            elif not STRICT_GATES and node[0] == "post" and node[1] == "~": spreads.append(node)      # 既定: 器に撒く行(`[ foo : v / this~ ]`)。書いた行が勝ち、撒く行は書かれなかった残りを埋める(list_model.md §5.3)
            elif STRICT_GATES: extras.append(node)                    # R80: 欄でない行(欄を指す名前なら local-field で断る。評価の所で)
            else: raise SyntaxError("構造体の行は `名前 : 値` か裸の識別子です")
        if extras:
            refs = {}; local_refs(extras, refs, True)
            if not any(k in refs for k, _ in fields): raise SyntaxError("構造体の行は `名前 : 値` か裸の識別子です")
            return ("fieldblock", fields, extras)
        if STRICT_GATES:                                           # R113: `s : _` の欄は席を取らない(書いた `_` 1つだけの右辺。`[s : _]` は `[]` と同じ)
            kept = [(k, v) for k, v in fields if v != ("hole",)]
            if len(kept) != len(fields):
                gone = [k for k, v in fields if v == ("hole",) and k not in {kk for kk, _ in kept}]
                return erased_node(("struct", kept) if kept else ("lit", []), gone)
        return ("struct", fields, spreads) if spreads else ("struct", fields)
    nodes = [n for _, n in items]
    if in_brackets and not STRICT_GATES and len(nodes) >= 2 and all(n[0] == "id" for n in nodes):   # 既定: [ x \n y ] は省略記法(--strict では名前1つの行も要素、R133・list_model)
        return ("struct", [(n[1], n) for n in nodes])
    if STRICT_GATES and len(nodes) >= 2: return ("rows", nodes)       # --strict: 行の列は List。行に書いた関数も要素のまま(R61 の `,` の積とは違い、関数を `!_` にしない。§6.4・R125)
    return nodes[0] if len(nodes) == 1 else ("prod", nodes)         # 行が要素の列(次元の行): 1 2 / 3 4 = 1 2 , 3 4

class Rows(list):
    """parse_rows の結果。pos[k] = k 番目の行の (行番号, 字下げ)。R130 が最初に当たった裸の行を名指しするのに使う"""
    pos = ()
def parse_rows(rows):                          # match_case の行(括りのブロックを値に持てる)
    out, i, marks = [], 0, []
    if not rows: return out
    base = rows[0][0]
    while i < len(rows):
        ind, text = rows[i]
        marks.append((len(out), getattr(text, "lineno", 0), ind))
        if ind != base: raise SyntaxError("本体の行は字下げを揃えます")
        children, tail, nxt = take_block(rows, i)
        if tail is not None: toks = spliced(text, children, tail)
        elif children and ends_infix(text):                    # 行末の中置演算子の右の字下げのブロック
            p = Parser(op_spliced(text, children))
            try:
                r = p.parse_row()
                if p.i != len(p.t): raise SyntaxError(leftover_tok_msg(p.t[p.i]))
            except SyntaxError as e: raise syntax_at(e, p)
            out.append(r); i = nxt; continue
        elif children and text.rstrip().endswith("?"):         # `名前 : 仮引数 ?` の下の字下げの本体(入れ子の関数。本体の中の局所の定義)
            toks = tokenize(text)
            p = Parser(toks, parse_rows(children))
            try:
                r = p.parse_row()
                if p.i != len(p.t): raise SyntaxError(leftover_tok_msg(p.t[p.i]))
            except SyntaxError as e: raise syntax_at(e, p)
            out.append(r); i = nxt; continue
        elif children:                         # `条件 :` の下の字下げのブロック(`:` の右に置ける)。枝の行を含めば入れ子の cases、値の行だけなら括りと同じ値
            if not text.rstrip().endswith(":"): raise NotImplementedError("入れ子の字下げは `条件 :` の下だけ実装")
            if STRICT_GATES and any(str(r).lstrip().startswith("?") for _, r in children): raise param_block_position_error(text)       # R134: 枝の値に仮引数のブロック
            cp = Parser(tokenize(lstr(text.rstrip()[:-1], getattr(text, "lineno", 0), getattr(text, "indent", 0))))
            try:
                cond = cp.parse_expr(0)
                if cp.i != len(cp.t): raise SyntaxError(leftover_tok_msg(cp.t[cp.i]))
            except SyntaxError as e: raise syntax_at(e, cp)
            inner = check_body_rows(parse_rows(children))
            val = ("cases", inner) if any(c is not None for c, _ in inner) else make_block_value(children)
            out.append((cond, val)); i = nxt; continue
        elif text.startswith("`") and text.endswith("`") and text.count("`") == 2 and nxt < len(rows):
            i = nxt; continue                  # docstring(最後の行は既定値なので捨てない)
        else: toks = tokenize(text)
        if ends_comma(toks): raise trailing_comma_error(rows[nxt - 1][1] if tail is not None else text, True)      # 行末の `,` は書かない(list_model.md §3.1・match_case.md §5)
        p = Parser(toks)
        try:
            r = p.parse_row()
            if p.i != len(p.t): raise SyntaxError(leftover_tok_msg(p.t[p.i]))
        except SyntaxError as e: raise syntax_at(e, p)
        out.append(r); i = nxt
    res = Rows(out); last = {}
    for n, ln, ind in marks: last[n] = (ln, ind)
    res.pos = [last.get(k) for k in range(len(out))]
    return res

def group_spec(rows):                          # 複数行の括り仮引数: 名前 / 名前 : 既定値 / ~rest
    names, rest, defaults, after = [], None, {}, []
    base = rows[0][0] if rows else 0
    for ind, row in rows:
        if ind != base: raise SyntaxError("括りの中の行は字下げを揃えます")
        p = Parser(tokenize(row)); t = p.next()
        if p.is_op(t, "~"): rest = p.next().text
        elif t.kind == "ID":
            (after if rest else names).append(t.text)
            if p.is_op(p.peek(), ":"):
                if STRICT_GATES: raise r131_error(t.text, tok=p.peek())
                raise SyntaxError("括りの中の仮引数には既定値を書けません(pattern_guide.md、2026-10-18)。"
                                  "器を既定で持たせるなら、呼び出す側が作って渡します")
        else: raise SyntaxError(f"括り仮引数の行として不正です: {row!r}")
        if p.i != len(p.t): raise SyntaxError(f"括り仮引数の行を解釈できません: {row!r}")
    return ("destr", names, rest, defaults, after)

def r131_error(nm, unit=False, tok=None):                # R131: 仮引数の括りに既定値の行を書いた(--strict。読む段でファイルごと止める。reason は param-default-bracket)
    head = "param-default-bracket: 仮引数の括りに、既定値の行があります" + (f"(`{nm} : …`)" if nm else "") + "。括りは参照の口(呼ぶ側の器を指す口)で、既定値を持ちません。番地を直に指したいなら、呼ぶ側が番地を渡します。"
    if unit and nm: tail = f"既定値に `_` を置く口は要りません。値で受けるなら `{nm}`(値の口)、参照で受けるなら `[{nm}]`(参照の口)と書きます(§4 R114)。"
    else: tail = "既定値は、字下げの仮引数のブロックの `名前 : 既定値` の行に書きます(`gq :` ⏎ `⇥⇥y : 1` ⏎ `⇥? …`)。括りの `?` と `$[…]` には仮引数のブロックの綴りが無いので、既定値を使うなら名前の定義にします。"
    e = SyntaxError(head + tail + "文法に無い形なので、読む段で止めます(§4 R131)")
    if tok is not None and getattr(tok, "line", 0): e.loc = (PARSE_FILE, tok.line, tok.col)       # 仮引数のブロックの行は syntax_at を通らないので、場所をここで付ける
    return e

def unit_like(x, env, pnames):                 # 既定値の綴りが `_` と分かる値か(未定義の名前・`[]`・`[_]`・`~_`・`_ _`・`_ , _`・それらを右辺に持つ名前)
    if x[0] == "bin" and x[1] == "'" and len(x) == 4 and x[2][0] == "id" and x[3][0] == "id":     # R139・R115: 構造体の名前を無い欄の名前で引いた `cfg ' hieght` は `!_` と分かる値
        o_ = env.owner(x[2][1]); sv_ = o_.vars.get(x[2][1]) if o_ is not None else None
        if isinstance(sv_, Struct) and x[3][1] not in sv_: return True
    k = x[0]
    if x == ("hole",) or x == ("lit", []): return True
    if k in ("lift", "block"): return not isinstance(x[1], list) and unit_like(x[1], env, pnames)
    if k == "post" and x[1] == "~": return unit_like(x[2], env, pnames)
    if k == "seq": return bool(x[1]) and all(unit_like(y, env, pnames) for y in x[1])
    if k == "prod":
        rest = [y for y in x[1] if y != ("not", ("hole",))]
        return bool(rest) and all(unit_like(y, env, pnames) for y in rest)
    if k == "id" and x[1] not in pnames:
        o = env.owner(x[1])
        return undefined_plain(env, x[1]) if o is None else (x[1] in getattr(o, "zeronames", ()) or x[1] in getattr(o, "voidnames", ()))
    if (k in ("addr", "input") or (k == "bin" and x[1] == "'")) and closed_expr(x, env, pnames):      # R139: `5 ' 1`・`$inc ' 1`・`$vs`・`$w`・`@w` も `!_` と分かる値
        v = quiet_ev(x, env)
        return v is not None and v is not ID and is_unit(v) and not isinstance(v, Closure)
    return False
FILE_DEFS = set()                              # ファイルのいちばん外の定義の名前(定義の順に依らず、先に集める。P2)
IDENT_NAMES = set()                            # 右辺が `_` 1つのファイルの定義の名前(恒等射の名前。R113)
def is_identity_name(x, env, pnames):         # `i : _` の名前は恒等射(関数)で、`!_` と分かる値ではない(R49 の類に入らない。評価する所で残れば `!_`、R128)
    if not (isinstance(x, tuple) and x and x[0] == "id") or x[1] in pnames: return False
    if env.owner(x[1]) is None: return x[1] in IDENT_NAMES
    return False
def branch_unit_gate(n, env):                  # R128(2026-11-18 版): 本体の枝の条件か値が `!_` と分かる値(印 zero の物、R49。未定義の名前も)なら、呼ばない定義でも G22。既定の行は枝でない
    body = n[2]
    while isinstance(body, tuple) and body and body[0] == "block": body = body[1]
    if not (isinstance(body, tuple) and body and body[0] == "cases"): return
    pnames = set()
    for sp in n[1]:
        pnames.update([sp[1]] if sp[0] == "name" else list(sp[1]) + list(sp[4] if len(sp) > 4 else []) + ([sp[2]] if sp[2] else []))
    for c, e in body[1]:
        if c is None: continue
        for what, x in (("条件", c), ("値", e)):
            if x != ("hole",) and x != ("not", ("hole",)) and not is_identity_name(x, env, pnames) and unit_like(x, env, pnames):
                raise Gate(f"G22: 枝の{what}が `!_` と分かる値です(`{node_src(x)}`)。呼ばない定義でも断ります(§4 R128)。名前の書き間違いを直すか、その枝を消します")
def unit_defaults_gate(n, env):                # R139(§5 Q84 は閉じた): 既定値が `!_` と分かる値(印 zero の物、R49)の行は、呼ばない定義でも G22
    pnames = set()
    for sp in n[1]:
        pnames.update([sp[1]] if sp[0] == "name" else list(sp[1]) + list(sp[4] if len(sp) > 4 else []) + ([sp[2]] if sp[2] else []))
    for sp in n[1]:
        for nm, d in ([(sp[1], sp[2])] if sp[0] == "name" and sp[2] is not None else list(sp[3].items()) if sp[0] == "destr" and len(sp) > 3 and sp[3] else []):
            if d != ("hole",) and unit_like(d, env, pnames):
                raise Gate(f"G22: 既定値が `!_` と分かる値の仮引数 `{nm}` は、呼ばない定義でも断ります(§4 R139。無い欄を引いた `cfg ' hieght`・値に付けた `$vs` など、`!_` と分かる値は既定値になりません)。値で受けるなら `{nm}`、参照で受けるなら `[{nm}]` と書きます")

def unit_default_gate(name, d):                # R114: 既定値が書いた `_` 1つだけの仮引数は断る(`[~rest : _]` と同じ G22)
    if STRICT_GATES and d == ("hole",):
        raise Gate(f"G22: 既定値に `_` を書いた仮引数 `{name}` は断ります(R114。`_` は書かなかったことと同じで、既定値になりません)。値で受けるなら `{name}`、参照で受けるなら `[{name}]` と書きます")

DEF_DEPTH = [0]                                # いま読んでいる仮引数の既定値の入れ子の深さ(R127 断りの順 4 の木の順)
def parse_param_line(row):
    toks_ = tokenize(row)
    if STRICT_GATES:                           # R131: 括りの中の `:`・左に括りのある `:` の行(`[x ~xs] : [1 2 3]`・`~[y] : 1`)。最初の深さ0の `:` より右(既定値の右辺)は見ない
        depth_, opened_ = 0, False
        for k_, t_ in enumerate(toks_):
            if t_.kind == "OPEN": depth_ += 1; opened_ = True
            elif t_.kind == "CLOSE": depth_ -= 1
            elif t_.kind == "OP" and t_.text == ":":
                if depth_ > 0 or opened_:
                    prev_ = [x for x in toks_[:k_] if x.kind == "ID"]
                    raise r131_error(prev_[-1].text if prev_ and depth_ > 0 else None, tok=t_)
                break
    p = Parser(toks_)
    spec = p.parse_param()
    if p.is_op(p.peek(), ":"):
        if spec[0] != "name": raise SyntaxError("分解の形の仮引数にデフォルト値は書けません")
        p.next(); DEF_DEPTH[0] += 1
        try: spec = ("name", spec[1], p.parse_expr(0))
        except (SyntaxError, SignError) as e_:
            if not hasattr(e_, "tdepth"): e_.tdepth = DEF_DEPTH[0]                        # R127 断りの順 4: 既定値の中の関数の `?` は、外の関数の `?` を全部見た後
            raise
        finally: DEF_DEPTH[0] -= 1
        unit_default_gate(spec[1], spec[2])
    if p.i != len(p.t): raise SyntaxError(f"仮引数の行を解釈できません: {row!r}")
    return spec

def define_head(text):                         # (名前, export か)
    head = tokenize(text)
    exported = len(head) == 3 and head[0].kind == "OP" and head[0].text == "#"
    if exported: head = head[1:]
    if not (len(head) == 2 and head[0].kind == "ID" and head[1].kind == "OP" and head[1].text == ":"):
        raise NotImplementedError("字下げブロックを持てる定義は `名前 :` の形だけ実装")
    return head[0].text, exported

def wrap_export(node, exported): return ("export", node) if exported else node

def own_question_row(children):
    """`名前 :` の下のブロックが、その名前の仮引数のブロックか(R134)。`?` の行の持ち主(上のいちばん近い浅い行)が、この `名前 :` の行そのものなら仮引数のブロック。
    欄の `m :` の下の `?` の行(`obj :` ⏎ `⇥m :` ⏎ `⇥⇥⇥y : 2` ⏎ `⇥⇥? y`)は、欄 m の仮引数のブロックで、obj は構造体"""
    for k, (d, row) in enumerate(children):
        if row.startswith("?") and not any(children[j][0] < d for j in range(k)): return True
    return False

def build_block_def(text, children):           # name :  / 仮引数ブロック(2段) / ? 本体
    name, exported = define_head(text)
    qs = [k for k, (_, row) in enumerate(children) if row.startswith("?")]
    if STRICT_GATES:                                                       # R134: 既定値の値(`k :` の下)に仮引数のブロック
        for k in qs:
            if children[k][0] >= 2:
                for m in range(k - 1, -1, -1):
                    if children[m][0] < children[k][0] and str(children[m][1]).rstrip().endswith(":"): raise param_block_position_error(children[m][1], "仮引数の既定値の値")
    if len(qs) > 1: raise SyntaxError("? が複数あります")
    q = qs[0]; qind, qrow = children[q]
    if qind >= 2: raise SyntaxError("? を仮引数の行と同じ深さに置けません(1段字下げにします)")
    if q == 0: raise SyntaxError("仮引数の行がありません")
    prows, params, i = children[:q], [], 0
    while i < len(prows):
        ind, row = prows[i]
        if ind > 2: raise SyntaxError("仮引数の行は2段に揃えます(3段以上の行があります)")
        if ind < 2: raise SyntaxError("仮引数の行は2段字下げです")
        sub, tail, nxt = take_block(prows, i)
        if tail is not None:                   # [ ... ] の複数行
            if tail.strip().startswith("?"):
                raise SyntaxError("複数の行に書いた括りの閉じの行に ? を続けられません")
            params.append(group_spec(sub))
        else:
            if sub: raise SyntaxError("仮引数の行は2段に揃えます(3段以上の行があります)")
            params.append(parse_param_line(row))
        i = nxt
    inline, tail_rows = qrow[1:].strip(), children[q + 1:]
    if inline and tail_rows: raise SyntaxError("? の後ろに本体を書いたときは、続きの行を書けません")
    if inline: body = finish(tokenize(inline))
    else:
        rows = parse_rows(tail_rows)
        if not rows: raise SyntaxError("本体がありません")
        check_body_rows(rows, True)
        body = ("cases", rows)
    return wrap_export(("def", name, ("lam", params, body)), exported)

IMPORT_STACK = []                              # 読み込み中のファイル(相対パスの基準・循環の検出)
MODULES = {}                                   # 絶対パス → ファイルの値(1回だけ評価)

IMPORT_NOTED = set()
IMPORT_FAILED = []                             # 失敗した import のパス(診断 information の材料)

def import_file(path, spread=False):           # spread: `f`@~ はファイルの全定義を展開する
    import os
    if not isinstance(path, str): raise NotImplementedError("標準ライブラリの import(IO@ など)は未実装")
    importer = IMPORT_STACK[-1] if IMPORT_STACK else ""
    base = os.path.dirname(importer) if importer else os.getcwd()
    full = os.path.abspath(os.path.join(base, path))
    if full not in MODULES:
        if full in IMPORT_STACK: raise SignError(f"import が循環しています: {path}")
        if not os.path.exists(full):           # 失敗した import: 名前は定義されず、未定義 → __ に収束する
            IMPORT_FAILED.append(path)
            _m = f"取り込むファイル `{path}` が見つかりません。この取り込みは何も定義せず、そこから来るはずの名前は未定義(`_`)になります"      # 断らず、既定でも知らせる(利用者 2026-11-04)
            INFO_KINDS.add("import-not-found")
            if STRICT_GATES:
                if ("import-not-found", _m) not in WARNINGS: WARNINGS.append(("import-not-found", _m)); WARN_LINES[("import-not-found", _m)] = CURLINE[0]
            elif _m not in IMPORT_NOTED:                   # 既定は終わりにまとめて出さない(終わらない入力でも読めるように、その場で stderr へ)
                IMPORT_NOTED.add(_m); print(f"知らせ: import-not-found: {_m}", file=sys.stderr)
            return Struct() if spread else UNIT
        IMPORT_STACK.append(full)
        try:
            env, last = Env(), UNIT
            for v in run(open(full, encoding="utf-8").read(), env): last = v
        finally: IMPORT_STACK.pop()
        MODULES[full] = (env, last)
    env, last = MODULES[full]
    if env.exports: return Struct(env.exports)   # `#` の公開があれば、撒く/返すのは公開だけ(execution_model.md §2)
    return Struct(env.vars) if spread else path   # 公開が無い(alpha の自己ホストのソース): @~ は頂の束縛を全部、@ は字面の文字列

def is_import_spread(node): return node[0] == "importspread"

# ---- 構文木のキャッシュ(起動時間の短縮。仕様に無い最適化。既定の道のみ。SIGN_NO_CACHE=1 で切れる) ----
#      構文解析は外の状態に依らず(既定の道では警告も出さない)、同じ原文と同じ sign_interp.py なら同じ構文木になる。
#      重い解析(目安 15 ミリ秒以上)だけ、利用者のキャッシュ置き場(SIGN_CACHE_DIR か ~/.cache/sign。本人だけが読み書きできる)に pickle で置く。
#      読めない・壊れている・形が合わない物は黙って捨てて解析し直す。
CACHE_ON = [os.environ.get("SIGN_NO_CACHE") != "1"]
_CACHE_SALT = []
import pickle as _pickle
class _AstPickler(_pickle.Pickler):
    """Char だけは名前で書く(`python sign_interp.py` で走ると、この型は __main__ の物と sign_interp の物の 2 つあり、別の型の Char が混ざると isinstance が外れる)。"""
    def persistent_id(self, obj):
        return ("C", str(obj)) if type(obj) is Char else None
class _AstUnpickler(_pickle.Unpickler):
    def persistent_load(self, pid):
        if pid[0] == "C": return Char(pid[1])
        raise _pickle.UnpicklingError("unknown")
    def find_class(self, module, name):                      # 構文木は組み込みの型(tuple・list・dict・str・int・None)だけ。ほかの型が出たら捨てて解析し直す
        raise _pickle.UnpicklingError("class not allowed")
# キャッシュに置く最小の解析時間(秒)。試験が時間の揺れに左右されないよう、SIGN_CACHE_MIN_SECONDS で変えられる
try: _CACHE_MIN_SECONDS = float(os.environ.get("SIGN_CACHE_MIN_SECONDS", "0.015"))
except ValueError: _CACHE_MIN_SECONDS = 0.015

def _cache_path(src):
    import hashlib
    if not _CACHE_SALT:
        try: _CACHE_SALT.append(hashlib.sha1(open(__file__, "rb").read()).hexdigest())      # 構文解析の実装が変われば別の鍵
        except OSError: _CACHE_SALT.append("")
    if not _CACHE_SALT[0]: return None
    d = os.environ.get("SIGN_CACHE_DIR") or os.path.join(os.path.expanduser("~"), ".cache", "sign")
    return os.path.join(d, hashlib.sha1((_CACHE_SALT[0] + "\0" + src).encode("utf-8", "surrogatepass")).hexdigest() + ".pkl")
def parse_source(src, defer=False):
    """ソース全体を構文木(文の並び)にする。評価はしない(型の静的パスもこれを使う)。"""
    global PARSE_FILE
    if not CACHE_ON[0] or STRICT_GATES or len(src) < 400: return _parse_source(src, defer)
    path = None
    try:
        path = _cache_path(src)
        if path and os.path.isfile(path):
            with open(path, "rb") as fh: nodes = _AstUnpickler(fh).load()
            if isinstance(nodes, list):
                PARSE_FILE = IMPORT_STACK[-1] if IMPORT_STACK else None
                SRC_LINES[PARSE_FILE] = src.replace("\r\n", "\n").replace("\r", "\n").split("\n")
                return nodes
    except Exception: pass
    t0 = time.perf_counter()
    nodes = _parse_source(src)
    if path and time.perf_counter() - t0 >= _CACHE_MIN_SECONDS:
        try:
            import pickle
            os.makedirs(os.path.dirname(path), mode=0o700, exist_ok=True)
            tmp = path + ".%d.tmp" % os.getpid()
            with open(tmp, "wb") as fh: _AstPickler(fh, pickle.HIGHEST_PROTOCOL).dump(nodes)
            os.replace(tmp, path)
        except Exception:
            try: os.remove(tmp)
            except Exception: pass
    return nodes

DEFERRED = []                                  # 解く前の段(仮引数・使う所の `#`)の断り。run が、ファイルのいちばん外の同名(P2)の後で出す
def refusal_stage(e):
    """R127 の断りの順: 0 閉じていない文字列 / 1 前処理 / 2 前段の文法 / 3 行の文法 / 5 仮引数 / 6 使う所の `#`(4 はファイルのいちばん外の同名で、run が見る)"""
    m = str(e)
    if m.startswith(("compare-chain", "infix-missing-operand", "pointfree-tree-notation", "operator-unknown", "operator-removed", "infix-mixed-assoc")): return 3
    if m.startswith(("param-block-position", "param-not-name", "param-default-bracket")): return 5
    if m.startswith("export-mark-position"): return 6
    if "閉じていない文字列" in m or "文字列が閉じて" in m: return 0
    if m.startswith(("block-after-value", "question-row-indent", "definition-end-blank-line", "param-block-bracket")) or any(w in m for w in ("字下げ", "ブロックの行", "閉じ括弧の行", "0桁目", "仮引数の行", "本体がありません", "? が複数", "? の後ろに本体", "括りの閉じの行")): return 1
    return 2
def raise_by_stage(errs, defer):
    _pbp = [e for e in errs if str(e).startswith("param-block-position")]
    if _pbp and any(str(e) == "本体の行は字下げを揃えます" for e in errs):          # R134: 仮引数のブロックを本体の中に置いた形は、字下げの乱れより置き場の断りで名指す
        errs = _pbp
    ranked = sorted(((refusal_stage(e), k, e) for k, e in enumerate(errs)), key=lambda t: (t[0], getattr(t[2], "tdepth", 0) if t[0] >= 5 else 0, (getattr(t[2], "loc", None) or (0, 10**9))[1] if t[0] >= 5 else 0, t[1]))
    early = [t for t in ranked if t[0] <= 3]
    if early or not defer: raise ranked[0][2]
    DEFERRED.extend(t[2] for t in ranked)

def _parse_source(src, defer=False):
    global PARSE_FILE
    PARSE_FILE = IMPORT_STACK[-1] if IMPORT_STACK else None
    SRC_LINES[PARSE_FILE] = src.replace("\r\n", "\n").replace("\r", "\n").split("\n")
    nodes, lines, i = [], logical_lines(src), 0
    errs = list(PBP_PENDING); PBP_PENDING.clear()               # R134 の置き場の断り(段 5)
    # --strict: 断りの順(R127 の段)のために、行ごとの断りを集めてから、いちばん先の段の物で断る
    while i < len(lines):
        i0 = i
        try:
            indent, text = lines[i]
            if indent != 0: raise SyntaxError(f"字下げの位置が不正です: {text!r}")
            if text.startswith("?"): raise SyntaxError("? を0桁目に置けません(定義の行より深く字下げします)")
            children, tail, i = take_block(lines, i)
            if children and i < len(lines) and lines[i][0] == 0 and lines[i][1].startswith("?"):
                raise SyntaxError("? を0桁目に置けません(定義の行より深く字下げします)")
            stripped = text.rstrip()
            if tail is not None:                   # p : [ ... ]  /  f [ ... ]
                node = finish(spliced(text, children, tail))
            elif children and stripped.endswith(":"):
                if own_question_row(children):
                    node = build_block_def(text, children)
                else:                              # 字下げで書く構造体 / 余積で並べた式
                    name, exported = define_head(text)
                    node = wrap_export(("def", name, make_block_value(children)), exported)
            elif children and stripped.endswith("?"):
                node = finish(tokenize(text), parse_rows(children))
            elif children and ends_infix(text): node = finish(op_spliced(text, children))
            elif children: raise SyntaxError("block-after-value: 値や語、前置・後置にしかならない演算子(`$`・`!!`・`!`)で終わる行の下には字下げのブロックを置けません。続けるなら TAB の後に空白を置きます(`\\t 5`)、ブロックを渡すなら `:`・`?`・中置演算子の右に置きます")
            else: node = finish(tokenize(text))
            nodes.append(node)
        except (SyntaxError, SignError) as e_:
            if not STRICT_GATES: raise
            errs.append(e_)
            if i == i0: break                                   # 行の取り出しで失敗した(次の行へ進めない)
    if errs: raise_by_stage(errs, defer)
    return nodes


LEVEL_COVER = {}                               # 仮引数に当てた `$`(`$f`・`$@f`)を値の演算子の被演算子に置いた節 id → 演算子。呼んだときの dollar-non-function も level-mismatch で指す(R99)
def closed_expr(x, env, params):
    """仮引数を使わず、呼び出しも書き込みも無い式か(字面・見える名前・`$`・`@`・値の演算子・`'`・`,`・`~`)。読む段が、その式を今の名前で解いてよい物"""
    while isinstance(x, tuple) and x and x[0] == "block": x = x[1]
    if not isinstance(x, tuple) or not x: return False
    k = x[0]
    if k == "lit": return True
    if k == "id": return x[1] not in params and x[1] not in ("__", "_") and env.owner(x[1]) is not None
    if k in ("addr", "input"): return closed_expr(x[1], env, params)
    if k == "bin" and len(x) > 3 and (x[1] in VALUE_OPS or x[1] in ("'", "==", "!==")): return closed_expr(x[2], env, params) and closed_expr(x[3], env, params)
    if k == "prod": return bool(x[1]) and all(closed_expr(y, env, params) for y in x[1] if y != ("not", ("hole",)))
    if k == "post" and x[1] == "~": return closed_expr(x[2], env, params)
    if k == "pre" and len(x) > 2 and x[1] == "~": return closed_expr(x[2], env, params)
    return False
def quiet_ev(x, env):
    """知らせを出さずに解く(読む段の見立て用)。断り・例外は None"""
    nw, nl = len(WARNINGS), LEFTOVERS[0]
    try: return ev(x, env)
    except Exception: return None
    finally:
        for kv in WARNINGS[nw:]: WARN_LINES.pop(kv, None)
        del WARNINGS[nw:]; LEFTOVERS[0] = nl
def const_closure(v):
    """R125: 関数が、呼ぶごとの名前(仮引数・本体の局所)を使わない定数の点か。使えば、書いた行の外で生きない"""
    if not isinstance(v, Closure): return True
    if v.native is not None or v.params is None or v.args: return False      # 点なし・部分適用は、捕えた物が見えないので定数と見ない
    if v.env is None or v.env.parent is None: return True
    own = set()
    for sp in v.params: own.update(_param_names_of(sp))
    names = []
    def walk(x):
        if isinstance(x, list):
            for c in x: walk(c)
        elif isinstance(x, tuple) and x:
            if x[0] == "id" and len(x) > 1 and isinstance(x[1], str): names.append(x[1])
            for c in x[1:]:
                if isinstance(c, (tuple, list)): walk(c)
    walk(v.body)
    for nm in names:
        if nm in own: continue
        o = v.env.owner(nm)
        if o is not None and o.parent is not None: return False
    return True
VARY_ROWS = set()                              # 本体の節 id: 枝で違う関数の入る List の行(返す時に関数の行を `!_` にする。知らせは読む段が出し済み)
VARY_FIELDS = {}                               # 本体の節 id → (節, 欄の名前の集合): 枝や実行時の鍵で違う関数が入りうる欄(R125)。返す所で `!_` にする

VALUE_OPS = {"+", "-", "*", "/", "%", "^", "<<", ">>", "&&", ";;", "><", "||", "<", "<=", "=", ">=", ">", "!="}           # `==`・`!==` は関数の番地も比べる(R62)
def lam_static(n, env):
    """R81・R99・R139(--strict): 値の演算子の被演算子に置いた形だけで答えが決まる物は、呼ばない定義でも読む段で、その式を書いた行に知らせる。
    仮引数に当てた `$`(`tw2 : f ? $f + 1`・`$@f + 1`)は level-mismatch(呼んで値が来ても、その dollar-non-function は level-mismatch が指す)。
    仮引数を使わず、字面とファイルの名前と関数の番地だけでできた被演算子の組(`$inc + 1`・`inc + 1`・`0x10 + i`)は、その式を今の名前で解いて、呼んだときと同じ知らせを出す。"""
    params = set()
    def pnames(sp):
        if isinstance(sp, tuple):
            if sp and sp[0] == "name" and len(sp) > 1 and isinstance(sp[1], str): params.add(sp[1])
            for c in sp[1:]:
                if isinstance(c, (tuple, list)): pnames(c)
        elif isinstance(sp, list):
            for c in sp: pnames(c)
    for sp in n[1]: pnames(sp)
    def core(x):
        while isinstance(x, tuple) and x and x[0] == "block": x = x[1]
        return x
    def pdollar(x):
        x = core(x)
        if x[0] != "addr": return None
        y = x[1]
        if y[0] == "input": y = y[1]
        return x if (y[0] == "id" and y[1] in params) else None
    def closed(x):
        x = core(x)
        if x[0] == "lit": return True
        if x[0] == "id": return x[1] not in params and x[1] != "__" and env.owner(x[1]) is not None
        if x[0] == "addr" and core(x[1])[0] == "id":
            nm = core(x[1])[1]
            return nm not in params and isinstance(env.get(nm) if env.owner(nm) is not None else None, Closure)
        return False
    def named(x):
        x = core(x); return x[0] in ("id", "addr")
    def emit_at(x, f):
        ln = node_line(x)
        old = CURLINE[0]
        if ln: CURLINE[0] = ln
        try: f()
        finally: CURLINE[0] = old
    def walk(x):
        if isinstance(x, list):
            for c in x: walk(c)
            return
        if not isinstance(x, tuple) or not x: return
        if x[0] == "lam": return                                      # 入れ子の関数は、その関数を作るときに見る
        if x[0] == "bin" and x[1] in VALUE_OPS and len(x) > 3:
            hit = False
            for side in (x[2], x[3]):
                d = pdollar(side)
                if d is not None:
                    LEVEL_COVER[id(d)] = (x[1], d); hit = True
                    emit_at(x, lambda: warn("level-mismatch", LEVEL_MSG.format(op=x[1])))
            if not hit and closed(x[2]) and closed(x[3]) and (named(x[2]) or named(x[3])):
                def trial():
                    try: ev(x, env)
                    except Exception: pass
                emit_at(x, trial)
                return
        for c in x[1:]:
            if isinstance(c, (tuple, list)): walk(c)
    def walk_dollar(x):                                               # R100・R81: `$` の中身も書いた所として読む(`$vs`・`$[inc , double]`・`$($inc + 1)`)
        if isinstance(x, list):
            for c in x: walk_dollar(c)
            return
        if not isinstance(x, tuple) or not x: return
        if x[0] == "lam": return
        if x[0] == "addr" and pdollar(x) is None and closed_expr(x[1], env, params) and not (core(x[1])[0] == "id" and isinstance(env.get(core(x[1])[1]), Closure)):
            def trial_d():
                try: ev(x, env)
                except Exception: pass
            emit_at(x, trial_d); return
        if x[0] == "addr" and pdollar(x) is None:
            u_ = core(x[1])
            if u_[0] == "prod":                                         # R78・R101: `$[@f , 1]`: 前置 `@` は種類の分からない因子で、`,` が残る積は値(dollar-non-function)
                fs_ = [y for y in u_[1] if y not in (("hole",), ("not", ("hole",)))]
                if len(fs_) >= 2 and any(y[0] == "input" for y in fs_) and all(y[0] == "input" or closed_expr(y, env, params) for y in fs_):
                    emit_at(x, lambda x=x: dollar_warn(x, None)); return
        for c in x[1:]:
            if isinstance(c, (tuple, list)): walk_dollar(c)
    def bare_ret(lam, outer):                                         # R125: 返す所に書いた裸の関数の名前(`k : x ? inc`・既定値の `[y ? inc]`)
        ps = set(outer)
        for sp in lam[1]: ps.update(_param_names_of(sp))
        b = core(lam[2])
        if b[0] == "id" and b[1] not in ps and env.owner(b[1]) is not None:
            f = env.get(b[1])
            if isinstance(f, Closure) and not f.dead and f is not ID:
                emit_at(b, lambda: info("bare-function-return", BARE_RETURN_MSG))
    def nested_lams(x):
        if isinstance(x, list):
            for c in x: nested_lams(c)
            return
        if not isinstance(x, tuple) or not x: return
        if x[0] == "lam": bare_ret(x, params); return
        for c in x[1:]:
            if isinstance(c, (tuple, list)): nested_lams(c)
    def fn_tree(v):                                                   # 欄の値の木(比べる物)
        v = core(v)
        if v[0] == "id" and v[1] not in params and env.owner(v[1]) is not None:
            f = env.get(v[1])
            if isinstance(f, Closure) and not f.dead and f is not ID: return f
        if v[0] == "lam": return Closure(params=v[1], body=v[2], env=env)
        return None
    def vary(fns):
        fs = [f for f in fns if f is not None]
        return len(fs) >= 2 and not all(fn_tree_same(fs[0], g) for g in fs[1:])
    def field_vary():                                                 # R125: 枝で違う関数が入りうる欄・実行時の鍵で引く欄
        b = core(n[2]); keys = set()
        if b[0] == "cases":
            sts = [core(v) for _, v in b[1]]
            sts = [t for t in sts if t[0] == "struct"]
            if len(sts) >= 2:
                names = []
                for t in sts:
                    for k_, _ in t[1]:
                        if k_ not in names: names.append(k_)
                for k_ in names:
                    if vary([fn_tree(v) for t in sts for kk, v in t[1] if kk == k_]):
                        keys.add(k_)
                        for t in sts:
                            if any(kk == k_ and fn_tree(v) is not None for kk, v in t[1]):
                                emit_at(t, lambda t=t, k_=k_: info("bare-function-return", BARE_RETURN_MSG + f"(返す構造体の欄 {k_} は、枝で違う関数が入りうるので `!_`。R125。{node_line(t) or '?'} 行目の枝)"))
            vals_ = [(t_, v_) for t_, v_ in ((core(v), v) for _, v in b[1]) if t_[0] == "id" and t_[1] not in params and env.owner(t_[1]) is not None and isinstance(env.get(t_[1]), RowList)]
            if len(vals_) >= 2:                                           # 2026-11-17 仕様(R125): 枝で違う List の行(`x > 0 : fs3` ⏎ `fd`)の関数は、木が違えば1つに決まらず `!_`。名前を書いた枝の行と既定の行に1つずつ知らせる
                rows_ = [list(env.get(t_[1])) for t_, _ in vals_]
                rvary = False
                for k_ in range(max(len(r_) for r_ in rows_)):
                    fs_ = [r_[k_] for r_ in rows_ if k_ < len(r_) and isinstance(r_[k_], Closure) and not r_[k_].dead and r_[k_] is not ID]
                    if len(fs_) >= 2 and not all(fn_tree_same(fs_[0], g_) for g_ in fs_[1:]): rvary = True
                if rvary:
                    for t_, v_ in vals_:
                        emit_at(v_, lambda v_=v_: info("bare-function-return", BARE_RETURN_MSG + f"(返す List の行は、枝で違う関数が入りうるので `!_`。R125。{node_line(v_) or '?'} 行目の枝)"))
                    VARY_ROWS.add(id(n[2]))
        elif b[0] == "bin" and b[1] == "'" and len(b) > 3 and core(b[2])[0] == "id" and core(b[2])[1] not in params \
                and env.owner(core(b[2])[1]) is not None and not closed_expr(b[3], env, params):
            c = env.get(core(b[2])[1])
            els = list(c.values()) if isinstance(c, Struct) else list(c) if isinstance(c, list) and not isinstance(c, str) else []
            els = [e for e in els if isinstance(e, Struct)]
            names = []
            for e in els:
                for k_ in e:
                    if k_ not in names: names.append(k_)
            for k_ in names:
                if vary([e.get(k_) if isinstance(e.get(k_), Closure) and not e.get(k_).dead else None for e in els]):
                    keys.add(k_)
            if keys: emit_at(b, lambda: info("bare-function-return", BARE_RETURN_MSG + f"(実行時に決まる鍵で引いて返す欄 {', '.join(sorted(keys))} は、違う関数が入りうるので `!_`。R125)"))
        if keys: VARY_FIELDS[id(n[2])] = (n[2], keys)
    for sp in n[1]:
        if isinstance(sp, tuple) and sp and sp[0] == "name" and len(sp) > 2 and sp[2] is not None:
            d_ = sp[2]
            walk(d_); walk_dollar(d_); nested_lams(d_)
            dc = core(d_)                                             # R52: 既定値の `5 inc`(値の上に積んで余る関数)
            if dc[0] == "seq" and len(dc[1]) >= 2 and all(closed_expr(y, env, params) for y in dc[1]):
                vals = [quiet_ev(y, env) for y in dc[1]]
                if not any(isinstance(v, Closure) for v in vals[:-1]) and isinstance(vals[-1], Closure):
                    emit_at(dc, lambda: warn("leftover-lambda", LEFTOVER_MSG))
    walk(n[2]); walk_dollar(n[2]); nested_lams(n[2])
    bare_ret(n, ())
    try: field_vary()
    except Exception: pass

def lam_leftover(n, env):
    """R52: 本体の根の並びが、値(リテラル・仮引数)の後ろに、何も受けない関数で終わる形(`y inc`)は、定義の行で知らせる。"""
    body = n[2]
    if body[0] != "seq" or len(body[1]) < 2: return
    names = {sp[1] for sp in n[1] if sp[0] == "name"}
    last, prev = body[1][-1], body[1][-2]
    if any(e[0] in ("input", "sec") for e in body[1][:-1]): return          # R136: 関数でありうる項(`@f`・`@f x`・点なしの答え)の上の余りは、予想の上では知らせない(実体が当たった方だけを出す)
    if prev[0] == "id" and any(sp[0] == "name" and sp[1] == prev[1] and len(sp) > 2 and sp[2] is not None for sp in n[1]): return    # 既定値のある仮引数も種類が未知
    if last[0] == "id" and last[1] not in names and isinstance(env.get(last[1]), Closure) \
            and (prev[0] == "lit" or (prev[0] == "id" and prev[1] in names)):
        warn("leftover-lambda", LEFTOVER_MSG)

def only_hole(t, env=None):
    """書いた `_` だけでできた項か(R56・R61・R71: `_`・`[_]`・`_ _`・`_ , _`・`_ , !_`。`_` を右辺に持つ名前も)"""
    if t == ("hole",): return True
    if t[0] == "block": return only_hole(t[1], env)
    if t[0] == "seq": return bool(t[1]) and all(only_hole(x, env) for x in t[1])
    if t[0] == "prod":
        rest = [x for x in t[1] if x != ("not", ("hole",))]
        return bool(rest) and all(only_hole(x, env) for x in rest)
    if t[0] == "id" and env is not None:
        o = env.owner(t[1])
        if o is None: return STRICT_GATES and undefined_plain(env, t[1])          # R111: 取り込みの無い範囲の未定義の名前は `_`
        return t[1] in getattr(o, "zeronames", ())
    return False
def undefined_plain(env, name):
    if name in BUILTINS or name == "__": return False
    if STRICT_GATES and name in FILE_DEFS and env.owner(name) is None: return False        # 定義の順に依らない(まだ束ねていないだけ)
    if DECL_USED[0] and declined_reason(env, name): return False
    e_ = env
    while e_:
        if getattr(e_, "spread", False): return False
        e_ = e_.parent
    return env.owner(name) is None
def r104_empty(t, env):
    """R104: `$` の先が、長さ 0 と分かる流れか(`[]`・`_`・`[_]`・`[]` を右辺に持つ名前)。まだ解いていない名前は分からない物。"""
    if t[0] == "id":
        o = env.owner(t[1])
        if o is None: return False
        return empty_value(o.vars[t[1]]) or t[1] in getattr(o, "zeronames", ())
    return empty_streams_to_marks([("post", "~", t)], env)[0] == MARK
def dollar_src(n):
    return "$" + node_src(n[1])
def node_src(x):
    k = x[0]
    if k == "id": return x[1]
    if k == "lit": return str(x[1]) if not isinstance(x[1], list) else "[]"
    if k == "hole": return "_"
    if k == "not" and x[1] == ("hole",): return "!_"
    if k == "block":
        inner = x[1]
        return ("[" if False else "(") + node_src(inner) + ")" if inner[0] != "prod" else "[" + node_src(inner) + "]"
    if k == "seq": return " ".join(node_src(y) for y in x[1])
    if k == "prod": return " , ".join(node_src(y) for y in x[1])
    if k == "addr": return "$" + node_src(x[1])
    if k == "post": return node_src(x[2]) + x[1]
    if k == "bin": return f"{node_src(x[2])} {x[1]} {node_src(x[3])}"
    return "…"
def dollar_hint(rest):
    def one(e):
        if e[0] == "addr" or e[0] == "post": return node_src(e)
        if e[0] == "block" and e[1][0] == "prod":
            return "[" + " , ".join(one(y) for y in e[1][1]) + "]"
        return "$" + node_src(e)
    return "[" + " , ".join(one(e) for e in rest) + "]"
def dollar_warn(n, name):
    lc_ = LEVEL_COVER.get(id(n))
    if lc_ is not None and lc_[1] is n: warn("level-mismatch", LEVEL_MSG.format(op=lc_[0])); return      # R99: 仮引数に当てた `$` を値の演算子に置いた所は level-mismatch が指す
    p = POS.get(id(n)); where = f"{p[1]}:{p[2]}: " if p else ""
    what = f"`${name}` の `$` は持ち上げで、先 `{name}` は関数ではありません。" if name else "この `$` は持ち上げで、先は関数ではありません。"
    warn("dollar-non-function", where + what + "`$` が受けるのは関数だけで、この `$` の項は `!_` になります。値が欲しいなら `$` を外して書きます(§4 R99・R100)")
PROVISIONAL = set()                            # R103: 自分の定義の中の `$v` を A と仮置きして読んだ名前
def ev_addr_strict(n, env):
    """R99〜R102(2026-11-13 の仕様): `$` が受けるのは関数だけ。`$名前`・`$[…]` は、先が関数なら関数の番地、関数の番地なら同じ番地(μ)、
    関数でない物(値の名前・字面・器・値だけの `,` の積・計算)なら `!_` で、dollar-non-function で知らせる(前は値を読む参照だった)。言い切れない物(後置の印・種類が未知の取り込み・中で関数が余る物・番地を受けない `@`)は G20。
    `$_` は零射 `[x ? _]`、`$!_` は1引数の恒等射 `[x ? x]` の番地。"""
    t = n[1]
    if t[0] == "id" and t[1] == "__": return UNIT                    # `__` は未定義の名前(単位)。従来どおり
    if t[0] == "id" and STRICT_GATES and env.owner(t[1]) is None:
        rt_ = env
        while rt_.parent is not None: rt_ = rt_.parent
        if t[1] in (rt_.__dict__.get("running") or ()):                     # R103: 自分の値を求める途中の `$v` は、v を A と仮置きした値に当てた `$`(`!_`)
            PROVISIONAL.add(t[1]); dollar_warn(n, t[1]); return UNIT
    if t[0] == "id" and only_hole(t, env): return Ref(native_fixed(lambda x: UNIT, 1))     # `q : _` の `$q`(R56・R63)
    if t[0] == "id" and DECL_USED[0] and (r := declined_reason(env, t[1])):
        if r in ("imported-scope", "import-unknown", "unknown-import"): return Lift()               # R99: 取り込みのある範囲の名前は先の種類の分からない持ち上げ
        strict_gate(f"G20: `${t[1]}` : {t[1]} は{DECL_TEXT[r]}ため、`$` で指せません({r}。R80)", n)
    if t[0] == "id":
        owner = env.owner(t[1])
        cur = owner.vars[t[1]] if owner else None
        if STRICT_GATES and owner is None:
            e_ = env
            while e_:
                if getattr(e_, "spread", False): return Lift()                  # R99: `io@` ⏎ `$zz` は先の種類の分からない持ち上げ(`$?`)。知らせない
                e_ = e_.parent
            if t[1] not in BUILTINS and not (DECL_USED[0] and declined_reason(env, t[1])):
                return Ref(native_fixed(lambda x: UNIT, 1))                    # R111: 取り込みの無い範囲の未定義の名前は `_`。`$no` は `$_` と同じ零射の番地(知らせない)
        if isinstance(cur, Closure) and cur.lo:
            strict_gate(f"G20: `${t[1]}` : その定義の中に、値の上に積まれて余る関数があります(R59。`{t[1]}` を直してから `$` を付けます)", n)
        if STRICT_GATES and isinstance(cur, list) and any(isinstance(x, Closure) for x in cur): return Lift()     # R99: 中身に関数が見える形(A(U))は関数かもしれない
        if isinstance(cur, (Ref, VarRef)): return cur                # R99(2026-11-13): 関数の番地を運ぶ名前に当てた `$` は同じ番地(μ。`g9 : $inc` の `$g9` は `$inc`)。知らせない
        if STRICT_GATES and is_unit(cur) and cur is not ABS: return UNIT      # R56: `!_` と分かる値(を右辺に持つ名前)に当てた `$` は同じ `!_` と分かる値で、知らせない
        if STRICT_GATES and cur is ID: return Ref(ID)                # R49(2026-11-17 の仕様): `$i`(`i : _`)は `$_` と同じ恒等射の番地
        if not isinstance(cur, Closure) or cur.dead:                 # R99・R100(2026-11-13): 先が関数でない `$` の項は `!_`。書いた `$` の項ごとに 1 回知らせる
            dollar_warn(n, t[1]); return UNIT
        return VarRef(owner or env, t[1])                            # 関数の番地
    if STRICT_GATES:                                                 # R49: `$[i]`・`$[_]`・`$[(_)]` も `$_` と同じ恒等射の番地
        c_ = t
        while c_[0] == "block" and isinstance(c_[1], tuple) and c_[1] and isinstance(c_[1][0], str): c_ = c_[1]
        if c_ is not t and (c_ == ("not", ("hole",)) or (c_[0] == "id" and env.owner(c_[1]) is not None and env.get(c_[1]) is ID)): return Ref(ID)
    u = t
    while u[0] == "block" and u[1][0] in ("block", "prod"): u = u[1]
    if u[0] == "block": u = u[1] if u[1][0] == "prod" else u
    if STRICT_GATES and u[0] == "prod" and not only_hole(t, env):          # R101: 単位律(恒等射・書いた `_`・名前の恒等射は `,` の単位)を当てた後も `,` が残る積は G20
        def _unit(x):
            return x == ("hole",)                                  # 2026-11-17 仕様(R61・R101): 単位は `!_` と分かる辺だけ。恒等射(`_`・`i`・`~_`)は関数の因子(`$[inc , _]` は dollar-non-function)
        rest = [x for x in u[1] if not _unit(x)]
        vals_ = []
        for x in rest:                                              # R101・R61: 単位(恒等射・`!_` と分かる値・計算の `!_`)を消して数える。中身に書いた違反は知らせる(R103)
            try: v_ = ev(x, env)
            except Gate: v_ = None
            vals_.append(v_)
        keep = [(x, v_) for x, v_ in zip(rest, vals_) if not (v_ is not None and is_unit(v_) and x[0] != "input")]      # R78: 前置 `@` の項は種類の分からない因子(単位でない)
        if not keep: return UNIT                                    # 単位だけの積は `!_` と分かる値(知らせない、R56)
        if len(keep) == 1:
            _nn = ("addr", keep[0][0])
            if id(n) in POS: POS[id(_nn)] = POS[id(n)]; POS_KEEP.append(_nn)
            return ev_addr_strict(_nn, env)
        for x, v_ in keep:                                          # 2つ以上残る積は値: 丸ごとの関数の因子は leftover-lambda(R61)、`$` の項は dollar-non-function
            if isinstance(v_, Closure) and not v_.dead:
                warn("leftover-lambda", LEFTOVER_MSG + "(`,` の積の因子。関数を積の要素にするなら `[$inc , $double]` と要素ごとに `$` を付けます。R61・R101)")
        dollar_warn(n, None); return UNIT
    if only_hole(t, env): return Ref(native_fixed(lambda x: UNIT, 1))   # $_ : 零射 [x ? _](`$[_]`・`$[_ , !_]`・`q : _` の `$q` も、R56・R71・R63)
    if t[0] == "not" and t[1] == ("hole",): return Ref(ID) if STRICT_GATES else Ref(native_fixed(lambda x: x, 1))   # $_(--strict の綴り): 恒等射そのものの番地(R49。`@[$_]` は `i : _` の i)。既定の `$!_` は1引数の恒等射

    if t[0] == "post" and t[1] == "~" and STRICT_GATES and r104_empty(t[2], env):
        return Ref(native_fixed(lambda x: UNIT, 1))                  # R104: 長さ 0 と分かる流れの `$` は `$_`(零射の番地。知らせない)
    if t[0] == "post":
        strict_gate("G20: 後置の印の付いた `$` の先は、1つの Reader と言い切れません", n)
    before = LEFTOVERS[0]
    if STRICT_GATES:
        h_ = t
        while h_[0] == "block" and not isinstance(h_[1], list): h_ = h_[1]
        if h_[0] == "lam" and "#" not in repr(h_[2]) and "input" not in repr(h_[2]):          # R59・R20: 括りの関数の本体の、仮引数を含まない行は `$` を書いた所で読む(`$[[x] ? f2 (5 inc) 1]` は G20)
            pn_ = set()
            for sp_ in h_[1]: pn_.update(_param_names_of(sp_))
            if not any(f"('id', {q!r})" in repr(h_[2]) for q in pn_) and h_[2][0] in ("seq", "bin", "prod"):
                _nw = len(WARNINGS)
                try: ev(h_[2], env)
                except Exception: pass
                finally:
                    del WARNINGS[_nw:]
    v = ev(t, env)
    if LEFTOVERS[0] != before:                                       # R59: 中で値の上に積まれて余る関数がある
        strict_gate("G20: `$[…]` の中に、値の上に積まれて余る関数があります(`$[add (5 inc)]`・`$[x ? x inc]`)。中身が1つの関数と言い切れません", n)
    if t[0] == "input":                                              # $@f : f が運ぶ参照
        if isinstance(v, (Ref, VarRef)): return v
        return Lift()                                                # R99: 印の無い前置 `@` の項は先の種類の分からない持ち上げ
    if STRICT_GATES:
        h = t
        while h[0] == "block" and not isinstance(h[1], list): h = h[1]
        if h[0] == "seq" and h[1] and h[1][0][0] == "id" and env.owner(h[1][0][1]) is None and h[1][0][1] not in BUILTINS:
            return Lift()                                            # R99: 根の未知な適用(`$[uu 5]`)は先の種類の分からない持ち上げ
        if h[0] == "cases" and (isinstance(v, Closure) or is_unit(v)):
            return Lift()                                            # R99: 枝で選ぶ括りで中身に関数か未知が見える形(`$[5 > 1 : inc]`)
        if isinstance(v, list) and any(isinstance(x, Closure) or is_unit(x) for x in v):
            return Lift()                                            # R99: 中身に関数か未知が見える形(A(U))は関数かもしれない
    if isinstance(v, (Ref, VarRef)): return v                        # R99(2026-11-13): 関数の番地にもう一度当てた `$` は同じ番地(μ。`$$inc`・`$[$inc]` は `$inc`)。知らせない
    if isinstance(v, Closure): return Ref(v)
    if not is_unit(v) or v == [] or v is ABS: dollar_warn(n, None)               # R100(計算に当てた `$` も。`$($inc + 1)`): 先が関数でない `$` の項は `!_` で、知らせる(撒かない空の括り `$[]` も。§5 Q78 (e))
    return UNIT                                                      # R99(2026-11-13): 値に当てた `$` は `!_`(データの番地は作らない。番地は `0x…` で書く、R62)

def force_pending(root, name):
    """value_spec V9: ファイルのいちばん外の値の定義は順序に依らない。自分の行で1回走らせて覚え、先に引かれたらその時に1回走る。"""
    idx, node = root.pending.pop(name)
    root.__dict__.setdefault("forced", {})[idx] = None
    root.running.add(name)
    try: v = ev_place(node, root)
    finally: root.running.discard(name)
    root.forced[idx] = v
    return root.vars.get(name, UNIT)

def hoist_lambdas(nodes, env):
    """P2(法則3): いちばん外の `名前 : 引数 ? 本体` を先に全部集める。並びの順に依らず、後ろの定義の関数も呼べる。
    1回しか定義されていない名前だけを対象にする(同名の再定義は、書いた順のまま)。"""
    defs = []
    for node in nodes:
        d = node[1] if node[0] == "export" else node
        if d[0] == "def": defs.append(d)
    counts = {}
    for d in defs: counts[d[1]] = counts.get(d[1], 0) + 1
    for d in defs:
        if d[2][0] == "lam" and counts[d[1]] == 1 and env.vars.get(d[1]) is None:
            _lo = LEFTOVERS[0]
            v = ev(d[2], env)
            if STRICT_GATES and LEFTOVERS[0] != _lo and isinstance(v, Closure): v = _cp(v, lo=True)
            env.set(d[1], v)

DEPTH_GATE = [0]                               # 深さの門の上限(--strict。0 は無効)。run が決める
DEPTH_TICK = [0]
def depth_gate_limit(nodes, src):
    """深さの門(実体の鍵の入れ子の G7)の上限: (32 × 書いた括りの関数の数 + 1) × 書いたいちばん深い形(coproduct_spec §3.4 の実体の守り)。解く前にソースだけから決める。
    括りの関数 = 括りの仮引数を持つ関数。書いた形の深さは、ソースの括りの入れ子の最大(鍵の深さより浅くならない側)。"""
    cnt = [0]
    def walk(n):
        if isinstance(n, list):
            for c in n: walk(c)
            return
        if not isinstance(n, tuple) or not n: return
        if n[0] == "lam" and any(isinstance(sp, tuple) and sp and sp[0] != "name" for sp in n[1]): cnt[0] += 1
        for c in n:
            if isinstance(c, (list, tuple)): walk(c)
    walk(nodes)
    d = m = 0; q = False
    for ch in src:
        if ch == "`": q = not q
        elif not q:
            if ch in "([{": d += 1; m = max(m, d)
            elif ch in ")]}": d = max(0, d - 1)
    return (32 * max(1, cnt[0]) + 1) * max(1, m)
def value_depth(x):
    """器の入れ子の深さ(数・文字列・関数などは 1 段、器は中身のいちばん深い物の 1 段上)。見る節の数に上限があり、届かなければ -1"""
    seen = {}
    left = [600]
    def d(o):
        if not isinstance(o, (list, tuple)) or isinstance(o, str): return 1
        i = id(o)
        if i in seen: return seen[i]
        left[0] -= 1
        if left[0] < 0: raise OverflowError
        seen[i] = 1
        r = 1 + max((d(y) for y in o), default=0)
        seen[i] = r
        return r
    try: return d(x)
    except (OverflowError, RecursionError): return -1
def depth_gate(a):
    DEPTH_TICK[0] += 1
    if DEPTH_TICK[0] & 7: return
    if not isinstance(a, (list, tuple)): return
    r = value_depth(a)
    if r > DEPTH_GATE[0]:
        strict_gate(f"G7: 括りの仮引数に渡る物の入れ子が上限({DEPTH_GATE[0]} 段)を超えました。形が1段ずつ深くなる再帰(`f : [x ~xs] ? f [xs xs]`)は、実体の鍵が深くなり続けて止まりません(実体の守り・深さの門。上限は 32 × 書いた括りの関数の数 + 1 に、書いた形の深さを掛けた数)")

DROP_DUP = []

def static_exports(path):
    """取り込むファイルの公開(`#`)の名前を、走らせずに構文だけで集める(P2 の名前の表に入れるため)。見つからない・読めない物は空。"""
    import os
    importer = IMPORT_STACK[-1] if IMPORT_STACK else ""
    full = os.path.abspath(os.path.join(os.path.dirname(importer) if importer else os.getcwd(), path))
    try: nodes_ = parse_source(open(full, encoding="utf-8").read())
    except Exception: return []
    return [n[1][1] for n in nodes_ if n[0] == "export" and n[1][0] == "def" and n[1][2] != ("hole",)]

def run(src, env=None):
    fresh = env is None
    env, results = env or Env(), []
    DEFERRED.clear() if fresh else None
    nodes = parse_source(src, defer=STRICT_GATES and fresh)
    if STRICT_GATES and fresh: DEPTH_GATE[0] = depth_gate_limit(nodes, src); DEPTH_TICK[0] = 0
    if STRICT_GATES and fresh:                                   # P2 の門(V9): ファイルのいちばん外で同じ名前の2つ目は断る(`x : _` は書かなかったことと同じで数えない)
        seen_ = {}
        for node in nodes:
            if node[0] == "importspread" and node[1][0] == "lit" and isinstance(node[1][1], str):     # 撒く取り込みの公開(`#`)は裸の名前として範囲に入る。枚を跨ぐ同じ名前は断る(compiler_pipeline.md §4・coproduct_spec P2)
                for nm_ in static_exports(node[1][1]):
                    if nm_ in seen_:
                        o_ = seen_[nm_]
                        raise locate(Gate(f"name-duplicate: 名前 {nm_} が取り込み `{node[1][1]}` の公開と、{('取り込み `' + o_ + '` の公開') if isinstance(o_, str) else '自分の定義'}の両方にあります(枚を跨ぐ同じ名前は断ります。P2。どちらかの名前を変えます)"), node)
                    seen_[nm_] = node[1][1]
                continue
            d_ = node[1] if node[0] == "export" else node
            if d_[0] == "def" and d_[2] != ("hole",):
                if d_[1] in seen_:
                    o_ = seen_[d_[1]]
                    if isinstance(o_, str): raise locate(Gate(f"name-duplicate: 名前 {d_[1]} が自分の定義と、取り込み `{o_}` の公開の両方にあります(枚を跨ぐ同じ名前は断ります。P2。どちらかの名前を変えます)"), d_)
                    # 同じ枚の中の同名は、先に書いた方が勝ち、2つ目は使わない(止めずに information。compiler_pipeline.md §4・documents が優先)。落とすのは行そのもの
                    i1_ = 1 + next(i for i, m_ in enumerate(nodes) if (m_[1] if m_[0] == "export" else m_) is o_)
                    DROP_DUP.append((node, f"名前 `{d_[1]}` はこの枚の {i1_} 番目の文と {1 + nodes.index(node)} 番目の文の両方で定義されています。先に書いた {i1_} 番目が勝ち、{1 + nodes.index(node)} 番目は使われません(compiler_pipeline.md §4。行番号は言えません)"))
                    continue
                seen_[d_[1]] = d_
    if DROP_DUP:
        _drop = {id(n_) for n_, _m in DROP_DUP}; nodes = [n_ for n_ in nodes if id(n_) not in _drop]
        for _n, _m in DROP_DUP: info("name-duplicate", _m)
        DROP_DUP.clear()
    if OPT:                                                       # --opt: 部分計算(sign_pe.py)で残余プログラムにしてから走らせる
        import sign_pe
        nodes = sign_pe.optimize(sys.modules[__name__], nodes)
    if STRICT_GATES and fresh:                                    # R127 の断りの順 5(仮引数: R134・param-not-name・R131・同じ関数の同名)→ 6(使う所の `#`)
        late = [(refusal_stage(e), getattr(e, "tdepth", 0), (getattr(e, "loc", None) or (0, 10**9))[1], 0, e) for e in DEFERRED]; DEFERRED.clear()
        try: static_param_dup(nodes)
        except (SyntaxError, SignError) as e_: late.append((5, getattr(e_, "tdepth", 0), (getattr(e_, "loc", None) or (0, 10**9))[1], 1, e_))      # 木の順(外の関数の `?` が先、既定値の中が後)。同じ `?` では、R134・param-not-name・R131 の後
        if late: raise sorted(late, key=lambda t: t[:4])[0][4]
    if STRICT_GATES and fresh:
        try: static_undefined(nodes, env)
        except Gate: raise                                         # R138: 未定義の名前は断る(name-undefined)
        except Exception: pass                                     # 知らせの補助。失敗しても実行は続ける
        FILE_DEFS.clear(); FILE_DEFS.update(n_[1] for n_ in nodes if isinstance(n_, tuple) and n_ and n_[0] in ("def", "export") and isinstance(n_[1], str))
        IDENT_NAMES.clear(); IDENT_NAMES.update(n_[1] for n_ in nodes if isinstance(n_, tuple) and n_ and n_[0] == "def" and n_[2] in (("not", ("hole",)), ("hole",)))
        try: static_shadow(nodes)
        except Exception: pass
    hoist_lambdas(nodes, env)
    if STRICT_GATES and env.parent is None:                       # V9: 値の定義の遅延(引かれた時に1回走る)
        cnt = {}
        for node in nodes:
            d = node[1] if node[0] == "export" else node
            if d[0] == "def": cnt[d[1]] = cnt.get(d[1], 0) + 1
        env.pending = {}; env.running = set()
        for i, node in enumerate(nodes):
            d = node[1] if node[0] == "export" else node
            if d[0] == "def" and cnt[d[1]] == 1 and d[2][0] != "lam" and env.vars.get(d[1]) is None and d[1] not in BUILTINS:
                env.pending[d[1]] = (i, node)
    for i_, node in enumerate(nodes):
        if env.__dict__.get("forced") and i_ in env.forced:           # 先に引かれて走った定義の行: 覚えた値をそのまま使う
            results.append(env.forced[i_]); continue
        if env.__dict__.get("pending"):
            d_ = node[1] if node[0] == "export" else node
            if d_[0] == "def" and env.pending.get(d_[1], (None,))[0] == i_: env.pending.pop(d_[1])      # 自分の行で走る
        if not STRICT_GATES:                                      # 既定: 止まらない輪の知らせに行番号を付けるためだけに、いちばん外の行を控える(CURLINE は触らない)
            p_ = POS.get(id(node)) or (POS.get(id(node[1])) if node[0] == "export" else None)
            ROW_LINE[0] = p_[1] if p_ else None
        if STRICT_GATES:
            p_ = POS.get(id(node)) or (POS.get(id(node[1])) if node[0] == "export" else None)
            if p_: CURLINE[0] = p_[1]
            ROW_LINE[0] = CURLINE[0]
            WORK[0] = 0                                           # V10: 計算の量は行ごとに数え直す
        rn_ = None
        if env.__dict__.get("running") is not None:
            d_ = node[1] if node[0] == "export" else node
            if d_[0] == "def" and d_[2][0] != "lam": rn_ = d_[1]; env.running.add(rn_)
        try: v = ev_place(node, env)
        finally:
            if rn_ is not None: env.running.discard(rn_)
        if STRICT_GATES and isinstance(v, Closure) and node[0] not in ("def", "export", "opdef"):
            if not v.dead: warn("leftover-lambda", LEFTOVER_MSG)  # R48: 余ったラムダ(部分適用・穴・合成も)は知らせる
            v = UNIT                                              # R42: 評価する所の終わりに残った未評価のラムダは _
        if STRICT_GATES and is_import_spread(node): env.spread = True                  # R99: 取り込みのある範囲の名前は先の種類が分からない
        if is_import_spread(node) and isinstance(v, Struct):
            for k, x in v.items(): env.set(k, x)                  # `file`@~ : export を現在のスコープへ
        results.append(v)
    return results

def run_with_big_stack(fn):
    """深い再帰のため、大きいスタックのスレッドで fn を実行する。
    OS が受け付けるスタックの大きさは環境で違う(Windows は 512MB を断る)ので、大きい順に試す。"""
    import threading
    for mb in (512, 256, 128, 64, 32, 16):
        try:
            threading.stack_size(mb * 1024 * 1024)
        except (ValueError, RuntimeError):
            continue                                    # この大きさは受け付けられない
        sys.setrecursionlimit(min(200000, mb * 1024 * 1024 // 2048))   # スタックに見合う再帰の上限
        th = threading.Thread(target=fn)
        try:
            th.start()
        except (RuntimeError, MemoryError):             # スタックを確保できなかった
            continue
        try:
            while th.is_alive():                        # join(None) だと Windows では Ctrl+C が届かないので、短く待って回す
                th.join(0.2)
        except KeyboardInterrupt:                       # Ctrl+C: トレースバックを出さずに止める(実行中でも、REPL の入力待ちでも)
            try: sys.stdout.flush()
            except Exception: pass
            print("\n中断しました", file=sys.stderr)
            os._exit(130)
        return
    sys.setrecursionlimit(5000)                         # どれも駄目なら、普通のスタックで動かす
    fn()

VERSION = "alpha1 実装 2026-11-17 12:20 JST"

def _dev(make):
    """装置を用意する(--gpio・--i2c・--spi など)。部品が入っていない・バックエンドの名前が違う・使えない、などで落とさず、理由を知らせて終わる。"""
    try: return make()
    except Exception as e:
        print(f"エラー: 装置を用意できません({type(e).__name__}): {e}", file=sys.stderr); sys.exit(1)
CHARSET = ["ascii"]                           # option.ms の charset(ascii | utf32。文字の域の上限だけに効く。メモリ上の幅は asm 版の話)


def _tool(name):                                  # 同じフォルダの道具(sign_check.py など)を読む。無ければ理由を言って終わる(落ちない)
    try: return __import__(name)
    except ImportError as e:
        print(f"エラー: {name}.py を読めません({e})。sign_interp.py と同じフォルダに置きます", file=sys.stderr); sys.exit(1)

def _cli():                                       # コマンド行の入口(`python sign_interp.py …` と、翻訳済みの本体を読むだけの起動口 `sign.py` の両方から呼ぶ)
    global LAYER, STRICT_GATES, OPT
    for _a in [a for a in sys.argv if a.startswith("--charset=")]:
        CHARSET[0] = "utf32" if _a[10:] == "utf32" else "ascii"
        if "--asm" not in sys.argv: sys.argv.remove(_a)           # --asm の組み立ては自分で読む
    for stream in (sys.stdout, sys.stderr):             # 端末の文字コードで表せない文字があっても落ちない
        try: stream.reconfigure(errors="replace")
        except Exception: pass
    if "--version" in sys.argv:
        print("Sign (sign_interp.py) " + VERSION)
        import hashlib as _hashlib, os as _os               # (os を直に import すると、この関数の os が局所名になって他の所が壊れる)版の食い違いを見つけるための印(各ファイルの md5 の先頭 8 文字)
        here = _os.path.dirname(_os.path.abspath(__file__))
        for name in ("sign_interp.py", "sign_gfx.py", "sign_asm.py", "std.sn"):
            try:
                with open(_os.path.join(here, name), "rb") as fh: print(f"  {name}: {_hashlib.md5(fh.read()).hexdigest()[:8]}")
            except OSError: pass
        return
    if "--check" in sys.argv:                           # 実行せずに整合性を静的に検査して知らせる(sign_check.py。使い方は `python sign.py --check file.sn [--json] [--werror] [--no-hint] [--unused]`)
        sys.argv.remove("--check")
        sign_check = _tool("sign_check")
        sys.exit(sign_check.main(sys.argv[1:]))
    if "--asm" in sys.argv:                             # 実行せずに AArch64 のアセンブリを書き出す【拡張】(sign_asm.py。整数と関数だけ。出せない形は理由を言って終わる)
        sys.argv.remove("--asm")
        sign_asm = _tool("sign_asm")
        sys.exit(sign_asm.main(sys.argv[1:]))
    if "--emit-st" in sys.argv:                         # `#` の公開定義のうちデータだけを `.st` に書き出す【拡張】(sign_st.py。関数の署名はまだ)
        sys.argv.remove("--emit-st")
        sign_st = _tool("sign_st")
        sys.exit(sign_st.main(sys.argv[1:]))
    if "--forth" in sys.argv:                           # 実行せずに構文木を後置(Forth の読みの形)で書き出す【拡張】(sign_forth.py。構文だけで意味は写さない)
        sys.argv.remove("--forth")
        sign_forth = _tool("sign_forth")
        sys.exit(sign_forth.main(sys.argv[1:]))
    if "--sexp" in sys.argv:                            # 実行せずに構文木を S 式(Lisp の読みの形)で書き出す【拡張】(sign_sexp.py。構文だけで意味は写さない)
        sys.argv.remove("--sexp")
        sign_sexp = _tool("sign_sexp")
        sys.exit(sign_sexp.main(sys.argv[1:]))
    if "--layer" in sys.argv:
        i = sys.argv.index("--layer"); LAYER = int(sys.argv[i + 1]); del sys.argv[i:i + 2]
    if "--strict" in sys.argv:
        STRICT_GATES = True; sys.argv.remove("--strict")
    if "--opt" in sys.argv:
        OPT = True; sys.argv.remove("--opt")
    for _a in [a for a in sys.argv if a == "--par" or a.startswith("--par=")]:       # 純粋な関数の並列実行(sign_par.py)。--par=N で同時に走らせる数(既定は CPU の数)
        sys.argv.remove(_a)
        _stats = "--par-stats" in sys.argv
        if _stats: sys.argv.remove("--par-stats")
        try: _n = int(_a[6:]) if _a.startswith("--par=") else (os.cpu_count() or 1)
        except ValueError: print("エラー: --par=N の N は整数です(%s)。並列にしません" % _a, file=sys.stderr); _n = 1
        if STRICT_GATES: print("注意: --par は --strict と一緒には使えません(並列にしません)", file=sys.stderr)
        elif not hasattr(os, "fork"): print("注意: この環境には fork が無いので --par は使えません(並列にしません)", file=sys.stderr)
        elif _n > 1:
            sign_par = _tool("sign_par")
            PAR[0] = sign_par.Par(sys.modules[__name__], _n, float(os.environ.get("SIGN_PAR_PROBE_MS", "30")), _stats)
    if "--par-stats" in sys.argv: sys.argv.remove("--par-stats")
    if "--check-f32" in sys.argv:                       # Vector の Float を 32 ビット精度で扱う(ハードウェア上の SIMD と同じ精度。既定は Python の 64 ビット)
        F32[0] = True; sys.argv.remove("--check-f32")
    if "--check-int" in sys.argv:                       # Int の溢れを罠にし、値域の外の十進の字面を断る(仕様どおり。既定は Python の整数)
        global arith
        INTCHK[0] = True; FAST[0] = False; arith = arith_checked; sys.argv.remove("--check-int")
    for a in [a for a in sys.argv if a == "--check-bounds" or a.startswith("--check-bounds=")]:      # 番地の読み書きが装置の帯からはみ出したらエラー。=N で見張る幅(既定 0x100)
        BOUNDS[0] = True
        if "=" in a: BOUNDS[1] = int(a.split("=", 1)[1], 0)
        sys.argv.remove(a)
    for a in [a for a in sys.argv if a.startswith("--region=")]:                                       # --region=名前:始まり:大きさ は --ram と同じ範囲の宣言(実行時は番地の出どころを持たないので範囲だけ見る。出どころまで見るのは sign_check.py)
        f_ = a[9:].split(":")
        if len(f_) == 3: BOUNDS[2].append((int(f_[1], 0), int(f_[2], 0))); BOUNDS[0] = True
        sys.argv.remove(a)
    for a in [a for a in sys.argv if a.startswith("--ram=")]:                                          # --ram=始まり:大きさ(16 進可)。宣言すると、帯と宣言した範囲の外はすべてエラー
        s_, z_ = a[6:].split(":"); BOUNDS[2].append((int(s_, 0), int(z_, 0))); BOUNDS[0] = True; sys.argv.remove(a)
    for a in [a for a in sys.argv if a == "--sys" or a.startswith("--sys=")]:      # システムコール装置(sign_sys.py)。--sys=DIR で作業フォルダを指す(既定は今のフォルダ)
        sign_sys = _tool("sign_sys")
        DEVICES.append(_dev(lambda: sign_sys.Sys(a[6:] or None))); sys.argv.remove(a)
    for a in [a for a in sys.argv if a == "--gpio" or a.startswith("--gpio=")]:    # GPIO 装置(sign_gpio.py)。--gpio=fake などでバックエンドを選ぶ
        sign_gpio = _tool("sign_gpio")
        DEVICES.append(_dev(lambda: sign_gpio.Gpio(a[7:] or None))); sys.argv.remove(a)
    for a in [a for a in sys.argv if a == "--i2c" or a.startswith("--i2c=")]:     # I2C 装置(sign_bus.py)
        sign_bus = _tool("sign_bus")
        DEVICES.append(_dev(lambda: sign_bus.I2c(a[6:] or None))); sys.argv.remove(a)
    for a in [a for a in sys.argv if a == "--spi" or a.startswith("--spi=")]:     # SPI 装置(sign_bus.py)
        sign_bus = _tool("sign_bus")
        DEVICES.append(_dev(lambda: sign_bus.Spi(a[6:] or None))); sys.argv.remove(a)
    for a in [a for a in sys.argv if a == "--sound" or a.startswith("--sound=")]:   # 音の装置(sign_audio.py)
        sign_audio = _tool("sign_audio")
        DEVICES.append(_dev(lambda: sign_audio.Sound(a[8:] or None))); sys.argv.remove(a)
    for a in [a for a in sys.argv if a == "--db" or a.startswith("--db=")]:       # SQLite 装置(sign_db.py)。--db=フォルダ でファイルを置く場所を指す(既定は今のフォルダ)
        sign_db = _tool("sign_db")
        DEVICES.append(_dev(lambda: sign_db.Db(a[5:] or None))); sys.argv.remove(a)
    net_ca = next((x[9:] for x in sys.argv if x.startswith("--net-ca=")), None)         # TLS で信じる CA(PEM)
    net_proxy = next((x[12:] for x in sys.argv if x.startswith("--net-proxy=")), None)  # プロキシ(http://… socks5://… env)
    for x in [x for x in sys.argv if x.startswith(("--net-ca=", "--net-proxy="))]: sys.argv.remove(x)
    for a in [a for a in sys.argv if a == "--net" or a.startswith("--net=")]:       # ネットワーク装置(sign_net.py)。--net=local・--net=host1,host2 で相手を絞る
        sign_net = _tool("sign_net")
        DEVICES.append(_dev(lambda: sign_net.Net(a[6:] or None, ca=net_ca, proxy=net_proxy))); sys.argv.remove(a)
    for a in [a for a in sys.argv if a.startswith("--display=")]:        # 描画装置(sign_gfx.py)をバックエンドに付ける
        sign_gfx = _tool("sign_gfx")
        DEVICES.append(sign_gfx.parse_spec(a[len("--display="):])); sys.argv.remove(a)
    if DEVICES or "--timer" in sys.argv or "--timer=virtual" in sys.argv:    # タイマー装置(0x9200000)。--timer=virtual は待たずに時計だけ進める
        sign_gfx = _tool("sign_gfx")
        virtual = "--timer=virtual" in sys.argv
        disp = next((d for d in DEVICES if isinstance(d, sign_gfx.Display)), None)   # 描画装置があればそれ(--sys・--gpio などの装置が先頭に来ても取り違えない)
        DEVICES.append(sign_gfx.Timer(disp, virtual))
        for a in ("--timer", "--timer=virtual"):
            if a in sys.argv: sys.argv.remove(a)
        timer = DEVICES[-1]
        script = next((x[len("--input="):] for x in sys.argv if x.startswith("--input=")), "")
        for x in [x for x in sys.argv if x.startswith("--input=")]: sys.argv.remove(x)
        inp = sign_gfx.Input(timer, script)                                    # 入力装置(0x9300000)
        DEVICES.append(inp)
        if disp is not None: disp.on_event = inp.push; inp.display = disp              # window の本物の入力を行列へ
    status = []
    def report(e):
        loc = getattr(e, "loc", None)
        if loc:
            f, ln, col = loc
            name = os.path.relpath(f) if f else "<入力>"
            print(f"エラー: {name}:{ln}:{col}: {e}", file=sys.stderr)
            src = SRC_LINES.get(f)
            if src and 0 < ln <= len(src):
                print(f"  {ln:>4} | {src[ln - 1]}", file=sys.stderr)
                print(f"       | {''.join(c if c == chr(9) else ' ' for c in src[ln - 1][:col - 1])}^", file=sys.stderr)
        else: print(f"エラー: {e}", file=sys.stderr)
        status.append(1)
    if len(sys.argv) > 1:
        def main():
            try:
                IMPORT_STACK.append(os.path.abspath(sys.argv[1]))
                with open(sys.argv[1], encoding="utf-8") as fh: res = run(fh.read())
                if res and not STRICT_GATES: print(show(res[-1]))      # V9: 定義でない行の値は、ファイルでは捨てる(--strict)。既定は旧 alpha のとおり最後の行の値を表示する
            except (SyntaxError, SignError, NotImplementedError) as e: report(e)
            except WorkLimit as e: report(e)
            except RecursionError: report("再帰が深すぎます(スタックの大きさが足りません)")
            except OSError as e: report(e)
            except MemoryError: report("メモリが足りません。この入力は処理を続けられません")
            except UnicodeDecodeError: report("ファイルを UTF-8 として読めません。この入力は処理を続けられません")
            except Exception as e: report(f"内部エラー({type(e).__name__}): この入力は処理を続けられません。{e}")      # 処理系は入力で異常終了しない: 続けられない事由を知らせて終わる
        def main_then_finish():
            main()
            for d in DEVICES:                                       # window は閉じるまで残す(同じスレッドで)
                if hasattr(d, "finish"): d.finish()
        run_with_big_stack(main_then_finish)
        for kind, msg in WARNINGS:
            ln_ = WARN_LINES.get((kind, msg))
            print(f"{'知らせ' if kind in INFO_KINDS else '警告'}: {kind}: {msg}" + (f" [{ln_} 行目]" if ln_ else ""), file=sys.stderr)
        sys.exit(status[0] if status else 0)
    else:
        def repl():
            env = Env()
            pending = []                                              # 定義の続きを読むとき、字下げの無い行に当たったら次の入力として取っておく
            while True:
                if pending: line = pending.pop(0)
                else:
                    try: line = input("sign> ")
                    except EOFError: break
                if line.rstrip().endswith(("?", "[", ":")):          # 本体が次の行以降に続く定義: 空行か字下げの無い行まで読む
                    more = [line]
                    while True:
                        try: nxt = input("  ... ")
                        except EOFError: break
                        if not nxt.strip(): break
                        if nxt[0] not in " \t]":                      # 字下げの無い行 = 新しい入力
                            pending.append(nxt); break
                        more.append(nxt)
                    line = "\n".join(more) + "\n"
                try:
                    for v in run(line, env): print(show(v))
                except (SyntaxError, SignError, NotImplementedError) as e: print(f"エラー: {e}")
                except WorkLimit as e: print(f"エラー: {e}")
                except RecursionError: print("エラー: 再帰が深すぎます")
                except MemoryError: print("エラー: メモリが足りません。この入力は処理を続けられません")
                except Exception as e: print(f"エラー: 内部エラー({type(e).__name__}): この入力は処理を続けられません。{e}")       # 次の入力へ続ける
        run_with_big_stack(repl)

if __name__ == "__main__":
    _cli()
