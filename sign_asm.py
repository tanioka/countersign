import os
"""sign_asm.py — Sign の構文木から AArch64 のアセンブリ(GNU as の綴り)を出す。

設計者の Pass 4(pass4.js)と、integer_overflow.md §1.1 の命令列に合わせている。
出せる範囲(第 2 段)は、整数だけの計算である:

  - 十進の整数の字面(Int の値域 -(2^63-1) 〜 2^63-1。外は字面の時点でコンパイルエラー)
  - `+` `-` `*`(Int は値域の外へ出たら罠 = wfi。integer_overflow.md §1.1 の命令列)、符号反転
  - `/` `%`(割る数が 0 でない十進の字面のときだけ。それ以外は `__` を運ぶ道が要るので、まだ出さない)
  - 仮引数を持つ関数の定義と、その飽和した呼び出し(AAPCS64: 引数 x0〜x7、返値 x0)
  - トップレベルの式(`_.main` に入る。最後の式の値が x0 で返る)
  - 値が字面の名前(`a : 5`)
  - 行の並び(`条件 : 値` の行と最後の既定の行)。条件は比較 `< <= > >= = !=`(連なった `a < b < c` も。前から順に調べ、外れたら後ろは評価しない)
  - 再帰。自分への末尾呼び出しは、仮引数のスロットを上書きして先頭へ飛ぶ(呼びが積み上がらない)

出せないものは黙って落とさず、AsmError で名指しする(pass4.js と同じ線引き)。

【pass4.js の約束に従った所】
  - 式の途中の値は、フレームのスロット(x29 相対)に置く。`bl` が x0〜x7・x9〜x15 を壊すので、
    レジスタは「読んで・演算して・書く」あいだだけ使い、呼び出しを跨がない。
  - フレームは `stp x29, x30, [sp, #-N]!` / `mov x29, sp` と `ldp x29, x30, [sp], #N`。大きさは 16 + スロット数を 16 に切り上げた数。
  - 即値の組み立ては emitImm と同じ(`mov` / `movz`+`movk` / `movn`+`movk`)。
  - 整数の + - * の検査は integer_overflow.md §1.1 の表のとおり(`adds`/`subs` + `ccmp` + `b.vs`、`mul`/`smulh` + `cmp` + `ccmp` + `b.vs`)。

【この実装だけの選択(設計者の資料に無い所)】
  - 罠の行き先 `.Ltrap`(`wfi` を繰り返す)。
  - 覗き穴の最適化(slotsToRegisters など)はしない。出した命令列がそのまま読める形にしてある。
  - `target="linux"` の起動部 `_start` と整数の印字(結果を 1 行出して exit する)。設計者のターゲット(aarch64_rpi など)は
    ベアメタルで、その起動部(qemu/start.s)は資料に無い。単体の実行ファイルにするための足場である。
"""
import re

from sign_interp import Char, WInt      # 文字(`\\a`)は str の部分クラス。素の str が文字列

INT_MAX = (1 << 63) - 1
ARG_REGS = ["x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7"]
FRAME_MARK = "@@FRAME@@"
NICHE_BITS = 0x8000000000000000       # Int の `__`(target_info.js の UNIT_NICHE_ASM。INT64_MIN は Int の値でない)


NEON = [True]       # Float / Vector の算術の関数を NEON 命令で出す(sign_neon.py)。--no-neon で切る(切ると Float は断る)
SCALAR = [True]     # レコードの分解(sign_fuse.scalarize_records)。--no-scalar で切る
HOIST = [True]      # ループ不変式(sign_fuse.lazy_invariants)。--no-hoist で切る
SHARE = [True]      # 枝をまたぐ共通部分式(sign_fuse.share_exprs)。--no-share で切る
FUSE = [True]       # 融合変換(sign_fuse.py)。--no-fuse で切る
LINT = [True]       # 生成した asm の置き場の寿命の検査(sign_lint.py)。--no-lint で切る。違反は警告にとどめ、生成は止めない
LAST_LINT = []      # 直近の generate の違反の一覧
PEEP = [True]       # ピープホール最適化(sign_peep.py)。--no-peephole で切る

class AsmError(Exception):
    """出せない形(名指しで断る)。"""

class StrictRefusal(AsmError):
    """--strict: コンパイラ(既定の読み)と strict の読みの答えが分かれうる形を、出さずに断る(strict_divergences の続き。コード生成の終わりで、証明器・解析を使って精密に調べた断り)"""



_REGLIKE = r"(?i)[xwbhsdqvz][0-9]{1,2}|sp|wsp|lr|fp|xzr|wzr|pc|nzcv|p[0-9]{1,2}"
def symbol_of(name):
    """アセンブラの名前に使える綴りにする。Sign の識別子は日本語なども書けるので、読めない字は 16 進にする。
    一対一(単射): ふつうの名前はそのまま。レジスタと同じ綴り・`sn_` や `_u` で始まる名前・`__sp`(投機の複製の印)で終わる名前は `sn_` を前に付け、
    読めない字を含む名前は `_u…`(字は 16 進。`_` も `_5f_` と書くので読み戻せる)。どれも像の始まりが違う(そのまま = `sn_`・`_u` 以外、`sn_` = 付けた物、`_u` = 符号化)ので、別の名前は別の綴りになる。"""
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name):
        if re.fullmatch(_REGLIKE, name) or name.startswith(("sn_", "_u")) or name.endswith("__sp"): return "sn_" + name
        return name
    return "_u" + "".join(c if re.fullmatch(r"[A-Za-z0-9]", c) else "_%x_" % ord(c) for c in name)


def emit_imm(out, reg, value, comment=None):
    """pass4.js の emitImm と同じ組み立て。"""
    u = value & ((1 << 64) - 1)
    def chunks(fill): return [(s, (u >> s) & 0xFFFF) for s in range(0, 64, 16) if ((u >> s) & 0xFFFF) != fill]
    zeros, ones = chunks(0), chunks(0xFFFF)
    lsl = lambda s: "" if s == 0 else ", lsl #%d" % s
    c = ("  // " + comment) if comment else ""
    if u <= 0xFFFF:
        out.append("\tmov %s, #%d%s" % (reg, u, c)); return
    if len(ones) < len(zeros):
        if not ones:
            out.append("\tmovn %s, #0%s" % (reg, c)); return
        s0, c0 = ones[0]
        out.append("\tmovn %s, #0x%x%s%s" % (reg, 0xFFFF ^ c0, lsl(s0), c))
        for s, cc in ones[1:]: out.append("\tmovk %s, #0x%x%s" % (reg, cc, lsl(s)))
        return
    s0, c0 = zeros[0]
    out.append("\tmovz %s, #0x%x%s%s" % (reg, c0, lsl(s0), c))
    for s, cc in zeros[1:]: out.append("\tmovk %s, #0x%x%s" % (reg, cc, lsl(s)))


def int_literal(n):
    """字面の値を取り出す。十進の整数だけ。値域の外はコンパイルエラー(integer_overflow.md §1.1 末)。"""
    v = n[1]
    if isinstance(v, bool) or not isinstance(v, int):
        raise AsmError("整数でない字面(%r)はまだ出せません" % (v,))
    if v > INT_MAX or v < -INT_MAX:
        raise AsmError("字面 %d は Int の値域 -%d 〜 %d の外です(コンパイルエラー。integer_overflow.md §1.1)" % (v, INT_MAX, INT_MAX))
    return v


WIDTH = {"I": 1, "C": 1, "L": 2, "S": 2, "N": 2, "R": 3}   # 仮引数・返値が使うレジスタ(とスロット)の本数。R = 規則 {start, step, end}(値渡し、メモリ上に無い。stack_abi.md §4.6)
CW = 1                  # メモリ上の Char 1 個の幅(byte): ascii = 1、utf32 = 4(option.ms の charset。option_ms_schema.md §4.2)
def csh(): return 2 if CW == 4 else 0
def char_ok(o):
    """符号位置 o が現在の charset の域(U+0001 から上限まで。utf32 はサロゲートを除く)に入るか。"""
    if o == 0: return False
    return o <= 127 if CW == 1 else (o <= 0x10FFFF and not 0xD800 <= o <= 0xDFFF)
def char_msg():
    return ("文字は ASCII(0 を除く)だけ出せます(仕様: charset が既定の ascii のとき U+0080 以上はコンパイルエラー — option_ms_schema.md §4.2。utf32 にするには --charset=utf32)" if CW == 1
            else "文字は U+0001〜U+10FFFF(サロゲート U+D800〜U+DFFF を除く)だけ出せます")
WIDE = ("L", "S", "N")      # {ptr, len} の 2 本で運ぶ種類: L = Int のリスト、S = 文字列(ASCII の 1 バイト)、N = リストのリスト(要素は 16 バイトの記述子 {ptr, len}。list_model.md)


MIXED = [False]        # 混ざる入れ子がある(印字の helper が ptr の bit0 を見る)


def expand_aliases(nodes):
    """別名の展開と、算術の節(`[+] 2 3`)の書き直し(作るのは、仕様と処理系の答えが決まっている形だけ)。
    - 別名: 最上位の `p : inc`(関数・別名・節の名前をそのまま右辺に置く定義)は同じ関数なので、`p` の使用を右辺へ置き換えて、定義を消す(`add : [+]` も同じ)。名前が他で束縛されない・式が 1 つ以上ある・
      右辺の名前も他で束縛されないときだけ。
    - 節: `[+] a b c` → `a + b + c`(左から畳む)、`[- 2] x` → `x - 2`、`[2 -] x` → `2 - x`。演算子は `+ - * / %`、`[op]` の畳みは実引数 2 個以上、右・左の節は実引数ちょうど 1 個。
      それ以外(`[>] 3 2`・`[+ 2] 3 4` の写し・実引数 1 個の畳み)は、今までどおり断る。実引数が器・文字列のときは、`+` 等の側で断る。"""
    top_defs = {n[1]: n for n in nodes if n[0] == "def"}
    bound = {}
    def binders(t):
        if isinstance(t, tuple):
            if t and t[0] == "name" and len(t) > 1 and isinstance(t[1], str): bound[t[1]] = bound.get(t[1], 0) + 1
            if t and t[0] == "def" and len(t) > 1 and isinstance(t[1], str): bound[t[1]] = bound.get(t[1], 0) + 1
            for x in t: binders(x)
        elif isinstance(t, list):
            for x in t: binders(x)
    for n in nodes: binders(n)
    alias = {}
    for name, n in top_defs.items():
        rhs = n[2]
        if len(n) > 3 and any(x for x in n[3:]): continue                       # 注釈・修飾つきの定義は触らない
        if bound.get(name, 0) != 1: continue
        if rhs[0] == "id" and rhs[1] in top_defs and rhs[1] != name and bound.get(rhs[1], 0) == 1: alias[name] = rhs
        elif rhs[0] == "sec" and rhs[1] in ("fold", "left", "right") and rhs[2] in ("+", "-", "*", "/", "%", "<", "<=", ">", ">=", "=", "!="): alias[name] = rhs
    if alias:
        if all(n[0] == "def" for n in nodes): alias = {}                      # 式の無いファイルは最後の定義の値を印字する(別名を消すと変わる)
        # 文字列として現れる名前(輸出など)があれば触らない
        def strays(t, nm):
            c = 0
            if isinstance(t, tuple):
                if t[:1] in (("id",), ("name",), ("def",)) and len(t) > 1 and t[1] == nm: c += 0
                else: c += sum(1 for x in t if x == nm)
                for x in t:
                    if isinstance(x, (tuple, list)): c += strays(x, nm)
            elif isinstance(t, list):
                for x in t:
                    if x == nm: c += 1
                    elif isinstance(x, (tuple, list)): c += strays(x, nm)
            return c
        for nm in list(alias):
            if any(strays(n, nm) for n in nodes): del alias[nm]
    def resolve(nm):
        seen = set()
        while nm in alias and nm not in seen:
            seen.add(nm); t = alias[nm]
            if t[0] == "id": nm = t[1]
            else: return t
        return ("id", nm) if nm not in seen or nm not in alias else None
    final = {}
    for nm in alias:
        r = resolve(nm)
        if r is not None and not (r[0] == "id" and r[1] in alias): final[nm] = r
    secops = ("+", "-", "*", "/", "%", "<", "<=", ">", ">=", "=", "!=")
    OPNAME = {"+": "add", "-": "sub", "*": "mul", "/": "div", "%": "mod", "<": "lt", "<=": "le", ">": "gt", ">=": "ge", "=": "eq", "!=": "ne"}
    used = set(); used_r = set()
    def mk(op, l, r): return ("cmp", [l, r], [op]) if op in ("<", "<=", ">", ">=", "=", "!=") else ("bin", op, l, r)
    def range_lits(a):
        """`[a ~ b]`(a・b が整数の字面で、刻みなし)なら (a, b)。それ以外は None。"""
        while a[0] == "block": a = a[1]
        if not (a[0] == "bin" and a[1] == "~"): return None
        def li(t):
            while t[0] == "block": t = t[1]
            neg = False
            if t[0] == "neg": neg = True; t = t[1]
            while t[0] == "block": t = t[1]
            if t[0] == "lit" and isinstance(t[1], int) and not isinstance(t[1], bool) and (len(t) < 3 or t[2] != "Address") \
                    and abs(t[1]) < (1 << 60): return -t[1] if neg else t[1]
            return None
        x, y = li(a[2]), li(a[3])
        return None if x is None or y is None else (x, y)
    def sec_apply(sec, args):
        kind, op, opd = sec[1], sec[2], sec[3]
        if op not in secops or (len(sec) > 4 and sec[4]): return None
        if kind == "fold" and opd is None:
            if len(args) == 1:
                if args[0][0] == "lit" and isinstance(args[0][1], int): return args[0]
                # 範囲の字面 `[a ~ b]`(整数の字面の両端)の畳みは、表に広げず、数を進める輪にする(stack_abi.md の範囲式)。
                # 昇りは `_rfoldU_<op>`、降りは `_rfoldD_<op>`。最初の要素 a を初めの値にして、残りを前から畳む(器の畳みと同じ順)
                rg = range_lits(args[0])
                if rg is not None:
                    a, b = rg
                    used_r.add(op)
                    if a <= b: return ("seq", [("id", "_rfoldU_" + OPNAME[op]), ("lit", a + 1), ("lit", b), ("lit", a)])
                    return ("seq", [("id", "_rfoldD_" + OPNAME[op]), ("lit", a - 1), ("lit", b), ("lit", a)])
                # 器 1 個の畳みは中身を畳む(`[+] xs` は合計、空は `__`)。補助の関数 `_foldS_<op>`(添字で回す末尾再帰)を呼ぶ
                used.add(op); return ("seq", [("id", "_foldS_" + OPNAME[op]), args[0]])
            e = args[0]
            for x in args[1:]: e = mk(op, e, x)
            return e
        if kind == "right" and opd is not None: return mk(op, args[0], opd)
        if kind == "left" and opd is not None: return mk(op, opd, args[0])
        return None
    def rw(t):
        if isinstance(t, tuple):
            if t[:1] == ("id",) and len(t) == 2 and t[1] in final: return final[t[1]]
            if t and t[0] == "seq" and len(t) > 1 and isinstance(t[1], list) and len(t[1]) >= 2:
                items = [rw(x) for x in t[1]]
                if items[0][:1] == ("sec",):
                    r = sec_apply(items[0], items[1:])
                    if r is not None:
                        k = items[0][1]                       # 右・左の節は先頭の実引数だけに掛かる。残りは並べる
                        rest = items[2:] if k in ("right", "left") else []
                        return r if not rest else ("seq", [r] + rest) + tuple(rw(y) for y in t[2:])
                return ("seq", items) + tuple(rw(y) for y in t[2:])
            return tuple(rw(x) for x in t)
        if isinstance(t, list): return [rw(x) for x in t]
        return t
    out = []
    for n in nodes:
        if n[0] == "def" and n[1] in final: continue
        out.append(rw(n))
    if used or used_r:
        import sign_interp
        helpers = []
        for op in sorted(used_r):
            nm = OPNAME[op]
            if bound.get("_rfoldU_" + nm) or bound.get("_rfoldD_" + nm): raise AsmError("補助の名前 `_rfoldU_%s` が使われています" % nm)
            src = ("_rfoldU_%s : i hi acc ?\n\ti > hi : acc\n\t_rfoldU_%s (i + 1) hi (acc %s i)\n" % (nm, nm, op)
                   + "_rfoldD_%s : i lo acc ?\n\ti < lo : acc\n\t_rfoldD_%s (i - 1) lo (acc %s i)\n" % (nm, nm, op))
            helpers += sign_interp.parse_source(src)
        for op in sorted(used):
            nm = OPNAME[op]
            if bound.get("_foldS_" + nm) or bound.get("_fold_" + nm): raise AsmError("補助の名前 `_foldS_%s` が使われています" % nm)
            src = ("_fold_%s : xs i acc ?\n\ti >= ||xs|| : acc\n\t_fold_%s xs (i + 1) (acc %s (xs ' i))\n" % (nm, nm, op)
                   + "_foldS_%s : xs ?\n\t||xs|| = 0 : __\n\t_fold_%s xs 1 (xs ' 0)\n" % (nm, nm))
            helpers += sign_interp.parse_source(src)
        out = helpers + out
    return out


def expand_mixed_spreads(nodes):
    """字面の名前の混ざる入れ子 `m : [1 [2 3]]` の展開 `m~` を、要素を並べた並びに書き直す(`0 m~` → `0 1 (2 3)`、`g m~` → `g 1 (2 3)`)。
    処理系の読み: 入れ子の展開は、要素がリストだけなら平らに(`0 m~` → `[0, 1, 2, 3, 4]`)、スカラーが混ざれば要素をそのまま(`[0, 1, [2, 3]]`)並べる。
    どちらになるかは入れ子の中身で決まるので、静的に分かる字面の名前(要素が Int の字面とその括りだけ・名前が他で束縛されない)に限る。仮引数の入れ子は、実行時の中身で
    結果の種類が変わるため、ここでは書き直さず、後で名指しで断る。"""
    def lit_int(t):
        while t[0] == "block": t = t[1]
        if t[0] == "lit" and isinstance(t[1], int) and not isinstance(t[1], bool): return t
        if t[0] == "neg" and t[1][0] == "lit" and isinstance(t[1][1], int) and not isinstance(t[1][1], bool): return t
        return None
    def elems(v):
        while v[0] == "block": v = v[1]
        if v[0] not in ("seq", "prod") or len(v[1]) < 2: return None
        out, sc = [], 0
        for it in v[1]:
            while it[0] == "block": it = it[1]
            li = lit_int(it)
            if li is not None: out.append(li); sc += 1; continue
            if it[0] in ("seq", "prod") and len(it[1]) >= 2 and all(lit_int(x) is not None for x in it[1]):
                out.append(("block", ("seq", [lit_int(x) for x in it[1]]))); continue
            return None
        return out if 0 < sc < len(out) else None            # スカラーが混ざる字面だけ(全部リストの入れ子は今までの道)
    cand = {}
    for n in nodes:
        if n[0] == "def" and len(n) > 2 and not (n[2][0] == "lam"):
            e = elems(n[2])
            if e is not None: cand[n[1]] = e
    if not cand: return nodes
    uses = set()
    def scan(t, top=False):
        if isinstance(t, tuple):
            if t and t[0] == "post" and len(t) > 2 and t[1] == "~" and isinstance(t[2], tuple) and t[2][:1] == ("id",) and t[2][1] in cand: uses.add(t[2][1])
            for x in t: scan(x)
        elif isinstance(t, list):
            for x in t: scan(x)
    scan(nodes)
    if not uses: return nodes
    bound = {}
    def binders(t, top):
        if isinstance(t, tuple):
            if t and t[0] == "name" and len(t) > 1 and isinstance(t[1], str): bound[t[1]] = bound.get(t[1], 0) + 1
            if t and t[0] == "def" and not top and len(t) > 1 and isinstance(t[1], str): bound[t[1]] = bound.get(t[1], 0) + 1
            for x in t: binders(x, False)
        elif isinstance(t, list):
            for x in t: binders(x, False)
    for n in nodes:
        if n[0] == "def": bound[n[1]] = bound.get(n[1], 0) + 1
        for x in n[2:]: binders(x, False)
        if n[0] != "def": binders(n, False)
    ok = {m for m in uses if bound.get(m, 0) == 1}
    if not ok: return nodes
    def rw(t):
        if isinstance(t, tuple):
            if t and t[0] in ("seq", "prod") and len(t) > 1 and isinstance(t[1], list):
                items = []
                for x in t[1]:
                    if isinstance(x, tuple) and x[:2] == ("post", "~") and len(x) > 2 and x[2][:1] == ("id",) and x[2][1] in ok: items += [rw(e) for e in cand[x[2][1]]]
                    else: items.append(rw(x))
                return (t[0], items) + tuple(rw(y) for y in t[2:])
            return tuple(rw(x) for x in t)
        if isinstance(t, list): return [rw(x) for x in t]
        return t
    return [rw(n) for n in nodes]


class Sc(tuple):
    """入れ子の字面のスカラー要素(長さ 1 の 1 要素の並び)。記述子では ptr の bit0 を立てて、リストの要素 1 個と区別する(DESIGN_NESTED.md §4)。"""
    __slots__ = ()


class Str(tuple):
    """入れ子の字面の文字列の要素(文字コードの並び)。記述子では ptr の bit1 を立てる(文字の幅 CW で読む)。"""
    __slots__ = ()


class Nst(list):
    """入れ子の字面の、もう一段の入れ子の要素(要素の並び)。記述子では ptr の bit2 を立てる(ptr は内側の記述子の表、len はその数)。"""


class FnGen:
    """1 つの関数(か `_.main`)の本体を出す。"""

    def __init__(self, prog, name, params, loop=False, force_sret=False, force_nest=False):
        self.prog = prog
        self.name = name
        self.retk = prog.retk.get(name, "I")
        kinds = prog.pkind.get(name) or ["I"] * len(params)
        self.kinds = dict(zip(params, kinds))                 # 仮引数の種類: "I" = Int、"L" = Int のリスト({ptr, len} の 2 本)
        self.slot, self.order, cell = {}, [], 0
        for p in params:
            self.slot[p] = cell; self.order.append((p, cell, self.kinds[p]))
            cell += WIDTH[self.kinds[p]]          # 仮引数 → スロット番号(リストは 2 つ使う)
        self.sret = prog.bound.get(name) is not None or force_sret      # 組み立てて返す(か、そのまま返す)関数は、x8(置き場)と x15(入る個数)をもらう
        if self.sret: self.sdest, self.slim, self.scur = cell, cell + 1, cell + 2; cell += 3
        if self.sret and (self.retk == "N" or force_nest): self.scon = cell; cell += 1      # 入れ子の器: 内容の領域(arena)に書いていく位置
        if name in prog.maskfns: self.mcell = cell; cell += 1                                # 呼ぶ側が x17 に置いた、器の実引数ごとの旗のビット
        self.alloca = 0                                       # `sub sp` で取った置き場の数
        self.pre_alloca = False                               # 入口で作業領域を取ったか(伸びる累積)
        self.entry_pos = None
        self.cse_lazy = []                                    # 入口で `__` にしておくスロットの鍵(ループ不変式)
        self.cse, self.cse_def = {}, set()                    # 共通部分式の鍵 → スロット(reserve_shared が決める)
        self.base = cell                                      # 一時のスロットはその後ろ
        self.depth = 0
        self.top = self.base
        self.lines = []
        self.has_call = False
        self.entry = prog.label() if loop else None      # 自分への末尾呼び出しの飛び先(関数だけ。_.main には無い)

    def reserve_shared(self, body):
        """本体の中の共通部分式の印(sh)ごとに、関数の間ずっと生きるスロットを 1 つ取る(一時のスロットの前)。"""
        keys = []
        def walk(t):
            if isinstance(t, list):
                for x in t: walk(x)
            elif isinstance(t, tuple) and t:
                if t[0] == "block" and len(t) > 3 and t[2] in ("sh", "lazy") and t[3] not in keys and self.prog.kind(t[1], self.kinds) == "I":
                    keys.append(t[3])
                    if t[2] == "lazy": self.cse_lazy.append(t[3])
                for x in t:
                    if isinstance(x, (tuple, list)): walk(x)
        walk(body)
        for kx in keys:
            self.cse[kx] = self.base; self.base += 1
        self.top = self.base

    # ---- スロット ----
    def tmp(self):
        i = self.base + self.depth
        self.depth += 1
        self.top = max(self.top, i + 1)
        return i

    def free(self): self.depth -= 1

    @staticmethod
    def off(i): return 16 + 8 * i

    def emit(self, text, comment=None):
        self.lines.append("\t" + text + (("  // " + comment) if comment else ""))

    # ---- 式 ----
    def late_imm(self, a):
        """実引数 a が整数の字面(アドレスなど印の付く字面・桁の大きい字面を除く)なら、その値。呼びの直前にレジスタへ直に入れてよい物。"""
        t = self.strip(a)
        if t[0] == "lit" and len(t) == 2 and isinstance(t[1], int) and not isinstance(t[1], bool) and abs(t[1]) < (1 << 62):
            return t[1]
        return None

    def mu(self, n):
        """n は `__` になりうるか(Program.maybe)。"""
        return self.prog.maybe(n)

    def niche(self, reg="x13"):
        emit_imm(self.lines, reg, NICHE_BITS, "__")

    def simple(self, n):
        """スロットか即値だけで置ける項(途中の値を預けずに済む)。"""
        if n[0] == "lit": return True
        if n[0] == "neg" and n[1][0] == "lit": return True
        if n[0] == "id": return (n[1] in self.slot and self.kinds[n[1]] == "I") or n[1] in self.prog.consts or n[1] in self.prog.dyn or n[1] == "__"
        if n[0] == "block": return self.simple(n[1])
        return False

    def load(self, n, reg):
        """simple な項を reg へ。"""
        if n[0] == "block": return self.load(n[1], reg)
        if n[0] == "lit": emit_imm(self.lines, reg, int_literal(n)); return
        if n[0] == "neg":
            emit_imm(self.lines, reg, -int_literal(n[1])); return
        if n[0] == "id":
            if n[1] == "__": emit_imm(self.lines, reg, NICHE_BITS, "__"); return
            if n[1] in self.slot:
                self.emit("ldr %s, [x29, #%d]" % (reg, self.off(self.slot[n[1]])), n[1]); return
            if n[1] in self.prog.dyn:
                lb = dyn_label(n[1])
                self.emit("adrp %s, %s" % (reg, lb), "起動で評価した定義 " + n[1]); self.emit("add %s, %s, :lo12:%s" % (reg, reg, lb)); self.emit("ldr %s, [%s]" % (reg, reg)); return
            c = self.prog.consts[n[1]]
            emit_imm(self.lines, reg, NICHE_BITS if c is None else c, n[1]); return
        raise AsmError("内部の誤り: simple でない項")

    def gen(self, n, tail=False):
        """n を評価して x0 に置く。tail は『関数の最後の仕事』(自分への呼びは飛び先に替えられる)。"""
        k = n[0]
        if k == "block":
            if len(n) > 3 and n[2] == "lazy" and n[3] in self.cse:
                # ループ不変式(sign_fuse.lazy_invariants): スロットは入口で `__`。空なら評価して置き、あれば読む(評価の場所は元のまま)
                off = self.off(self.cse[n[3]]); done = self.prog.label()
                self.emit("ldr x0, [x29, #%d]" % off, "ループ不変式: 置いてあれば読む"); self.niche(); self.emit("cmp x0, x13"); self.emit("b.ne %s" % done)
                self.gen(n[1]); self.emit("str x0, [x29, #%d]" % off, "ループ不変式の値を置く(次の回は読む)")
                self.lines.append("%s:" % done); return
            if len(n) > 3 and n[2] in ("sh", "ref") and n[3] in self.cse:
                # 共通部分式(sign_fuse.share_exprs): 最初の評価で値をスロットに置き、あとの出現は読む。置く前に読む形は、元の式を評価する(安全側)
                off = self.off(self.cse[n[3]])
                if n[2] == "sh":
                    self.gen(n[1]); self.emit("str x0, [x29, #%d]" % off, "共通部分式の値を置く(あとの枝が読む)"); self.cse_def.add(n[3]); return
                if n[3] in self.cse_def:
                    self.emit("ldr x0, [x29, #%d]" % off, "共通部分式の値を読む(同じ式を再計算しない)"); return
            return self.gen(n[1], tail)
        if k == "cases":
            if self.prog.kind(n, self.kinds) != "I": raise AsmError("リスト・文字列・文字を値として使う形はまだ出せません(関数の返値と最後の式の印字、引数、要素の取り出しだけ)")
            return self.gen_cases(n, tail)
        if k == "norm": return self.gen_norm(n)
        if self.prog.kind(n, self.kinds) != "I":
            raise AsmError("リスト・文字列・文字を値として使う形(返す・足す・比べる)はまだ出せません。出せるのは要素の取り出し `l ' i`・長さ `||l||`・関数へ渡す・最後の式として印字、だけ")
        if self.simple(n):
            self.load(n, "x0"); return
        if k == "id":
            if n[1] in self.prog.fns:
                raise AsmError("関数 %s を値として使う形(部分適用・関数値)はまだ出せません" % n[1])
            raise AsmError("まだ出せない識別子です(%s)" % n[1])
        if k == "neg":
            self.gen(n[1])
            if self.mu(n[1]):
                done = self.prog.label()
                self.niche(); self.emit("cmp x0, x13"); self.emit("b.eq %s" % done, "-__ は __")
                self.emit("neg x0, x0", "符号反転は溢れない(値域が 0 を挟んで対称)")
                self.lines.append("%s:" % done)
            else:
                self.emit("neg x0, x0", "符号反転は溢れない(値域が 0 を挟んで対称)")
            return
        if k == "input": self.note_cell(n[1])
        if k == "input":                                # `@番地`: 普通のメモリの 64 ビットを読む(operator_table.md の input)
            if self.prog.kind(n[1], self.kinds) != "I": raise AsmError("`@` の番地が Int でない形はまだ出せません")
            self.gen(n[1])
            done = self.prog.label() if self.mu(n[1]) else None
            if done: self.niche(); self.emit("cmp x0, x13"); self.emit("b.eq %s" % done, "番地が __ なら __")
            wd = self.addr_width(n[1])
            rdev = REALDEV[0] and wd not in (1, 2)
            if rdev:
                dn, de = self.prog.label(), self.prog.label()
                emit_imm(self.lines, "x10", 0x9000000); self.emit("cmp x0, x10"); self.emit("b.lo %s" % dn)
                self.emit("mov x1, #%d" % (4 if wd == 4 else 8), "幅"); self.emit("bl _sign_dev_ld", "装置からの読み(実機の中継。sign_realdev.py)"); self.emit("b %s" % de)
                self.lines.append("%s:" % dn)
            if wd in (1, 2, 4): self.emit({1: "ldrb w0, [x0]", 2: "ldrh w0, [x0]", 4: "ldr w0, [x0]"}[wd], "幅 %d byte で読む(ゼロ拡張)" % wd)
            else: self.emit("ldr x0, [x0]", "64 ビットで読む(書かれていない所は、メモリの中身そのまま。処理系は『書かれていない』を __ とするが、実機に区別は無い)")
            if rdev: self.lines.append("%s:" % de)
            if done: self.lines.append("%s:" % done)
            return
        if k == "cmp": return self.gen_cmp(n, None)
        if k == "bin": return self.gen_bin(n)
        if k == "seq": return self.gen_call(n, tail)
        raise AsmError("まだ出せない形です(%s)" % k)

    def addr_width(self, a):
        """番地の項 a の読み書きの幅(byte)。0 = 幅を言っていない(target の語幅 8)。"""
        return self.prog.width_expr(a, self.name)

    def note_cell(self, addr):
        """定数の番地への Int の読み書きを覚える(終わりに、8 バイト未満の間隔の番地の組を information に出す)。"""
        c = self.prog.const_int(addr)
        if c is not None: self.prog.addr_cells.setdefault(c, (self.name, self.addr_width(addr) or 8))

    # ---- 並列(--par。sign_asmpar.py): 両辺が純粋な整数関数の呼び出しの + - * ----
    def par_arg_ok(self, a):
        """仕事に出す呼び出しの実引数・並列にする呼び出しの隣の項に置ける式: sign_asmpar.arg_ok の形に、純粋な整数関数の呼び出し(入れ子)を足した物。親が評価してから渡すので、入れ子は直列でも並列でもよい。"""
        import sign_asmpar
        a = self.strip(a); k = a[0]
        if sign_asmpar.arg_ok(self.prog, a): return True
        if k in ("block", "neg"): return self.par_arg_ok(a[1])
        if k == "bin": return a[1] in sign_asmpar.OPS and self.par_arg_ok(a[2]) and self.par_arg_ok(a[3])
        if k == "seq": return self.par_call(a) is not None
        return False

    def par_call(self, n):
        n = self.strip(n)
        if n[0] != "seq": return None
        items = n[1]; h = items[0]
        el = self.prog.par_elig()
        if h[0] != "id" or h[1] not in el or h[1] in self.slot or len(items) - 1 != el[h[1]]: return None
        import sign_asmpar
        for a, kd in zip(items[1:], self.prog.pkind[h[1]]):
            if kd == "I":
                if not self.par_arg_ok(a) or self.mu(a) or self.prog.kind(a, self.kinds) != "I": return None
            elif kd == "C":
                if not self.par_char_arg(a): return None
            elif not self.par_list_arg(a, kd): return None
        return h[1], items[1:]

    # ---- 投機(--par-spec。sign_asmpar.py): `l | r`・`l & r`・`cond : v` の右・値の呼び出しを、左・条件と並べて先に走らせる ----
    def spec_call(self, n):
        """投機に出せる呼び出し (関数, 実引数) か None: 必ず終わると言える純粋な整数関数で、実引数に呼び出しが無い(親が先に評価しても、答えが要らなければ捨てるだけで、罠も長い計算も増えない)。"""
        import sign_asmpar
        c = self.par_call(n)
        if c is None or c[0] not in self.prog.spec_elig(): return None
        for a, kd in zip(c[1], self.prog.pkind[c[0]]):
            if kd == "I" and not sign_asmpar.arg_ok(self.prog, self.strip(a)): return None
            if kd == "C" and self.has_seq(a): return None
        return c

    def spec_for(self, v, other):
        """v を投機に出す価値があれば (関数, 実引数)。other(先に評価する左・条件)が呼び出しを含む(重そう)ときだけ。"""
        if PAR[0] is None or not SPEC[0] or getattr(self.prog, "target", "bare") != "linux" or not self.has_seq(other): return None
        return self.spec_call(v)

    def spec_begin(self, f, al):
        """実引数を評価して、池の入れ物に置き、仕事に出す。入れ物の番地(出せなかったら 0)をフレームの sb に置く。tmp を (sb, 退避, 実引数…) の順に取る。
        実引数の評価の中の罠(溢れ)は、投機を諦めて直列へ(親が先に評価しても罠を増やさない)。"""
        import re
        em = self.emit; off = self.off
        self.prog.spec_used.add(f)
        nw = self.par_nwords(f)
        sb = self.tmp(); tv = self.tmp(); tmps = [self.tmp() for _ in range(nw)]
        go = self.prog.label()
        em("str xzr, [x29, #%d]" % off(sb), "投機: まだ出していない")
        a0 = len(self.lines)
        self.par_put_args(f, al, tmps, first=0)
        for i in range(a0, len(self.lines)): self.lines[i] = re.sub(r"\.Ltrap(_part)?\b", go, self.lines[i])
        em("bl _sign_spec_alloc", "池から入れ物をもらう(投機の中・空きの労働者が無ければ 0)"); em("str x0, [x29, #%d]" % off(sb)); em("cbz x0, %s" % go)
        em("str xzr, [x0]"); em("adr x12, _sign_sw_%s" % symbol_of(f)); em("str x12, [x0, #8]", "投機の包み")
        em("mrs x9, tpidr_el0"); em("ldr x10, [x9, #8]"); em("add x10, x10, #1"); em("str x10, [x0, #24]", "子の段")
        for i in range(nw): em("ldr x12, [x29, #%d]" % off(tmps[i])); em("str x12, [x0, #%d]" % (40 + 8 * i))
        em("mov x1, #0"); em("bl _sign_par_submit", "投機に出す(入れなければ状態 0 のまま。要るときに合流が自分で計算する)")
        self.lines.append("%s:" % go)
        return sb, tv, nw + 2

    def spec_join(self, sb, ser, done):
        """答えが要る: 入れ物があれば合流して x0 に(失敗の印が立っていれば ser = 直列で計算し直す)。入れ物が無ければ ser。"""
        em = self.emit
        em("ldr x9, [x29, #%d]" % self.off(sb)); em("cbz x9, %s" % ser); em("mov x0, x9"); em("bl _sign_spec_join", "投機の答え(罠・巻き戻しなら x1=1)")
        em("cbz x1, %s" % done)

    def spec_cancel(self, sb, tv, done):
        """答えは要らない(x0 は預けて守る)。出していれば捨てる。"""
        em = self.emit
        em("ldr x9, [x29, #%d]" % self.off(sb)); em("cbz x9, %s" % done)
        em("str x0, [x29, #%d]" % self.off(tv)); em("mov x0, x9"); em("bl _sign_spec_cancel", "投機を捨てる(行列にあれば外す・走行中なら労働者が空きに戻す)")
        em("ldr x0, [x29, #%d]" % self.off(tv))

    def par_char_arg(self, a):
        """仕事に出す呼び出しの Char の実引数: 自分の Char の仮引数・文字の定数の名前・文字の字面、または文字列の要素 `s ' i`(s は文字列の仮引数か字面の名前、
        i は副作用の無い Int の式)で、`__` にならない物。呼ぶ側が先に評価して値(文字コード)だけ渡す。"""
        a = self.strip(a)
        if self.mu(a): return False
        if a[0] == "lit": return isinstance(a[1], Char) and len(a) == 2
        if a[0] == "id": return (a[1] in self.slot and self.kinds.get(a[1]) == "C") or a[1] in self.prog.chars
        if a[0] == "bin" and a[1] == "'":
            l = self.strip(a[2])
            if l[0] != "id" or self.prog.kind(a, self.kinds) != "C": return False
            if self.prog.tail_of(a) is not None or self.prog.slice_of(a) is not None: return False
            return self.par_arg_ok(a[3]) and self.prog.kind(a[3], self.kinds) == "I"
        return False

    def par_list_arg(self, a, kd):
        """仕事に出す呼び出しの、リスト(kd = "L")・文字列("S")の実引数: 自分の器の仮引数か、字面の名前だけ(`__` にならず、呼ぶ前に作らずに見せるだけで渡せる)。"""
        a = self.strip(a)
        if a[0] != "id": return False
        if a[1] in self.slot: return self.kinds.get(a[1]) == kd
        return (kd == "L" and a[1] in self.prog.lists) or (kd == "S" and a[1] in self.prog.strs) or (kd == "N" and a[1] in self.prog.nests)

    def par_put_args(self, f, al, blk, first=5):
        """仕事の入れ物 blk の実引数の欄(first 語目から)に、実引数を置く。Int は 1 語、リスト・文字列は {番地, 長さ} の 2 語。"""
        em = self.emit; off = self.off; w = first
        for a, kd in zip(al, self.prog.pkind[f]):
            if kd in ("I", "C"):
                if kd == "I": self.gen(a)
                else: self.gen_char_value(a)
                em("str x0, [x29, #%d]" % off(blk[w])); w += 1
            else:
                self.load_list(a, "x11", "x12"); em("str x11, [x29, #%d]" % off(blk[w]), "器の番地"); em("str x12, [x29, #%d]" % off(blk[w + 1]), "器の長さ"); w += 2

    def par_nwords(self, f):
        import sign_asmpar
        return sign_asmpar.nwords(self.prog.pkind[f])

    def has_seq(self, x):
        if isinstance(x, (tuple, list)):
            if isinstance(x, tuple) and x and x[0] == "seq": return True
            return any(self.has_seq(y) for y in x)
        return False

    def par_args(self, args, pk, accs):
        """実引数のうち純粋な整数関数の呼び出しが 2 つ以上あり、残りの実引数が副作用の無い Int の式なら、その呼び出しの位置の並び(評価の順は答えに効かない)。"""
        if PAR[0] is None or getattr(self.prog, "target", "bare") != "linux" or accs or any(k != "I" for k in pk): return []
        import sign_asmpar
        idx = []
        for i, a in enumerate(args):
            if self.par_call(a) is not None: idx.append(i)
            elif not self.par_arg_ok(a) or self.mu(a): return []
        return idx if len(idx) >= 2 else []

    def par_light_pre(self, site, Ls):
        """仕事に出す前の軽さの関門。既定: 位置の数え(3 回続けて軽ければ以後ずっと直列)。--par-relight: このスレッドで軽かった枠(TLS+0 の x29)と同じか深い枠なら直列。見送りは TLS+24 に数え、2^20 回ごとに覚えを消して試し直す。x9 = TLS、x10 は壊さない。"""
        import sign_asmpar
        em = self.emit
        if not sign_asmpar.RELIGHT:
            em("adrp x11, %s" % site); em("add x11, x11, :lo12:%s" % site); em("ldr x12, [x11]"); em("cmp x12, #3"); em("b.hs %s" % Ls); return
        ok = self.prog.label()
        em("ldr x12, [x9]", "軽かった枠の深さ(0 = 覚え無し)"); em("cbz x12, %s" % ok); em("cmp x29, x12"); em("b.hi %s" % ok, "それより浅い枠なら試す")
        em("ldr x13, [x9, #24]"); em("add x13, x13, #1"); em("str x13, [x9, #24]"); em("lsl x14, x13, #44"); em("cbnz x14, %s" % Ls, "深い枠は直列(下 20 ビットが 0 になる回だけ先へ)")
        em("str xzr, [x9]", "2^20 回見送ったら覚えを消す"); em("b %s" % Ls)
        self.lines.append("%s:" % ok)

    def par_light_post(self, hv, af):
        """合流のあと: x9 = かかった時計、x11 = 位置の数えの番地。既定は数えを増やす/戻す。--par-relight は、軽ければこの枠の x29 を(今の覚えより浅ければ)覚える。"""
        import sign_asmpar
        em = self.emit
        self.cmp_light(); em("b.hs %s" % hv)
        if not sign_asmpar.RELIGHT:
            em("ldr x12, [x11]"); em("add x12, x12, #1"); em("str x12, [x11]", "軽かった回を数える"); em("b %s" % af)
            self.lines.append("%s:" % hv); em("str xzr, [x11]", "重かったら数え直し"); return
        em("mrs x12, tpidr_el0"); em("ldr x13, [x12]"); em("cmp x29, x13"); em("b.ls %s" % af); em("str x29, [x12]", "軽かった枠の深さを覚える")
        self.lines.append("%s:" % hv)

    def cmp_light(self):
        """x9(左の仕事にかかった時計)と、軽さの境 LIGHT(--par-light=N。4095 を超えれば x15 に作って比べる)を比べる。"""
        L = sign_asmpar_light()
        if L <= 4095: self.emit("cmp x9, #%d" % L)
        else:
            self.emit("movz x15, #%d" % (L & 0xFFFF))
            if L >> 16: self.emit("movk x15, #%d, lsl #16" % ((L >> 16) & 0xFFFF))
            self.emit("cmp x9, x15")

    def par_pair(self, op, l, r):
        """('l', 左の呼び出し) か ('r', 右の呼び出し)。両方が呼び出しなら左を仕事に出す。片方だけなら、もう片方が呼び出しを含む(重そうな)ときだけ。"""
        if PAR[0] is None or op not in ("+", "-", "*", "/", "%", "&&", "||", ";;", "<<", ">>") or getattr(self.prog, "target", "bare") != "linux": return None
        a = self.par_call(l)
        if a is not None:
            if self.par_call(r) is None and not self.has_seq(r): return None
            return ("l", a)
        b = self.par_call(r)
        if b is not None and self.has_seq(l): return ("r", b)
        return None

    def par_emit(self, pc_, l, r, t):
        """左を(空いていれば)別のスレッドへ、右を自分で。左の答えを t に、右の答えを x0 に置く。直列のコードも同じ式に残し、実行時に選ぶ。"""
        import sign_asmpar
        side, (fl, al) = pc_
        sub_n, par_n = (l, r) if side == "l" else (r, l)         # 仕事に出す呼び出し / 自分で評価する式
        P = PAR[0]; K = sign_asmpar.levels(P)
        site = "_sign_ps%d" % self.prog.par_nsites; self.prog.par_nsites += 1
        self.prog.par_used.add(fl)
        Ls, Ld = self.prog.label(), self.prog.label()
        em = self.emit; off = self.off
        em("mrs x9, tpidr_el0", "並列の候補: 労働者に空きが無いか、軽いと分かった所なら直列"); em("ldr x10, [x9, #8]"); em("adrp x11, _sign_par_load"); em("add x11, x11, :lo12:_sign_par_load"); em("ldr x12, [x11]"); em("cmp x12, #%d" % (P - 1)); em("b.hs %s" % Ls, "空きの労働者が無ければ直列")
        self.par_light_pre(site, Ls)
        blk = [self.tmp() for _ in range(5 + self.par_nwords(fl))]
        em("str xzr, [x29, #%d]" % off(blk[0]), "状態 0"); em("adr x12, _sign_pw_%s" % symbol_of(fl)); em("str x12, [x29, #%d]" % off(blk[1]), "包み")
        em("add x12, x10, #1"); em("str x12, [x29, #%d]" % off(blk[3]), "子の段")
        self.par_put_args(fl, al, blk)
        em("add x0, x29, #%d" % off(blk[0])); em("mov x1, #0"); em("bl _sign_par_submit", "左を仕事に出す(空きが無ければ入れない)")
        em("mrs x9, tpidr_el0"); em("ldr x10, [x9, #8]"); em("add x10, x10, #1"); em("str x10, [x9, #8]", "段を 1 つ上げて右を計算")
        self.gen(par_n)
        tr = self.tmp(); em("str x0, [x29, #%d]" % off(tr), "自分で評価した式の答え"); jr = self.tmp()
        em("mrs x9, tpidr_el0"); em("ldr x10, [x9, #8]"); em("sub x10, x10, #1"); em("str x10, [x9, #8]")
        em("add x0, x29, #%d" % off(blk[0])); em("bl _sign_par_join", "仕事の答え(奪うか待つ)"); em("str x0, [x29, #%d]" % off(jr))
        em("ldr x9, [x29, #%d]" % off(blk[4]), "左にかかった時計"); em("adrp x11, %s" % site); em("add x11, x11, :lo12:%s" % site)
        hv, af = self.prog.label(), self.prog.label()
        self.par_light_post(hv, af)
        self.lines.append("%s:" % af)
        a_, b_ = (jr, tr) if side == "l" else (tr, jr)           # 左の値は t へ、右の値は x0 へ
        em("ldr x9, [x29, #%d]" % off(a_)); em("str x9, [x29, #%d]" % off(t)); em("ldr x0, [x29, #%d]" % off(b_)); em("b %s" % Ld)
        self.free(); self.free(); [self.free() for _ in blk]
        self.lines.append("%s:" % Ls)
        self.gen(l); em("str x0, [x29, #%d]" % off(t), "途中の値はフレームへ(直列)"); self.gen(r)
        self.lines.append("%s:" % Ld)

    def par_leaf(self, x):
        """連なりの葉: 純粋な整数関数の呼び出しなら (関数, 実引数)、呼び出しを含まない純粋な Int の式(定数・名前・+ - *)なら None(自分で評価する)、それ以外は False。"""
        c = self.par_call(x)
        if c is not None: return c
        import sign_asmpar
        x = self.strip(x)
        if sign_asmpar.arg_ok(self.prog, x) and not self.mu(x) and self.prog.kind(x, self.kinds) == "I": return None
        return False

    def par_chain(self, n):
        """左へ入れ子の連なり `((a op b) op c) op d` の全部の葉が純粋な整数関数の呼び出し(3 つ以上)なら、(葉の列, 各段の項, 各段の演算)。"""
        if PAR[0] is None or getattr(self.prog, "target", "bare") != "linux": return None
        ops, subs, leaves, cur = [], [], [], n
        while True:
            cur = self.strip(cur)
            if cur[0] == "bin" and cur[1] in ("+", "-", "*", "/", "%", "&&", "||", ";;", "<<", ">>"):
                c = self.par_leaf(cur[3])
                if c is False: return None
                ops.append(cur[1]); subs.append(cur); leaves.append((cur[3], c)); cur = cur[2]
            else:
                c = self.par_leaf(cur)
                if c is False: return None
                leaves.append((cur, c)); break
        if len(leaves) < 3 or sum(1 for _, c in leaves if c is not None) < 2: return None
        return leaves[::-1], subs[::-1], ops[::-1]

    def nested_calls(self, n):
        """式 n(足す・引く・かける・割る・負・括りの木)に、純粋な整数関数の呼び出しで、実引数の中にまた関数の呼び出しがあるものが在るか。"""
        y = self.strip(n)
        if PAR[0] is None: return False
        if y[0] == "bin" and y[1] in ("+", "-", "*", "/", "%", "<<", ">>", "||", ";;", "&&"): return self.nested_calls(y[2]) or self.nested_calls(y[3])
        if y[0] == "neg": return self.nested_calls(y[1])
        if y[0] == "seq" and y[1] and y[1][0][0] == "id" and y[1][0][1] in self.prog.par_elig():
            return any(self.has_seq(a) for a in y[1][1:])
        return False

    def par_hoist(self, n):
        """式の木のどこにあっても(足す・引く・かける・割る・負・括りの中。`|` `&` は右を要るときにだけ評価するので入らない)、
        互いに独立な純粋な整数関数の呼び出しが 2 つ以上あれば、全部を先に並列で評価して名前(スロット)に置き、式はその名前で評価する。
        呼び出しの答えは `__` にならない物だけ(式の評価の途中の `__` を見ない)。出せたら True。"""
        if PAR[0] is None or getattr(self.prog, "target", "bare") != "linux": return False
        pl = self.hoist_plan([n])
        if pl is None: return False
        names, vals = self.hoist_exec(pl[0]); rebuilt = pl[1][0]
        self.gen(rebuilt)
        for nm in names: del self.slot[nm]; del self.kinds[nm]
        for _ in vals: self.free()
        return True

    def par_run_leaves(self, leaves):
        """k 個の純粋な呼び出し(葉)の答えを、フレームの k 個のスロット(返り値)へ。最後を除く全部を仕事に出し、最後を自分で計算し、順に待つ(直列のコードも残し、実行時に選ぶ)。
        スロットは呼び側が free する。連なりの畳み込みと、実引数の呼び出しどうし(`f (g x) (h y)`)が使う。"""
        import sign_asmpar
        P = PAR[0]; K = sign_asmpar.levels(P); k = len(leaves)
        site = "_sign_ps%d" % self.prog.par_nsites; self.prog.par_nsites += 1
        Ls, Ld = self.prog.label(), self.prog.label()
        em = self.emit; off = self.off
        vals = [self.tmp() for _ in range(k)]
        cidx = [i for i, (_, c_) in enumerate(leaves) if c_ is not None]; sub_i = cidx[:-1]        # 仕事に出す葉(呼び出しのうち最後を除く)。残りは自分で評価する
        for i in cidx: self.prog.par_used.add(leaves[i][1][0])
        em("mrs x9, tpidr_el0", "並列の候補(連なり %d 個): 労働者に空きが無いか、軽いと分かった所なら直列" % k); em("ldr x10, [x9, #8]"); em("adrp x11, _sign_par_load"); em("add x11, x11, :lo12:_sign_par_load"); em("ldr x12, [x11]"); em("cmp x12, #%d" % (P - 1)); em("b.hs %s" % Ls, "空きの労働者が無ければ直列")
        self.par_light_pre(site, Ls)
        blks = []
        for i_ in sub_i:
            (fl, al) = leaves[i_][1]
            blk = [self.tmp() for _ in range(5 + self.par_nwords(fl))]; blks.append(blk)
            em("str xzr, [x29, #%d]" % off(blk[0]), "状態 0"); em("adr x12, _sign_pw_%s" % symbol_of(fl)); em("str x12, [x29, #%d]" % off(blk[1]), "包み")
            em("mrs x9, tpidr_el0"); em("ldr x10, [x9, #8]"); em("add x12, x10, #1"); em("str x12, [x29, #%d]" % off(blk[3]), "子の段")
            self.par_put_args(fl, al, blk)
            em("add x0, x29, #%d" % off(blk[0])); em("mov x1, #1"); em("bl _sign_par_submit", "仕事に出す(連なり・実引数の葉。空きが無くても行列に入れる: 先に終わった労働者が次の葉を取る)")
        em("mrs x9, tpidr_el0"); em("ldr x10, [x9, #8]"); em("add x10, x10, #1"); em("str x10, [x9, #8]", "段を 1 つ上げて最後を計算")
        for i_ in range(k):
            if i_ in sub_i: continue
            self.gen(leaves[i_][0]); em("str x0, [x29, #%d]" % off(vals[i_]), "自分で評価する葉(最後の呼び出し・呼び出しでない項)")
        em("mrs x9, tpidr_el0"); em("ldr x10, [x9, #8]"); em("sub x10, x10, #1"); em("str x10, [x9, #8]")
        for blk in blks:                                  # まだ行列に残っている葉を先に全部奪って走らせる(走行中の葉を待つ前に。待っている間に空いた労働者が残りを取れる)
            em("add x0, x29, #%d" % off(blk[0])); em("bl _sign_par_steal", "行列に残っていれば奪って走らせる(待たない)")
        for i, blk in zip(sub_i, blks):
            em("add x0, x29, #%d" % off(blk[0])); em("bl _sign_par_join", "答え(奪うか待つ)"); em("str x0, [x29, #%d]" % off(vals[i]))
        em("ldr x9, [x29, #%d]" % off(blks[0][4]), "かかった時計の最大")
        for blk in blks[1:]:
            em("ldr x14, [x29, #%d]" % off(blk[4])); em("cmp x14, x9"); em("csel x9, x14, x9, hi")
        em("adrp x11, %s" % site); em("add x11, x11, :lo12:%s" % site)
        hv, af = self.prog.label(), self.prog.label()
        self.par_light_post(hv, af)
        self.lines.append("%s:" % af); em("b %s" % Ld)
        for blk in blks: [self.free() for _ in blk]
        self.lines.append("%s:" % Ls)
        for i, (ln, _) in enumerate(leaves):
            self.gen(ln); em("str x0, [x29, #%d]" % off(vals[i]), "途中の値はフレームへ(直列)")
        self.lines.append("%s:" % Ld)
        return vals

    def par_emit_chain(self, leaves, subs, ops):
        """k 個の葉: 最後を除く全部を仕事に出し、最後を自分で計算し、順に待つ。畳み込みは元のとおり左から、元の演算(溢れの罠・`__`)で。"""
        k = len(leaves); em = self.emit; off = self.off
        vals = self.par_run_leaves(leaves)
        em("ldr x9, [x29, #%d]" % off(vals[0]))
        for j in range(1, k):
            if j > 1: em("mov x9, x0")
            em("ldr x10, [x29, #%d]" % off(vals[j]))
            self.bin_tail(ops[j - 1], (leaves[0][0] if j == 1 else subs[j - 2]), leaves[j][0])
        for _ in vals: self.free()

    def gen_bin(self, n):
        _, op, l, r = n
        if op == "'": return self.gen_index(l, r)
        if op in ("==", "!=="):
            # 数と文字では `=`/`!=` と同じ意味(operator_table.md: 左が零射なら零射、`!==` は非 Unit 側の値)
            return self.gen_cmp(("cmp", [l, r], [op]), None)
        if op in ("|", "&") and self.mu(l) and self.prog.kind(l, self.kinds) == "I" and self.prog.kind(r, self.kinds) == "I":
            sp = self.spec_for(r, l)
            if sp is not None:                          # --par-spec: 右を先に別のスレッドで走らせておく(左が決めれば捨てる。罠・巻き戻しは直列で計算し直す)
                sb, tv, nfree = self.spec_begin(*sp)
                done, ser, canc = self.prog.label(), self.prog.label(), self.prog.label()
                self.gen(l)
                self.niche(); self.emit("cmp x0, x13"); self.emit("b.%s %s" % ("ne" if op == "|" else "eq", canc), "左が答えを決める: 右は要らない" if op == "|" else "左が __ なら __: 右は要らない")
                self.spec_join(sb, ser, done)
                self.lines.append("%s:" % ser); self.gen(r); self.emit("b %s" % done)
                self.lines.append("%s:" % canc); self.spec_cancel(sb, tv, done)
                self.lines.append("%s:" % done)
                for _ in range(nfree): self.free()
                return
        if op == "|":                                   # 左が `__` でなければ左。右は要るときにだけ評価する
            self.gen(l)
            if not self.mu(l): return
            done = self.prog.label()
            self.niche(); self.emit("cmp x0, x13"); self.emit("b.ne %s" % done, "左が __ でなければ左が答え")
            self.gen(r)
            self.lines.append("%s:" % done); return
        if op == "&":                                   # 左が `__` なら `__`、そうでなければ右
            self.gen(l)
            if self.mu(l):
                done = self.prog.label()
                self.niche(); self.emit("cmp x0, x13"); self.emit("b.eq %s" % done, "左が __ なら __")
                self.gen(r)
                self.lines.append("%s:" % done)
            else:
                self.gen(r)
            return
        if op == "#": self.note_cell(l)
        if op == "#":                                   # 書き込み `a # v`(operator_table.md: アドレスにデータを入れ、成功したらアドレスを返す。`0x00 # __` は何もせず番地を返す)
            if self.prog.kind(l, self.kinds) != "I" or self.prog.kind(r, self.kinds) not in ("I", "C"):
                raise AsmError("`#` の書き込みは、番地も値も Int か文字の形だけ出せます。リスト・文字列(器)を番地へ書く形は、仕様の参照コンパイラも『書ける値はレジスタ1本ぶんです』と断ります(alpha/javascript/pass4.js)。器は要素ごとに `out # (s ' i)` と書く(idiom_to_instructions.md §1.3)[番地 %s・値 %s: %r # %r]" % (self.prog.kind(l, self.kinds), self.prog.kind(r, self.kinds), l, r))
            self.gen(l)                                 # 番地を先に評価し、値をあとに評価する(R107)
            fin = self.prog.label() if self.mu(l) else None
            if fin: self.niche(); self.emit("cmp x0, x13"); self.emit("b.eq %s" % fin, "番地が __ なら答えは __(右は評価しない。処理系と同じ)")
            t = self.tmp(); self.emit("str x0, [x29, #%d]" % self.off(t), "番地")
            rs = r
            while rs[0] == "block": rs = rs[1]
            if self.prog.kind(r, self.kinds) == "C":            # 文字を書く: 字面・文字の定数・文字列の取り出し(文字コードで書く)
                self.gen_char_value(rs)
            else: self.gen(r)
            self.emit("ldr x9, [x29, #%d]" % self.off(t)); self.free()
            skip = self.prog.label()
            if self.mu(r):
                self.niche(); self.emit("cmp x0, x13"); self.emit("b.eq %s" % skip, "値が __ なら何も書かない(番地は返る)")
            wd = self.addr_width(l)
            rdev = REALDEV[0] and wd not in (1, 2)
            if rdev:                                    # --real-dev: 装置の番地(0x9000000 以上)は実機の中継ルーチンへ
                dn, de = self.prog.label(), self.prog.label()
                emit_imm(self.lines, "x10", 0x9000000); self.emit("cmp x9, x10"); self.emit("b.lo %s" % dn)
                self.emit("mov x1, #%d" % (4 if wd == 4 or (wd == 0 and CW == 4 and self.prog.kind(r, self.kinds) == "C") else 8), "幅")
                self.emit("bl _sign_dev_st", "装置への書き込み(実機の中継。sign_realdev.py)"); self.emit("b %s" % de)
                self.lines.append("%s:" % dn)
            if wd in (1, 2, 4): self.emit({1: "strb w0, [x9]", 2: "strh w0, [x9]", 4: "str w0, [x9]"}[wd], "幅 %d byte で書く(value_representation.md §5。値はその幅へ切れる)" % wd)
            elif CW == 4 and self.prog.kind(r, self.kinds) == "C": self.emit("str w0, [x9]", "Char は charset(utf32)の幅 4 byte で書く(value_representation.md §5.5。装置の UART 模擬はこれを UTF-8 にして出す。Int は 8 byte でその下位 1 byte)")
            else: self.emit("str x0, [x9]", "64 ビットで書く(装置・普通のメモリの区別は処理系の仮想装置の領分。実機では番地が実在することが前提)")
            if rdev: self.lines.append("%s:" % de)
            self.lines.append("%s:" % skip)
            self.emit("mov x0, x9", "答えは番地")
            if fin: self.lines.append("%s:" % fin)
            return
        if op == "-" and self.prog.kind(l, self.kinds) == "C" and self.prog.kind(r, self.kinds) == "C":
            # 文字 - 文字 = Int(符号位置の差。片方が __ なら __。処理系: `(s ' 5) - 0u0` は範囲の外で __)
            self.gen_char_value(l)
            t = self.tmp(); self.emit("str x0, [x29, #%d]" % self.off(t), "左の文字")
            self.gen_char_value(r)
            self.emit("mov x10, x0"); self.emit("ldr x9, [x29, #%d]" % self.off(t)); self.free()
            unit, done = self.prog.label(), self.prog.label()
            def lit_ch(o):
                o = self.strip(o); return (o[0] == "lit" and isinstance(o[1], Char)) or (o[0] == "id" and o[1] in self.prog.chars and o[1] not in self.slot)
            if not lit_ch(l): self.emit("cbz x9, %s" % unit, "Char の __ は U+0000(字面の U+0000 は __ ではない)")
            if not lit_ch(r): self.emit("cbz x10, %s" % unit)
            self.emit("sub x0, x9, x10", "符号位置の差は Int の値域に収まる"); self.emit("b %s" % done)
            self.lines.append("%s:" % unit); self.niche("x0")
            self.lines.append("%s:" % done)
            return
        if op not in ("+", "-", "*", "/", "%", "<<", ">>", "||", ";;", "&&"):
            raise AsmError("演算子 `%s` はまだ出せません" % op)
        if self.nested_calls(n) and self.par_hoist(n): return        # 実引数の中にも呼び出しがある形は、内側から段に分けて並列に
        ch = self.par_chain(n)
        if ch is not None:
            self.par_emit_chain(*ch); return
        if not self.simple(r) and self.par_pair(op, l, r) is None and self.par_hoist(n): return
        if self.simple(r):
            self.gen(l)
            self.emit("mov x9, x0")
            self.load(r, "x10")
        else:
            pc_ = self.par_pair(op, l, r)
            if pc_ is not None:
                t = self.tmp(); self.par_emit(pc_, l, r, t)
            else:
                self.gen(l)
                t = self.tmp()
                self.emit("str x0, [x29, #%d]" % self.off(t), "途中の値はフレームへ")
                self.gen(r)
            self.emit("mov x10, x0")
            self.emit("ldr x9, [x29, #%d]" % self.off(t))
            self.free()
        self.bin_tail(op, l, r)

    def bin_tail(self, op, l, r):
        """x9 = 左の値、x10 = 右の値 から、演算 op の答えを x0 へ(`__` の扱い・溢れの罠を含む)。連なりの畳み込みにも使う。"""
        done = None
        ml, mr = self.mu(l), self.mu(r)
        if ml or mr:
            # 算術の `__` は両側で単位元(爆発律): 片方が `__` なら残った辺が答え、両方なら `__`。
            # 罠の道の入口で見直す(integer_overflow.md §1.1)代わりに、先に見て分ける(niche のまま計算して偽の罠に飛ぶのを避ける)
            done = self.prog.label()
            self.niche()
            if ml:
                nl = self.prog.label()
                self.emit("cmp x9, x13"); self.emit("b.ne %s" % nl)
                self.emit("mov x0, x10"); self.emit("b %s" % done)
                self.lines.append("%s:" % nl)
            if mr:
                nr = self.prog.label()
                self.emit("cmp x10, x13"); self.emit("b.ne %s" % nr)
                self.emit("mov x0, x9"); self.emit("b %s" % done)
                self.lines.append("%s:" % nr)
        if op in ("<<", ">>") and done is None: done = self.prog.label()
        if op in ("/", "%"):
            rr = r
            while rr[0] == "block": rr = rr[1]
            nonzero = (rr[0] == "lit" and int_literal(rr) != 0) or (rr[0] == "neg" and rr[1][0] == "lit" and int_literal(rr[1]) != 0)
            if not nonzero:
                ok = self.prog.label()
                if done is None: done = self.prog.label()
                self.emit("cmp x10, #0"); self.emit("b.ne %s" % ok, "0 で割ると __")
                self.niche("x0"); self.emit("b %s" % done)
                self.lines.append("%s:" % ok)
            if op == "/":
                self.emit("sdiv x0, x9, x10", "商は被除数を超えず、値域は対称なので溢れない(integer_overflow.md §1.1)")
            else:
                self.emit("sdiv x11, x9, x10")
                self.emit("msub x0, x11, x10, x9", "余り = 被除数 - 商 × 割る数")
        elif op in ("&&", "||", ";;"):                       # ビット演算(operator_table.md): 2 の補数の 64 ビットで。結果が INT64_MIN になれば値域の外(罠)
            self.prog.trap_used = True
            self.emit({"&&": "and x0, x9, x10", "||": "orr x0, x9, x10", ";;": "eor x0, x9, x10"}[op])
            self.niche(); self.emit("cmp x0, x13"); self.emit("b.eq .Ltrap", "結果が __ の印と同じ値(INT64_MIN)は値域の外")
        elif op == ">>":                                     # 算術右シフト。数が負なら __。64 以上は符号だけが残る
            ok, sh = self.prog.label(), self.prog.label()
            self.emit("cmp x10, #0"); self.emit("b.ge %s" % ok, "シフト数が負なら __")
            self.niche("x0"); self.emit("b %s" % done)
            self.lines.append("%s:" % ok)
            self.emit("cmp x10, #63"); self.emit("b.ls %s" % sh); self.emit("mov x10, #63", "63 を超えるシフトは符号だけが残る")
            self.lines.append("%s:" % sh)
            self.emit("asr x0, x9, x10")
        elif op == "<<":                                     # 左シフト。数が負なら __。結果が Int の値域の外なら罠
            self.prog.trap_used = True
            ok, big, end = self.prog.label(), self.prog.label(), self.prog.label()
            self.emit("cmp x10, #0"); self.emit("b.ge %s" % ok, "シフト数が負なら __")
            self.niche("x0"); self.emit("b %s" % done)
            self.lines.append("%s:" % ok)
            self.emit("cmp x10, #63"); self.emit("b.hi %s" % big)
            self.emit("lsl x11, x9, x10"); self.emit("asr x12, x11, x10"); self.emit("cmp x12, x9"); self.emit("b.ne .Ltrap", "戻して合わなければ溢れた")
            self.niche(); self.emit("cmp x11, x13"); self.emit("b.eq .Ltrap", "INT64_MIN になった")
            self.emit("mov x0, x11"); self.emit("b %s" % end)
            self.lines.append("%s:" % big)
            self.emit("cbnz x9, .Ltrap", "64 以上のシフトで 0 でない値は溢れる"); self.emit("mov x0, #0")
            self.lines.append("%s:" % end)
        else:
            self.prog.trap_used = True
            if op == "+":
                self.emit("adds x9, x9, x10")
                self.emit("ccmp xzr, x9, #1, vc", "溢れずに INT64_MIN に着いた結果も罠")
                self.emit("b.vs .Ltrap")
                self.emit("mov x0, x9")
            elif op == "-":
                self.emit("subs x9, x9, x10")
                self.emit("ccmp xzr, x9, #1, vc")
                self.emit("b.vs .Ltrap")
                self.emit("mov x0, x9")
            else:
                self.emit("mul x11, x9, x10")
                self.emit("smulh x12, x9, x10", "積の上の語")
                self.emit("cmp x12, x11, asr #63", "上の語が下の語の符号の伸びでなければ溢れた")
                self.emit("ccmp xzr, x11, #1, eq")
                self.emit("b.vs .Ltrap")
                self.emit("mov x0, x11")
        if done: self.lines.append("%s:" % done)

    # ---- リスト(Int の要素。読むだけ) ----
    def load_list(self, n, rp, rl):
        """リスト・文字列を表す項 n の先頭の番地を rp へ、長さを rl へ。"""
        while n[0] == "block": n = n[1]
        tl = self.prog.tail_of(n) if n[0] == "bin" else None
        if tl is not None:
            inner, a = tl
            ik = self.prog.kind(inner, self.kinds)
            if ik not in WIDE: raise AsmError("末尾の切り出しができるのはリストと文字列だけです")
            esz = {"L": 8, "S": CW, "N": 16}[ik]
            self.load_list(inner, "x9", "x10")
            u, d = self.prog.label(), self.prog.label()
            if a < 4096: self.emit("cmp x10, #%d" % a, "始まりの添字 %d が長さ以上なら尽きている(`__`)" % a)
            else: emit_imm(self.lines, "x14", a); self.emit("cmp x10, x14")
            self.emit("b.ls %s" % u)
            if a * esz < 4096: self.emit("add %s, x9, #%d" % (rp, a * esz), "a 番目から終わりまで(コピーしない。見せるだけ)")
            else: emit_imm(self.lines, "x14", a * esz); self.emit("add %s, x9, x14" % rp)
            if a < 4096: self.emit("sub %s, x10, #%d" % (rl, a), "長さ")
            else: emit_imm(self.lines, "x14", a); self.emit("sub %s, x10, x14" % rl)
            self.emit("b %s" % d)
            self.lines.append("%s:" % u); self.emit("mov %s, #0" % rp); self.emit("mov %s, #0" % rl, "尽きたら __(len = 0)")
            self.lines.append("%s:" % d)
            return
        sl = self.prog.slice_of(n) if n[0] == "bin" else None
        if sl is not None:
            inner, a, b = sl
            ik = self.prog.kind(inner, self.kinds)
            if ik not in WIDE: raise AsmError("スライスできるのはリストと文字列だけです")
            esz = {"L": 8, "S": CW, "N": 16}[ik]
            self.load_list(inner, "x9", "x10")
            u, d = self.prog.label(), self.prog.label()
            if b + 1 < 4096: self.emit("cmp x10, #%d" % (b + 1), "終わりの添字 %d が範囲の内か(外なら __)" % b)
            else: emit_imm(self.lines, "x14", b + 1); self.emit("cmp x10, x14")
            self.emit("b.lo %s" % u)
            if a * esz < 4096: self.emit("add %s, x9, #%d" % (rp, a * esz), "始まりの添字 %d(コピーしない。見せるだけ)" % a)
            else: emit_imm(self.lines, "x14", a * esz); self.emit("add %s, x9, x14" % rp)
            emit_imm(self.lines, rl, b - a + 1, "長さ")
            self.emit("b %s" % d)
            self.lines.append("%s:" % u); self.emit("mov %s, #0" % rp); self.emit("mov %s, #0" % rl, "範囲の外は __(len = 0)")
            self.lines.append("%s:" % d)
            return
        ov = self.prog.one_elem(n)
        if ov is not None and self.prog.kind(n, self.kinds) == "I":          # Int の字面 ≅ 要素 1 個のリスト(リストを受ける仮引数へ渡す)
            label = self.prog.rodata_label([ov])
            self.emit("adrp %s, %s" % (rp, label), "1 要素のリスト(.rodata)"); self.emit("add %s, %s, :lo12:%s" % (rp, rp, label)); emit_imm(self.lines, rl, 1, "len = 1")
            return
        if n[0] == "bin" and n[1] == "'" and self.prog.kind(n[2], self.kinds) == "N":
            return self.gen_index_nest(n[2], n[3], rp, rl)
        if n[0] == "id" and n[1] in self.prog.nests or n[0] == "seq" and self.prog.nested_values(n) is not None:
            if n[0] == "id": label, cnt = self.prog.nests[n[1]][:2]
            else: vl = self.prog.nested_values(n); self.prog.nest_mark_lit(n); label, cnt = self.prog.nest_label(vl), len(vl)
            self.emit("adrp %s, %s" % (rp, label), "入れ子のリストの記述子の表(.rodata。1 つ 16 バイトの {ptr, len})")
            self.emit("add %s, %s, :lo12:%s" % (rp, rp, label))
            emit_imm(self.lines, rl, cnt, "要素(内側のリスト)の数")
            return
        if self.is_call(n) or n[0] == "cases":
            if n[0] == "cases": self.gen_cases(n, False, self.prog.kind(n, self.kinds))
            else: self.gen_call(n)
            if rp != "x0": self.emit("mov %s, x0" % rp)
            if rl != "x1": self.emit("mov %s, x1" % rl)
            return
        if n[0] == "id" and n[1] in self.slot and self.kinds[n[1]] in WIDE:
            c = self.slot[n[1]]
            self.emit("ldr %s, [x29, #%d]" % (rp, self.off(c)), n[1] + ".ptr")
            self.emit("ldr %s, [x29, #%d]" % (rl, self.off(c + 1)), n[1] + ".len"); return
        if n[0] == "id" and n[1] in self.prog.lists:
            label, vals = self.prog.lists[n[1]]
        elif n[0] == "id" and n[1] in self.prog.strs:
            label, vals = self.prog.strs[n[1]]
        elif self.prog.str_value(n) is not None:
            vals = self.prog.str_value(n); label = self.prog.rodata_label(vals, True)
        else:
            vals = self.prog.list_values(n)
            if vals is None:
                if self.prog.builds(n) is not None: raise AsmError("要素を式で組み立てた器(リスト・入れ子のリスト)は、関数の返値の位置でしか作れません(引数や途中の値に直接は置けません。関数に包んで返してください。相互再帰の輪で累積を伸ばす形が、処理系に認識できなかったときもこの断りになります)")
                raise AsmError("リスト・文字列の形がまだ出せません(字面と、それを渡された仮引数だけ)")
            label = self.prog.rodata_label(vals)
        self.emit("adrp %s, %s" % (rp, label), "リストの像(.rodata)")
        self.emit("add %s, %s, :lo12:%s" % (rp, rp, label))
        emit_imm(self.lines, rl, len(vals), "長さ")

    def solid_items(self, l): return self.prog.solid_seq(l, self.kinds)

    def static_list(self, l): return self.prog.static_list(l, self.kinds)

    def maybe_items(self, l):
        """要素が全部 Int の式(比べ・関数の呼びなど `__` になりうるものも可)の並び `(a b c)` なら、その要素。`__` の要素は並びから落ちるので、
        長さと位置は実行時に決まる。先頭が関数の名前で実引数が余る並び(`(g x 5)`、g は引数 1 個)は、`(g x)` の結果の後ろに余りを積む読み
        (設計者の裁定。余りの実引数は呼びの後ろに値として並ぶ)で、呼びと余りの要素に開く。入れ子・Int でない要素・17 個以上は None。"""
        while l[0] == "block": l = l[1]
        if l[0] != "seq" or len(l) != 2 or len(l[1]) < 2: return None
        items = list(l[1]); h = items[0]
        while h[0] == "block": h = h[1]
        if h[0] == "id" and h[1] in self.prog.fns:
            n = len(self.prog.fns[h[1]])
            if len(items) - 1 < n: return None
            items = [("seq", items[:n + 1])] + items[n + 1:]
        if len(items) < 2 or len(items) > 16: return None
        for e in items:
            while e[0] == "block": e = e[1]
            if e[0] == "id" and e[1] in self.prog.fns: return None
            if e[0] == "seq" and not self.is_call(e): return None
            if self.prog.kind(e, self.kinds) != "I": return None
        return items

    def gen_seq_pick(self, items, k, r=None):
        """`(a b c) ' k`。全部の要素を左から評価して預け、`__` でないものだけを数え、k 番目(負は後ろから)を出す。外れれば `__`。
        k が定数でなければ(r が添字の式)、要素のあとで添字を評価して預ける。添字が `__` なら `__`。"""
        ts = []
        for e in items:
            self.gen(e); t = self.tmp(); ts.append(t); self.emit("str x0, [x29, #%d]" % self.off(t), "要素を預ける")
        ti = None
        if k is None:
            self.gen(r); ti = self.tmp(); self.emit("str x0, [x29, #%d]" % self.off(ti), "添字を預ける")
        self.niche()
        unit, done = self.prog.label(), self.prog.label()
        self.emit("mov x11, #0", "`__` でない要素の数")
        for t in ts:
            sk = self.prog.label()
            self.emit("ldr x0, [x29, #%d]" % self.off(t)); self.emit("cmp x0, x13"); self.emit("b.eq %s" % sk); self.emit("add x11, x11, #1")
            self.lines.append("%s:" % sk)
        if k is None:
            self.emit("ldr x12, [x29, #%d]" % self.off(ti), "添字")
            if self.mu(r): self.emit("cmp x12, x13"); self.emit("b.eq %s" % unit, "添字が __ なら __")
            pos = self.prog.label()
            self.emit("cmp x12, #0"); self.emit("b.ge %s" % pos); self.emit("add x12, x12, x11", "負の添字は後ろから")
            self.lines.append("%s:" % pos)
            self.emit("cmp x12, x11"); self.emit("b.hs %s" % unit, "範囲の外(符号なしで比べると、後ろからでも足りない負の数も外れる)")
        elif k >= 0:
            self.emit("cmp x11, #%d" % k); self.emit("b.ls %s" % unit, "数が足りなければ __"); self.emit("mov x12, #%d" % k)
        else:
            self.emit("cmp x11, #%d" % -k); self.emit("b.lo %s" % unit, "数が足りなければ __"); self.emit("sub x12, x11, #%d" % -k)
        for t in ts:
            sk = self.prog.label()
            self.emit("ldr x0, [x29, #%d]" % self.off(t)); self.emit("cmp x0, x13"); self.emit("b.eq %s" % sk)
            self.emit("cmp x12, #0"); self.emit("b.eq %s" % done, "k 番目の要素")
            self.emit("sub x12, x12, #1")
            self.lines.append("%s:" % sk)
        self.lines.append("%s:" % unit); self.emit("mov x0, x13", "__")
        self.lines.append("%s:" % done)
        for _ in ts: self.free()
        if ti is not None: self.free()

    def gen_seq_count(self, items):
        ts = []
        for e in items:
            self.gen(e); t = self.tmp(); ts.append(t); self.emit("str x0, [x29, #%d]" % self.off(t), "要素を預ける")
        self.niche(); self.emit("mov x11, #0")
        for t in ts:
            sk = self.prog.label()
            self.emit("ldr x0, [x29, #%d]" % self.off(t)); self.emit("cmp x0, x13"); self.emit("b.eq %s" % sk); self.emit("add x11, x11, #1")
            self.lines.append("%s:" % sk)
        self.emit("mov x0, x11", "`__` でない要素の数")
        for _ in ts: self.free()

    def gen_norm(self, n):
        ls = self.static_list(n[1]); it = ls[1] if ls is not None else None
        if it is not None: self.emit("mov x0, #%d" % len(it), "要素が全部 `__` にならない Int の並びの長さ"); return
        mi = self.maybe_items(n[1])
        if mi is not None: self.gen_seq_count(mi); return
        if self.prog.kind(n[1], self.kinds) == "R":
            self.load_rule(n[1], "x9", "x10", "x12"); self.emit_rule_count("x9", "x10", "x12", "x0"); return
        if self.prog.kind(n[1], self.kinds) == "I":      # Int は長さ 1 の並び。`__` なら 0
            self.gen(n[1])
            if self.mu(n[1]):
                lz = self.prog.label(); self.niche(); self.emit("cmp x0, x13"); self.emit("mov x0, #1"); self.emit("b.ne %s" % lz, "__ なら 0、そうでなければ 1"); self.emit("mov x0, #0"); self.lines.append("%s:" % lz)
            else: self.emit("mov x0, #1", "Int は長さ 1")
            return
        if self.prog.kind(n[1], self.kinds) not in WIDE:
            raise AsmError("`||x||` はリスト・文字列・規則の長さだけ出せます(それ以外はまだ)")
        o, self.ext_ok = self.ext_ok, True
        try: self.load_list(n[1], "x9", "x0")
        finally: self.ext_ok = o

    def gen_index(self, l, r):
        """`l ' i`: i が -長さ 〜 長さ-1 なら要素(負は後ろから)、外れれば `__`。範囲の外は読まない。"""
        ls = self.static_list(l); it = ls[1] if ls is not None else None; k = self.prog.const_int(r)
        if it is not None and k is not None:             # 要素が全部 `__` にならない並び(入れ子も可)の定数の添字は、その要素だけを出す(外れれば `__`)
            if not -len(it) <= k < len(it): self.niche("x0"); return
            e = it[k]
            while e[0] == "block": e = e[1]
            if not (e[0] == "seq" and not self.is_call(e)): self.gen(it[k]); return          # 選んだのが入れ子の並びなら、器が要る(今までの経路が断る)
        mi = self.maybe_items(l)
        if mi is not None and (k is not None or self.prog.kind(r, self.kinds) == "I"): self.gen_seq_pick(mi, k, r); return
        lk = self.prog.kind(l, self.kinds)
        if lk == "R": return self.gen_index_rule(l, r)
        if lk == "N": raise AsmError("内部の誤り: 入れ子の取り出しは load_list の道")
        if lk == "I":                                    # Int は長さ 1 の並びと読まれる(処理系の観測): 添字が 0 か -1 なら自分、ほかは `__`。自分が `__` なら `__` のまま
            if self.prog.kind(r, self.kinds) != "I": raise AsmError("添字は Int だけです")
            t = self.tmp(); self.gen(l); self.emit("str x0, [x29, #%d]" % self.off(t), "Int の値を預ける")
            self.gen(r); self.emit("mov x11, x0")
            unit, done, take = self.prog.label(), self.prog.label(), self.prog.label()
            if self.mu(r):
                self.niche(); self.emit("cmp x11, x13"); self.emit("b.eq %s" % unit, "添字が __ なら __")
            self.emit("cmp x11, #0"); self.emit("b.eq %s" % take)
            self.emit("add x12, x11, #1"); self.emit("cbnz x12, %s" % unit, "0 でも -1 でもなければ __")
            self.lines.append("%s:" % take); self.emit("ldr x0, [x29, #%d]" % self.off(t)); self.emit("b %s" % done)
            self.lines.append("%s:" % unit); self.niche("x0")
            self.lines.append("%s:" % done); self.free(); return
        if lk not in WIDE:
            raise AsmError("`'` はリスト・文字列・規則の要素の取り出しだけ出せます(それ以外はまだ)")
        if self.prog.kind(r, self.kinds) != "I":
            raise AsmError("添字は Int だけです")
        self.gen(r)
        self.emit("mov x11, x0")
        unit, done = self.prog.label(), self.prog.label()
        if self.mu(r):
            self.niche(); self.emit("cmp x11, x13"); self.emit("b.eq %s" % unit, "添字が __ なら __")
        ll = l
        while ll[0] == "block": ll = ll[1]
        if self.is_call(ll) or ll[0] in ("cases", "bin"):         # 呼び・入れ子の取り出しは x11 を壊すので、添字を預けておく
            t = self.tmp(); self.emit("str x11, [x29, #%d]" % self.off(t), "添字を預ける")
            o, self.ext_ok = self.ext_ok, True
            try: self.load_list(l, "x9", "x10")
            finally: self.ext_ok = o
            self.emit("ldr x11, [x29, #%d]" % self.off(t)); self.free()
        else:
            self.load_list(l, "x9", "x10")
        pos = self.prog.label()
        self.emit("cmp x11, #0"); self.emit("b.ge %s" % pos)
        self.emit("add x11, x11, x10", "負の添字は後ろから")
        self.lines.append("%s:" % pos)
        self.emit("cmp x11, x10"); self.emit("b.hs %s" % unit, "範囲の外(符号なしで比べると、後ろからでも足りない負の数も外れる)。読まない")
        if lk == "S":
            self.emit("ldrb w0, [x9, x11]", "文字(ASCII の 1 バイト)") if CW == 1 else self.emit("ldr w0, [x9, x11, lsl #2]", "文字(utf32 の 4 バイト)")
            self.emit("b %s" % done)
            self.lines.append("%s:" % unit); self.emit("mov x0, #0", "Char の `__` は U+0000(niche)")
        else:
            self.emit("ldr x0, [x9, x11, lsl #3]")
            self.emit("b %s" % done)
            self.lines.append("%s:" % unit); self.niche("x0")
        self.lines.append("%s:" % done)

    ext_ok = False         # 入れ子の要素 `m ' i` を、取り出し・長さの底として読んでいる(混ざる入れ子でも出せる使い方)
    ext_raw = False        # 最上位の印字: 印のまま {ptr, len} を渡す(印字がスカラーかリストかを見て綴る)

    def gen_index_nest(self, l, r, rp, rl):
        """`m ' i`(m は入れ子のリスト): i が -個数 〜 個数-1 なら i 番目の内側のリスト(記述子 {ptr, len} を読むだけ。コピーしない)、
        外れれば `__`(ptr = len = 0)。結果を rp(先頭)と rl(長さ)へ。"""
        if self.prog.kind(r, self.kinds) != "I": raise AsmError("添字は Int だけです")
        self.prog.nest_emit_seen.add(self.prog.mixed_nest)
        raw, self.ext_raw = self.ext_raw, False      # 印のまま渡すのは一番外の取り出しだけ(中の段は外して辿る)
        if self.prog.scalar_nest and not self.ext_ok and not raw and self.prog.kind(("bin", "'", l, r), self.kinds) == "L": self.prog.note_unsafe("混ざる入れ子(スカラーとリストが並ぶ)の要素 `m ' i` を、取り出し・長さ・最上位の印字以外に使う形(要素がスカラーかリストかは実行時の印で決まり、値として渡す・返す・足すは使う所の種類が定まらない)")
        self.gen(r)
        self.emit("mov x11, x0")
        unit, done, pos = self.prog.label(), self.prog.label(), self.prog.label()
        if self.mu(r):
            self.niche(); self.emit("cmp x11, x13"); self.emit("b.eq %s" % unit, "添字が __ なら __")
        ll = self.strip(l)
        if self.is_call(ll) or ll[0] in ("cases", "bin"):
            t = self.tmp(); self.emit("str x11, [x29, #%d]" % self.off(t), "添字を預ける")
            self.load_list(l, "x9", "x10")
            self.emit("ldr x11, [x29, #%d]" % self.off(t)); self.free()
        else:
            self.load_list(l, "x9", "x10")
        self.emit("cmp x11, #0"); self.emit("b.ge %s" % pos)
        self.emit("add x11, x11, x10", "負の添字は後ろから")
        self.lines.append("%s:" % pos)
        self.emit("cmp x11, x10"); self.emit("b.hs %s" % unit, "範囲の外。読まない")
        self.emit("lsl x11, x11, #4", "記述子は 1 つ 16 バイト")
        self.emit("add x9, x9, x11")
        self.emit("ldr x0, [x9]", "内側のリストの先頭"); self.emit("ldr x1, [x9, #8]", "内側のリストの長さ")
        if self.prog.mixed_nest and not raw:
            self.emit("and x0, x0, #-8", "ptr の下位 3 ビットは印(bit0 = スカラー、bit1 = 文字列、bit2 = 入れ子)。外して先頭の番地にする(スカラーは値のセル。長さ 1 のリストとして読む)")
        self.emit("b %s" % done)
        self.lines.append("%s:" % unit); self.emit("mov x0, #0"); self.emit("mov x1, #0", "器の `__` は len = 0")
        self.lines.append("%s:" % done)
        if rp != "x0": self.emit("mov %s, x0" % rp)
        if rl != "x1": self.emit("mov %s, x1" % rl)

    def gen_call(self, n, tail=False, inplace=None):
        h = self.hoist_call(n) if inplace is None else None
        if h is None: return self.gen_call_core(n, tail, inplace)
        rebuilt, names, vals = h
        self.gen_call_core(rebuilt, tail, inplace)
        for nm in names: del self.slot[nm]; del self.kinds[nm]
        for _ in vals: self.free()

    def hoist_call(self, n):
        """--par: 実引数のあちこち(`f ((g x) + 1) ((h y) * 2)` のように、式の中)にある独立な純粋な呼び出しが 2 つ以上あれば、先に並列で評価して名前に置き、
        呼び先へは名前で渡す(実引数は呼ぶ前に全部評価するので、順は答えに効かない)。(組み直した呼び、名前の並び、スロットの並び) か None。"""
        if PAR[0] is None or getattr(self.prog, "target", "bare") != "linux": return None
        items = n[1]; head = items[0]
        if head[0] != "id" or head[1] not in self.prog.fns: return None
        f = head[1]; args = items[1:]
        if len(args) != len(self.prog.fns[f]): return None
        pk = self.prog.pkind[f]
        if any(k != "I" for k in pk) or f in self.prog.flagrelay or f in self.prog.maskfns or (f == self.name and self.prog.grow.get(f)) \
                or (f != self.name and (self.name, f) in self.prog.ring_grow): return None
        if not any(self.has_seq(b) for a in args for b in [self.strip(a)] if b[0] == "seq" and b[1] and b[1][0][0] == "id" and any(self.has_seq(c) for c in b[1][1:])) \
                and self.par_args(args, pk, {}): return None             # 実引数が呼び出しだけの形は、そちらが受ける(その中にまた呼び出しがあれば、こちらが段に分けて受ける)
        pl = self.hoist_plan(args, False)
        if pl is None: return None
        names, vals = self.hoist_exec(pl[0])
        return ("seq", [items[0]] + pl[1]) + tuple(n[2:]), names, vals

    pvn = 0

    def reg_pv(self, pre, leaves, vals):
        """先に評価した葉を名前(スロット)に置く。答えが `__` になりうる葉の名前は、`__` になりうるものとして見積もらせる(`__` は + - * で消える単位)。"""
        names = [pre + str(i) for i in range(len(leaves))]
        for nm, v, (y, c) in zip(names, vals, leaves):
            self.slot[nm] = v; self.kinds[nm] = "I"
            if self.mu(y): self.prog.maybe_ids.add(nm)
        return names

    def pv_prefix(self):
        """先に評価した葉の名前(スロット)の頭。入れ子の組み直しで名前がぶつからないよう、関数ごとに通し番号を振る。"""
        FnGen.pvn += 1
        return "%%pv%d_" % FnGen.pvn

    def hoist_plan(self, xs, allow_mu=True):
        """式 xs の中の独立な純粋な呼び出しを、段に分けて先に評価する計画を立てる(コードはまだ出さない)。
        1 段目は実引数に呼び出しを含まない呼び出し、2 段目は 1 段目の答え(名前)を実引数にする呼び出し、…(`(f (g x)) + (f (g y))` なら、g 2 本 → f 2 本)。
        どれかの段に 2 つ以上の葉が無ければ(並列で得をしない)None。(段の並び [(名前の頭, 葉の並び)], 組み直した式の並び) を返す。"""
        plan = []; cur = list(xs)
        for _ in range(6):
            leaves = []; pre = self.pv_prefix()
            new = [self.hoist_walk(x, leaves, pre, allow_mu, True) for x in cur]
            if not leaves: break
            plan.append((pre, leaves)); cur = new
        if not plan or not any(len(l) >= 2 for _, l in plan): return None
        return plan, cur

    def hoist_exec(self, plan):
        """hoist_plan の計画のコードを出す。(名前の並び, スロットの並び)。"""
        names, vals = [], []
        for pre, leaves in plan:
            if len(leaves) == 1:                                   # 1 本だけの段(前の段の答えを使う呼び出し 1 つ)は、そのまま自分で計算してスロットに置く
                self.gen(leaves[0][0]); t = self.tmp(); self.emit("str x0, [x29, #%d]" % self.off(t), "段の答え"); v = [t]
            else: v = self.par_run_leaves(leaves)
            names += self.reg_pv(pre, leaves, v); vals += v
        return names, vals

    def hoist_walk(self, x, leaves, pre, allow_mu=True, deep=False):
        """x の中の、仕事に出せる呼び出し(答えが `__` にならない物)を leaves に集め、名前(pre + 番号)に替えた木を返す。"""
        y = self.strip(x)
        if deep and y[0] == "seq" and y[1] and y[1][0][0] == "id":
            h = y[1][0][1]; el = self.prog.par_elig()
            if h in el and len(y[1]) - 1 == el[h] and all(k == "I" for k in self.prog.pkind[h]) and any(self.has_seq(a) for a in y[1][1:]):
                n0 = len(leaves)
                na = [self.hoist_walk(a, leaves, pre, False, True) for a in y[1][1:]]      # 実引数の中の呼び出し(答えが __ にならない物)を先に
                if len(leaves) > n0: return ("seq", [y[1][0]] + na) + tuple(y[2:])
        c = self.par_call(y)
        if c is not None and (allow_mu or not self.mu(y)):
            leaves.append((y, c)); return ("id", pre + str(len(leaves) - 1))
        if y[0] == "bin" and y[1] in ("+", "-", "*", "/", "%", "<<", ">>", "||", ";;", "&&"):
            return ("bin", y[1], self.hoist_walk(y[2], leaves, pre, allow_mu, deep), self.hoist_walk(y[3], leaves, pre, allow_mu, deep))
        if y[0] == "neg": return ("neg", self.hoist_walk(y[1], leaves, pre, allow_mu, deep))
        return y

    def gen_call_core(self, n, tail=False, inplace=None):
        """inplace = (書く位置のセル, 入る個数のセル): 器を組み立てて返す関数を、置き場を新しく取らずに、いま書いている位置へ直に書かせる
        (設計者の『撒きながら食う』。コピーも積み上げも無い)。"""
        items = n[1]
        head = items[0]
        if head[0] != "id" or head[1] not in self.prog.fns:
            if any(self.prog.kind(x, self.kinds) in WIDE for x in items):
                raise AsmError("並びの要素にリストがあります(入れ子)。入れ子のリストは、字面か関数の返値の位置でだけ作れます。平らに繋ぐには `xs~ ys~` と展開してください(`xs ys` は入れ子のリスト、`xs~ ys~` が連結。operator_table.md の unshift / concat)")
            if any(x[0] == "post" and x[1] == "~" and self.prog.kind(x[2], self.kinds) == "R" for x in items):
                raise AsmError("規則の展開(`r~`)はまだ出せません(展開先の大きさが仮引数の器の長さ ||p|| で測れず、上界が出せない。設計者の sret も器の 2 本しか測れない)")
            if any(x[0] == "post" and x[1] == "~" for x in items):
                raise AsmError("展開(~)できるのは、仮引数の器・字面・定数の範囲・定数端のスライスだけです(関数の結果などの展開はまだ出せません)")
            raise AsmError("関数でない物の適用はまだ出せません")
        f = head[1]
        params = self.prog.fns[f]
        args = items[1:]
        if len(args) != len(params):
            raise AsmError("%s は引数 %d 個の関数ですが、%d 個で呼ばれています(部分適用・余った引数はまだ出せません)" % (f, len(params), len(args)))
        pk = self.prog.pkind[f]
        # 引数を左から評価して、いったんフレームのスロットへ(後の引数の評価が x0〜x7 を壊すので)。リストは {ptr, len} の 2 つ
        tmps = []               # (スロットの並び, 種類)
        fl_relay = f in self.prog.flagrelay and self.name in self.prog.flagfns
        fcell = self.tmp() if fl_relay else None          # 素通しで返す実引数の旗(x2)を預ける
        fl_mask = f in self.prog.maskfns and self.name in self.prog.flagfns
        mcells = {j: self.tmp() for j in sorted(self.prog.relay.get(f, ()))} if fl_mask else {}      # 返しうる実引数ごとの旗
        gws = []                # 伸びる累積の末尾呼び出し: (書く要素のスロット, 種類, t1, t2, 呼ぶ側の累積の仮引数)。引数を全部評価し終えてから累積の末尾へ書く
        ringcall = f != self.name and (self.name, f) in self.prog.ring_grow
        accs = {}               # 呼び先の位置 → 呼ぶ側の累積の仮引数
        if f == self.name and self.prog.grow.get(f):
            for (j_, _d, _e) in [self.prog.grow[f]] + self.prog.grow_extra.get(f, []): accs[j_] = self.prog.fns[f][j_]
        elif ringcall:
            for rg_ in self.prog.ring_grow[(self.name, f)][1]: accs[rg_[0]] = self.prog.fns[self.name][rg_[1]]
        pvals = {}              # --par: 実引数の呼び出しどうし(`f (g x) (h y)`)。位置 → 答えのスロット
        pidx = self.par_args(args, pk, accs)
        # 字面の整数の実引数は、フレームへ書いて読み戻さず、呼びの直前にレジスタへ直に入れる(late[スロット] = 値)。
        # 字面は後の引数の評価に壊されない。器の返す所・旗・並列・累積の伸びがある呼びは、今までの道のまま。
        late = {}
        late_ok = not self.prog.bound.get(f) and not accs and not fl_mask and not fl_relay and not pidx
        for ai, (a, kd) in enumerate(zip(args, pk)):
            if ai in pvals or (pidx and ai == pidx[0]):
                if ai == pidx[0]:
                    vs_ = self.par_run_leaves([(args[j], self.par_call(args[j])) for j in pidx])
                    pvals = dict(zip(pidx, vs_))
                tmps.append(([pvals[ai]], kd)); continue
            if ai in accs and not self.prog.same_or_shrunk(a, f, ai) and self.prog.is_acc_arg(a, accs[ai]):
                cacc = accs[ai]
                its = self.prog.builds(self.strip(a))[1:]
                ets = []
                for it in its:
                    if kd == "S":
                        x = self.strip(it)
                        if self.prog.kind(x, self.kinds) == "C": self.gen_char_value(x); t = self.tmp(); ets.append(("chr", t)); self.emit("str x0, [x29, #%d]" % self.off(t), "累積に足す文字")
                        else: ets.append(("lit", x))
                    else:
                        self.gen(it); t = self.tmp(); ets.append(t)
                        self.emit("str x0, [x29, #%d]" % self.off(t), "累積に足す要素")
                t1 = self.tmp(); t2 = self.tmp()
                self.emit("ldr x0, [x29, #%d]" % self.off(self.slot[cacc]), "累積の器(自分の作業領域)")
                self.emit("ldr x1, [x29, #%d]" % self.off(self.slot[cacc] + 1))
                if kd == "S": self.emit("str x0, [x29, #%d]" % self.off(t1)); self.emit("str x1, [x29, #%d]" % self.off(t2), "(長さは書いたあとで決める)")
                else:
                    self.emit("add x1, x1, #%d" % len(ets), "伸びたあとの len")
                    self.emit("str x0, [x29, #%d]" % self.off(t1)); self.emit("str x1, [x29, #%d]" % self.off(t2))
                tmps.append(([t1, t2], kd)); gws.append((ets, kd, t1, t2, cacc))
                continue
            if kd in WIDE:
                if self.prog.kind(a, self.kinds) != kd and not (kd == "L" and self.prog.one_elem(a) is not None): raise AsmError("%s: %s を受ける仮引数に、別の種類の物が渡されています" % (f, {"L": "リスト", "S": "文字列", "N": "入れ子のリスト"}[kd]))
                self.load_list(a, "x0", "x1")
                if fl_mask and ai in mcells:
                    self.emit("str %s, [x29, #%d]" % ("x2" if self.prog.may_single(a, self.prog.sp, self.prog.relay) else "xzr", self.off(mcells[ai])), "旗(第 %d 引数)" % (ai + 1))
                if fl_relay and ai == self.prog.pure_relay(f):
                    self.emit("str %s, [x29, #%d]" % ("x2" if self.prog.may_single(a, self.prog.sp, self.prog.relay) else "xzr", self.off(fcell)), "旗(実引数から。戻ったあとに x2 へ置き直す)")
                t1 = self.tmp(); t2 = self.tmp()
                self.emit("str x0, [x29, #%d]" % self.off(t1), "実引数(ptr)")
                self.emit("str x1, [x29, #%d]" % self.off(t2), "実引数(len)")
                tmps.append(([t1, t2], kd))
            elif kd == "R":
                sa = self.strip(a)
                if self.prog.kind(a, self.kinds) != "R" and not (sa[0] == "bin" and sa[1] == "~" and self.prog.range_values(sa) is not None):
                    raise AsmError("%s: 規則を受ける仮引数に、別の種類の物が渡されています" % f)
                self.load_rule(a, "x0", "x1", "x2")
                ts = [self.tmp() for _ in range(3)]
                for t, rg, nm in zip(ts, ("x0", "x1", "x2"), ("start", "step", "end")): self.emit("str %s, [x29, #%d]" % (rg, self.off(t)), "実引数(%s)" % nm)
                tmps.append((ts, kd))
            elif kd == "C":
                if self.prog.kind(a, self.kinds) != "C": raise AsmError("%s: 文字の仮引数に、文字でない物が渡されています" % f)
                self.gen_char_value(a)
                t = self.tmp(); tmps.append(([t], kd))
                self.emit("str x0, [x29, #%d]" % self.off(t), "実引数(文字。`__` は U+0000)")
            else:
                if self.prog.kind(a, self.kinds) != "I": raise AsmError("%s: Int の仮引数に、Int でない物が渡されています" % f)
                lv = self.late_imm(a) if late_ok else None
                if lv is not None:
                    t = self.tmp(); tmps.append(([t], kd)); late[t] = lv
                else:
                    self.gen(a)
                    t = self.tmp(); tmps.append(([t], kd))
                    self.emit("str x0, [x29, #%d]" % self.off(t), "実引数")
        nslots = sum(len(ts) for ts, _ in tmps) + sum(sum(1 for e in gw[0] if (e[0] == "chr" if gw[1] == "S" else True)) for gw in gws)
        # 実引数に `__` があれば、本体は走らず呼び全体が `__`(処理系と同じ。引数の評価は全部済んでいる)
        unit_l = None; ovf_l = None
        marg = [i for i, a in enumerate(args) if pk[i] == "I" and self.mu(a)]
        warg = [i for i, a in enumerate(args) if pk[i] in WIDE and (self.is_call(a) or self.prog.kind(a, self.kinds) in WIDE and (self.strip(a)[0] == "cases" or self.strip(a)[0:2] == ("bin", "'")))]
        rk = self.prog.retk.get(f, "I")
        carg = [i for i, a in enumerate(args) if pk[i] == "C" and not (self.strip(a)[0] == "lit" or self.strip(a)[0] == "id" and self.strip(a)[1] in self.prog.chars)]
        if marg or warg or carg:
            unit_l = self.prog.label()
            vl = unit_l                                   # 実引数が `__` のときの行き先
            if id(n) in self.prog.part_trap:              # --strict: 余った関数が生きる呼び。`__` の実引数は罠で止める
                vl = ".Ltrap_part"; self.prog.part_used = True; self.prog.trap_used = True; self.prog.part_seen.add(id(n))
            for i in carg:
                self.emit("ldr x9, [x29, #%d]" % self.off(tmps[i][0][0]))
                self.emit("cbz x9, %s" % vl, "文字の実引数が __(U+0000)なら呼び全体が __")
            if marg: self.niche()
            for i in marg:
                t0 = tmps[i][0][0]
                if t0 in late: emit_imm(self.lines, "x9", late[t0], "実引数")
                else: self.emit("ldr x9, [x29, #%d]" % self.off(t0))
                self.emit("cmp x9, x13"); self.emit("b.eq %s" % vl, "引数が __ なら呼び全体が __")
            for i in warg:
                self.emit("ldr x9, [x29, #%d]" % self.off(tmps[i][0][1]), "器の len")
                self.emit("cbz x9, %s" % vl, "引数が __(len = 0)なら呼び全体が __")
        if gws:                                          # 作業領域に入らない伸びは、書く前に `__`(解析の見積もりが外れても、スタックを壊さない)
            if unit_l is None: unit_l = self.prog.label()
            if getattr(self.prog, "target", "bare") == "linux":
                ovf_l = self.prog.label(); self.prog.ovf_used = True   # linux では原因を 1 行 stderr に出してから __
            else:
                ovf_l = ".Ltrap_work"; self.prog.trap_used = True; self.prog.work_trap = True           # bare では黙って __ にせずトラップ
            gl = {x[0]: x[1] for x in [self.prog.grow[self.name]] + self.prog.grow_extra.get(self.name, [])}
            for gw in gws:
                pa_ = self.prog.fns[self.name].index(gw[4])
                self.emit("ldr x9, [x29, #%d]" % self.off(self.slot[gw[4]]), "累積の作業領域")
                self.emit("ldr x10, [x9, #-8]", "入る個数")
                self.emit("ldr x11, [x29, #%d]" % self.off(self.slot[gw[4]] + 1))
                self.emit("add x11, x11, #%d" % gl[pa_], "伸びたあとの個数")
                self.emit("cmp x11, x10"); self.emit("b.hi %s" % ovf_l, "作業領域に入らなければ呼び全体が __")
        if tail and f == self.name and self.entry and not any(self.prog.fresh_const(a, f, j) is not None and self.prog.is_mk(a) for j, a in enumerate(args)):
            # 自分への末尾呼び出し: 仮引数のスロットを新しい値で上書きして先頭へ飛ぶ(呼びの積み上がりが無い)
            for gw in gws: self.commit_grow(gw)
            for (ts, kd), p in zip(tmps, params):
                for j, t in enumerate(ts):
                    if t in late: emit_imm(self.lines, "x9", late[t], "実引数(字面)")
                    else: self.emit("ldr x9, [x29, #%d]" % self.off(t))
                    self.emit("str x9, [x29, #%d]" % self.off(self.slot[p] + j), "仮引数 %s を更新" % p)
            for _ in range(nslots): self.free()
            self.emit("b %s" % self.entry, "自分への末尾呼び出し")
            if ovf_l is not None and ovf_l != unit_l and ovf_l != ".Ltrap_work":
                self.lines.append("%s:" % ovf_l); self.emit("bl _sign_overflow", "作業領域に入らない伸び: 原因を 1 行出す(結果は __)")
            if unit_l:
                self.lines.append("%s:" % unit_l); self.unit_result(rk)
            return
        for gw in gws: self.commit_grow(gw)
        r = 0; extra = []
        for ts, kd in tmps:
            for t in ts:
                if r < len(ARG_REGS):
                    if t in late: emit_imm(self.lines, ARG_REGS[r], late[t], "実引数(字面)")
                    else: self.emit("ldr %s, [x29, #%d]" % (ARG_REGS[r], self.off(t)))
                else: extra.append(t)                       # 9 語目から先はスタックで渡す(AAPCS64: 呼ぶ側の sp の所から 8 バイトずつ)
                r += 1
        for _ in range(nslots): self.free()
        bd = self.prog.bound.get(f)
        if bd:
            if tail and self.sret:
                self.emit("ldr x8, [x29, #%d]" % self.off(self.sdest), "自分がもらった置き場をそのまま下へ渡す")
                self.emit("ldr x15, [x29, #%d]" % self.off(self.slim))
            elif inplace:
                self.emit("ldr x8, [x29, #%d]" % self.off(inplace[0]), "いま書いている位置へ直に書かせる")
                self.emit("ldr x15, [x29, #%d]" % self.off(inplace[1]), "そこに入る残りの個数")
            else:
                self.emit_slot(bd, self.prog.boundk.get(f) if rk == "N" else None, tmps, CW if rk == "S" else 8)
        if fl_mask:
            self.emit("mov x17, #0", "器の実引数の旗をビットで渡す")
            for j, c in mcells.items():
                self.emit("ldr x9, [x29, #%d]" % self.off(c))
                if j: self.emit("lsl x9, x9, #%d" % j)
                self.emit("add x17, x17, x9", "ビットは重ならない")
        if extra:
            area = 16 * ((len(extra) + 1) // 2)
            self.emit("sub sp, sp, #%d" % area, "スタックで渡す実引数 %d 語の置き場(呼びの直前に取り、呼びのあとで戻す)" % len(extra))
            for k, t in enumerate(extra):
                if t in late: emit_imm(self.lines, "x9", late[t], "実引数(字面)")
                else: self.emit("ldr x9, [x29, #%d]" % self.off(t))
                self.emit("str x9, [sp, #%d]" % (8 * k))
        self.emit("bl %s" % (symbol_of(f) + ".rec" if ((f == self.name and self.prog.grow.get(f)) or ringcall) else symbol_of(f)), "再帰の入口(作業領域は自分のものを渡す)" if ((f == self.name and self.prog.grow.get(f)) or ringcall) else None)
        if extra: self.emit("add sp, sp, #%d" % area)
        self.has_call = True
        if unit_l:
            done = self.prog.label()
            self.emit("b %s" % done)
            if ovf_l is not None and ovf_l != unit_l and ovf_l != ".Ltrap_work":
                self.lines.append("%s:" % ovf_l); self.emit("bl _sign_overflow", "作業領域に入らない伸び: 原因を 1 行出す(結果は __)")
            self.lines.append("%s:" % unit_l); self.unit_result(rk)
            self.lines.append("%s:" % done)
        if fl_relay:
            self.emit("ldr x2, [x29, #%d]" % self.off(fcell), "旗を置き直す"); self.free()
        for _ in mcells: self.free()

    def commit_grow(self, gw):
        """引数を全部評価し終えたあとで、累積の作業領域の末尾へ足す要素を書く(自分の長さは変えない。呼びの実引数は t1/t2 が持つ)。"""
        cacc = gw[4]
        if gw[1] == "L":
            self.emit("ldr x10, [x29, #%d]" % self.off(self.slot[cacc]), "累積の作業領域")
            self.emit("ldr x11, [x29, #%d]" % self.off(self.slot[cacc] + 1))
            self.emit("lsl x11, x11, #3"); self.emit("add x10, x10, x11", "いまの末尾")
            for i, t in enumerate(gw[0]):
                self.emit("ldr x9, [x29, #%d]" % self.off(t)); self.emit("str x9, [x10, #%d]" % (8 * i), "累積の末尾へ書く")
        elif gw:
            # 文字列の累積: 末尾の位置を持つセル(t2 を借りる)から、文字(U+0000 は消える)と字面を順に書き、長さを決める
            ets, _, t1, t2, _c = gw
            cur = self.tmp()
            self.emit("ldr x10, [x29, #%d]" % self.off(t1)); self.emit("ldr x11, [x29, #%d]" % self.off(t2)); self.emit("add x10, x10, x11, lsl #%d" % csh(), "いまの末尾")
            self.emit("str x10, [x29, #%d]" % self.off(cur))
            for kd2, d in ets:
                if kd2 == "chr":
                    sk = self.prog.label()
                    self.emit("ldr x0, [x29, #%d]" % self.off(d)); self.emit("cbz x0, %s" % sk, "U+0000(__)は並びから消える")
                    self.emit("ldr x9, [x29, #%d]" % self.off(cur)); self.emit("strb w0, [x9]" if CW == 1 else "str w0, [x9]"); self.emit("add x9, x9, #%d" % CW); self.emit("str x9, [x29, #%d]" % self.off(cur))
                    self.lines.append("%s:" % sk)
                else:
                    self.load_list(d, "x11", "x12"); self.copy_bytes(cur)
            self.emit("ldr x9, [x29, #%d]" % self.off(cur)); self.emit("ldr x10, [x29, #%d]" % self.off(t1)); self.emit("sub x9, x9, x10", "伸びたあとの長さ(バイト)")
            if CW == 4: self.emit("lsr x9, x9, #2", "文字数")
            self.emit("str x9, [x29, #%d]" % self.off(t2)); self.free()

    def emit_slot(self, bd, bk, tmps, esz=8):
        """返値の置き場を呼ぶ側が取る: `sub sp`、x8 = 置き場、x15 = 入る個数。bd = 上界 konst + Σ coef × ||器||(8 バイトの語の数)。
        入れ子の器(bk が None でない)は、置き場 = [記述子 16 × K][次に書く位置][終わり][内容 M 語]。x15 = K で、
        arena の頭(次に書く位置と終わり)は x8 + 16 × x15 にある(pass4.js emitContentArena)。呼ぶ側が頭を初期化する。"""
        from math import ceil
        if not bd[1]:
            bd = (ceil(bd[0]), bd[1])
            size = (esz * bd[0] + 15) // 16 * 16
            if size < 4096: self.emit("sub sp, sp, #%d" % size, "返値スロット(上界 %d 語)。呼ぶ側が取る" % bd[0])
            else: emit_imm(self.lines, "x9", size); self.emit("sub sp, sp, x9", "返値スロット(上界 %d 語)。呼ぶ側が取る" % bd[0])
            self.emit("mov x8, sp")
            if bk is None: self.emit("mov x15, #%d" % bd[0], "入る個数")
            else: emit_imm(self.lines, "x11", bd[0], "置き場の語数")
        else:
            # 上界 = 定数 + Σ 係数 × ||実引数の器||。実引数の長さは評価済みで、スロットに残っている
            emit_imm(self.lines, "x11", ceil(bd[0]), "上界: 定数ぶん")
            for j, c in sorted(bd[1].items(), key=str):
                if isinstance(j, int) and len(tmps[j][0]) == 1:           # Int の引数で回る回数を見積もる: 値(負なら 0)
                    lk = self.prog.label()
                    self.emit("ldr x9, [x29, #%d]" % self.off(tmps[j][0][0]), "第 %d 引数(Int)の値: 回る回数の見積もり" % (j + 1)); self.emit("cmp x9, #0"); self.emit("b.ge %s" % lk); self.emit("mov x9, #0")
                    self.lines.append("%s:" % lk)
                elif isinstance(j, int): self.emit("ldr x9, [x29, #%d]" % self.off(tmps[j][0][1]), "第 %d 引数の器の長さ" % (j + 1))
                else:
                    # 入れ子の引数: 内側の長さの総和(平らにしたときの要素数)を、記述子を端から辿って数える
                    lp, le = self.prog.label(), self.prog.label()
                    self.emit("ldr x12, [x29, #%d]" % self.off(tmps[j[1]][0][0]), "第 %d 引数の記述子の表" % (j[1] + 1))
                    self.emit("ldr x13, [x29, #%d]" % self.off(tmps[j[1]][0][1])); self.emit("mov x9, #0", "内側の長さの総和")
                    self.lines.append("%s:" % lp)
                    self.emit("cbz x13, %s" % le); self.emit("ldr x14, [x12, #8]"); self.emit("add x9, x9, x14")
                    self.emit("add x12, x12, #16"); self.emit("sub x13, x13, #1"); self.emit("b %s" % lp)
                    self.lines.append("%s:" % le)
                if c != 1:
                    num, den = (c.numerator, c.denominator) if hasattr(c, "numerator") else (c, 1)
                    self.emit("mov x10, #%d" % num); self.emit("mul x9, x9, x10", "係数")
                    if den != 1:
                        self.emit("add x9, x9, #%d" % (den - 1)); self.emit("mov x10, #%d" % den); self.emit("udiv x9, x9, x10", "分数の係数 %d/%d(切り上げ)" % (num, den))
                self.emit("add x11, x11, x9")
            if esz == 8: self.emit("lsl x9, x11, #3", "バイト数(1 語 8 バイト)")
            elif esz == 4: self.emit("lsl x9, x11, #2", "バイト数(1 文字 4 バイト)")
            else: self.emit("mov x9, x11", "バイト数(1 要素 1 バイト)")
            self.emit("add x9, x9, #15"); self.emit("and x9, x9, #0xfffffffffffffff0", "16 バイトへ丸める")
            self.emit("sub sp, sp, x9", "返値スロット。呼ぶ側が実行時の上界で取る")
            self.emit("mov x8, sp")
            if bk is None: self.emit("mov x15, x11", "入る個数")
        self.alloca += 1
        if bk is not None:
            if bk[1]: raise AsmError("内部の誤り: 入れ子の器の記述子の数が実行時に決まる形")
            self.emit("mov x15, #%d" % bk[0], "記述子の数 K")
            self.emit("lsl x9, x15, #4"); self.emit("add x9, x8, x9", "arena の頭 = 置き場 + 16 × K")
            self.emit("add x10, x9, #16"); self.emit("str x10, [x9]", "次に書く位置 = 内容の領域の先頭")
            self.emit("lsl x10, x11, #3"); self.emit("add x10, x8, x10"); self.emit("str x10, [x9, #8]", "終わり = 置き場の終わり")

    def strip(self, n):
        while n[0] == "block": n = n[1]
        return n

    # ---- 分岐 ----
    INV = {"lt": "ge", "ge": "lt", "le": "gt", "gt": "le", "eq": "ne", "ne": "eq"}
    CC = {"<": "lt", "<=": "le", ">": "gt", ">=": "ge", "=": "eq", "!=": "ne", "==": "eq", "!==": "ne"}     # 符号あり(Int)の条件コード。operator_table.js の asm 欄

    def unit_result(self, vk):
        """種類 vk の `__` を x0(と x1)へ。Int は niche、文字は U+0000、器は len = 0。"""
        if vk == "I": self.niche("x0")
        elif vk == "R": raise AsmError("規則を返す分岐に既定の行が無い形(`__` になりうる)はまだ出せません。規則の `__` は起点を niche にして運ぶので、使う側が毎回見ることになる")
        elif vk == "C": self.emit("mov x0, #0", "Char の `__` は U+0000")
        else: self.emit("mov x0, #0"); self.emit("mov x1, #0", "器の `__` は len = 0")

    def pre_grow(self):
        """伸びる累積引数を持つ関数の入口: 作業領域(||acc|| + d × ||食う器|| 語)を取り、累積をそこへ写して、仮引数をその作業領域に向ける。
        回るたびの末尾呼び出しは、この領域の末尾へ書き足すだけ(入口へ戻る飛び先はこの後ろ)。"""
        gr = self.prog.grow.get(self.name)
        if not gr: return
        self.pre_alloca = True
        for gr_ in [gr] + self.prog.grow_extra.get(self.name, []): self.pre_grow_one(gr_)
        self.entry_pos = len(self.lines)

    def pre_grow_one(self, gr):
        g, d, e = gr
        ps = self.prog.fns[self.name]
        cp, cl = self.slot[ps[g]], self.slot[ps[g]] + 1
        self.emit("ldr x9, [x29, #%d]" % self.off(cl), "累積の長さ")
        if isinstance(e, tuple):                      # 輪: 回る回数 ≤ 食える器の長さの総和
            self.emit("mov x10, #0")
            for e_ in e:
                if isinstance(e_, tuple): emit_imm(self.lines, "x3", e_[1], "回る回数の上界(証明した定数)"); self.emit("add x10, x10, x3"); continue
                if self.kinds[ps[e_]] == "I":                   # 回る回数を Int の値で見積もる(負なら 0)
                    lk = self.prog.label()
                    self.emit("ldr x3, [x29, #%d]" % self.off(self.slot[ps[e_]]), "回る回数の見積もり %s" % ps[e_]); self.emit("cmp x3, #0"); self.emit("b.ge %s" % lk); self.emit("mov x3, #0")
                    self.lines.append("%s:" % lk); self.emit("add x10, x10, x3"); continue
                self.emit("ldr x3, [x29, #%d]" % self.off(self.slot[ps[e_]] + 1), "食える器 %s の長さ" % ps[e_]); self.emit("add x10, x10, x3")
        else: self.emit("ldr x10, [x29, #%d]" % self.off(self.slot[ps[e]] + 1), "食う器の長さ(回る回数の上界)")
        emit_imm(self.lines, "x11", d, "1 回で伸びる個数")
        self.emit("mul x10, x10, x11"); self.emit("add x9, x9, x10", "作業領域の語数 = ||acc|| + d × ||食う器||")
        sh = csh() if self.kinds[ps[g]] == "S" else 3          # 文字列は Char の幅(ascii 1 バイト・utf32 4 バイト)、リストは 8 バイトの語
        self.emit("mov x10, x9", "作業領域に入る個数")
        if sh: self.emit("lsl x9, x9, #%d" % sh)
        self.emit("add x9, x9, #15"); self.emit("lsr x9, x9, #4"); self.emit("lsl x9, x9, #4", "16 バイトに切り上げ")
        self.emit("add x9, x9, #16", "先頭に 16 バイト(入る個数を置く)")
        self.emit("sub sp, sp, x9", "作業領域(入口で 1 回だけ。回っても積み上がらない)")
        self.emit("add x12, sp, #16")
        self.emit("str x10, [x12, #-8]", "入る個数(伸ばす前に確かめる)")
        l1, l2 = self.prog.label(), self.prog.label()
        self.emit("ldr x0, [x29, #%d]" % self.off(cp)); self.emit("ldr x1, [x29, #%d]" % self.off(cl)); self.emit("mov x14, #0")
        self.lines.append("%s:" % l1)
        self.emit("cmp x14, x1"); self.emit("b.hs %s" % l2)
        if sh == 3: self.emit("ldr x3, [x0, x14, lsl #3]"); self.emit("str x3, [x12, x14, lsl #3]")
        elif sh == 2: self.emit("ldr w3, [x0, x14, lsl #2]"); self.emit("str w3, [x12, x14, lsl #2]")
        else: self.emit("ldrb w3, [x0, x14]"); self.emit("strb w3, [x12, x14]")
        self.emit("add x14, x14, #1"); self.emit("b %s" % l1)
        self.lines.append("%s:" % l2)
        self.emit("str x12, [x29, #%d]" % self.off(cp), "仮引数 %s を作業領域へ向ける" % ps[g])

    def gen_copy_result(self, v, vk):
        """累積(入口の作業領域にある)をそのまま返す枝: 作業領域は関数を抜けると捨てるので、置き場へ写す。入らなければ `__`。x0 = 先頭、x1 = 長さ。"""
        fail, done = self.prog.label(), self.prog.label()
        self.load_list(v, "x11", "x12")
        self.emit("ldr x10, [x29, #%d]" % self.off(self.slim), "置き場に入る個数")
        self.emit("cmp x12, x10"); self.emit("b.hi %s" % fail, "入らなければ `__`")
        cur = self.tmp()
        self.emit("ldr x9, [x29, #%d]" % self.off(self.sdest)); self.emit("str x9, [x29, #%d]" % self.off(cur))
        ln = self.tmp()
        self.emit("str x12, [x29, #%d]" % self.off(ln))
        (self.copy_words if vk == "L" else self.copy_bytes)(cur)
        self.emit("ldr x0, [x29, #%d]" % self.off(self.sdest)); self.emit("ldr x1, [x29, #%d]" % self.off(ln))
        self.free(); self.free()
        self.emit("b %s" % done)
        self.lines.append("%s:" % fail); self.unit_result(vk)
        self.lines.append("%s:" % done)

    def gen_any(self, v, tail, vk):
        """種類 vk の値になる項を x0(と x1)へ。旗を運ぶ関数(最上位で『1 個だけ残ると Int』になりうる結果を作る)は、返すたびに x2 に旗を置く。"""
        self._gen_any(v, tail, vk)
        if vk == "L" and self.name in self.prog.flagfns:
            w = self.strip(v)
            if w[0] == "cases" or self.prog.builds(w) is not None: return
            if self.name in self.prog.maskfns and w[0] == "id" and w[1] in self.slot and self.kinds[w[1]] == "L":
                j = self.prog.fns[self.name].index(w[1])
                self.emit("ldr x9, [x29, #%d]" % self.off(self.mcell), "旗: 第 %d 引数の旗" % (j + 1))
                if j: self.emit("lsr x9, x9, #%d" % j)
                self.emit("and x2, x9, #1"); return
            if self.is_call(w) and w[1][0][0] == "id" and (w[1][0][1] in self.prog.flagfns or w[1][0][1] in self.prog.flagrelay): return
            self.emit("mov x2, #0", "旗: 組み立てた 1 個ではない")

    def _gen_any(self, v, tail, vk):
        while v[0] == "block" and len(v) == 2: v = v[1]          # 共通部分式の印つきの括り(長さ 4)は残す: gen が値を置く・読む
        if vk == "I": return self.gen(v, tail)
        if v[0] == "cases": return self.gen_cases(v, tail, vk)
        if v == ("id", "__"): return self.unit_result(vk)
        if self.is_call(v): return self.gen_call(v, tail)
        if self.prog.grow.get(self.name) and vk in ("L", "S") and self.prog.builds(v) is None and self.sret:
            return self.gen_copy_result(v, vk)
        if vk == "L" and self.prog.builds(v) is not None: return self.gen_build(v)
        if vk == "N" and self.prog.builds(v) is not None: return self.gen_build_nest(v)
        if vk == "S" and self.prog.builds(v) is not None: return self.gen_build_str(v)
        if vk == "R": return self.load_rule(v, "x0", "x1", "x2")
        if vk == "C": return self.gen_char_value(v)
        self.load_list(v, "x0", "x1")

    # ---- 規則(レンジ) {start, step, end}: メモリ上に無く、3 本のレジスタで値渡し ----
    def emit_rule_count(self, rs, rst, re_, dst):
        """要素数 = (end - start) / step + 1(向きが逆なら 0)を dst へ。x13 を壊す。溢れは罠(Int の算術)。"""
        self.prog.trap_used = True
        zero, one, done = self.prog.label(), self.prog.label(), self.prog.label()
        self.emit("subs %s, %s, %s" % (dst, re_, rs), "end - start")
        self.emit("ccmp xzr, %s, #1, vc" % dst); self.emit("b.vs .Ltrap")
        self.emit("cbz %s, %s" % (dst, one), "始まりと終わりが同じなら 1 個")
        self.emit("eor x13, %s, %s" % (dst, rst)); self.emit("tbnz x13, #63, %s" % zero, "歩幅の向きが逆なら 0 個")
        self.emit("sdiv %s, %s, %s" % (dst, dst, rst), "歩幅で割る(走査は要らない。list_model.md §2.3)")
        self.emit("adds %s, %s, #1" % (dst, dst), "+1(終わりを含む)")
        self.emit("ccmp xzr, %s, #1, vc" % dst); self.emit("b.vs .Ltrap")
        self.emit("b %s" % done)
        self.lines.append("%s:" % one); self.emit("mov %s, #1" % dst); self.emit("b %s" % done)
        self.lines.append("%s:" % zero); self.emit("mov %s, #0" % dst)
        self.lines.append("%s:" % done)

    def gen_rule(self, n):
        """範囲の式 `[a ~ b]` `[a ~+ s ~ b]` を 3 つ組にして x0, x1, x2 へ。歩幅を書かない形は始まりと終わりの大小で ±1 にして畳む。
        要素数の計算(溢れは罠)をここで一度通しておくので、規則を受け取る側は溢れを気にしなくてよい。歩幅 0 は進まないので罠。"""
        lo, step, hi = self.prog.rule_parts(n)
        for x in (lo, step, hi):
            if x is None: continue
            if self.prog.kind(x, self.kinds) != "I": raise AsmError("規則の端点・歩幅は Int だけです")
            if self.mu(x): raise AsmError("端点・歩幅が `__` になりうる規則はまだ出せません(`__` の規則は起点を niche にして運ぶ)")
        cells = []
        for x in (lo, step, hi):
            if x is None: continue
            self.gen(x); t = self.tmp(); cells.append(t)
            self.emit("str x0, [x29, #%d]" % self.off(t))
        self.emit("ldr x9, [x29, #%d]" % self.off(cells[0]), "start")
        self.emit("ldr x12, [x29, #%d]" % self.off(cells[-1]), "end")
        if step is not None:
            self.prog.trap_used = True
            self.emit("ldr x10, [x29, #%d]" % self.off(cells[1]), "step")
            self.emit("cbz x10, .Ltrap", "歩幅 0 は進まない(処理系は『派生範囲が進みません』)")
        else:
            self.emit("cmp x9, x12"); self.emit("mov x10, #1"); self.emit("movn x14, #0", "−1")
            self.emit("csel x10, x10, x14, le", "昇順なら +1、降順なら −1(歩幅に畳む)")
        self.emit_rule_count("x9", "x10", "x12", "x14")
        self.emit("mov x0, x9"); self.emit("mov x1, x10"); self.emit("mov x2, x12")
        for _ in cells: self.free()

    def load_rule(self, n, r0, r1, r2):
        """規則を表す項 n の start, step, end を r0, r1, r2 へ。"""
        n = self.strip(n)
        if n[0] == "id" and n[1] in self.slot and self.kinds[n[1]] == "R":
            c = self.slot[n[1]]
            for j, (r, nm) in enumerate(zip((r0, r1, r2), ("start", "step", "end"))):
                self.emit("ldr %s, [x29, #%d]" % (r, self.off(c + j)), n[1] + "." + nm)
            return
        if n[0] == "bin" and n[1] == "~":
            rv = self.prog.range_values(n)
            if rv is not None:                                 # 端が定数の範囲: 3 つ組を即値で
                st = (rv[1] - rv[0]) if len(rv) > 1 else 1
                for r, v in zip((r0, r1, r2), (rv[0], st, rv[-1])): emit_imm(self.lines, r, v)
                return
            self.gen_rule(n)
        elif self.is_call(n) or n[0] == "cases":
            if n[0] == "cases": self.gen_cases(n, False, "R")
            else: self.gen_call(n)
        else:
            raise AsmError("規則の形がまだ出せません(範囲の式・規則を渡された仮引数・規則を返す関数だけ)")
        for r, src in ((r0, "x0"), (r1, "x1"), (r2, "x2")):
            if r != src: self.emit("mov %s, %s" % (r, src))

    def gen_index_rule(self, l, r):
        """`規則 ' i`: 添字を 0 〜 個数-1(負は後ろから)に均し、start + i × step。外れれば `__`。ロードではなく算術。"""
        if self.prog.kind(r, self.kinds) != "I": raise AsmError("添字は Int だけです")
        self.gen(r); self.emit("mov x11, x0")
        unit, done, pos = self.prog.label(), self.prog.label(), self.prog.label()
        if self.mu(r):
            self.niche(); self.emit("cmp x11, x13"); self.emit("b.eq %s" % unit, "添字が __ なら __")
        ll = self.strip(l)
        if self.is_call(ll) or ll[0] == "cases":
            t = self.tmp(); self.emit("str x11, [x29, #%d]" % self.off(t), "添字を預ける")
            self.load_rule(l, "x9", "x10", "x12")
            self.emit("ldr x11, [x29, #%d]" % self.off(t)); self.free()
        else:
            self.load_rule(l, "x9", "x10", "x12")
        self.emit_rule_count("x9", "x10", "x12", "x14")
        self.emit("cmp x11, #0"); self.emit("b.ge %s" % pos)
        self.emit("add x11, x11, x14", "負の添字は後ろから")
        self.lines.append("%s:" % pos)
        self.emit("cmp x11, x14"); self.emit("b.hs %s" % unit, "範囲の外(均しても負なら符号なしで大きいので同じ)。要素は無い")
        self.emit("mul x13, x11, x10"); self.emit("add x0, x9, x13", "start + i × step")
        self.emit("b %s" % done)
        self.lines.append("%s:" % unit); self.niche("x0")
        self.lines.append("%s:" % done)

    def spread_total(self, x):
        """展開 `x~` の要素の総数を x12 へ(x11, x13, x14 を壊す)。入れ子は内側の長さの総和。"""
        if self.prog.kind(x, self.kinds) != "N": self.load_list(x, "x11", "x12"); return
        self.prog.note_unsafe("入れ子の展開 `m~`(仮引数・呼びの結果)。スカラーが混ざる入れ子があるプログラムでは、展開の結果が実行時の中身で変わる(要素がリストだけなら平ら、スカラーが混ざれば入れ子のまま)ので、結果の種類が静的に決まらない。字面の名前の入れ子の展開は出せる")
        lp, le = self.prog.label(), self.prog.label()
        self.load_list(x, "x11", "x13"); self.emit("mov x12, #0", "内側の長さの総和")
        self.lines.append("%s:" % lp)
        self.emit("cbz x13, %s" % le); self.emit("ldr x14, [x11, #8]"); self.emit("add x12, x12, x14")
        self.emit("add x11, x11, #16"); self.emit("sub x13, x13, #1"); self.emit("b %s" % lp)
        self.lines.append("%s:" % le)

    def flat_total_regs(self):
        """x11 = 記述子の並び、x12 = 内側の数 のとき、内側の長さの総和を x12 へ(x11, x13, x14 を壊す)。"""
        self.prog.note_unsafe("入れ子の展開 `m~`(仮引数・呼びの結果)。スカラーが混ざる入れ子があるプログラムでは、展開の結果が実行時の中身で変わる(要素がリストだけなら平ら、スカラーが混ざれば入れ子のまま)ので、結果の種類が静的に決まらない。字面の名前の入れ子の展開は出せる")
        lp, le = self.prog.label(), self.prog.label()
        self.emit("mov x13, x12"); self.emit("mov x12, #0", "内側の長さの総和")
        self.lines.append("%s:" % lp)
        self.emit("cbz x13, %s" % le); self.emit("ldr x14, [x11, #8]"); self.emit("add x12, x12, x14")
        self.emit("add x11, x11, #16"); self.emit("sub x13, x13, #1"); self.emit("b %s" % lp)
        self.lines.append("%s:" % le)

    def flat_copy_regs(self, cur):
        """x11 = 記述子の並び、x12 = 内側の数 のとき、内側を端から平らに、セル cur の位置から書いて進める。"""
        self.prog.note_unsafe("入れ子の展開 `m~`(仮引数・呼びの結果)。スカラーが混ざる入れ子があるプログラムでは、展開の結果が実行時の中身で変わる(要素がリストだけなら平ら、スカラーが混ざれば入れ子のまま)ので、結果の種類が静的に決まらない。字面の名前の入れ子の展開は出せる")
        lp, le, nx, ni = (self.prog.label() for _ in range(4))
        self.emit("ldr x9, [x29, #%d]" % self.off(cur))
        self.lines.append("%s:" % lp)
        self.emit("cbz x12, %s" % le)
        self.emit("ldr x13, [x11]", "内側の先頭"); self.emit("ldr x10, [x11, #8]", "内側の長さ")
        self.lines.append("%s:" % ni)
        self.emit("cbz x10, %s" % nx)
        self.emit("ldr x14, [x13]"); self.emit("str x14, [x9]")
        self.emit("add x13, x13, #8"); self.emit("add x9, x9, #8"); self.emit("sub x10, x10, #1"); self.emit("b %s" % ni)
        self.lines.append("%s:" % nx)
        self.emit("add x11, x11, #16"); self.emit("sub x12, x12, #1"); self.emit("b %s" % lp)
        self.lines.append("%s:" % le)
        self.emit("str x9, [x29, #%d]" % self.off(cur), "書く位置を進める")

    def copy_words(self, cur):
        """x11 の指す x12 語を、セル cur が持つ位置から書き、位置を進める。"""
        lp, le = self.prog.label(), self.prog.label()
        self.emit("ldr x9, [x29, #%d]" % self.off(cur)); self.emit("mov x14, #0")
        self.lines.append("%s:" % lp)
        self.emit("cmp x14, x12"); self.emit("b.hs %s" % le)
        self.emit("ldr x13, [x11, x14, lsl #3]"); self.emit("str x13, [x9, x14, lsl #3]")
        self.emit("add x14, x14, #1"); self.emit("b %s" % lp)
        self.lines.append("%s:" % le)
        self.emit("add x9, x9, x12, lsl #3", "書く位置を進める"); self.emit("str x9, [x29, #%d]" % self.off(cur))

    def spread_copy(self, x, cur):
        """展開 `x~` の要素を、フレームのセル cur が持つ位置から順に書き、位置を進める(入れ子は内側を端から平らに)。"""
        lp, le = self.prog.label(), self.prog.label()
        if self.prog.kind(x, self.kinds) != "N":
            self.load_list(x, "x11", "x12")
            self.copy_words(cur)
            return
        nx, ni = self.prog.label(), self.prog.label()
        self.load_list(x, "x11", "x12"); self.emit("ldr x9, [x29, #%d]" % self.off(cur))
        self.lines.append("%s:" % lp)
        self.emit("cbz x12, %s" % le)
        self.emit("ldr x13, [x11]", "内側の先頭"); self.emit("ldr x10, [x11, #8]", "内側の長さ")
        self.lines.append("%s:" % ni)
        self.emit("cbz x10, %s" % nx)
        self.emit("ldr x14, [x13]"); self.emit("str x14, [x9]")
        self.emit("add x13, x13, #8"); self.emit("add x9, x9, #8"); self.emit("sub x10, x10, #1"); self.emit("b %s" % ni)
        self.lines.append("%s:" % nx)
        self.emit("add x11, x11, #16"); self.emit("sub x12, x12, #1"); self.emit("b %s" % lp)
        self.lines.append("%s:" % le)
        self.emit("str x9, [x29, #%d]" % self.off(cur), "書く位置を進める")

    def gen_build(self, n):
        """要素を式で組み立てて(`x~` は展開して繋いで)返す: もらった置き場(x8)へ左から書き、x0 = 先頭、x1 = 個数。
        要る個数を先に数えて、もらった個数(x15)に入らなければ何も書かずに器を作らない(`__`。stack_abi.md §4.7)。
        展開が器を組み立てて返す関数の呼び(`(f xs)~`。再帰を含む)で、そういう呼びがその並びに 1 つだけなら、その関数には新しい置き場を取らずに
        いま書いている位置へ直に書かせる(入る個数は『全体 - 先に数えた分』)。上界は呼び先の上界で足りる。
        ほかの呼びは先に 1 度だけ呼んで結果を写す(2 度呼ぶと再帰が指数になる)。"""
        if not self.sret: raise AsmError("組み立てた器は、返す位置でしか作れません(置き場を呼ぶ側がくれる関数の返値だけ)")
        items = self.prog.builds(n)
        infos = []
        for it in items:
            ty, x = self.prog.item_info(it)
            kx = self.prog.kind(x, self.kinds)
            if ty == "scalar":
                if kx != "I": raise AsmError("並びの要素にリストがあります(入れ子)。平らに繋ぐには `xs~` と展開してください(`xs ys` は入れ子、`xs~ ys~` が連結。operator_table.md の unshift / concat)")
            else:
                if kx not in ("L", "N"): raise AsmError("展開(~)できるのはリストと入れ子のリストだけです(文字列・Int はまだ)")
            infos.append((ty, x))
        hoisted = self.build_hoist(infos)            # --par: 要素の中の独立な純粋な呼び出しは、先に並列で評価して名前に置く
        calls = [i for i, (ty, x) in enumerate(infos) if ty == "spread" and self.is_call(x)]
        bcalls = [i for i in calls if self.prog.builder_call(infos[i][1]) and self.prog.kind(infos[i][1], self.kinds) == "L"]
        inpl = bcalls[0] if len(bcalls) == 1 else None
        # `__` になりうる要素(`xs ' 5` が範囲の外、など)は並びから消える: 個数が実行時に決まる。値は 1 度だけ評価してセルに預け、数える・書くで使う
        mscalar = [i for i, (t, x) in enumerate(infos) if t == "scalar" and self.mu(x)]
        nscalar = sum(1 for i, (t, _) in enumerate(infos) if t == "scalar" and i not in mscalar)
        fail, done = self.prog.label(), self.prog.label()
        tot, cap = self.tmp(), self.tmp()
        cells = {i: (self.tmp(), self.tmp()) for i in calls if i != inpl}
        mcells = {i: self.tmp() for i in mscalar}
        emit_imm(self.lines, "x9", nscalar, "要る個数(定数ぶん)")
        self.emit("str x9, [x29, #%d]" % self.off(tot))
        for i in mscalar:
            sk = self.prog.label()
            self.gen(infos[i][1]); self.emit("str x0, [x29, #%d]" % self.off(mcells[i]), "`__` になりうる要素(1 度だけ評価)")
            self.niche(); self.emit("cmp x0, x13"); self.emit("b.eq %s" % sk, "__ は並びから消える")
            self.emit("ldr x9, [x29, #%d]" % self.off(tot)); self.emit("add x9, x9, #1"); self.emit("str x9, [x29, #%d]" % self.off(tot))
            self.lines.append("%s:" % sk)
        for i, (ty, x) in enumerate(infos):
            if ty != "spread" or i == inpl: continue
            if i in cells:
                self.load_list(x, "x11", "x12")
                self.emit("str x11, [x29, #%d]" % self.off(cells[i][0]), "呼びの結果(先に 1 度だけ呼ぶ)"); self.emit("str x12, [x29, #%d]" % self.off(cells[i][1]))
                if self.prog.kind(x, self.kinds) == "N": self.flat_total_regs()          # 入れ子を返す呼びの展開: 内側を端から平らに(内側の長さの総和)
            else: self.spread_total(x)
            self.emit("ldr x9, [x29, #%d]" % self.off(tot)); self.emit("add x9, x9, x12", "展開する器の長さを足す")
            self.emit("str x9, [x29, #%d]" % self.off(tot))
        self.emit("ldr x9, [x29, #%d]" % self.off(tot))
        self.emit("ldr x10, [x29, #%d]" % self.off(self.slim), "置き場に入る個数")
        self.emit("cmp x9, x10"); self.emit("b.hi %s" % fail, "入らなければ何も書かず、器は作らない(`__`)")
        if inpl is not None:
            self.emit("sub x10, x10, x9"); self.emit("str x10, [x29, #%d]" % self.off(cap), "直に書かせる呼びに残す個数")
        self.emit("ldr x9, [x29, #%d]" % self.off(self.sdest))
        self.emit("str x9, [x29, #%d]" % self.off(self.scur), "書く位置")
        for i, (ty, x) in enumerate(infos):
            if ty == "scalar":
                sk = self.prog.label()
                if i in mcells:
                    self.emit("ldr x0, [x29, #%d]" % self.off(mcells[i])); self.niche(); self.emit("cmp x0, x13"); self.emit("b.eq %s" % sk, "__ は書かない")
                else: self.gen(x)
                self.emit("ldr x9, [x29, #%d]" % self.off(self.scur))
                self.emit("str x0, [x9]"); self.emit("add x9, x9, #8"); self.emit("str x9, [x29, #%d]" % self.off(self.scur))
                self.lines.append("%s:" % sk)
            elif i == inpl:
                self.gen_call(self.strip(x), False, (self.scur, cap))
                ski, dni = self.prog.label(), self.prog.label()
                self.emit("ldr x9, [x29, #%d]" % self.off(self.scur)); self.emit("cbz x1, %s" % ski, "`__`(0 個)は進めない")
                self.emit("cmp x0, x9"); self.emit("b.eq %s" % ski, "置き場に直に書いてきた")
                self.emit("mov x11, x0"); self.emit("mov x12, x1", "字面の像など、置き場の外の器を返した(底の行が字面だけの関数): 書き先へ写す")
                self.copy_words(self.scur); self.emit("b %s" % dni)
                self.lines.append("%s:" % ski)
                self.emit("ldr x9, [x29, #%d]" % self.off(self.scur)); self.emit("add x9, x9, x1, lsl #3", "返ってきた個数ぶん位置を進める(`__` なら 0)")
                self.emit("str x9, [x29, #%d]" % self.off(self.scur))
                self.lines.append("%s:" % dni)
            elif i in cells:
                self.emit("ldr x11, [x29, #%d]" % self.off(cells[i][0])); self.emit("ldr x12, [x29, #%d]" % self.off(cells[i][1]))
                if self.prog.kind(x, self.kinds) == "N": self.flat_copy_regs(self.scur)
                else: self.copy_words(self.scur)
            else:
                self.spread_copy(x, self.scur)
        self.emit("ldr x0, [x29, #%d]" % self.off(self.sdest))
        self.emit("ldr x1, [x29, #%d]" % self.off(self.scur))
        self.emit("sub x1, x1, x0"); self.emit("lsr x1, x1, #3", "個数")
        self.emit("b %s" % done)
        self.lines.append("%s:" % fail); self.unit_result("L")
        self.lines.append("%s:" % done)
        if self.name in self.prog.flagfns:
            sk = self.prog.label()
            self.emit("mov x2, #0", "旗: 組み立てた結果が 1 個だけ(処理系は Int)なら 1")
            if mscalar: self.emit("cmp x1, #1"); self.emit("b.ne %s" % sk); self.emit("mov x2, #1"); self.lines.append("%s:" % sk)
        for _ in range(2 + 2 * len(cells) + len(mcells)): self.free()
        if hoisted:
            for nm in hoisted[0]: del self.slot[nm]; del self.kinds[nm]
            for _ in hoisted[1]: self.free()

    def gen_dyn_init(self, dynn):
        """起動のとき、値が計算で決まる定義(`a : fib 30`)を源の順に評価して、セルに置く。続く定義が互いの名前を使わないかぎり(同じ組)、
        組の中の独立な純粋な呼び出しは、先に全部並列で評価する(--par)。"""
        i = 0
        while i < len(dynn):
            grp = [dynn[i]]; names = {dynn[i][1]}; j = i + 1
            def ids(x, acc):
                if isinstance(x, tuple) and x:
                    if x[0] == "id" and len(x) == 2: acc.add(x[1])
                    else:
                        for y in x[1:]: ids(y, acc)
                elif isinstance(x, list):
                    for y in x: ids(y, acc)
                return acc
            while j < len(dynn):
                u = ids(dynn[j][2], set())
                for h in list(u):
                    if h in self.prog.fns: u |= self.prog.fn_dyn_refs(h)
                if u & names: break
                grp.append(dynn[j]); names.add(dynn[j][1]); j += 1
            i = j
            exprs = [d[2] for d in grp]; vals = []; pre = None
            hn = []
            if PAR[0] is not None and getattr(self.prog, "target", "bare") == "linux":
                pl = self.hoist_plan(exprs)
                if pl is not None:
                    hn, vals = self.hoist_exec(pl[0]); exprs = pl[1]
            for d, x in zip(grp, exprs):
                self.gen(x)
                lb = dyn_label(d[1])
                self.emit("adrp x9, %s" % lb, "定義 %s の値を置く" % d[1]); self.emit("add x9, x9, :lo12:%s" % lb); self.emit("str x0, [x9]")
            for nm in hn: del self.slot[nm]; del self.kinds[nm]
            for _ in vals: self.free()

    def build_hoist(self, infos):
        """並びの要素(`(f a) (g b) (h c)`、`(f a) + 1` など。展開でない要素)のうち、独立な純粋な整数関数の呼び出しが 2 つ以上あれば、先に全部を並列で評価してスロットに置き、
        要素はその名前に替える(infos をその場で書き換える)。(名前の並び, スロットの並び) か None。要素の値は呼び出しが先に済むだけで変わらない(純粋で `__` にならない呼びだけ)。"""
        if PAR[0] is None or getattr(self.prog, "target", "bare") != "linux": return None
        idx = [i for i, (ty, x) in enumerate(infos) if ty == "scalar"]
        pl = self.hoist_plan([infos[i][1] for i in idx])
        if pl is None: return None
        names, vals = self.hoist_exec(pl[0])
        for i, x in zip(idx, pl[1]): infos[i] = (infos[i][0], x)
        return names, vals

    def copy_bytes(self, cur, narrow=False):
        """x11 の指す x12 バイトを、セル cur が持つ位置から書き、位置を進める。"""
        lp, le = self.prog.label(), self.prog.label()
        self.emit("ldr x9, [x29, #%d]" % self.off(cur)); self.emit("mov x14, #0")
        self.lines.append("%s:" % lp)
        self.emit("cmp x14, x12"); self.emit("b.hs %s" % le)
        if CW == 1: self.emit("ldrb w13, [x11, x14]"); self.emit("strb w13, [x9, x14]")
        elif narrow: self.emit("ldrb w13, [x11, x14]"); self.emit("str w13, [x9, x14, lsl #2]")
        else: self.emit("ldr w13, [x11, x14, lsl #2]"); self.emit("str w13, [x9, x14, lsl #2]")
        self.emit("add x14, x14, #1"); self.emit("b %s" % lp)
        self.lines.append("%s:" % le)
        self.emit("add x9, x9, x12, lsl #%d" % csh()); self.emit("str x9, [x29, #%d]" % self.off(cur))

    def gen_build_str(self, n):
        """文字列の連結 `a b`(文字列・文字の並置。余積): もらった置き場(x8)へ左から 1 バイトずつ書く。x0 = 先頭、x1 = 長さ。
        `__` の要素(長さ 0 の文字列・U+0000 の文字)は並びから消える(何も足さない)。器を組み立てて返す関数の結果は、
        先に呼んで置き場へ写す。要る長さを先に数え、もらった個数(x15)に入らなければ何も書かずに `__`。"""
        if not self.sret: raise AsmError("組み立てた器は、返す位置でしか作れません(置き場を呼ぶ側がくれる関数の返値だけ)")
        plan = []
        for it in self.prog.builds(n):
            ty, x = self.prog.item_info(it)
            xs = self.strip(x); kx = self.prog.kind(xs, self.kinds)
            if ty != "scalar" or kx not in ("S", "C", "I"): raise AsmError("文字列の連結で並べられるのは、文字列・文字・数だけです")
            plan.append(("chr", xs) if kx == "C" else ("int", xs) if kx == "I" else ("call", xs) if self.prog.builder_call(xs) else ("str", xs))
        self.prog.str_cost(self.prog.builds(n), None if self.name == "_.main" else self.name)
        fail, done = self.prog.label(), self.prog.label()
        bc = [i for i, (kd, d) in enumerate(plan) if kd == "call"]
        inpl = bc[0] if len(bc) == 1 else None            # 器を組み立てて返す呼びが 1 つだけなら、置き場を取らずに直に書かせる
        tot = self.tmp(); cap = self.tmp(); cells = {}; bufs = {}; ccells = {}
        for i, (kd, d) in enumerate(plan):
            if kd in ("call", "int") and i != inpl: cells[i] = (self.tmp(), self.tmp())
            if kd == "int": bufs[i] = [self.tmp(), self.tmp(), self.tmp()]          # 十進の綴りを書く 24 バイト(連続したセル)
            if kd == "chr": ccells[i] = self.tmp()                                  # 文字は 1 度だけ評価して預ける(数える段と書く段で使う)
        self.emit("mov x9, #0"); self.emit("str x9, [x29, #%d]" % self.off(tot), "要る長さ")
        for i, (kd, d) in enumerate(plan):
            skip = self.prog.label()
            if i == inpl: continue
            if kd == "int":
                z, dn, lp, pos = (self.prog.label() for _ in range(4))
                end = self.off(bufs[i][0]) + 24
                self.gen(d)
                self.emit("add x9, x29, #%d" % end, "綴りの終わり(右詰めで書く)")
                if self.mu(d): self.niche(); self.emit("cmp x0, x13"); self.emit("b.eq %s" % z, "__ は並びから消える(長さ 0)")
                self.emit("mov x11, x0"); self.emit("cmp x0, #0"); self.emit("cneg x0, x0, lt", "絶対値"); self.emit("mov x12, #10")
                self.lines.append("%s:" % lp)
                self.emit("udiv x13, x0, x12"); self.emit("msub x14, x13, x12, x0"); self.emit("add x14, x14, #48")
                self.emit("sub x9, x9, #1"); self.emit("strb w14, [x9]"); self.emit("mov x0, x13"); self.emit("cbnz x0, %s" % lp)
                self.emit("tbz x11, #63, %s" % pos); self.emit("mov w10, #45", "'-'"); self.emit("sub x9, x9, #1"); self.emit("strb w10, [x9]")
                self.lines.append("%s:" % pos)
                self.emit("b %s" % dn)
                self.lines.append("%s:" % z)
                self.emit("add x9, x29, #%d" % end)
                self.lines.append("%s:" % dn)
                self.emit("add x12, x29, #%d" % end); self.emit("sub x12, x12, x9", "綴りの長さ")
                self.emit("str x9, [x29, #%d]" % self.off(cells[i][0]), "綴りの先頭"); self.emit("str x12, [x29, #%d]" % self.off(cells[i][1]))
                self.emit("ldr x9, [x29, #%d]" % self.off(tot)); self.emit("add x9, x9, x12"); self.emit("str x9, [x29, #%d]" % self.off(tot))
            elif kd == "chr":
                self.gen_char_value(d); self.emit("str x0, [x29, #%d]" % self.off(ccells[i]), "文字(1 度だけ評価)")
                self.emit("cbz x0, %s" % skip, "U+0000(__)は並びから消える")
                self.emit("ldr x9, [x29, #%d]" % self.off(tot)); self.emit("add x9, x9, #1"); self.emit("str x9, [x29, #%d]" % self.off(tot))
                self.lines.append("%s:" % skip)
            else:
                self.load_list(d, "x11", "x12")
                if kd == "call":
                    self.emit("str x11, [x29, #%d]" % self.off(cells[i][0]), "結果の先頭(この関数の一時の置き場)"); self.emit("str x12, [x29, #%d]" % self.off(cells[i][1]))
                self.emit("ldr x9, [x29, #%d]" % self.off(tot)); self.emit("add x9, x9, x12"); self.emit("str x9, [x29, #%d]" % self.off(tot))
        self.emit("ldr x9, [x29, #%d]" % self.off(tot)); self.emit("ldr x10, [x29, #%d]" % self.off(self.slim), "置き場に入る長さ")
        self.emit("cmp x9, x10"); self.emit("b.hi %s" % fail, "入らなければ何も書かず、器は作らない(`__`)")
        if inpl is not None: self.emit("sub x10, x10, x9"); self.emit("str x10, [x29, #%d]" % self.off(cap), "直に書かせる呼びに残す長さ")
        self.emit("ldr x9, [x29, #%d]" % self.off(self.sdest)); self.emit("str x9, [x29, #%d]" % self.off(self.scur), "書く位置")
        for i, (kd, d) in enumerate(plan):
            if kd == "chr":
                skip = self.prog.label()
                self.emit("ldr x0, [x29, #%d]" % self.off(ccells[i])); self.emit("cbz x0, %s" % skip)
                self.emit("ldr x9, [x29, #%d]" % self.off(self.scur)); self.emit("strb w0, [x9]" if CW == 1 else "str w0, [x9]"); self.emit("add x9, x9, #%d" % CW)
                self.emit("str x9, [x29, #%d]" % self.off(self.scur))
                self.lines.append("%s:" % skip)
            elif i == inpl:
                self.gen_call(d, False, (self.scur, cap))
                self.emit("ldr x9, [x29, #%d]" % self.off(self.scur)); self.emit("add x9, x9, x1, lsl #%d" % csh(), "返ってきた長さぶん位置を進める(`__` なら 0)")
                self.emit("str x9, [x29, #%d]" % self.off(self.scur))
            else:
                if kd in ("call", "int"): self.emit("ldr x11, [x29, #%d]" % self.off(cells[i][0])); self.emit("ldr x12, [x29, #%d]" % self.off(cells[i][1]))
                else: self.load_list(d, "x11", "x12")
                self.copy_bytes(self.scur, narrow=(kd == "int"))
        self.emit("ldr x0, [x29, #%d]" % self.off(self.sdest)); self.emit("ldr x1, [x29, #%d]" % self.off(self.scur))
        self.emit("sub x1, x1, x0", "長さ(バイト)")
        if CW == 4: self.emit("lsr x1, x1, #2", "文字数")
        self.emit("b %s" % done)
        self.lines.append("%s:" % fail); self.unit_result("S")
        self.lines.append("%s:" % done)
        for _ in range(2 + 2 * len(cells) + 3 * len(bufs) + len(ccells)): self.free()

    def gen_build_nest(self, n):
        """入れ子のリストを組み立てて返す(設計者の内容の領域 arena。pass4.js emitContentArena)。
        もらった置き場(x8)の先頭に記述子 {ptr, len} を 1 つ 16 バイトで左から並べ、式で作る内側のリスト(`(a b)`)の要素は
        arena(x8 + 16 × x15 の頭が指す『次に書く位置』から)へ 8 バイトずつ積む。すでにある器(仮引数・字面・定数端のスライス)は
        コピーせず、その {ptr, len} を記述子に写す。器を組み立てて返す関数の結果(`(mk a)`)は、呼ぶ側(ここ)の一時の置き場に
        できるので、先に呼んで arena へ写す(置き場は関数が返ると消えるため)。要る内容の語数と記述子の数を先に数え、
        入らなければ何も書かずに `__`。"""
        if not self.sret: raise AsmError("組み立てた器は、返す位置でしか作れません(置き場を呼ぶ側がくれる関数の返値だけ)")
        items = self.prog.builds(n)
        if len(items) > 1000: raise AsmError("入れ子のリストの要素が多すぎます(1000 まで)")
        plan = []                                  # ("build", [(ty, x)...]) / ("call", x) / ("view", x)
        for it in items:
            ty, x = self.prog.item_info(it)
            if ty != "scalar": raise AsmError("入れ子の並びの中の展開(~)はまだ出せません(リストとスカラーが混ざる。平らにするなら `xs~ ys~`)")
            xs = self.strip(x)
            kx = self.prog.kind(xs, self.kinds)
            if kx == "I":                                  # スカラーの要素: 内容の領域に 1 語を置き、記述子は {そのセル | 1, 1}(ptr の bit0 が印)
                if self.mu(xs): raise AsmError("入れ子の要素のスカラーが `__` になりうる形はまだ出せません(`__` は入れ子に入らず並びから消える)")
                plan.append(("sc", xs)); continue
            if kx != "L": raise AsmError("入れ子の要素にできるのは Int のリストと Int だけです(文字列・もう一段の入れ子はまだ)")
            inner = self.prog.builds(xs)
            if inner is not None:
                sub = []
                for it2 in inner:
                    t2, x2 = self.prog.item_info(it2)
                    k2 = self.prog.kind(x2, self.kinds)
                    if t2 == "scalar":
                        if k2 != "I": raise AsmError("入れ子の要素の中にまたリストがあります(3 段の入れ子はまだ)")
                    else:
                        if k2 not in ("L", "N"): raise AsmError("展開(~)できるのはリストと入れ子のリストだけです(文字列・Int はまだ)")
                        self.prog.check_spread(x2, inner)
                    sub.append((t2, x2))
                if any(t == "scalar" and self.mu(x) for t, x in sub) and sum(1 for t, x in sub if t == "scalar" and not self.mu(x)) < 2:
                    raise AsmError("入れ子の内側の要素が `__` になりうる形は、`__` にならない要素が 2 個以上あるときだけ出せます(全部が消えると内側が `__` に、1 個だけ残ると内側が Int になり、入れ子の種類が実行時に変わる)")
                plan.append(("build", sub))
            elif self.prog.builder_call(xs) is not None:
                g = self.prog.builder_call(xs)
                if self.prog.unit_possible(g): raise AsmError("入れ子の要素に、`__` を返しうる関数の結果(%s)は置けません(`__` は入れ子に入らず並びから消える)" % g)
                for a, kd in zip(xs[1][1:], self.prog.pkind[g]):
                    sa = self.strip(a)
                    ok = (not self.mu(a)) if kd == "I" else (sa[0] == "id" or self.prog.list_values(sa) is not None or self.prog.str_value(sa) is not None or self.prog.nested_values(sa) is not None) if kd in WIDE else True
                    if not ok: raise AsmError("入れ子の要素に置く %s の引数が `__` になりうる形はまだ出せません(`__` は入れ子に入らず並びから消える)" % g)
                plan.append(("call", xs))
            else:
                mv = self.prog.check_view(xs)
                plan.append(("viewm" if mv else "view", xs))
        K = len(plan)
        dyn = any(kd == "viewm" for kd, _ in plan)
        if dyn and sum(1 for kd, _ in plan if kd != "viewm") < 2:
            raise AsmError("入れ子の要素に `__` になりうる内側があり、`__` にならない要素が 2 個未満です(全部が消えて 1 個だけ残ると、入れ子でなく 1 つのリストになる)")
        fail, done = self.prog.label(), self.prog.label()
        tot, cur = self.tmp(), self.tmp()          # 要る内容の語数 / 内側のリストの始まり
        cells = {}                                 # 呼びの結果(ptr, len)を預けるセル
        for i, (kd, d) in enumerate(plan):
            if kd == "call": cells[i] = (self.tmp(), self.tmp())
        mc = {}                                    # `__` になりうる内側の要素 (内側の番号, 位置) → 値を 1 度だけ評価して預けるセル
        for i, (kd, d) in enumerate(plan):
            if kd == "build":
                for k, (t, x) in enumerate(d):
                    if t == "scalar" and self.mu(x): mc[(i, k)] = self.tmp()
        nscalar = sum(1 for i, (kd, d) in enumerate(plan) if kd == "build" for k, (t, _) in enumerate(d) if t == "scalar" and (i, k) not in mc) + sum(1 for kd, _ in plan if kd == "sc")
        emit_imm(self.lines, "x9", nscalar, "要る内容の語数(定数ぶん)")
        self.emit("str x9, [x29, #%d]" % self.off(tot))
        for i, (kd, d) in enumerate(plan):
            if kd == "call":
                self.load_list(d, "x0", "x1")
                self.emit("str x0, [x29, #%d]" % self.off(cells[i][0]), "結果の先頭(この関数の一時の置き場)"); self.emit("str x1, [x29, #%d]" % self.off(cells[i][1]), "結果の長さ")
                self.emit("ldr x9, [x29, #%d]" % self.off(tot)); self.emit("add x9, x9, x1", "写す長さを足す")
                self.emit("str x9, [x29, #%d]" % self.off(tot))
            elif kd == "build":
                for k, (t, x) in enumerate(d):
                    if (i, k) in mc:
                        sk = self.prog.label()
                        self.gen(x); self.emit("str x0, [x29, #%d]" % self.off(mc[(i, k)]), "`__` になりうる要素(1 度だけ評価)")
                        self.niche(); self.emit("cmp x0, x13"); self.emit("b.eq %s" % sk, "__ は並びから消える")
                        self.emit("ldr x9, [x29, #%d]" % self.off(tot)); self.emit("add x9, x9, #1"); self.emit("str x9, [x29, #%d]" % self.off(tot))
                        self.lines.append("%s:" % sk)
                        continue
                    if t != "spread": continue
                    self.spread_total(x)
                    self.emit("ldr x9, [x29, #%d]" % self.off(tot)); self.emit("add x9, x9, x12", "展開する器の長さを足す")
                    self.emit("str x9, [x29, #%d]" % self.off(tot))
        self.emit("ldr x10, [x29, #%d]" % self.off(self.slim), "置き場に入る記述子の数 K")
        self.emit("cmp x10, #%d" % K); self.emit("b.lo %s" % fail, "入らなければ何も書かない(`__`)")
        self.emit("ldr x9, [x29, #%d]" % self.off(self.sdest))
        self.emit("lsl x10, x10, #4"); self.emit("add x9, x9, x10", "arena の頭 = 置き場 + 16 × K")
        self.emit("ldr x10, [x9]", "次に書く位置"); self.emit("ldr x11, [x9, #8]", "終わり")
        self.emit("sub x11, x11, x10", "残りのバイト数")
        self.emit("ldr x12, [x29, #%d]" % self.off(tot)); self.emit("lsl x12, x12, #3")
        self.emit("cmp x12, x11"); self.emit("b.hi %s" % fail, "内容が入らなければ何も書かない(`__`)")
        self.emit("str x10, [x29, #%d]" % self.off(self.scon), "書く位置")
        di = self.tmp()
        self.emit("mov x9, #0"); self.emit("str x9, [x29, #%d]" % self.off(di), "書いた記述子の数")
        for i, (kd, d) in enumerate(plan):
            skipl = self.prog.label()
            if kd in ("build", "call"):
                self.emit("ldr x9, [x29, #%d]" % self.off(self.scon)); self.emit("str x9, [x29, #%d]" % self.off(cur), "内側のリスト %d の始まり" % i)
                if kd == "call":
                    lp, le = self.prog.label(), self.prog.label()
                    self.emit("ldr x11, [x29, #%d]" % self.off(cells[i][0])); self.emit("ldr x12, [x29, #%d]" % self.off(cells[i][1]))
                    self.emit("mov x14, #0", "結果を arena へ写す")
                    self.lines.append("%s:" % lp)
                    self.emit("cmp x14, x12"); self.emit("b.hs %s" % le)
                    self.emit("ldr x13, [x11, x14, lsl #3]"); self.emit("str x13, [x9, x14, lsl #3]")
                    self.emit("add x14, x14, #1"); self.emit("b %s" % lp)
                    self.lines.append("%s:" % le)
                    self.emit("add x9, x9, x12, lsl #3"); self.emit("str x9, [x29, #%d]" % self.off(self.scon))
                else:
                    for k, (t, x) in enumerate(d):
                        if t == "scalar":
                            sk = self.prog.label()
                            if (i, k) in mc:
                                self.emit("ldr x0, [x29, #%d]" % self.off(mc[(i, k)])); self.niche(); self.emit("cmp x0, x13"); self.emit("b.eq %s" % sk, "__ は書かない")
                            else: self.gen(x)
                            self.emit("ldr x9, [x29, #%d]" % self.off(self.scon))
                            self.emit("str x0, [x9]"); self.emit("add x9, x9, #8"); self.emit("str x9, [x29, #%d]" % self.off(self.scon))
                            self.lines.append("%s:" % sk)
                        else:
                            self.spread_copy(x, self.scon)
                self.emit("ldr x11, [x29, #%d]" % self.off(cur)); self.emit("ldr x10, [x29, #%d]" % self.off(self.scon))
                self.emit("sub x12, x10, x11"); self.emit("lsr x12, x12, #3", "内側のリストの長さ")
            elif kd == "sc":
                self.gen(d)
                self.emit("ldr x9, [x29, #%d]" % self.off(self.scon)); self.emit("str x0, [x9]", "スカラーの値のセル")
                self.emit("orr x11, x9, #1", "記述子の ptr = セル | 1(bit0 = スカラーの印)"); self.emit("mov x12, #1")
                self.emit("add x9, x9, #8"); self.emit("str x9, [x29, #%d]" % self.off(self.scon))
            else:
                self.load_list(d, "x11", "x12")
                if kd == "viewm": self.emit("cbz x12, %s" % skipl, "`__` の内側は並びから消える")
            self.emit("ldr x9, [x29, #%d]" % self.off(self.sdest))
            if dyn:
                self.emit("ldr x13, [x29, #%d]" % self.off(di)); self.emit("lsl x14, x13, #4"); self.emit("add x9, x9, x14")
                self.emit("str x11, [x9]", "記述子の ptr"); self.emit("str x12, [x9, #8]", "記述子の len")
                self.emit("add x13, x13, #1"); self.emit("str x13, [x29, #%d]" % self.off(di))
            else:
                self.emit("str x11, [x9, #%d]" % (16 * i), "記述子 %d の ptr" % i); self.emit("str x12, [x9, #%d]" % (16 * i + 8), "記述子 %d の len" % i)
            if kd == "viewm": self.lines.append("%s:" % skipl)
        self.emit("ldr x9, [x29, #%d]" % self.off(self.sdest)); self.emit("ldr x10, [x29, #%d]" % self.off(self.slim))
        self.emit("lsl x10, x10, #4"); self.emit("add x9, x9, x10")
        self.emit("ldr x10, [x29, #%d]" % self.off(self.scon)); self.emit("str x10, [x9]", "arena の次に書く位置を進めておく")
        self.emit("ldr x0, [x29, #%d]" % self.off(self.sdest))
        if dyn: self.emit("ldr x1, [x29, #%d]" % self.off(di), "書いた記述子の数")
        else: self.emit("mov x1, #%d" % K, "記述子の数")
        self.emit("b %s" % done)
        self.lines.append("%s:" % fail); self.unit_result("N")
        self.lines.append("%s:" % done)
        for _ in range(3 + 2 * len(cells) + len(mc)): self.free()

    def is_call(self, n):
        while n[0] == "block": n = n[1]
        return n[0] == "seq" and n[1][0][0] == "id" and n[1][0][1] in self.prog.fns

    def gen_cases(self, n, tail, vk="I"):
        """行の並び: 条件が成り立てばその値、成り立たなければ次の行。全部外れて既定の行も無ければ `__`。"""
        rows = n[1]
        end = self.prog.label()
        has_default = False
        skip = 0
        for i, (cond, val) in enumerate(rows):
            if i < skip: continue
            if cond is not None and SPEC_LOOK[0] > 1 and vk == "I" and not (STRICT[0] and any(r[1] is not None and self.mu(r[1]) for r in rows[i:i + SPEC_LOOK[0]])) and PAR[0] is not None and SPEC[0] and getattr(self.prog, "target", "bare") == "linux" and self.has_seq(cond):
                grp = list(range(i, min(i + SPEC_LOOK[0], len(rows))))
                for pos, j in enumerate(grp):                      # 既定の行は最後のときだけ含める(最後でなければ今までの経路が断る)
                    if rows[j][0] is None:
                        grp = grp[:pos + 1] if j == len(rows) - 1 else grp[:pos]
                        break
                sps = {j: self.spec_call(rows[j][1]) for j in grp}
                if sum(1 for v in sps.values() if v is not None) >= 2:      # --spec-look: 先の行の値も、今の条件を調べる間に先に走らせる
                    sbs = {}; nfree = 0
                    for j in grp:
                        if sps[j] is not None:
                            sb, tv, nf = self.spec_begin(*sps[j]); sbs[j] = (sb, tv); nfree += nf
                    for j in grp:
                        cj, vj = rows[j]
                        if cj is None:                                    # 既定の行: 答えが要る
                            if j in sbs:
                                ser, ok = self.prog.label(), self.prog.label()
                                self.spec_join(sbs[j][0], ser, ok)
                                self.lines.append("%s:" % ser); self.gen_any(vj, tail, vk)
                                self.lines.append("%s:" % ok)
                            else: self.gen_any(vj, tail, vk)
                            has_default = True
                            continue
                        lf, nxt2, ser, ok = (self.prog.label() for _ in range(4))
                        self.gen_cond(cj, lf)
                        for k in grp:                                     # 成り立った: 後ろの行の投機はもう要らない
                            if k > j and k in sbs:
                                d = self.prog.label(); self.spec_cancel(sbs[k][0], sbs[k][1], d); self.lines.append("%s:" % d)
                        if j in sbs:
                            self.spec_join(sbs[j][0], ser, ok)
                            self.lines.append("%s:" % ser); self.gen_any(vj, tail, vk)
                            self.lines.append("%s:" % ok)
                        else: self.gen_any(vj, tail, vk)
                        self.emit("b %s" % end)
                        self.lines.append("%s:" % lf)
                        if j in sbs: self.spec_cancel(sbs[j][0], sbs[j][1], nxt2)
                        self.lines.append("%s:" % nxt2)
                    for _ in range(nfree): self.free()
                    skip = grp[-1] + 1
                    continue
            if cond is None:
                if i != len(rows) - 1: raise AsmError("既定の行が最後でない形はまだ出せません")
                self.gen_any(val, tail, vk); has_default = True
                break
            nxt = self.prog.label()
            sp = self.spec_for(val, cond) if vk == "I" and not (STRICT[0] and self.mu(val)) else None       # strict: 値が __ になりうる行は先読みせず、次の行へ落とす普通の道へ(V10)
            if sp is not None:                          # --par-spec: 値の呼び出しを、条件を調べる間に別のスレッドで先に走らせる
                sb, tv, nfree = self.spec_begin(*sp)
                lf, ser, ok = self.prog.label(), self.prog.label(), self.prog.label()
                self.gen_cond(cond, lf)
                self.spec_join(sb, ser, ok)
                self.lines.append("%s:" % ser); self.gen_any(val, tail, vk)
                self.lines.append("%s:" % ok); self.emit("b %s" % end)
                self.lines.append("%s:" % lf); self.spec_cancel(sb, tv, nxt)
                self.lines.append("%s:" % nxt)
                for _ in range(nfree): self.free()
                continue
            self.gen_cond(cond, nxt)
            if STRICT[0] and vk == "I" and self.mu(val):                  # V10: 行は `c & v | 次の行`。値が `__` なら次の行へ落ちる
                if self.is_call(val) and tail: raise AsmError("行の値が __ になりうる末尾呼びは、次の行へ落とせないので出せません(V10)")
                self.gen_any(val, False, vk)
                self.niche(); self.emit("cmp x0, x13"); self.emit("b.eq %s" % nxt, "値が __ なら次の行へ")
            else: self.gen_any(val, tail, vk)
            self.emit("b %s" % end)
            self.lines.append("%s:" % nxt)
        if not has_default: self.unit_result(vk)
        self.lines.append("%s:" % end)

    def gen_cond(self, c, false_label):
        """条件 c が成り立たなければ false_label へ飛ぶ(成り立てば下へ流れる)。成り立つ = `__` でない。"""
        while c[0] == "block": c = c[1]
        if c[0] == "bin" and c[1] in ("==", "!=="): c = ("cmp", [c[2], c[3]], [c[1]])
        if c[0] == "cmp": return self.gen_cmp(c, false_label)
        if c[0] == "bin" and c[1] == "&":                 # `a & b` が __ でない = a も b も __ でない(文字の比べなど、値として運べない項も条件のまま辿る)
            self.gen_cond(c[2], false_label); self.gen_cond(c[3], false_label); return
        if c[0] == "bin" and c[1] == "|":                 # `a | b` が __ でない = a か b のどちらかが __ でない
            nb, ok = self.prog.label(), self.prog.label()
            self.gen_cond(c[2], nb); self.emit("b %s" % ok); self.lines.append("%s:" % nb)
            self.gen_cond(c[3], false_label); self.lines.append("%s:" % ok); return
        if self.prog.kind(c, self.kinds) == "C":
            self.gen_char_value(c); self.emit("cbz x0, %s" % false_label, "文字の `__` は U+0000"); return
        self.gen(c)
        if self.mu(c):
            self.niche(); self.emit("cmp x0, x13"); self.emit("b.eq %s" % false_label, "__ は偽")

    def char_range(self, unit):
        """x0 が文字の域(上限以下で、utf32 ではサロゲートでもない。負は符号なしで大きい)に無ければ unit へ。"""
        if CW == 1: self.emit("cmp x0, #127"); self.emit("b.hi %s" % unit, "U+007F を超える・負は __"); return
        emit_imm(self.lines, "x12", 0x10FFFF); self.emit("cmp x0, x12"); self.emit("b.hi %s" % unit, "U+10FFFF を超える・負は __")
        emit_imm(self.lines, "x12", 0xD800); self.emit("sub x12, x0, x12"); self.emit("cmp x12, #0x7ff"); self.emit("b.ls %s" % unit, "サロゲート(U+D800〜U+DFFF)は __")

    def gen_char_value(self, n):
        """文字(Char)になる項を x0 へ。`__` は 0(U+0000)。"""
        while n[0] == "block": n = n[1]
        if n[0] == "lit" and isinstance(n[1], Char) and len(n) == 2:
            if not char_ok(ord(n[1])) and ord(n[1]) != 0: raise AsmError(char_msg())
            emit_imm(self.lines, "x0", ord(n[1]), "文字"); return
        if n[0] == "id" and n[1] in self.prog.chars and n[1] not in self.slot: emit_imm(self.lines, "x0", self.prog.chars[n[1]], "文字 " + n[1]); return
        if n[0] == "id" and n[1] in self.slot and self.kinds.get(n[1]) == "C": self.emit("ldr x0, [x29, #%d]" % self.off(self.slot[n[1]]), n[1]); return
        if n[0] == "bin" and n[1] == "+" and self.prog.kind(n[2], self.kinds) == "C" and self.prog.kind(n[3], self.kinds) == "C":
            unit, done = self.prog.label(), self.prog.label()
            self.gen_char_value(n[3]); t = self.tmp(); self.emit("str x0, [x29, #%d]" % self.off(t), "右の文字")
            self.gen_char_value(n[2])
            self.emit("ldr x10, [x29, #%d]" % self.off(t))
            self.emit("cbz x0, %s" % unit, "どちらかが __ なら __"); self.emit("cbz x10, %s" % unit)
            self.emit("add x0, x0, x10", "文字コードの和(溢れない)")
            self.char_range(unit)
            self.emit("b %s" % done)
            self.lines.append("%s:" % unit); self.emit("mov x0, #0", "__")
            self.lines.append("%s:" % done)
            return
        if n[0] == "bin" and n[1] in ("+", "-") and self.prog.kind(n[2], self.kinds) == "C" and self.prog.kind(n[3], self.kinds) == "I":
            # Char ± Int: 結果が文字の範囲(U+0001〜U+007F)に入れば Char、外れるか片方が __ なら __(処理系の観測)。
            # U+0000 の文字は、Char の `__`(= 0)と区別できないので罠にする(実装の決め)
            self.prog.trap_used = True
            unit, done = self.prog.label(), self.prog.label()
            self.gen(n[3]); t = self.tmp(); self.emit("str x0, [x29, #%d]" % self.off(t), "足す数")
            self.gen_char_value(n[2])
            self.emit("ldr x10, [x29, #%d]" % self.off(t))
            self.emit("cbz x0, %s" % unit, "文字が __ なら __")
            self.niche(); self.emit("cmp x10, x13"); self.emit("b.eq %s" % unit, "数が __ なら __")
            if CW == 1: self.emit("add x11, x10, #128"); self.emit("cmp x11, #256"); self.emit("b.hi %s" % unit, "動きが ±128 を超えれば文字の範囲の外")
            else: emit_imm(self.lines, "x12", 0x110000); self.emit("add x11, x10, x12"); self.emit("lsl x12, x12, #1"); self.emit("cmp x11, x12"); self.emit("b.hi %s" % unit, "動きが ±U+110000 を超えれば文字の範囲の外")
            self.emit("%s x0, x0, x10" % ("add" if n[1] == "+" else "sub"))
            self.char_range(unit)
            self.emit("cbnz x0, %s" % done); self.emit("b .Ltrap", "U+0000 の文字は Char の `__` と区別できない(罠)")
            self.lines.append("%s:" % unit); self.emit("mov x0, #0", "__")
            self.lines.append("%s:" % done)
            return
        if n[0] == "bin" and n[1] == "'": return self.gen_index(n[2], n[3])
        if n[0] == "bin" and n[1] in ("==", "!=="): return self.gen_cmp(("cmp", [n[2], n[3]], [n[1]]), None)
        if n[0] == "cmp": return self.gen_cmp(n, None)
        if n[0] == "cases": return self.gen_cases(n, False, "C")
        if self.is_call(n): return self.gen_call(n)
        raise AsmError("この形の文字はまだ出せません(文字の字面・`s ' i`・比較だけ)")

    def gen_cmp(self, c, false_label):
        """比較。false_label があれば条件として(外れたらそこへ飛ぶ)、無ければ値として
        (成り立てば最後の比較の左の項、外れれば `__`。処理系と同じ)。`__` の項があれば外れ。
        ただし `!=` `!==` は恒等射: 片方だけ `__` なら成り立ち、値は非 `__` 側。両方 `__` なら外れ(operator_table.md)。
        項はすべて Int か、すべて Char(Char の `__` は 0)。"""
        operands, ops = c[1], c[2]
        for o in ops:
            if o not in self.CC:
                raise AsmError("比較 `%s` はまだ出せません(< <= > >= = != == !== だけ)" % o)
        kinds = [self.prog.kind(o, self.kinds) for o in operands]
        if PAR[0] is not None and getattr(self.prog, "target", "bare") == "linux" and len(operands) == 2 and kinds == ["I", "I"]:
            pl = self.hoist_plan(operands)          # `f x < g y`: 比べるには両方の項が要る(条件の枝でも同じ)ので、独立な呼び出しは先に並列で
            if pl is not None:
                names, vals = self.hoist_exec(pl[0])
                self.gen_cmp(("cmp", pl[1], ops) + tuple(c[3:]), false_label)
                for nm in names: del self.slot[nm]; del self.kinds[nm]
                for _ in vals: self.free()
                return
        ck = kinds[0]
        if ck not in ("I", "C") or any(k != ck for k in kinds):
            raise AsmError("比較できるのは Int 同士か文字同士だけです(リスト・文字列の比べや、種類の違う物の比べはまだ出せません)")
        isc = ck == "C"
        nr = "xzr" if isc else "x13"                      # `__` のビット列を持つ(か、0 そのもの)レジスタ
        def mu(o):
            while o[0] == "block": o = o[1]
            if isc: return not (o[0] == "lit" and isinstance(o[1], Char) and len(o) == 2)
            return self.mu(o)
        def unit_val(reg):
            if isc: self.emit("mov %s, #0" % reg, "Char の `__`")
            else: self.niche(reg)
        as_value = false_label is None
        if as_value: false_label = self.prog.label()
        # 各項は左から順に、必要になったときにだけ評価する(外れた時点で止まり、後ろの項は評価しない)。
        # 連なった比較 `a < b < c` の真ん中は 2 回使うので、式ならスロットに預ける。
        held = 0
        def operand(o):
            nonlocal held
            if not isc and self.simple(o): return ("n", o)
            if isc: self.gen_char_value(o)
            else: self.gen(o)
            t = self.tmp(); held += 1
            self.emit("str x0, [x29, #%d]" % self.off(t), "比べる項")
            return ("s", t)
        def put(ref, reg):
            if ref[0] == "n": self.load(ref[1], reg)
            else: self.emit("ldr %s, [x29, #%d]" % (reg, self.off(ref[1])))
        prev = operand(operands[0])
        for i, o in enumerate(ops):
            cur = operand(operands[i + 1])
            put(prev, "x9"); put(cur, "x10")
            ml, mr = mu(operands[i]), mu(operands[i + 1])
            ident = o in ("!=", "!==") and (ml or mr)
            if ident:
                if not isc: self.niche()
                ok, lok = self.prog.label(), self.prog.label()
                self.emit("cmp x9, %s" % nr)
                self.emit("b.ne %s" % lok)
                self.emit("cmp x10, %s" % nr); self.emit("b.eq %s" % false_label, "両方 __ なら外れ")
                self.emit("b %s" % ok, "左だけ __ なら成り立つ(値は右)")
                self.lines.append("%s:" % lok)
                if mr: self.emit("cmp x10, %s" % nr); self.emit("b.eq %s" % ok, "右だけ __ なら成り立つ(値は左)")
                self.emit("cmp x9, x10"); self.emit("b.eq %s" % false_label)
                self.lines.append("%s:" % ok)
            else:
                if ml or mr:
                    if not isc: self.niche()
                    if ml: self.emit("cmp x9, %s" % nr); self.emit("b.eq %s" % false_label, "__ との比較は外れ")
                    if mr: self.emit("cmp x10, %s" % nr); self.emit("b.eq %s" % false_label)
                self.emit("cmp x9, x10")
                self.emit("b.%s %s" % (self.INV[self.CC[o]], false_label))
            if as_value and i == len(ops) - 1:
                put(prev, "x0")
                if ident and ml:
                    self.emit("cmp x0, %s" % nr); self.emit("csel x0, x10, x0, eq", "左が __ なら右が値")
            prev = cur
        for _ in range(held): self.free()
        if as_value:
            done = self.prog.label()
            self.emit("b %s" % done)
            self.lines.append("%s:" % false_label); unit_val("x0")
            self.lines.append("%s:" % done)

    # ---- 組み立て ----
    def finish(self, label, export=False):
        cells = self.top
        frame = 16 + ((cells * 8 + 15) // 16) * 16
        head = []
        if export: head.append("\t.global %s" % label)
        head += ["%s:" % label,
                 "\tstp x29, x30, [sp, #-%d]!  // フレーム %d バイト" % (frame, frame),
                 "\tmov x29, sp"]
        # 仮引数をスロットへ写す
        r = 0
        for p, cell, kd in self.order:
            for j in range(WIDTH[kd]):
                part = {"L": (".ptr", ".len"), "S": (".ptr", ".len"), "N": (".ptr", ".len"), "R": (".start", ".step", ".end")}.get(kd, ("",))[j]
                if r < len(ARG_REGS):
                    head.append("\tstr %s, [x29, #%d]  // 仮引数 %s%s" % (ARG_REGS[r], self.off(cell + j), p, part))
                else:
                    head.append("\tldr x9, [x29, #%d]  // スタックで渡された仮引数 %s%s(呼ぶ側の sp = フレームの上)" % (frame + 8 * (r - len(ARG_REGS)), p, part))
                    head.append("\tstr x9, [x29, #%d]" % self.off(cell + j))
                r += 1
        if self.name in self.prog.maskfns:
            head.append("\tstr x17, [x29, #%d]  // 器の実引数ごとの旗(ビット j = 第 j 引数。呼ぶ側が置く)" % self.off(self.mcell))
        if self.sret and label != "_.main":
            head.append("\tstr x8, [x29, #%d]  // 返値スロットの先頭(呼ぶ側が用意)" % self.off(self.sdest))
            head.append("\tstr x15, [x29, #%d]  // そこに入る個数" % self.off(self.slim))
        for kx in self.cse_lazy:
            head.append("\tmovz x9, #0x8000, lsl #48  // __")
            head.append("\tstr x9, [x29, #%d]  // ループ不変式のスロットを空にする" % self.off(self.cse[kx]))
        import re
        looped = self.entry and any(re.search(re.escape(self.entry) + r"(?!\d)", l) for l in self.lines)      # `.L1` が `.L12` に当たらないように
        lines = self.lines
        if self.pre_alloca and self.entry_pos is not None:
            # 伸びる累積: 外から呼ばれたときだけ作業領域を作る。自分から呼ぶ再帰は `<名前>.rec` から入り(フレームと引数の保存だけ)、
            # 呼ぶ側の作業領域をそのまま使う(再帰の深さごとに作業領域が積み上がらない)。末尾呼び出しの飛び先 entry は両方の合流点
            rec = ["\tb %s" % self.entry, "%s.rec:" % label,
                   "\tstp x29, x30, [sp, #-%d]!  // フレーム %d バイト(再帰の入口。作業領域は呼ぶ側のものを使う)" % (frame, frame), "\tmov x29, sp"] + head[head.index("\tmov x29, sp") + 1:]
            lines = lines[:self.entry_pos] + rec + ["%s:" % self.entry] + lines[self.entry_pos:]
        elif looped:      # 末尾呼び出しが使ったときだけ
            if self.entry_pos is None: head.append("%s:" % self.entry)
            else: lines = lines[:self.entry_pos] + ["%s:" % self.entry] + lines[self.entry_pos:]
        if looped and self.alloca:
            raise AsmError("%s: 自分への末尾呼び出し(ループ)と、器の置き場を取る呼びが同じ関数にあります(回るたびに sub sp が積み上がるため、まだ出せません)" % label.lstrip("_."))
        tail = (["\tmov sp, x29  // sub sp で取った置き場を捨てる"] if (self.alloca or self.pre_alloca) else []) + ["\tldp x29, x30, [sp], #%d  // フレームを戻す" % frame, "\tret"]
        out = head + lines + tail
        if PEEP[0] and os.environ.get("SIGN_PEEP", "1") != "0":
            import sign_opt
            out = sign_opt.optimize(out)          # 制御フロー解析・共通部分式・デッドコード・ループ不変式・割り付け、そのあと窓の置き換え
        return out


IMPORT_DIR = [None]      # `f`@~ の相対パスの基準(読み込んだ原文のあるディレクトリ。無ければカレント)

def expand_imports(nodes, seen=None, stack=()):
    """最上位の `path`@~(importspread)を、そのファイルの定義に置き換える(interpreter の import_file と同じ解き方: パスは取り込む側のファイルからの相対)。
    取り込まれたファイルの最上位は定義だけ(式があれば断る: 取り込み時の副作用を出せない)。公開の印 `#` があるファイルは、
    撒かれるのが公開の名前だけになるので、まだ出せない。同じファイルは 1 回だけ。名前が既にある定義と重なれば断る。"""
    import os, sign_interp
    if seen is None: seen = set()
    base = IMPORT_DIR[0] or os.getcwd()
    out, names = [], set()
    for n in nodes:
        if n[0] != "importspread": out.append(n); continue
        p = n[1]
        while p[0] == "block": p = p[1]
        if not (p[0] == "lit" and isinstance(p[1], str)): raise AsmError("取り込むファイル名が字面でない形はまだ出せません")
        full = os.path.abspath(os.path.join(base, p[1]))
        if full in stack: raise AsmError("import が循環しています: %s" % p[1])
        if full in seen: continue
        if not os.path.exists(full): raise AsmError("取り込むファイル `%s` が見つかりません" % p[1])
        seen.add(full)
        old = IMPORT_DIR[0]; IMPORT_DIR[0] = os.path.dirname(full)
        try:
            sub = sign_interp.parse_source(open(full, encoding="utf-8").read())
            if any(x[0] == "export" or (x[0] == "def" and len(x) > 3 and x[3]) for x in sub): raise AsmError("%s: 公開の印 `#` があるファイルの取り込みはまだ出せません(撒かれるのが公開の名前だけになる)" % p[1])
            sub = expand_imports(sub, seen, stack + (full,))
        finally: IMPORT_DIR[0] = old
        bad = [x for x in sub if x[0] != "def"]
        if bad: raise AsmError("%s: 取り込むファイルの最上位に式があります(取り込み時の副作用はまだ出せません)" % p[1])
        out.extend(sub)
    pos = {}
    for i, n in enumerate(out):
        if n[0] == "def" and isinstance(n[1], str): pos.setdefault(n[1], []).append(i)
    drop = set()
    for nm, ps in pos.items():
        if len(ps) < 2: continue
        # 同じ名前の定義が重なるとき、あとの定義が勝つ(名前は呼ばれるときに引かれる)。見分けがつくのは、前の定義が関数で、
        # 重なりの間に最上位の式(前の定義を見てしまう物)が無いときだけ。それ以外は断る
        if any(out[i][2][0] != "lam" for i in ps[:-1]) or any(out[j][0] != "def" for j in range(ps[0], ps[-1])):
            raise AsmError("同じ名前の定義が重なっています(%s)。前の定義が値、または間に最上位の式があるので、どちらが勝つかをまだ決められません" % nm)
        drop.update(ps[:-1])
    if drop: out = [n for i, n in enumerate(out) if i not in drop]
    return out


def dyn_label(name):
    return "_sign_dyn_" + symbol_of(name)


def rename_shadowing_params(nodes):
    """仮引数が、同じ名前の定義を隠している関数は、その仮引数(と本体の中の使い方)を別の名前に付け替える。
    処理系は仮引数が勝つ(`x1 : 7` のとき `g : x1 ? [x1 3]` の `x1` は仮引数)。asm は、呼びか器かを名前が定義にあるかだけで決める所が多く
    (`self.fns` の引き当て)、スコープを見ないので、そのままだと定義の方に取って答えが食い違う。付け替えれば、どの所も正しく仮引数として扱われる。
    内側の関数(`$[x1 ? …]`)が同じ名前を自分の仮引数にしていれば、その内側は付け替えない(内側の仮引数が勝つ)。"""
    names = {n[1] for n in nodes if isinstance(n, tuple) and n and n[0] == "def"}
    def pnames(ps):
        o = set()
        for q in ps:
            if q[0] == "name": o.add(q[1])
            elif q[0] == "destr":
                o |= {x for x in q[1] if isinstance(x, str)}
                if isinstance(q[2], str): o.add(q[2])
                if len(q) > 4: o |= {x for x in q[4] if isinstance(x, str)}
        return o
    def ren(t, m):
        if isinstance(t, list): return [ren(x, m) for x in t]
        if not isinstance(t, tuple) or not t: return t
        if t[0] == "id" and len(t) == 2 and t[1] in m: return ("id", m[t[1]])
        if t[0] == "lam" and len(t) > 2 and isinstance(t[1], list):
            inner = pnames(t[1]); m2 = {k: v for k, v in m.items() if k not in inner}
            if len(m2) != len(m):                      # 内側が一部の名前を自分の仮引数にしている
                return ("lam", rename_params(t[1], m2), ren(t[2], m2)) + tuple(t[3:]) if m2 else t
            return ("lam", rename_params(t[1], m), ren(t[2], m)) + tuple(t[3:])
        return tuple(ren(x, m) if isinstance(x, (tuple, list)) else x for x in t)
    def rename_params(ps, m):
        out = []
        for q in ps:
            if q[0] == "name" and q[1] in m: out.append(("name", m[q[1]]) + tuple(q[2:]))
            elif q[0] == "destr":
                nm = [m.get(x, x) if isinstance(x, str) else x for x in q[1]]
                tl = m.get(q[2], q[2]) if isinstance(q[2], str) else q[2]
                rest = (list(q[4]) if len(q) > 4 and isinstance(q[4], list) else None)
                if rest is not None: rest = [m.get(x, x) if isinstance(x, str) else x for x in rest]
                out.append(("destr", nm, tl, q[3]) + ((rest,) if rest is not None else ()) + tuple(q[5:]))
            else: out.append(q)
        return out
    out = []; changed = False
    for n in nodes:
        if isinstance(n, tuple) and n and n[0] == "def" and len(n) > 2 and n[2][0] == "lam":
            ps = pnames(n[2][1]); sh = ps & names
            if sh:
                taken = names | ps
                m = {}
                for x in sorted(sh):
                    y = x + "_"
                    while y in taken: y += "_"
                    taken.add(y); m[x] = y
                lam = n[2]
                n = n[:2] + (("lam", rename_params(lam[1], m), ren(lam[2], m)) + tuple(lam[3:]),) + tuple(n[3:])
                changed = True
        out.append(n)
    return out if changed else nodes


class Program:
    def __init__(self, nodes):
        if any(n[0] == "importspread" for n in nodes): nodes = expand_imports(nodes)
        nodes = rename_shadowing_params(nodes)                 # 仮引数が定義と同じ名前なら、仮引数を付け替える(asm は名前だけで呼びか器かを決めるため。処理系は仮引数が勝つ)
        if FUSE[0]:
            import sign_fuse
            try: nodes = sign_fuse.fuse_fold_map(nodes)           # 融合 段 2(別名・節の展開の前。`[op]` がまだ節の形のうちに): `[op] (map $g xs)` を 1 つの輪へ(中間の器を作らない)
            except ValueError as e: raise AsmError(str(e))
        if SCALAR[0]:
            import sign_fuse
            nodes = sign_fuse.scalarize_records(nodes)         # レコードの分解: 字面の器を受ける仮引数へ、要素をそのまま渡す(器を作らない)
        nodes = expand_aliases(nodes)                          # 別名 `p : inc`・算術の節 `[+] 2 3` の展開
        nodes = expand_mixed_spreads(nodes)                    # 字面の名前の混ざる入れ子の展開 `m~` は、要素を並べた並びへ
        import sign_inline                                     # 特殊化: `$関数` を渡す呼び出しを、渡された関数ごとの実体 `F$G` へ付け替える(仕様の「コンパイル時特殊化」)
        try: nodes = sign_inline.specialize(nodes)
        except sign_inline.SpecError as e: raise AsmError(str(e))
        self.nodes = [("def", n[1], self.unpack_params(n[1], n[2])) + tuple(n[3:]) if n[0] == "def" and n[2][0] == "lam" else n for n in nodes]      # 括りの仮引数は最初に器 1 本の形へ直す
        if HOIST[0]:
            import sign_fuse
            self.nodes = sign_fuse.lazy_invariants(self.nodes)   # ループ不変式: 最初に必要になった時に 1 回だけ(share_exprs より先。lazy の中には share の印をつけない)
        if SHARE[0]:
            import sign_fuse
            self.nodes = sign_fuse.share_exprs(self.nodes)     # 共通部分式(枝をまたぐ式)の印。解析からは今までの括りと同じに見える
        self.fnval = None        # 最上位に式が無く、最後の定義が関数のとき、処理系が印字する `<fn/N>`(N は仮引数の数)
        if self.nodes and all(n[0] == "def" for n in self.nodes):        # 式の無いファイルは、最後の定義の値を印字する(処理系の観測: `x : 5` は 5、関数は `<fn/N>`)
            last = nodes[-1][2] if isinstance(nodes[-1], tuple) and len(nodes[-1]) > 2 else None
            if last is not None and last[0] == "lam": self.fnval = "<fn/%d>" % len(last[1])
            elif last is not None and last[0] == "seq" and nodes[-1][0] == "def": self.nodes = self.nodes + [("id", nodes[-1][1])]       # 呼びの定義は一度だけ評価した値(セル)を読む(副作用のある `h : println `x`` を二度評価しない)
            elif last is not None: self.nodes = self.nodes + [last]
        self.inner_pos = set()   # 輪の辺が入れ子の内側の長さに頼る新しい器を渡す位置 (関数, 仮引数の番号)(総和から除く)
        self.inner_cand = set()
        self.inner_nconst = {}
        self.inner_pass = set()
        self.hop_acc = {}; self.hop_pass = {}; self.grow_extra = {}; self.bound0 = {}; self.ring_grow = {}; self.ring_d = 0; self.ring_changed = False
        self.q_pass = set()      # 内側頼みの位置から内側頼みの位置へ器を渡す辺 ((関数, 番号), (関数, 番号))
        self.inner_size = {}     # (呼ぶ側, 呼ばれる側, 位置) → (定数, {("m", k): 係数})
        self.viols = []
        self.flagrelay = set() # 旗を実引数から運ぶ素通しの関数
        self.maskfns = set()   # 枝によって返す器の引数が変わる関数: 実引数の旗を x17 のビット(第 j 引数 = ビット j)で受け、返す枝ごとに x2 へ置く
        self.flagfns = set()   # 最上位で印字する結果が『1 個だけ残ると Int』になりうるとき、実行時の旗(x2)を運ぶ関数
        self.fns = {}          # 名前 → 仮引数の名前の並び
        self.chars = {}        # 名前 → 文字コード(文字の字面の定義 `newline : '\\n'`)
        self.consts = {}       # 名前 → 整数(字面だけの定義)
        self.maybe_ids = set() # 先に評価した葉の名前のうち、答えが `__` になりうる物
        self.defaults = {}     # 名前 → (既定値の無い仮引数の数, [(仮引数の名前, 既定値の式)]) 既定値のある関数。呼び出しの側で、足りない実引数を既定値の式で埋める(expand_defaults)
        self.dyn = {}          # 名前 → 右辺(値が計算で決まる Int の定義。起動で一度だけ評価して .bss のセル _sign_dyn_名前 に置く)
        self.trap_used = False
        self.cwidth = {}          # 名前 → 幅つきの番地の幅(byte)
        self.addr_cells = {}      # 定数の番地 → 最初に使った関数(64 ビットの読み書きが重なる組を知らせる)
        self.estimate = os.environ.get("SIGN_ESTIMATE") != "0"; self.infos = []       # 上界を証明でなく見積もりで通す(仕様: stack_abi.md §4.7)。通した関数は infos に残す
        self.work_trap = False
        self.part_trap = {}      # strict: 余った関数が生きる呼び(id → 節)。実引数が `!_` になったら罠(.Ltrap_part)
        self.part_seen = set()   # codegen がその罠を出した呼びの id
        self.part_used = False
        self.sp = set()
        self.grow = {}        # 関数 → (累積を伸ばす引数, 1 回で伸びる個数, 食う引数)
        self.nlabel = 0
        self.par_nsites = 0; self.par_used = set(); self.spec_used = set()          # --par: 並列の候補の所の数・包みが要る関数
        self.ret_maybe = {}    # 関数 → 返値が `__` になりうるか
        self.bodies = {}
        self.lists = {}        # 名前 → (像のラベル, 要素の並び)(字面の並びの定義)
        self.rodata = {}       # (文字列か, 要素の並び) → ラベル(同じ中身は 1 つに畳む)
        self.strs = {}         # 名前 → (像のラベル, 文字コードの並び)(文字列の字面の定義)
        self.pkind = {}        # 関数 → 仮引数の種類の並び("I" か "L" か "S")
        self.live = set()      # 最上位の式から辿れる関数
        self.bound = {}        # 関数 → 返す器の要素数の上界(0 でなければ x8/x15 で呼ぶ側の置き場をもらう。stack_abi.md §4.7)
        self.retk = {}         # 関数 → 返値の種類("I" "L" "S" "C" "N")
        self.nests = {}        # 名前 → (記述子の表のラベル, 内側のリストの数, 要素の総数)(入れ子のリストの字面の定義)
        self.nest_emit_seen = set()
        self.rule_names = set()
        self.boundk = {}       # 入れ子の器を組み立てて返す関数 → (記述子の数 K, {})。arena の頭は x8 + 16 × K

    def rodata_label(self, vals, is_str=False):
        key = (is_str, tuple(vals))
        if key not in self.rodata: self.rodata[key] = (".Lstr%d" if is_str else ".Llist%d") % len(self.rodata)
        return self.rodata[key]

    mixed_nest = False     # スカラーとリストが混ざる入れ子が現れた(記述子の ptr の bit0 が立つ要素がある)
    nest_unsafe = None     # 混ざる入れ子では出せない使い方の説明(終わりに、混在があれば断る)

    def note_unsafe(self, msg):
        if self.nest_unsafe is None: self.nest_unsafe = []
        if msg not in self.nest_unsafe: self.nest_unsafe.append(msg)

    nest_ik = None         # 入れ子の内側の種類: "L" = Int のリスト、"S" = 文字列(字面の `[`ab`, `cd`]`)。両方が出る組は断る

    nest_emit_seen = None  # 取り出しを出したとき、印のある入れ子が見つかっていたか(後から見つかると印を外す命令が抜ける)
    nest_depth = None      # 入れ子の深さ(2 段の入れ子 = 1、3 段 = 2…)。同じ組の入れ子は同じ深さだけ(要素の取り出しの種類を静的に決めるため)
    scalar_nest = False    # スカラーの要素を持つ入れ子がある(取り出し `m ' i` の先がスカラーかリストかは実行時の印で決まる)

    def nest_mark(self, ik, depth=1):
        if self.nest_ik not in (None, ik):
            raise AsmError("Int のリストの入れ子と、文字列の入れ子(文字列のリスト)が同じ組に出ています。内側の幅が 8 と 1 で違うので、まだ出せません" if "X" not in (self.nest_ik, ik) else "文字列とリストが混ざる入れ子と、そうでない入れ子が同じ組に出ています(取り出した要素の種類が静的に決まらないので、まだ出せません)")
        if self.nest_depth not in (None, depth):
            raise AsmError("深さの違う入れ子(2 段と 3 段など)が同じ組に出ています。取り出しの種類を静的に決めるため、深さは 1 つだけ出せます")
        self.nest_ik = ik; self.nest_depth = depth

    def nest_label(self, elems, strs=False):
        """入れ子の字面(要素の並び)の記述子の表のラベル。要素は list(Int のリスト)・Sc(スカラー: ptr | 1)・Str(文字列: ptr | 2)・Nst(もう一段の入れ子: ptr | 4)。
        内側の像・内側の表も .rodata に置く。"""
        ks = []
        for e in elems:
            if isinstance(e, Sc): self.rodata_label(list(e), False); ks.append(("s", e[0]))
            elif isinstance(e, Str): self.rodata_label(list(e), True); ks.append(("t",) + tuple(e))
            elif isinstance(e, Nst): ks.append(("n", self.nest_label(list(e)), len(e)))
            else: self.rodata_label(e, strs); ks.append(tuple(e))
        key = ("N", tuple(ks))
        if key not in self.rodata: self.rodata[key] = ".Lnest%d" % len(self.rodata)
        return self.rodata[key]

    def nest_ikind(self, n):
        """入れ子の字面 n の、内側の種類: "L" = Int のリスト(スカラー込み)、"S" = 文字列、"X" = 文字列とそれ以外が混ざる。"""
        out = self._nested(n)[0]
        flat = []
        def walk(es):
            for e in es:
                if isinstance(e, Nst): walk(e)
                else: flat.append(e)
        walk(out)
        ns = sum(1 for e in flat if isinstance(e, Str))
        return "S" if ns == len(flat) else "L" if ns == 0 else "X"

    def nest_depth_lit(self, n):
        d = self.nest_depth_of_lit(self._nested(n)[0])
        if d < 0: raise AsmError("入れ子の深さが揃っていません(同じ段に、入れ子とそうでない要素が混ざる形はまだ出せません)")
        return d

    def nest_mark_lit(self, n):
        self.nest_mark(self.nest_ikind(n), self.nest_depth_lit(n))

    def ndepth(self, n, env):
        """式 n(入れ子の種類)の深さ: 取り出し `m ' i` は 1 段浅い、切り出し・名前・仮引数・呼びはその組の深さ。"""
        while n[0] == "block": n = n[1]
        if n[0] == "bin" and n[1] == "'" and self.tail_of(n) is None and self.slice_of(n) is None and self.kind(n[2], env) == "N": return self.ndepth(n[2], env) - 1
        return self.nest_depth or 1

    def nested_values(self, n):
        """n が入れ子のリストの字面(中身がどれも字面のリスト・定数の範囲・そういう名前、または中身がどれも文字列の字面・名前)なら、
        内側の要素の並びの並び、でなければ None。スカラーが混ざる並びは None(種類の検査で断る)。文字列の入れ子かどうかは nested_is_str。"""
        r = self._nested(n)
        return None if r is None else r[0]

    def nested_is_str(self, n):
        r = self._nested(n)
        return bool(r and r[1])

    def _nested(self, n):
        """(要素の並び, 全部が文字列か) か None。要素は Int のリスト(list)・スカラー(Sc)・文字列(Str)・もう一段の入れ子(Nst)。
        並置 `a b` の文字列は連結なので入れ子にならず(積 `,` のときだけ)、2 段より深い入れ子の上の段は、要素が全部入れ子のときだけ。"""
        while n[0] == "block": n = n[1]
        if n[0] not in ("seq", "prod") or len(n[1]) < 2: return None
        h = n[1][0]
        if h[0] == "id" and h[1] in self.fns: return None
        out = []
        for it in n[1]:
            while it[0] == "block": it = it[1]
            sc = it[1] if it[0] == "lit" and isinstance(it[1], int) and not isinstance(it[1], bool) else None
            if sc is not None: sc = int_literal(it)
            elif it[0] == "neg" and it[1][0] == "lit" and isinstance(it[1][1], int) and not isinstance(it[1][1], bool): sc = -int_literal(it[1])
            elif it[0] == "id" and isinstance(self.consts.get(it[1]), int) and it[1] not in self.lists: sc = self.consts[it[1]]
            if sc is not None: out.append(Sc((sc,))); continue      # スカラーの要素(`[1 [2 3]]` の 1。字面の `[3]` も同じ 3)
            if it[0] == "id" and it[1] in self.lists: out.append(list(self.lists[it[1]][1])); continue
            if n[0] == "seq" and ((it[0] == "id" and it[1] in self.strs) or (it[0] == "lit" and self.str_value(it) is not None)): return None      # 並置の文字列は連結(入れ子は積 `,` のときだけ)
            if it[0] == "id" and it[1] in self.strs: out.append(Str(self.strs[it[1]][1])); continue
            if it[0] == "id": return None
            if it[0] == "post": return None
            sv = self.str_value(it) if it[0] == "lit" else None
            if sv is not None: out.append(Str(sv)); continue
            lv = self.list_values(it) if it[0] in ("seq", "prod", "bin") else None
            if lv is not None: out.append(list(lv)); continue
            sub = self._nested(it) if it[0] in ("seq", "prod") else None
            if sub is None: return None
            out.append(Nst(sub[0]))
        nsc = sum(1 for e in out if isinstance(e, Sc)); nst = sum(1 for e in out if isinstance(e, Str)); nnest = sum(1 for e in out if isinstance(e, Nst))
        if nsc == len(out): return None                           # スカラーだけの並びは Int のリスト(入れ子でない)
        if nnest and nnest != len(out): raise AsmError("入れ子の深さが揃っていません(同じ段に、入れ子とそうでない要素が混ざる形 `[1 [2 [3 4]]]` はまだ出せません。取り出しの種類が静的に決まらないため)")
        if nsc: self.mixed_nest = True; self.scalar_nest = True
        if nst: self.mixed_nest = True                            # 文字列の要素: ptr の bit1(印字・取り出しが印を見る)
        if nnest: self.mixed_nest = True
        return out, bool(nst == len(out))

    def nest_depth_of_lit(self, out):
        """_nested の要素の並びの深さ(内側がリスト・スカラー・文字列なら 1、その内側が入れ子なら 2…)。揃わなければ -1。"""
        if not out or not isinstance(out[0], Nst): return 1
        ds = {self.nest_depth_of_lit(e) for e in out}
        return -1 if len(ds) != 1 or -1 in ds else 1 + ds.pop()

    # ---- 枝の条件から分かる器の長さの下限(`||xs|| < 3` が偽の枝では ||xs|| ≥ 3 なので `xs ' 2` は在る)----
    def length_lin(self, a, caller):
        """器の実引数 a の長さを caller の仮引数の長さの一次式で({p: 係数}, 定数)。分からなければ None。"""
        a = self.strip(a)
        ps = self.fns.get(caller, []) if caller else []
        if a[0] == "id":
            if a[1] in ps and self.pkind[caller][ps.index(a[1])] in ("L", "S"): return ({a[1]: 1}, 0)
            if a[1] in self.lists: return ({}, len(self.lists[a[1]][1]))
            if a[1] in self.strs: return ({}, len(self.strs[a[1]][1]))
            return None
        tl = self.tail_of(a) if a[0] == "bin" else None
        if tl:
            b = self.strip(tl[0])
            if b[0] == "id" and b[1] in ps and self.pkind[caller][ps.index(b[1])] in ("L", "S"): return ({b[1]: 1}, -tl[1])
            return None
        lv = self.list_values(a)
        if lv is not None: return ({}, len(lv))
        sv = self.str_value(a)
        if sv is not None: return ({}, len(sv))
        return None

    def int_facts(self, g, truth):
        """条件 g が truth のとき分かる Int の仮引数の下限 {("i", 名前): 下限}(`i >= c`・`i > c`・`c <= i` と、偽のときの反対)。"""
        g = self.strip(g); out = {}
        def put(d):
            for k, v in d.items(): out[k] = (min if k[0] == "u" else max)(out.get(k, v), v)
        if g[0] == "bin" and g[1] == "&" and truth:
            for h in (g[2], g[3]): put(self.int_facts(h, True))
        elif g[0] == "bin" and g[1] == "|" and not truth:
            for h in (g[2], g[3]): put(self.int_facts(h, False))
        elif g[0] == "cmp" and len(g[1]) == 2 and len(g[2]) == 1:
            op = g[2][0]
            if not truth:
                op = {"<": ">=", ">": "<=", "<=": ">", ">=": "<"}.get(op)
                if op is None: return out
            l, r = self.strip(g[1][0]), self.strip(g[1][1])
            def idc(e):           # `i`・`i + c`・`c + i`・`i - c` → (名前, 足されている c)
                e = self.strip(e)
                if e[0] == "id": return e[1], 0
                if e[0] == "bin" and e[1] in ("+", "-"):
                    x, y = self.strip(e[2]), self.strip(e[3])
                    if x[0] == "id" and self.const_int(y) is not None: return x[1], self.const_int(y) * (1 if e[1] == "+" else -1)
                    if e[1] == "+" and y[0] == "id" and self.const_int(x) is not None: return y[1], self.const_int(x)
                return None
            if idc(l) is not None and idc(r) is not None and idc(l)[0] != idc(r)[0] and self.const_int(l) is None and self.const_int(r) is None:
                (n1, o1), (n2, o2) = idc(l), idc(r)
                if op in ("<", "<="): n1, o1, n2, o2, op = n2, o2, n1, o1, {"<": ">", "<=": ">="}[op]
                if op in (">", ">="): out[("rel", n1, n2)] = o2 - o1 + (1 if op == ">" else 0)       # n1 ≥ n2 + off
                return out
            if idc(l) is not None and self.const_int(r) is not None: (name, off), c = idc(l), self.const_int(r) - idc(l)[1]
            elif idc(r) is not None and self.const_int(l) is not None:
                (name, off), c = idc(r), self.const_int(l) - idc(r)[1]; op = {"<": ">", "<=": ">=", ">": "<", ">=": "<="}.get(op)
                if op is None: return out
            else: return out
            if op == ">=": out[("i", name)] = c
            elif op == ">": out[("i", name)] = c + 1
            elif op == "<=": out[("u", name)] = c
            elif op == "<": out[("u", name)] = c - 1
        return out

    def lbound(self, e, nn, fx, depth=0):
        """Int の式 e の下限(分かれば整数、でなければ None)。nn = 0 以上と分かっている Int の仮引数、fx = その場の条件から分かる下限の事実。"""
        e = self.strip(e)
        if e[0] == "lit": return e[1] if isinstance(e[1], int) and not isinstance(e[1], bool) else None
        if e[0] == "id":
            v = fx.get(("i", e[1]))
            if e[1] in nn: v = max(0, v) if v is not None else 0
            if depth < 3:                                                # 他の Int との比較 `i >= j + off`(j の下限 + off)
                for k, off in fx.items():
                    if k[0] == "rel" and k[1] == e[1]:
                        lj = self.lbound(("id", k[2]), nn, fx, depth + 1)
                        if lj is not None and (v is None or lj + off > v): v = lj + off
            return v
        if e[0] == "norm": return 0
        if e[0] == "bin" and e[1] in ("+", "*", "/", "%", "-"):
            c = self.const_int(e[3])
            if e[1] == "-":
                p_, q_ = self.strip(e[2]), self.strip(e[3])
                if p_[0] == "id" and q_[0] == "id" and ("rel", p_[1], q_[1]) in fx: return fx[("rel", p_[1], q_[1])]        # i ≥ j + off なら i - j ≥ off
                x = self.lbound(e[2], nn, fx, depth)
                return None if x is None or c is None else x - c
            x, y = self.lbound(e[2], nn, fx, depth), self.lbound(e[3], nn, fx, depth)
            if x is None or y is None: return None
            if e[1] == "+": return x + y
            if x < 0 or y < 0: return None
            return x * y if e[1] == "*" else 0
        return None

    def ubound(self, e, nn, fx):
        """Int の式 e の上限(分かれば整数、でなければ None)。"""
        e = self.strip(e)
        if e[0] == "lit": return e[1] if isinstance(e[1], int) and not isinstance(e[1], bool) else None
        if e[0] == "id": return fx.get(("u", e[1]))
        if e[0] == "bin" and e[1] in ("+", "-", "%", "/", "*"):
            c = self.const_int(e[3])
            if e[1] in ("+", "-"):
                x = self.ubound(e[2], nn, fx)
                if x is None: return None
                if c is not None: return x + (c if e[1] == "+" else -c)
                if e[1] == "+":
                    y = self.ubound(e[3], nn, fx); return None if y is None else x + y
                return None
            if c is None or c <= 0: return None
            if e[1] == "%": return c - 1 if self.nonneg_expr(e[2], nn, fx) else None
            x = self.ubound(e[2], nn, fx)
            if x is None or not self.nonneg_expr(e[2], nn, fx): return None
            return x // c if e[1] == "/" else x * c
        return None

    def nonneg_expr(self, e, nn, fx=None):
        v = self.lbound(e, nn, fx or {})
        return v is not None and v >= 0

    def kform(self, a, kname):
        """a が `kname`・`kname + c`・`c + kname`(c は非負の定数)なら c、でなければ None。"""
        a = self.strip(a)
        if a == ("id", kname): return 0
        if a[0] == "bin" and a[1] == "+":
            l, r = self.strip(a[2]), self.strip(a[3])
            if l == ("id", kname) and self.const_int(r) is not None and self.const_int(r) >= 0: return self.const_int(r)
            if r == ("id", kname) and self.const_int(l) is not None and self.const_int(l) >= 0: return self.const_int(l)
        return None

    def compute_counters(self):
        """輪を通るカウンタの前提(輪の全体で確かめる)。同じ位置の器 x(番号 xi)と Int のカウンタ k(番号 ki)を持つ関数の集合 V の最大の不動点:
        V の関数どうしの呼びは x を同じ位置にそのまま渡し、k を `k + c`(c ≥ 0)で渡す。V の外(関数の外・V でない関数)からの呼びは k に非負の字面だけ渡す。
        すると k は V の中で減らず、x は差し替えられない。戻り値 (xi, ki, V) か None(最大の V が 2 関数未満なら None)。"""
        if getattr(self, "_lbmap", None) is None: self._lbmap = self.build_lbmap()
        sites = []
        def walk(x, caller):
            if isinstance(x, tuple) and x:
                if x[0] == "seq" and x[1] and isinstance(x[1], list) and x[1][0][0] == "id" and x[1][0][1] in self.fns and len(x[1]) - 1 == len(self.fns[x[1][0][1]]):
                    sites.append((caller, x[1][0][1], x[1][1:], x))
                for y in (x[1:] if isinstance(x[0], str) else x): walk(y, caller)
            elif isinstance(x, list):
                for y in x: walk(y, caller)
        for f, body in self.bodies.items(): walk(body, f)
        for n in self.nodes:
            if n[0] != "def": walk(n, None)
        best = None
        maxn = max([len(p) for p in self.fns.values()], default=0)
        for xi in range(maxn):
            for ki in range(maxn):
                if xi == ki: continue
                V = {f for f, ps in self.fns.items() if len(ps) > max(xi, ki) and self.pkind[f][xi] in ("L", "S", "N") and self.pkind[f][ki] == "I" and ps[ki] in self.nonneg.get(f, set())}
                changed = True
                while changed:
                    changed = False
                    for c, g, args, node in sites:
                        if g not in V: continue
                        if c in V: ok = self.strip(args[xi]) == ("id", self.fns[c][xi]) and self.pkind[c][xi] == self.pkind[g][xi] and self.kform(args[ki], self.fns[c][ki]) is not None
                        else: ok = self.const_int(args[ki]) is not None and self.const_int(args[ki]) >= 0
                        if not ok: V.discard(g); changed = True
                if len(V) >= 2 and (best is None or len(V) > len(best[2])): best = (xi, ki, V)
        return best

    def counting_hop(self, f, g, args):
        """f から g への呼びが『数える辺』か: f, g ∈ V で、k を `k + c`(c ≥ 1)で渡し、その呼びの枝の条件で k < ||x|| と分かる。
        (各回の呼びで k が 1 以上増え、k は 0 ≤ k < ||x|| でしか呼べないので、この辺を通る回数は ||x|| 以下。)"""
        if not hasattr(self, "_cr"): self._cr = self.compute_counters()
        if self._cr is None: return False
        xi, ki, V = self._cr
        if f not in V or g not in V or len(args) <= max(xi, ki): return False
        c = self.kform(args[ki], self.fns[f][ki])
        if not c or c < 1: return False
        fx = self._argfacts.get(id(args[ki])) if isinstance(args[ki], tuple) else None
        return bool(fx) and ("lt", self.skey(("id", self.fns[f][ki])), self.fns[f][xi]) in fx

    def compute_nonneg(self):
        """Int の仮引数のうち、関数の外・自分を含む全部の呼びで 0 以上が渡るもの {関数: {名前}}(帰納法。最大の不動点から外れるものを捨てる)。"""
        sites = []
        def walk(x, caller):
            if isinstance(x, tuple) and x:
                if x[0] == "seq" and x[1] and isinstance(x[1], list) and x[1][0][0] == "id" and x[1][0][1] in self.fns and len(x[1]) - 1 == len(self.fns[x[1][0][1]]):
                    sites.append((caller, x[1][0][1], x[1][1:], x))
                for y in (x[1:] if isinstance(x[0], str) else x): walk(y, caller)
            elif isinstance(x, list):
                for y in x: walk(y, caller)
        for f, body in self.bodies.items(): walk(body, f)
        for n in self.nodes:
            if n[0] != "def": walk(n, None)
        nn = {f: {p for p, k in zip(ps, self.pkind[f]) if k == "I"} for f, ps in self.fns.items()}
        changed = True
        while changed:
            changed = False
            for caller, g, args, node in sites:
                fx = self._lbmap.get(id(node), {})
                for p, a in zip(self.fns[g], args):
                    if p in nn[g] and not self.nonneg_expr(a, nn.get(caller, set()), fx):
                        nn[g].discard(p); changed = True
        return nn

    def compute_aliases(self):
        """Int の仮引数 n が、呼ぶたびに器の仮引数 q の長さ + c と等しい(n = ||q|| + c)と分かる関数の表 {関数: {n: (q, c)}}。
        関数の外からの呼びの実引数がその等式を満たし、自分への呼びが等式を保つとき(帰納法)だけ。"""
        sites = []
        def walk(x, caller):
            if isinstance(x, tuple) and x:
                if x[0] == "seq" and x[1] and isinstance(x[1], list) and x[1][0][0] == "id" and x[1][0][1] in self.fns and len(x[1]) - 1 == len(self.fns[x[1][0][1]]):
                    sites.append((caller, x[1][0][1], x[1][1:]))
                for y in (x[1:] if isinstance(x[0], str) else x): walk(y, caller)
            elif isinstance(x, list):
                for y in x: walk(y, caller)
        for f, body in self.bodies.items(): walk(body, f)
        for n in self.nodes:
            if n[0] != "def": walk(n, None)
        def check(args, caller, i, j, hyp):
            ln = self.length_lin(args[j], caller)
            an = self.lin(args[i], hyp)
            if ln is None or an is None: return None
            co = dict(an[0])
            for k, v in ln[0].items(): co[k] = co.get(k, 0) - v
            if any(co.values()): return None
            return an[1] - ln[1]
        # 候補: 別名に頼らない呼び(外からの呼びや、別名なしで書ける呼び)から c が 1 通りに決まる (f, n, q, c)。
        cand = {}
        def hyp_of(caller):
            hyp = {}
            for (ff, nn, qq), v in sorted(cand.items()):
                if ff == caller and nn not in hyp: hyp[nn] = (qq, v)
            return hyp
        for _ in range(6):                       # 別名に頼る呼びも、呼ぶ側の候補を仮定して候補を増やす(あとで帰納法で確かめる)
            grew = False
            for f, ps in self.fns.items():
                for i, ki in enumerate(self.pkind[f]):
                    if ki != "I": continue
                    for j, kj in enumerate(self.pkind[f]):
                        if kj not in ("L", "S") or (f, ps[i], ps[j]) in cand: continue
                        cs0 = {x for x in (check(a, c, i, j, hyp_of(c)) for c, g, a in sites if g == f) if x is not None}
                        if len(cs0) == 1: cand[(f, ps[i], ps[j])] = next(iter(cs0)); grew = True
            if not grew: break
        # 帰納法: 全部の呼びが(呼ぶ側の候補を仮定して)等式を満たすものだけ残す。外れたものを捨てて、変わらなくなるまで繰り返す
        changed = True
        while changed:
            changed = False
            for (f, n, q), c0 in list(cand.items()):
                i, j = self.fns[f].index(n), self.fns[f].index(q)
                for caller, g, a in sites:
                    if g != f: continue
                    hyp = {}
                    for (ff, nn, qq), v in sorted(cand.items()):
                        if ff == caller and nn not in hyp: hyp[nn] = (qq, v)
                    if check(a, caller, i, j, hyp) != c0:
                        del cand[(f, n, q)]; changed = True; break
        al = {}
        for (f, n, q), v in sorted(cand.items()): al.setdefault(f, {}).setdefault(n, (q, v))
        return al

    def lin(self, e, al=None):
        """e が ||p|| の一次式(整数係数)なら ({p: 係数}, 定数)、でなければ None。al は Int の仮引数 n → (器の仮引数 q, c)(n = ||q|| + c と分かっているもの)。"""
        e = self.strip(e)
        if e[0] == "lit" and isinstance(e[1], int): return ({}, e[1])
        if al and e[0] == "id" and e[1] in al: return ({al[e[1]][0]: 1}, al[e[1]][1])
        if e[0] == "norm" and self.strip(e[1])[0] == "id": return ({self.strip(e[1])[1]: 1}, 0)
        if e[0] == "norm" and self.strip(e[1])[0] == "bin" and self.strip(e[1])[1] == "'" and self.slice_of(self.strip(e[1])) is None and self.tail_of(self.strip(e[1])) is None:
            return ({("elen", self.skey(e[1])): 1}, 0)                       # 入れ子の要素の長さ ||m ' i|| も、条件から下限を取れる擬似的な仮引数

        if e[0] == "neg":
            r = self.lin(e[1], al); return None if r is None else ({k: -v for k, v in r[0].items()}, -r[1])
        if e[0] == "bin" and e[1] in ("+", "-"):
            l, r = self.lin(e[2], al), self.lin(e[3], al)
            if l is None or r is None: return None
            sg = 1 if e[1] == "+" else -1
            co = dict(l[0])
            for k, v in r[0].items(): co[k] = co.get(k, 0) + sg * v
            return ({k: v for k, v in co.items() if v}, l[1] + sg * r[1])
        if e[0] == "bin" and e[1] == "*":
            l, r = self.lin(e[2], al), self.lin(e[3], al)
            if l is None or r is None: return None
            if not l[0]: return ({k: v * l[1] for k, v in r[0].items() if v * l[1]}, r[1] * l[1])
            if not r[0]: return ({k: v * r[1] for k, v in l[0].items() if v * r[1]}, l[1] * r[1])
        return None

    def ge_facts(self, co, c, base):
        """Σ k_i·||p_i|| + c ≥ 0 から分かる {p: 長さの下限}。他の項は負の係数(=下限が使える向き)のものだけのとき、その項の下限(既知か 1)を使う。"""
        out = {}
        for p, k in co.items():
            if k <= 0: continue
            others = [(q, kk) for q, kk in co.items() if q != p]
            if any(kk > 0 for _, kk in others): continue
            need = -c + sum(-kk * max(1, base.get(q, 0)) for q, kk in others)
            lb = -((-need) // k)                    # 切り上げ
            if lb > 0: out[p] = lb
        return out

    def skey(self, e):
        """式の構造を比べるための鍵(ブロックの括弧は外す)。"""
        e = self.strip(e)
        if isinstance(e, tuple): return tuple(self.skey(x) if isinstance(x, tuple) else (tuple(self.skey(y) if isinstance(y, tuple) else y for y in x) if isinstance(x, list) else x) for x in e)
        return e

    def elem_facts(self, a, op, b, al=None):
        """`a < b` / `a <= b`(真)から、非自明な式 e についての事実: ("ge0", 鍵)(e ≥ 0)、("lt", 鍵, p)(e < ||p||)。"""
        out = {}
        la, lb_ = self.lin(a, al), self.lin(b, al)
        if la is not None and not la[0] and lb_ is None:                     # c < e / c <= e
            c0 = la[1]
            if (op == "<" and c0 >= -1) or (op == "<=" and c0 >= 0): out[("ge0", self.skey(b))] = 1
        if lb_ is not None and la is None and len(lb_[0]) == 1:              # e < ||p|| + c / e <= ||p|| + c
            (p, k), = lb_[0].items(); c0 = lb_[1]
            if k == 1 and ((op == "<" and c0 <= 0) or (op == "<=" and c0 <= -1)): out[("lt", self.skey(a), p)] = 1
        return out

    def lb_facts(self, g, truth, base=None, al=None):
        """条件 g が truth(真/偽)のとき分かる {仮引数: 長さの下限}。分からなければ {}。base はそれまでに分かっている下限。"""
        base = base or {}
        g = self.strip(g)
        out = {}
        def put(d):
            for k, v in d.items(): out[k] = max(out.get(k, 0), v)
        if g[0] == "bin" and g[1] == "&" and truth:
            for h in (g[2], g[3]): put(self.lb_facts(h, True, base, al))
        elif g[0] == "bin" and g[1] == "|" and not truth:
            for h in (g[2], g[3]): put(self.lb_facts(h, False, base, al))
        elif g[0] == "cmp" and len(g[1]) == 2 and len(g[2]) == 1:
            l, r = self.lin(g[1][0], al), self.lin(g[1][1], al); op = g[2][0]
            if not truth:
                if op == "=" and l is not None and r is not None:                      # `||p|| = c` が偽: 下限が c ちょうどなら c + 1(仮引数の器は空でない=下限は 1 から)
                    co_ = dict(l[0])
                    for k_, v_ in r[0].items(): co_[k_] = co_.get(k_, 0) - v_
                    co_ = {k_: v_ for k_, v_ in co_.items() if v_}; c_ = l[1] - r[1]
                    if len(co_) == 1:
                        (p_, k_), = co_.items()
                        if abs(k_) == 1 and not isinstance(p_, tuple) and max(1, base.get(p_, 0)) == -c_ * k_: out[p_] = -c_ * k_ + 1
                    return out
                op = {"<": ">=", ">": "<=", "<=": ">", ">=": "<"}.get(op)
                if op is None: return out
            if l is None or r is None:                                         # 要素など ||p|| の式でないものの事実
                A, B = g[1][0], g[1][1]
                if op in (">", ">="): A, B, op = B, A, {">": "<", ">=": "<="}[op]
                if op in ("<", "<="): put(self.elem_facts(A, op, B, al))
                return out
            co = dict(l[0])
            for k, v in r[0].items(): co[k] = co.get(k, 0) - v
            co = {k: v for k, v in co.items() if v}; c = l[1] - r[1]          # L = 左 − 右
            neg = ({k: -v for k, v in co.items()}, -c)
            forms = {">": [(co, c - 1)], ">=": [(co, c)], "<": [(neg[0], neg[1] - 1)], "<=": [neg], "=": [(co, c), neg]}.get(op, [])
            for cc, c0 in forms: put(self.ge_facts(cc, c0, base))
        return out

    def build_lbmap(self):
        m = {}
        def merge(a, b):
            r = dict(a)
            for k, v in b.items(): r[k] = ((min if (isinstance(k, tuple) and k[0] == "u") else max)(r[k], v)) if k in r else v
            return r
        lbf = lambda g, t, acc: merge(self.lb_facts(g, t, acc, self._al_cur), self.int_facts(g, t))
        def walk(x, facts, gl=()):
            if isinstance(x, tuple) and x:
                if x[0] == "cases":
                    acc, accg = facts, gl
                    for g, v in x[1]:
                        if g is None: walk(v, acc, accg); continue
                        walk(g, acc, accg)
                        walk(v, merge(acc, lbf(g, True, acc)), accg + ((g, True),))
                        acc = merge(acc, lbf(g, False, acc)); accg = accg + ((g, False),)
                    return
                if (x[0] == "bin" and x[1] == "'") or (x[0] == "seq" and x[1] and isinstance(x[1], list) and x[1][0][0] == "id" and x[1][0][1] in self.fns): m[id(x)] = facts; self._fnof[id(x)] = self._f_cur; self._guards[id(x)] = gl
                if x[0] == "seq" and x[1] and isinstance(x[1], list) and x[1][0][0] == "id" and x[1][0][1] in self.fns:
                    for ax in x[1][1:]:
                        if isinstance(ax, tuple):
                            old = self._argfacts.get(id(ax))
                            self._argfacts[id(ax)] = dict(facts) if old is None else {k: (max if (isinstance(k, tuple) and k[0] == "u") else min)(v, old[k]) for k, v in facts.items() if k in old}
                for y in (x[1:] if isinstance(x[0], str) else x): walk(y, facts, gl)
            elif isinstance(x, list):
                for y in x: walk(y, facts, gl)
        self._fnof = {}; self._argfacts = {}; self._guards = {}
        al_all = self.aliases = self.compute_aliases()
        for f, body in self.bodies.items():
            al = al_all.get(f, {})
            self._al_cur = al; self._f_cur = f
            walk(body, {})
        self._lbmap = m
        self.nonneg = self.compute_nonneg()
        return m

    def idx_ok_old(self, n):
        """`p ' i`(p は仮引数。i は定数か `||p||` の一次式)が、枝の条件から必ず範囲内と言えるか。"""
        if n[0] != "bin" or n[1] != "'" or self.slice_of(n) is not None or self.tail_of(n) is not None: return False
        l = self.strip(n[2])
        if l[0] == "bin" and l[1] == "'" and self.slice_of(l) is None and self.tail_of(l) is None:      # (m ' i) ' 0: 入れ子の要素(内側)は空でないので、先頭・末尾は在る
            c_ = self.const_int(n[3])
            if c_ is None or not self.idx_ok(l): return False
            if c_ in (0, -1): return True
            lbe = self._lbmap.get(id(n), {}).get(("elen", self.skey(l)), 0)
            return (c_ >= 0 and c_ < lbe) or (c_ < 0 and -c_ <= lbe)
        if l[0] != "id": return False
        c = self.const_int(n[3])
        if getattr(self, "_lbmap", None) is None: self._lbmap = self.build_lbmap()
        lb = max(1, self._lbmap.get(id(n), {}).get(l[1], 0))
        if c is not None: return c < lb if c >= 0 else -c <= lb
        ix = self.strip(n[3])
        if ix[0] == "bin" and ix[1] == "-" and self.strip(ix[3]) == ("norm", ("id", l[1])) and self.lin(ix[2], self.aliases.get(self._fnof.get(id(n)), {})) is None:
            # a - ||p||: a が 0 以上で ||p|| 未満なら -||p||..-1(末尾から数える)で範囲内
            fx_ = self._lbmap.get(id(n), {}); nn_ = self.nonneg.get(self._fnof.get(id(n)), set()); a_ = ix[2]
            if not self.nonneg_expr(a_, nn_, fx_): return False
            ub_ = self.ubound(a_, nn_, fx_)
            return ("lt", self.skey(a_), l[1]) in fx_ or (ub_ is not None and ub_ < lb)
        if ix[0] == "bin" and ix[1] == "%":                              # a % ||p||(余りの符号は割られる数に従う): 結果は -(||p||-1)..||p||-1 で、負なら末尾から数えるので常に範囲内
            dn = self.lin(ix[3], self.aliases.get(self._fnof.get(id(n)), {}))
            if dn is not None and dn[0] == {l[1]: 1} and dn[1] == 0: return True
        if ix[0] == "bin" and ix[1] == "/" and (self.const_int(ix[3]) or 0) >= 2:          # (||p|| + c) / d: 商は 0..||p||-1(下限 lb から単調に効く)
            d = self.const_int(ix[3]); ln = self.lin(ix[2], self.aliases.get(self._fnof.get(id(n)), {}))
            if ln is not None and set(ln[0]) == {l[1]} and 1 <= ln[0][l[1]] <= d and ln[0][l[1]] * lb + ln[1] >= 0:      # 係数 k ≤ d なら L - 1 - (kL+c)/d は L と共に減らない
                return (ln[0][l[1]] * lb + ln[1]) // d <= lb - 1
            return False
        li = self.lin(n[3], self.aliases.get(self._fnof.get(id(n)), {}))
        if li is None:                                                  # 要素など: 条件で 0 ≤ e < ||p|| と分かっている
            fx = self._lbmap.get(id(n), {})
            key = self.skey(n[3])
            nn_ = self.nonneg.get(self._fnof.get(id(n)), set())
            ge0 = ("ge0", key) in fx or self.nonneg_expr(n[3], nn_, fx)
            if ge0 and ("lt", key, l[1]) in fx: return True
            ub = self.ubound(n[3], nn_, fx)                                  # 0 ≤ e ≤ 定数 < 器の長さの下限
            return bool(self.nonneg_expr(n[3], nn_, fx) and ub is not None and ub < lb)
        if set(li[0]) - {l[1]}: return False
        k, c0 = li[0].get(l[1], 0), li[1]
        if k == 1: return c0 <= -1 and lb + c0 >= 0                     # ||p|| + c0 は 0..||p||-1
        if k == 0: return 0 <= c0 < lb
        return False

    def idx_ok(self, n):
        """`p ' e` が必ず範囲内か。従来の規則(idx_ok_old)で言えなければ、枝の条件の全体を線形制約にして証明器で確かめる(prove_idx)。"""
        if os.environ.get("SIGN_OLD") != "0" and self.idx_ok_old(n): return True            # SIGN_OLD=0: 個別規則を使わず証明器だけ(比較用)
        if os.environ.get("SIGN_PROVE") == "0": return False
        try: r = self.prove_idx(n)
        except (KeyError, RecursionError): r = False
        if r: self.prove_gain = getattr(self, "prove_gain", 0) + 1
        return r

    def prove_idx(self, n):
        """n = `p ' e`(p は器の仮引数)。経路の条件(行の守り: 前の行は偽、この行は真)と仮引数の事実を線形制約にし、`e ≥ ||p||` と `e ≤ -||p|| - 1` がどちらも成り立たないことを証明する(Fourier-Motzkin)。"""
        from sign_prove import Sys
        if n[0] != "bin" or n[1] != "'" or self.slice_of(n) is not None or self.tail_of(n) is not None: return False
        if getattr(self, "_lbmap", None) is None: self._lbmap = self.build_lbmap()
        f = self._fnof.get(id(n)); l = self.strip(n[2])
        if f is None: return False
        if l[0] == "id" and l[1] in self.fns[f] and self.pkind[f][self.fns[f].index(l[1])] in ("L", "S", "N"): lkey = "len:" + l[1]
        elif (l[0] == "bin" and l[1] == "'" and self.slice_of(l) is None and self.tail_of(l) is None and self.strip(l[2])[0] == "id" and self.strip(l[2])[1] in self.fns[f]
              and self.pkind[f][self.fns[f].index(self.strip(l[2])[1])] == "N" and self.idx_ok(l)):
            lkey = "elen:" + repr(self.skey(l))                                   # 入れ子の要素 `m ' i`(取り出し自体が範囲内と分かるもの)の長さ
        else: return False
        al = self.aliases.get(f, {}); nn = self.nonneg.get(f, set()); sysm = Sys(); seen = set()
        def atom(name, lo=None):
            if name not in seen:
                seen.add(name)
                if lo is not None: sysm.add({name: 1}, -lo)
            return ({name: 1}, 0)
        def ladd(a, b, k=1): 
            c = dict(a[0])
            for x, v in b[0].items(): c[x] = c.get(x, 0) + k * v
            return (c, a[1] + k * b[1])
        def lin(e):
            e = self.strip(e)
            cv = self.const_int(e)
            if cv is not None: return ({}, cv)
            if e[0] == "id":
                if e[1] in al: q, c0 = al[e[1]]; r = atom("len:" + q, 1); return (r[0], c0)
                if e[1] in self.fns[f] and self.pkind[f][self.fns[f].index(e[1])] == "I": return atom("v:" + e[1], 0 if e[1] in nn else None)
                return None
            if e[0] == "norm":
                x = self.strip(e[1])
                if x[0] == "id" and x[1] in self.fns[f] and self.pkind[f][self.fns[f].index(x[1])] in ("L", "S", "N"): return atom("len:" + x[1], 1)
                if x[0] == "bin" and x[1] == "'" and self.slice_of(x) is None and self.tail_of(x) is None: return atom("elen:" + repr(self.skey(x)), 1)
                return None
            if e[0] == "neg":
                r = lin(e[1]); return None if r is None else ({k: -v for k, v in r[0].items()}, -r[1])
            if e[0] == "bin" and e[1] == "'" and self.slice_of(e) is None and self.tail_of(e) is None: return atom("el:" + repr(self.skey(e)))
            if e[0] == "bin" and e[1] in ("+", "-"):
                a, b = lin(e[2]), lin(e[3])
                return None if a is None or b is None else ladd(a, b, 1 if e[1] == "+" else -1)
            if e[0] == "bin" and e[1] == "*":
                a, b = lin(e[2]), lin(e[3])
                if a is None or b is None: return None
                if not a[0]: return ({k: v * a[1] for k, v in b[0].items()}, b[1] * a[1])
                if not b[0]: return ({k: v * b[1] for k, v in a[0].items()}, a[1] * b[1])
                if self.nonneg_expr(e, nn): return atom("p:" + repr(self.skey(e)), 0)
                return None
            if e[0] == "bin" and e[1] in ("%", "/"):
                a = lin(e[2]); den = self.strip(e[3]); c = self.const_int(den)
                nnum = self.nonneg_expr(e[2], nn)
                key = repr(self.skey(e))
                if e[1] == "%":
                    if c is not None and c > 0:
                        r = atom("m:" + key)
                        sysm.add(r[0], c - 1); sysm.add({k: -v for k, v in r[0].items()}, c - 1)
                        if nnum: sysm.add(r[0], 0)
                        return r
                    if den[0] == "norm":
                        L = lin(den)
                        if L is None: return None
                        r = atom("m:" + key)
                        lo = ladd(L, r, -1); lo = (lo[0], lo[1] - 1); sysm.add(lo[0], lo[1])              # L - 1 - r ≥ 0
                        hi = ladd(L, r, 1); hi = (hi[0], hi[1] - 1); sysm.add(hi[0], hi[1])              # L - 1 + r ≥ 0
                        if nnum: sysm.add(r[0], 0)
                        return r
                    return None
                if c is not None and c > 0 and nnum and a is not None:
                    q = atom("d:" + key)
                    t = ({k: c * v for k, v in q[0].items()}, 0)
                    d1 = ladd(a, t, -1); sysm.add(d1[0], d1[1])                                       # a - c·q ≥ 0
                    d2 = ladd(t, a, -1); sysm.add(d2[0], d2[1] + c - 1)                               # c·q + c-1 - a ≥ 0
                    sysm.add(q[0], 0)
                    return q
                return None
            return None
        def guard(g, truth):
            g = self.strip(g)
            if g[0] == "bin" and g[1] == "&" and truth: guard(g[2], True); guard(g[3], True); return
            if g[0] == "bin" and g[1] == "|" and not truth: guard(g[2], False); guard(g[3], False); return
            if g[0] != "cmp": return
            ops = g[2]; xs = g[1]
            if len(ops) > 1 and not truth: return
            for k, op in enumerate(ops):
                if not truth: op = {"<": ">=", ">": "<=", "<=": ">", ">=": "<"}.get(op)
                if op is None: continue
                a, b = lin(xs[k]), lin(xs[k + 1])
                if a is None or b is None: continue
                if op == "<": d = ladd(b, a, -1); sysm.add(d[0], d[1] - 1)
                elif op == "<=": d = ladd(b, a, -1); sysm.add(d[0], d[1])
                elif op == ">": d = ladd(a, b, -1); sysm.add(d[0], d[1] - 1)
                elif op == ">=": d = ladd(a, b, -1); sysm.add(d[0], d[1])
                elif op == "=": d = ladd(a, b, -1); sysm.eq(d[0], d[1])
        for g, truth in self._guards.get(id(n), ()): guard(g, truth)
        e = lin(n[3]); L = atom(lkey, 1)
        if e is None: return False
        base = list(sysm.cs)
        s1 = Sys(); s1.cs = list(base); d = ladd(e, L, -1); s1.add(d[0], d[1])                       # e - L ≥ 0 (上に外れる)
        if not s1.unsat(): return False
        s2 = Sys(); s2.cs = list(base); d = ladd(({k: -v for k, v in e[0].items()}, -e[1]), L, -1); s2.add(d[0], d[1] - 1)       # -e - L - 1 ≥ 0 (下に外れる)
        return s2.unsat()

    def nonempty(self, x):
        """x は空でない器か。仮引数・名前(`__` の器の呼びは走らない)と、入れ子の仮引数の先頭・末尾の内側(内側は空にならない。空の内側は並びから消える)。"""
        x = self.strip(x)
        if x[0] == "id": return x[1] != "__" and not (x[1] in self.consts and self.consts[x[1]] is None) and x[1] not in self.rule_names
        return x[0] == "bin" and x[1] == "'" and self.const_int(x[3]) in (0, -1) and self.slice_of(x) is None and self.tail_of(x) is None and self.nonempty(x[2])

    def check_view(self, x):
        """入れ子の要素にする既存の器 x(コピーせず {ptr, len} を写す)が、この関数の外に生き残る物か。組み立て中の関数の置き場は返った後に消える。
        戻り値は『`__` になりうるか』: `__` の要素は入れ子に入らず並びから消える(個数が実行時に決まる)。"""
        x = self.strip(x)
        if x[0] == "id": return False                                 # 仮引数(`__` なら本体は走らない)・字面の名前
        if self.list_values(x) is not None: return False
        if x[0] == "bin" and x[1] == "'":
            if self.slice_of(x) is not None and self.slice_in_range(x): return False
            if self.tail_of(x) is None and self.slice_of(x) is None and self.const_int(x[3]) in (0, -1) and self.nonempty(x[2]): return False      # 空でない入れ子の先頭・末尾の内側(呼ぶ側の物)
            if self.tail_of(x) is None and self.slice_of(x) is None and self.nonempty(x[2]) and self.const_int(x[3]) is not None: return True       # 範囲の外になりうる内側: `__` で、並びから消える
            raise AsmError("入れ子の要素にする取り出し・スライスが範囲の外になりうる形はまだ出せません(`__` は入れ子に入らず並びから消え、種類が実行時に変わるため)")
        if x[0] == "seq" and x[1][0][0] == "id" and x[1][0][1] in self.fns:
            g = x[1][0][1]
            if self.bound.get(g) is not None: raise AsmError("入れ子の要素に、器を組み立てて返す関数の結果(%s)は置けません(その置き場は呼ぶ側の物で、arena に移すコピーがまだ無い)" % g)
            if self.ret_maybe.get(g, False): raise AsmError("入れ子の要素に、`__` を返しうる関数の結果(%s)は置けません" % g)
            return False
        raise AsmError("入れ子の要素にできる形ではありません(仮引数・字面・定数端のスライス・器を組み立てない関数の結果だけ)")

    def str_value(self, n):
        """n が文字列の字面なら文字コードの並び(ASCII・1 文字 1 バイト。target_info.sn の ascii)、でなければ None。
        字面・文字の字面・文字列の名前だけを並置した並び(`` `ab` `cd` ``)は連結した文字列(list_model.md §4.2 の余積)。"""
        while n[0] == "block": n = n[1]
        if n[0] == "bin" and n[1] == "*":                       # Char * Int(定数)は文字列の繰り返し(`0u30 * 3` = `000`)
            ch = self.strip(n[2]); cnt = self.const_int(n[3])
            if ch[0] == "lit" and isinstance(ch[1], Char) and len(ch) == 2 and cnt is not None:
                if not char_ok(ord(ch[1])): raise AsmError(char_msg())
                if cnt < 1: raise AsmError("`Char * Int` の回数が 1 未満です(結果は `__`。文字列の種類にならないので出せません)")
                if cnt > self.RANGE_LIMIT: raise AsmError("`Char * Int` の回数が %d 回あり、大きすぎます(.rodata に広げるので %d 回まで)" % (cnt, self.RANGE_LIMIT))
                return [ord(ch[1])] * cnt
            return None
        if n[0] == "seq" and len(n[1]) >= 2 and not (n[1][0][0] == "id" and n[1][0][1] in self.fns):
            out, has = [], False
            for it in n[1]:
                while it[0] == "block": it = it[1]
                if it[0] == "id" and it[1] in self.strs: out += self.strs[it[1]][1]; has = True; continue
                iv = self.const_int(it) if it[0] in ("lit", "neg", "id") else None
                if iv is not None and not (it[0] == "lit" and isinstance(it[1], str)):
                    out += [ord(c) for c in str(iv)]; continue                 # 数は十進の文字列にして並べる
                if it[0] == "id" and it[1] in self.consts and self.consts[it[1]] is None: continue     # `__` は並びから消える
                if it == ("id", "__"): continue
                if it[0] == "bin" and it[1] == "*":
                    sub = self.str_value(it)
                    if sub is None: return None
                    out += sub; has = True; continue
                if it[0] != "lit" or not isinstance(it[1], str) or len(it) != 2: return None
                if isinstance(it[1], Char):
                    if not char_ok(ord(it[1])): raise AsmError(char_msg())
                    out.append(ord(it[1]))
                else: out += self.str_value(it); has = True
            return out if has else None
        if n[0] != "lit" or not isinstance(n[1], str) or isinstance(n[1], Char) or len(n) != 2: return None
        t = n[1]
        if "\\" in t: raise AsmError("文字列の中のエスケープ(\\)はまだ出せません")
        if any(not char_ok(ord(c)) for c in t): raise AsmError(char_msg())
        return [ord(c) for c in t]

    @staticmethod
    def strip(n):
        while n[0] == "block": n = n[1]
        return n

    @staticmethod
    def rule_parts(n):
        """範囲 `a ~ b` / `a ~+ s ~ b` の (始まり, 歩幅 または None, 終わり)。"""
        lo, hi, step = n[2], n[3], None
        while lo[0] == "block": lo = lo[1]
        if lo[0] == "bin" and lo[1] == "~+": lo, step = lo[2], lo[3]
        return lo, step, hi

    def const_int(self, n):
        """n が定数の Int(字面・負の字面・定数名・それらの + - *)なら値、でなければ None。"""
        while n[0] == "block": n = n[1]
        if n[0] == "lit": return n[1] if isinstance(n[1], int) and not isinstance(n[1], bool) and abs(n[1]) <= INT_MAX else None
        if n[0] == "neg": v = self.const_int(n[1]); return -v if v is not None else None
        if n[0] == "id": c = self.consts.get(n[1]); return c if isinstance(c, int) else None
        if n[0] == "bin" and n[1] == "'":                          # 定数の並びの定数の添字(`(7 8) ' 1`)は、範囲の中だけ畳む(外は `__` になるので畳まない)
            l = n[2]
            while l[0] == "block": l = l[1]
            k = self.const_int(n[3])
            if l[0] != "seq" or k is None or not 0 <= k < len(l[1]): return None
            vs = [self.const_int(e) for e in l[1]]
            if any(v is None for v in vs): return None             # `__` になる要素は並びから消える(`(__ 2) ' 1` は `__`)ので、全部が定数の Int のときだけ畳む
            return vs[k]
        if n[0] == "bin" and n[1] in ("+", "-", "*"):
            a, b = self.const_int(n[2]), self.const_int(n[3])
            if a is None or b is None: return None
            v = a + b if n[1] == "+" else a - b if n[1] == "-" else a * b
            return v if abs(v) <= INT_MAX else None
        return None

    CMP = {"<": lambda a, b: a < b, ">": lambda a, b: a > b, "<=": lambda a, b: a <= b, ">=": lambda a, b: a >= b, "=": lambda a, b: a == b, "!=": lambda a, b: a != b}

    def const_cmp(self, n):
        """定数どうしの比べ(`3 < 5`、`c != 2`)を畳む。処理系の読み(観測): 真なら左辺の値、偽なら `__`。戻りは (True, 値 か None=`__`)、畳めなければ None。
        比べの被演算子は const_int で畳める Int だけ(`__` を含む算術は畳まない)。"""
        while n[0] == "block": n = n[1]
        if n[0] != "cmp" or len(n[2]) != 1 or n[2][0] not in self.CMP or len(n[1]) != 2: return None          # 連なった比べ(`1 < x < 20`)は畳まない
        a, b = self.const_int(n[1][0]), self.const_int(n[1][1])
        if a is None or b is None: return None
        return (True, a if self.CMP[n[2][0]](a, b) else None)

    NOF = object()

    def const_val(self, n):
        """畳める定数の式の値: Int、`__`(None)、畳めなければ NOF。
        処理系の観測: 片方が `__` の + - * / % は、もう片方をそのまま返す(`__ - 1` は 1、`2 / __` は 2)。両方 `__` なら `__`。`-__` は `__`。
        比べは、被演算子が `__` なら `__`、Int どうしなら真で左辺・偽で `__`。Int どうしの / % は畳まない(割り算の丸めは asm の側の読みに任せる)。"""
        while n[0] == "block": n = n[1]
        c = self.const_cmp(n)
        if c is not None: return c[1]
        if n[0] == "cmp" and len(n[2]) == 1 and n[2][0] in self.CMP and len(n[1]) == 2:
            a, b = self.const_val(n[1][0]), self.const_val(n[1][1])
            return None if (a is not self.NOF and b is not self.NOF and (a is None or b is None)) else self.NOF
        if n[0] == "id" and n[1] in self.consts:
            v = self.consts[n[1]]
            return v if v is None or isinstance(v, int) and not isinstance(v, bool) else self.NOF
        if n[0] == "id" and n[1] == "__": return None
        v = self.const_int(n)
        if v is not None: return v
        if n[0] == "neg":
            a = self.const_val(n[1]); return None if a is None else self.NOF
        if n[0] == "bin" and n[1] == "|":                    # `(0x4 * 1) | 4`(幅の定義。--strict では左が番地、既定では左が `__` で右が答え)。両辺が同じ数に畳めるときだけ畳む(どちらのモードでも同じ値)
            a, b = self.const_val(n[2]), self.const_val(n[3])
            return a if a is not self.NOF and a is not None and a == b else self.NOF
        if n[0] == "bin" and n[1] in ("+", "-", "*", "/", "%"):
            a, b = self.const_val(n[2]), self.const_val(n[3])
            if a is self.NOF or b is self.NOF: return self.NOF
            if a is None and b is None: return None
            if a is None: return b
            if b is None: return a
        return self.NOF

    RANGE_LIMIT = 4096

    def range_values(self, n):
        """n が端も刻みも定数の範囲 `[a ~ b]` `[a ~+ s ~ b]` なら要素の並び(.rodata に広げる)、でなければ None。"""
        while n[0] == "block": n = n[1]
        if n[0] != "bin" or n[1] != "~": return None
        lo, hi, step = n[2], n[3], None
        if lo[0] == "bin" and lo[1] == "~+": lo, step = lo[2], lo[3]
        a, b = self.const_int(lo), self.const_int(hi)
        st = self.const_int(step) if step is not None else (1 if a is not None and b is not None and a <= b else -1)
        if a is None or b is None or st is None: return None
        if st == 0: raise AsmError("範囲の刻みが 0 です(進みません)")
        if (st > 0 and a > b) or (st < 0 and a < b): return None
        cnt = (b - a) // st + 1
        if cnt > self.RANGE_LIMIT: raise AsmError("範囲が %d 個あり、大きすぎます(.rodata に広げるので %d 個まで。規則{start, step, end}の値渡しはまだ出せません)" % (cnt, self.RANGE_LIMIT))
        return [a + st * i for i in range(cnt)]

    def eaten_positions(self):
        """プログラム中の関数呼びのうち、末尾の切り出し `p ' a~` を渡している実引数の位置の集合(位置は 0 起点。輪の仲間は位置を揃える前提)。"""
        if getattr(self, "_eaten_q", None) is None:
            out = set()
            def walk(x):
                if isinstance(x, tuple) and x:
                    if x[0] == "seq" and x[1] and isinstance(x[1], list) and x[1][0][0] == "id" and x[1][0][1] in self.fns:
                        for q, a in enumerate(x[1][1:]):
                            try:
                                if isinstance(a, tuple) and self.tail_of(a) is not None: out.add(q)
                            except AsmError: pass
                    for y in (x[1:] if isinstance(x[0], str) else x): walk(y)
                elif isinstance(x, list):
                    for y in x: walk(y)
            for b in self.bodies.values(): walk(b)
            self._eaten_q = out
        return self._eaten_q

    def tail_of(self, n):
        """n が末尾の切り出し `器 ' a~`(か `器 ' [a ~]`。a は非負の定数)なら (器, a)、でなければ None。
        a 番目から終わりまで(コピーしない視点)。a 個以下しか無ければ `__`(設計者の『器を食う』再帰が毎段で使う形)。"""
        while n[0] == "block": n = n[1]
        if n[0] != "bin" or n[1] != "'": return None
        idx = n[3]   # 括弧で包んだ `(a~)` は処理系で別の意味(`__`)になるので剥がさない
        if idx[0] == "post" and idx[1] == "~": a = idx[2]
        elif idx[0] == "sec" and idx[1] == "left" and idx[2] == "~" and not idx[4]: a = idx[3]
        else: return None
        v = self.const_int(a)
        if v is None: raise AsmError("末尾の切り出し `p ' a~` は a が定数のときだけ出せます")
        if v < 0: raise AsmError("末尾の切り出しの始まりが負の形はまだ出せません")
        return (n[2], v)

    def eat_index(self, x, f):
        """x が f 自身の呼びで、器の仮引数を 1 つだけ末尾切り出し `p ' a~`(a ≥ 1。毎段で短くなる)にして渡し、ほかの器は同じ仮引数のまま渡す形なら、
        食われる仮引数の番号。そうでなければ None(設計者の selfConsumes)。"""
        x = self.strip(x)
        if not (f in self.fns and x[0] == "seq" and x[1][0] == ("id", f)): return None
        eaten = None
        for j, a in enumerate(x[1][1:]):
            if j >= len(self.pkind[f]) or self.pkind[f][j] not in WIDE: continue
            if self.strip(a) == ("id", self.fns[f][j]): continue
            tl = self.tail_of(a)
            if tl and self.strip(tl[0]) == ("id", self.fns[f][j]) and tl[1] >= 1 and eaten is None: eaten = j; continue
            if self.grow_form(a, f, j) is not None: continue          # 累積を後ろへ伸ばして渡す(食う器は別に要る)
            return None
        return eaten

    def same_or_shrunk(self, a, f, j):
        """f の自分への呼びの第 j 引数 a が、仮引数のまま、か、その末尾切り出し(同じか短い)か。短くなる方向なら返る器の上界は変わらない。"""
        if self.strip(a) == ("id", self.fns[f][j]): return True
        tl = self.tail_of(a)
        return bool(tl and self.strip(tl[0]) == ("id", self.fns[f][j]))

    def grow_form(self, a, f, j):
        """a が `acc~ x y`(L: 第 j 仮引数 acc の後ろへ Int の式を d 個足す)か `acc c1 c2`(S: 後ろへ文字・字面の文字列を足す)なら、1 回に伸びる上界 d(L は個数、S はバイト数)。でなければ None。"""
        its = self.builds(self.strip(a))
        if not its or self.pkind[f][j] not in ("L", "S"): return None
        ty, x = self.item_info(its[0])
        want = "spread" if self.pkind[f][j] == "L" else "scalar"
        if ty != want or self.strip(x) != ("id", self.fns[f][j]): return None
        rest = its[1:]
        if not rest: return None
        if self.pkind[f][j] == "L":
            if any(self.item_info(it)[0] != "scalar" for it in rest): return None
            if any(self.maybe(it) for it in rest): raise AsmError("%s: 累積に足す要素が `__` になりうる形はまだ出せません(並びから消えるので長さが変わる)" % f)
            return len(rest)
        env = dict(zip(self.fns[f], self.pkind[f]))
        d = 0
        for it in rest:
            if self.item_info(it)[0] != "scalar": return None
            x = self.strip(it); kx = self.kind(x, env)
            if kx == "C": d += 1
            elif kx == "S" and self.str_value(x) is not None: d += len(self.str_value(x))
            else: raise AsmError("%s: 文字列の累積に足せるのは、文字と字面の文字列だけです(数の綴り・長さが実行時に決まる文字列はまだ)" % f)
        return d

    def is_acc_arg(self, a, name):
        """実引数 a が `name 要素…`(仮引数 name の後ろへ足す形)か。"""
        a = self.strip(a)
        its = self.builds(a) if a[0] == "seq" else None
        return bool(its) and len(its) >= 2 and self.strip(self.item_info(its[0])[1]) == ("id", name)

    def grow_src(self, a, f):
        """a が `P~ x y`(f の L の仮引数 P の後ろへ Int の式を足す)なら (P の番号, 足す個数)。でなければ None。"""
        its = self.builds(self.strip(a)) if self.strip(a)[0] == "seq" else None
        if not its or len(its) < 2: return None
        ty, x = self.item_info(its[0]); x = self.strip(x)
        if ty != "spread" or x[0] != "id" or x[1] not in self.fns[f]: return None
        pa = self.fns[f].index(x[1])
        if self.pkind[f][pa] != "L": return None
        rest = its[1:]
        if any(self.item_info(it)[0] != "scalar" for it in rest): return None
        if any(self.maybe(it) for it in rest): raise AsmError("%s: 累積に足す要素が `__` になりうる形はまだ出せません(並びから消えるので長さが変わる)" % f)
        return pa, len(rest)

    def ring_grow_call(self, f, g, args):
        """f から輪の相手 g への呼びが、f の累積 P を伸ばして g の第 q 引数へ渡す形なら (q, P の番号, 伸び d, 食う f の仮引数, それを渡す g の位置)。
        累積の位置は f と g で違ってよい。他の器の引数は、f の仮引数そのものか末尾の切り出しだけ(うち 1 つ以上が末尾の切り出し=食う器)。"""
        if len(args) != len(self.fns[g]): return None
        acc = [(q, self.grow_src(a, f)) for q, a in enumerate(args) if self.pkind[g][q] == "L"]
        acc = [(q, r) for q, r in acc if r is not None]
        if not acc: return None
        if len({r[0] for _, r in acc}) != len(acc): raise AsmError("%s: 輪(%s への呼び)で同じ累積を 2 か所へ伸ばして渡す形はまだ出せません" % (f, g))
        accq = {q for q, _ in acc}; accp = {r[0] for _, r in acc}
        eat = None
        for q2, a in enumerate(args):
            if q2 in accq or self.pkind[g][q2] not in WIDE: continue
            sa = self.strip(a); tl = self.tail_of(sa) if sa[0] == "bin" else None
            base = self.strip(tl[0]) if tl else sa
            if base[0] != "id" or base[1] not in self.fns[f] or self.fns[f].index(base[1]) in accp or self.pkind[f][self.fns[f].index(base[1])] != self.pkind[g][q2]:
                raise AsmError("%s: 輪(%s への呼び)で累積を伸ばすとき、他の器の引数は f の仮引数か末尾の切り出しだけ出せます" % (f, g))
            if tl and tl[1] >= 1 and eat is None: eat = (self.fns[f].index(base[1]), q2)
        if eat is None and self.counting_hop(f, g, args): eat = (self._cr[0], self._cr[0])
        if eat is None: raise AsmError("%s: 累積を伸ばす輪の呼びで、別の器を毎回 `p ' a~`(a ≥ 1)と食っていません。回る回数が測れないので上界が出せません" % f)
        return [(q, pa, d, eat[0], eat[1]) for q, (pa, d) in acc]

    def counter_eat(self, f, args):
        """自分への呼びが、Int の仮引数 i を `i + c`(c ≥ 1)で進め、枝の条件で `i < ||xs||` と分かり、i は全部の呼びで 0 以上、xs は同じまま渡すなら、
        xs の番号(回る回数は ||xs|| 以下: 呼びのたびに i が 1 以上増え、0 ≤ i < ||xs|| でしか呼べない)。でなければ None。"""
        if getattr(self, "_lbmap", None) is None: self._lbmap = self.build_lbmap()
        fx = None
        for ax in args:
            if isinstance(ax, tuple) and id(ax) in self._argfacts: fx = self._argfacts[id(ax)]; break
        if not fx: return None
        nn = self.nonneg.get(f, set())
        for j, a in enumerate(args):
            if self.pkind[f][j] != "I" or self.fns[f][j] not in nn: continue
            a = self.strip(a)
            if not (a[0] == "bin" and a[1] == "+"): continue
            l, r = self.strip(a[2]), self.strip(a[3])
            if not ((l == ("id", self.fns[f][j]) and (self.const_int(r) or 0) >= 1) or (r == ("id", self.fns[f][j]) and (self.const_int(l) or 0) >= 1)): continue
            key = self.skey(("id", self.fns[f][j]))
            for k, p in enumerate(self.fns[f]):
                if self.pkind[f][k] in WIDE and ("lt", key, p) in fx and self.strip(args[k]) == ("id", p): return k
        return None

    def self_calls(self, f):
        """f の本体にある、f 自身への呼び(全部の引数が付いたもの)の実引数の並び。"""
        out = []
        if not hasattr(self, "_call_node"): self._call_node = {}
        def walk(x):
            if isinstance(x, tuple) and x:
                if x[0] == "seq" and x[1] and isinstance(x[1], list) and x[1][0][0] == "id" and x[1][0][1] == f and len(x[1]) - 1 == len(self.fns[f]): out.append(x[1][1:]); self._call_node[id(x[1][1:][0]) if x[1][1:] and isinstance(x[1][1:][0], tuple) else 0] = x
                for y in (x[1:] if isinstance(x[0], str) else x): walk(y)
            elif isinstance(x, list):
                for y in x: walk(y)
        walk(self.bodies[f]); return out

    def state_bound(self, f, gl):
        """自分への呼びの全部で、(1) 伸ばす累積 gl 以外の器の引数は変わらずに渡され、(2) Int の引数は 0 以上で上限が定数と分かり、
        (3) 枝の条件が累積を見ない(累積の中身で流れが変わらない)なら、止まる限り同じ状態(Int の組)を 2 度通らないので、
        呼びの回数は (Π(上限+1)) + 1 以下。その定数を返す。でなければ None。(多重ループの回数。)"""
        if getattr(self, "_lbmap", None) is None: self._lbmap = self.build_lbmap()
        if not hasattr(self, "_call_node"): self._call_node = {}
        calls = self.self_calls(f)
        if not calls: return None
        nn = self.nonneg.get(f, set()); ps = self.fns[f]; accp = {self.fns[f][j] for j, _ in gl}
        U = {}
        for args in calls:
            node = self._call_node.get(id(args[0]) if args and isinstance(args[0], tuple) else 0)
            if node is None: return None
            fxs = self._argfacts.get(id(args[0])) if isinstance(args[0], tuple) else None
            if fxs is None: return None
            for g_, truth in self._guards.get(id(node), ()):
                for t in self.walk_ids(g_):
                    if t in accp: return None
            for j, a in enumerate(args):
                a = self.strip(a)
                if ps[j] in accp: continue
                if a == ("id", ps[j]): continue
                if self.pkind[f][j] != "I" or ps[j] not in nn: return None
                u = self.ubound(a, nn, fxs)
                if u is None or u < 0: return None
                U[j] = max(U.get(j, 0), u)
        if not U: return None
        k = 1
        for u in U.values(): k *= u + 1
        return k + 1

    def walk_ids(self, x):
        out = set()
        def w(y):
            if isinstance(y, tuple) and y:
                if y[0] == "id": out.add(y[1])
                for z in y[1:]: w(z)
            elif isinstance(y, list):
                for z in y: w(z)
        w(x); return out

    def monotone_arg(self, f, j, sign):
        """f の自分への呼びの全部が、第 j 引数を `p + c`(sign=+1)または `p - c`(sign=-1)(c ≥ 1 の定数)で渡すか。
        そうなら、このカウンタは一方向にしか進まない(途中でやり直す呼びが無い)ので、呼びの回数を値の幅で抑えられる。"""
        me = ("id", self.fns[f][j])
        for args in self.self_calls(f):
            a = self.strip(args[j])
            if not (a[0] == "bin" and a[1] == ("+" if sign > 0 else "-")): return False
            l, r = self.strip(a[2]), self.strip(a[3])
            if sign > 0:
                c = self.const_int(r) if l == me else (self.const_int(l) if r == me else None)
            else:
                c = self.const_int(r) if l == me else None
            if c is None or c < 1: return False
        return True

    def counter_const(self, f, args):
        """自分への呼びが、Int の仮引数 i を `i + c`(c ≥ 1)で進め、i は全部の呼びで 0 以上、この呼びの場では i ≤ U と分かるなら、
        呼びの回数は U // c + 1 以下(定数)。証明できた回数を返す。でなければ None。"""
        if getattr(self, "_lbmap", None) is None: self._lbmap = self.build_lbmap()
        fx = None
        for ax in args:
            if isinstance(ax, tuple) and id(ax) in self._argfacts: fx = self._argfacts[id(ax)]; break
        if not fx: return None
        nn = self.nonneg.get(f, set()); best = None
        for j, a in enumerate(args):
            if self.pkind[f][j] != "I" or self.fns[f][j] not in nn: continue
            a = self.strip(a)
            if not (a[0] == "bin" and a[1] == "+"): continue
            l, r = self.strip(a[2]), self.strip(a[3]); me = ("id", self.fns[f][j])
            c = self.const_int(r) if l == me else (self.const_int(l) if r == me else None)
            u = fx.get(("u", self.fns[f][j]))
            if c is None or c < 1 or u is None or u < 0 or not self.monotone_arg(f, j, 1): continue
            k = u // c + 1
            if best is None or k < best: best = k
        return best

    def counter_down(self, f, args):
        """自分への呼びが、Int の仮引数 n を `n - c`(c ≥ 1)で進め、この呼びの場で n ≥ L と分かる(L は定数)なら、呼びの回数は
        max(n の入口の値, 0) + max(-L, 0) + 1 以下(呼びのたびに n が 1 以上減り、n ≥ L でしか呼べない)。その eat((j, ("k", 定数)))を返す。でなければ None。"""
        if getattr(self, "_lbmap", None) is None: self._lbmap = self.build_lbmap()
        fx = None
        for ax in args:
            if isinstance(ax, tuple) and id(ax) in self._argfacts: fx = self._argfacts[id(ax)]; break
        if not fx: return None
        nn = self.nonneg.get(f, set())
        for j, a in enumerate(args):
            if self.pkind[f][j] != "I": continue
            a = self.strip(a)
            if not (a[0] == "bin" and a[1] == "-" and self.strip(a[2]) == ("id", self.fns[f][j])): continue
            c = self.const_int(a[3])
            L = self.lbound(("id", self.fns[f][j]), nn, fx)
            if c is None or c < 1 or L is None or not self.monotone_arg(f, j, -1): continue
            return (j, ("k", max(-L, 0) + 1))
        return None

    def grow_multi(self, f, args, lonly=False):
        """grow_check の複数累積版。自分への末尾呼びの実引数で、伸ばす累積を全部 ([(位置, 個数)], 食う器) で返す。"""
        gl, eat = [], None
        for j, a in enumerate(args):
            if self.pkind[f][j] not in WIDE or self.same_or_shrunk(a, f, j):
                if self.pkind[f][j] in WIDE:
                    tl = self.tail_of(a)
                    if tl and self.strip(tl[0]) == ("id", self.fns[f][j]) and tl[1] >= 1 and eat is None: eat = j
                continue
            if self.fresh_const(a, f, j) is not None: continue
            dd = self.grow_form(a, f, j)
            if dd is None or (lonly and self.pkind[f][j] != "L"): raise AsmError("%s: 自分への呼びで器の引数を変えています(同じものか、末尾の切り出し `p ' a~`、累積を後ろへ伸ばす `acc~ x` だけ出せます)。返る器の大きさの見積もりが出せません" % f)
            gl.append((j, dd))
        if not gl: return [], None
        if eat is None: eat = self.counter_eat(f, args)
        if eat is None:
            kc = self.counter_const(f, args)
            if kc is not None: eat = (("k", kc),)                       # 回る回数が定数で証明できた(Int カウンタが定数の上限まで)
        if eat is None:
            sb = self.state_bound(f, gl)
            if sb is not None: eat = (("k", sb),)                        # 止まる限り同じ状態を 2 度通らない: 回る回数 ≤ 状態の数(多重ループ)
        if eat is None:
            cd = self.counter_down(f, args)
            if cd is not None: eat = cd                                  # 下向きのカウンタ: 回る回数 ≤ 入口の値 + 定数(証明)
        if eat is None and self.estimate:                                # 回る回数が証明できない: 食える器の長さの総和で見積もる(外れたら書く前に `__`)
            eat = tuple(j for j, k in enumerate(self.pkind[f]) if k in WIDE and j not in {x for x, _ in gl} and (f, j) not in self.inner_pos)
            ints = tuple(j for j, k in enumerate(self.pkind[f]) if k == "I" and j not in {x for x, _ in gl} and self.strip(args[j]) == ("id", self.fns[f][j]))
            if eat:
                self.note_estimate(f, "回る回数を、食える器の長さの総和で見積もった(毎回食っていることは証明できない)")
                if ints:
                    eat = eat + ints; self.note_estimate(f, "変わらずに渡される Int の仮引数の値も回る回数の見積もりに足した")
            else:
                eat = tuple(j for j, k in enumerate(self.pkind[f]) if k == "I" and j not in {x for x, _ in gl} and any(isinstance(ax, tuple) and self.strip(ax) == ("id", self.fns[f][j]) for ax in [args[j]]))
                if eat: self.note_estimate(f, "回る回数を、変わらずに渡される Int の仮引数の値で見積もった(カウンタがそこまで進むことは証明できない)")
                else: eat = None
        if eat is None: raise AsmError("%s: 累積を伸ばす末尾呼び出しで、別の器を毎回 `p ' a~`(a ≥ 1)と食っていません。回る回数が測れないので上界が出せません" % f)
        return gl, eat

    def note_estimate(self, f, why):
        if (f, why) not in self.infos: self.infos.append((f, why))

    def grow_check(self, f, args):
        """f の自分への末尾呼びの実引数を調べる。器の引数が全部「同じか短い」なら None。累積を伸ばし(複数でもよい)、別の器を毎回 1 以上食うなら
        (最初の伸ばす引数, 1 回で伸びる個数, 食う引数, [(他の伸ばす引数, 個数)])。それ以外は断る(回る回数が測れない・二次になる)。"""
        gl, eat = self.grow_multi(f, args)
        if not gl: return None
        return (gl[0][0], gl[0][1], eat, gl[1:])

    def merge_gr(self, f, gr, gj):
        """枝ごとの伸ばし方 gj を gr に合わせる(伸ばす引数の集まりと食う引数は全枝で同じ。個数は最大)。"""
        new = {gj[0]: gj[1]}
        for j, d in gj[3]: new[j] = d
        if gr is None: return (gj[0], gj[1], gj[2], list(gj[3]))
        old = {gr[0]: gr[1]}
        for j, d in gr[3]: old[j] = d
        if set(old) != set(new) or gr[2] != gj[2]: raise AsmError("%s: 伸ばす器・食う器が枝ごとに違う形はまだ出せません" % f)
        mg = {j: max(old[j], new[j]) for j in old}
        ks = sorted(mg)
        return (ks[0], mg[ks[0]], gr[2], [(j, mg[j]) for j in ks[1:]])

    def set_grow(self, f, gr, t):
        """伸ばす累積ごとに、底の枝の係数 × 個数を食う器の係数へ足す(t は {鍵: 係数})。grow に登録する。"""
        eat = gr[2]; base = dict(t); ke = 0
        for j, d in [(gr[0], gr[1])] + list(gr[3]):
            c = base.get(j, 0)
            if c:
                for e_ in (eat if isinstance(eat, tuple) else (eat,)):
                    if isinstance(e_, tuple): ke += c * d * e_[1]
                    else: t[e_] = t.get(e_, 0) + c * d
        self.grow[f] = (gr[0], gr[1], gr[2]); self.grow_extra[f] = [(j, d, eat) for j, d in gr[3]]
        return ke

    def slice_of(self, n):
        """n が `器 ' [a ~ b]`(端が非負の定数・a ≤ b)なら (器, a, b)。範囲の添字なのに出せない形なら理由つきで断る。普通の添字なら None。"""
        while n[0] == "block": n = n[1]
        if n[0] != "bin" or n[1] != "'": return None
        if self.tail_of(n) is not None: return None
        idx = n[3]
        while idx[0] == "block": idx = idx[1]
        if idx[0] == "sec" or (idx[0] == "bin" and idx[1] in ("~", "~+")) :
            if idx[0] != "bin" or idx[1] != "~" or (idx[2][0] == "bin" and idx[2][1] == "~+"):
                raise AsmError("スライスは `[a ~ b]` だけ出せます(刻み付き・端の省略はまだ)")
            a, b = self.const_int(idx[2]), self.const_int(idx[3])
            if a is None or b is None: raise AsmError("スライスの端が定数でない形はまだ出せません(逆順にもなりうるため、複写が要る。実行時の端は未対応)")
            if a < 0 or b < 0: raise AsmError("端が負のスライスはまだ出せません(後ろから数える向きが器の長さで決まる)")
            if a > b: raise AsmError("逆順のスライスはまだ出せません(コピーが要る)")
            return (n[2], a, b)
        return None

    def one_elem(self, a):
        """a が Int の字面か定数名(1 要素のリスト ≅ Int)ならその値、でなければ None。"""
        a = self.strip(a)
        if a[0] == "lit" and isinstance(a[1], int) and not isinstance(a[1], bool): return int_literal(a)
        if a[0] == "id" and isinstance(self.consts.get(a[1]), int): return self.consts[a[1]]
        return None

    def list_values(self, n):
        """n がリストの字面(Int の字面の並び・定数の範囲)なら要素の並び、でなければ None。"""
        while n[0] == "block": n = n[1]
        rv = self.range_values(n)
        if rv is not None: return rv
        if n[0] not in ("seq", "prod") or len(n[1]) < 2: return None            # `[1 , 2]`(積)も `1 2` と同じ Int のリスト
        out = []
        for it in n[1]:
            while it[0] == "block": it = it[1]
            if it[0] == "lit":
                if isinstance(it[1], bool) or not isinstance(it[1], int): return None      # 文字・文字列の字面は数のリストの要素でない
                out.append(int_literal(it))
            elif it[0] == "neg" and it[1][0] == "lit": out.append(-int_literal(it[1]))
            elif it[0] == "id" and isinstance(self.consts.get(it[1]), int): out.append(self.consts[it[1]])
            else: return None
        return out

    def builds(self, n):
        """n が『要素を式で組み立てる』並び(`a * 2 a + 1`)なら要素の項、でなければ None。字面だけの並びは .rodata に置けるので含めない。"""
        while n[0] == "block": n = n[1]
        if n[0] != "seq" or len(n[1]) < 2: return None
        h = n[1][0]
        if h[0] == "id" and h[1] in self.fns: return None
        if self.list_values(n) is not None: return None
        if self.nested_values(n) is not None: return None
        if self.str_value(n) is not None: return None
        out = []
        for it in n[1]:
            if it[0] == "post" and it[1] == "~":
                inner = self.builds(it[2])
                if inner is not None: out += inner; continue      # `(a b)~` は a b をそのまま並べたのと同じ
            out.append(it)
        return out

    @staticmethod
    def item_info(it):
        """並びの要素: 展開 `x~` なら ("spread", x)、そうでなければ ("scalar", it)。"""
        if it[0] == "post" and it[1] == "~": return ("spread", it[2])
        return ("scalar", it)

    def ret_nodes(self, v):
        """値の位置(関数の返値になる項)を順に。"""
        while v[0] == "block": v = v[1]
        if v[0] == "cases":
            for _, x in v[1]: yield from self.ret_nodes(x)
        else: yield v

    def slice_in_range(self, x):
        """スライス x の範囲が、元の器(字面・定数)の中に収まっているか(収まらないと `__`)。仮引数のスライスは収まるとは言えない。"""
        x = self.strip(x)
        sl = self.slice_of(x) if x[0] == "bin" else None
        if sl is None: return True
        inner = self.strip(sl[0])
        vals = self.lists[inner[1]][1] if inner[0] == "id" and inner[1] in self.lists else self.list_values(inner)
        return vals is not None and sl[2] < len(vals)

    allow_unit = False
    mk_const = {}          # 補助関数 → (定数, {仮引数の番号: 係数}, 切り出した関数)。実引数の組み立てを切り出したものの大きさ(切り出した関数の仮引数の長さで)

    def fresh_const(self, a, f, j):
        """f の自分への呼びの第 j 引数 a が、定数の大きさの新しい器(切り出した組み立ての呼び)ならその大きさ、でなければ None。"""
        a = self.strip(a)
        if a[0] == "seq" and a[1][0][0] == "id" and a[1][0][1] in self.mk_const and self.pkind[f][j] in ("L", "S"):
            c, t, lf = self.mk_const[a[1][0][1]]
            if lf != f or any(self.argof(k) == j or not self.nongrow(f, self.argof(k)) for k in t): return None      # 大きさが、回るたびに変わる器の長さ(入れ子なら内側の総和)に頼るなら(伸びる)出せない
            return (c, t)
        hd = self.nest_head(a, f) if a[0] == "bin" else None      # 入れ子の 1 つの内側 `m ' i` をそのまま(見せるだけ。置き場は要らない)
        if hd is not None and self.pkind[f][j] in ("L", "S") and hd[0] != j and self.nongrow(f, hd[0]): return (0, {("m", hd[0]): 1})
        return None

    def is_mk(self, a):
        a = self.strip(a)
        return a[0] == "seq" and a[1][0][0] == "id" and a[1][0][1] in self.mk_const

    def nongrow(self, f, k):
        """f の第 k 仮引数(器)が、自分への呼びのどれでも『同じか短い』か(回っても初めより長くならない)。"""
        ok = True
        def walk(x):
            nonlocal ok
            if isinstance(x, tuple) and x:
                if x[0] == "seq" and x[1] and x[1][0] == ("id", f):
                    a = x[1][1:]
                    if k < len(a) and not self.same_or_shrunk(a[k], f, k): ok = False
                for y in (x[1:] if isinstance(x[0], str) else x): walk(y)
            elif isinstance(x, list):
                for y in x: walk(y)
        walk(self.bodies[f])
        return ok

    def fresh_extra(self, f, body, t):
        """自分への呼びの新しい器(定数の大きさ c_j)が、返す物の大きさに足す分: 係数 t[j] × c_j の和(新しい器を ys として使う底の枝が、元の ys に c_j を足した長さ以下)。"""
        cs = {}
        extra = {}
        def walk(x):
            if isinstance(x, tuple) and x:
                if x[0] == "seq" and x[1] and x[1][0] == ("id", f):
                    for j, a in enumerate(x[1][1:]):
                        c = self.fresh_const(a, f, j) if j < len(self.fns[f]) else None
                        if c is not None:
                            c0, tt = cs.get(j, (0, {}))
                            cs[j] = (max(c0, c[0]), {k: max(tt.get(k, 0), c[1].get(k, 0)) for k in set(tt) | set(c[1])})
                for y in (x[1:] if isinstance(x[0], str) else x): walk(y)
            elif isinstance(x, list):
                for y in x: walk(y)
        walk(body)
        k_add, t_add = 0, {}
        for j, (c, tt) in cs.items():
            k_add += t.get(j, 0) * c
            for k, cc in tt.items(): t_add[k] = t_add.get(k, 0) + t.get(j, 0) * cc
        return k_add, t_add

    def items_ok(self, items):
        """並び items に、`__` にならない要素(スカラー)が 2 個以上あるか。あれば、展開が `__`(何も足さない)になっても、残りは 2 個以上なので結果は常に器。"""
        return sum(1 for it in items if self.item_info(it)[0] == "scalar" and not self.maybe(self.item_info(it)[1])) >= 2

    def spread_size(self, x, f, items):
        """並び items の展開 x の長さの上界(size_of)。x が `__` になりうる形(範囲外のスライス・`__` を返す関数)は、items に `__` にならない要素が
        2 個以上あるときだけ許す。"""
        self.check_spread(x, items)
        self.allow_unit = self.items_ok(items)
        try: return self.size_of(x, f)
        finally: self.allow_unit = False

    def check_spread(self, x, items=None):
        """展開 `x~` の x が `__` になりうるなら断る。`__` の展開は何も足さないので、残りが 1 項だけになると結果の種類が
        実行時に変わる(スカラー 3 か、展開前の並び `~[4, 5]` になる。list_model.md「後置 ~ は値を返す」)。静的な種類では持てない。"""
        while x[0] == "block": x = x[1]
        if items is not None and self.items_ok(items): return
        if x[0] == "bin" and self.tail_of(x) is not None:
            raise AsmError("範囲の外になりうるスライスの展開はまだ出せません(末尾の切り出しは尽きると `__`。`__` の展開は何も足さず、残りが 1 項だけになると結果の種類が実行時に変わるため)")
        sl = self.slice_of(x) if x[0] == "bin" else None
        if sl is None: return
        inner = sl[0]
        while inner[0] == "block": inner = inner[1]
        vals = self.lists[inner[1]][1] if inner[0] == "id" and inner[1] in self.lists else self.list_values(inner)
        if vals is None or sl[2] >= len(vals):
            raise AsmError("範囲の外になりうるスライスの展開はまだ出せません(`__` の展開は何も足さず、残りが 1 項だけになると結果の種類が実行時に変わるため)")

    def int_size(self, x, f):
        """回る回数の見積もりに使う Int の式 x の上界 max(x, 0) ≤ 定数 + Σ 係数 × (Int の仮引数の値 / 器の長さ) を (定数, {鍵: 係数}) で。測れなければ None。"""
        x = self.strip(x)
        if x[0] == "lit" and isinstance(x[1], int) and not isinstance(x[1], bool): return (max(x[1], 0), {})
        if x[0] == "id" and x[1] in self.fns[f]:
            j = self.fns[f].index(x[1]); return (0, {j: 1}) if self.pkind[f][j] == "I" else None
        if x[0] == "norm":
            y = self.strip(x[1])
            if y[0] == "id" and y[1] in self.fns[f]:
                j = self.fns[f].index(y[1]); return (0, {j: 1}) if self.pkind[f][j] in ("L", "S") else None
            return None
        if x[0] == "bin" and x[1] in ("+", "-", "*"):
            a, b = self.int_size(x[2], f), self.int_size(x[3], f)
            if x[1] == "+":
                if a is None or b is None: return None
                t = dict(a[1])
                for k, c in b[1].items(): t[k] = t.get(k, 0) + c
                return (a[0] + b[0], t)
            if x[1] == "-":
                cv = self.const_int(x[3])
                if cv is None or cv < 0 or a is None: return None            # n - c(c ≥ 0)は max(n,0) 以下。引く数が変数のときは測れない
                return a
            ca, cb = self.const_int(x[2]), self.const_int(x[3])
            if cb is not None and cb >= 0 and a is not None: return (a[0] * cb, {k: c * cb for k, c in a[1].items()})
            if ca is not None and ca >= 0 and b is not None: return (b[0] * ca, {k: c * ca for k, c in b[1].items()})
        return None

    def size_of(self, x, f, intok=False):
        """展開・引数に渡す器 x を展開したときの Int の要素数の上界を (定数, {係数の鍵: 係数}) で。見積もれなければ None。
        係数の鍵: 整数 j = f の j 番目の仮引数(リスト・文字列)の長さ ||p||、("m", j) = j 番目の仮引数(入れ子)の内側の長さの総和。
        入れ子を展開すると内側が平らに繋がるので、要素数は内側の長さの総和になる(外側の個数だけでは測れない)。"""
        while x[0] == "block": x = x[1]
        if x[0] == "lit" and isinstance(x[1], int) and not isinstance(x[1], bool): return (max(x[1], 0), {})          # 回る回数を Int で見積もる引数(定数)
        if intok and f is not None:
            r = self.int_size(x, f)
            if r is not None: return r
        if x[0] == "id" and f is not None and x[1] in self.fns[f]:
            j = self.fns[f].index(x[1])
            pk = self.pkind[f][j]
            if pk == "I" and intok: return (0, {j: 1})          # 回る回数を Int の値で見積もる引数: 値(負なら 0)が係数の鍵になる
            return (0, {j: 1}) if pk in ("L", "S") else (0, {("m", j): 1}) if pk == "N" else None
        if x[0] == "id" and x[1] in self.lists: return (len(self.lists[x[1]][1]), {})
        if x[0] == "id" and x[1] in self.strs: return (len(self.strs[x[1]][1]), {})
        if x[0] == "id" and x[1] in self.nests: return (self.nests[x[1]][2], {})
        sv = self.str_value(x)
        if sv is not None: return (len(sv), {})
        lv = self.list_values(x)
        if lv is not None: return (len(lv), {})
        nv = self.nested_values(x)
        if nv is not None: return (sum(len(v) for v in nv), {})
        if x[0] == "bin" and x[1] == "'" and self.tail_of(x) is None and self.slice_of(x) is None and f is not None:
            b = x[2]
            while b[0] == "block": b = b[1]
            if b[0] == "id" and b[1] in self.fns[f] and self.pkind[f][self.fns[f].index(b[1])] == "N":
                return (0, {("m", self.fns[f].index(b[1])): 1})      # 入れ子の 1 つの内側: 内側の長さの総和以下
        tl = self.tail_of(x) if x[0] == "bin" else None
        if tl is not None:                               # 末尾の切り出し: 元の器より短い(定数のときは a 個ぶん引ける)
            bs = self.size_of(tl[0], f)
            if bs is None: return None
            return (bs[0] if bs[1] else max(bs[0] - tl[1], 0), bs[1])
        if x[0] == "seq" and x[1][0][0] == "id" and x[1][0][1] in self.mk_const:
            c, t, lf = self.mk_const[x[1][0][1]]
            if lf == f: return (c, dict(t))
            return (c, {}) if not t else None
        g = self.builder_call(x)
        if g is not None:                                # 器を組み立てて返す関数の結果: その上界(引数の長さで置き換える)
            bg, args = self.bound[g], self.strip(x)[1][1:]
            M, t = bg[0], {}
            for j, c in bg[1].items():
                sz = self.size_of(args[self.argof(j)], f, True)
                if sz is None: return None
                M += c * sz[0]
                for jj, cc in sz[1].items(): t[jj] = t.get(jj, 0) + c * cc
            return (M, t)
        sl = self.slice_of(x) if x[0] == "bin" else None
        if sl is not None:
            env = dict(zip(self.fns[f], self.pkind[f])) if f is not None else {}
            return (sl[2] - sl[1] + 1, {}) if self.kind(sl[0], env) != "N" else None      # 入れ子のスライスの展開は内側の長さが測れない
        its = self.builds(x) if x[0] == "seq" else None
        if its is not None:                              # 組み立てた並び: 要素の数 + 展開の長さ(組み立ててから使う側の見積もり用)
            M, t = 0, {}
            for it in its:
                ty, y = self.item_info(it)
                if ty == "scalar": M += 1; continue
                sz = self.size_of(y, f)
                if sz is None: return None
                M += sz[0]
                for jj, cc in sz[1].items(): t[jj] = t.get(jj, 0) + cc
            return (M, t)
        if x[0] == "cases":                              # 条件式: 全部の枝が `__` にならなければ、枝ごとの上界の最大(定数と各係数を別々に)
            genv = dict(zip(self.fns[f], self.pkind[f])) if f in self.fns else {}
            if self.unit_expr(x, genv, set()) and not self.allow_unit: return None
            return self.max_sizes([self.size_of(v, f) for v in self.ret_nodes(x)])
        if x[0] == "seq" and x[1][0][0] == "id" and x[1][0][1] in self.fns and len(x[1]) - 1 == len(self.fns[x[1][0][1]]):
            g = x[1][0][1]                               # 器を組み立てない関数(受け取った器・字面をそのまま返す)の結果: 返す物の上界を実引数の長さで置き換える
            if self.bound.get(g) is not None or self.retk.get(g) != "L" or g in self.sz_seen or (self.unit_possible(g) and not self.allow_unit): return None
            self.sz_seen.add(g)
            try: rs = self.max_sizes([self.size_of(v, g) for v in self.ret_nodes(self.bodies[g])])
            finally: self.sz_seen.discard(g)
            if rs is None: return None
            M, t = rs[0], {}
            for j, c in rs[1].items():
                sz = self.size_of(x[1][1 + self.argof(j)], f)
                if sz is None: return None
                M += c * sz[0]
                for jj, cc in sz[1].items(): t[jj] = t.get(jj, 0) + c * cc
            return (M, t)
        return None

    sz_seen = set()

    @staticmethod
    def max_sizes(szs):
        """上界の組 (定数, {鍵: 係数}) の最大(定数と各係数を別々に)。1 つでも見積もれなければ None。"""
        if not szs or any(z is None for z in szs): return None
        M, t = 0, {}
        for k, c in szs:
            M = max(M, k)
            for j, cc in c.items(): t[j] = max(t.get(j, 0), cc)
        return (M, t)

    lenient = False

    def cant(self, msg):
        """大きさが見積もれない。上界を解いている途中(呼び先の上界がまだ無い)なら今は 0 と見て、解き終えてからもう一度見て断る。"""
        if not self.lenient: raise AsmError(msg)

    @staticmethod
    def argof(key):
        """係数の鍵が指す実引数の番号。"""
        return key if isinstance(key, int) else key[1]

    def nest_head(self, x, f):
        """x が入れ子の仮引数の 1 つの内側 `p ' i`(i は非負の定数)なら (p の番号, i)、でなければ None。"""
        x = self.strip(x)
        if not (x[0] == "bin" and x[1] == "'") or self.tail_of(x) is not None or f not in self.fns: return None
        b = self.strip(x[2]); i = self.const_int(x[3])
        if b[0] == "id" and b[1] in self.fns[f] and self.pkind[f][self.fns[f].index(b[1])] == "N" and i is not None and i >= 0:
            return (self.fns[f].index(b[1]), i)
        return None

    def eat_call(self, items, f):
        """items の展開のうち、f を食って呼ぶもの(式)。"""
        for it in items:
            ty, x = self.item_info(it)
            if ty == "spread" and self.eat_index(x, f) is not None: return x
        return None

    def has_grow(self, f, body):
        """f の本体に、累積を伸ばす自分への末尾呼びがあるか(あれば、累積は入口の作業領域にあるので、器をそのまま返す枝は置き場へ写す)。"""
        for v in self.ret_nodes(body):
            if v[0] == "seq" and v[1][0] == ("id", f) and self.grow_check(f, v[1][1:]) is not None: return True
        if any(k[0] == f for k in self.hop_acc): return True
        return False

    def hop_edge(self, x, f):
        """x が、f から別の関数 g への『食って渡す』呼びなら (g, a)、でなければ None。相互再帰の輪の辺。
        g の器の仮引数それぞれに渡すのは、(i) f の器の仮引数(そのまま、か末尾の切り出し `p ' a~`。同じ仮引数は 2 回渡さず、種類は同じ)か、
        (ii) 定数の大きさの器(字面・名前。種類は同じ)か、f の器の長さに頼る新しい器(`xs~ 7`。その器を食って作り直したとみなす)か、
        (iii) 入れ子の内側の長さに頼る新しい器(`(m ' 0)~ 9`、`m ' 0`)。f の器で渡さないものがあってもよい(器の数が変わってよい)。
        a = 食った数の和 − (ii) の大きさの和。これが 1 以上なら、辺を通るたびに器の長さの総和の外の分を除いた総和が a 以上減る(輪を回る回数はその総和以下)。
        (iii) が入る位置 (g, q) は『内側頼みの位置』で、総和から除く(長さが入れ子の内側の総和に頼るので総和では測れない)。
        そこへは (iii) か定数の新しい器しか渡せず、そこの器を別の関数へ渡すこともできない(違反は輪の中で断る)。"""
        x = self.strip(x)
        if not (x[0] == "seq" and x[1][0][0] == "id"): return None
        g = x[1][0][1]; args = x[1][1:]
        if g == f or g not in self.fns or len(args) != len(self.fns[g]) or self.retk.get(g) not in ("L", "S") or self.retk.get(g) != self.retk.get(f): return None
        wf = [j for j, k in enumerate(self.pkind[f]) if k in WIDE]
        wg = [j for j, k in enumerate(self.pkind[g]) if k in WIDE]
        if any(self.pkind[f][j] not in ("L", "S", "N") for j in wf) or any(self.pkind[g][j] not in ("L", "S", "N") for j in wg): return None
        if not wf or not wg: return None
        used, net, fresh, inner, passed = set(), 0, [], [], []
        env = dict(zip(self.fns[f], self.pkind[f]))
        accs, eat_ = [], None; passthru = []
        for q in wg:
            ga = None
            sa_ = self.strip(args[q])
            its_ = self.builds(sa_) if sa_[0] == "seq" else None
            if its_ and len(its_) >= 2 and self.retk.get(f) in ("L", "S"):
                fx = self.strip(self.item_info(its_[0])[1])
                if fx[0] == "id" and fx[1] in self.fns[f]:
                    pa_ = self.fns[f].index(fx[1])
                    if self.pkind[f][pa_] == self.pkind[g][q] == self.retk.get(f):
                        if self.pkind[f][pa_] == "L": ga = self.grow_src(args[q], f)
                        else:
                            dd_ = self.grow_form(args[q], f, pa_)
                            ga = (pa_, dd_) if dd_ is not None else None
            if ga is not None:                                    # 累積を伸ばして渡す(位置は違ってよい。作業領域を共有。伸びは辺の個数に足す)
                pa_, d_ = ga
                if pa_ in used or (f, pa_) in self.inner_pos or (g, q) in self.inner_pos: return None
                used.add(pa_); passed.append((q, pa_)); accs.append((q, pa_, d_)); continue
            a = self.strip(args[q])
            tl = self.tail_of(a) if a[0] == "bin" else None
            base = self.strip(tl[0]) if tl else a
            if not tl and base[0] == "id" and base[1] in self.fns[f] and self.pkind[g][q] in ("L", "S") and self.pkind[f][self.fns[f].index(base[1])] == self.pkind[g][q]: passthru.append((q, self.fns[f].index(base[1])))
            if tl and tl[1] >= 1 and base[0] == "id" and base[1] in self.fns[f] and eat_ is None: eat_ = (self.fns[f].index(base[1]), q)
            if base[0] == "id" and base[1] in self.fns[f]:
                pj = self.fns[f].index(base[1])
                if pj not in wf or pj in used or self.pkind[f][pj] != self.pkind[g][q]: return None
                used.add(pj)
                if (f, pj) in self.inner_pos:                        # 内側頼みの位置の器を渡す: 渡された先の位置も内側頼みになる(総和に入らない)
                    self.inner_cand.add((g, q)); self.q_pass.add(((f, pj), (g, q)))
                elif tl: net += tl[1]
                passed.append((q, pj))
                continue
            if tl: return None
            try: sz = self.size_of(a, f); kd = self.kind(a, env)
            except AsmError: return None
            if sz is None or kd != self.pkind[g][q]: return None
            if any(isinstance(k, tuple) for k in sz[1]):             # 入れ子の内側の長さに頼る新しい器(器の長さにも頼ってよい)
                if self.pkind[g][q] not in ("L", "S"): return None
                inner.append((q, sz)); continue
            fresh.append((q, sz))
        # 新しい器の大きさが f の器の長さに頼る(`xs~ 7`)なら、その器を食って(係数 1 で 1 度だけ)作り直したものとみなす: 総和は定数ぶんしか増えない
        refs = set()
        for q, sz in fresh + inner:
            for k, cc in sz[1].items():
                if isinstance(k, tuple): continue
                if k not in wf or k in used or k in refs or cc != 1 or (f, k) in self.inner_pos: return None
                refs.add(k)
        for q, sz in fresh:
            if (g, q) not in self.inner_pos: net -= sz[0]
            elif self.pkind[g][q] != "N": self.inner_size[(f, g, q)] = (sz[0], {})            # 内側頼みの位置へ渡す定数の新しい器(その位置の器の長さの上界に入る)
            if self.pkind[g][q] == "N": self.inner_nconst[(f, g, q)] = sz[0]                 # 定数の入れ子の内側の総和(入れ子の内側の総和の上界に足す)
        for q, sz in inner:
            self.inner_cand.add((g, q)); self.inner_size[(f, g, q)] = (sz[0], dict(sz[1]))
        for q, pj in passed:
            if (g, q) in self.inner_pos and (f, pj) not in self.inner_pos: self.inner_pass.add((f, g, q))      # 総和に入る器が内側頼みの位置へ渡る(その長さは総和以下)
        if net < 1 and self.estimate and not self.counting_hop(f, g, args):       # 食うことも数えることも証明できない辺: 見積もりで 1 食うとみなす(外れたら書く前に `__`)
            pq = [(q_, pj_) for q_, pj_ in passed if self.pkind[f][pj_] in WIDE and pj_ not in {pa_ for _q, pa_, _d in accs}]
            if pq:
                self.note_estimate(f, "輪の相手 %s への呼びが器を食っていることを証明できない(見積もりで通した)" % g)
                net = 1
                if eat_ is None:
                    eq_ = self.eaten_positions()
                    pq = sorted(pq, key=lambda t: 0 if t[0] in eq_ else 1)            # プログラム中のどこかで実際に食われている位置の器を、食う器とみなす
                    eat_ = (pq[0][1], pq[0][0])
        if net < 1 and self.counting_hop(f, g, args):               # 数える辺: 食わなくても、通る回数が ||x|| 以下なので 1 食うとみなす
            net = 1
            if eat_ is None: eat_ = (self._cr[0], self._cr[0])
        if accs:
            if net < 1: return None
            old_ = {q_: (pa_, d_) for q_, pa_, d_ in self.hop_acc.get((f, g), ([], None))[0]}        # 同じ (f, g) への呼びが複数あれば、伸びは最大
            for q_, pa_, d_ in accs: old_[q_] = (pa_, max(d_, old_[q_][1]) if q_ in old_ else d_)
            self.hop_acc[(f, g)] = ([(q_, v[0], v[1]) for q_, v in sorted(old_.items())], eat_)
        if net >= 1 and passthru:
            cur = self.hop_pass.setdefault((f, g), {})
            for q_, pa_ in passthru: cur[q_] = pa_
        return (g, net) if net >= 1 else None

    def hop_target(self, x, f):
        e = self.hop_edge(x, f)
        return e[0] if e else None

    def find_rings(self):
        """hop 辺でたがいに行ける関数の組(2 つ以上)を {関数: 組} で。"""
        edges = {}
        for pas in range(8):         # 内側頼みの位置は、辺を見て初めて分かる。位置の集まりが動かなくなるまで見直す(最後の 1 回は違反の記録を取り直す)
            edges = {}; self.viols = []; self.inner_pass = set(); self.q_pass = set()
            for f, body in self.live_bodies():
                if self.retk.get(f) not in ("L", "S"): continue
                for v in self.ret_nodes(body):
                    its = self.builds(v)
                    want = "spread" if self.retk.get(f) == "L" else "scalar"
                    for x in ([self.item_info(it)[1] for it in its if self.item_info(it)[0] == want] if its is not None else [v]):
                        g = self.hop_target(x, f)
                        if g is not None: edges.setdefault(f, set()).add(g)
            if pas >= 1 and self.inner_pos == self.inner_cand: break
            self.inner_pos = set(self.inner_cand)
        reach = {}
        for f in edges:
            seen, st = set(), list(edges[f])
            while st:
                u = st.pop()
                if u in seen: continue
                seen.add(u); st += list(edges.get(u, ()))
            reach[f] = seen
        rings = {}
        for f in reach:
            grp = frozenset(g for g in reach[f] if f in reach.get(g, ()) ) | {f}
            if len(grp) >= 2 and f in reach[f]: rings[f] = grp
        for (f, g, msg) in self.viols:
            if f in rings and g in rings[f]: raise AsmError("%s: 輪を渡る呼びで、入れ子の内側の長さに頼る新しい器の位置(%s)の使い方が出せません(%s)" % (f, g, msg))
        return rings

    def solve_slots(self):
        """組み立てて返す関数の上界 `konst + Σ coef × ||器||` を、動かなくなるまで繰り返して決める(stack_abi.md §4.7)。
        分岐は枝ごとの最大(定数と各係数を別々に)。呼び先の結果をそのまま返す枝は、呼び先の式の仮引数を実引数の長さで置き換えて引き継ぐ。
        自分への呼びは、器の引数を素通しするとき(T = T)だけ何も足さない。"""
        self.lenient = True
        rings = self.find_rings()
        for rounds in range(200):
            changed = False
            loc = {}
            for f, body in self.live_bodies():
                if self.retk.get(f) == "N":
                    if self.solve_nest_slot(f, body): changed = True
                    continue
                if self.retk.get(f) == "S":
                    if self.solve_str_slot(f, body, rings, loc): changed = True
                    continue
                if self.retk.get(f) != "L": continue
                kmax, tmax = 0, {}
                gr, rec_seen = None, False
                growing = self.has_grow(f, body)
                hm = 0                                          # 輪を 1 辺回る枝が撒く『入れ子の先頭の内側』の数の最大
                hops = []                                       # 輪を 1 辺回る枝: (相手, その枝が足す個数, 辺で減る器の長さの和)(輪の関数だけ)
                for v in self.ret_nodes(body):
                    k, t, rec, hop = 0, {}, None, False
                    heads = []                                  # 入れ子の仮引数の内側 `p ' i` の展開 [(p の番号, i)]
                    hop_x = hop_e = None
                    items = self.builds(v)
                    if items is not None:
                        for it in items:
                            ty, x = self.item_info(it)
                            if ty == "scalar": k += 1; continue
                            hd = self.nest_head(x, f)
                            if hd is not None: heads.append(hd)
                            if f in rings:
                                hg = self.hop_target(x, f)
                                if hg is not None and hg in rings[f]:
                                    if hop: raise AsmError("%s: 1 つの枝で輪の相手を 2 回呼ぶ形はまだ出せません" % f)
                                    hop = True; hop_x = x; hop_e = self.hop_edge(x, f); continue
                                xs_ = self.strip(x)
                                if xs_[0] == "seq" and xs_[1][0][0] == "id" and xs_[1][0][1] in rings[f]:
                                    raise AsmError("%s: 相互再帰の相手 %s を、器を食わずに呼んでいます(回る回数が測れない)" % (f, xs_[1][0][1]))
                            ej = self.eat_index(x, f)
                            if ej is not None:             # 器を食う自己呼びの展開: T(n) = k + T(n-1)。段ごとの定数 k が係数(設計者の selfConsumes)
                                if rec is not None: raise AsmError("%s: 1 つの枝で自分を 2 回食う形はまだ出せません" % f)
                                gj = self.grow_check(f, self.strip(x)[1][1:])
                                if gj is not None:
                                    gr = self.merge_gr(f, gr, gj)
                                rec = ej; rec_seen = True; continue
                            sz = self.spread_size(x, f, items)
                            if sz is None: self.cant("%s: 展開(~)する物の長さが見積もれません(仮引数の器・字面・定数の範囲・定数端のスライスだけ)" % f); continue
                            k += sz[0]
                            for j, c in sz[1].items(): t[j] = t.get(j, 0) + c
                        if rec is not None:
                            once = {}
                            if self.pkind[f][rec] == "N":
                                # 食われる入れ子の先頭の内側 `p ' i`(i < a)の展開は、段ごとに別の内側なので、全段で内側の長さの総和 1 回ぶん
                                a_eat = self.tail_of([a for a in self.strip(self.eat_call(items, f))[1][1:] if self.tail_of(a)][0])[1]
                                for hj, hi in heads:
                                    if hj == rec and 0 <= hi < a_eat:
                                        t[("m", rec)] = t.get(("m", rec), 0) - 1
                                        if t[("m", rec)] == 0: del t[("m", rec)]
                                        once[("m", rec)] = once.get(("m", rec), 0) + 1
                            if t: raise AsmError("%s: 食いながら別の器も撒く枝は、上界が段ごとの二次になりうるのでまだ出せません" % f)
                            k, t = 0, ({rec: k} if k else {})              # 底 + k × ||食われる器||(k は 1 段で足す個数)
                            for kk, cc in once.items(): t[kk] = t.get(kk, 0) + cc
                        if hop:
                            # 食われる入れ子の先頭の内側 `p ' i`(i < a)の展開は、輪を 1 辺回るごとに別の内側なので、全体で内側の長さの総和 1 回ぶん
                            nh_by = {}
                            for hj, hi in heads:
                                if self.pkind[f][hj] != "N": continue
                                for aa in self.strip(hop_x)[1][1:]:
                                    tl_ = self.tail_of(aa) if self.strip(aa)[0] == "bin" else None
                                    if tl_ and self.strip(tl_[0]) == ("id", self.fns[f][hj]) and 0 <= hi < tl_[1]:
                                        t[("m", hj)] = t.get(("m", hj), 0) - 1
                                        if t[("m", hj)] == 0: del t[("m", hj)]
                                        nh_by[(hj, hi)] = nh_by.get((hj, hi), 0) + 1; break
                            nh = max(nh_by.values(), default=0)        # 同じ内側を何回撒くか(違う内側どうしは重ならない)
                            if t: raise AsmError("%s: 輪を回りながら別の器も撒く枝は、上界が二次になりうるのでまだ出せません" % f)
                            hops.append((hop_e[0], k, hop_e[1])); hm = max(hm, nh); continue
                    elif v[0] == "seq" and v[1][0][0] == "id" and v[1][0][1] in self.fns:
                        g = v[1][0][1]; args = v[1][1:]
                        if f in rings and g in rings[f]:
                            he = self.hop_edge(v, f)
                            if he is None: raise AsmError("%s: 相互再帰の相手 %s を、器を食わずに呼んでいます(回る回数が測れない)" % (f, g))
                            hops.append((he[0], 0, he[1])); continue
                        if g == f:
                            gj = self.grow_check(f, args)
                            if gj is not None:
                                gr = self.merge_gr(f, gr, gj)
                            continue
                        bg = self.bound.get(g)
                        if bg is None: continue
                        k += bg[0]
                        for j, c in bg[1].items():
                            sz = self.size_of(args[self.argof(j)], f, True)
                            if sz is None: self.cant("%s: %s に渡す第 %d 引数の長さが見積もれません" % (f, g, self.argof(j) + 1)); continue
                            k += c * sz[0]
                            for jj, cc in sz[1].items(): t[jj] = t.get(jj, 0) + c * cc
                    elif growing and self.kind(v, dict(zip(self.fns[f], self.pkind[f]))) == "L":
                        sz = self.size_of(v, f)          # 累積をそのまま返す枝: 置き場へ写す
                        if sz is None: self.cant("%s: 返す器の長さが見積もれません" % f); continue
                        k = sz[0]; t = dict(sz[1])
                    else: continue
                    kmax = max(kmax, k)
                    for j, c in t.items(): tmax[j] = max(tmax.get(j, 0), c)
                ka, ta = self.fresh_extra(f, body, tmax)
                kmax += ka
                for k, cc in ta.items(): tmax[k] = tmax.get(k, 0) + cc
                if gr:
                    # 伸びる累積引数(設計者の『撒きながら食う』の累積版): 回る回数は食われる器の長さ以下、1 回で d 個伸びる。
                    # 底の枝は累積の器を ||acc|| × c 語使うので、||acc|| → ||acc|| + d × ||食われる器|| と見て、係数を食われる器へ足す
                    kmax += self.set_grow(f, gr, tmax)
                if f in rings:
                    loc[f] = (kmax, tmax, hops, hm); continue
                new = (kmax, tmax) if (kmax or tmax) else None
                if new is not None and new != self.bound.get(f): self.bound[f] = new; changed = True
            done_r = set()
            for f in loc:
                grp = rings[f]
                if grp in done_r or any(g not in loc for g in grp): continue
                done_r.add(grp)
                # 相互再帰の輪: 輪を回る回数は器の長さ n 以下で、1 回に足す個数は最大 K。輪を出る底の枝は最大 (定数 C、器の係数 c)。
                # よって輪のどの関数も 底 C + (K + c) × n。(輪の関数は器の仮引数がただ 1 つなので、鍵はその番号)
                # 輪の関数ごとの上界 α×S + β_f(S は器の長さの総和)。
                # 底の枝(定数 k_b、係数 c_b)は c_b ≤ α かつ k_b ≤ β_f ならよい。辺 f→g(足す個数 k_e、減る長さ a_e)は k_e + α(S − a_e) + β_g ≤ αS + β_f、
                # つまり β_f ≥ k_e − α a_e + β_g。α は、正の輪(Σ(k_e − α a_e) > 0)が無くなる最小の整数(≥ 底の係数の最大)。β は最長経路
                cb, cm, H = 0, 0, 0
                kb, edges, cq = {}, [], {}
                for g in grp:
                    es = [j for j, kd in enumerate(self.pkind[g]) if kd in WIDE]
                    kg, tg, hops_g, hm_ = loc[g]
                    if any((j[1] if isinstance(j, tuple) else j) not in es for j in tg): raise AsmError("%s: 相互再帰の輪の中で、器の仮引数以外の長さに頼る形はまだ出せません" % g)
                    kb[g] = kg; H = max(H, hm_)
                    for j, cc in tg.items():
                        if isinstance(j, tuple): cm = max(cm, cc)
                        elif (g, j) in self.inner_pos: cq[(g, j)] = cc          # 内側頼みの位置の器: 総和 S に入れず、別に足す
                        else: cb = max(cb, cc)
                    for (h, k_e, a_e) in hops_g:
                        if h not in grp: raise AsmError("%s: 輪の外へ食って渡す辺はまだ出せません" % g)
                        edges.append((g, h, k_e, a_e, sum(x_[2] for x_ in self.hop_acc.get((g, h), ([], None))[0])))
                from fractions import Fraction
                edges = [(g_, h_, k_e + cb * dd_, a_e) for (g_, h_, k_e, a_e, dd_) in edges]       # 累積が伸びる分は、底で係数 cb 倍で効く
                def relax(alpha, init):
                    """辺 f→g: β_f ≥ k_e − α a_e + β_g の最長経路。正の輪があれば、その輪の辺の並びを返す。"""
                    dist, pred = dict(init), {}
                    last = None
                    for _ in range(len(grp) + 1):
                        last = None
                        for e in edges:
                            g_, h_, k_e, a_e = e
                            v = k_e - alpha * a_e + dist[h_]
                            if v > dist[g_]: dist[g_] = v; pred[g_] = e; last = g_
                        if last is None: return dist, None
                    x = last
                    for _ in range(len(grp)): x = pred[x][1]
                    cyc, y = [], x
                    while True:
                        e = pred[y]; cyc.append(e); y = e[1]
                        if y == x: break
                    return dist, cyc
                alpha = Fraction(cb)
                while True:
                    beta, cyc = relax(alpha, {g: 0 for g in grp})
                    if cyc is None: break
                    alpha = Fraction(sum(e[2] for e in cyc), sum(e[3] for e in cyc))      # 正の輪の平均(Σk / Σa)。傾きの下限が上がる
                beta, _ = relax(alpha, kb)
                gamma = max(cm, H)          # 入れ子の内側の総和の係数: 食い終えた窓(辺ごとに別の内側)と残りの内側は重ならないので、足さず最大
                # 内側頼みの位置 (h, q): 入口の器(その関数が入口のとき)か、辺で渡る新しい器(定数 c + Σ 係数 × 入れ子の内側の総和)。
                # 内側の総和は、辺ごとに入れ子の仮引数を端から食うだけ(単射)なので、入口の入れ子の仮引数の内側の総和の和以下。
                # 内側頼みの位置の器は、入口の値か、辺で渡る値(定数 / 定数 + 器の長さ + 入れ子の内側の総和 / 総和に入る器そのもの)のどれか。
                # 内側頼みの位置の器の長さ ≤ 入口の内側頼みの器の長さの和 + 定数 + (器の長さの係数) × S + (内側の総和の係数) × 入れ子の内側の総和の和。
                # 位置ごとの係数は、関数ごとに位置を足し合わせて(下)輪の定数・係数にする。
                CQ = max(cq.values(), default=0)
                NC = sum(v for (a_, b_, q_), v in self.inner_nconst.items() if a_ in grp and b_ in grp)
                # 位置 p の底での器の長さ ≤ 入口の値(co で数える)か、p へ渡ってくる位置への新しい器(辺 (a, b, q) の定数・器の長さ・内側の総和)。
                # 底は関数 h の内側頼みの位置ごとに cq × 長さを使うので、h ごとに位置を足し合わせ、その最大を輪の定数・係数にする(位置が 2 つ以上あっても足りる)。
                back = {p: {p} for p in cq}
                for p in cq:
                    grew = True
                    while grew:
                        grew = False
                        for (p_, q_) in self.q_pass:
                            if q_ in back[p] and p_ not in back[p]: back[p].add(p_); grew = True
                # 位置ごとに、渡ってくる新しい器の最大を取り、関数 h ごとに位置を足し合わせる。
                # 同じ辺の器が別々の時刻に作られて別の位置に同時に居ることがあるので、辺の器を 1 つの位置にだけ割り当てる締め方は一般には安全でない。
                # 安全に言えるのは、辺の器から 2 つの位置への「渡る回数」がどの道でも同じ 1 通り(輪に周回が無い)ときだけ: そのとき 2 つの位置の器は同じ時刻の
                # 同じ呼びで作られた同じ器でしかありえず、1 つの位置にしか居られない。
                succ = {}
                for (p_, q_) in self.q_pass:
                    if p_ in cq or q_ in cq or True: succ.setdefault(p_, set()).add(q_)
                def plen(u, p, stack=()):
                    """u から p へ渡る回数の集まり。周回があれば None。"""
                    if u in stack: return None
                    out = {0} if u == p else set()
                    for v in succ.get(u, ()):
                        r = plen(v, p, stack + (u,))
                        if r is None: return None
                        out |= {x + 1 for x in r}
                    return out
                Xc, Xm_, Xl = {}, {}, {}
                per_h = {}
                for p, cqp in cq.items():
                    ent = [(k_, sz) for k_, sz in self.inner_size.items() if k_[0] in grp and k_[1] in grp and (k_[1], k_[2]) in back[p]]
                    pa_ = 1 if any(a_ in grp and b_ in grp and (b_, q_) in back[p] for (a_, b_, q_) in self.inner_pass) else 0
                    per_h.setdefault(p[0], []).append((p, cqp, ent, pa_))
                def excl(k_, p1, p2):
                    l1, l2 = plen((k_[1], k_[2]), p1), plen((k_[1], k_[2]), p2)
                    return l1 is not None and l2 is not None and len(l1) == 1 and l1 == l2
                comp_val = lambda sz, comp: (sz[0] + sum(v for k, v in sz[1].items() if isinstance(k, tuple)) * NC) if comp == 0 else (sum(v for k, v in sz[1].items() if isinstance(k, tuple)) if comp == 2 else sum(v for k, v in sz[1].items() if not isinstance(k, tuple)))
                def assign(plist, comp):
                    best = [0]
                    def rec(i, chosen, acc):
                        if i == len(plist): best[0] = max(best[0], acc); return
                        p, cqp, ent, pa_ = plist[i]
                        floor = cqp * (1 if (comp == 1 and pa_) else 0)
                        rec(i + 1, chosen, acc + floor)
                        for k_, sz in ent:
                            if any(k2 == k_ and excl(k_, p2, p) for k2, p2 in chosen): continue          # 同じ器が同時に 2 つの位置には居ない
                            rec(i + 1, chosen + [(k_, p)], acc + cqp * max(comp_val(sz, comp), 1 if (comp == 1 and pa_) else 0))
                    rec(0, [], 0)
                    return best[0]
                for h, plist in per_h.items():
                    if len(plist) > 5:                                  # 位置が多い輪は数え上げをせず、重なりを許す(安全側)
                        Xc[h] = sum(cqp * max([comp_val(sz, 0) for _, sz in ent], default=0) for p, cqp, ent, pa_ in plist)
                        Xm_[h] = sum(cqp * max([comp_val(sz, 2) for _, sz in ent], default=0) for p, cqp, ent, pa_ in plist)
                        Xl[h] = sum(cqp * max([comp_val(sz, 1) for _, sz in ent] + [1 if pa_ else 0], default=0) for p, cqp, ent, pa_ in plist)
                    else: Xc[h], Xm_[h], Xl[h] = assign(plist, 0), assign(plist, 2), assign(plist, 1)
                X_const, X_m, X_len = max(Xc.values(), default=0), max(Xm_.values(), default=0), max(Xl.values(), default=0)
                norm = lambda q: int(q) if Fraction(q).denominator == 1 else Fraction(q)
                for g in grp:
                    es = [j for j, kd in enumerate(self.pkind[g]) if kd in WIDE]
                    co = {e: norm(alpha + X_len) for e in es if (alpha or X_len) and (g, e) not in self.inner_pos}
                    for e in es:
                        if (g, e) in self.inner_pos and CQ:
                            rch, st_ = {(g, e)}, [(g, e)]                      # この位置の器が渡っていく先(内側頼みの位置どうし)
                            while st_:
                                u_ = st_.pop()
                                for (p_, q_) in self.q_pass:
                                    if p_ == u_ and q_ not in rch: rch.add(q_); st_.append(q_)
                            co[e] = max([cq.get(p_, 0) for p_ in rch], default=0)       # 位置ごとの係数: 渡り先の係数の最大(全位置の最大 CQ より締まる)
                            if not co[e]: del co[e]
                        if self.pkind[g][e] == "N" and (gamma or X_m): co[("m", e)] = gamma + X_m
                    new = (norm(beta[g] + X_const + X_m * NC), co) if (beta[g] or co or X_const) else None
                    if new is not None and new != self.bound.get(g): self.bound[g] = new; changed = True
            if not changed:
                if self.lenient: self.lenient = False; continue          # もう一度、今度は見積もれない所を断る
                for _round in range(8):                                    # 渡すだけの辺は、累積を持つ位置が分かるたびに増える(輪を一周して決まる)ので、変わらなくなるまで繰り返す
                    grew_ = False
                    for (f_, g_), pm in self.hop_pass.items():
                        if f_ not in rings or g_ not in rings[f_]: continue
                        own = {pa_ for (a_, b_), (al_, _e) in self.hop_acc.items() if a_ == f_ for _q, pa_, _d in al_} | {q_ for (a_, b_), (al_, _e) in self.hop_acc.items() if b_ == f_ for q_, _pa, _d in al_}
                        cur_, eat_c = self.hop_acc.get((f_, g_), ([], None))
                        have = {q_ for q_, _pa, _d in cur_}
                        ps_ = [(q_, pa_, 0) for q_, pa_ in sorted(pm.items()) if pa_ in own and q_ not in have]
                        if ps_: self.hop_acc[(f_, g_)] = (sorted(cur_ + ps_), eat_c); grew_ = True
                    if not grew_: break
                for (f_, g_), (accs_, eat2) in self.hop_acc.items():
                    if f_ in rings and g_ in rings[f_]:
                        self.ring_grow[(f_, g_)] = (None, [(q_, pa_, d_, None, None) for q_, pa_, d_ in accs_])
                        cur = self.grow.get(f_)
                        accs_all = {pa_: d_ for q_, pa_, d_ in accs_}
                        for x_ in ([cur] + self.grow_extra.get(f_, [])) if cur else []: accs_all[x_[0]] = max(accs_all.get(x_[0], 0), x_[1])
                        ks_ = sorted(accs_all)
                        eats_all = tuple(i for i, k_ in enumerate(self.pkind[f_]) if k_ in WIDE and i not in accs_all and (f_, i) not in self.inner_pos)
                        if not eats_all: raise AsmError("%s: 累積を伸ばす輪で、食う器がありません(回る回数が測れない)" % f_)
                        self.grow[f_] = (ks_[0], accs_all[ks_[0]], eats_all); self.grow_extra[f_] = [(k_, accs_all[k_], eats_all) for k_ in ks_[1:]]
                for (f_, g_), (_x, rgs_) in self.ring_grow.items():
                    gl_ = ([self.grow[g_]] + self.grow_extra.get(g_, [])) if g_ in self.grow else []
                    if {x[0] for x in gl_} != {r[0] for r in rgs_} or any(x[2] != r[4] for x in gl_ for r in rgs_ if r[4] is not None):
                        raise AsmError("%s: 輪の相手 %s が、渡された累積(第 %s 引数)を伸ばして次へ渡す形ではありません(累積を渡し合う輪は、全員が自分の累積を伸ばして次へ渡す形だけ)" % (f_, g_, "・".join(str(r[0] + 1) for r in rgs_)))
                dm = max([x[1] for fk in {k[0] for k in self.ring_grow} | {k[1] for k in self.ring_grow} for x in ([self.grow[fk]] + self.grow_extra.get(fk, []))] + [self.ring_d], default=0)
                for fk in {k[0] for k in self.ring_grow} | {k[1] for k in self.ring_grow}:
                    self.grow[fk] = (self.grow[fk][0], dm, self.grow[fk][2])
                    self.grow_extra[fk] = [(x[0], dm, x[2]) for x in self.grow_extra.get(fk, [])]
                return
        raise AsmError("返す器の大きさの上界が収束しません(再帰のたびに増える形)")

    def builder_call(self, x):
        """x が、器を組み立てて返す関数の呼びなら関数の名前、でなければ None。"""
        x = self.strip(x)
        if x[0] == "seq" and x[1][0][0] == "id" and x[1][0][1] in self.fns and self.bound.get(x[1][0][1]) is not None: return x[1][0][1]
        return None

    def nest_cost(self, items, f):
        """入れ子の組み立て(並び items)が要る (記述子の数 K, 内容の語数 M, {係数の鍵: 係数})。
        式で作る内側の要素は 1 語ずつ、展開は size_of、器を組み立てて返す関数の結果は、その関数の上界(arena へ写す)。既にある器は内容を使わない。"""
        K, M, t = len(items), 0, {}
        def add(sz, c=1):
            nonlocal M
            M += c * sz[0]
            for j, cc in sz[1].items(): t[j] = t.get(j, 0) + c * cc
        for it in items:
            ty, x = self.item_info(it)
            if ty != "scalar": raise AsmError("入れ子の並びの中の展開(~)はまだ出せません(リストとスカラーが混ざる。平らにするなら `xs~ ys~`)")
            inner = self.builds(x)
            if inner is not None:
                for it2 in inner:
                    t2, x2 = self.item_info(it2)
                    if t2 == "scalar": M += 1; continue
                    sz = self.spread_size(x2, f, inner)
                    if sz is None: self.cant("%s: 展開(~)する物の長さが見積もれません(仮引数の器・字面・定数の範囲・定数端のスライスだけ)" % (f or "最上位")); continue
                    add(sz)
                continue
            g = self.builder_call(x)
            if g is None:
                if self.kind(x, dict(zip(self.fns[f], self.pkind[f])) if f in self.fns else {}) == "I": M += 1      # スカラーの要素: 値のセル 1 語
                continue                                      # 既にある器は写すだけ(内容を使わない)
            bg, args = self.bound[g], self.strip(x)[1][1:]
            M += bg[0]
            for j, c in bg[1].items():
                sz = self.size_of(args[self.argof(j)], f, True)
                if sz is None: self.cant("%s: %s に渡す第 %d 引数の長さが見積もれません" % (f or "最上位", g, self.argof(j) + 1)); continue
                add(sz, c)
        return K, M, t

    def str_definite(self, x):
        """文字列の項 x が `__` にならないと言えるか(仮引数・名前・字面・範囲に収まる定数端のスライス・`__` を返さない関数の結果)。"""
        x = self.strip(x)
        if x[0] == "id": return True
        if self.str_value(x) is not None: return True
        if x[0] == "bin" and x[1] == "'": return self.slice_of(x) is not None and self.slice_in_range(x)
        if x[0] == "seq" and x[1][0][0] == "id" and x[1][0][1] in self.fns: return not self.unit_possible(x[1][0][1])
        return False

    def str_cost(self, items, f, rings=None):
        """文字列の連結(並び items)の長さの上界 (定数, {係数の鍵: 係数})。文字は 1、文字列は size_of、器を組み立てて返す関数の結果はその上界。
        1 つは `__` にならない文字列が要る(全部が消えうると、結果が文字や `__` に変わる)。"""
        env = dict(zip(self.fns[f], self.pkind[f])) if f in self.fns else {}
        M, t, definite, rec, hop, ndef_c = 0, {}, False, None, False, 0
        def add(sz, c=1):
            nonlocal M
            M += c * sz[0]
            for j, cc in sz[1].items(): t[j] = t.get(j, 0) + c * cc
        for it in items:
            ty, x = self.item_info(it)
            if ty != "scalar": raise AsmError("文字列の連結の中の展開(~)はまだ出せません")
            kx = self.kind(x, env)
            if rings and f in rings and kx == "S":
                hg = self.hop_target(x, f)
                xs_ = self.strip(x)
                if hg is not None and hg in rings[f]:
                    if hop: raise AsmError("%s: 1 つの枝で輪の相手を 2 回呼ぶ形はまだ出せません" % f)
                    if self.str_definite(x): definite = True
                    hop = True; self.last_hop_e = self.hop_edge(x, f); continue
                if xs_[0] == "seq" and xs_[1][0][0] == "id" and xs_[1][0][1] in rings[f]:
                    raise AsmError("%s: 相互再帰の相手 %s を、器を食わずに呼んでいます(回る回数が測れない)" % (f, xs_[1][0][1]))
            ej = self.eat_index(x, f) if kx == "S" and f in self.fns else None
            if ej is not None:                               # 器を食う自己呼び: T(n) = k + T(n-1)
                if rec is not None: raise AsmError("%s: 1 つの枝で自分を 2 回食う形はまだ出せません" % f)
                if self.str_definite(x): definite = True
                gj = self.grow_check(f, self.strip(x)[1][1:])
                if gj is not None: self.last_gr = gj
                rec = ej; self.last_rec = True; continue
            if kx == "C":
                M += 1
                if not self.maybe(x): ndef_c += 1
                continue
            if kx == "I": M += 20; continue                   # 数の十進の綴り: 符号 + 19 桁まで
            if kx != "S": raise AsmError("文字列の連結で並べられるのは、文字列・文字・数だけです")
            if self.str_definite(x): definite = True
            g = self.builder_call(x)
            if g is not None:
                bg, args = self.bound[g], self.strip(x)[1][1:]
                M += bg[0]
                for j, c in bg[1].items():
                    sz = self.size_of(args[self.argof(j)], f if f in self.fns else None, True)
                    if sz is None: self.cant("%s に渡す第 %d 引数の長さが見積もれません" % (g, self.argof(j) + 1)); continue
                    add(sz, c)
                continue
            sz = self.size_of(x, f if f in self.fns else None)
            if sz is None: self.cant("連結する文字列の長さが見積もれません(仮引数・字面・名前・定数端のスライス・組み立てる関数の結果だけ)"); continue
            add(sz)
        if not definite and ndef_c < 2: raise AsmError("文字列の連結に、`__` にならない文字列も、`__` にならない文字 2 個以上もありません(全部が消えうると、結果が文字や `__` に変わる)")
        if rec is not None:
            if t: raise AsmError("%s: 食いながら別の器も撒く枝は、上界が段ごとの二次になりうるのでまだ出せません" % f)
            M, t = 0, ({rec: M} if M else {})
        if hop:
            if t: raise AsmError("%s: 輪を回りながら別の器も撒く枝は、上界が二次になりうるのでまだ出せません" % f)
            self.last_hop = True
        return M, t

    def solve_str_slot(self, f, body, rings=None, loc=None):
        """文字列を組み立てて返す関数の置き場(長さの上界 konst + Σ coef×||器||)。L の solve_slots と同じ考え方。"""
        Mmax, Mt, hops = 0, {}, []
        rings = rings or {}
        gr, rec_seen = None, False
        growing = self.has_grow(f, body)
        for v in self.ret_nodes(body):
            items = self.builds(v)
            self.last_hop = False; self.last_rec = False; self.last_gr = None
            if items is not None:
                M, t = self.str_cost(items, f, rings)
                if self.last_rec: rec_seen = True
                gj = self.last_gr
                if gj is not None:
                    gr = self.merge_gr(f, gr, gj)
                if self.last_hop:
                    hops.append((self.last_hop_e[0], M, self.last_hop_e[1])); continue
            elif v[0] == "seq" and v[1][0][0] == "id" and v[1][0][1] in self.fns:
                g = v[1][0][1]; args = v[1][1:]
                if f in rings and g in rings[f]:
                    he = self.hop_edge(v, f)
                    if he is None: raise AsmError("%s: 相互再帰の相手 %s を、器を食わずに呼んでいます(回る回数が測れない)" % (f, g))
                    hops.append((he[0], 0, he[1])); continue
                if g == f:
                    gj = self.grow_check(f, args)
                    if gj is not None:
                        gr = self.merge_gr(f, gr, gj)
                    continue
                bg = self.bound.get(g)
                if bg is None: continue
                M, t = bg[0], {}
                for j, c in bg[1].items():
                    sz = self.size_of(args[self.argof(j)], f, True)
                    if sz is None: self.cant("%s: %s に渡す第 %d 引数の長さが見積もれません" % (f, g, self.argof(j) + 1)); continue
                    M += c * sz[0]
                    for jj, cc in sz[1].items(): t[jj] = t.get(jj, 0) + c * cc
            elif growing and self.kind(v, dict(zip(self.fns[f], self.pkind[f]))) == "S":
                sz = self.size_of(v, f)
                if sz is None: self.cant("%s: 返す文字列の長さが見積もれません" % f); continue
                M, t = sz[0], dict(sz[1])
            else: continue
            Mmax = max(Mmax, M)
            for j, c in t.items(): Mt[j] = max(Mt.get(j, 0), c)
        ka, ta = self.fresh_extra(f, body, Mt)
        Mmax += ka
        for k, cc in ta.items(): Mt[k] = Mt.get(k, 0) + cc
        if gr:
            Mmax += self.set_grow(f, gr, Mt)
        if f in rings:
            loc[f] = (Mmax, Mt, hops, 0); return False
        new = (Mmax, Mt) if (Mmax or Mt) else None
        if new is not None and new != self.bound.get(f): self.bound[f] = new; return True
        return False

    def solve_nest_slot(self, f, body):
        """入れ子の器を返す関数 f の置き場を決める: 記述子 K 個(16 バイト)+ arena の頭(16 バイト)+ 内容 M 語(8 バイト)。
        分岐ごとに (K, M) を出し、K と M を別々に最大にする(K の最大の枝と M の最大の枝が別でも、どちらにも足りる置き場にするため)。
        置き場の語数 = 2 K + 2 + M(= bound[f])。K は boundk[f]。呼び先の結果をそのまま返す枝は、呼び先の K と M を引き継ぐ。変わったら True。"""
        Kmax, Mmax, Mt = 0, 0, {}
        grows, gr, gx, ring_edges = [], None, [], []
        for v in self.ret_nodes(body):
            items = self.builds(v)
            if items is not None: K, M, t = self.nest_cost(items, f)
            elif v[0] == "seq" and v[1][0][0] == "id" and v[1][0][1] in self.fns:
                K, M, t = 0, 0, {}
                g = v[1][0][1]; args = v[1][1:]
                if g == f:
                    for j, a in enumerate(args):
                        if self.pkind[f][j] in WIDE and not self.same_or_shrunk(a, f, j):
                            if self.pkind[f][j] == "L" and self.grow_form(a, f, j) is not None:
                                if not grows or grows[-1][0] is not args: grows.append((args, j))
                                continue
                            if self.fresh_const(a, f, j) is not None: continue
                            raise AsmError("%s: 自分への呼びで器の引数を変えています(同じものか、末尾の切り出し `p ' a~`、定数か変わらない器の長さに頼る新しい器だけ出せます)。返る器の大きさの見積もりが出せません" % f)
                    continue
                rg = self.ring_grow_call(f, g, args) if g in self.fns else None
                if rg:
                    ring_edges.append((g, rg))
                    bg, bk = self.bound0.get(g), self.boundk.get(g)
                    if bg is None or bk is None: continue
                    K = bk[0]; M = bg[0] - 2 * bk[0] - 2
                    for j, c in bg[1].items():
                        a_ = ("id", self.fns[f][{r[0]: r[1] for r in rg}[j]]) if j in {r[0] for r in rg} else args[self.argof(j)]       # 伸びる累積は伸ばす前の器で見積もる(伸びは入口でまとめて足す)
                        sz = self.size_of(a_, f)
                        if sz is None: self.cant("%s: %s に渡す第 %d 引数の長さが見積もれません" % (f, g, self.argof(j) + 1)); continue
                        M += c * sz[0]
                        for jj, cc in sz[1].items(): t[jj] = t.get(jj, 0) + c * cc
                    Kmax, Mmax = max(Kmax, K), max(Mmax, M)
                    for j, c in t.items(): Mt[j] = max(Mt.get(j, 0), c)
                    continue
                bg, bk = self.bound.get(g), self.boundk.get(g)
                if bg is None or bk is None: continue
                K = bk[0]; M = bg[0] - 2 * bk[0] - 2
                for j, c in bg[1].items():
                    sz = self.size_of(args[self.argof(j)], f, True)
                    if sz is None: self.cant("%s: %s に渡す第 %d 引数の長さが見積もれません" % (f, g, self.argof(j) + 1)); continue
                    M += c * sz[0]
                    for jj, cc in sz[1].items(): t[jj] = t.get(jj, 0) + c * cc
            else: continue
            Kmax, Mmax = max(Kmax, K), max(Mmax, M)
            for j, c in t.items(): Mt[j] = max(Mt.get(j, 0), c)
        if not Kmax: return False
        Mt0, Mmax0 = dict(Mt), Mmax
        Mtb = dict(Mt); accd = {}
        for g_, rgs in ring_edges:                             # 輪を回って伸びる累積(輪の相手も同じ作業領域を使う)
            for q_, pa_, d, pe_, qe_ in rgs:
                d = max(d, self.ring_d)
                Mt[pe_] = Mt.get(pe_, 0) + d * Mtb.get(pa_, 0)
                if d > self.ring_d: self.ring_d = d; self.ring_changed = True
            gl = {pa_: (max(d_, self.ring_d), pe_) for q_, pa_, d_, pe_, qe_ in rgs}
            if accd and {k: v[1] for k, v in accd.items()} != {k: v[1] for k, v in gl.items()}: raise AsmError("%s: 伸ばす器・食う器が枝ごとに違う形はまだ出せません" % f)
            for k, v in gl.items(): accd[k] = (max(v[0], accd[k][0]) if k in accd else v[0], v[1])
            self.ring_grow[(f, g_)] = (None, rgs)
        for args, j in grows:                                # 伸びる累積: 底での長さは 入口 + 1 回の伸び × 食う器の長さ(累積ごとに足す)
            gl, eat = self.grow_multi(f, args, True)
            if accd and {k: v[1] for k, v in accd.items()} != {k: eat for k, _ in gl}: raise AsmError("%s: 伸ばす器・食う器が枝ごとに違う形はまだ出せません" % f)
            for k, d in gl:
                if k not in accd:
                    for e_ in (eat if isinstance(eat, tuple) else (eat,)):
                        if isinstance(e_, tuple): Mmax += d * Mtb.get(k, 0) * e_[1]
                        else: Mt[e_] = Mt.get(e_, 0) + d * Mtb.get(k, 0)
                accd[k] = (max(d, accd[k][0]) if k in accd else d, eat)
        if accd:
            for v in self.ret_nodes(body):
                for it in (self.builds(v) or ()):
                    ty, x = self.item_info(it)
                    if ty == "scalar" and any(self.strip(x) == ("id", self.fns[f][k]) for k in accd):
                        raise AsmError("%s: 伸ばす累積をそのまま内側の要素として返す形は出せません(累積は入口の作業領域にあり、関数を抜けると消える。`acc~ x` のように中身を写す形にしてください)" % f)
            ks = sorted(accd)
            self.grow[f] = (ks[0], accd[ks[0]][0], accd[ks[0]][1])
            self.grow_extra[f] = [(k, accd[k][0], accd[k][1]) for k in ks[1:]]
        ka, ta = self.fresh_extra(f, body, Mt)           # 自分への呼びの新しい器を、底の枝が内容として写す分
        Mmax += ka
        for k, cc in ta.items(): Mt[k] = Mt.get(k, 0) + cc
        newb, newk = (2 * Kmax + 2 + Mmax, Mt), (Kmax, {})
        ka0, ta0 = self.fresh_extra(f, body, Mt0)
        Mt0 = dict(Mt0)
        for k, cc in ta0.items(): Mt0[k] = Mt0.get(k, 0) + cc
        nb0 = (2 * Kmax + 2 + Mmax0 + ka0, Mt0)
        ch = self.ring_changed; self.ring_changed = False
        if nb0 != self.bound0.get(f): self.bound0[f] = nb0; ch = True
        if newb != self.bound.get(f) or newk != self.boundk.get(f):
            self.bound[f], self.boundk[f] = newb, newk
            ch = True
        return ch

    def unit_possible(self, g, seen=None):
        """関数 g の返値が `__` になりうるか(行の並びに既定の行が無い・`__` を返す・範囲外になりうる取り出し)。組み立てて返す関数は、
        置き場が足りない時の `__` を勘定に入れない(呼ぶ側が上界で取るので起きない)。"""
        seen = seen or set()
        if g in seen: return False
        seen.add(g)
        genv = dict(zip(self.fns[g], self.pkind[g])) if g in self.fns and g in self.pkind else {}
        return self.unit_expr(self.bodies[g], genv, seen)

    def unit_expr(self, body, genv, seen):
        """式 body が `__` になりうるか(unit_possible の本体。genv = 仮引数の種類)。"""
        def walk(v):
            v = self.strip(v)
            if v[0] == "cases":
                if not v[1] or v[1][-1][0] is not None: return True
                return any(walk(x) for _, x in v[1])
            if v == ("id", "__"): return True
            if v[0] == "bin" and v[1] == "'": return not (self.slice_of(v) is not None and self.slice_in_range(v)) and not self.idx_ok(v)
            if v[0] == "seq" and v[1][0][0] == "id" and v[1][0][1] in self.fns:
                h = v[1][0][1]
                return self.unit_possible(h, seen) or any(self.maybe(a) for a in v[1][1:] if self.kind(a, genv) == "I")
            return False
        return walk(body)

    def solid_seq(self, l, env, lenient=False):
        """`(x c 4)` のように、要素が全部「`__` にならない Int の単純な項」(仮引数・定数の名前・字面・負の字面・定数どうしの算術)の並びなら、その要素の並び。
        入れ子の並びも、中身が全部そうなら、それ自体が `__` にならない 1 要素として許す。`__` の要素は並びから消えるので、`__` になりうる要素
        (比べ・`__` の定数・Int でない仮引数)があるときは None。"""
        while l[0] == "block": l = l[1]
        if l[0] != "seq" or len(l) != 2 or len(l[1]) < 2: return None
        if l[1][0][0] == "id" and l[1][0][1] in self.fns: return None
        for e in l[1]:
            while e[0] == "block": e = e[1]
            if e[0] == "seq":
                if self.solid_seq(e, env, lenient) is None: return None
                continue
            if self.const_int(e) is not None: continue            # 定数の Int(`(0 - 2)` なども)は `__` にならない
            if e[0] == "neg": e = e[1]
            if e[0] == "lit":
                if not (isinstance(e[1], int) and not isinstance(e[1], bool)): return None
            elif e[0] == "id":
                if e[1] in self.consts and not isinstance(self.consts[e[1]], int): return None
                if e[1] not in self.consts and e[1] not in env: return None
            else: return None
            kd = self.kind(e, env)
            if (kd != "I" and not (lenient and kd == "?")) or self.maybe(e): return None          # lenient: 種類を決めている途中の仮引数("?")は、Int とみなして先へ進める
        return l[1]

    def static_list(self, l, env, lenient=False):
        """`__` にならない要素だけの並びの字面(入れ子も可)、またはそれの定数の添字で選んだ入れ子の並び、なら、その並びの節。違えば None。"""
        while l[0] == "block": l = l[1]
        if l[0] == "seq": return l if self.solid_seq(l, env, lenient) is not None else None
        if l[0] == "bin" and l[1] == "'":
            k = self.const_int(l[3]); base = self.static_list(l[2], env, lenient)
            if k is None or base is None: return None
            it = base[1]
            if not -len(it) <= k < len(it): return None
            e = it[k]
            while e[0] == "block": e = e[1]
            return e if e[0] == "seq" and self.solid_seq(e, env, lenient) is not None else None
        return None

    def kind(self, n, env):
        """式の種類: "I" = Int(か `__`)、"L" = Int のリスト。env は仮引数の種類。"""
        k = n[0]
        if k == "block": return self.kind(n[1], env)
        if k == "dyn": return self.kind(n[2], env)
        if k == "id":
            if n[1] in env: return env[n[1]]            # "?" = まだ分からない仮引数
            return "L" if n[1] in self.lists else "S" if n[1] in self.strs else "N" if n[1] in self.nests else "C" if n[1] in self.chars else "I"
        if k == "lit":
            if isinstance(n[1], Char) and len(n) == 2: return "C"
            return "S" if self.str_value(n) is not None else "I"
        if k == "bin" and n[1] == "'":
            tl = self.tail_of(n)
            if tl is not None:
                ik = self.kind(tl[0], env)
                if ik not in ("L", "S", "N", "?"): raise AsmError("末尾の切り出しができるのはリストと文字列だけです")
                return ik
            sl = self.slice_of(n)
            if sl is not None:
                ik = self.kind(sl[0], env)
                if ik not in ("L", "S", "N", "?"): raise AsmError("スライスできるのはリストと文字列だけです")
                return ik
            sl_ = self.static_list(n[2], env, True); kk_ = self.const_int(n[3])
            if sl_ is not None and kk_ is not None:                  # 入れ子の字面の定数の添字: 選んだのが Int の要素(か範囲の外 = `__`)なら Int
                it_ = sl_[1]
                if not -len(it_) <= kk_ < len(it_): return "I"
                e_ = it_[kk_]
                while e_[0] == "block": e_ = e_[1]
                if e_[0] != "seq": return "I"
                return self.kind(e_, env)                             # 選んだのが入れ子の並び: その並びの種類
            lk = self.kind(n[2], env)
            if lk == "N":
                if self.nest_ik == "X": raise AsmError("文字列とリストが混ざる入れ子の要素の取り出しはまだ出せません(要素が文字列かリストかで、その先の種類が変わる)")
                if self.ndepth(n[2], env) > 1: return "N"      # 3 段以上の入れ子の途中の段: まだ入れ子
                return "S" if self.nest_ik == "S" else "L"
            return "C" if lk == "S" else "?" if lk == "?" else "I"
        if k == "bin" and n[1] == "~":
            if self.range_values(n) is not None: return "L"
            lo, step, hi = self.rule_parts(n)
            for x in (lo, step, hi):
                if x is not None and self.kind(x, env) not in ("I", "?"): raise AsmError("規則の端点・歩幅は Int だけです")
            return "R"
        if k == "bin" and n[1] == "*" and self.str_value(n) is not None: return "S"      # Char * 定数 Int
        if k == "bin" and n[1] == "*" and self.kind(n[2], env) == "C": raise AsmError("`Char * Int` は回数が定数のときだけ出せます(長さが実行時に決まる文字列は、確保する領域がまだ無い)")
        if k == "bin" and n[1] == "+" and self.kind(n[2], env) == "C" and self.kind(n[3], env) == "C": return "C"      # Char + Char は文字コードの和(範囲の外は __)
        if k == "bin" and n[1] in ("+", "-") and self.kind(n[2], env) == "C" and self.kind(n[3], env) in ("I", "?"): return "C"      # Char ± Int は Char(`0u30 + n`。範囲の外は __)
        if k == "bin" and n[1] == "~+":
            raise AsmError("終端の無い規則(`[a ~+ s]`)はまだ出せません(数えられず、引くだけ。設計者の 2 本渡し)")
        if k == "cmp" or (k == "bin" and n[1] in ("==", "!==")):
            first = n[1][0] if k == "cmp" else n[2]
            return "C" if self.kind(first, env) == "C" else "I"
        if k == "prod":
            if self.list_values(n) is not None: return "L"
            if self.nested_values(n) is not None:
                self.nest_mark_lit(n)
                return "N"
            raise AsmError("`[a , b]`(積)で出せるのは、Int の字面・リストの字面・文字列の字面を並べた形だけです")
        if k == "seq":
            if n[1][0][0] == "id" and n[1][0][1] in self.fns: return self.retk.get(n[1][0][1], "?")
            if self.str_value(n) is not None: return "S"
            if self.list_values(n) is not None: return "L"
            if self.nested_values(n) is not None:
                self.nest_mark_lit(n)
                return "N"
            items = self.builds(n)
            if items is not None:
                sk, pk_ = [], []
                for it in items:
                    t, x = self.item_info(it)
                    (sk if t == "scalar" else pk_).append(self.kind(x, env))
                if "S" in sk or "C" in sk:
                    # 文字列・文字の並置は連結した文字列(余積)。数との並置(`` `a` 0 ``)は数の文字列化が要るので出さない
                    if "S" in sk and all(x in ("S", "C", "I", "?") for x in sk) and not pk_: return "S"
                    if "S" not in sk and "?" in sk and not pk_ and all(x in ("C", "I", "?") for x in sk): return "?"      # 相手の種類がまだ分からない(相互再帰)
                    if "S" not in sk and not pk_ and len(sk) >= 2 and all(x == "C" for x in sk): return "S"      # 文字だけの並置も連結した文字列(`__` にならない文字が 2 個以上は str_cost が確かめる)
                    raise AsmError("文字列の連結 `a b` で出せるのは、文字列・文字・数を並べた形で、文字列が少なくとも 1 つあるものです(リスト・入れ子との並置、文字だけの並置、展開はまだ)")
                if "N" in sk: raise AsmError("入れ子の入れ子(3 段)はまだ出せません")
                if "L" in sk:
                    # 要素がリストの並び = 入れ子のリスト(`xs ys` は入れ子。operator_table.md の unshift)。スカラーや展開との混在は、
                    # 種類が揃わない(異種の並び)ので出せない
                    if any(x not in ("L", "I", "?") for x in sk) or pk_ or ("?" in sk and "I" in sk):
                        raise AsmError("並びの要素の種類が揃っていません(リストとそれ以外が混ざっています。入れ子のリストはリストと Int だけの並び。平らにするなら `xs~ ys~`)")
                    if "I" in sk: self.mixed_nest = True; self.scalar_nest = True      # スカラーとリストの混在(記述子の bit0 の印)
                    self.nest_mark("L")
                    return "N"
                if any(x not in ("I", "?") for x in sk) or any(x not in ("L", "N", "?") for x in pk_): return "I"
                if sk and not pk_ and "?" in sk: return "?"     # 仮引数の種類がまだ決まらない(Int の並びか、リストの並びか、文字列と数の並置か)
                return "L"
            return "I"
        if k == "cases":
            ks, lits = set(), False
            for _, v in n[1]:
                vv = v
                while vv[0] == "block": vv = vv[1]
                if vv == ("id", "__"): continue                 # `__` はどの種類にもなれる
                kv = self.kind(v, env)
                if kv == "L" and vv[0] == "bin" and vv[1] == "~" and self.range_values(vv) is not None: lits = True   # 端が定数の範囲は、他の枝が規則なら規則になれる
                ks.add(kv)
            if lits and "R" in ks and not any(self.kind(v, env) == "L" and not (self.strip(v)[0] == "bin" and self.strip(v)[1] == "~") for _, v in n[1]): ks.discard("L")
            if "?" in ks and len(ks) > 1: ks.discard("?")
            if len(ks) > 1: raise AsmError("枝の値の種類が揃っていません(Int・リスト・文字列・文字の混在)")
            return ks.pop() if ks else "I"
        return "I"

    def solve_kinds(self):
        """仮引数の種類を、呼び出しに渡される実引数の種類から決める(観測に代わる。compiler_pipeline.md §6.5)。動かなくなるまで繰り返す。"""
        pk = {f: [None] * len(ps) for f, ps in self.fns.items()}
        nonone = set()           # Int の字面でない Int が渡されている仮引数(これはリストに直せない)
        def walk(x, env, cb):
            if isinstance(x, tuple) and x and isinstance(x[0], str):
                cb(x, env)
                for y in (x[1:] if isinstance(x[0], str) else x): walk(y, env, cb)
            elif isinstance(x, (list, tuple)):
                for y in x: walk(y, env, cb)
        for final in (False, True):
            # 端が定数の範囲(.rodata のリストにも規則にもなれる)は、1 回目では仮引数の種類を決めない。他の呼びが規則を渡していれば規則、
            # どこからも決まらなければ 2 回目でリストにする。
            changed = True
            while changed:
                changed = False
                def cb(x, env):
                    nonlocal changed
                    if x[0] == "seq" and x[1][0][0] == "id" and x[1][0][1] in self.fns:
                        f = x[1][0][1]
                        for i, a in enumerate(x[1][1:]):
                            if i >= len(pk[f]): break
                            kd = self.kind(a, env)
                            if kd == "?": continue
                            lit_rng = kd == "L" and self.range_values(self.strip(a)) is not None
                            if lit_rng and pk[f][i] == "R": continue
                            if lit_rng and pk[f][i] is None and not final: continue
                            one = self.one_elem(a)               # `[0]` は要素 1 個のリスト ≅ Int。リストを受ける仮引数には 1 要素のリストとして渡せる
                            if pk[f][i] == "L" and kd == "I" and one is not None: continue
                            if kd == "I" and one is None: nonone.add((f, i))
                            if pk[f][i] == "I" and kd == "L" and (f, i) not in nonone: pk[f][i] = "L"; changed = True; continue      # Int の字面だけが先に来ていた
                            if pk[f][i] is None: pk[f][i] = kd; changed = True
                            elif pk[f][i] != kd:
                                raise AsmError("%s の第 %d 引数に、種類の違う物(Int・リスト・文字列・規則)が渡されています(1 つの仮引数に複数の種類は、型ごとの実体がまだ作れないので出せません。compiler_pipeline.md §6.5)" % (f, i + 1))
                for f, body in self.live_bodies():
                    env = {p: (k or "?") for p, k in zip(self.fns[f], pk[f])}
                    walk(body, env, cb)
                for n in self.nodes:
                    if n[0] != "def": walk(n, {}, cb)
                for f, body in self.live_bodies():
                    env = {p: (k or "?") for p, k in zip(self.fns[f], pk[f])}
                    rk = self.kind(body, env)
                    if rk != "?" and self.retk.get(f) != rk: self.retk[f] = rk; changed = True
        for f in self.fns: self.retk.setdefault(f, "I")
        self.pkind = {f: [k or "I" for k in ks] for f, ks in pk.items()}
        self.rule_names = {p for f, ks in self.pkind.items() for p, k in zip(self.fns[f], ks) if k == "R"}      # 規則は 0 個になりうる(`p ' 0` が `__`)
        for f, ks in self.pkind.items():
            if sum(WIDTH[k] for k in ks) > 64:
                raise AsmError("%s: 引数が多すぎます(スタック渡しを含め 64 語まで)" % f)
            env = dict(zip(self.fns[f], ks))

    def label(self):
        self.nlabel += 1
        return ".L%d" % self.nlabel

    def par_elig(self):                                # --par: 並列にできる純粋な整数関数 {名前: 仮引数の数}(最初に聞かれた時に求める)
        if not hasattr(self, "_par_elig"):
            import sign_asmpar
            self._par_elig = sign_asmpar.eligible(self)
        return self._par_elig

    def spec_elig(self):                               # --par-spec: 投機に出せる(必ず終わると言える)関数 {名前: 再帰の測り}
        if not hasattr(self, "_spec_elig"):
            import sign_asmpar
            self._spec_elig = sign_asmpar.terminating(self, self.par_elig()) if SPEC[0] else {}
        return self._spec_elig

    def maybe(self, n):
        """n の値は `__` になりうるか(静的な見積もり。外れる側に倒さない)。
        関数の本体が走るのは実引数が全部 `__` でないときだけ(処理系と同じ)なので、仮引数は `__` にならない。"""
        k = n[0]
        if k == "block": return self.maybe(n[1])
        if k == "dyn": return self.maybe(n[2])
        if k == "lit": return False
        if k == "neg": return self.maybe(n[1])
        if k == "id":
            if n[1] == "__" or n[1] in self.maybe_ids: return True
            if n[1] in self.dyn: return self.maybe(self.dyn[n[1]])          # 起動で評価した定義の値が `__` になりうるか(セルには `__` の印のまま置く)
            return n[1] in self.consts and self.consts[n[1]] is None
        if k == "cmp": return True
        if k == "norm": return False
        if k == "input": return True                     # 読んだ 64 ビットがたまたま __ の型(印)かもしれない
        if k == "bin":
            op, l, r = n[1], n[2], n[3]
            if op == "-" and any((o[0] == "lit" and isinstance(o[1], Char) and len(o) == 2) or (o[0] == "id" and o[1] in self.chars) for o in (self.strip(l), self.strip(r))): return True        # 文字 - 文字: 片方が範囲の外なら __
            if op in ("+", "-", "*", "||", ";;", "&&"): return self.maybe(l) and self.maybe(r)
            if op in ("<<", ">>"): return True               # シフト数が負なら __
            if op in ("/", "%"):
                rr = r
                while rr[0] == "block": rr = rr[1]
                nonzero = (rr[0] == "lit" and rr[1] != 0) or (rr[0] == "neg" and rr[1][0] == "lit" and rr[1][1] != 0)
                return (self.maybe(l) and self.maybe(r)) or not nonzero
            if op == "#": return self.maybe(l)                # 番地が答え。左が __ なら __(右は評価しない)
            if op == "|": return self.maybe(l) and self.maybe(r)
            if op == "&": return self.maybe(l) or self.maybe(r)
            if op == "'":
                # 空でない器(仮引数・名前。`__` の器の呼びは走らない)の先頭 `p ' 0` と末尾 `p ' -1` は必ず在る
                nonempty = self.nonempty
                if nonempty(l) and self.const_int(r) in (0, -1) and self.slice_of(n) is None and self.tail_of(n) is None:
                    return False
                if self.idx_ok(n): return False
                return True
            return True
        if k == "cases":
            rows = n[1]
            if not rows or rows[-1][0] is not None: return True
            return any(self.maybe(v) for _, v in rows)
        if k == "seq":
            items = n[1]
            if self.list_values(n) is not None: return False
            if items[0][0] == "id" and items[0][1] in self.fns:
                return self.ret_maybe.get(items[0][1], False) or any(self.maybe(a) for a in items[1:])
            its = self.builds(n)
            if its is not None:         # 組み立てた並び: `__` にならない要素が 1 つでもあれば、全部は消えない
                return not any(self.item_info(it)[0] == "scalar" and not self.maybe(self.item_info(it)[1]) for it in its)
            return True
        return True

    def may_single(self, x, sp, relay):
        """式 x の値が、1 個だけ残った Int になりうるか(single_possible の説明を参照)。呼びは、呼び先が sp か、素通しで返す引数が Int になりうるとき。"""
        x = self.strip(x)
        its = self.builds(x)
        if its is not None:
            sc = [self.item_info(it)[1] for it in its if self.item_info(it)[0] == "scalar"]
            return any(self.maybe(a) for a in sc) and sum(1 for a in sc if not self.maybe(a)) < 2
        if x[0] == "seq" and x[1][0][0] == "id" and x[1][0][1] in self.fns:
            g = x[1][0][1]; args = x[1][1:]
            return g in sp or any(j < len(args) and self.may_single(args[j], sp, relay) for j in relay.get(g, ()))
        return False

    def single_possible(self):
        """関数ごとに『返値が、1 個だけ残った Int(処理系はリストでなく Int として扱う)になりうるか』。
        `__` になりうる要素のある組み立てで、`__` にならない要素が 2 個未満だと、全部が消えて 1 個だけ残りうる。1 個の器と Int は、値の演算(長さ・取り出し・展開)では同じだが、
        最上位の印字(処理系は `5`、スライスの 1 個の器は `[5]`)と、入れ子の要素では違いが出るので、そういう関数の結果を最上位で印字する形は断る。
        器の仮引数をそのまま返す枝(素通し)を持つ関数は、その実引数が Int になりうれば、結果もそうなる。"""
        relay = {}
        for f, body in self.live_bodies():
            for v in self.ret_nodes(body):
                x = self.strip(v)
                if x[0] == "id" and x[1] in self.fns[f] and self.pkind[f][self.fns[f].index(x[1])] == "L": relay.setdefault(f, set()).add(self.fns[f].index(x[1]))
        self.relay = relay
        sp, changed = set(), True
        while changed:
            changed = False
            for f, body in self.live_bodies():
                if f in sp or self.retk.get(f) != "L": continue
                if any(self.may_single(v, sp, relay) for v in self.ret_nodes(body)): sp.add(f); changed = True
        return sp

    def solve_maybe(self):
        """関数ごとの『返値が __ になりうるか』を、動かなくなるまで繰り返して決める(増える一方なので止まる)。"""
        changed = True
        while changed:
            changed = False
            for f, body in self.live_bodies():
                if not self.ret_maybe.get(f, False) and self.maybe(body):
                    self.ret_maybe[f] = True; changed = True

    def width_expr(self, a, f):
        """番地の項 a(関数 f の中)の幅(byte)。`1x…` `2x…` `4x…` `8x…` の字面・それを定義した名前・幅の分かった仮引数、
        それに数を足し引きした物は同じ幅。幅つき同士の和や『数 − 番地』は幅が落ちる(処理系の WInt と同じ)。value_representation.md §5。"""
        a = self.strip(a)
        if a[0] == "lit": return a[1].w if type(a[1]) is WInt else 0
        if a[0] == "id":
            if f and a[1] in self.fns.get(f, []): return (self.pw.get(f) or {}).get(self.fns[f].index(a[1])) or 0
            return self.cwidth.get(a[1], 0) if a[1] in self.consts else 0
        if a[0] == "bin" and a[1] in ("+", "-"):
            wl, wr = self.width_expr(a[2], f), self.width_expr(a[3], f)
            if a[1] == "+": return wl if wl and not wr else wr if wr and not wl else 0
            return wl if wl and not wr else 0
        return 0

    def solve_widths(self):
        """幅つきの番地が関数の仮引数へ渡る道を辿って、仮引数の幅を決める(型 `Address(w)` が幅を運ぶ代わり。§5.10)。
        幅の違う番地が同じ仮引数に渡る形は、機械では 1 つの読み書きの命令に決まらないので断る。"""
        self.pw = {f: {} for f in self.fns}
        def calls(x, out):
            if isinstance(x, tuple):
                if x and x[0] == "seq" and isinstance(x[1], list) and x[1] and x[1][0][0] == "id" and x[1][0][1] in self.fns: out.append(x)
                for y in (x[1:] if x and isinstance(x[0], str) else x): calls(y, out)         # 印の無い組(枝の (条件, 値))は先頭も辿る
            elif isinstance(x, list):
                for y in x: calls(y, out)
        changed = True
        while changed:
            changed = False
            srcs = [(f, b) for f, b in self.live_bodies()] + [(None, n) for n in self.nodes if n[0] != "def"]
            for f, body in srcs:
                cs = []; calls(body, cs)
                for c in cs:
                    g = c[1][0][1]
                    for i, a in enumerate(c[1][1:]):
                        if i >= len(self.fns[g]): break
                        w = self.width_expr(a, f)
                        if not w: continue
                        cur = self.pw[g].get(i)
                        if cur is None: self.pw[g][i] = w; changed = True
                        elif cur != w: raise AsmError("%s の第 %d 引数に、幅の違う番地(%d byte と %d byte)が渡されています。1 つの読み書きの命令に決まりません(value_representation.md §5)" % (g, i + 1, cur, w))

    def live_bodies(self):
        return [(f, b) for f, b in self.bodies.items() if f in self.live]

    def find_live(self):
        """最上位の式から辿れる関数だけ(使われない関数は出さない。仮引数の種類も、呼び出しからしか決まらない)。"""
        live, work = set(), []
        def visit(x):
            if isinstance(x, tuple) and x:
                if x[0] == "id" and len(x) == 2 and x[1] in self.fns and x[1] not in live: live.add(x[1]); work.append(x[1])
                for y in x: visit(y)
            elif isinstance(x, list):
                for y in x: visit(y)
        for n in self.nodes:
            if n[0] != "def": visit(n)
        while work: visit(self.bodies[work.pop()])
        self.live = live

    def dyn_shape(self, r):
        """値が字面でない定義の右辺として受ける形(Int の式の形): 整数の字面・名前・括り・符号・算術・関数の呼び出し。純粋かどうかは generate が後で確かめる。"""
        k = r[0]
        if k == "lit": return type(r[1]) is int
        if k == "id": return True
        if k in ("block", "neg"): return self.dyn_shape(r[1])
        if k == "bin": return r[1] in ("+", "-", "*", "/", "%", "&&", "||", ";;", "<<", ">>") and self.dyn_shape(r[2]) and self.dyn_shape(r[3])
        if k == "seq": return len(r[1]) >= 2 and r[1][0][0] == "id" and all(self.dyn_shape(a) or self.str_value(self.strip(a)) is not None for a in r[1][1:])       # 実引数は Int の式か、文字列の字面(`h : println `x``)
        return False

    def collect(self):
        dynn = []
        for n in self.nodes:
            if n[0] == "dyn":                                  # 一度 collect を通した節(補助関数を切り出したあとの作り直し)
                if n[1] not in self.dyn: self.dyn[n[1]] = n[2]
                dynn.append(n); continue
            if n[0] != "def": continue
            name, rhs = n[1], n[2]
            if name in self.fns or name in self.consts or name in self.lists or name in self.strs or name in self.nests or name in self.dyn: continue          # 先に書いた方が勝つ(compiler_pipeline.md §4)
            if rhs[0] == "lam":
                ps = []; dfl = []
                for p in rhs[1]:
                    if p[0] != "name":
                        raise AsmError("%s: 裸の仮引数(名前だけ。既定値は仮引数のブロックの `名前 : 式` の行)だけ出せます" % name)
                    ps.append(p[1])
                    if p[2] is not None: dfl.append((len(ps) - 1, p[2]))
                if len(set(ps)) != len(ps):
                    raise AsmError("%s: 仮引数の名前が重なっています" % name)
                if dfl:
                    if len(dfl) != len(ps) - dfl[0][0]: raise AsmError("%s: 既定値のある仮引数は、既定値の無い仮引数のあとに並べた形だけ出せます" % name)
                    self.defaults[name] = (dfl[0][0], [(ps[i], e) for i, e in dfl])
                self.fns[name] = ps
                self.bodies[name] = rhs[2]
            else:
                r = rhs
                while r[0] == "block": r = r[1]
                sv = self.str_value(r)
                lv = self.list_values(r)
                nv = self.nested_values(r) if lv is None and sv is None else None
                if nv is not None:
                    st = False; self.nest_mark_lit(r)
                    self.nests[name] = (self.nest_label(nv), len(nv), sum(len(v) for v in nv))
                elif r[0] == "id" and r[1] in self.nests: self.nests[name] = self.nests[r[1]]
                elif sv is not None: self.strs[name] = (self.rodata_label(sv, True), sv)
                elif r[0] == "id" and r[1] in self.strs: self.strs[name] = self.strs[r[1]]
                elif lv is not None: self.lists[name] = (self.rodata_label(lv), lv)
                elif r[0] == "id" and r[1] in self.lists: self.lists[name] = self.lists[r[1]]
                elif r[0] == "lit" and isinstance(r[1], Char) and len(r) == 2:
                    if not char_ok(ord(r[1])): raise AsmError(char_msg())
                    self.chars[name] = ord(r[1])
                elif r == ("id", "__"): self.consts[name] = None
                elif r[0] == "lit":
                    self.consts[name] = int_literal(r)
                    if type(r[1]) is WInt: self.cwidth[name] = r[1].w
                elif r[0] == "neg" and r[1][0] == "lit": self.consts[name] = -int_literal(r[1])
                elif self.const_val(r) is not self.NOF: self.consts[name] = self.const_val(r)          # 定数どうしの比べ(`ok : 3 < 5`、真なら左辺・偽なら `__`)と、`__` を含む算術(`c + 1`)を畳む
                elif self.const_int(r) is not None: self.consts[name] = self.const_int(r)          # 定数名どうしの + - *(`color : gfx + 0x08`)は、その場で畳む
                elif self.dyn_shape(r):
                    self.dyn[name] = r; dynn.append(("dyn", name, r))          # 値が計算で決まる定義(`a : fib 30`): 起動のとき一度だけ評価してセルに置く(generate が確かめる)
                else:
                    raise AsmError("%s: 値が字面でない定義はまだ出せません" % name)
        if dynn: self.nodes = dynn + [m for m in self.nodes if m[0] != "dyn"]          # 値が計算で決まる定義は、式より先に(源の順で)評価する。定義の節は残る(同じ名前の後の定義は無視される)

    flagged = False

    def unpack_params(self, fname, lam):
        """括りの仮引数 `[px py lv]`(名前だけ)を、器 1 本の仮引数 `_dN` と、本体の中の `px` → `_dN ' 0`、`py` → `_dN ' 1`、… の置き換えに直す。
        処理系の読み(観測): 名前は位置で結ばれ、足りない名前は `__`、余りは捨てる。これは `_dN ' k` の読みと同じ(範囲の外は `__`)。
        最後の残り `~t` は `_dN ' k~`(k は前の名前の数)に直す。既定値・残りの後ろの名前・入れ子の括り・本体の中で同じ名前を束ね直す形は断る。"""
        ps, body = lam[1], lam[2]
        if not any(p[0] == "destr" for p in ps): return lam
        mapping, out = {}, []
        for i, p in enumerate(ps):
            if p[0] != "destr": out.append(p); continue
            _, names, dflt, rest_a, rest_b = p[:5] if len(p) >= 5 else (p + (None,) * 5)[:5]
            # p = ("destr", 名前の並び, 残りの名前か None, 既定値の表, 残りの後ろの名前の並び)。dflt が残りの名前、rest_a が既定値、rest_b が後ろの名前
            if rest_a or rest_b or not all(isinstance(nm, str) and nm.isidentifier() and nm != "_" for nm in names) or not (dflt is None or (isinstance(dflt, str) and dflt.isidentifier() and dflt != "_")):
                raise AsmError("%s: 括りの仮引数は名前と最後の残り `[a b ~rest]` だけ出せます(既定値・残りの後ろの名前・入れ子はまだ)" % fname)
            if len(set(names + ([dflt] if dflt else []))) != len(names) + (1 if dflt else 0): raise AsmError("%s: 括りの中の名前が重なっています" % fname)
            fresh = "_d%d" % i
            out.append(("name", fresh, None))
            for k, nm in enumerate(names):
                mapping[nm] = ("block", ("bin", "'", ("id", fresh), ("lit", k)))
            if dflt: mapping[dflt] = ("block", ("bin", "'", ("id", fresh), ("post", "~", ("lit", len(names))))) if names else ("id", fresh)      # 残り `~t` は `_dN ' k~`(k = 前の名前の数)。前に名前が無ければ器そのもの
        if any(p[0] == "name" and p[1] in mapping for p in out): raise AsmError("%s: 括りの中の名前が別の仮引数と重なっています" % fname)
        def sub(x):
            if isinstance(x, tuple):
                if x[:1] == ("id",) and len(x) == 2 and x[1] in mapping: return mapping[x[1]]
                if x[:1] == ("lam",) and any(isinstance(q, tuple) and ((q[0] == "name" and q[1] in mapping) or (q[0] == "destr" and any(nm in mapping for nm in q[1]))) for q in x[1]):
                    raise AsmError("%s: 括りの名前を内側の器が束ね直しています" % fname)
                if x[:1] == ("def",) and len(x) > 1 and x[1] in mapping: raise AsmError("%s: 括りの名前を本体の中で定義し直しています" % fname)
                return tuple(sub(y) for y in x)
            if isinstance(x, list): return [sub(y) for y in x]
            return x
        return ("lam", out, sub(body))

    def pure_relay(self, g):
        """g の返す物が、器の仮引数 j そのもの(か `__`)だけなら j、でなければ None。"""
        pj = None
        for v in self.ret_nodes(self.bodies[g]):
            v = self.strip(v)
            if v == ("id", "__"): continue
            if v[0] == "id" and v[1] in self.fns[g] and self.pkind[g][self.fns[g].index(v[1])] == "L":
                j = self.fns[g].index(v[1])
                if pj not in (None, j): return None
                pj = j
            else: return None
        return pj

    def flag_ok(self, x, seen=None):
        """最上位で印字する式 x が、1 個だけ残ったとき Int になりうるのを、実行時の旗(x2 = 1: 組み立てた結果が 1 個だけ)で運べる形か。
        旗を運べるのは、組み立てた並び自身か、その呼び(素通しで器の引数を返さない関数)を辿った先。通るなら旗を運ぶ関数を flagfns に入れる。"""
        x = self.strip(x)
        if self.builds(x) is not None: return True
        if not (x[0] == "seq" and x[1][0][0] == "id" and x[1][0][1] in self.fns): return False
        g = x[1][0][1]; seen = seen if seen is not None else set()
        if g in seen: return True
        seen.add(g)
        pj = self.pure_relay(g)
        if pj is not None and g not in self.sp:        # 受けた器をそのまま返すだけの関数: 旗は実引数から運ぶ(呼ぶ側が実引数の旗を覚えて、戻ったあとに置き直す)
            a = self.strip(x)[1][1 + pj]
            if not self.may_single(a, self.sp, self.relay): return True
            if self.flag_ok(a, seen): self.flagrelay.add(g); return True
            return False
        if self.relay.get(g):                          # 枝によって返す器の引数が変わる関数: 実引数の旗をビットで渡す
            args = self.strip(x)[1][1:]
            for j in self.relay[g]:
                if j < len(args) and self.may_single(args[j], self.sp, self.relay) and not self.flag_ok(args[j], seen): return False
            self.maskfns.add(g)
        elif g not in self.sp: return False
        ok = True
        for v in self.ret_nodes(self.bodies[g]):
            v = self.strip(v)
            if v[0] == "seq" and v[1][0][0] == "id" and v[1][0][1] in self.fns and self.builds(v) is None:
                if self.may_single(v, self.sp, self.relay) and not self.flag_ok(v, seen): ok = False
        if ok: self.flagfns.add(g)
        return ok

    def expand_defaults(self):
        """既定値のある関数(仮引数のブロックの `名前 : 式` の行。coproduct_spec R128: 局所の値の置き場)の呼び出しを、全部の実引数を渡す形に直す。
        既定値の式は、前の仮引数の名前をその実引数で置き換えて、呼ぶ側で評価する(処理系の観測: 既定のモードは、足りない実引数を既定値で埋める)。
        実引数が既定値に使われるときは、呼び出しを含まない式だけ(同じ式を何度か評価することになるため)。全部渡した呼び出し(`g 10 3 4`)はそのまま。"""
        if not self.defaults: return
        dflt = self.defaults
        def subst(x, m):
            if isinstance(x, tuple) and x:
                if x[0] == "id" and len(x) == 2: return ("block", m[x[1]]) if x[1] in m else x
                return tuple(x[:1]) + tuple(subst(y, m) for y in x[1:])
            if isinstance(x, list): return [subst(y, m) for y in x]
            return x
        def has_call(x):
            if isinstance(x, tuple) and x:
                if x[0] == "seq" and x[1] and x[1][0][0] == "id" and (x[1][0][1] in self.fns or x[1][0][1] in dflt): return True
                return any(has_call(y) for y in x[1:])
            if isinstance(x, list): return any(has_call(y) for y in x)
            return False
        def walk(x):
            if isinstance(x, list): return [walk(y) for y in x]
            if not isinstance(x, tuple) or not x: return x
            if x[0] == "id": return x
            y = tuple(x[:1]) + tuple(walk(z) for z in x[1:])
            if y[0] == "seq" and y[1] and y[1][0][0] == "id" and y[1][0][1] in dflt:
                f = y[1][0][1]; k, ds = dflt[f]; args = y[1][1:]
                if len(args) == k:
                    ps = self.fns[f]; m = {}
                    for p, a in zip(ps, args): m[p] = a
                    used = set()
                    def ids(e):
                        if isinstance(e, tuple) and e:
                            if e[0] == "id" and len(e) == 2: used.add(e[1])
                            else:
                                for q in e[1:]: ids(q)
                        elif isinstance(e, list):
                            for q in e: ids(q)
                    for _, e in ds: ids(e)
                    for p, a in zip(ps, args):
                        if p in used and has_call(a): raise AsmError("%s: 既定値が使う実引数に、関数の呼び出しを含む形はまだ出せません(同じ式を何度も評価することになる)。実引数を先に名前に置いてください" % f)
                    out = list(args)
                    for p, e in ds:
                        v = subst(e, m); m[p] = v; out.append(("block", v))
                    y = ("seq", [y[1][0]] + out) + tuple(y[2:])
            return y
        nodes = []
        for n in self.nodes:
            if n[0] == "def" and n[2][0] == "lam":
                lam = n[2]
                nodes.append(("def", n[1], ("lam", [("name", p[1], None) if p[0] == "name" else p for p in lam[1]], walk(lam[2]))) + tuple(n[3:]))
            else: nodes.append(walk(n))
        self.nodes = nodes
        for n in nodes:
            if n[0] == "def" and n[2][0] == "lam" and n[1] in self.fns and n[1] in self.bodies:
                if n[1] not in getattr(self, "_bd_done", set()): self.bodies[n[1]] = n[2][2]; self._bd_done = getattr(self, "_bd_done", set()) | {n[1]}
            elif n[0] == "dyn": self.dyn[n[1]] = n[2]
        self.defaults = {}

    def inline_wide_dyn(self):
        """値が器・文字列になる最上位の定義(`xs : mk 3`)。器は長さが実行で決まり、置き場は呼ぶ側の物なので、セルには置けない。
        右辺は純粋で決まった値なので、使う所へ括った右辺を書き込む(使うたびに作り直す。値は同じ)。定義の節は外して、作り直した節の並びを返す(None なら該当なし)。"""
        wide = {}
        for n in self.nodes:
            if n[0] == "dyn" and n[1] not in wide:
                try: kd = self.kind(n[2], {})
                except AsmError: continue
                if kd in WIDE: wide[n[1]] = n[2]
        if not wide: return None
        def sub(x, bound=()):
            if isinstance(x, list): return [sub(y, bound) for y in x]
            if not isinstance(x, tuple) or not x: return x
            if x[0] == "id" and len(x) == 2: return ("block", wide[x[1]]) if x[1] in wide and x[1] not in bound else x
            if x[0] == "lam":
                nb = tuple(bound) + tuple(p[1] for p in x[1] if p[0] == "name")
                return ("lam", [("name", p[1], sub(p[2], bound) if p[2] is not None else None) if p[0] == "name" else p for p in x[1]], sub(x[2], nb)) + tuple(x[3:])
            return tuple(x[:1]) + tuple(sub(y, bound) for y in x[1:])
        out = []; gone = set()
        for n in self.nodes:
            if n[0] == "dyn" and n[1] in wide: continue
            if n[0] == "def" and n[1] in wide and n[1] not in gone and (n[2] is wide[n[1]] or True):
                if n[2][0] != "lam": gone.add(n[1]); continue
            out.append(sub(n))
        return out

    def fn_dyn_refs(self, f, seen=None):
        """関数 f(と、f から呼ぶ関数)の本体が読む『起動で評価する定義』の名前の集まり。"""
        seen = seen if seen is not None else set(); out = set()
        if f in seen or f not in self.bodies: return out
        seen.add(f)
        def walk(x):
            if isinstance(x, tuple) and x:
                if x[0] == "id" and len(x) == 2:
                    if x[1] in self.dyn: out.add(x[1])
                    elif x[1] in self.fns: out.update(self.fn_dyn_refs(x[1], seen))
                else:
                    for y in x[1:]: walk(y)
            elif isinstance(x, list):
                for y in x: walk(y)
        walk(self.bodies[f])
        return out

    def check_dyn(self):
        """値が計算で決まる定義(`a : fib 30`)を確かめる。右辺は 定数・先に書いた同じ種類の定義・純粋な整数関数の呼び出しの + - * / % など(副作用が無いので、
        起動のときに源の順で一度だけ評価してよい)。`__` になりうる右辺、まだ評価していない定義を読む関数を呼ぶ右辺は、まだ出せない。
        式が1つも無い(印字する物が無い)ファイルでは、評価しても見えないので何も出さない。"""
        if not self.dyn: return
        if not any(n[0] not in ("def", "dyn") for n in self.nodes):
            self.nodes = [n for n in self.nodes if n[0] != "dyn"]; self.dyn = {}; return
        el = self.par_elig(); known = set()
        why = "右辺は、定数・先に書いた同じ種類の定義・純粋な整数関数(仮引数が Int・Int の器・文字列で、メモリに触れない。器は字面の名前)の呼び出しの + - * / % など(`__` になってもよい)だけ出せます"
        def pure(r):
            k = r[0]
            if k == "lit": return type(r[1]) is int
            if k == "id": return isinstance(self.consts.get(r[1]), int) or r[1] in known
            if k in ("block", "neg"): return pure(r[1])
            if k == "bin": return r[1] in ("+", "-", "*", "/", "%", "&&", "||", ";;", "<<", ">>") and pure(r[2]) and pure(r[3])
            if k == "seq":
                h = r[1][0]
                if h[0] != "id" or h[1] not in self.fns or len(r[1]) - 1 != len(self.pkind.get(h[1], ())): return False
                eff = h[1] not in el                          # 副作用のある関数(`println`)の呼びも、起動のとき源の順で一度だけ評価する(処理系は定義を読み込みの順に一度だけ評価する)
                for a, kd in zip(r[1][1:], self.pkind[h[1]]):
                    if kd == "I":
                        if not pure(a): return False
                    elif eff and kd == "S" and self.str_value(self.strip(a)) is not None: continue
                    else:
                        a = self.strip(a)
                        if not (a[0] == "id" and ((kd == "L" and a[1] in self.lists) or (kd == "S" and a[1] in self.strs) or (kd == "N" and a[1] in self.nests))): return False
                return self.fn_dyn_refs(h[1]) <= known
            return False
        for n in self.nodes:
            if n[0] != "dyn": continue
            if not pure(n[2]) or self.kind(n[2], {}) != "I":
                raise AsmError("%s: 値が字面でない定義はまだ出せません(%s)" % (n[1], why))
            known.add(n[1])

    def lift_args(self):
        """関数の呼びの実引数に、要素を式で組み立てた器(`g (n n n)`、`g ((xs ' 0) 7)`)があれば、それを返すだけの補助関数に切り出して、
        実引数をその呼びに置き換えた節の並びを返す(なければ None)。器を組み立てる置き場は『返値の位置』でしか取れないので、
        補助関数の返値にすれば、置き場は呼ぶ側が上界で取る既存の道で済む。補助関数の仮引数は、並びが使う、いまの関数の仮引数。"""
        used = {n[1] for n in self.nodes if n[0] == "def"}
        newdefs, cnt, mkc = [], [0], {}
        globs = set(self.fns) | set(self.consts) | set(self.dyn) | set(self.lists) | set(self.strs) | set(self.nests) | {"__"}
        def ids(x, acc):
            if isinstance(x, tuple) and x:
                if x[0] == "id" and len(x) == 2: acc.add(x[1])
                else:
                    for y in (x[1:] if isinstance(x[0], str) else x): ids(y, acc)
            elif isinstance(x, list):
                for y in x: ids(y, acc)
            return acc
        def x_callee_is_self_j(f, name, j):
            return j < len(self.fns[f]) and self.fns[f][j] == name       # 呼ぶ側の j 番目の仮引数そのもので始まる(自分への呼びで j 番目を伸ばす形)
        def reaches(g, f):
            """g から呼びを辿って f に着くか(自分・輪への呼びの実引数は、累積を伸ばす道(`acc~ x`)に任せる)。"""
            seen, work = set(), [g]
            while work:
                h = work.pop()
                if h == f: return True
                if h in seen or h not in self.bodies: continue
                seen.add(h); work += [y for y in ids(self.bodies[h], set()) if y in self.fns]
            return False
        def eats_(args, f):
            for a in args:
                sa = self.strip(a); tl = self.tail_of(sa) if sa[0] == "bin" else None
                if tl and tl[1] >= 1 and self.strip(tl[0])[0] == "id" and self.strip(tl[0])[1] in self.fns[f]: return True
            return False
        def acc_form(sa, f, env, j, g=None, x_args=()):
            """並びが、いまの関数の器の仮引数で始まる(`acc~ x`・文字列の `acc c`)=累積を伸ばす形か。それは累積の道に任せる。"""
            its = self.builds(sa)
            if not its: return False
            ty, y = self.item_info(its[0]); y = self.strip(y)
            return y[0] == "id" and y[1] in self.fns[f] and env.get(y[1]) in ("L", "S", "N") and (x_callee_is_self_j(f, y[1], j) or (g is not None and g != f and (self.retk.get(f) == "N" or (self.retk.get(f) in ("L", "S") and eats_(x_args, f)))))
        def walk(x, f, env):
            if isinstance(x, list): return [walk(y, f, env) for y in x]
            if not isinstance(x, tuple) or not x: return x
            x = tuple(x[:1]) + tuple(walk(y, f, env) for y in x[1:]) if x[0] != "id" else x
            if x[0] == "seq" and x[1] and x[1][0][0] == "id" and x[1][0][1] in self.fns:
                out = [x[1][0]]
                for aj, a in enumerate(x[1][1:]):
                    sa = self.strip(a)
                    if sa[0] == "seq" and not (f and reaches(x[1][0][1], f) and acc_form(sa, f, env, aj, x[1][0][1], x[1][1:])) and self.builds(sa) is not None and self.kind(sa, env) in ("L", "N", "S"):
                        fv = ids(sa, set())
                        ps = [p for p in (self.fns[f] if f else []) if p in fv]
                        if all(v in globs or v in ps for v in fv):
                            while True:
                                cnt[0] += 1; nm = "mkarg%d" % cnt[0]
                                if nm not in used: break
                            used.add(nm)
                            try: sz0 = self.size_of(sa, f)
                            except AsmError: sz0 = None
                            if sz0 is not None and self.kind(sa, env) in ("L", "S"): mkc[nm] = (sz0[0], dict(sz0[1]), f)      # 新しい器の大きさ(定数 + 仮引数の長さ)
                            params = ps or ["z"]
                            newdefs.append(("def", nm, ("lam", [("name", p, None) for p in params], sa)))
                            a = ("block", ("seq", [("id", nm)] + ([("id", p) for p in ps] or [("lit", 0)])))
                    out.append(a)
                x = ("seq", out)
            return x
        nodes = []
        for n in self.nodes:
            if n[0] == "def" and n[1] in self.fns and n[1] in self.live and n[2][0] == "lam" and self.bodies.get(n[1]) is n[2][2]:
                f = n[1]; env = dict(zip(self.fns[f], self.pkind[f]))
                nodes.append(("def", f, ("lam", n[2][1], walk(n[2][2], f, env))))
            elif n[0] != "def": nodes.append(walk(n, None, {}))
            else: nodes.append(n)
        if not newdefs: return None
        self.mkc_next = dict(self.mk_const); self.mkc_next.update(mkc)
        return nodes + newdefs

    def rev_apply(self):
        """`x g`(値のあとに引数 1 個の関数の名前、ちょうど 2 項)は逆適用(operator_table 10.3)で `g x`。呼びの形に直す。"""
        def walk(x):
            if isinstance(x, tuple) and x:
                r = tuple(walk(y) if isinstance(y, (tuple, list)) else y for y in x)
                if r[0] == "seq" and len(r) == 2 and isinstance(r[1], list) and len(r[1]) == 2:
                    a, b = r[1]
                    if b[0] == "id" and b[1] in self.fns and len(self.fns[b[1]]) == 1 and not (a[0] == "id" and a[1] in self.fns):
                        return ("seq", [b, a])
                return r
            if isinstance(x, list): return [walk(y) if isinstance(y, (tuple, list)) else y for y in x]
            return x
        def hit(x):
            if isinstance(x, tuple) and x:
                if x[0] == "seq" and len(x) == 2 and isinstance(x[1], list) and len(x[1]) == 2:
                    a, b = x[1]
                    if b[0] == "id" and b[1] in self.fns and len(self.fns[b[1]]) == 1 and not (a[0] == "id" and a[1] in self.fns): return True
                return any(hit(y) for y in x if isinstance(y, (tuple, list)))
            if isinstance(x, list): return any(hit(y) for y in x if isinstance(y, (tuple, list)))
            return False
        if not (any(hit(n) for n in self.nodes) or any(hit(b) for b in self.bodies.values())): return          # 直す所が無ければ節の同一性を壊さない
        self.nodes = [walk(n) for n in self.nodes]
        for n in self.nodes:                     # 節の本体と bodies は同じ物でなければならない(lift_args などが同一性で見る)
            if n[0] == "def" and n[1] in self.bodies and n[2][0] == "lam": self.bodies[n[1]] = n[2][2]

    def fold_nest_pick(self):
        """`((x 2) 3) ' 0` のように、中身が全部 `__` にならない入れ子の並びの字面から、定数の添字で入れ子の並びを選ぶ形は、選んだ内側の並び `(x 2)` に
        置き換える(位置は実行時にずれないので静的に決まる)。結果は普通の並びの字面になり、返値の位置・引数の位置など、並びの字面が使える所で使える。
        種類が決まったあと(仮引数の種類が要る)に呼ぶ。直す所が無ければ何もしない(ノードの同一性を壊さない)。"""
        def pick(n, env):
            if n[0] == "bin" and n[1] == "'":
                k = self.const_int(n[3]); base = self.static_list(n[2], env)
                if k is None or base is None: return None
                it = base[1]
                if not -len(it) <= k < len(it): return None
                e = it[k]
                while e[0] == "block": e = e[1]
                if e[0] == "seq" and self.solid_seq(e, env) is not None: return e
            return None
        def hit(x, env):
            if isinstance(x, tuple) and x:
                if x[0] == "bin" and pick(x, env) is not None: return True
                return any(hit(y, env) for y in x if isinstance(y, (tuple, list)))
            if isinstance(x, list): return any(hit(y, env) for y in x if isinstance(y, (tuple, list)))
            return False
        def walk(x, env):
            if isinstance(x, tuple) and x:
                if x[0] == "bin":
                    r = pick(x, env)
                    if r is not None: return ("block", r)
                t = tuple(walk(y, env) if isinstance(y, (tuple, list)) else y for y in x)
                return t[1] if t[0] == "block" and t[1][0] == "block" else t              # 括りが二重にならないようにする
            if isinstance(x, list): return [walk(y, env) if isinstance(y, (tuple, list)) else y for y in x]
            return x
        envs = {f: dict(zip(self.fns[f], self.pkind[f])) for f in self.fns}
        env_of = lambda n: envs.get(n[1], {}) if n[0] == "def" else {}
        if not (any(hit(b, envs[f]) for f, b in self.bodies.items() if f in envs) or any(hit(n, env_of(n)) for n in self.nodes)): return
        self.nodes = [walk(n, env_of(n)) for n in self.nodes]
        for n in self.nodes:                     # 節の本体と bodies は同じ物でなければならない(lift_args などが同一性で見る)
            if n[0] == "def" and n[1] in self.bodies and n[2][0] == "lam": self.bodies[n[1]] = n[2][2]

    def drop_void_items(self):
        """並び(余積 `a b c`)から、畳める `__` の要素を消す。処理系は `__` の要素を並びから落とす(`(c 4) ' 0` は 4、`(c c)` は `__`、1 個だけ残れば Int の 4)。
        関数の呼び(先頭が関数の名前)や、関数の名前を要素に持つ並びは、`__` の実引数が `__` を返すので触らない。"""
        def void(e):
            return self.const_val(e) is None
        def callish(items):
            return any(isinstance(x, tuple) and len(x) == 2 and x[0] == "id" and x[1] in self.fns for x in items)
        def walk(x):
            if isinstance(x, tuple) and x:
                if x[0] == "seq" and len(x) == 2 and isinstance(x[1], list):
                    items = [walk(y) for y in x[1]]
                    if callish(items): return ("seq", items)
                    keep = [y for y in items if not void(y)]
                    if len(keep) == len(items): return ("seq", items)
                    if not keep: return ("id", "__")
                    return keep[0] if len(keep) == 1 else ("seq", keep)
                r = tuple(walk(y) if isinstance(y, (tuple, list)) else y for y in x)
                if r[0] == "bin" and len(r) == 4 and r[1] == "'" and void(r[2]): return ("id", "__")          # `__ ' k` は `__`
                if r[0] == "bin" and len(r) == 4 and r[1] == "'" and self.const_int(r[2]) is not None and self.const_int(r[3]) is not None:          # 定数の Int は長さ 1 の並びと読まれる(処理系の観測: `4 ' 0` と `4 ' (0 - 1)` は 4、ほかは `__`)
                    return r[2] if self.const_int(r[3]) in (0, -1) else ("id", "__")
                if r[0] == "norm" and len(r) == 2 and void(r[1]): return ("lit", 0)                            # `||__||` は 0
                return r
            if isinstance(x, list): return [walk(y) if isinstance(y, (tuple, list)) else y for y in x]
            return x
        if not any(v is None for v in self.consts.values()) and not any(isinstance(n, tuple) and n[0] == "cmp" for n in self.nodes): return
        self.nodes = [n if n[0] == "def" and n[1] in self.consts else walk(n) for n in self.nodes]
        for f in list(self.bodies): self.bodies[f] = walk(self.bodies[f])

    def tail_nonvoid(self, n):
        """n が末尾の切り出し `p ' a~`(p は仮引数)で、そこへ来る経路の条件から ||p|| > a と言えるなら True(a 個以下しか無いと `__` になるので、それが無いと言える)。"""
        n = self.strip(n)
        if not (isinstance(n, tuple) and n and n[0] == "bin" and n[1] == "'"): return False
        t = self.tail_of(n)
        if t is None: return False
        l = self.strip(t[0])
        if l[0] != "id": return False
        if getattr(self, "_lbmap", None) is None: self._lbmap = self.build_lbmap()
        lb = max(1, self._lbmap.get(id(n), {}).get(l[1], 0))
        return t[1] < lb

    def strict_call_check(self):
        """--strict(STRICT[0])のとき、規則 6: 実引数が計算で `!_` になりうる関数の呼びを調べる。strict は `!_` の実引数が流れから消えて関数が余る(部分適用。R83・R84)。
        asm(既定の読み)は呼び全体が `!_`。両者が分かれるのは、余った関数が生きるとき(同じ流れの後ろに値が続いて受け取るか、`~` で値として流れに残るか)だけ。
        演算子の項・`||…||`・添字・他の関数の最後の実引数では `!_` と同じ答え。余った関数は関数の境界(定義の本体の終わり)を越えない(`(p 0) 5` は p の本体が余った関数でも 5。strict の値で確かめた)。
        1. 実引数が `!_` になりうる(syntactic: 比べ・`& | ;`・`/ %`・書いた `__`。添字は範囲内の証明 idx_ok・末尾の切り出しは tail_nonvoid で言えなければ)呼びを「漏らす呼び」とする。
           条件の行(`c : …`)の中で、実引数がその条件そのもの(末尾の切り出しなら ||xs|| > a)なら、その枝では `!_` でない。
        2. 部分適用を静的に解く: 漏らす呼びの実引数が 1 つ(比べか末尾の切り出し)で、後ろに字面の値が続き、並びが 3 項以上なら、条件の行で 2 つの枝に分けた木を返す
           (`!_` でない枝は今のまま、`!_` の枝は実引数を消して次の値を最後の実引数にした呼び。generate が作り直す)。枝の値の種類(Int と並び)が揃わない形は AsmError で断る。
        3. 解けない漏らす呼び(後ろに値が続く・`~` が付く)は、実引数が実際に `!_` になったときだけ罠(.Ltrap_part, x16 = 3)で止める。
           `~` は余った関数が値として流れに残る(asm に関数値は無い)ので、出ない入力は strict と同じ答え、出る入力は黙って別の答えにせず止まる。
           罠を出せなかった呼び(codegen が節を作り直したなど)が残れば、generate の終わりで StrictRefusal(part_seen)。
           引数の数が仮引数の数と違う漏らす呼びは断る(strict は引数がずれて別の関数の読みになる)。"""
        if not STRICT[0]: return
        def unwrap(n):
            while isinstance(n, tuple) and n and n[0] == "block": n = n[1]
            return n
        def has_idx(n):
            stack = [n]
            while stack:
                x = stack.pop()
                if not isinstance(x, tuple) or not x or x[0] == "lam": continue
                if x[0] == "bin" and len(x) == 4 and x[1] == "'": return True
                for y in x[1:]:
                    if isinstance(y, tuple): stack.append(y)
                    elif isinstance(y, list): stack.extend(z for z in y if isinstance(z, tuple))
            return False
        def syn_void(n):
            stack = [n]
            while stack:
                x = stack.pop()
                if not isinstance(x, tuple) or not x or x[0] == "lam": continue
                if x[0] == "hole" or (x[0] == "not" and x[1] == ("hole",)) or x == ("id", "__"): return True
                if x[0] == "cmp": return True
                if x[0] == "bin" and len(x) == 4:
                    if x[1] in ("&", "|", ";"): return True
                    if x[1] in ("/", "%") and not (x[3][0] == "lit" and x[3][1] != 0): return True
                for y in x[1:]:
                    if isinstance(y, tuple): stack.append(y)
                    elif isinstance(y, list): stack.extend(z for z in y if isinstance(z, tuple))
            return False
        def idx_void(mm):
            """添字を含む実引数が `!_` になりうるか(範囲内と言えない添字・入れ子の要素の添字を含むなら True)"""
            try:
                if self.maybe(mm) and not self.tail_nonvoid(mm): return True
                stack = [mm]
                while stack:
                    x = stack.pop()
                    if not isinstance(x, tuple) or not x or x[0] == "lam": continue
                    if x[0] == "bin" and len(x) == 4 and x[1] == "'":
                        lx = self.strip(x[2])
                        if (isinstance(lx, tuple) and lx and lx[0] == "bin" and len(lx) == 4 and lx[1] == "'") or (self.maybe(x) and not self.tail_nonvoid(x)): return True
                    for y in x[1:]:
                        if isinstance(y, tuple): stack.append(y)
                        elif isinstance(y, list): stack.extend(z for z in y if isinstance(z, tuple))
                return False
            except Exception: return True
        def arg_void(m):
            mm = unwrap(m)
            if not (isinstance(mm, tuple) and mm): return False
            if mm[0] == "seq" and len(mm[1]) >= 2 and not is_call(mm, ()): return False      # 流れ(`acc~ x`)は丸ごとは `!_` でない。要素の `!_` は elem_void が見る
            return syn_void(mm) or (has_idx(mm) and idx_void(mm))
        import sign_interp as SI
        def src(n):
            try: return SI.node_src(n)[:70]
            except Exception: return repr(n)[:70]
        def elem_void(n, params):
            stack = [n]
            while stack:
                x = stack.pop()
                if not isinstance(x, tuple) or not x or x[0] == "lam": continue
                if x[0] == "seq" and len(x[1]) >= 2 and not (isinstance(x[1][0], tuple) and x[1][0][0] == "id" and x[1][0][1] in self.fns and x[1][0][1] not in params):
                    if any(arg_void(it) for it in x[1]): return True
                for y in x[1:]:
                    if isinstance(y, tuple): stack.append(y)
                    elif isinstance(y, list): stack.extend(z for z in y if isinstance(z, tuple))
            return False
        gstack = []                       # いま居る条件の行の条件(鍵)。呼びの `!_` になりうる実引数が、その条件そのもの(か、末尾の切り出しの ||xs|| > a)なら、その枝では `!_` でない
        sites = []                        # 部分適用を静的に解ける呼び (並びの節, 位置, 呼びの節, `!_` になりうる実引数の位置, 末尾の切り出し (器, a))
        def guard_of(m):
            """実引数 m が `!_` でないと、いまの条件の行の条件から言えるか(m が比べそのもので、行の条件と同じ。末尾の切り出しなら ||xs|| > a が条件)。"""
            mm = unwrap(m)
            if not gstack: return False
            if isinstance(mm, tuple) and mm and mm[0] == "cmp": return self.skey(mm) in gstack
            try: tl = self.tail_of(self.strip(mm))
            except AsmError: return False
            if tl is None or not (isinstance(tl[0], tuple) and tl[0][0] == "id"): return False
            return self.skey(("cmp", [("norm", tl[0]), ("lit", tl[1])], [">"])) in gstack
        calls = []                        # (呼びの節, 後ろに値が続くか・`~` が付くか(余った関数が生きるか), 呼ぶ関数の名前, 漏らすか(実引数が void になりうる), 数が合うか)
        def is_call(n, params):
            return n[0] == "seq" and len(n[1]) >= 2 and isinstance(n[1][0], tuple) and n[1][0][0] == "id" and n[1][0][1] in self.fns and n[1][0][1] not in params
        def walk(n, params, live):
            """live = この節が、余った関数が生きる位置にあるか(同じ流れの後ろに値が続く・`~` で値として残る)。
            余った関数は関数の境界(定義の本体の終わり)を越えない(`(p 0) 5` は p の本体が余った関数を返しても 5。strict の値で確かめた)。"""
            if not isinstance(n, tuple) or not n: return
            k = n[0]
            if k == "lam":
                ps = set(params) | {q[1] for q in n[1] if isinstance(q, tuple) and len(q) > 1 and isinstance(q[1], str)}
                walk(n[2], ps, False); return
            if k == "block": walk(n[1], params, live); return
            if k == "seq":
                if is_call(n, params):
                    f = n[1][0][1]; args = n[1][1:]
                    voids = [j for j, m in enumerate(args) if arg_void(m) and not guard_of(m)]
                    for j, m in enumerate(args):                 # 実引数の流れの要素が `!_` になりうる(`acc~ (… ' 0)`)。strict は積まれずに消え、asm は印を要素に残す(質問書 A6)
                        if j not in voids and elem_void(unwrap(m), params):
                            raise StrictRefusal("--strict の読みにできない形があります(コンパイラは既定の読みで解きます):\n  [6] 実引数の並びの要素が `!_` になりうる呼び `%s …`(strict はその要素が消える。asm は `!_` の印を要素に残す。質問書 A6)\n      %s" % (f, src(n)))
                    calls.append((n, live, f, bool(voids), len(args) == len(self.fns[f])))
                    for j, m in enumerate(args): walk(m, params, j < len(args) - 1)       # 後ろの実引数が、余った関数に受け取られる
                    return
                its = n[1]
                for i_, it0 in enumerate(its[:-1]):                       # 部分適用を静的に解ける形: `!_` になりうる実引数が 1 つの呼びの後ろに、字面の値が続く
                    c_ = unwrap(it0)
                    if isinstance(c_, tuple) and c_ and c_[0] == "seq" and is_call(c_, params) and len(c_[1]) - 1 == len(self.fns[c_[1][0][1]]) and len(its) >= 3:
                        vs_ = [j for j, m in enumerate(c_[1][1:]) if arg_void(m) and not guard_of(m)]
                        r1_ = unwrap(its[i_ + 1])
                        if len(vs_) == 1 and isinstance(r1_, tuple) and r1_ and r1_[0] == "lit":
                            aj_ = unwrap(c_[1][1 + vs_[0]]); cond_ = None
                            try: tl_ = self.tail_of(self.strip(aj_))
                            except AsmError: tl_ = None
                            if tl_ is not None and isinstance(tl_[0], tuple) and tl_[0][0] == "id": cond_ = ("cmp", [("norm", tl_[0]), ("lit", tl_[1])], [">"])      # `xs ' a~` は ||xs|| > a のときだけ在る
                            elif isinstance(aj_, tuple) and aj_ and aj_[0] == "cmp": cond_ = aj_                                                                 # 比べは、真なら左の値、偽なら `!_`(条件の行は `!_` でなければ真)
                            if cond_ is not None: sites.append((n, i_, c_, vs_[0], cond_)); break
                for j, x in enumerate(its): walk(x, params, live or j < len(its) - 1)     # 後ろに値が続く項は、余った関数がそれを受け取る
                return
            if k == "cases":
                for c, e in n[1]:
                    if c is not None: walk(c, params, False)
                    if c is not None: gstack.append(self.skey(c))
                    try: walk(e, params, live)
                    finally:
                        if c is not None: gstack.pop()
                return
            if k == "bin" and len(n) == 4 and n[1] in ("&", "|"):
                walk(n[2], params, False); walk(n[3], params, live); return
            if k == "post" and n[1] == "~": walk(n[2], params, True); return          # `(g …)~`: 余った関数が値として流れに残る
            for y in n[1:]:
                if isinstance(y, tuple): walk(y, params, False)
                elif isinstance(y, list):
                    for z in y:
                        if isinstance(z, tuple):
                            if len(z) == 2 and k == "cases": walk(z[0], params, False); walk(z[1], params, live)
                            else: walk(z, params, False)
        owners = {}                                   # 呼びの節の id → それを含む定義の名前(出力されない関数の中の呼びは、罠を出せなくてもよい)
        for n in self.nodes:
            k0 = len(calls)
            if n[0] == "def" and isinstance(n[2], tuple) and n[2][0] == "lam": walk(n[2], set(), False)
            elif n[0] == "def": walk(n[2], set(), False)
            else: walk(n, set(), False)
            for c in calls[k0:]: owners[id(c[0])] = n[1] if n[0] == "def" else None
        if sites:
            if getattr(self, "sc_depth", 0) > 30: raise StrictRefusal("--strict の読みにできない形があります(コンパイラは既定の読みで解きます):\n  [6] 余った関数が後ろの値を受け取る呼びが多すぎて、静的に解ききれません")
            seq_, i_, c_, j_, cond = sites[0]
            its = seq_[1]; head = c_[1][0]; args = c_[1][1:]
            newcall = ("seq", [head] + args[:j_] + args[j_ + 1:] + [its[i_ + 1]]) + tuple(c_[2:])        # `!_` の実引数は流れから消え、関数は次の値を受け取る
            items2 = list(its[:i_]) + [("block", newcall)] + list(its[i_ + 2:])
            row2 = items2[0] if len(items2) == 1 else ("seq", items2) + tuple(seq_[2:])
            new = ("cases", [(cond, seq_), (None, row2)])
            def subst(x):
                if x is seq_: return new
                if isinstance(x, tuple): return tuple(subst(y) for y in x) if any(isinstance(y, (tuple, list)) for y in x) else x
                if isinstance(x, list): return [subst(y) for y in x]
                return x
            return [subst(n0) for n0 in self.nodes]
        for (n, live, f, voidarg, fit) in calls:
            if voidarg and not fit:
                raise StrictRefusal("--strict の読みにできない形があります(コンパイラは既定の読みで解きます):\n  [6] 実引数が `!_` になりうる呼び `%s …` で、引数の数が仮引数の数と違う(strict は `!_` の実引数が消えて引数がずれる。R83・R84)\n      %s" % (f, src(n)))
            if voidarg and live:                       # 余った関数が生きる形: 関数値は asm に無いので、実引数が実際に `!_` になったときだけ罠で止める(出ない入力は strict と同じ答え)
                self.part_trap[id(n)] = (n, src(n), owners.get(id(n)))

    def generate(self, target="bare", source=None):
        self.target = target
        self.collect()
        self.rev_apply()
        self.drop_void_items()
        self.expand_defaults()
        self.find_live()
        self.solve_kinds()
        self.fold_nest_pick()
        nn = self.inline_wide_dyn()
        if nn is None: nn = self.lift_args()
        if nn is not None:
            sub = Program(nn); sub.mk_const = getattr(self, "mkc_next", getattr(self, "mk_const", 0)); out = sub.generate(target, source)
            self.__dict__.update(sub.__dict__)
            return out
        self.solve_widths()
        self.solve_slots()
        self.solve_maybe()
        nn = self.strict_call_check()
        if nn is not None:
            sub = Program(nn); sub.mk_const = getattr(self, "mkc_next", getattr(self, "mk_const", 0)); sub.sc_depth = getattr(self, "sc_depth", 0) + 1; out = sub.generate(target, source)
            self.__dict__.update(sub.__dict__)
            return out
        self.check_dyn()
        self.sp = self.single_possible()
        ex0 = [n for n in self.nodes if n[0] not in ("def", "dyn")]
        if ex0 and self.kind(ex0[-1], {}) == "L" and self.may_single(ex0[-1], self.sp, self.relay) and self.flag_ok(ex0[-1]):
            self.flagged = True; self.flagfns.add("_.main")      # 1 個だけ残ると Int になりうる結果を、旗(x2)つきで印字する
        out = ["// Sign — AArch64 (AAPCS64)"]
        if source: out.append("// source: %s" % source)
        out += ["\t.text", ""]
        done = set()
        for n in self.nodes:
            if n[0] == "def" and n[1] in self.fns and n[1] in self.live and n[1] not in done and n[2][0] == "lam":
                done.add(n[1])
                try:
                    g = FnGen(self, n[1], self.fns[n[1]], loop=True)
                    g.reserve_shared(n[2][2])
                    g.pre_grow()
                    g.gen_any(n[2][2], True, self.retk[n[1]])
                    out += g.finish(symbol_of(n[1])) + [""]
                except AsmError as e:
                    if "[関数 " in str(e): raise
                    raise AsmError("%s [関数 %s の中]" % (e, n[1]))
        dynn = [n for n in self.nodes if n[0] == "dyn"]
        exprs = [n for n in self.nodes if n[0] not in ("def", "dyn")]
        if exprs and self.kind(exprs[-1], {}) == "L":
            bad = self.may_single(exprs[-1], self.sp, self.relay)
            if bad and self.flagged: bad = False
            if bad: raise AsmError("最上位で印字する器が、`__` になりうる要素のせいで、1 個だけ残って Int になりうる形です(処理系は `5`、1 個の器は `[5]` と書き分ける)。`__` にならない要素を 2 個以上足すか、展開(`~`)で他の並びに繋いでください")
        mb = None
        if exprs and self.kind(exprs[-1], {}) == "L" and self.builds(exprs[-1]) is not None:
            k = 0
            for it in self.builds(exprs[-1]):
                ty, x = self.item_info(it)
                if ty == "scalar": k += 1
                else:
                    sz = self.spread_size(x, None, self.builds(exprs[-1]))
                    if sz is None: self.cant("展開(~)する物の長さが見積もれません(字面・定数の範囲・定数端のスライスだけ)"); continue
                    k += sz[0]
            from math import ceil
            mb = ceil(k)
        mbs = None                 # 最上位の式が文字列の連結なら長さの上界
        if exprs and self.kind(exprs[-1], {}) == "S" and self.builds(exprs[-1]) is not None:
            M, t = self.str_cost(self.builds(exprs[-1]), "_.main")
            if t: raise AsmError("内部の誤り: 最上位の連結が実行時の大きさに頼っています")
            from math import ceil
            mbs = ceil(M)
        mbn = None                 # 最上位の式が入れ子の器を組み立てるなら (記述子の数 K, 内容の語数 M)
        if exprs and self.kind(exprs[-1], {}) == "N" and self.builds(exprs[-1]) is not None:
            K, M, t = self.nest_cost(self.builds(exprs[-1]), None)
            if t: raise AsmError("内部の誤り: 最上位の入れ子の組み立てが実行時の大きさに頼っています")
            from math import ceil
            mbn = (K, ceil(M))
        g = FnGen(self, "_.main", [], force_sret=mb is not None or mbn is not None or mbs is not None, force_nest=mbn is not None)
        top = "I"
        g.gen_dyn_init(dynn)
        for i, e in enumerate(exprs):
            tk = self.kind(e, {})
            if i < len(exprs) - 1 or tk == "I": g.gen(e); continue
            top = tk
            if tk == "L" and mb is not None:
                size = (8 * mb + 15) // 16 * 16
                g.emit("sub sp, sp, #%d" % size, "返値スロット(上界 %d 個)。最上位の式が自分で取る" % mb)
                g.emit("mov x8, sp"); g.emit("mov x15, #%d" % mb)
                g.emit("str x8, [x29, #%d]" % g.off(g.sdest)); g.emit("str x15, [x29, #%d]" % g.off(g.slim))
                g.alloca += 1
                g.gen_build(e)
            elif tk == "S" and mbs is not None:
                g.emit_slot((mbs, {}), None, [], CW)
                g.emit("str x8, [x29, #%d]" % g.off(g.sdest)); g.emit("str x15, [x29, #%d]" % g.off(g.slim))
                g.gen_build_str(e)
            elif tk == "N" and mbn is not None:
                g.emit_slot((2 * mbn[0] + 2 + mbn[1], {}), (mbn[0], {}), [])
                g.emit("str x8, [x29, #%d]" % g.off(g.sdest)); g.emit("str x15, [x29, #%d]" % g.off(g.slim))
                g.gen_build_nest(e)
            elif tk in WIDE:
                ee = self.strip(e)
                raw = self.scalar_nest and tk == "L" and ee[0] == "bin" and ee[1] == "'" and self.tail_of(ee) is None and self.slice_of(ee) is None and self.kind(ee[2], {}) == "N"
                if raw: g.ext_raw = True; top = "E"      # 混ざる入れ子の要素そのものの印字: 印のまま渡し、印字がスカラーかリストかを見る
                try: g.load_list(e, "x0", "x1")
                finally: g.ext_raw = False
            elif tk == "R": g.load_rule(e, "x0", "x1", "x2")
            elif tk == "C": g.gen_char_value(e)
        if not exprs: g.emit("mov x0, #0", "トップレベルに式が無い")
        out += g.finish("_.main", export=True) + [""]
        cells = sorted(self.addr_cells)
        close = [(a, b) for a, b in zip(cells, cells[1:]) if b - a < self.addr_cells[a][1]]       # 幅(既定は語幅 8 byte)より近い番地の組は重なる
        if close:
            a, b = close[0]
            self.note_estimate(self.addr_cells[a][0], "幅より近い定数の番地が %d 組あります(例: 0x%x と 0x%x。幅 %d byte)。仕様(value_representation.md §5.4)では `0x…` の幅は target の語幅(aarch64 は 8 バイト)なので重なります。4 バイトの変数・レジスタには幅を書く `4x…` を使います。番地ごとに別のセルとして扱う処理系の古い読みとは答えが変わります" % (len(close), a, b, self.addr_cells[a][1]))
        if STRICT[0] and any(i not in self.part_seen and (o is None or o in self.live) for i, (_n, _t, o) in self.part_trap.items()):             # 罠を出せなかった呼びが残るなら、strict の読みにできない(`!_` の実引数で答えが変わるのを黙って通さない)
            raise StrictRefusal("--strict の読みにできない形があります(コンパイラは既定の読みで解きます):\n  [6] 実引数が `!_` になりうる呼びの後ろに値が続くか、`~` が付く形で、実行時の罠を出せません(asm に関数値は無い)\n      %s" % "; ".join(sorted({t for i, (_n, t, o) in self.part_trap.items() if i not in self.part_seen and (o is None or o in self.live)})[:1]))
        if self.trap_used:
            if self.work_trap: out += [".Ltrap_work:", "\tmov x16, #2  // 作業領域に入らない伸び(原因の印)", "\tb .Ltrap_halt", ""]
            if self.part_used: out += [".Ltrap_part:", "\tmov x16, #3  // --strict: 余った関数が値として残る・後ろの値を受け取る形(asm に関数値は無い。原因の印)", "\tb .Ltrap_halt", ""]
            out += [".Ltrap:", "\tmov x16, #1  // Int の溢れなど(原因の印)", ".Ltrap_halt:", "\twfi  // Int の溢れ(罠)。integer_overflow.md §1", "\tb .Ltrap_halt", ""]
        if self.mixed_nest and False in self.nest_emit_seen: raise AsmError("内部の誤り: 入れ子の取り出しを出したあとで、印のある入れ子が見つかりました(印を外す命令が抜けた取り出しがあります)")
        if self.mixed_nest and self.nest_unsafe:
            raise AsmError("混ざる入れ子の使い方が出せません: " + self.nest_unsafe[0])
        MIXED[0] = self.mixed_nest
        if target == "linux":
            out += linux_start(bool(exprs), bool(exprs) and top == "I" and self.maybe(exprs[-1]), top, self.flagged, getattr(self, "ovf_used", False), self.fnval)
        if self.rodata:
            out += ["\t.section .rodata"]
            for (is_str, vals), label in sorted(self.rodata.items(), key=lambda kv: kv[0][0] is not True):   # 文字列(バイト)を先に、そのあと 8 バイト境界のリストと記述子の表
                if is_str is True: out += (["\t.balign 8"] if self.mixed_nest else ["\t.balign 4"] if CW == 4 else []) + ["%s:" % label, *(["\t.%s " % ("byte" if CW == 1 else "word") + ", ".join(map(str, vals))] if vals else [])]
                elif is_str in ("N", "NS"):                         # 入れ子のリストの記述子の表: 内側ごとに {ptr, len}(16 バイト)。ptr の下位 3 ビットは印(bit0 = スカラー、bit1 = 文字列、bit2 = 入れ子の表)
                    out += ["\t.balign 8", "%s:" % label]
                    for inner in vals:
                        if inner and inner[0] == "s": out += ["\t.quad %s+1" % self.rodata[(False, (inner[1],))], "\t.quad 1"]      # スカラーの要素: ptr の bit0 = 1(ptr − 1 が値のセル)
                        elif inner and inner[0] == "t": out += ["\t.quad %s+2" % self.rodata[(True, tuple(inner[1:]))], "\t.quad %d" % (len(inner) - 1)]      # 文字列の要素: bit1
                        elif inner and inner[0] == "n": out += ["\t.quad %s+4" % inner[1], "\t.quad %d" % inner[2]]      # 入れ子の要素: bit2(ptr は内側の記述子の表、len はその数)
                        else: out += ["\t.quad %s" % self.rodata[(is_str == "NS", tuple(inner))], "\t.quad %d" % len(inner)]
                else: out += ["\t.balign 8", "%s:" % label, *["\t.quad %d" % v for v in vals]]
        if MIXED[0] and top in ("N", "E") and target == "linux":
            out += ["\t.section .bss", "\t.balign 16", "_sign_pn_stack:", "\t.skip 2048"]      # 入れ子の印字の再帰用の専用スタック(x27)
        if self.dyn:
            out += ["\t.section .bss", "\t.balign 8"]
            for nm in self.dyn: out += ["%s:" % dyn_label(nm), "\t.skip 8"]
        return "\n".join(out) + "\n"


_LINUX_PUT_HELPERS = [
            "// x0 の下位 1 バイトを標準出力へ",
            "_sign_putc:",
            "\tsub sp, sp, #16", "\tstrb w0, [sp]",
            "\tmov x0, #1", "\tmov x1, sp", "\tmov x2, #1", "\tmov x8, #64", "\tsvc #0",
            "\tadd sp, sp, #16", "\tret", "",
            "// x0 を 10 進で(改行なし)標準出力へ",
            "_sign_put_int:",
            "\tsub sp, sp, #48", "\tadd x9, sp, #48",
            "\tmov x11, x0", "\tcmp x0, #0", "\tcneg x0, x0, lt", "\tmov x12, #10",
            "1:",
            "\tudiv x13, x0, x12", "\tmsub x14, x13, x12, x0", "\tadd x14, x14, #48",
            "\tsub x9, x9, #1", "\tstrb w14, [x9]", "\tmov x0, x13", "\tcbnz x0, 1b",
            "\ttbz x11, #63, 2f",
            "\tmov w10, #45", "\tsub x9, x9, #1", "\tstrb w10, [x9]",
            "2:",
            "\tadd x2, sp, #48", "\tsub x2, x2, x9", "\tmov x1, x9", "\tmov x0, #1", "\tmov x8, #64", "\tsvc #0",
            "\tadd sp, sp, #48", "\tret", "",
]


_UTF8_PUTC = [
            "// x0(符号位置)を UTF-8 にして標準出力へ(IO 境界は UTF-8。option_ms_schema.md §4.2)",
            "_sign_putc:",
            "\tsub sp, sp, #16",
            "\tcmp x0, #0x80", "\tb.hs 1f",
            "\tstrb w0, [sp]", "\tmov x2, #1", "\tb 9f",
            "1:",
            "\tcmp x0, #0x800", "\tb.hs 2f",
            "\tlsr x9, x0, #6", "\torr w9, w9, #0xC0", "\tstrb w9, [sp]",
            "\tand w10, w0, #0x3F", "\torr w10, w10, #0x80", "\tstrb w10, [sp, #1]", "\tmov x2, #2", "\tb 9f",
            "2:",
            "\tmov x9, #0x10000", "\tcmp x0, x9", "\tb.hs 3f",
            "\tlsr x9, x0, #12", "\torr w9, w9, #0xE0", "\tstrb w9, [sp]",
            "\tlsr x9, x0, #6", "\tand w9, w9, #0x3F", "\torr w9, w9, #0x80", "\tstrb w9, [sp, #1]",
            "\tand w10, w0, #0x3F", "\torr w10, w10, #0x80", "\tstrb w10, [sp, #2]", "\tmov x2, #3", "\tb 9f",
            "3:",
            "\tlsr x9, x0, #18", "\torr w9, w9, #0xF0", "\tstrb w9, [sp]",
            "\tlsr x9, x0, #12", "\tand w9, w9, #0x3F", "\torr w9, w9, #0x80", "\tstrb w9, [sp, #1]",
            "\tlsr x9, x0, #6", "\tand w9, w9, #0x3F", "\torr w9, w9, #0x80", "\tstrb w9, [sp, #2]",
            "\tand w10, w0, #0x3F", "\torr w10, w10, #0x80", "\tstrb w10, [sp, #3]", "\tmov x2, #4",
            "9:",
            "\tmov x0, #1", "\tmov x1, sp", "\tmov x8, #64", "\tsvc #0",
            "\tadd sp, sp, #16", "\tret", "",
]
_UTF32_PRINT_STR = [
            "// 文字列(x0 = 先頭, x1 = 文字数。4 バイトの文字)を `...` で包んで 1 行(UTF-8 で出す)。空(= __)は __",
            "_sign_print_str:",
            "\tmov x22, x30",
            "\tcbnz x1, 1f",
            "\tmov x0, #95", "\tbl _sign_putc", "\tmov x0, #95", "\tbl _sign_putc", "\tmov x0, #10", "\tbl _sign_putc", "\tb 3f",
            "1:",
            "\tmov x19, x0", "\tmov x20, x1", "\tmov x21, #0",
            "\tmov x0, #96", "\tbl _sign_putc",
            "2:",
            "\tldr w0, [x19, x21, lsl #2]", "\tbl _sign_putc", "\tadd x21, x21, #1", "\tcmp x21, x20", "\tb.lo 2b",
            "\tmov x0, #96", "\tbl _sign_putc", "\tmov x0, #10", "\tbl _sign_putc",
            "3:",
            "\tmov x30, x22", "\tret", "",
]
_UTF32_PRINT_CHAR = [
            "// 文字(x0。0 は __)を `\\c` の綴りで 1 行(UTF-8 で出す)",
            "_sign_print_char:",
            "\tmov x22, x30",
            "\tcbnz x0, 1f",
            "\tmov x0, #95", "\tbl _sign_putc", "\tmov x0, #95", "\tbl _sign_putc", "\tmov x0, #10", "\tbl _sign_putc", "\tb 2f",
            "1:",
            "\tmov x19, x0", "\tmov x0, #92", "\tbl _sign_putc", "\tmov x0, x19", "\tbl _sign_putc", "\tmov x0, #10", "\tbl _sign_putc",
            "2:",
            "\tmov x30, x22", "\tret", "",
]


def put_helpers():
    """_sign_putc と _sign_put_int(charset が utf32 なら _sign_putc は UTF-8 に符号化する)。"""
    return (_UTF8_PUTC + _LINUX_PUT_HELPERS[next(i for i, l in enumerate(_LINUX_PUT_HELPERS) if l.startswith("// x0 を 10 進")):]) if CW == 4 else list(_LINUX_PUT_HELPERS)


def linux_start(prints, maybe_unit=False, top="I", flag=False, overflow=False, fn_text=None):
    """単体の Linux 実行ファイル用の足場(この実装だけの選択)。結果を 10 進で 1 行出して exit(0) する。"""
    s = ["\t.global _start", "_start:", "\tbl _.main"]
    if prints: s.append("\tbl _sign_print_" + {"I": "int", "S": "str", "C": "char", "L": "list", "R": "rule", "N": "nested", "E": "elem"}[top])
    if fn_text:                                              # 式の無いファイルの最後の定義が関数: `<fn/N>` と改行を標準出力へ
        txt = fn_text + "\n"
        s += ["\tmov x0, #1", "\tadrp x1, .Lfnval", "\tadd x1, x1, :lo12:.Lfnval", "\tmov x2, #%d" % len(txt), "\tmov x8, #64  // write", "\tsvc #0"]
    s += ["\tmov x0, #0", "\tmov x8, #93  // exit", "\tsvc #0", ""]
    if fn_text: s += ["\t.section .rodata", ".Lfnval:", "\t.byte " + ", ".join(str(ord(c)) for c in fn_text + "\n"), "\t.text", ""]
    if overflow:
        msg = b"sign: work area overflow (result is __)\n"
        msg += b"\0" * (-len(msg) % 8)
        s += ["// 作業領域に入らない累積の伸び: 原因を 1 行 stderr に出す(解析の見積もりが外れた印。結果は __ になる)", "_sign_overflow:", "\tsub sp, sp, #%d" % (len(msg) + 8 + 8)]
        for i in range(0, len(msg), 8):
            v = int.from_bytes(msg[i:i + 8], "little")
            tmp = []
            emit_imm(tmp, "x9", v)
            s += tmp + ["\tstr x9, [sp, #%d]" % i]
        s += ["\tmov x0, #2", "\tmov x1, sp", "\tmov x2, #%d" % len(msg.rstrip(b"\0")), "\tmov x8, #64", "\tsvc #0", "\tadd sp, sp, #%d" % (len(msg) + 16), "\tret", ""]
    if prints and top == "S" and CW == 4:
        s += _UTF32_PRINT_STR + put_helpers()
    elif prints and top == "S":
        s += [
            "// 文字列(x0 = 先頭, x1 = 長さ)を `...` で包んで 1 行。空(= __)は __",
            "_sign_print_str:",
            "\tsub sp, sp, #16",
            "\tcbnz x1, 1f",
            "\tmov w10, #95", "\tstrb w10, [sp]", "\tstrb w10, [sp, #1]", "\tmov w10, #10", "\tstrb w10, [sp, #2]",
            "\tmov x0, #1", "\tmov x1, sp", "\tmov x2, #3", "\tmov x8, #64", "\tsvc #0",
            "\tb 2f",
            "1:",
            "\tmov x9, x0", "\tmov x12, x1",
            "\tmov w10, #96", "\tstrb w10, [sp]",
            "\tmov x0, #1", "\tmov x1, sp", "\tmov x2, #1", "\tmov x8, #64", "\tsvc #0",
            "\tmov x0, #1", "\tmov x1, x9", "\tmov x2, x12", "\tmov x8, #64", "\tsvc #0",
            "\tmov w10, #96", "\tstrb w10, [sp]", "\tmov w10, #10", "\tstrb w10, [sp, #1]",
            "\tmov x0, #1", "\tmov x1, sp", "\tmov x2, #2", "\tmov x8, #64", "\tsvc #0",
            "2:",
            "\tadd sp, sp, #16", "\tret", "",
        ]
    elif prints and top == "L":
        s += [
            "// リスト(x0 = 先頭, x1 = 長さ)を `[10, 20, 30]` の綴りで 1 行。空(= __)は __",
            "_sign_print_list:",
            "\tmov x22, x30",
            *(["\tcmp x1, #1", "\tb.ne 5f", "\tcmp x2, #1", "\tb.ne 5f",
               "\tldr x0, [x0]", "\tbl _sign_put_int", "\tmov x0, #10", "\tbl _sign_putc", "\tmov x30, x22", "\tret",
               "5:"] if flag else []),
            *(["\ttbz x0, #0, 9f", "\tsub x0, x0, #1", "\tldr x0, [x0]", "\tbl _sign_put_int", "\tb 4f", "9:"] if MIXED[0] else []),      # ptr の bit0 = スカラーの要素(混ざる入れ子の要素そのもの)
            "\tmov x19, x0", "\tmov x20, x1", "\tmov x21, #0",
            "\tcbnz x20, 1f",
            "\tmov x0, #95", "\tbl _sign_putc", "\tmov x0, #95", "\tbl _sign_putc", "\tb 4f",
            "1:",
            "\tmov x0, #91", "\tbl _sign_putc",
            "2:",
            "\tcbz x21, 3f",
            "\tmov x0, #44", "\tbl _sign_putc", "\tmov x0, #32", "\tbl _sign_putc",
            "3:",
            "\tldr x0, [x19, x21, lsl #3]", "\tbl _sign_put_int",
            "\tadd x21, x21, #1", "\tcmp x21, x20", "\tb.lo 2b",
            "\tmov x0, #93", "\tbl _sign_putc",
            "4:",
            "\tmov x0, #10", "\tbl _sign_putc",
            "\tmov x30, x22", "\tret", "",
        ]
        s += put_helpers()
    elif prints and top in ("N", "E") and MIXED[0]:
        gb = ["\tldrb w0, [x22, x21]"] if CW == 1 else ["\tldr w0, [x22, x21, lsl #2]"]
        s += [
            "// 作業用の入れ子の印字はスタックを使わず(返値の置き場が捨てられたスタックの下にあるので、上書きしない)、.bss の専用の小さなスタック(x27)で再帰する\n// 入れ子の要素の印字(ptr の下位 3 ビットが印: bit0 = スカラー(ptr − 1 が値のセル)、bit1 = 文字列、bit2 = 入れ子の表、印なし = Int のリスト)。再帰して回る",
            "// _sign_pn_one: x19 = 印つきの ptr、x20 = len の 1 つの要素を出す(x21, x22 を壊す)。_sign_pn_elems: x0 = 記述子の表、x1 = 数 を `[…]` で出す(x19-x25 を保つ)",
            "_sign_pn_one:",
            "\tsub x27, x27, #16", "\tstr x30, [x27]",
            "\tlsr x22, x19, #3", "\tlsl x22, x22, #3",
            "\ttbz x19, #0, 3f",
            "\tldr x0, [x22]", "\tbl _sign_put_int", "\tb 9f",
            "3:",
            "\ttbz x19, #1, 4f",
            "\tmov x0, #96", "\tbl _sign_putc", "\tmov x21, #0",
            "5:",
            "\tcmp x21, x20", "\tb.hs 6f",
            *gb, "\tbl _sign_putc",
            "\tadd x21, x21, #1", "\tb 5b",
            "6:",
            "\tmov x0, #96", "\tbl _sign_putc", "\tb 9f",
            "4:",
            "\ttbz x19, #2, 7f",
            "\tmov x0, x22", "\tmov x1, x20", "\tbl _sign_pn_elems", "\tb 9f",
            "7:",
            "\tmov x0, #91", "\tbl _sign_putc", "\tmov x21, #0",
            "10:",
            "\tcmp x21, x20", "\tb.hs 11f",
            "\tcbz x21, 12f",
            "\tmov x0, #44", "\tbl _sign_putc", "\tmov x0, #32", "\tbl _sign_putc",
            "12:",
            "\tldr x0, [x22, x21, lsl #3]", "\tbl _sign_put_int",
            "\tadd x21, x21, #1", "\tb 10b",
            "11:",
            "\tmov x0, #93", "\tbl _sign_putc",
            "9:",
            "\tldr x30, [x27]", "\tadd x27, x27, #16", "\tret", "",
            "_sign_pn_elems:",
            "\tsub x27, x27, #64",
            "\tstr x30, [x27]", "\tstr x19, [x27, #8]", "\tstr x20, [x27, #16]", "\tstr x21, [x27, #24]",
            "\tstr x22, [x27, #32]", "\tstr x23, [x27, #40]", "\tstr x24, [x27, #48]", "\tstr x25, [x27, #56]",
            "\tmov x24, x0", "\tmov x25, x1", "\tmov x23, #0",
            "\tmov x0, #91", "\tbl _sign_putc",
            "1:",
            "\tcmp x23, x25", "\tb.hs 3f",
            "\tcbz x23, 2f",
            "\tmov x0, #44", "\tbl _sign_putc", "\tmov x0, #32", "\tbl _sign_putc",
            "2:",
            "\tlsl x9, x23, #4", "\tadd x9, x24, x9", "\tldr x19, [x9]", "\tldr x20, [x9, #8]",
            "\tbl _sign_pn_one",
            "\tadd x23, x23, #1", "\tb 1b",
            "3:",
            "\tmov x0, #93", "\tbl _sign_putc",
            "\tldr x30, [x27]", "\tldr x19, [x27, #8]", "\tldr x20, [x27, #16]", "\tldr x21, [x27, #24]",
            "\tldr x22, [x27, #32]", "\tldr x23, [x27, #40]", "\tldr x24, [x27, #48]", "\tldr x25, [x27, #56]",
            "\tadd x27, x27, #64", "\tret", "",
            "// 入れ子(x0 = 記述子の表, x1 = 数)を 1 行。0 個(= __)は __",
            "_sign_print_nested:",
            "\tadrp x27, _sign_pn_stack", "\tadd x27, x27, :lo12:_sign_pn_stack", "\tadd x27, x27, #2048",
            "\tsub x27, x27, #16", "\tstr x30, [x27]",
            "\tcbnz x1, 1f",
            "\tmov x0, #95", "\tbl _sign_putc", "\tmov x0, #95", "\tbl _sign_putc", "\tb 2f",
            "1:",
            "\tbl _sign_pn_elems",
            "2:",
            "\tmov x0, #10", "\tbl _sign_putc",
            "\tldr x30, [x27]", "\tadd x27, x27, #16", "\tret", "",
            "// 入れ子の要素そのもの(x0 = 印つきの ptr, x1 = len)を 1 行。len 0(= __)は __",
            "_sign_print_elem:",
            "\tadrp x27, _sign_pn_stack", "\tadd x27, x27, :lo12:_sign_pn_stack", "\tadd x27, x27, #2048",
            "\tsub x27, x27, #16", "\tstr x30, [x27]",
            "\tmov x19, x0", "\tmov x20, x1",
            "\tcbnz x20, 1f",
            "\tmov x0, #95", "\tbl _sign_putc", "\tmov x0, #95", "\tbl _sign_putc", "\tb 2f",
            "1:",
            "\tbl _sign_pn_one",
            "2:",
            "\tmov x0, #10", "\tbl _sign_putc",
            "\tldr x30, [x27]", "\tadd x27, x27, #16", "\tret", "",
        ]
        s += put_helpers()
    elif prints and top == "N":
        s += [
            "// 入れ子のリスト(x0 = 記述子の表, x1 = 内側のリストの数)を `[[1, 2], [3, 4, 5]]` の綴りで 1 行。0 個(= __)は __",
            "// 記述子は 1 つ 16 バイトの {ptr, len}。レジスタだけで回り、スタックは putc・put_int の各 1 フレーム(書くのは各フレームの上端の数バイト)",
            "_sign_print_nested:",
            "\tmov x22, x30",
            "\tmov x24, x0", "\tmov x25, x1", "\tmov x23, #0",
            "\tcbnz x25, 1f",
            "\tmov x0, #95", "\tbl _sign_putc", "\tmov x0, #95", "\tbl _sign_putc", "\tb 8f",
            "1:",
            "\tmov x0, #91", "\tbl _sign_putc",
            "2:",
            "\tcbz x23, 3f",
            "\tmov x0, #44", "\tbl _sign_putc", "\tmov x0, #32", "\tbl _sign_putc",
            "3:",
            "\tlsl x9, x23, #4", "\tadd x9, x24, x9", "\tldr x19, [x9]", "\tldr x20, [x9, #8]", "\tmov x21, #0",
            *(["\ttbz x19, #0, 9f", "\tsub x19, x19, #1", "\tldr x0, [x19]", "\tbl _sign_put_int", "\tb 7f", "9:"] if MIXED[0] else []),      # スカラーの要素(ptr の bit0): 数だけ出す
            "\tmov x0, #91", "\tbl _sign_putc",
            "\tcbz x20, 6f",
            "4:",
            "\tcbz x21, 5f",
            "\tmov x0, #44", "\tbl _sign_putc", "\tmov x0, #32", "\tbl _sign_putc",
            "5:",
            "\tldr x0, [x19, x21, lsl #3]", "\tbl _sign_put_int",
            "\tadd x21, x21, #1", "\tcmp x21, x20", "\tb.lo 4b",
            "6:",
            "\tmov x0, #93", "\tbl _sign_putc",
            "7:",
            "\tadd x23, x23, #1", "\tcmp x23, x25", "\tb.lo 2b",
            "\tmov x0, #93", "\tbl _sign_putc",
            "8:",
            "\tmov x0, #10", "\tbl _sign_putc",
            "\tmov x30, x22", "\tret", "",
        ]
        s += put_helpers()
    elif prints and top == "R":
        s += [
            "// 規則(x0 = start, x1 = step, x2 = end)を `[10, 20, 30]` の綴りで 1 行。0 個は `[]`",
            "_sign_print_rule:",
            "\tmov x22, x30",
            "\tmov x19, x0", "\tmov x20, x1", "\tmov x21, x2",
            "\tsub x23, x21, x19", "\tmov x24, #1", "\tcbz x23, 6f",
            "\teor x13, x23, x20", "\tmov x24, #0", "\ttbnz x13, #63, 6f",
            "\tsdiv x24, x23, x20", "\tadd x24, x24, #1",
            "6:",
            "\tmov x0, #91", "\tbl _sign_putc",
            "\tmov x25, #0", "\tcbz x24, 4f",
            "2:",
            "\tcbz x25, 3f",
            "\tmov x0, #44", "\tbl _sign_putc", "\tmov x0, #32", "\tbl _sign_putc",
            "3:",
            "\tmul x13, x25, x20", "\tadd x0, x19, x13", "\tbl _sign_put_int",
            "\tadd x25, x25, #1", "\tcmp x25, x24", "\tb.lo 2b",
            "4:",
            "\tmov x0, #93", "\tbl _sign_putc", "\tmov x0, #10", "\tbl _sign_putc",
            "\tmov x30, x22", "\tret", "",
        ]
        s += put_helpers()
    elif prints and top == "C" and CW == 4:
        s += _UTF32_PRINT_CHAR + put_helpers()
    elif prints and top == "C":
        s += [
            "// 文字(x0。0 は __)を `\\c` の綴りで 1 行",
            "_sign_print_char:",
            "\tsub sp, sp, #16",
            "\tcbnz x0, 1f",
            "\tmov w10, #95", "\tstrb w10, [sp]", "\tstrb w10, [sp, #1]", "\tmov w10, #10", "\tstrb w10, [sp, #2]", "\tmov x2, #3", "\tb 2f",
            "1:",
            "\tmov w10, #92", "\tstrb w10, [sp]", "\tstrb w0, [sp, #1]", "\tmov w10, #10", "\tstrb w10, [sp, #2]", "\tmov x2, #3",
            "2:",
            "\tmov x0, #1", "\tmov x1, sp", "\tmov x8, #64", "\tsvc #0",
            "\tadd sp, sp, #16", "\tret", "",
        ]
    elif prints:
        s += [
            "// x0 を 10 進で標準出力へ(負なら先頭に -)、あとに改行",
            "_sign_print_int:",
            *(["\tmovz x13, #0x8000, lsl #48  // __",
               "\tcmp x0, x13",
               "\tb.ne 3f",
               "\tsub sp, sp, #16",
               "\tmov w10, #95  // '_'",
               "\tstrb w10, [sp]",
               "\tstrb w10, [sp, #1]",
               "\tmov w10, #10",
               "\tstrb w10, [sp, #2]",
               "\tmov x0, #1",
               "\tmov x1, sp",
               "\tmov x2, #3",
               "\tmov x8, #64  // write",
               "\tsvc #0",
               "\tadd sp, sp, #16",
               "\tret",
               "3:"] if maybe_unit else []),
            "\tsub sp, sp, #48",
            "\tadd x9, sp, #47",
            "\tmov w10, #10",
            "\tstrb w10, [x9]  // 改行",
            "\tmov x11, x0",
            "\tcmp x0, #0",
            "\tcneg x0, x0, lt  // 絶対値(INT64_MIN は値でないので溢れない)",
            "\tmov x12, #10",
            "1:",
            "\tudiv x13, x0, x12",
            "\tmsub x14, x13, x12, x0",
            "\tadd x14, x14, #48",
            "\tsub x9, x9, #1",
            "\tstrb w14, [x9]",
            "\tmov x0, x13",
            "\tcbnz x0, 1b",
            "\ttbz x11, #63, 2f",
            "\tmov w10, #45  // '-'",
            "\tsub x9, x9, #1",
            "\tstrb w10, [x9]",
            "2:",
            "\tadd x2, sp, #48",
            "\tsub x2, x2, x9  // 長さ",
            "\tmov x1, x9",
            "\tmov x0, #1",
            "\tmov x8, #64  // write",
            "\tsvc #0",
            "\tadd sp, sp, #48",
            "\tret",
            "",
        ]
    return s


LAST_INFOS = []          # 直前の generate で『見積もりで通した』関数(information)。[(関数, 言い分)]

REALDB = [False]
def sign_asmpar_light():
    import sign_asmpar
    return int(sign_asmpar.LIGHT)

SPEC = [False]               # --par-spec: 投機の並列(sign_asmpar.py)
SPEC_LOOK = [1]              # --spec-look=N: 行の並びで、N 行先まで値を先に走らせる(1 = 今の行だけ)
SPEC_ABORT = [False]         # --spec-abort: 捨てられた投機を再帰関数の入口で止める(実機では全体が遅くなったので既定は切)
PAR = [None]                  # --par=N: 並列実行(N = スレッドの数。sign_asmpar.py)。None なら使わない
REALDEV = [False]            # --real-dev: 装置の番地(0x9000000 以上)への # と @ を、実機の装置の中継(sign_realdev.py)へ回す

GFXSZ = [(64, 32)]
def generate(nodes, target="bare", source=None, charset="ascii", real_dev=False, fps=60, real_db=False, display=(64, 32), par=None, par_spec=False):
    global LAST_INFOS, CW
    PAR[0] = par if (par and par > 1) else None
    SPEC[0] = bool(par_spec and PAR[0] is not None)
    if PAR[0] is not None and target != "linux": raise AsmError("--par は --target=linux のときだけ使えます(スレッドを Linux の clone で作るため)")
    GFXSZ[0] = tuple(display)
    CW = 4 if charset == "utf32" else 1
    REALDEV[0] = bool(real_dev or real_db); REALDB[0] = bool(real_db); real_dev = REALDEV[0]
    if NEON[0]:
        import sign_neon
        if sign_neon.main_needs_float(nodes):
            if target not in ("bare", "linux"): raise AsmError("Float / Vector(NEON)は --target=bare(結果は v0 / d0)か --target=linux(結果を書いて exit)のときだけ出せます")
            if real_dev: raise AsmError("Float / Vector(NEON)は --real-dev と一緒には使えません")
            try: text = sign_neon.generate(nodes, target=target)
            except sign_neon.NeonError as e: raise AsmError("NEON: %s" % e)
            LAST_INFOS = []; LAST_LINT[:] = []
            if LINT[0]:
                import sign_lint
                LAST_LINT.extend(sign_lint.lint(text))
            return text
    if real_dev: nodes = add_console_driver(nodes, fps)
    p = Program(nodes); text = p.generate(target, source); LAST_INFOS = list(p.infos)
    if real_dev:
        if target != "linux": raise AsmError("--real-dev は --target=linux のときだけ使えます(装置を Linux のシステムコールへ置き換えるため)")
        text = add_realdev(text)
    if PAR[0] is not None and (p.par_used or p.spec_used): text = add_par(text, p)
    LAST_LINT[:] = []
    if LINT[0]:
        import sign_lint
        LAST_LINT.extend(sign_lint.lint(text))
    return text


def add_par(text, p):
    """--par: 包み・実行環境(スレッドの池・待ち行列・合流)・.bss を足し、起動で主スレッドの TLS を作り、終了を exit_group にする。"""
    import sign_asmpar
    el = p.par_elig(); body = []
    for f in sorted(p.par_used): body += sign_asmpar.wrapper(f, symbol_of(f), sign_asmpar.nwords(p.pkind[f]))
    spec = bool(p.spec_used)
    clones = []
    if spec and SPEC_ABORT[0]:      # 再帰する関数と、それを(間接にも)呼ぶ関数が複製の対象(呼ぶ側も複製しないと元の再帰へ入ってしまう)
        el_ = p.spec_elig(); cs_ = {f for f, meas in el_.items() if meas is not None}; cal_ = {}
        for f in el_:
            acc = set(); sign_asmpar._callees(p.bodies[f], set(el_), acc); cal_[f] = acc
        grow = True
        while grow:
            grow = False
            for f in el_:
                if f not in cs_ and cal_[f] & cs_: cs_.add(f); grow = True
        clones = sorted(cs_)
    csym = {symbol_of(f) for f in clones}
    for f in sorted(p.spec_used): body += sign_asmpar.spec_wrapper(f, symbol_of(f), sign_asmpar.nwords(p.pkind[f]), (symbol_of(f) + "__sp") if symbol_of(f) in csym else None)
    pwsym = set()
    for f in sorted(p.par_used):                      # 投機専用の複製を呼ぶ並列の包み(投機の中で合流が自分で走らせる左の半分も、確認つきの複製へ入る)
        if symbol_of(f) in csym:
            pwsym.add(symbol_of(f))
            body += [l.replace("_sign_pw_%s:" % symbol_of(f), "_sign_pw_%s__sp:" % symbol_of(f)).replace("\tbl %s" % symbol_of(f), "\tbl %s__sp" % symbol_of(f)) for l in sign_asmpar.wrapper(f, symbol_of(f), sign_asmpar.nwords(p.pkind[f]))]
    body = ["\t.text"] + body + sign_asmpar.runtime(PAR[0], spec)
    if spec:        # 罠は、投機の中なら巻き戻す(外なら今までどおり止まる)
        chk = ["\tmrs x16, tpidr_el0", "\tldr x16, [x16, #16]", "\tcbnz x16, _sign_spec_rollback"]
        text = text.replace("\n.Ltrap:\n", "\n.Ltrap:\n" + "\n".join(chk) + "\n", 1).replace("\n.Ltrap_work:\n", "\n.Ltrap_work:\n" + "\n".join(chk) + "\n", 1)
    for f in clones:                 # 投機専用の複製 <名>__sp: 入口で捨てられた印を見て巻き戻して抜ける(通常の呼び出しは元の関数なので遅くならない。x16・x9 だけ使う。x17・x8・x15 は引数)
        sy = symbol_of(f); st = text.find("\n%s:\n" % sy)
        if st < 0: continue
        en = len(text)
        for mm in re.finditer(r"\n(?!\.L)([A-Za-z_][\w.]*):", text[st + 1:]):
            if mm.group(1) != sy: en = st + 1 + mm.start() + 1; break
        fb = text[st + 1:en]
        locs = set(re.findall(r"^(\.L\w+):", fb, re.M))
        fb = re.sub(r"(?<![\w.])(\.L\w+)(?!\w)", lambda m: m.group(1) + "__sp" if m.group(1) in locs else m.group(1), fb)
        fb = re.sub(r"\bbl\s+(\w+)\b", lambda m: m.group(0) + "__sp" if m.group(1) in csym else m.group(0), fb)
        fb = re.sub(r"\b_sign_pw_(\w+?)\b(?!__sp)", lambda m: m.group(0) + "__sp" if m.group(1) in pwsym else m.group(0), fb)
        fb = re.sub(r"(?m)^%s:$" % re.escape(sy), "%s__sp:" % sy, fb)
        chk = [] if p.spec_elig()[f] is None else ["\tmrs x16, tpidr_el0", "\tldr x16, [x16, #16]", "\tcbz x16, _sign_sa_%s" % sy, "\tldr x9, [x16, #128]", "\tcbnz x9, _sign_spec_rollback", "_sign_sa_%s:" % sy]
        lines = fb.split("\n"); j = max(i for i, l in enumerate(lines) if l == "%s__sp:" % sy)
        fb = "\n".join(lines[:j + 1] + chk + lines[j + 1:])
        text = text[:en] + fb + ("" if fb.endswith("\n") else "\n") + text[en:]
    i = text.find("\t.section")
    text = text[:i] + "\n".join(body) + "\n" + text[i:] if i >= 0 else text.rstrip("\n") + "\n" + "\n".join(body) + "\n"
    text = text.replace("\n_start:\n", "\n_start:\n\tbl _sign_par_boot\n", 1)
    text = text.replace("\tmov x8, #93  // exit", "\tmov x8, #94  // exit_group(労働者もまとめて終える)")
    return text.rstrip("\n") + "\n" + "\n".join(sign_asmpar.bss(PAR[0], p.par_nsites, spec)) + "\n"


def add_console_driver(nodes, fps):
    """--real-dev: `tick` を定義していて、最上位に式の無いファイルは、ゲーム機(sign_console.py)と同じ周期で動かす。
    init を 1 回、そのあと 1 こまごとに『鳴ったアラームを on_timer へ(1 こまに 16 個まで)→ tick』、残りの時間を待つ。tick か on_timer が -1 を返せば終わり。
    (入力の出来事・描画・窓は無い。on_key などは呼ばれない。)中継ルーチンの DUE(0x9200018 の読み)で、鳴ったアラームの番号を取る。"""
    names = {n[1] for n in nodes if n[0] == "def"}
    if "tick" not in names or any(n[0] not in ("def", "importspread", "import") for n in nodes): return nodes
    import sign_interp
    period = max(1, 1000 // max(1, fps))
    src = ["zz_con_period : %d" % period]
    if "on_timer" in names:
        src += ["zz_con_dispatch : id n ?", "\tid < 0 : 0", "\tn <= 0 : 0", "\t(on_timer id) = -1 : -1", "\tzz_con_dispatch (@0x9200018) (n - 1)"]
    else:
        src += ["zz_con_dispatch : id n ? 0"]
    src += ["zz_con_left : t0 ?", "\tzz_con_period - ((@0x9200000) - t0) < 1 : 1", "\tzz_con_period - ((@0x9200000) - t0)",
            "zz_con_loop : z ? zz_con_step (@0x9200000)",
            "zz_con_step : t0 ?", "\t(zz_con_dispatch (@0x9200018) 16) = -1 : 0", "\t(tick 0) = -1 : 0", "\tzz_con_loop (0x9200004 # (zz_con_left t0))",
            "zz_con_main : z ? zz_con_loop (%s)" % ("init 0" if "init" in names else "0"),
            "zz_con_main 0", ""]
    return list(nodes) + list(sign_interp.parse_source("\n".join(src)))


def add_realdev(text):
    import sign_realdev
    putc = list(_UTF8_PUTC if CW == 4 else _LINUX_PUT_HELPERS[:next(i for i, l in enumerate(_LINUX_PUT_HELPERS) if l.startswith("// x0 を 10 進"))])
    putc = [l.replace("_sign_putc", "_sign_dev_putc") for l in putc if not l.startswith("//")]
    ro, bss = sign_realdev.data_lines(REALDB[0], GFXSZ[0])
    body = "\n".join(sign_realdev.shim(putc, CW, REALDB[0], GFXSZ[0])) + "\n"
    i = text.find("\t.section .rodata")
    text = text[:i] + body + text[i:] if i >= 0 else text + body
    text = text.replace("_start:\n\tbl _.main", "_start:\n\tbl _sign_dev_map\n\tbl _.main", 1)          # 作業メモリを確保してから始める
    return text.rstrip("\n") + "\n" + "\n".join(ro + bss) + "\n"


USAGE = """使い方: python3 sign.py --asm 〈プログラム.sn〉 [--target=bare|linux] [--charset=ascii|utf32] [--strict] [--no-opt] [--no-peephole] [--no-lint] [--no-fuse] [--no-share] [--no-hoist] [--no-scalar] [--no-neon] [--real-dev] [--display=幅x高さ] [-o 出力.s] [--elf=出力ファイル]

  実行せずに、AArch64 のアセンブリ(GNU as の綴り)を標準出力(か -o の先)へ書く。
  --target=bare   既定。`_.main` までを出す(設計者のターゲット aarch64_rpi など向け。起動部は別)
  --target=linux  Linux 用の起動部 `_start` と、結果を 10 進で 1 行出して exit する足場を付ける(単体の実行ファイル用)
  --charset=utf32 メモリ上の Char を 4 バイトにする(option.ms の charset。既定は ascii = 1 バイト。省略時は同じフォルダの option.ms を見る)。IO 境界は UTF-8
  --par-site-light (--par の調整用)前の既定。軽さを呼び出し位置ごとに数え、3 回続けて軽いと以後ずっと直列にする(境の既定 1000)。今の既定は、軽かった枠の積みの深さをスレッドごとに覚える方式(境の既定 100)
  --par-spin=N    (--par の調整用)join が走行中の仕事を待つとき、眠る前に N 回状態を見に行く(既定 0 = 見ない。軽い仕事の往復を減らす)
  --par-light=N   (--par の調整用)軽い仕事の境の時計の数(既定 100。Pi 4 の cntvct は 54 MHz なので約 2 マイクロ秒、Pi 3 A+ は 19.2 MHz なので約 5 マイクロ秒)
  --spec-look=N   (--par-spec に足す。実験用)行の並び `c1 : v1 / c2 : v2 / …` で、N 行先までの値の呼び出しも、今の条件を調べる間に先に走らせる。既定は 1(今の行だけ)
  --spec-abort    (--par-spec に足す。実験用)捨てられた投機を、再帰する関数の入口で止める。実機(Pi 3 A+)では入口の確認で全体が遅くなったので既定は切
  --par-spec      (--par と一緒に。linux 用)投機の並列: `l | r`・`l & r`・`cond : v` の右・値が、必ず終わると言える純粋な整数関数の呼び出しなら、左・条件を調べる間に先に別のスレッドで走らせる。
                  答えが要らなければ捨て、投機が罠(溢れ)にぶつかれば巻き戻して印だけ付け、答えが要るときだけ親が直列で計算し直す(答えは直列と同じ)。
                  限界: 積みの深さは証明できない(労働者の積みは 64 MiB。主の積みより小さくはならないが、ulimit -s unlimited なら主のほうが深く行ける)。--par=N 無しなら 4 本
  --par[=N]       (linux 用)純粋な整数関数の兄弟の呼び出し(`f a + g b`)を N 本(既定 4)のスレッドに分ける。値は変わらない(sign_asmpar.py)
  --real-dev      (linux 用)装置の番地への # と @ を、実機の Linux の装置(/dev/i2c-N・/dev/gpiochip0・時計・標準入出力)の操作に置き換える。実機では未実行
  --real-db       (--real-dev に足す)SQLite 装置(0x9A00000)も libsqlite3 で動かす。--pi-bundle=DIR で prog.s・sign_db.c・build.sh を作る(Pi で gcc が要る)。--elf とは併せられない
  --fps=N         (--real-dev で tick を持つファイル)1 秒に N こま(既定 60)。tick・init・on_timer をゲーム機と同じ周期で回す
  --strict        別の道: --strict(仕様の読み)と同じ答えになるコードを出す(構文木を書き換えてから出す。既定の道は変えない)。直す形は4つ: `x ' 名前`(`__`)・逆適用 `c f`(`c`)・最後でない行の値が `!_` なら次の行へ・本体の `y : 2` は条件の行。書き換えられない形は断る。累積に `__` を足す形などは、既定と同じく出せない
  --no-estimate   上界を見積もりで通さない(既定は仕様どおり、証明できない上界も見積もり+実行時の確認で通し、information に名指しする)
  --elf=FILE      linux の足場つきで組んでリンクし、AArch64 の静的な ELF を FILE に書く(clang と ld.lld が要る。実行は Raspberry Pi など AArch64 の Linux で)
出せる範囲は整数・比較・分岐・関数(再帰を含む)と、Int のリスト・ASCII の文字列・文字(取り出し・長さ・比較・関数へ渡す・関数から返す・最後の式として印字)だけ。範囲(端が定数なら .rodata のリスト、実行時の値なら規則 {start, step, end} の値渡し)・スライス(端が非負の定数)・連結(`xs~ ys~`)・入れ子のリスト(`(1 2) (3 4 5)`、`xs ys`。arena)・文字列の連結(`a b`)も出せる。返す器の大きさは、上界 konst + Σ coef×||器|| を呼ぶ側が実行時に計算して置き場を取る。書き込み `a # v`(Int の番地と値。64 ビット、答えは番地)、9 個以上の引数(9 語目からスタック渡し)も出せる。出せない形は、理由を言って終わる(終了コード 1)。"""


STRICT = [False]
def _fold_minmax(n):
    """--strict --asm: 順序の比べの畳み `[>] a b …`(`[>=]` は max、`[<]`・`[<=]` は min。sign_interp.fold_cmp)を、
    `((a op b) | b) op c) | c …` に書き直す(`a op b` は成り立てば a、外れれば `!_`。`|` は `!_` なら右)。
    実引数が 2 つ以上で、全部が字面の整数・名前(2 度書くので、計算を含む形は対象外)のときだけ。当たらなければ None"""
    if not (isinstance(n, tuple) and n and n[0] == "seq" and len(n[1]) >= 3): return None
    h = n[1][0]
    if not (isinstance(h, tuple) and h[0] == "sec" and len(h) >= 4 and h[1] == "fold" and h[2] in (">", "<", ">=", "<=") and h[3] is None and not (len(h) > 4 and h[4])): return None
    def simple(a):
        while isinstance(a, tuple) and a and a[0] == "block": a = a[1]
        if isinstance(a, tuple) and a and a[0] == "neg": a = a[1]
        return isinstance(a, tuple) and a and ((a[0] == "id" and a[1] != "__") or (a[0] == "lit" and isinstance(a[1], int) and not isinstance(a[1], bool)))   # `__` は畳みで飛ばされる(`[>=] 7 __` は 7)ので書き直せない
    args = n[1][1:]
    if not all(simple(a) for a in args): return None
    e = args[0]
    for x in args[1:]: e = ("bin", "|", ("cmp", [e, x], [h[2]]), x)
    return ("block", e)

# strict の形の規則の表(番号 → 名前・書き換える所・断る所)。二つの関数は直列: strict_rewrite が書き換え、その結果に strict_divergences をかけて残りを断る。
# 形が両方をすり抜けない(書き換えるか断るかのどちらかに必ず当たる)ことは test_strict_rules.py が見本で守る。
STRICT_RULES = {
    1: ("鍵が名前 `x ' k`(R64)",         "strict_rewrite: 鍵を `__` に",                 "strict_divergences: 書き換え残り"),
    2: ("逆適用 `c f`",                  "strict_rewrite: `c` だけに",                   "strict_divergences: 書き換え残り(`c f x` など)"),
    3: ("行の値が `!_` になりうる(R128)", "strict_rewrite: `(c & v) | 次の行以降`",       "strict_divergences: 静的に見えない形"),
    4: ("行の左が名前だけ(R128)",        "strict_rewrite: `(y | y)` に",                 "strict_divergences: 仮引数でもファイルの値でもない名前"),
    5: ("`!=` の void",                  "strict_rewrite: `(a==a)&(b==b)&(a!=b)` に",    "(断りなし)"),
    6: ("順序・等しさの畳み",            "strict_rewrite: 最大・最小に(`__` なしの整数・名前だけ)", "strict_divergences: それ以外の畳み(`__`・計算・`==`/`=` の void 混じり)"),
}

def _fold_eq_simple(n):
    """`[==] a b …`・`[=] a b …` で、実引数が字面の整数・名前(`__` でない)だけ。void が混ざらないので既定の読みと答えが同じ。"""
    if not (isinstance(n, tuple) and n and n[0] == "seq" and len(n[1]) >= 2): return False
    h = n[1][0]
    if not (isinstance(h, tuple) and h[0] == "sec" and len(h) >= 4 and h[1] == "fold" and h[2] in ("==", "=") and h[3] is None and not (len(h) > 4 and h[4])): return False
    def simple(a):
        while isinstance(a, tuple) and a and a[0] == "block": a = a[1]
        if isinstance(a, tuple) and a and a[0] == "neg": a = a[1]
        return isinstance(a, tuple) and a and ((a[0] == "id" and a[1] != "__") or (a[0] == "lit" and isinstance(a[1], int) and not isinstance(a[1], bool)))
    return all(simple(a) for a in n[1][1:])

def strict_divergences(tree):
    """--strict --asm(2026-11-18): コンパイラは既定の読みで解く。--strict(仕様の読み)と答えが分かれる次の6つの形に当たったら、出さずに名指しで断る。
      1. `x ' k` の鍵 k が名前(strict は欄の名前で `!_`、既定は名前の値で引く。仕様 R64)
      2. 逆適用 `c f`(値の後ろに関数を置く。strict は値のままで関数は余り、既定は f c)
      3. 最後でない行の値が `!_` になりうる形(strict は消えて次の行へ進み、既定はその `!_` を返して止まる。R128)。
         静的に見えるのは `/`・`%`(割る数が 0 でない字面のときを除く)・比べ・`&`・`|`・`;`・書いた `__` を値に含む形だけ(呼び出しの答えまでは見ない)
      4. 本体の行の左が名前だけの `y : 2`(strict は条件の行、既定は局所の定義。R128)
      5. 順序の比べの畳み `[>]`・`[<]`・`[>=]`・`[<=]`(strict は偽でも右の数を返す)。実引数が 2 つ以上で字面の整数・名前だけの形は strict_rewrite が最大・最小に書き直すので断らない(`_fold_minmax`)。器 1 個の畳み `[>] xs`・計算を含む実引数・名前に束ねた `[>]` は断る
      6. 計算で `!_` になりうる実引数を持つ、関数の呼び(strict は実引数が消えて関数が余る。asm は呼び全体が `!_`)。木の段ではなく、コード生成の終わり(`Program.strict_call_check`)で、末尾の位置・余った関数を返しうる関数の不動点・範囲内の証明を使って調べる(`StrictRefusal`)
    戻り値: [(番号, 説明, 式の綴り)]"""
    import sign_interp as SI
    found = []; handled = set()
    funcs = {n[1] for n in tree if isinstance(n, tuple) and n and n[0] == "def" and isinstance(n[2], tuple) and n[2][0] == "lam"}
    vals = {n[1] for n in tree if isinstance(n, tuple) and n and n[0] == "def" and not (isinstance(n[2], tuple) and n[2][0] == "lam")}
    def src(n):
        try: return SI.node_src(n)
        except Exception: return repr(n)[:60]
    def unwrap(n):
        while isinstance(n, tuple) and n and n[0] == "block": n = n[1]
        return n
    arity = {n[1]: len(n[2][1]) for n in tree if isinstance(n, tuple) and n and n[0] == "def" and isinstance(n[2], tuple) and n[2][0] == "lam"}
    head_ids = set()                                             # 後ろに実引数が続く式の頭にある、かっこの中の呼び
    def mark(n):
        if not isinstance(n, tuple) or not n: return
        if n[0] == "seq" and len(n[1]) >= 2:
            h = n[1][0]
            if isinstance(h, tuple) and h and h[0] == "block":
                u = unwrap(h)
                if isinstance(u, tuple) and u and u[0] == "seq": head_ids.add(id(u))
        for y in n[1:]:
            if isinstance(y, tuple): mark(y)
            elif isinstance(y, list):
                for z in y:
                    if isinstance(z, tuple): mark(z)
    for n in tree: mark(n)
    def maybe_void(n):
        stack = [n]
        while stack:
            x = stack.pop()
            if not isinstance(x, tuple) or not x: continue
            if x[0] == "lam": continue
            if x[0] == "hole" or (x[0] == "not" and x[1] == ("hole",)): return True
            if x[0] == "cmp": return True
            if x[0] == "bin" and len(x) == 4:
                if x[1] in ("&", "|", ";"): return True
                if x[1] in ("/", "%") and not (x[3][0] == "lit" and x[3][1] != 0): return True
            for y in x[1:]:
                if isinstance(y, tuple): stack.append(y)
                elif isinstance(y, list): stack.extend(z for z in y if isinstance(z, tuple))
        return False
    def has_index(n):
        stack = [n]
        while stack:
            x = stack.pop()
            if not isinstance(x, tuple) or not x: continue
            if x[0] == "lam": continue
            if x[0] == "bin" and len(x) == 4 and x[1] == "'": return True
            for y in x[1:]:
                if isinstance(y, tuple): stack.append(y)
                elif isinstance(y, list): stack.extend(z for z in y if isinstance(z, tuple))
        return False
    def walk(n, params):
        if not isinstance(n, tuple) or not n: return
        k = n[0]
        if k == "lam":
            ps = set(params) | {q[1] for q in n[1] if isinstance(q, tuple) and len(q) > 1 and isinstance(q[1], str)}
            walk(n[2], ps); return
        if k == "bin" and len(n) == 4 and n[1] in ("'", "@"):
            key = unwrap(n[3] if n[1] == "'" else n[2])
            if isinstance(key, tuple) and key and key[0] == "post" and key[1] == "~": key = unwrap(key[2])
            if isinstance(key, tuple) and key and key[0] == "id": found.append((1, "`' ` の鍵が名前 `%s`(strict は欄の名前で `!_`、既定は名前の値で引く。仕様 R64)" % key[1], src(n)))
        if k == "seq" and (_fold_minmax(n) is not None or _fold_eq_simple(n)): handled.add(id(n[1][0]))      # 5. strict_rewrite が最大・最小に書き直す形(`==`・`=` の畳みは void が混ざらない形だけ通す)
        if k == "sec" and len(n) >= 3 and n[1] == "fold" and n[2] in (">", "<", ">=", "<=", "==", "=") and id(n) not in handled:
            found.append((5, "順序の比べの畳み `[%s]`(strict は偽でも右の数を返す `[>] 3 5` が 5。既定は `!_`)" % n[2], src(n)))
        if k == "seq" and len(n[1]) >= 2:
            h = n[1][0]
            if isinstance(h, tuple) and (h[0] == "lit" or (h[0] == "id" and (h[1] in params or h[1] in vals) and h[1] not in funcs)):
                for m in n[1][1:]:
                    if isinstance(m, tuple) and m[0] == "id" and m[1] in funcs and m[1] not in params:
                        found.append((2, "逆適用 `%s %s`(strict は値のままで関数 `%s` は余り、既定は `%s %s` を当てる)" % (src(h), m[1], m[1], m[1], src(h)), src(n))); break
        if k == "cases":
            rows = n[1]
            for i, (cond, expr) in enumerate(rows):
                if cond is not None and isinstance(cond, tuple) and cond[0] == "id":
                    found.append((4, "行の左が名前だけ `%s : …`(strict は条件の行、既定は局所の定義。R128)" % cond[1], src(cond) + " : " + src(expr)))
                if i < len(rows) - 1 and cond is not None and maybe_void(expr):
                    found.append((3, "最後でない行の値が `!_` になりうる(strict は消えて次の行へ進み、既定は `!_` を返して止まる。R128)", src(cond) + " : " + src(expr)))
        for y in n[1:]:
            if isinstance(y, tuple): walk(y, params)
            elif isinstance(y, list):
                for z in y:
                    if isinstance(z, tuple):
                        if len(z) == 2 and k == "cases": walk(z[0], params); walk(z[1], params)
                        else: walk(z, params)
    for n in tree: walk(n, set())
    seen = set(); out = []
    for f in found:
        if f not in seen: seen.add(f); out.append(f)
    return out

def strict_rewrite(tree):
    """--strict --asm(2026-11-18): 別の道。既定の読みで解くコンパイラに、--strict(仕様の読み)の答えを出させるため、
    構文木を strict の読みと同じ答えになる形へ書き換えてから generate に渡す(既定の道は変えない)。
      1. `x ' k`・`k @ x` の鍵 k が名前 → `__`(strict は欄の名前で `!_`。R64)
      2. 逆適用 `c f`(値の後ろに関数の名前1つだけ) → `c`(関数は余りで落ちる)
      3. 最後でない行 `c : v` の値 v が `!_` になりうる(呼び出し・比べ・`/` `%` など) → その行から後ろを `(c & v) | (次の行以降)` に(strict は `!_` なら次の行へ進む。R128)
      6. 順序の比べの畳み `[>] a b …`(実引数 2 つ以上、字面の整数か名前だけ)→ `((a op b) | b) op c) | c …`(strict は max/min。`a op b` は成り立てば a、外れれば `!_`)
      5. `a != b`・`a !== b` → `(a == a) & (b == b) & (a != b)`(どちらかが `!_` なら `!_`。既定の道の `!=` は void を「違う」と読む)
      4. 行の左が名前だけ `y : …`(y は仮引数かファイルの値) → 左を `(y | y)` に(条件の行と読ませる。R128)。仮引数でもファイルの定義でもない名前は直せない
    戻り値: (書き換えた木, 直せなかった形の [(番号, 説明, 式の綴り)])"""
    import sign_interp as SI, os
    off = set(os.environ.get("SIGN_NOPATCH", "").split(","))                  # 計測用: 補正の番号を切る(例 SIGN_NOPATCH=3,5)。既定は全部入れる
    rest = []
    funcs = {n[1] for n in tree if isinstance(n, tuple) and n and n[0] == "def" and isinstance(n[2], tuple) and n[2][0] == "lam"}
    vals = {n[1] for n in tree if isinstance(n, tuple) and n and n[0] == "def" and not (isinstance(n[2], tuple) and n[2][0] == "lam")}
    def src(n):
        try: return SI.node_src(n)
        except Exception: return repr(n)[:60]
    def unwrap(n):
        while isinstance(n, tuple) and n and n[0] == "block": n = n[1]
        return n
    def has_call(n):
        stack = [n]
        while stack:
            x = stack.pop()
            if not isinstance(x, tuple) or not x: continue
            if x[0] == "lam": continue
            if x[0] == "seq" and x[1] and isinstance(x[1][0], tuple) and x[1][0][0] == "id" and x[1][0][1] in funcs: return True
            for y in x[1:]:
                if isinstance(y, tuple): stack.append(y)
                elif isinstance(y, list): stack.extend(z for z in y if isinstance(z, tuple))
        return False
    def maybe_void(n):
        stack = [n]
        while stack:
            x = stack.pop()
            if not isinstance(x, tuple) or not x: continue
            if x[0] == "lam": continue
            if x[0] == "id" and x[1] == "__": return True
            if x[0] == "cmp": return True
            if x[0] == "bin" and len(x) == 4:
                if x[1] in ("&", "|", ";"): return True
                if x[1] in ("/", "%") and not (x[3][0] == "lit" and x[3][1] != 0): return True
            for y in x[1:]:
                if isinstance(y, tuple): stack.append(y)
                elif isinstance(y, list): stack.extend(z for z in y if isinstance(z, tuple))
        return False
    def chain(rows):
        c, e = rows[0]
        if len(rows) == 1: return e if c is None else ("bin", "&", c, e)
        return ("bin", "|", ("bin", "&", c, e), chain(rows[1:]))
    def tr(n, params):
        if isinstance(n, list): return [tr(x, params) for x in n]
        if not isinstance(n, tuple) or not n: return n
        k = n[0]
        if k == "lam":
            ps = set(params) | {q[1] for q in n[1] if isinstance(q, tuple) and len(q) > 1 and isinstance(q[1], str)}
            return (k, n[1], tr(n[2], ps)) + tuple(n[3:])
        if k == "bin" and len(n) == 4 and n[1] in ("'", "@"):
            key = unwrap(n[3] if n[1] == "'" else n[2])
            if isinstance(key, tuple) and key and key[0] == "post" and key[1] == "~": key = unwrap(key[2])
            if isinstance(key, tuple) and key and key[0] == "id": return ("id", "__")
        if k == "bin" and len(n) == 4 and n[1] in ("!=", "!==") and "5" not in off:                  # 5. strict: `!_` を含む比べは `!_`(完全性公理)。既定の道では `!=` は void を「違う」と読むので、両辺が値のときだけ比べに進ませる
            l_, r_ = tr(n[2], params), tr(n[3], params)
            if not (isinstance(l_, tuple) and l_[0] == "lit" and isinstance(r_, tuple) and r_[0] == "lit"):
                return ("bin", "&", ("bin", "==", l_, l_), ("bin", "&", ("bin", "==", r_, r_), ("bin", n[1], l_, r_)))
            return ("bin", n[1], l_, r_)
        if k == "cmp" and len(n) == 3 and n[2] == ["!="] and len(n[1]) == 2 and "5" not in off:       # `a != b` は cmp の形で来る
            l_, r_ = tr(n[1][0], params), tr(n[1][1], params)
            if not (isinstance(l_, tuple) and l_[0] == "lit" and isinstance(r_, tuple) and r_[0] == "lit"):
                return ("bin", "&", ("bin", "==", l_, l_), ("bin", "&", ("bin", "==", r_, r_), ("cmp", [l_, r_], ["!="])))
            return ("cmp", [l_, r_], ["!="])
        if k == "seq" and _fold_minmax(n) is not None: return _fold_minmax(n)    # 6. 順序の比べの畳みは最大・最小(`!_` を返さず、strict の値になる)
        if k == "seq" and len(n[1]) == 2 and "2" not in off:
            h, m = n[1]
            if isinstance(h, tuple) and (h[0] == "lit" or (h[0] == "id" and (h[1] in params or h[1] in vals) and h[1] not in funcs)) \
                    and isinstance(m, tuple) and m[0] == "id" and m[1] in funcs and m[1] not in params:
                return tr(h, params)
        if k == "cases":
            rows = []
            for c, e in n[1]:
                if isinstance(c, tuple) and c[0] == "id" and c[1] != "__" and "4" not in off:           # `__` は字面の void(未定義の名前ではない。行は外れる)
                    if c[1] in params or c[1] in vals: c = ("bin", "|", c, c)
                    else: rest.append((4, "行の左が名前だけ `%s : …`(仮引数でもファイルの定義でもない名前。strict では未定義)" % c[1], src(c) + " : " + src(e)))
                rows.append((tr(c, params) if c is not None else None, tr(e, params)))
            for i, (c, e) in enumerate(rows[:-1]):
                if "3" not in off and c is not None and (maybe_void(e) or has_call(e)):
                    return ("cases", rows[:i] + [(None, chain(rows[i:]))])
            return ("cases", rows)
        return (k,) + tuple(tr(y, params) for y in n[1:])
    out = [tr(n, set()) for n in tree]
    for f in strict_divergences(out):                           # 書き換えて残った形(たとえば逆適用 `c f x`)は断る
        if f[0] != 4 and f not in rest: rest.append(f)
    return out, rest

def main(argv):
    import os, subprocess, sys, tempfile
    path = out = elf = None
    target = "bare"; charset = None; real_dev = False; fps = 60; real_db = False; bundle = None; display = (64, 32); par = None; par_spec = False
    for a in argv:
        if a.startswith("--target="): target = a[9:]
        elif a.startswith("--elf="): elf = a[6:]; target = "linux"
        elif a.startswith("--charset="):
            charset = a[10:]
            if charset not in ("ascii", "utf32"): print("エラー: --charset は ascii か utf32 です(%s)" % charset, file=sys.stderr); return 1
        elif a == "--real-dev": real_dev = True
        elif a == "--par-relight":                            # 軽さを積みの深さで覚える(既定になったので何もしない。前の版の呼び方を通す)
            import sign_asmpar; sign_asmpar.RELIGHT = True
        elif a == "--par-site-light":                         # 前の既定: 軽さを呼び出し位置ごとに数える(3 回続けて軽いと以後ずっと直列)。境の既定は 1000
            import sign_asmpar; sign_asmpar.RELIGHT = False
            if not sign_asmpar.LIGHT_SET: sign_asmpar.LIGHT = 1000
        elif a.startswith("--par-spin="):                     # join の眠る前の見回りの回数。実機での調整用(sign_asmpar.SPIN)
            try:
                import sign_asmpar; sign_asmpar.SPIN = int(a[11:])
            except ValueError: print("エラー: --par-spin=N の N は整数です(%s)" % a, file=sys.stderr); return 1
        elif a.startswith("--par-light="):                    # 軽い仕事の境(cntvct_el0 の時計の数)。実機での調整用(sign_asmpar.LIGHT)
            try:
                import sign_asmpar; sign_asmpar.LIGHT = int(a[12:]); sign_asmpar.LIGHT_SET = True
            except ValueError: print("エラー: --par-light=N の N は整数です(%s)" % a, file=sys.stderr); return 1
        elif a == "--par-spec": par_spec = True
        elif a == "--spec-abort": SPEC_ABORT[0] = True
        elif a.startswith("--spec-look="):
            try: SPEC_LOOK[0] = max(1, int(a[12:]))
            except ValueError: print("エラー: --spec-look=N の N は整数です(%s)" % a, file=sys.stderr); return 1
        elif a == "--par" or a.startswith("--par="):
            try: par = int(a[6:]) if a.startswith("--par=") else 4
            except ValueError: print("エラー: --par=N の N は整数です(%s)" % a, file=sys.stderr); return 1
        elif a == "--real-db": real_db = True; real_dev = True; target = "linux"
        elif a.startswith("--pi-bundle="): bundle = a[12:]; real_db = True; real_dev = True; target = "linux"
        elif a.startswith("--fps="): fps = int(a[6:])
        elif a.startswith("--display="):                    # 論理画面の大きさ(--real-dev の描画)。処理系の書き方(png:ファイル:128x64 など)の最後の 幅x高さ だけを読む
            tail = a[10:].split(":")[-1]
            if "x" in tail and tail.replace("x", "").isdigit() and tail.count("x") == 1:
                w_, h_ = map(int, tail.split("x"))
                if not (1 <= w_ <= 4096 and 1 <= h_ <= 4096 and w_ * h_ <= 2073600): print("エラー: --display の大きさは 1x1〜4096x4096 で、画素は 2073600 以下です(%s)" % tail, file=sys.stderr); return 1
                display = (w_, h_)
        elif a == "--strict": STRICT[0] = True
        elif a == "--no-peephole": PEEP[0] = False
        elif a == "--no-lint": LINT[0] = False
        elif a == "--no-fuse": FUSE[0] = False
        elif a == "--no-share": SHARE[0] = False
        elif a == "--no-hoist": HOIST[0] = False
        elif a == "--no-scalar": SCALAR[0] = False
        elif a == "--no-neon": NEON[0] = False
        elif a == "--no-opt": PEEP[0] = False; os.environ["SIGN_OPT"] = "0"          # 最適化を全部切る(第107〜108段。効果の比べ・疑うとき用)
        elif a == "--no-estimate": os.environ["SIGN_ESTIMATE"] = "0"          # 上界を見積もりで通さず、証明できないものは断る
        elif a == "-o" or a.startswith("-o="): pass
        elif a in ("-h", "--help"): print(USAGE); return 0
        elif a.startswith("-") and a != "-": print("エラー: 知らないオプションです: %s\n%s" % (a, USAGE), file=sys.stderr); return 1
    if "-o" in argv:
        i = argv.index("-o")
        if i + 1 >= len(argv): print("エラー: -o にはファイル名が要ります", file=sys.stderr); return 1
        out = argv[i + 1]
    skip = {out} if out else set()
    files = [a for a in argv if not a.startswith("-") and a not in skip]
    if len(files) != 1: print("エラー: プログラムのファイルを 1 つ指してください\n" + USAGE, file=sys.stderr); return 1
    path = files[0]
    if target not in ("bare", "linux"): print("エラー: --target は bare か linux です(%s)" % target, file=sys.stderr); return 1
    try:
        src = open(path, encoding="utf-8").read()
        IMPORT_DIR[0] = os.path.dirname(os.path.abspath(path))
    except (OSError, UnicodeDecodeError) as e:
        print("エラー: %s を読めません(%s)" % (path, e), file=sys.stderr); return 1
    try:
        import sign_interp
        if charset is None:                                    # 指定が無ければ、プログラムと同じフォルダの option.ms の `charset : \`utf32\`` を見る(既定は ascii)
            charset = "ascii"
            try:
                om = open(os.path.join(os.path.dirname(os.path.abspath(path)), "option.ms"), encoding="utf-8").read()
                m = re.search(r"^charset\s*:\s*`?(ascii|utf32)`?", om, re.M)
                if m: charset = m.group(1)
            except OSError: pass
        sign_interp.CHARSET[0] = charset
        _tree = sign_interp.parse_source(src)
        if STRICT[0]:
            _tree, _f = strict_rewrite(_tree)                  # 別の道: strict の読みと同じ答えになる木へ書き換える
            if _f:
                raise AsmError("--strict の読みにできない形があります(書き換えられない形。コンパイラは既定の読みで解きます):\n" + "\n".join("  [%d] %s\n      %s" % f for f in _f[:12]) + ("\n  ほか %d 件" % (len(_f) - 12) if len(_f) > 12 else ""))
        text = generate(_tree, target, os.path.basename(path), charset, real_dev, fps, real_db, display, par if (par or not par_spec) else 4, par_spec)
        for fn, ln, rule, msg in LAST_LINT[:10]:      # 置き場の寿命の検査(sign_lint.py)。警告だけで、生成は止めない
            print("%s: 警告(lint %s): %s の %d 行目: %s" % (path, rule, fn, ln, msg), file=sys.stderr)
        if len(LAST_LINT) > 10: print("  ほか %d 件" % (len(LAST_LINT) - 10), file=sys.stderr)
    except AsmError as e:
        print("%s: 出せません: %s" % (path, e), file=sys.stderr)
        if "種類が揃っていません" in str(e):               # compiler_pipeline.md §3: 通った腕によって型が変わる値が関数の外へ出る形は、後段が出していないのではなく、断ると決めた形(札が要るなら書く側が enum で書く)
            print("  (これは Sign が断ると決めた形です: 型の違う値が関数の外へ出ます。種類の札が要るなら、書く側が書きます。compiler_pipeline.md §3)", file=sys.stderr)
        elif re.search(r"測れない|収束|上界|食わずに|食う器", str(e)):          # 上界まわりの断りは、仕様の禁止ではなく処理系の未対応/証明の不足
            if os.environ.get("SIGN_ESTIMATE") == "0":
                print("  (証明できる形だけを通すモードです。--no-estimate を外すと、仕様どおり見積もり+実行時の確認で通る形があります)", file=sys.stderr)
            else:
                print("  (これは処理系がまだ出せない形で、Sign の仕様が禁じる形ではありません。仕様では上界は見積もりで足ります。)", file=sys.stderr)
        return 1
    except RecursionError:
        print("%s: 式が深すぎて読めません" % path, file=sys.stderr); return 1
    except Exception as e:                      # 構文の誤りなど。落とさず理由を言って終わる
        print("%s: 読めません(%s): %s" % (path, type(e).__name__, e), file=sys.stderr); return 1
    for fn_, why_ in LAST_INFOS: print("information: %s: %s" % (fn_, why_), file=sys.stderr)
    if bundle:
        import shutil
        try:
            os.makedirs(bundle, exist_ok=True)
            open(os.path.join(bundle, "prog.s"), "w", encoding="utf-8").write(text + '\n\t.section .note.GNU-stack,"",@progbits\n')
            shutil.copy(os.path.join(os.path.dirname(os.path.abspath(__file__)), "sign_db.c"), os.path.join(bundle, "sign_db.c"))
            open(os.path.join(bundle, "build.sh"), "w").write("#!/bin/sh\n# Raspberry Pi 上で:  sudo apt install gcc libsqlite3-dev   のあと   sh build.sh   →  ./prog\n# (データベースのファイルは、./prog を起動したフォルダの下に作られる)\nset -e\ngcc -O2 -nostartfiles -no-pie -Wl,-Ttext-segment=0x10000000 -o prog prog.s sign_db.c -lsqlite3\n")
        except OSError as e:
            print("エラー: %s に書けません(%s)" % (bundle, e), file=sys.stderr); return 1
        print("書きました: %s/(prog.s・sign_db.c・build.sh)。Raspberry Pi で sh build.sh" % bundle, file=sys.stderr)
        return 0
    if elf and real_db:
        print("エラー: --real-db は libsqlite3 が要るので静的な ELF にはできません。--pi-bundle=DIR で一式を作り、Raspberry Pi で sh build.sh してください", file=sys.stderr); return 1
    if elf:
        with tempfile.TemporaryDirectory() as d:
            s, o = os.path.join(d, "a.s"), os.path.join(d, "a.o")
            open(s, "w", encoding="utf-8").write(text)
            try:
                r = subprocess.run(["clang", "--target=aarch64-linux-gnu", "-c", s, "-o", o], capture_output=True, text=True)
                if r.returncode == 0: r = subprocess.run(["ld.lld", "-static", "-e", "_start"] + (["--image-base=0x10000000"] if real_dev else []) + [o, "-o", elf], capture_output=True, text=True)
            except OSError as e:
                print("エラー: 組み立て・リンクの道具(clang・ld.lld)が使えません(%s)" % e, file=sys.stderr); return 1
            if r.returncode != 0:
                print("エラー: 組み立て・リンクに失敗しました:\n%s" % (r.stderr or r.stdout).strip(), file=sys.stderr); return 1
        print("書きました: %s(AArch64 の静的な ELF)" % elf, file=sys.stderr)
        return 0
    if out:
        try: open(out, "w", encoding="utf-8").write(text)
        except OSError as e: print("エラー: %s に書けません(%s)" % (out, e), file=sys.stderr); return 1
        print("書きました: %s" % out, file=sys.stderr)
    else:
        sys.stdout.write(text)
    return 0
