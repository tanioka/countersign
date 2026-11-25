"""Sign の strict 中間表現(SIR、第二段階)。
旧 AST(`parse_source` の木)は、既定の読みと strict の読みの両方のために作られていて、strict の答えは評価器の動きと、sign_asm の `strict_rewrite`・`strict_call_check` の継ぎはぎで合わせていた。
SIR は、strict の読みを**木の形そのものに書き出した**中間表現で、評価器とコード生成が同じ物を見る。
  ("int", n) / ("void",)                      値。整数は 64 ビット(範囲を出れば `!_`、value_spec V5)
  ("var", 名前)                                 仮引数(関数の本体の中)
  ("op", 記号, a, b)                            + - * / %。void の被演算子は単位で消える(`5 + _` は 5)。両方 void なら void。`/` `%` は割る数が 0 なら void(消えた void と同じ)
  ("fold", 記号, [項...])                      `[>] a b c` などの畳み: void は飛ばし、`<` `>` `<=` `>=` は残りを `(a op b) | b` で畳む(最小・最大)、`==` `=` は全部等しければその値、違えば void
  ("abs", a)                                   絶対値 `|a|`(中が整数の 1 行)。void は void。値域が 0 を挟んで対称なので溢れない(integer_overflow.md)。リスト・並びの絶対値は断る
  ("neg", a)                                   符号反転。void は void のまま(`-_` は void。`0 - _` の 0 とは別)
  ("chain", [記号...], [項...])                  比べの連鎖: 3 項の範囲(`a < b < c` 等)は両方成り立てば真ん中の項、`=`・`==` だけの連鎖は全部等しければ最初の項。外れたら後ろの項は評価しない
  ("cmp", 記号, a, b)                           < > <= >= = == != !==。成り立てば a、外れ・どちらかが void なら void(R-rule、`a op b` は a か void)
  ("and", a, b) / ("or", a, b)                  `&`: a が void でなければ b、void なら void。`|`: a が void でなければ a、void なら b
  ("rows", [(条件 か None, 値), ...])             行の列。各行は `c & v | 次の行`(V10): 条件が void でなく値も void でなければその値。値が void なら次の行へ落ちる。条件 None は既定の行。尽きれば void
  ("call", 名前, [実引数...])                     関数の呼び。口の数ちょうど。実引数が 1 つでも void なら呼びは成り立たず(部分適用)、SIR の評価は ("partial",) を返す
  ("str", "abc") / ("chr", コード)              文字列・文字の定数(S1、SIR_VALUES.md)。ASCII だけ。使える所は `||s||`(長さ)・名前・答えだけで、算術・比べ・添字・実引数・並びに置く形は断る
  ("struct", [(名前, 式)...]) / ("field", 式, 名前)    欄ブロック(構造体)と、名前の鍵の欄引き `p ' a`(S3・S5、SIR_VALUES.md)。欄の式は前の欄の名前を見られる。欄引きの底が欄ブロックでなければ `!_`(R64)
  ("flow", [項...])                              並び(積)。void の項は消える。項が 1 つだけ残ればその項、0 ならvoid
SIR に下げられない形は Unsup を投げ、理由を持つ(未対応の数え方が、そのまま次の段の仕事の一覧になる)。"""
I64_MAX, I64_MIN = 2**63 - 1, -(2**63 - 1)     # 範囲の下は -MAX(MIN に着くのも `!_`、value_spec V5)

from sign_interp import Char

class Unsup(Exception):
    pass

class Str(str): pass                                                           # 文字列の値(ASCII)
class Chr:                                                                      # 文字の値。整数とは別の種類(strict が区別する)なので int の部分クラスにしない
    __slots__ = ("c",)
    def __init__(self, c): self.c = c
    def __eq__(self, o): return isinstance(o, Chr) and o.c == self.c
    def __hash__(self): return hash(("chr", self.c))
class Rec:                                                                      # 欄ブロック(構造体)の値: (欄の名前, 値) の並び。値は単位(None)でもよい(`b : (3 < 2)` の欄は `!_` で残る)
    __slots__ = ("items",)
    def __init__(self, items): self.items = items
def show_rec(v):
    if v is None: return "!_"
    if isinstance(v, Rec): return "[" + ", ".join("%s: %s" % (n, show_rec(x)) for n, x in v.items) + "]"
    if isinstance(v, Str): return "`" + str(v) + "`"
    if isinstance(v, Chr): return "\\" + chr(v.c)
    return str(v)
def textual(v): return isinstance(v, (Str, Chr, Rec))

class Funcs(dict):
    """{関数名: (仮引数名の列, 本体の SIR)}。既定値のある関数だけ `defaults[名前]`(仮引数ごとの整数か None)を持つ(口は、既定値の無い口が先、既定値のある口が後)。"""
    def __init__(self): super().__init__(); self.defaults = {}

def int_default(d):
    """既定値は整数の字面だけ(式の既定値は SIR の対象外)。"""
    d = unblock(d)
    if d[0] == "lit" and isinstance(d[1], int) and not isinstance(d[1], bool): return d[1]
    if d[0] == "neg" and unblock(d[1])[0] == "lit" and isinstance(unblock(d[1])[1], int): return -unblock(d[1])[1]
    raise Unsup("既定値が整数の字面でない")

def lower(nodes):
    """旧 AST の節の列 → (Funcs = {関数名: (仮引数名の列, 本体の SIR)}, 最後の行の SIR か None)。下げられなければ Unsup"""
    funcs, arity = Funcs(), {}
    for n in nodes:
        if n[0] == "def":
            if isinstance(n[2], tuple) and n[2][0] == "lam":
                if any(p[0] != "name" for p in n[2][1]): raise Unsup("括りの仮引数")
                ds = [None if p[2] is None else int_default(p[2]) for p in n[2][1]]
                if any(d is not None for d in ds):
                    if any(d is None for d in ds[ds.index(next(d for d in ds if d is not None)):]): raise Unsup("既定値のある口の後に、既定値の無い口")
                    funcs.defaults[n[1]] = ds
                arity[n[1]] = len(n[2][1])
            else: arity[n[1]] = 0                                                  # 値の定義は口の無い呼び
    body_top = None
    for n in nodes:
        if n[0] == "def":
            if isinstance(n[2], tuple) and n[2][0] == "lam":
                lam = n[2]; ps = [p[1] for p in lam[1]]
                INFUNC[0] = True
                try: funcs[n[1]] = (ps, expr(lam[2], set(ps), arity))
                finally: INFUNC[0] = False
            else: funcs[n[1]] = ([], expr(n[2], set(), arity))
        else: body_top = expr(n, set(), arity)
    return funcs, body_top

INFUNC = [False]
INROWS = [0]                       # 行(cases)の中を下げている間は 0 でない

def lit_list(items):
    """整数の字面だけの並び(2 つ以上)は整数のリスト値。"""
    out = []
    for x in items:
        x = unblock(x)
        if x[0] == "lit" and isinstance(x[1], int) and not isinstance(x[1], bool): out.append(x[1])
        elif x[0] == "neg" and unblock(x[1])[0] == "lit" and isinstance(unblock(x[1])[1], int): out.append(-unblock(x[1])[1])
        else: return None
    return ("list", tuple(out)) if len(out) >= 2 and all(I64_MIN <= v <= I64_MAX for v in out) else None

def unblock(n):
    while isinstance(n, tuple) and n and n[0] == "block": n = n[1]
    return n

def expr(n, params, arity):
    n = unblock(n)
    k = n[0]
    if k == "lit":
        if isinstance(n[1], str):
            if not n[1].isascii() or not n[1]: raise Unsup("ASCII でない・空の文字列と文字")
            if isinstance(n[1], Char):
                if len(n[1]) != 1: raise Unsup("文字の形")
                return ("chr", ord(n[1]))
            return ("str", str(n[1]))
        if isinstance(n[1], float):                                                # S4: Float の字面(type_system.md 昇格格子・IEEE 754)。有限だけ
            if n[1] != n[1] or n[1] in (float("inf"), float("-inf")): raise Unsup("有限でない Float の字面")
            return ("flt", n[1])
        if not isinstance(n[1], int) or isinstance(n[1], bool): raise Unsup("整数でない字面")
        return ("int", n[1])
    if k == "struct":
        names = [f[0] for f in n[1]]
        if len(set(names)) != len(names): raise Unsup("欄の名前が同じ括りで 2 回(P2。strict が断る)")
        out, seen = [], set(params)
        for name, fe in n[1]:
            out.append((name, expr(fe, seen, arity))); seen = seen | {name}
        return ("struct", out)
    if k == "neg":
        x = expr(n[1], params, arity)
        return ("neg", x)
    if k == "id":
        if n[1] == "__": return ("void",)
        if n[1] in params: return ("var", n[1])
        if n[1] in arity:
            if arity[n[1]] == 0: return ("call", n[1], [])
            raise Unsup("関数の名前を値として置く")
        if INROWS[0]: raise Unsup("行・枝の中の未定義の名前(R128・R139 の門 G22 と、行の値の読みが strict と分かれる)")
        return ("void",)                                                      # 見える範囲に定義の無い名前は `!_`(R21。読む段が name-undefined の warning を出す。SIR の観測は値だけで、知らせは持たない)。取り込み `@` は SIR の外なので、範囲の取り込みで名前が増えることは無い
    if k == "bin":
        op = n[1]
        if op in ("+", "-", "*", "/", "%"): return ("op", op, expr(n[2], params, arity), expr(n[3], params, arity))
        if op == "&": return ("and", expr(n[2], params, arity), expr(n[3], params, arity))
        if op == "|": return ("or", expr(n[2], params, arity), expr(n[3], params, arity))
        if op == "'":
            key = unblock(n[3])
            if key[0] == "post" and key[1] == "~": key = unblock(key[2])
            if key[0] == "id" and key[1] != "__":                                  # R64: 鍵の名前は欄の名前(値の名前でも)。欄ブロックなら欄、ほかは `!_`
                return ("field", expr(n[2], params, arity), key[1])
            return ("idx", expr(n[2], params, arity), expr(n[3], params, arity))
        if op in ("==", "!==", "!="): return ("cmp", op, expr(n[2], params, arity), expr(n[3], params, arity))
        raise Unsup("演算子 " + op)
    if k == "abs": return ("abs", expr(n[1], params, arity))
    if k == "norm": return ("len", expr(n[1], params, arity))
    if k == "cmp":
        xs = [expr(x, params, arity) for x in n[1]]
        if len(xs) == 2: return ("cmp", n[2][0], xs[0], xs[1])
        ops = n[2]
        rng = all(o in ("<", "<=") for o in ops) or all(o in (">", ">=") for o in ops)
        if (len(xs) == 3 and rng) or all(o == "=" for o in ops) or all(o == "==" for o in ops): return ("chain", list(ops), xs)
        raise Unsup("比べの連鎖の形(R119)")
    if k == "cases":
        INROWS[0] += 1
        try: return ("rows", [(None if c is None else expr(c, params, arity), expr(v, params, arity)) for c, v in n[1]])
        finally: INROWS[0] -= 1
    if k == "seq":
        items = n[1]
        h = unblock(items[0])
        if h[0] == "sec" and len(h) == 5 and h[1] == "fold" and h[3] is None and h[4] is False and len(items) >= 2:
            if h[2] not in ("<", ">", "<=", ">=", "==", "="): raise Unsup("畳みの節 " + h[2])
            return ("fold", h[2], [expr(x, params, arity) for x in items[1:]])
        if len(items) == 2:                                                        # 逆適用 `c f`: 関数 f は余りで落ち、値は c(補正 2)
            m = unblock(items[1])
            if (h[0] == "lit" or (h[0] == "id" and h[1] != "__" and (h[1] in params or arity.get(h[1]) == 0))) \
                    and m[0] == "id" and m[1] not in params and arity.get(m[1], 0) > 0:
                return expr(h, params, arity)
        if h[0] == "id" and h[1] in arity and h[1] not in params:
            a = arity[h[1]]
            args = [expr(x, params, arity) for x in items[1:1 + a]]
            call = ("call", h[1], args)
            rest = [expr(x, params, arity) for x in items[1 + a:]]
            return call if not rest else ("flow", [call] + rest)
        li = lit_list(items)
        if li is not None: return li
        return ("flow", [expr(x, params, arity) for x in items])
    raise Unsup("節 " + k)

def clamp(v): return v if I64_MIN <= v <= I64_MAX else None

def evaluate(funcs, top, fuel=200000):
    """SIR の評価。戻り値: ("val", 整数) / ("void",) / ("partial",)(呼びの実引数が void) / ("fuel",)"""
    steps = [0]
    class Fuel(Exception): pass
    class PF:                                                                   # 部分適用: 実引数が void で消えて、まだ足りない関数(後ろの値を受け取る。R83・R84)
        def __init__(self, f, args, need): self.f, self.args, self.need = f, args, need
    class Flow(list): pass                                                      # 2 つ以上の値の並び
    def one(v):                                                                 # 演算の項に置く: 部分適用は `!_` と同じ。複数の並びは断る
        if isinstance(v, PF): return None
        if isinstance(v, Flow): raise Unsup("複数の値の並びを演算の項に置く")
        return v
    def run_call(name, args):
        ps, body = funcs[name]
        v = ev(body, dict(zip(ps, args)))
        return None if isinstance(v, PF) else v                                 # 余った関数は関数の境界を越えない
    def fold_flow(items):
        """並び(値と余った関数)を左から畳む(strict の resolve_fold・Pipe と同じ。V3: 関数·値は口を 1 つ埋める、関数·関数は合成、値·関数は積む)。
        合成した関数(段の並び)に値が来ると、最初の開いた段から順に埋め、埋まった段の答えは次の段の最初の口へ流れる。答えが単位なら次の段は何も受けず開いたまま。
        段が全部埋まれば答えを並びに戻す。足りないまま並びが終われば、余った関数は消える(値の上に積まれた関数は警告つきで消え、下の値が残る)"""
        vals, pre, pipe = [], None, None
        def settle(out):
            nonlocal vals, pre, pipe
            vals = (pre if pre is not None else []) + ([] if out is None else [out]); pre = None; pipe = None
        def feed(v):
            while True:
                st = pipe[0]
                if v is None: return None                                      # 単位は口を埋めない。段は開いたまま
                a2 = st.args + [v]
                if len(a2) < st.need + len(st.args):                           # まだ口が残る
                    pipe[0] = PF(st.f, a2, st.need - 1); return None
                r = run_call(st.f, a2)
                if isinstance(r, Flow): raise Unsup("合成した関数の段の答えが並び")
                pipe.pop(0)
                if not pipe: return ("done", r)
                v = r
        for x in items:
            if pipe is not None:
                if isinstance(x, PF): pipe.append(PF(x.f, list(x.args), x.need))
                else:
                    out = feed(x)
                    if out is not None: settle(out[1])
            elif isinstance(x, PF): pre = vals; vals = []; pipe = [PF(x.f, list(x.args), x.need)]
            else: vals.append(x)
        if pipe is not None:
            if pre is not None: vals = pre                                    # 余った関数は消え、下の値が残る
            else: vals = []
        return None if not vals else vals[0] if len(vals) == 1 else Flow(vals)
    def ev(e, env):
        steps[0] += 1
        if steps[0] > fuel: raise Fuel()
        k = e[0]
        if k == "int": return e[1]
        if k == "flt": return e[1]
        if k == "void": return None
        if k == "str": return Str(e[1])
        if k == "struct":
            env2, items = dict(env), []
            for name, fe in e[1]:
                v = ev(fe, env2)
                if isinstance(v, (PF, Flow, tuple)): raise Unsup("欄の値が余った関数・並び")
                env2[name] = v; items.append((name, v))
            return Rec(items)
        if k == "field":
            a = one(ev(e[1], env))
            if isinstance(a, Rec):
                for n_, v_ in a.items:
                    if n_ == e[2]: return v_
            return None
        if k == "chr": return Chr(e[1])
        if k == "var": return env[e[1]]
        if k == "op":
            a, b = one(ev(e[2], env)), one(ev(e[3], env))
            if isinstance(a, tuple) or isinstance(b, tuple): raise Unsup("リストの算術")
            if isinstance(a, Rec) or isinstance(b, Rec): raise Unsup("欄ブロックの算術")
            if isinstance(a, Chr) or isinstance(b, Chr):                         # 文字の域の射(type_system.md 1543–1590)。左辺が規則を選ぶ。域は U+0001〜U+007F(ascii)。`!_` は両側で吸収
                o = e[1]
                if a is None or b is None: return None
                if isinstance(a, (float, Rec)) or isinstance(b, (float, Rec)): raise Unsup("文字と Float・欄ブロックの算術")
                if isinstance(a, Str) or isinstance(b, Str): return None                  # 文字列は算術を飲まない(`s * \a` は回数が文字で射なし)
                def dom(r):
                    if r == 0: raise Unsup("ずらした先が U+0000(仕様は `!_`。strict は文字 U+0000 を返す。M1)")
                    return Chr(r) if 1 <= r <= 127 else None
                if isinstance(a, Chr) and isinstance(b, Chr):
                    if o == "+": return dom(a.c + b.c)
                    if o == "-": return a.c - b.c
                    return None                                                       # `c * d`・`c / d`・`c % d` は射なし
                if isinstance(a, Chr):                                                # `c ⊕ n`
                    if o == "+": return dom(a.c + b)
                    if o == "-": return dom(a.c - b)
                    if o == "*":
                        if b <= 0: return None
                        if b > 100000: raise Unsup("文字の繰り返しが大きい")
                        return Str(chr(a.c) * b)
                    return None                                                       # `c / n`・`c % n`・`c ^ n` は射なし
                b = b.c                                                             # `n ⊕ c`: 左が Int の域。文字は符号位置の数として読む
            if isinstance(a, Str) or isinstance(b, Str):
                if e[1] == "*" and isinstance(a, Str) and isinstance(b, int):          # 連結の n 乗(type_system.md 910)。n = 0 は空の余積で `!_`、負は射なし(`!_`)。回数が文字列・文字・Float・`!_` なら射なし(`!_`)。左が文字列でないとき(`3 * s`)は `!_`
                    if b <= 0: return None
                    if len(a) * b > 100000: raise Unsup("文字列の繰り返しが大きい(実装の上限の扱いを入れない)")
                    return Str(str(a) * b)
                return None                                                    # 算術は String を飲まない(list_model.md 4.1)。`s + 1`・`1 + s`・`s + __`・`s - s`・`s / 2` は `!_`。`!_` は外の演算の口で消える(`5 + (s + 1)` は 5)
            if a is None or b is None: return b if a is None else a
            op = e[1]
            if isinstance(a, float) or isinstance(b, float):                    # S4: 整数 ⊕ Float は Float へ昇格(type_system.md 昇格格子)、IEEE 754。`%` は仕様が Float の剰余を `x % 0.0` の NaN しか定めない(strict は床の剰余)ので断る。0 割り・溢れの `±∞`・NaN は `!_` との繋ぎが未決(integer_overflow.md 1.1 の NOTE)なので断る
                if op == "%": raise Unsup("Float の `%`(仕様は符号の規則を定めない)")
                if op == "/" and b == 0: raise Unsup("Float の 0 割り(`±∞`・NaN と `!_` の繋ぎが未決)")
                x, y = float(a), float(b)
                z = x + y if op == "+" else x - y if op == "-" else x * y if op == "*" else x / y
                if z != z or z in (float("inf"), float("-inf")): raise Unsup("Float の溢れ(`±∞`・NaN は `!_` との繋ぎが未決)")
                return z
            if op == "+": return clamp(a + b)
            if op == "-": return clamp(a - b)
            if op == "*": return clamp(a * b)
            if b == 0: return None
            q = abs(a) // abs(b) * (1 if (a >= 0) == (b >= 0) else -1)         # 0 へ丸める(value_spec の除算)
            return clamp(q) if op == "/" else clamp(a - q * b)
        if k == "cmp":
            a, b = one(ev(e[2], env)), one(ev(e[3], env))
            if isinstance(a, tuple) or isinstance(b, tuple): raise Unsup("リストの比べ")
            if isinstance(a, Str) and isinstance(b, Str) and e[1] in ("=", "=="): return a if a == b else None      # 同じ文字列なら左、違えば `!_`(strict の観測)
            if textual(a) or textual(b): raise Unsup("文字列・文字の比べ(`=`・`==` の文字列どうしだけ入れた)")
            if a is None or b is None: return None
            op = e[1]
            ok = {"<": a < b, ">": a > b, "<=": a <= b, ">=": a >= b, "=": a == b, "==": a == b, "!=": a != b, "!==": a != b}[op]
            return a if ok else None
        if k == "fold":
            vs = [v for v in (one(ev(x, env)) for x in e[2]) if v is not None]
            if any(isinstance(v, tuple) for v in vs): raise Unsup("リストの畳み")
            if any(textual(v) for v in vs): raise Unsup("文字列・文字の畳み")
            if not vs: return None
            op = e[1]
            if op in ("==", "="): return vs[0] if all(v == vs[0] for v in vs) else None
            acc = vs[0]
            for b in vs[1:]:
                acc = acc if {"<": acc < b, ">": acc > b, "<=": acc <= b, ">=": acc >= b}[op] else b
            return acc
        if k == "list": return e[1]
        if k == "len":
            a = ev(e[1], env)
            if isinstance(a, PF): return None                                   # `||f||`(f が余った関数)は囲みごと `!_`(仕様 R27)。`||_||` の 0 とは別
            a = one(a)
            if a is None: return 0                                              # `||_||` は 0(value_spec 83 行、U〔答え〕2026-10-28 00:17)。以前は単位にしていて、strict と食い違った
            if isinstance(a, Rec): return len(a.items)                           # 欄の数(単位の欄も数える)
            if isinstance(a, Str): return len(a)                                 # strict: ||`abc`|| = 3
            if isinstance(a, Chr): return 1                                      # ||\a|| = 1
            if not isinstance(a, tuple): raise Unsup("整数の長さ")
            return len(a)
        if k == "idx":
            a, i = one(ev(e[1], env)), one(ev(e[2], env))
            if isinstance(i, float):                                               # Address を要求する位置の Float は最近接へ丸める(type_system.md 4.1・`fcvtas`: 同じ近さなら 0 から遠い方)
                if abs(i) >= 2.0 ** 62: raise Unsup("Float の添字が大きすぎる(飽和の規則を入れない)")
                import math
                i = int(math.copysign(math.floor(abs(i) + 0.5), i))
            if isinstance(a, Rec):                                                 # 欄ブロックの添字: 整数は位置(負は後ろから)、文字列は欄の名前。範囲外・単位・名前なしは `!_`
                if i is None: return None
                if isinstance(i, Str):
                    for n_, v_ in a.items:
                        if n_ == str(i): return v_
                    return None
                if isinstance(i, (Chr, Rec, tuple)): raise Unsup("欄ブロックの鍵が文字・欄ブロック・リスト")
                if i < 0: i += len(a.items)
                return a.items[i][1] if 0 <= i < len(a.items) else None
            if isinstance(a, Chr) or textual(i): raise Unsup("文字・文字を添字にする形(文字の添字、文字列・文字の鍵)")
            if isinstance(a, Str):                                                 # String は List(Char) と同型(type_system.md 110 行)。範囲外は `!_`(idiom_to_instructions.md 767 行)、負は後ろから(type_system.md 423 行)
                if i is None: return None
                if isinstance(i, tuple): raise Unsup("文字列の添字がリスト")
                if i < 0: i += len(a)
                return Chr(ord(a[i])) if 0 <= i < len(a) else None
            if a is None or i is None: return None
            if not isinstance(a, tuple) or isinstance(i, tuple): raise Unsup("添字の型")
            if i < 0: i += len(a)
            return a[i] if 0 <= i < len(a) else None
        if k == "abs":
            a = one(ev(e[1], env))
            if isinstance(a, tuple): raise Unsup("リストの絶対値")
            if isinstance(a, Str): return None                                     # `|s|` は `!_`(strict の観測。算術は String を飲まない)
            if textual(a): raise Unsup("文字の絶対値")
            return None if a is None else abs(a)
        if k == "neg":
            a = one(ev(e[1], env))
            if isinstance(a, tuple): raise Unsup("リストの符号")
            if isinstance(a, Str): return None                                     # `-s` は `!_`
            if textual(a): raise Unsup("文字の符号")
            return None if a is None else (-a if isinstance(a, float) else clamp(-a))
        if k == "chain":
            ts, ops = e[2], e[1]
            vals = []
            for i, t in enumerate(ts):
                v = one(ev(t, env))
                if isinstance(v, tuple): raise Unsup("リストの比べ")
                if textual(v): raise Unsup("文字列・文字の比べ")
                if v is None: return None
                vals.append(v)
                if i:
                    a, b, o = vals[i-1], v, ops[i-1]
                    ok = {"<": a < b, ">": a > b, "<=": a <= b, ">=": a >= b, "=": a == b, "==": a == b}[o]
                    if not ok: return None
            return vals[1] if len(ts) == 3 and ops[0] in ("<", "<=", ">", ">=") else vals[0]
        if k == "and":
            a = ev(e[1], env)
            if isinstance(a, (PF, Flow)): raise Unsup("部分適用・並びを & の左に置く")
            if textual(a): raise Unsup("文字列・文字を & の左に置く")
            return None if a is None else ev(e[2], env)
        if k == "or":
            a = ev(e[1], env)
            if isinstance(a, (PF, Flow)): raise Unsup("部分適用・並びを | の左に置く")
            if textual(a): raise Unsup("文字列・文字を | の左に置く")
            return a if a is not None else ev(e[2], env)
        if k == "rows":
            for c, v in e[1]:                                                  # 行は `c & v | 次の行`(value_spec V10)。v が void なら次の行へ落ちる
                cv = None if c is None else one(ev(c, env))
                if textual(cv): raise Unsup("文字列・文字を行の条件に置く")
                if c is None or cv is not None:
                    r = ev(v, env)
                    if isinstance(r, PF): r = None                                 # 行の値に裸の関数が残れば `!_`(coproduct_spec bare-function-return)。枝の値の `!_` は次の行へ進む(V8・V10)
                    if r is not None: return r
            return None
        if k == "call":
            args = []
            for x in e[2]:
                v = ev(x, env)
                if isinstance(v, (PF, Flow)): raise Unsup("実引数が部分適用・並び")
                args.append(v)
            ds = getattr(funcs, "defaults", {}).get(e[1])
            if ds is not None and any(textual(v) for v in args): raise Unsup("既定値のある関数へ文字列・文字を渡す")
            if ds is not None:                                                  # 既定値のある関数(R107): 足りない・単位の口は既定値で埋める。既定値の無い口が足りない・単位なら部分適用になるので断る
                full = list(args) + [None] * (len(ds) - len(args))
                for i, d in enumerate(ds):
                    if full[i] is None:
                        if d is None: raise Unsup("既定値のある関数の、既定値の無い口が足りない・単位")
                        full[i] = d
                return run_call(e[1], full)
            have = [v for v in args if v is not None]
            n = len(funcs[e[1]][0])
            if len(have) < n: return PF(e[1], have, n - len(have))                    # void の実引数が消えた・口が足りない: 後ろの値を待つ
            return run_call(e[1], args)
        if k == "flow":
            items = []
            for x in e[1]:
                v = ev(x, env)
                if v is None: continue
                if isinstance(v, tuple): raise Unsup("流れの中のリスト")
                if textual(v): raise Unsup("文字列・文字を並びに置く")
                items.extend(v) if isinstance(v, Flow) else items.append(v)
            return fold_flow(items)
        raise Unsup("SIR " + k)
    try:
        v = ev(top, {})
    except Fuel: return ("fuel",)
    except RecursionError: return ("fuel",)
    if isinstance(v, PF): v = None                                              # 余った関数は消える
    if isinstance(v, Flow): return ("flow", tuple(v))
    if isinstance(v, Rec): return ("rec", show_rec(v))
    if isinstance(v, Str): return ("str", str(v))
    if isinstance(v, Chr): return ("chr", v.c)
    if isinstance(v, float): return ("flt", repr(v))
    if isinstance(v, tuple): return ("flow", v)                                 # 整数の並び(リスト)は流れと同じ字で出る
    return ("void",) if v is None else ("val", v)

# ---- SIR → 旧 AST(段階 C の試作): strict_rewrite を通さずに generate へ渡せる木を、SIR から作る ----
def nonvoid(e):
    """e は void にならない(被演算子に置いても単位の読みが要らない)と静的に言える。"""
    k = e[0]
    if k in ("int", "flt", "var"): return True
    if k in ("neg", "abs"): return nonvoid(e[1])
    if k == "op":
        if not (nonvoid(e[2]) and nonvoid(e[3])): return False
        if e[1] in ("/", "%"): return e[3][0] == "int" and e[3][1] != 0
        return True
    return False

def has_call(e):
    if not isinstance(e, tuple): return False
    if e[0] == "call" and e[2]: return True                 # 口の無い呼び(値の名前)は二重に評価しても同じ値
    for x in e[1:]:
        if isinstance(x, tuple) and has_call(x): return True
        if isinstance(x, list) and any(has_call(y) for y in x if isinstance(y, tuple)): return True
    return False

def check_textual(funcs, top):
    """文字列・文字は、機械語へ戻せる所だけ戻す。戻せる位置(ok): `||…||` の直下、文字列の添字 `s ' i` の底(添字そのものは数)、答え、口の無い定義の本体そのもの、
    文字列・文字が来る仮引数への実引数、文字列・文字をそのまま返す関数(本体が仮引数・字面・添字)の呼び。それ以外(算術・比べ・&|・行・並びの中)は断る。
    文字列・文字が来る仮引数は、その仮引数に来る実引数が全部文字列・文字のときだけ(混ざれば断る。機械語は仮引数の種類を呼びの実引数から決める)。
    機械語の文字は整数と同じ字で出て、文字の `__` は U+0000。答えの見方は実機の印字(linux)"""
    tf, tp = set(), set()                                                         # tf: 文字列・文字を返す関数の名前。tp: 文字列・文字が来る (関数, 仮引数)
    def tv(e, f):
        k = e[0]
        if k in ("str", "chr"): return True
        if k == "call": return e[1] in tf
        if k == "var": return (f, e[1]) in tp
        if k == "idx": return tv(e[1], f)
        return False
    def kids(e):
        for x in e[1:]:
            if isinstance(x, tuple) and x and isinstance(x[0], str): yield x
            elif isinstance(x, (list, tuple)):
                for y in x:
                    if isinstance(y, tuple) and y and isinstance(y[0], str): yield y
                    elif isinstance(y, tuple):
                        for z in y:
                            if isinstance(z, tuple) and z and isinstance(z[0], str): yield z
    def calls(e, f):
        if not isinstance(e, tuple): return
        if e[0] == "call": yield e, f
        for c in kids(e): yield from calls(c, f)
    allcalls = [c for n, (ps, b) in funcs.items() for c in calls(b, n)] + list(calls(top, None))
    while True:
        ch = False
        for n, (ps, b) in funcs.items():
            if n not in tf and tv(b, n): tf.add(n); ch = True
        for c, ctx in allcalls:
            g = funcs[c[1]][0]
            for i, a in enumerate(c[2]):
                if i < len(g) and (c[1], g[i]) not in tp and tv(a, ctx): tp.add((c[1], g[i])); ch = True
        if not ch: break
    dfl = getattr(funcs, "defaults", {})
    for c, ctx in allcalls:
        g = funcs[c[1]][0]
        for i, a in enumerate(c[2]):
            if i < len(g) and (c[1], g[i]) in tp and not tv(a, ctx): raise Unsup("文字列・文字と、そうでない実引数が同じ仮引数に来る")
        if any((c[1], q) in tp for q in g) and c[1] in dfl: raise Unsup("既定値のある関数へ文字列・文字を渡す")
    def walk(e, f, ok):
        if not isinstance(e, tuple): return
        k = e[0]
        if k in ("str", "chr") and not ok: raise Unsup("文字列・文字を機械語に戻せない位置に置く")
        if k == "var" and (f, e[1]) in tp and not ok: raise Unsup("文字列・文字の仮引数を機械語に戻せない位置に置く")
        if k == "call":
            g = funcs[e[1]][0]
            if e[1] in tf and not ok: raise Unsup("文字列・文字を返す関数の呼びを機械語に戻せない位置に置く")
            for i, a in enumerate(e[2]): walk(a, f, i < len(g) and (e[1], g[i]) in tp)
            return
        if k == "idx" and tv(e[1], f):
            if not ok: raise Unsup("文字列の添字を機械語に戻せない位置に置く")
            walk(e[1], f, True); walk(e[2], f, False); return
        for c in kids(e): walk(c, f, k == "len")
    for n, (ps, b) in funcs.items(): walk(b, n, tv(b, n))
    walk(top, None, tv(top, None))

class _Need(Exception):
    def __init__(self, e): self.e = e

def plan_flow(funcs, items, cap=5):
    """流れ(`("flow", [項...])`)のうち、実引数が単位になりうる呼び・口の足りない呼び(余った関数)を含む形を、
    **単位かどうかで場合分けした木**(`(E & A) | B`)に書き換える。各葉は、余った関数も合成も解いた、普通の並び(値と口の埋まった呼びだけ)。
    解き方は `evaluate` の `fold_flow`(strict の resolve_fold・Pipe)と同じ左からの畳みを、式の上で行う: 単位かどうかが決まらない式は場合分けの点(_Need)にする。
    木の符号化は、葉がどれも単位でない(空でない)ときだけ正しい(`E & A` の A が単位だと `|` の B へ落ちるため)。空の葉・値 1 つの葉と並びの葉が混ざる(機械語は枝の種類を揃えられない)・場合分けが cap を超える・関数の答えが並びなら None(今の道に戻す)。"""
    dfl = getattr(funcs, "defaults", {})
    if any(x[0] == "call" and x[1] in dfl for x in items): return None
    memo = {}
    def body_nv(f, seen=()):
        if f in memo: return memo[f]
        if f in seen: return False
        ps, b = funcs[f]
        memo[f] = False if b[0] in ("flow", "rows", "list") else nv(b, seen + (f,))
        return memo[f]
    def nv(x, seen=()):
        if x[0] == "call":
            ps, b = funcs[x[1]]
            return len(x[2]) == len(ps) and all(nv(a, seen) for a in x[2]) and body_nv(x[1], seen)
        return nonvoid(x)
    def interesting(x):
        if x[0] != "call": return False
        ps, b = funcs[x[1]]
        return len(x[2]) < len(ps) or not all(nv(a) for a in x[2])
    if not any(interesting(x) for x in items): return None
    for x in items:
        if x[0] == "call" and funcs[x[1]][1][0] == "flow": return None
    def sim(dec):
        def isnv(x):
            if nv(x): return True
            k = repr(x)
            if k in dec: return dec[k]
            raise _Need(x)
        vs = []                                                                         # 評価した項: ("v", 式) か ("pf", 関数, 実引数の式, 残りの口)
        for x in items:
            if x[0] == "call":
                have = [a for a in x[2] if isnv(a)]
                n = len(funcs[x[1]][0])
                if len(have) < n: vs.append(("pf", x[1], have, n - len(have))); continue
                c = ("call", x[1], have)
                if isnv(c): vs.append(("v", c))
            elif isnv(x): vs.append(("v", x))
        vals, pre, pipe = [], None, None
        def feed(v):
            while True:
                if v is None: return None
                f, args, need = pipe[0]
                a2 = args + [v]
                if need > 1: pipe[0] = (f, a2, need - 1); return None
                c = ("call", f, a2)
                rr = c if isnv(c) else None
                pipe.pop(0)
                if not pipe: return ("done", rr)
                v = rr
        for t in vs:
            if pipe is not None:
                if t[0] == "pf": pipe.append((t[1], list(t[2]), t[3]))
                else:
                    out = feed(t[1])
                    if out is not None:
                        vals = (pre if pre is not None else []) + ([] if out[1] is None else [out[1]]); pre = None; pipe = None
            elif t[0] == "pf": pre = vals; vals = []; pipe = [(t[1], list(t[2]), t[3])]
            else: vals.append(t[1])
        if pipe is not None: vals = pre if pre is not None else []
        return vals
    def build(dec):
        if len(dec) > cap: raise Unsup("場合分けが多すぎる")
        try: leaf = sim(dec)
        except _Need as n:
            k = repr(n.e)
            return ("node", n.e, build({**dec, k: True}), build({**dec, k: False}))
        if not leaf: raise Unsup("空の葉")
        return ("leaf", leaf)
    try: tree = build({})
    except Unsup: return None
    def sizes(t): return {len(t[1]) > 1} if t[0] == "leaf" else sizes(t[2]) | sizes(t[3])
    if len(sizes(tree)) > 1: return None                                          # 葉が値 1 つの枝と並びの枝が混ざる形は、機械語が枝の種類を揃えられない(Int と並び)
    def enc(t):
        if t[0] == "leaf": return t[1][0] if len(t[1]) == 1 else ("flow", list(t[1]), "leaf")
        return ("tree", t[1], enc(t[2]), enc(t[3]))                                  # 葉がどれも単位でないので、`cases`(行)で出せる(`&` `|` の連鎖は並びの値を持てない)
    return enc(tree)

def raise_ast(funcs, top):
    """SIR を旧 AST の列にする。void の単位の読みが要る形(void になりうる被演算子・呼びの実引数)は Unsup。整数だけ。"""
    def blk(x): return ("block", x) if x[0] in ("bin", "cmp", "seq", "neg", "cases") else x
    check_textual(funcs, top)
    def r(e, in_flow):
        k = e[0]
        if k == "flt": raise Unsup("Float は機械語へ戻さない(機械語に FPU の値が無い)")
        if k in ("struct", "field"): raise Unsup("欄ブロック・欄引きは機械語へ戻せない(機械語に欄の表がない)")
        if k == "str": return ("lit", e[1])
        if k == "chr": return ("lit", Char(chr(e[1])))
        if k == "int": return ("lit", e[1]) if e[1] >= 0 else ("neg", ("lit", -e[1]))
        if k == "void": return ("id", "__")
        if k == "var": return ("id", e[1])
        def operand(x):
            if not nonvoid(x): raise Unsup("void の単位の読み(被演算子が void になりうる)")
            return blk(r(x, False))
        def maybe(x):                                                          # void になりうる被演算子: 二重に評価するので、呼びを含めない
            if has_call(x): raise Unsup("void になりうる被演算子が呼びを含む")
            return blk(r(x, False))
        def both(xs, inner):                                                   # 全部あれば inner、どれかが void なら void(`a & b & inner`)
            e = inner
            for x in reversed(xs): e = ("bin", "&", x, e)
            return e
        if k == "abs":                                                         # asm に絶対値の節は無い。`(x < 0 & 0 - x) | x`(void は void、0 は 0、負は符号反転)。x を 3 回評価するので呼びは戻さない
            if has_call(e[1]): raise Unsup("絶対値の被演算子が呼びを含む")
            x = blk(r(e[1], False))
            return ("block", ("bin", "|", ("block", ("bin", "&", ("cmp", [x, ("lit", 0)], ["<"]), ("bin", "-", ("lit", 0), x))), x))
        if k == "neg": return ("neg", blk(r(e[1], False)))
        if k == "op": return ("bin", e[1], blk(r(e[2], False)), blk(r(e[3], False)))      # asm の算術は void を単位として扱い、0 割りは void(bin_tail)。包みは要らない
        if k in ("cmp", "chain"):
            ts = [e[2], e[3]] if k == "cmp" else e[2]
            ops = [e[1]] if k == "cmp" else list(e[1])
            bs = [blk(r(t, False)) for t in ts]
            if k == "cmp" and ops[0] in ("!=", "!=="):                               # 補正 5: 既定の `!=` は void を「違う」と読むので、両方あるときだけ比べる(二重に評価するので呼びは戻さない)
                if not all(nonvoid(t) for t in ts) and any(has_call(t) for t in ts): raise Unsup("`!=` の void になりうる被演算子が呼びを含む")
                if not all(nonvoid(t) for t in ts): return ("bin", "&", ("bin", "==", bs[0], bs[0]), ("bin", "&", ("bin", "==", bs[1], bs[1]), ("cmp", bs, ops)))
            return ("cmp", bs, ops)
        if k == "and": return ("bin", "&", blk(r(e[1], False)), blk(r(e[2], False)))
        if k == "or": return ("bin", "|", blk(r(e[1], False)), blk(r(e[2], False)))
        if k == "tree":                                                            # plan_flow の場合分け: E が単位でなければ A、単位なら B。A も B も単位にならない
            return ("block", ("cases", [(blk(r(e[1], False)), blk(r(e[2], False))), (None, blk(r(e[3], False)))]))
        if k == "rows":
            rows = e[1]
            if any(c is not None and not nonvoid(v) for c, v in rows[:-1]) or (rows[-1][0] is not None and not nonvoid(rows[-1][1]) and len(rows) > 1 and False):
                # 値が void になりうる行は次の行へ落ちる(V10)。`cases` ではなく `(c & v) | 残り` の連鎖で表す(旧経路の補正 3 と同じ形)
                acc = None
                for c, v in reversed(rows):
                    cur = blk(r(v, False)) if c is None else ("bin", "&", blk(r(c, False)), blk(r(v, False)))
                    acc = cur if acc is None else ("bin", "|", ("block", cur), ("block", acc))
                return ("block", acc)
            return ("cases", [(None if c is None else blk(r(c, False)), blk(r(v, False))) for c, v in rows])
        if k == "call":
            if not e[2]: return ("id", e[1])
            if e[1] in getattr(funcs, "defaults", {}) and not all(nonvoid(x) for x in e[2]):
                raise Unsup("既定値のある関数の実引数が単位になりうる")           # 機械語は、単位の実引数を既定値で埋めず部分適用に読む(下の「既定値: 単位は既定値」の食い違い)。静的に単位でないと言えるときだけ戻す
            return ("seq", [("id", e[1])] + [blk(r(x, False)) for x in e[2]])          # void になりうる実引数は strict の部分適用。asm 側の strict_call_check が罠か断りにする
        if k == "list": return ("seq", [r(("int", v), False) for v in e[1]])
        if k == "idx": return ("bin", "'", blk(r(e[1], False)), blk(r(e[2], False)))
        if k == "len":
            x = e[1]
            if x[0] == "call" and x[2] and not all(nonvoid(t) for t in x[2]): raise Unsup("`||g 実引数||` の実引数が単位になりうる(余った関数のノルムは `!_`。機械語は 0)")
            return ("norm", blk(r(e[1], False)))
        if k == "fold":
            op = e[1]
            xs = [x for x in e[2] if x[0] != "void"]                                  # 字面の void は畳みで飛ばされる
            if not all(x[0] in ("int", "var") for x in xs): raise Unsup("畳みの実引数が整数の字面・名前でない")
            if not xs: return ("id", "__")
            if len(xs) == 1: return r(xs[0], False)
            if op in ("==", "="): return ("seq", [("sec", "fold", op, None, False)] + [r(x, False) for x in xs])
            acc = r(xs[0], False)
            for x in xs[1:]: acc = ("block", ("bin", "|", ("cmp", [acc, r(x, False)], [op]), r(x, False)))      # `a op b` は成り立てば a、外れれば void。`|` で右
            return acc
        if k == "flow":
            items = [x for x in e[1] if x[0] != "void"]                                # 字面の単位は並びで消える(`inc 2 zz` の余りの未定義の名前)
            if len(items) == len(e[1]) and len(items) >= 2 and len(e) == 2:                   # 3 つ目の要素は「場合分けの葉」の印(もう解いた)
                planned = plan_flow(funcs, items)                                       # 単位になりうる実引数・余った関数がある流れは、単位かどうかで場合分けした木にする(合成を機械語で正しく出す)
                if planned is not None: return r(planned, in_flow)
            if not items: return ("id", "__")
            if len(items) < len(e[1]): return r(("flow", items), in_flow)
            if len(e[1]) == 1: return r(e[1][0], in_flow)
            dfl = getattr(funcs, "defaults", {})
            if any(x[0] == "call" and x[1] in dfl for x in e[1]): raise Unsup("既定値のある関数の呼びが並びの中にある(余りの実引数が付く形。機械語が答えを誤る)")
            return ("seq", [blk(r(x, True)) for x in e[1]])                          # 流れ: 部分適用は asm の strict_call_check が枝を分けるか罠にする
        raise Unsup("旧 AST に戻せない形 " + k)
    out = []
    for name, (ps, body) in funcs.items():
        b = r(body, False)
        ds = getattr(funcs, "defaults", {}).get(name, [None] * len(ps))
        dd = lambda d: None if d is None else ("lit", d) if d >= 0 else ("neg", ("lit", -d))
        out.append(("def", name, ("lam", [("name", p, dd(d)) for p, d in zip(ps, ds)], b)) if ps else ("def", name, b))
    out.append(r(top, False))
    return out
