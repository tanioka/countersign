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
  ("flow", [項...])                              並び(積)。void の項は消える。項が 1 つだけ残ればその項、0 ならvoid
SIR に下げられない形は Unsup を投げ、理由を持つ(未対応の数え方が、そのまま次の段の仕事の一覧になる)。"""
I64_MAX, I64_MIN = 2**63 - 1, -(2**63 - 1)     # 範囲の下は -MAX(MIN に着くのも `!_`、value_spec V5)

class Unsup(Exception):
    pass

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
        if not isinstance(n[1], int) or isinstance(n[1], bool): raise Unsup("整数でない字面")
        return ("int", n[1])
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
            if key[0] == "id" and key[1] != "__":                                  # R64: 鍵の名前は欄の名前。値の名前でも `!_`
                return ("idx", expr(n[2], params, arity), ("void",))
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
    def ev(e, env):
        steps[0] += 1
        if steps[0] > fuel: raise Fuel()
        k = e[0]
        if k == "int": return e[1]
        if k == "void": return None
        if k == "var": return env[e[1]]
        if k == "op":
            a, b = one(ev(e[2], env)), one(ev(e[3], env))
            if isinstance(a, tuple) or isinstance(b, tuple): raise Unsup("リストの算術")
            if a is None or b is None: return b if a is None else a
            op = e[1]
            if op == "+": return clamp(a + b)
            if op == "-": return clamp(a - b)
            if op == "*": return clamp(a * b)
            if b == 0: return None
            q = abs(a) // abs(b) * (1 if (a >= 0) == (b >= 0) else -1)         # 0 へ丸める(value_spec の除算)
            return clamp(q) if op == "/" else clamp(a - q * b)
        if k == "cmp":
            a, b = one(ev(e[2], env)), one(ev(e[3], env))
            if isinstance(a, tuple) or isinstance(b, tuple): raise Unsup("リストの比べ")
            if a is None or b is None: return None
            op = e[1]
            ok = {"<": a < b, ">": a > b, "<=": a <= b, ">=": a >= b, "=": a == b, "==": a == b, "!=": a != b, "!==": a != b}[op]
            return a if ok else None
        if k == "fold":
            vs = [v for v in (one(ev(x, env)) for x in e[2]) if v is not None]
            if any(isinstance(v, tuple) for v in vs): raise Unsup("リストの畳み")
            if not vs: return None
            op = e[1]
            if op in ("==", "="): return vs[0] if all(v == vs[0] for v in vs) else None
            acc = vs[0]
            for b in vs[1:]:
                acc = acc if {"<": acc < b, ">": acc > b, "<=": acc <= b, ">=": acc >= b}[op] else b
            return acc
        if k == "list": return e[1]
        if k == "len":
            a = one(ev(e[1], env))
            if a is None: return 0                                              # `||_||` は 0(value_spec 83 行、U〔答え〕2026-10-28 00:17)。以前は単位にしていて、strict と食い違った
            if not isinstance(a, tuple): raise Unsup("整数の長さ")
            return len(a)
        if k == "idx":
            a, i = one(ev(e[1], env)), one(ev(e[2], env))
            if a is None or i is None: return None
            if not isinstance(a, tuple) or isinstance(i, tuple): raise Unsup("添字の型")
            if i < 0: i += len(a)
            return a[i] if 0 <= i < len(a) else None
        if k == "abs":
            a = one(ev(e[1], env))
            if isinstance(a, tuple): raise Unsup("リストの絶対値")
            return None if a is None else abs(a)
        if k == "neg":
            a = one(ev(e[1], env))
            if isinstance(a, tuple): raise Unsup("リストの符号")
            return None if a is None else clamp(-a)
        if k == "chain":
            ts, ops = e[2], e[1]
            vals = []
            for i, t in enumerate(ts):
                v = one(ev(t, env))
                if isinstance(v, tuple): raise Unsup("リストの比べ")
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
            return None if a is None else ev(e[2], env)
        if k == "or":
            a = ev(e[1], env)
            if isinstance(a, (PF, Flow)): raise Unsup("部分適用・並びを | の左に置く")
            return a if a is not None else ev(e[2], env)
        if k == "rows":
            for c, v in e[1]:                                                  # 行は `c & v | 次の行`(value_spec V10)。v が void なら次の行へ落ちる
                if c is None or one(ev(c, env)) is not None:
                    r = ev(v, env)
                    if isinstance(r, PF): raise Unsup("行の値が部分適用")
                    if r is not None: return r
            return None
        if k == "call":
            args = []
            for x in e[2]:
                v = ev(x, env)
                if isinstance(v, (PF, Flow)): raise Unsup("実引数が部分適用・並び")
                args.append(v)
            ds = getattr(funcs, "defaults", {}).get(e[1])
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
                items.extend(v) if isinstance(v, Flow) else items.append(v)
            out = []
            for it in reversed(items):                                          # 右から左へ。部分適用は後ろの値を受け取る(足りなければ全部受けて消える)
                if isinstance(it, PF):
                    if len(out) >= it.need:
                        v = run_call(it.f, it.args + out[:it.need]); rest = out[it.need:]
                        out = (list(v) if isinstance(v, Flow) else [] if v is None else [v]) + rest
                    else: out = []
                else: out.insert(0, it)
            return None if not out else out[0] if len(out) == 1 else Flow(out)
        raise Unsup("SIR " + k)
    try:
        v = ev(top, {})
    except Fuel: return ("fuel",)
    except RecursionError: return ("fuel",)
    if isinstance(v, PF): v = None                                              # 余った関数は消える
    if isinstance(v, Flow): return ("flow", tuple(v))
    if isinstance(v, tuple): return ("flow", v)                                 # 整数の並び(リスト)は流れと同じ字で出る
    return ("void",) if v is None else ("val", v)

# ---- SIR → 旧 AST(段階 C の試作): strict_rewrite を通さずに generate へ渡せる木を、SIR から作る ----
def nonvoid(e):
    """e は void にならない(被演算子に置いても単位の読みが要らない)と静的に言える。"""
    k = e[0]
    if k in ("int", "var"): return True
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

def raise_ast(funcs, top):
    """SIR を旧 AST の列にする。void の単位の読みが要る形(void になりうる被演算子・呼びの実引数)は Unsup。整数だけ。"""
    def blk(x): return ("block", x) if x[0] in ("bin", "cmp", "seq", "neg", "cases") else x
    def r(e, in_flow):
        k = e[0]
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
        if k == "len": return ("norm", blk(r(e[1], False)))
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
            if not items: return ("id", "__")
            if len(items) < len(e[1]): return r(("flow", items), in_flow)
            if len(e[1]) == 1: return r(e[1][0], in_flow)
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
