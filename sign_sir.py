"""Sign の strict 中間表現(SIR、第二段階)。
旧 AST(`parse_source` の木)は、既定の読みと strict の読みの両方のために作られていて、strict の答えは評価器の動きと、sign_asm の `strict_rewrite`・`strict_call_check` の継ぎはぎで合わせていた。
SIR は、strict の読みを**木の形そのものに書き出した**中間表現で、評価器とコード生成が同じ物を見る。
  ("int", n) / ("void",)                      値。整数は 64 ビット(範囲を出れば `!_`、value_spec V5)
  ("var", 名前)                                 仮引数(関数の本体の中)
  ("op", 記号, a, b)                            + - * / %。void の被演算子は単位で消える(`5 + _` は 5)。両方 void なら void。`/` `%` は割る数が 0 なら void(消えた void と同じ)
  ("neg", a)                                   符号反転。void は void のまま(`-_` は void。`0 - _` の 0 とは別)
  ("chain", [記号...], [項...])                  比べの連鎖: 3 項の範囲(`a < b < c` 等)は両方成り立てば真ん中の項、`=`・`==` だけの連鎖は全部等しければ最初の項。外れたら後ろの項は評価しない
  ("cmp", 記号, a, b)                           < > <= >= = == != !==。成り立てば a、外れ・どちらかが void なら void(R-rule、`a op b` は a か void)
  ("and", a, b) / ("or", a, b)                  `&`: a が void でなければ b、void なら void。`|`: a が void でなければ a、void なら b
  ("rows", [(条件 か None, 値), ...])             行の列: 条件が void でない最初の行の値。条件 None は最後の既定の行。当たる行が無ければ void
  ("call", 名前, [実引数...])                     関数の呼び。口の数ちょうど。実引数が 1 つでも void なら呼びは成り立たず(部分適用)、SIR の評価は ("partial",) を返す
  ("flow", [項...])                              並び(積)。void の項は消える。項が 1 つだけ残ればその項、0 ならvoid
SIR に下げられない形は Unsup を投げ、理由を持つ(未対応の数え方が、そのまま次の段の仕事の一覧になる)。"""
I64_MAX, I64_MIN = 2**63 - 1, -(2**63 - 1)     # 範囲の下は -MAX(MIN に着くのも `!_`、value_spec V5)

class Unsup(Exception):
    pass

def lower(nodes):
    """旧 AST の節の列 → ({関数名: (仮引数名の列, 本体の SIR)}, 最後の行の SIR か None)。下げられなければ Unsup"""
    funcs, arity = {}, {}
    for n in nodes:
        if n[0] == "def":
            if isinstance(n[2], tuple) and n[2][0] == "lam":
                if any(p[0] != "name" or p[2] is not None for p in n[2][1]): raise Unsup("括り・既定値の仮引数")
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
        raise Unsup("名前 " + n[1])
    if k == "bin":
        op = n[1]
        if op in ("+", "-", "*", "/", "%"): return ("op", op, expr(n[2], params, arity), expr(n[3], params, arity))
        if op == "&": return ("and", expr(n[2], params, arity), expr(n[3], params, arity))
        if op == "|": return ("or", expr(n[2], params, arity), expr(n[3], params, arity))
        if op == "'":
            if INFUNC[0]: raise Unsup("関数の中の添字(R24・R81 の形の見え方が未モデル)")
            return ("idx", expr(n[2], params, arity), expr(n[3], params, arity))
        if op in ("==", "!==", "!="): return ("cmp", op, expr(n[2], params, arity), expr(n[3], params, arity))
        raise Unsup("演算子 " + op)
    if k == "norm": return ("len", expr(n[1], params, arity))
    if k == "cmp":
        xs = [expr(x, params, arity) for x in n[1]]
        if len(xs) == 2: return ("cmp", n[2][0], xs[0], xs[1])
        ops = n[2]
        rng = all(o in ("<", "<=") for o in ops) or all(o in (">", ">=") for o in ops)
        if (len(xs) == 3 and rng) or all(o == "=" for o in ops) or all(o == "==" for o in ops): return ("chain", list(ops), xs)
        raise Unsup("比べの連鎖の形(R119)")
    if k == "cases":
        return ("rows", [(None if c is None else expr(c, params, arity), expr(v, params, arity)) for c, v in n[1]])
    if k == "seq":
        items = n[1]
        h = unblock(items[0])
        if h[0] == "id" and h[1] in arity and h[1] not in params:
            a = arity[h[1]]
            args = [expr(x, params, arity) for x in items[1:1 + a]]
            if len(args) < a: raise Unsup("部分適用(口が足りない)")
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
    class Partial(Exception): pass
    class Fuel(Exception): pass
    def ev(e, env):
        steps[0] += 1
        if steps[0] > fuel: raise Fuel()
        k = e[0]
        if k == "int": return e[1]
        if k == "void": return None
        if k == "var": return env[e[1]]
        if k == "op":
            a, b = ev(e[2], env), ev(e[3], env)
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
            a, b = ev(e[2], env), ev(e[3], env)
            if isinstance(a, tuple) or isinstance(b, tuple): raise Unsup("リストの比べ")
            if a is None or b is None: return None
            op = e[1]
            ok = {"<": a < b, ">": a > b, "<=": a <= b, ">=": a >= b, "=": a == b, "==": a == b, "!=": a != b, "!==": a != b}[op]
            return a if ok else None
        if k == "list": return e[1]
        if k == "len":
            a = ev(e[1], env)
            if a is None: return None
            if not isinstance(a, tuple): raise Unsup("整数の長さ")
            return len(a)
        if k == "idx":
            a, i = ev(e[1], env), ev(e[2], env)
            if a is None or i is None: return None
            if not isinstance(a, tuple) or isinstance(i, tuple): raise Unsup("添字の型")
            if i < 0: i += len(a)
            return a[i] if 0 <= i < len(a) else None
        if k == "neg":
            a = ev(e[1], env)
            if isinstance(a, tuple): raise Unsup("リストの符号")
            return None if a is None else clamp(-a)
        if k == "chain":
            ts, ops = e[2], e[1]
            vals = []
            for i, t in enumerate(ts):
                v = ev(t, env)
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
            return None if a is None else ev(e[2], env)
        if k == "or":
            a = ev(e[1], env)
            return a if a is not None else ev(e[2], env)
        if k == "rows":
            for c, v in e[1]:
                if c is None or ev(c, env) is not None: return ev(v, env)
            return None
        if k == "call":
            args = [ev(x, env) for x in e[2]]
            if any(x is None for x in args): raise Partial()
            ps, body = funcs[e[1]]
            return ev(body, dict(zip(ps, args)))
        if k == "flow":
            vs = [v for v in (ev(x, env) for x in e[1]) if v is not None]
            if len(vs) > 1: raise Unsup("複数の値の並び")
            return vs[0] if vs else None
        raise Unsup("SIR " + k)
    try:
        v = ev(top, {})
    except Partial: return ("partial",)
    except Fuel: return ("fuel",)
    except RecursionError: return ("fuel",)
    if isinstance(v, tuple): raise Unsup("リストの値")
    return ("void",) if v is None else ("val", v)
