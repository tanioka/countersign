"""Sign の strict 中間表現(SIR、第二段階)。
旧 AST(`parse_source` の木)は、既定の読みと strict の読みの両方のために作られていて、strict の答えは評価器の動きと、sign_asm の `strict_rewrite`・`strict_call_check` の継ぎはぎで合わせていた。
SIR は、strict の読みを**木の形そのものに書き出した**中間表現で、評価器とコード生成が同じ物を見る。
  ("int", n) / ("void",)                      値。整数は 64 ビット(範囲を出れば `!_`、value_spec V5)
  ("var", 名前)                                 仮引数(関数の本体の中)
  ("op", 記号, a, b)                            + - * / %。void の被演算子は単位で消える(`5 + _` は 5)。両方 void なら void。`/` `%` は割る数が 0 なら void(消えた void と同じ)
  ("fold", 記号, [項...])                      `[>] a b c` などの畳み: void は飛ばし、`<` `>` `<=` `>=` は残りを `(a op b) | b` で畳む(最小・最大)、`==` `=` は全部等しければその値、違えば void
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
            key = unblock(n[3])
            if key[0] == "post" and key[1] == "~": key = unblock(key[2])
            if key[0] == "id" and key[1] != "__":                                  # R64: 鍵の名前は欄の名前。値の名前でも `!_`
                return ("idx", expr(n[2], params, arity), ("void",))
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
        if k == "fold":
            vs = [v for v in (ev(x, env) for x in e[2]) if v is not None]
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
            for c, v in e[1]:                                                  # 行は `c & v | 次の行`(value_spec V10)。v が void なら次の行へ落ちる
                if c is None or ev(c, env) is not None:
                    r = ev(v, env)
                    if r is not None: return r
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

# ---- SIR → 旧 AST(段階 C の試作): strict_rewrite を通さずに generate へ渡せる木を、SIR から作る ----
def nonvoid(e):
    """e は void にならない(被演算子に置いても単位の読みが要らない)と静的に言える。"""
    k = e[0]
    if k in ("int", "var"): return True
    if k == "neg": return nonvoid(e[1])
    if k == "op":
        if not (nonvoid(e[2]) and nonvoid(e[3])): return False
        if e[1] in ("/", "%"): return e[3][0] == "int" and e[3][1] != 0
        return True
    return False

def has_call(e):
    if not isinstance(e, tuple): return False
    if e[0] == "call": return True
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
        if k == "rows": return ("cases", [(None if c is None else blk(r(c, False)), blk(r(v, False))) for c, v in e[1]])
        if k == "call":
            if not e[2]: return ("id", e[1])
            return ("seq", [("id", e[1])] + [blk(r(x, False)) for x in e[2]])          # void になりうる実引数は strict の部分適用。asm 側の strict_call_check が罠か断りにする
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
        if k == "flow" and len(e[1]) == 1: return r(e[1][0], in_flow)
        raise Unsup("旧 AST に戻せない形 " + k)
    out = []
    for name, (ps, body) in funcs.items():
        b = r(body, False)
        out.append(("def", name, ("lam", [("name", p, None) for p in ps], b)) if ps else ("def", name, b))
    out.append(r(top, False))
    return out
