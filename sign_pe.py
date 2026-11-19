"""sign_pe.py : 部分計算(partial computation)と一般部分計算(GPC)による、処理系の最適化。

言語の意味は変えない。構文木を「残余プログラム」に書き換えるだけで、元の木と同じ値・同じ副作用を返す
(test_pe.py が、最適化の有る無しで結果を突き合わせる)。使うには  python3 sign_interp.py prog.sn --opt

やること(すべて、結果が確かに同じになる所だけ):
  1. 定数伝播     先頭の定義だけが並ぶ区間の `NAME : 整数リテラル` を、使う所へ埋める
                  (同名の束縛が他に無く、`$NAME` で番地を取られていないもの)
  2. 畳み込み     整数リテラルどうしの + - * 比較 & | と `!` を、処理系自身の binop で計算して置き換える
  3. 部分計算     純粋な大域関数に、整数(か __)のリテラルだけを渡す呼び出しを、燃料つきで先に実行して値にする
                  (副作用が無い関数だけ。燃料が尽きる・エラー・警告が出る呼び出しは、そのまま残す)
  4. GPC         `cond : expr` の行の中では cond が真だと分かる。その事実(n > 0 など)を行の中へ運び、
                  中にある同じ変数への比較を、区間の証明で 真/偽 に決めて、行ごと畳む・消す
                  (負の事実 ── 前の行が偽 ── は、変数が数だと分かっている時だけ使う)

使わないもの: 演算子の再定義(opdef)・import・`$` で番地を取られた名前のある所は、何もせずに元の木を返す。"""

KEEP = []                                      # 古い節を生かしておく(POS は id() で引くので、番号の使い回しを防ぐ)
STATS = {}
PURE_OPS = {"+", "-", "*", "/", "%", "^", "&", "|", "<", "<=", "=", "==", ">=", ">", "!=", "!==", ";"}
FOLD_OPS = {"+", "-", "*", "&", "|", "<", "<=", "=", "==", ">=", ">", "!=", "!=="}
CMP_OPS = {"<", "<=", ">", ">="}
FLIP = {"<": ">", "<=": ">=", ">": "<", ">=": "<="}
NEG = {"<": ">=", "<=": ">", ">": "<=", ">=": "<"}
INF = float("inf")


def count(k, n=1): STATS[k] = STATS.get(k, 0) + n


def nodes_of(x):
    """木の中のすべての節(先頭が文字列のタプル)を巡る。"""
    if isinstance(x, tuple):
        if x and isinstance(x[0], str): yield x
        for y in x: yield from nodes_of(y)
    elif isinstance(x, list):
        for y in x: yield from nodes_of(y)


def spec_names(sp):
    if sp[0] == "name": return [sp[1]]
    return list(sp[1]) + list(sp[4] if len(sp) > 4 else []) + ([sp[2]] if sp[2] else [])


def bound_names(tree):
    """tree の中で束縛されるすべての名前(def・仮引数)と、その回数。"""
    cnt = {}
    for n in nodes_of(tree):
        if n[0] == "def": cnt[n[1]] = cnt.get(n[1], 0) + 1
        elif n[0] == "lam":
            for sp in n[1]:
                for nm in spec_names(sp): cnt[nm] = cnt.get(nm, 0) + 1
    return cnt


def addr_names(tree):
    """`$…` の中に現れる名前(番地を取られる名前は、後から書き換わりうるので定数にしない)。"""
    out = set()
    for n in nodes_of(tree):
        if n[0] == "addr":
            for m in nodes_of(n[1]):
                if m[0] == "id": out.add(m[1])
    return out


# ---- 区間 ------------------------------------------------------------------------------------------
# 区間 (lo, lo_closed, hi, hi_closed) : 実数の範囲。比較が真だった変数は数(整数か小数)なので、実数で考えてよい。
FULL = (-INF, False, INF, False)


def region(op, c):
    if op == "<": return (-INF, False, c, False)
    if op == "<=": return (-INF, False, c, True)
    if op == ">": return (c, False, INF, False)
    return (c, True, INF, False)                   # >=


def meet(a, b):
    lo, loc = (a[0], a[1]) if (a[0], a[1]) > (b[0], b[1]) else (b[0], b[1])    # 同じ値なら閉でないほうが強い
    if a[0] == b[0]: loc = a[1] and b[1]
    hi, hic = (a[2], a[3]) if (a[2], a[3]) < (b[2], b[3]) else (b[2], b[3])
    if a[2] == b[2]: hic = a[3] and b[3]
    return (lo, loc, hi, hic)


def empty(a):
    return a[0] > a[2] or (a[0] == a[2] and not (a[1] and a[3]))


def inside(a, r):                                  # a ⊆ r
    lo_ok = a[0] > r[0] or (a[0] == r[0] and (r[1] or not a[1]))
    hi_ok = a[2] < r[2] or (a[2] == r[2] and (r[3] or not a[3]))
    return lo_ok and hi_ok


def unlit(n):
    """リテラルの整数(か書き込めない UNIT)を取り出す。ブロックは外す。無ければ None。"""
    while n[0] == "block": n = n[1]
    if n[0] == "lit" and type(n[1]) is int: return n
    return None


def cmp_fact(n):
    """純粋な比較 `名前 op 整数` を (名前, op, c) にする(向きは 名前 が左)。他は None。"""
    while n[0] == "block": n = n[1]
    if n[0] != "cmp" or len(n[2]) != 1: return None
    op = n[2][0]
    if op not in CMP_OPS: return None
    a, b = n[1]
    while a[0] == "block": a = a[1]
    while b[0] == "block": b = b[1]
    if a[0] == "id" and b[0] == "lit" and type(b[1]) is int: return (a[1], op, b[1])
    if b[0] == "id" and a[0] == "lit" and type(a[1]) is int: return (b[1], FLIP[op], a[1])
    return None


def facts_of(cond):
    """cond が(非 Unit で)真だと分かる事実 [(名前, op, c), …]。"""
    while cond[0] == "block": cond = cond[1]
    if cond[0] == "cmp":
        ops = cond[2]
        if any(o not in CMP_OPS for o in ops): return []
        out = []
        for i, o in enumerate(ops):
            f = cmp_fact(("cmp", [cond[1][i], cond[1][i + 1]], [o]))
            if f: out.append(f)
        return out
    if cond[0] == "bin" and cond[1] == "&": return facts_of(cond[2]) + facts_of(cond[3])
    return []


def with_fact(facts, f):
    name, op, c = f
    new = dict(facts)
    new[name] = meet(facts.get(name, FULL), region(op, c))
    return new


def decide(cond, facts):
    """facts の下で、純粋な比較 cond が 真(True)・偽(False)・不明(None)。"""
    f = cmp_fact(cond)
    if not f or f[0] not in facts: return None
    iv, r = facts[f[0]], region(f[1], f[2])
    if empty(iv): return None
    if inside(iv, r): return True
    if empty(meet(iv, r)): return False
    return None


# ---- 書き換え --------------------------------------------------------------------------------------
class PE:
    def __init__(self, S, nodes):
        self.S, self.nodes = S, nodes
        self.consts, self.pure, self.defs = {}, {}, {}
        self.fuel_total = 200000
        self.scratch = None

    def mk(self, old, new):
        p = self.S.POS.get(id(old))
        if p: self.S.POS[id(new)] = p
        KEEP.append(old)
        return new

    def lit(self, old, v, tag=None):
        n = ("lit", v) if tag is None else ("lit", v, tag)
        p = self.S.POS.get(id(old))
        if p: self.S.POS[id(n)] = p
        KEEP.append(old)
        return n

    # --- 前提の調べ
    def feasible(self):
        S = self.S
        if S.OVERRIDES: return False
        for n in nodes_of(self.nodes):
            if n[0] in ("opdef", "importspread"): return False
            if n[0] == "bin" and n[1] == "@" and n[2][0] == "lit" and isinstance(n[2][1], str): return False
        return True

    def analyse(self):
        nodes = self.nodes
        bcount, banned = bound_names(nodes), addr_names(nodes)
        for n in nodes:                                     # 全体で一度だけ巡る(大域関数の候補)
            if n[0] == "def" and n[2][0] == "lam" and bcount.get(n[1]) == 1 and n[1] not in banned:
                self.defs[n[1]] = n[2]
        for n in nodes:                                     # 先頭の「定義だけ」の区間 ── ここでは何も呼ばれない
            if n[0] != "def": break
            if n[2][0] == "lam": continue
            v = self.fold_expr(n[2])
            lit = unlit(v)
            if lit is not None and len(lit) > 2 and lit[2] in ("Address", "UInt"):
                continue                                    # `k : 0x4` の名前は番地の顔を持つ(渡し先で読まれる)ので、字面に置き換えない
            if lit is not None and bcount.get(n[1]) == 1 and n[1] not in banned and n[1] not in self.defs:
                self.consts[n[1]] = lit
            elif n[2][0] != "lit" and lit is None: break
        # 純粋な大域関数の不動点
        cand = set(self.defs)
        changed = True
        while changed:
            changed = False
            for nm in list(cand):
                if not self.pure_lam(self.defs[nm], cand):
                    cand.discard(nm); changed = True
        self.pure = {nm: self.defs[nm] for nm in cand}
        self.bcount, self.banned = bcount, banned

    def pure_lam(self, lam, cand, outer=frozenset()):
        names = set(outer)
        for sp in lam[1]:
            if sp[0] != "name": return False
            names.add(sp[1])
            if sp[2] is not None and not self.pure_node(sp[2], cand, names): return False
        for m in nodes_of(lam[2]):                          # 本体の中の束縛はすべて見える名前として許す
            if m[0] == "def": names.add(m[1])
            elif m[0] == "lam":
                for sp in m[1]:
                    if sp[0] != "name": return False
                    names.add(sp[1])
        return self.pure_node(lam[2], cand, names)

    def pure_node(self, n, cand, names):
        k = n[0]
        if k == "lit": return True
        if k == "hole": return True
        if k == "id": return n[1] in names or n[1] in cand or n[1] in self.consts or n[1] == "__"
        if k == "bin": return n[1] in PURE_OPS and self.pure_node(n[2], cand, names) and self.pure_node(n[3], cand, names)
        if k in ("block", "not", "neg", "bnot", "abs"): return self.pure_node(n[1], cand, names)
        if k in ("seq", "prod"): return all(self.pure_node(m, cand, names) for m in n[1])
        if k == "cmp": return all(self.pure_node(m, cand, names) for m in n[1])
        if k == "cases":
            return all((c is None or self.pure_node(c, cand, names)) and self.pure_node(e, cand, names) for c, e in n[1])
        if k == "def": return self.pure_node(n[2], cand, names)
        if k == "lam": return self.pure_lam(n, cand, names)
        return False

    # --- 畳み込み
    def fold_expr(self, n):
        """定数だけの式の値(リテラル節)を試す。substitution は 先頭区間の定義の計算にだけ使う。"""
        return self.rec(n, {}, frozenset(), in_prod=False, use_consts=True)

    def fold_bin(self, n, l, r):
        S = self.S
        if n[1] not in FOLD_OPS: return None
        a, b = unlit_or_unit(l), unlit_or_unit(r)
        if a is None or b is None: return None
        try:
            v = S.binop(n[1], a[1], lambda: b[1])
        except Exception:
            return None
        if type(v) is int or v is S.UNIT: return self.lit(n, v)
        return None

    # --- 本体
    def rec(self, n, facts, tracked, in_prod=False, use_consts=True):
        k = n[0]
        if k == "lit" or k == "hole": return n
        if k == "id":
            c = self.consts.get(n[1]) if use_consts else None
            if c is not None:
                count("const")
                return c
            return n
        if k == "bin":
            op = n[1]
            if op in ("'", "@"): return n
            l = self.rec(n[2], facts, tracked, use_consts=use_consts)
            fr = facts
            if op == "&":
                for f in facts_of(l):
                    if f[0] in tracked: fr = with_fact(fr, f)
            if op in ("&", "|") and facts:                    # 左が(事実から)真・偽と決まるなら、&・| は片方になる
                d = decide(l, facts)
                if d is not None:
                    count("gpc")
                    if op == "&":
                        return self.rec(n[3], fr, tracked, use_consts=use_consts) if d else self.lit(n, self.S.UNIT)
                    return l if d else self.rec(n[3], fr, tracked, use_consts=use_consts)
            r = self.rec(n[3], fr, tracked, use_consts=use_consts)
            _addr = any(isinstance(x, tuple) and x[0] == "lit" and len(x) > 2 and x[2] in ("Address", "UInt") for x in (l, r))        # R62: `0x… ± 0x…` は字面の和として番地の顔を持つので畳まない
            v = None if _addr else self.fold_bin(n, l, r)
            if v is not None: count("fold"); return v
            if l is n[2] and r is n[3]: return n
            return self.mk(n, ("bin", op, l, r))
        if k == "block":
            i = self.rec(n[1], facts, tracked, use_consts=use_consts)
            return n if i is n[1] else self.mk(n, ("block", i))
        if k == "seq":
            items = [self.rec(m, facts, tracked, use_consts=use_consts) for m in n[1]]
            new = n if all(a is b for a, b in zip(items, n[1])) else self.mk(n, ("seq", items))
            if not in_prod and use_consts:
                v = self.static_call(new)
                if v is not None: return v
            return new
        if k == "prod":
            items = [self.rec(m, facts, tracked, in_prod=True, use_consts=use_consts) for m in n[1]]
            return n if all(a is b for a, b in zip(items, n[1])) else self.mk(n, ("prod", items))
        if k == "cmp":
            ops = [self.rec(m, facts, tracked, use_consts=use_consts) for m in n[1]]
            new = n if all(a is b for a, b in zip(ops, n[1])) else self.mk(n, ("cmp", ops, n[2]))
            if len(n[2]) == 1:
                v = self.fold_bin(("bin", n[2][0]), ops[0], ops[1])
                if v is not None:
                    count("fold"); return self.lit(n, v[1])
            return new
        if k == "not":
            i = self.rec(n[1], facts, tracked, use_consts=use_consts)
            u = unlit_or_unit(i)
            if u is not None:
                v = self.S.logical_not(u[1])
                if type(v) is int or v is self.S.UNIT:
                    count("fold"); return self.lit(n, v)
            return n if i is n[1] else self.mk(n, ("not", i))
        if k in ("neg", "bnot"):
            i = self.rec(n[1], facts, tracked, use_consts=use_consts)
            return n if i is n[1] else self.mk(n, (k, i))
        if k == "def":
            r = self.rec(n[2], facts, tracked, use_consts=use_consts)
            return n if r is n[2] else self.mk(n, ("def", n[1], r))
        if k == "lam": return self.rec_lam(n, facts)
        if k == "cases": return self.rec_cases(n, facts, tracked, use_consts)
        return n

    def rec_lam(self, n, facts):
        bound = set()
        for sp in n[1]: bound.update(spec_names(sp))
        inner_facts = {a: b for a, b in facts.items() if a not in bound}
        # 追跡する名前: 単純な仮引数で、本体の中で他に束縛されず、番地も取られていないもの
        inner = bound_names(n[2])
        tracked = frozenset(sp[1] for sp in n[1] if sp[0] == "name" and sp[1] not in inner and sp[1] not in self.banned)
        body = self.rec(n[2], inner_facts, tracked)
        return n if body is n[2] else self.mk(n, ("lam", n[1], body))

    def rec_cases(self, n, facts, tracked, use_consts):
        if self.S.STRICT_GATES and len(n[1]) >= 2 and all(c is None for c, _ in n[1]): return n    # R76: 2行以上の枝の無い本体は手続き(各行を評価する所として読む)なので触らない
        if any(c is not None and c[0] == "id" for c, _ in n[1]): return n    # R80: 局所の定義の行かもしれない本体は触らない
        rows, cur, changed = [], dict(facts), False
        for cond, expr in n[1]:
            if cond is None:
                e = self.rec(expr, cur, tracked, use_consts=use_consts)
                rows.append((None, e)); changed |= e is not expr
                break
            c = self.rec(cond, cur, tracked, use_consts=use_consts)
            d = None
            u = unlit_or_unit(c)
            if u is not None: d = not self.S.is_unit(u[1])
            else:
                f = cmp_fact(c)
                if f and f[0] in tracked: d = decide(c, cur)
            if d is False:
                count("row-dead"); count("gpc") if u is None else None; changed = True; continue
            row_facts = cur
            if d is True:
                count("row-true"); count("gpc") if u is None else None; changed = True
                e = self.rec(expr, cur, tracked, use_consts=use_consts)
                rows.append((None, e)); break
            for f in facts_of(c):
                if f[0] in tracked: row_facts = with_fact(row_facts, f)
            e = self.rec(expr, row_facts, tracked, use_consts=use_consts)
            rows.append((c, e)); changed |= (c is not cond) or (e is not expr)
            f = cmp_fact(c)                                   # 負の事実は、すでに数だと分かっている変数にだけ
            if f and f[0] in tracked and f[0] in cur and not empty(cur[f[0]]):
                cur = with_fact(cur, (f[0], NEG[f[1]], f[2]))
        if not changed and len(rows) == len(n[1]): return n
        if not rows: return self.lit(n, self.S.UNIT)
        if rows[0][0] is None: return rows[0][1]
        return self.mk(n, ("cases", rows))

    # --- 部分計算(静的な呼び出し)
    def static_call(self, n):
        S = self.S
        items = n[1]
        if len(items) < 2 or items[0][0] != "id" or items[0][1] not in self.pure: return None
        args = items[1:]
        if any(unlit_or_unit(a) is None for a in args): return None
        if self.fuel_total <= 0: return None
        if self.scratch is None and not self.build_scratch(): return None
        w0, lo0 = len(S.WARNINGS), S.LEFTOVERS[0]
        S.FUEL[0] = min(3000, self.fuel_total)
        start = S.FUEL[0]
        try:
            r = S.ev(n, self.scratch)
        except (Exception, S.OutOfFuel):
            r = None
        finally:
            used = start - (S.FUEL[0] if S.FUEL[0] is not None else 0)
            self.fuel_total -= max(used, 1)
            S.FUEL[0] = None
        if len(S.WARNINGS) != w0 or S.LEFTOVERS[0] != lo0:        # 実行時に出るはずの警告は、消さない
            del S.WARNINGS[w0:]; S.LEFTOVERS[0] = lo0
            return None
        if type(r) is int or r is S.UNIT:
            count("static-call")
            return self.lit(n, r)
        return None

    def build_scratch(self):
        S = self.S
        env = S.Env()
        w0, lo0 = len(S.WARNINGS), S.LEFTOVERS[0]
        try:
            for nm, lit in self.consts.items(): env.set(nm, lit[1])
            for nm, lam in self.pure.items(): env.set(nm, S.Closure(params=lam[1], body=lam[2], env=env))
        except Exception:
            return False
        finally:
            del S.WARNINGS[w0:]; S.LEFTOVERS[0] = lo0
        self.scratch = env
        return True


def unlit_or_unit(n):
    while n[0] == "block": n = n[1]
    if n[0] == "lit" and (type(n[1]) is int or n[1] is _UNIT[0]): return n
    return None


_UNIT = [None]


def _unwrap(n):
    while isinstance(n, tuple) and n and (n[0] == "block" and not isinstance(n[1], list) or (n[0] == "seq" and len(n[1]) == 1)):
        n = n[1] if n[0] == "block" else n[1][0]
    return n


def _simple(n, ps):
    """整数の仮引数と整数リテラルだけの + - * (副作用も警告も無く、整数どうしなら型も変わらない)。"""
    n = _unwrap(n)
    if not (isinstance(n, tuple) and n): return False
    if n[0] == "lit": return type(n[1]) is int and len(n) == 2
    if n[0] == "id": return n[1] in ps
    if n[0] == "bin" and n[1] in ("+", "-", "*"): return _simple(n[2], ps) and _simple(n[3], ps)
    return False


def _simple_cond(n, ps):
    n = _unwrap(n)
    if n[0] == "cmp": return all(_simple(x, ps) for x in n[1])
    if n[0] == "bin" and n[1] in CMP_OPS | {"=", "==", "!=", "!=="}: return _simple(n[2], ps) and _simple(n[3], ps)
    return False


def _has(n, f):
    return any(m[0] == "id" and m[1] == f for m in nodes_of(n))


def _call(n, f, k, ps):
    n = _unwrap(n)
    if isinstance(n, tuple) and n and n[0] == "seq" and len(n[1]) == k + 1 and n[1][0] == ("id", f) and all(_simple(a, ps) for a in n[1][1:]): return n[1][1:]
    return None


def accumulate(node):
    """アキュムレータ導入: `f : p… ?` の本体が、(条件 : 基底 / 条件 : E + f(…) か E * f(…) / 条件 : f(…)) と最後の既定の行だけなら、
    累積版 `f%acc : p… %acc ?` を作り、f が整数だけで呼ばれた時に累積版の末尾再帰へ回す(整数の + と * は結合的で可換なので、
    E を積む順が変わっても同じ値。整数でない・個数が違う呼び出しは元の本体を走らせる)。深い非末尾再帰が、呼びの積み上がり無しで走る。"""
    if node[0] != "def" or node[2][0] != "lam" or node[2][2][0] != "cases": return None
    f, lam = node[1], node[2]
    if any(sp[0] != "name" or sp[2] is not None for sp in lam[1]): return None
    ps = [sp[1] for sp in lam[1]]; k = len(ps)
    if "%acc" in ps or not ps: return None
    rows = lam[2][1]
    if not rows or rows[-1][0] is not None or any(c is None for c, _ in rows[:-1]): return None
    op, out = None, []
    for c, e in rows:
        if c is not None and (_has(c, f) or not _simple_cond(c, ps)): return None
        u = _unwrap(e)
        if not _has(e, f):
            if not _simple(e, ps): return None
            out.append((c, "base", e)); continue
        a = _call(e, f, k, ps)
        if a is not None: out.append((c, "tail", a)); continue
        if not (isinstance(u, tuple) and u[0] == "bin" and u[1] in ("+", "*")): return None
        l, r = u[2], u[3]
        for call, other in ((r, l), (l, r)):
            a = _call(call, f, k, ps)
            if a is not None and not _has(other, f) and _simple(other, ps):
                if op not in (None, u[1]): return None
                op = u[1]; out.append((c, "rec", (a, other))); break
        else: return None
    if op is None: return None
    hid = f + "%acc"
    A = ("id", "%acc")
    def call(args, acc): return ("seq", [("id", hid)] + list(args) + [("block", acc)])
    new = []
    for c, kind, x in out:
        if kind == "base": new.append((c, ("bin", op, A, ("block", x))))
        elif kind == "tail": new.append((c, call(x, A)))
        else: new.append((c, call(x[0], ("bin", op, A, ("block", x[1])))))
    hnode = ("def", hid, ("lam", [("name", p, None) for p in ps] + [("name", "%acc", None)], ("cases", new)))
    return hnode[2], hid, (0 if op == "+" else 1)


# ---- 案2 インライン展開・案1 使われない局所の定義の除去と共通部分式(重複した純粋な呼び出し) ----
def _atom_lit(n):
    return n[0] == "lit" and len(n) == 2 and type(n[1]) in (int, float, str)


def _size(n):
    return sum(1 for _ in nodes_of(n))


def _rebuild(n, f):
    """節の子を f で写す。何も変わらなければ元の節をそのまま返す(POS の id を保つ)。"""
    if isinstance(n, list):
        new = [f(c) for c in n]
        return n if all(a is b for a, b in zip(new, n)) else new
    if isinstance(n, tuple):
        new = tuple(f(c) if (isinstance(c, (tuple, list))) else c for c in n)
        return n if all(a is b for a, b in zip(new, n)) else new
    return n


def inline_candidates(pe):
    """インライン展開できる大域関数: 仮引数は素の名前だけ、本体は仮引数・数の字面・+ - * だけの1つの式で小さい。"""
    out = {}
    for nm, lam in pe.defs.items():
        if any(sp[0] != "name" or sp[2] is not None for sp in lam[1]) or not lam[1]: continue
        ps = {sp[1] for sp in lam[1]}
        body = lam[2]
        ok = _size(body) <= 15
        def good(m):
            if m[0] == "lit": return _atom_lit(m) and type(m[1]) is not str
            if m[0] == "id": return m[1] in ps
            if m[0] == "bin": return m[1] in ("+", "-", "*") and good(m[2]) and good(m[3])
            if m[0] == "block": return not isinstance(m[1], list) and good(m[1])
            return False
        if ok and good(body): out[nm] = lam
    return out


def inline_pass(pe, S, tree):
    cand = inline_candidates(pe)
    if not cand: return tree
    strict = S.STRICT_GATES
    def subst(m, mp):
        if m[0] == "id" and m[1] in mp: return mp[m[1]]
        return _rebuild(m, lambda c: subst(c, mp) if isinstance(c, tuple) and c and isinstance(c[0], str) else c)
    def walk(n, scope):
        if isinstance(n, list): return _rebuild(n, lambda c: walk(c, scope))
        if not (isinstance(n, tuple) and n and isinstance(n[0], str)):
            return _rebuild(n, lambda c: walk(c, scope)) if isinstance(n, tuple) else n
        if n[0] == "lam":
            bound = set()
            for sp in n[1]: bound.update(spec_names(sp))
            for m in nodes_of(n[2]):
                if m[0] == "def": bound.add(m[1])
            plain = {sp[1] for sp in n[1] if sp[0] == "name" and sp[2] is None} if all(sp[0] == "name" for sp in n[1]) else set()
            inner = (scope - bound) | plain
            return _rebuild(n, lambda c: walk(c, inner) if isinstance(c, (tuple, list)) else c)
        if n[0] == "block" and not isinstance(n[1], list) and n[1][0] == "seq" and n[1][1] and n[1][1][0][0] == "id" and n[1][1][0][1] in cand:
            sq = n[1]                                  # 括った呼び出し `(sq n)` だけ(括らない並びの形は、strict の G3 などが見るので触れない)
            lam = cand[sq[1][0][1]]
            args = [walk(a, scope) for a in sq[1][1:]]
            if len(args) == len(lam[1]) and all(_atom_lit(a) or (a[0] == "id" and not strict and a[1] in scope) for a in args):
                mp = {sp[1]: a for sp, a in zip(lam[1], args)}
                count("inline")
                return pe.mk(n, ("block", subst(lam[2], mp)))
        return _rebuild(n, lambda c: walk(c, scope) if isinstance(c, (tuple, list)) else c)
    return walk(tree, frozenset())


def local_cleanup(pe, S, tree):
    """局所の定義の行 `名前 : 右辺`(cases の行で、条件が名前1つ)のうち、どこからも使われない物(右辺が数の字面か何も起こさない小さな関数)を消し、
    1つの式の本体の中の重複した純粋な呼び出し(`g n + g n`)を局所の定義 1 つにまとめる。"""
    if S.STRICT_GATES: return tree                    # R128: 本体に局所の定義は無い(`名前 : 右辺` の行は枝)。局所の定義を前提にした整理(使われない行の削除・共通部分の括り出し)は、読みを変えるので --strict では行わない
    quiet = set()
    def qgood(m, names):
        if m[0] in ("lit", "hole"): return m[0] == "hole" or _atom_lit(m) or isinstance(m[1], int)
        if m[0] == "id": return m[1] in names or m[1] in quiet
        if m[0] == "bin": return m[1] in ("+", "-", "*", "<", "<=", ">", ">=", "=", "==", "!=", "!==") and qgood(m[2], names) and qgood(m[3], names)
        if m[0] == "cmp": return all(qgood(x, names) for x in m[1])
        if m[0] == "block": return not isinstance(m[1], list) and qgood(m[1], names)
        if m[0] == "seq": return all(qgood(x, names) for x in m[1])
        if m[0] == "cases": return all((c is None or qgood(c, names)) and qgood(e, names) for c, e in m[1])
        return False
    quiet.update(pe.pure)
    changed = True
    while changed:                                   # 静かな関数の最大不動点(呼び先がみな静かな関数なら静か。自分への再帰も許す)
        changed = False
        for nm in list(quiet):
            lam = pe.pure[nm]
            if not (all(sp[0] == "name" and sp[2] is None for sp in lam[1]) and qgood(lam[2], {sp[1] for sp in lam[1]})): quiet.discard(nm); changed = True
    counter = [0]
    def fix_lam(n):
        if n[0] != "lam" or not all(sp[0] == "name" for sp in n[1]): return n
        ps = {sp[1] for sp in n[1]}
        body = n[2]
        if body[0] == "cases":                       # 使われない局所の定義の行
            rows = list(body[1]); drop = []
            for i, (c, e) in enumerate(rows):
                if c is not None and c[0] == "id" and c[1] not in ps and (_atom_lit(e) or (e[0] == "lit" and type(e[1]) is int)):
                    rest = [r for j, r in enumerate(rows) if j != i]
                    if not any((m[0] == "id" and m[1] == c[1]) or (m[0] == "def" and m[1] == c[1]) for m in nodes_of(rest)) and c[1] not in pe.banned:
                        drop.append(i)
            if drop:
                count("dead-local", len(drop))
                return pe.mk(n, ("lam", n[1], ("cases", [r for j, r in enumerate(rows) if j not in drop])))
            return n
        calls = {}
        def scan(m):
            if isinstance(m, list):
                for c in m: scan(c)
            elif isinstance(m, tuple) and m:
                if m[0] == "lam": return
                if m[0] == "seq" and m[1] and m[1][0][0] == "id" and m[1][0][1] in quiet and len(m[1]) == len(pe.pure[m[1][0][1]][1]) + 1 \
                        and all(_atom_lit(a) or (a[0] == "id" and a[1] in ps) for a in m[1][1:]):
                    calls.setdefault(repr(m), [m, 0])[1] += 1
                    return
                for c in m[1:] if isinstance(m[0], str) else m: scan(c)
        scan(body)
        dups = [v[0] for v in calls.values() if v[1] >= 2]
        if not dups: return n
        names = {}
        for d in dups:
            counter[0] += 1; names[repr(d)] = "%cse" + str(counter[0])
        def sub(m):
            if isinstance(m, tuple) and m and isinstance(m[0], str):
                if m[0] == "lam": return m
                if m[0] == "seq" and repr(m) in names: return ("id", names[repr(m)])
            return _rebuild(m, lambda c: sub(c) if isinstance(c, (tuple, list)) else c)
        newbody = sub(body)
        rows = [(("id", names[repr(d)]), d) for d in dups] + [(None, newbody)]
        count("cse", len(dups))
        return pe.mk(n, ("lam", n[1], ("cases", rows)))
    def walk(n):
        if isinstance(n, list): return _rebuild(n, walk)
        if isinstance(n, tuple):
            n2 = _rebuild(n, lambda c: walk(c) if isinstance(c, (tuple, list)) else c)
            if n2 and isinstance(n2[0], str) and n2[0] == "lam": return fix_lam(n2)
            return n2
        return n
    return walk(tree)


def optimize(S, nodes):
    """構文木(文の並び)を残余プログラムにする。S は sign_interp のモジュール。"""
    _UNIT[0] = S.UNIT
    STATS.clear()
    pe = PE(S, nodes)
    if not pe.feasible(): return nodes
    pe.analyse()
    out = []
    for n in nodes:
        if n[0] == "def" and n[2][0] == "lit" and n[1] in pe.consts:
            out.append(n); continue                            # 定数の定義そのものはそのまま(`$` もないので使われなくなるだけ)
        if n[0] == "export":
            out.append(n); continue
        r = pe.rec(n, {}, frozenset())
        r = inline_pass(pe, S, r)
        r = local_cleanup(pe, S, r)
        a = accumulate(r) if bound_names(nodes).get(r[1] if r[0] == "def" else None, 0) == 1 and r[0] == "def" else None
        if a is not None:
            KEEP.append(r[2]); S.ACC[id(r[2])] = a; count("accum")          # 累積版は別の文にせず(値の並びを変えない)、呼ぶ時に作る
        out.append(r)
    return out
