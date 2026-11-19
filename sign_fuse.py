"""融合変換 段 0: 「純」と「終わる」の判定(DESIGN_INLINE_SPECIALIZE.md §9)。

融合変換(`map f (map g xs)` や `[+] (map f xs)` を 1 回の走査にまとめる)は、2 つの段の実行の順が変わる。
結果を変えないために、融合の対象にする関数は次の 2 つを満たすものだけにする(利用者の回答 2026-11-14 で採用した定義)。

  純      `#`(書き込み)・`@`(メモリの読み。引数の関数の呼び出しも、名前になるまでは不明として扱う)・
          装置と乱数と入出力(`std.sn` の定義を通して書き込みか読みに行き着く)・定義の見えない名前を含まない。
  終わる  再帰が有限と分かる。呼び出しの輪が無い(再帰しない)か、自分だけを呼ぶ再帰で、次のどちらかに当てはまる。
            構造再帰: 括りの仮引数 `[h ~t]` の残り `t` を、同じ位置にそのまま渡して自分を呼ぶ。
            数の再帰: 先に置いた枝の守り(`n <= 0`・`i >= n` など)があり、守りに掛かる数を、自分を呼ぶ所で
                      字面の正の整数だけ(`n - 1`・`i + 1`)進める。守りの相手が別の仮引数なら、それは変えずに渡す。

判定は「分かるものだけ」を通す(分からなければ、純でない・終わらない扱い)。融合しない側に倒れるだけで、結果は変わらない。
前提(確かめていない点): 数の再帰は整数の引数を前提にする。整数でない値が来たときは仕様の `!_` の扱いに従うが、ここでは確かめていない。

使い方:
    a = Analysis(nodes)            # nodes は展開済みの木(`std.sn` の取り込みは expand_imports の後)
    a.info["name"].pure / .terminates / .reasons
    a.expr(node)                   # 式(呼び出しの所)の判定
    a.fusable("name")              # 純で終わる
    python3 sign_fuse.py file.sn   # 最上位の定義を一覧する
"""
import sys

PURE_NAMES = ("_", "i", "__")
PURE_TAGS = {"lit", "id", "bin", "cmp", "cases", "block", "seq", "lam", "name", "neg", "not", "norm", "abs",
             "post", "prod", "sec", "addr", "hole", "lift", "bnot"}


def _param_names(params):
    out = []
    for p in params:
        if p[0] == "name": out.append(p[1])
        elif p[0] == "destr":
            out += [nm for nm in p[1] if isinstance(nm, str)]
            if len(p) > 2 and isinstance(p[2], str): out.append(p[2])
            if len(p) > 4: out += [nm for nm in p[4] if isinstance(nm, str)]
    return out


class Info:
    def __init__(self, name):
        self.name = name
        self.local = []          # この定義の中だけで見つかった、純でない理由
        self.refs = set()        # 参照する最上位の定義の名前
        self.pure = False
        self.terminates = False
        self.reasons = []        # 純でない理由・終わると分からない理由(経由した定義の分も)

    def __repr__(self):
        return "Info(%s pure=%s terminates=%s %s)" % (self.name, self.pure, self.terminates, self.reasons)


class Analysis:
    def __init__(self, nodes):
        self.defs = {}
        dup = set()
        for n in nodes:
            if n[0] == "def" and len(n) == 3:
                if n[1] in self.defs: dup.add(n[1])
                self.defs[n[1]] = n[2]
        self.dup = dup
        self.info = {}
        for nm, rhs in self.defs.items():
            inf = Info(nm)
            if nm in dup: inf.local.append("同じ名前の定義が 2 つ以上ある")
            self._walk(rhs, set(), inf)
            self.info[nm] = inf
        self.reach = {}
        for nm in self.defs:
            seen = set(); stack = list(self.info[nm].refs)
            while stack:
                m = stack.pop()
                if m in seen or m not in self.info: continue
                seen.add(m); stack += list(self.info[m].refs)
            self.reach[nm] = seen
        self.term_local = {nm: self._term_local(nm) for nm in self.defs}
        for nm in self.defs:
            self._finish(self.info[nm], nm, self.reach[nm])

    # ---- 判定の仕上げ ----
    def _finish(self, inf, nm, reach):
        names = [nm] + sorted(reach - {nm})
        reasons = []
        for m in names:
            for r in self.info[m].local:
                reasons.append(r if m == nm else "%s 経由: %s" % (m, r))
        inf.pure = not reasons
        bad = []
        for m in names:
            ok, why = self.term_local[m]
            if not ok: bad.append(why if m == nm else "%s 経由: %s" % (m, why))
        inf.terminates = not bad
        inf.reasons = reasons + bad

    def fusable(self, name):
        i = self.info.get(name)
        return bool(i and i.pure and i.terminates)

    def expr(self, node, scope=()):
        """式の判定(呼び出しの所など)。参照する定義の判定も含める。"""
        inf = Info("<式>")
        self._walk(node, set(scope), inf)
        reach = set(); stack = list(inf.refs)
        while stack:
            m = stack.pop()
            if m in reach or m not in self.info: continue
            reach.add(m); stack += list(self.info[m].refs)
        tmp = Info("<式>")
        tmp.local = inf.local
        self.info["<式>"] = tmp
        try:
            self.term_local["<式>"] = (True, "")
            self._finish(inf, "<式>", reach)
        finally:
            self.info.pop("<式>", None); self.term_local.pop("<式>", None)
        return inf

    # ---- 木を歩く ----
    def _walk(self, x, scope, inf):
        if isinstance(x, list):
            for y in x: self._walk(y, scope, inf)
            return
        if not isinstance(x, tuple): return
        if not (x and isinstance(x[0], str)):
            for y in x: self._walk(y, scope, inf)
            return
        tag = x[0]
        if tag == "id":
            nm = x[1] if len(x) > 1 else None
            if nm in scope: return
            if nm in self.defs: inf.refs.add(nm); return
            if nm in PURE_NAMES: return
            inf.local.append("定義の見えない名前 %s" % (nm,))
            return
        if tag == "input":
            op = x[1] if len(x) > 1 else None
            if isinstance(op, tuple) and op[:1] == ("id",) and op[1] in scope:
                inf.local.append("引数の関数の呼び出し(@%s)。特殊化で名前になるまで不明" % op[1])
            else:
                inf.local.append("メモリの読み(@)")
            self._walk(op, scope, inf)
            return
        if tag == "seq":
            items = x[1]
            if items and isinstance(items[0], tuple) and items[0][:1] == ("id",) and items[0][1] in scope:
                inf.local.append("引数の関数の呼び出し(%s)。特殊化で名前になるまで不明" % items[0][1])
            self._walk(items, scope, inf)
            return
        if tag == "bin":
            if x[1] == "#": inf.local.append("書き込み(#)")
            self._walk(x[2:], scope, inf)
            return
        if tag == "sec":
            if "#" in x: inf.local.append("書き込み(#)")
            self._walk([y for y in x if isinstance(y, (tuple, list))], scope, inf)
            return
        if tag == "lam":
            sc = set(scope) | set(_param_names(x[1]))
            for p in x[1]:
                if p[0] == "name" and len(p) > 2 and p[2] is not None: self._walk(p[2], sc, inf)
            self._walk(x[2], sc, inf)
            return
        if tag == "def":
            sc = set(scope) | {x[1]}
            self._walk(x[2:], sc, inf)
            return
        if tag in PURE_TAGS:
            self._walk([y for y in x[1:] if isinstance(y, (tuple, list))], scope, inf)
            return
        inf.local.append("未対応の形(%s)" % tag)

    # ---- 終わるか ----
    def _term_local(self, nm):
        """この定義だけを見て、呼び出しの輪の中で終わると分かるか。輪が無ければ分かる。"""
        reach = self.reach[nm]
        if nm not in reach: return (True, "")
        for m in reach:
            if m != nm and nm in self.reach.get(m, ()):
                return (False, "相互再帰(%s)" % m)
        rhs = self.defs[nm]
        if not (isinstance(rhs, tuple) and rhs[0] == "lam"):
            return (False, "関数でない定義が自分を参照している")
        params = rhs[1]; body = rhs[2]
        names = [p[1] if p[0] == "name" else None for p in params]
        branches = None
        if isinstance(body, tuple) and body[0] == "cases": branches = body[1]
        calls = []                      # (枝の番号 or None, 実引数の並び)
        bad = []

        def find(x, bi, head=False):
            if isinstance(x, list):
                for y in x: find(y, bi)
                return
            if not isinstance(x, tuple): return
            if x[:1] == ("id",) and len(x) == 2:
                if x[1] == nm and not head: bad.append("自分を引数や値として使っている")
                return
            if x[:1] == ("seq",) and x[1] and x[1][0] == ("id", nm):
                calls.append((bi, list(x[1][1:])))
                find(x[1][1:], bi)
                return
            for y in x:
                find(y, bi)

        if branches is not None:
            for j, (cond, val) in enumerate(branches):
                before = len(calls)
                if cond is not None:
                    find(cond, j)
                    if len(calls) > before: bad.append("条件の中で自分を呼んでいる")
                find(val, j)
        else:
            find(body, None)
        if bad: return (False, bad[0])
        if not calls: return (True, "")

        def unwrap(a):
            while isinstance(a, tuple) and a[:1] == ("block",): a = a[1]
            return a

        # 構造再帰
        for i, p in enumerate(params):
            if p[0] == "destr" and len(p) > 2 and isinstance(p[2], str):
                if all(len(a) > i and unwrap(a[i]) == ("id", p[2]) for _, a in calls):
                    return (True, "")

        def is_lit_int(a):
            return isinstance(a, tuple) and a[:1] == ("lit",) and isinstance(a[1], int) and not isinstance(a[1], bool) \
                and (len(a) < 3 or a[2] != "Address")

        def step(a, p, sign):
            a = unwrap(a)
            return isinstance(a, tuple) and a[:1] == ("bin",) and a[1] == sign and unwrap(a[2]) == ("id", p) \
                and is_lit_int(unwrap(a[3])) and unwrap(a[3])[1] > 0

        if branches is not None:
            for j, (cond, val) in enumerate(branches):
                g = self._guard(cond, names)
                if g is None: continue
                p, b, d = g
                if any(bi is not None and bi <= j for bi, _ in calls): continue
                if p not in names: continue
                ip = names.index(p)
                sign = "-" if d == "down" else "+"
                ok = True
                for _, a in calls:
                    if len(a) <= ip or not step(a[ip], p, sign): ok = False; break
                    if isinstance(b, str):
                        if b not in names: ok = False; break
                        iq = names.index(b)
                        if len(a) <= iq or unwrap(a[iq]) != ("id", b): ok = False; break
                if ok: return (True, "")
        return (False, "再帰が有限と分からない(構造再帰でも、守りのある数の再帰でもない)")

    @staticmethod
    def _guard(cond, names):
        """守りの枝の条件から (守りに掛かる仮引数, 相手(整数の字面 or 仮引数名), 'down'|'up') を取る。"""
        if not (isinstance(cond, tuple) and cond[:1] == ("cmp",) and len(cond[1]) == 2 and len(cond[2]) == 1): return None
        a, b = cond[1]; op = cond[2][0]
        a = a if not (isinstance(a, tuple) and a[:1] == ("block",)) else a[1]
        b = b if not (isinstance(b, tuple) and b[:1] == ("block",)) else b[1]

        def lit(v):
            return isinstance(v, tuple) and v[:1] == ("lit",) and isinstance(v[1], int) and not isinstance(v[1], bool) \
                and (len(v) < 3 or v[2] != "Address")

        def par(v):
            return isinstance(v, tuple) and v[:1] == ("id",) and v[1] in names

        if op in ("<", "<=", ">", ">="):
            if par(a) and (lit(b) or (par(b) and b[1] != a[1])):
                d = "down" if op in ("<", "<=") else "up"
                return (a[1], b[1] if par(b) else b[1], d)
            if par(b) and (lit(a) or (par(a) and a[1] != b[1])):
                d = "down" if op in (">", ">=") else "up"
                return (b[1], a[1] if par(a) else a[1], d)
        return None


# ---- 段 2(C): `[op] (map f xs)` を、要素ごとに f を当てて畳む 1 つの輪にする ----
ARITH = {"+": "add", "-": "sub", "*": "mul", "/": "div", "%": "mod"}
TOTAL_OPS = ("+", "-", "*")          # 値が `!_` にならない演算(0 で割る・溢れの `!_` を含まない)


def _strip(t):
    while isinstance(t, tuple) and t and t[0] == "block": t = t[1]
    return t


def map_like(d):
    """利用者の定義が `m : f [h ~t] ? (@f h) (m f t)~`(f の結果を並べて残りへ進む)の形か。"""
    if not (d[0] == "def" and len(d) > 2 and d[2][0] == "lam"): return False
    ps, body = d[2][1], d[2][2]
    if len(ps) != 2 or ps[0][0] != "name" or ps[1][0] != "destr": return False
    f = ps[0][1]; dd = ps[1]
    if len(dd[1]) != 1 or dd[3] or dd[4]: return False
    h, t = dd[1][0], dd[2]
    if not (isinstance(body, tuple) and body[0] == "seq" and len(body[1]) == 2): return False
    a, b = body[1]
    if _strip(a) != ("seq", [("input", ("id", f)), ("id", h)]): return False
    if not (b[0] == "post" and b[1] == "~"): return False
    return _strip(b[2]) == ("seq", [("id", d[1]), ("id", f), ("id", t)])


def _total_body(e, x):
    """本体が、引数 x と整数の字面を + - * でつなぐだけ(値が必ず決まり、書き込みも読みも無い)か。"""
    e = _strip(e)
    if e[0] == "id": return e[1] == x
    if e[0] == "lit": return isinstance(e[1], int) and not isinstance(e[1], bool) and (len(e) < 3 or e[2] != "Address")
    if e[0] == "neg": return _total_body(e[1], x)
    if e[0] == "bin" and e[1] in TOTAL_OPS: return _total_body(e[2], x) and _total_body(e[3], x)
    if e[0] == "seq" and len(e[1]) == 1: return _total_body(e[1][0], x)
    return False


def fuse_fold_map(nodes):
    """`[op] (map $g xs)` → 補助 `_fmS_<op>_<g> xs`(添字で回す輪)。g は、引数 1 個で本体が + - * だけの全域な関数(名前、`$[* 2]`、`$[x ? x + 1]`)。
    中間の器を作らない。`map` に `!_` を返す要素・副作用は無いので、順序も結果も変わらない(DESIGN_INLINE_SPECIALIZE.md §9.5)。
    直す物が無ければ nodes をそのまま返す。"""
    import sign_interp
    maps = {d[1] for d in nodes if isinstance(d, tuple) and d[0] == "def" and map_like(d)}
    defs = {}
    for d in nodes:
        if isinstance(d, tuple) and d[0] == "def": defs[d[1]] = defs.get(d[1], 0) + 1
    maps = {m for m in maps if defs[m] == 1}
    if not maps: return nodes
    byname = {d[1]: d for d in nodes if isinstance(d, tuple) and d[0] == "def"}
    made = {}            # (op, g の名前) -> 補助の名前
    newdefs = []
    anon = [0]
    def g_name(a):
        a = _strip(a)
        if a[0] != "addr": return None
        v = _strip(a[1])
        if v[0] == "id":
            d = byname.get(v[1])
            if d and defs.get(v[1]) == 1 and d[2][0] == "lam" and len(d[2][1]) == 1 and d[2][1][0][0] == "name" \
                    and _total_body(d[2][2], d[2][1][0][1]): return v[1]
            return None
        lam = None
        if v[0] == "sec" and v[1] == "right" and v[2] in TOTAL_OPS and v[4] is False and _strip(v[3])[0] == "lit":
            lam = ("lam", [("name", "x", None)], ("bin", v[2], ("id", "x"), v[3]))
        elif v[0] == "lam" and len(v[1]) == 1 and v[1][0][0] == "name" and _total_body(v[2], v[1][0][1]): lam = v
        if lam is None or not _total_body(lam[2], lam[1][0][1]): return None
        anon[0] += 1; nm = "_fg%d_" % anon[0]
        newdefs.append(("def", nm, lam)); byname[nm] = newdefs[-1]; defs[nm] = 1
        return nm
    def helper(op, g):
        k = (op, g)
        if k not in made:
            nm = ARITH[op]
            h, hs = "_fm_%s_%s" % (nm, g), "_fmS_%s_%s" % (nm, g)
            if h in byname or hs in byname: raise ValueError("補助の名前 `%s` が使われています" % hs)
            src = ("%s : xs i acc ?\n\ti >= ||xs|| : acc\n\t%s xs (i + 1) (acc %s (%s (xs ' i)))\n" % (h, h, op, g)
                   + "%s : xs ?\n\t||xs|| = 0 : __\n\t%s xs 1 (%s (xs ' 0))\n" % (hs, h, g))
            newdefs.extend(sign_interp.parse_source(src))
            made[k] = hs
        return made[k]
    def rw(t):
        if isinstance(t, list): return [rw(x) for x in t]
        if not isinstance(t, tuple): return t
        if t and t[0] == "seq" and isinstance(t[1], list) and len(t[1]) == 2:
            a, b = t[1]
            if isinstance(a, tuple) and a[:1] == ("sec",) and a[1] == "fold" and a[3] is None and a[2] in ARITH and (len(a) < 5 or not a[4]):
                bb = _strip(b)
                if bb[0] == "seq" and len(bb[1]) == 3 and bb[1][0][:1] == ("id",) and bb[1][0][1] in maps:
                    g = g_name(bb[1][1])
                    if g is not None: return ("seq", [("id", helper(a[2], g)), rw(bb[1][2])])
        return tuple(rw(x) if isinstance(x, (tuple, list)) else x for x in t)
    out = [rw(n) for n in nodes]
    return newdefs + out if made else nodes


# ---- 共通部分式(枝をまたぐ式): 評価した場所で値を 1 回だけスロットに置き、あとの枝は読む ----
SHARE_STRICT = ("+", "-", "*", "/", "%")


def _shape_key(t):
    t = _strip(t)
    if isinstance(t, tuple): return tuple(_shape_key(x) if isinstance(x, (tuple, list)) else x for x in t)
    if isinstance(t, list): return tuple(_shape_key(x) for x in t)
    return t


def _arith_ok(e, params):
    """+ - * と、字面(0・-1 以外)で割る / % だけで、仮引数と整数の字面をつないだ式か(罠は溢れだけ。書き込み・読み・呼びは無い)。"""
    e = _strip(e)
    if e[0] == "id": return len(e) == 2 and e[1] in params
    if e[0] == "lit": return isinstance(e[1], int) and not isinstance(e[1], bool) and (len(e) < 3 or e[2] != "Address")
    if e[0] == "neg": return _arith_ok(e[1], params)
    if e[0] == "bin" and len(e) == 4 and e[1] in SHARE_STRICT:
        if e[1] in ("/", "%"):
            d = _strip(e[3])
            if not (d[0] == "lit" and isinstance(d[1], int) and not isinstance(d[1], bool) and d[1] not in (0, -1)): return False
        return _arith_ok(e[2], params) and _arith_ok(e[3], params)
    return False


def _size(t):
    return 1 + sum(_size(x) for x in t) if isinstance(t, (tuple, list)) else 0


def share_exprs(nodes):
    """条件の枝(`cases`)の本体で、同じ算術式 E が 2 回以上出るとき、E を最初に評価する枝の条件の中で値を 1 回だけスロットへ置き(`sh`)、
    あとの出現はそれを読む(`ref`)印をつける。印は ("block", E, "sh"|"ref", 鍵) で、解析からは今までの括りと同じに見える。
    罠(溢れ)が起きる時は変わらない: E を最初に評価する場所(その枝の条件のうち、先に評価が確実に進む位置)で、元と同じように評価するだけで、
    入口へ前倒しはしない。"""
    out = []
    ctr = [0]
    for d in nodes:
        if not (isinstance(d, tuple) and d[0] == "def" and len(d) > 2 and d[2][0] == "lam" and _strip(d[2][2])[0] == "cases"):
            out.append(d); continue
        params = {p[1] for p in d[2][1] if p[0] == "name"}
        if len(params) != len(d[2][1]) or not params: out.append(d); continue
        body = _strip(d[2][2]); cases = list(body[1])
        for _round in range(3):
            # 候補: 全部の部分木のうち _arith_ok で、演算を含み、形が同じものの出現数
            cnt = {}; first = {}
            def walk(t, ci, in_cond, strict):
                if isinstance(t, list):
                    for x in t: walk(x, ci, in_cond, strict)
                    return
                if not isinstance(t, tuple) or not t: return
                if isinstance(t[0], str):
                    if t[0] == "lam" or (t[0] == "block" and len(t) > 3 and t[2] == "lazy"): return      # lazy の中は、飛ばされうるので印をつけない
                    if t[0] in ("bin", "neg", "block") and _size(t) >= 5 and _arith_ok(t, params) and _strip(t)[0] in ("bin",):
                        k = _shape_key(t); cnt[k] = cnt.get(k, 0) + 1
                        if k not in first: first[k] = (ci, in_cond and strict)
                    nstrict = strict and (t[0] in ("block", "neg", "input", "cmp") or (t[0] == "bin" and t[1] in SHARE_STRICT))
                    for x in t[1:]: walk(x, ci, in_cond, nstrict)
                else:
                    for x in t: walk(x, ci, in_cond, strict)
            for ci, (c, e) in enumerate(cases):
                if c is not None: walk(c, ci, True, True)
                walk(e, ci, False, False)
            cands = [(k, v) for k, v in cnt.items() if v >= 2 and first[k][1]]
            if not cands: break
            key = max(cands, key=lambda kv: (_size(kv[0]) * kv[1], str(kv[0])))[0]
            ctr[0] += 1; name = "%s#%d" % (d[1], ctr[0])
            seen_first = [False]
            def rep(t):
                if isinstance(t, list): return [rep(x) for x in t]
                if not isinstance(t, tuple) or not t: return t
                if t[0] == "block" and len(t) > 3 and t[2] == "lazy": return t
                if isinstance(t[0], str) and t[0] in ("bin", "block", "neg") and _size(t) >= 5 and _arith_ok(t, params) and _shape_key(t) == key and _strip(t)[0] == "bin":
                    if not seen_first[0]: seen_first[0] = True; return ("block", t, "sh", name)
                    return ("block", t, "ref", name)
                return tuple(rep(x) if isinstance(x, (tuple, list)) else x for x in t)
            new = []
            for ci, (c, e) in enumerate(cases):
                new.append((rep(c) if c is not None else None, rep(e)))
            cases = new
        nb = ("cases", cases) + tuple(body[2:])
        out.append(d[:2] + (("lam", d[2][1], nb) + tuple(d[2][3:]),) + tuple(d[3:]))
    return out


# ---- ループ不変式: 自己再帰(末尾呼び)で変わらない引数だけの算術式は、最初に必要になった時に 1 回だけ計算する ----
def _self_calls(t, name, out):
    if isinstance(t, list):
        for x in t: _self_calls(x, name, out)
    elif isinstance(t, tuple) and t:
        if t[0] == "seq" and isinstance(t[1], list) and t[1] and t[1][0] == ("id", name): out.append(t[1][1:])
        for x in t:
            if isinstance(x, (tuple, list)): _self_calls(x, name, out)


def lazy_invariants(nodes):
    """自己再帰する関数で、全部の自己呼びが同じ位置にそのまま渡す仮引数(不変)だけでできた算術式 E(+ - * と字面で割る / %)に、
    ("block", E, "lazy", 鍵) の印をつける。`FnGen.gen` は、スロットを入口で `__` にしておき、E の所で『空なら評価して置く、あれば読む』を出す。
    評価の場所は元のまま(最初に必要になった所)なので、溢れの罠が起きる時は変わらない。2 回目以降のループで E を再計算しない。
    対象: 条件(cond)に出る、乗除剰を含む E(行に着けば毎回評価される。足し引きだけの式は、スロットを読むのと命令数が同じで得が無い。値の側は通るか分からず、2 回目以降が少ないので対象にしない)。"""
    out = []; ctr = [0]
    for d in nodes:
        if not (isinstance(d, tuple) and d[0] == "def" and len(d) > 2 and d[2][0] == "lam"):
            out.append(d); continue
        names = [p[1] for p in d[2][1] if p[0] == "name"]
        body = _strip(d[2][2])
        if len(names) != len(d[2][1]) or not names or body[0] != "cases":
            out.append(d); continue
        calls = []; _self_calls(d[2][2], d[1], calls)
        if not calls or any(len(c) != len(names) for c in calls):
            out.append(d); continue
        inv = {n for i, n in enumerate(names) if all(_strip(c[i]) == ("id", n) for c in calls)}
        rows = body[1]
        tails = [i for i, (c, e) in enumerate(rows) if (lambda x: x[0] == "seq" and isinstance(x[1], list) and x[1] and x[1][0] == ("id", d[1]))(_strip(e))]
        if not inv or not tails:
            out.append(d); continue
        keys = {}
        def mark(t, hot):
            """hot = ループの毎回通る所(条件・末尾の自己呼びの実引数)。極大の E に印をつける。"""
            if isinstance(t, list): return [mark(x, hot) for x in t]
            if not isinstance(t, tuple) or not t: return t
            if hot and isinstance(t[0], str) and t[0] in ("bin", "block") and _strip(t)[0] == "bin" and _arith_ok(t, inv) and not _arith_ok_const(t) and _costly(t):
                k = _shape_key(t)
                if k not in keys: ctr[0] += 1; keys[k] = "%s@%d" % (d[1], ctr[0])
                return ("block", t, "lazy", keys[k])
            if t[0] == "lam": return t
            return tuple(mark(x, hot) if isinstance(x, (tuple, list)) else x for x in t)
        new = []
        for i, (c, e) in enumerate(rows):
            new.append((mark(c, True) if c is not None else None, e))      # 条件だけ: 行に着けば毎回評価される。値の側(末尾の呼びの実引数)は、通るか分からず 2 回目以降が少ないので対象にしない
        if not keys:
            out.append(d); continue
        nb = ("cases", new) + tuple(body[2:])
        out.append(d[:2] + (("lam", d[2][1], nb) + tuple(d[2][3:]),) + tuple(d[3:]))
    return out


def _costly(t):
    """乗除剰(積の溢れの検査・除算)を含むか。足し引きだけの式は、スロットを読む(ldr・cmp・b)のと命令の数が同じで、得が無い。"""
    t = _strip(t)
    if not (isinstance(t, tuple) and t and t[0] == "bin"): return False
    return t[1] in ("*", "/", "%") or _costly(t[2]) or _costly(t[3])


def _arith_ok_const(t):
    """仮引数を 1 つも含まない(字面だけの)式か。定数畳み込みの仕事なので、ここでは印をつけない。"""
    t = _strip(t)
    if t[0] == "id": return False
    if t[0] == "lit": return True
    if t[0] == "neg": return _arith_ok_const(t[1])
    return _arith_ok_const(t[2]) and _arith_ok_const(t[3])


# ---- レコードの分解(既知の構造の分解): 字面の器を受ける仮引数へ、字面の器を作って渡す呼びを、要素をそのまま渡す呼びにする ----
def _lit_list(e, defs):
    """字面の器(括弧で並べた物)か。先頭が定義済みの名前なら呼びなので、器ではない。要素の式の並びを返す(違えば None)。"""
    e = _strip(e)
    if not (isinstance(e, tuple) and e and e[0] == "seq" and isinstance(e[1], list) and len(e[1]) >= 2): return None
    h = _strip(e[1][0])
    if isinstance(h, tuple) and h[:1] == ("id",) and h[1] in defs: return None
    return list(e[1])


def _scalar_total(e, defs, totals, depth=0):
    """値が必ず決まる(`!_` にならず、器でもない)式か。器の字面の要素が `!_` なら器が縮むので、分解してよいのは必ず決まる要素だけ。"""
    e = _strip(e)
    if not isinstance(e, tuple) or not e: return False
    t = e[0]
    if t == "lit": return isinstance(e[1], int) and not isinstance(e[1], bool) and (len(e) < 3 or e[2] != "Address")
    if t == "id": return len(e) == 2 and (e[1] not in defs or _const_total(e[1], defs, totals, depth))
    if t == "neg": return _scalar_total(e[1], defs, totals, depth)
    if t == "bin" and len(e) == 4 and e[1] in SHARE_STRICT:
        if e[1] in ("/", "%"):
            d = _strip(e[3])
            if not (d[0] == "lit" and isinstance(d[1], int) and not isinstance(d[1], bool) and d[1] not in (0, -1)): return False
        return _scalar_total(e[2], defs, totals, depth) and _scalar_total(e[3], defs, totals, depth)
    if t == "input": return _scalar_total(e[1], defs, totals, depth)                 # 読み(`@`)は、いつも整数を返す
    if t == "seq" and isinstance(e[1], list) and len(e[1]) >= 2:
        h = _strip(e[1][0])
        if h[:1] == ("id",) and h[1] in defs and depth < 4:                         # 全域な関数の呼び
            d = defs[h[1]]
            return _fn_total(h[1], defs, totals, depth + 1) and all(_scalar_total(a, defs, totals, depth) for a in e[1][1:])
    return False


def _const_total(name, defs, totals, depth):
    d = defs.get(name)
    return d is not None and d[2][0] != "lam" and depth < 4 and _scalar_total(d[2], defs, totals, depth + 1)


def _fn_total(name, defs, totals, depth):
    """引数が決まっていれば、必ず整数が決まる関数か(本体が全域な式、または最後の行が条件なしで全部の行の値が全域な `cases`)。"""
    if name in totals: return totals[name]
    totals[name] = False                                      # 再帰は全域とみなさない
    d = defs.get(name)
    ok = False
    if d and d[2][0] == "lam" and all(p[0] == "name" for p in d[2][1]):
        b = _strip(d[2][2])
        if b[0] == "cases":
            rows = b[1]
            ok = bool(rows) and rows[-1][0] is None and all(_scalar_total(r[1], defs, totals, depth) for r in rows) \
                and all(c is None or _scalar_total_cond(c, defs, totals, depth) for c, _ in rows)
        else:
            ok = _scalar_total(d[2][2], defs, totals, depth)
    totals[name] = ok
    return ok


def _scalar_total_cond(c, defs, totals, depth):
    """条件は、比較か、全域な式(値が決まれば真偽で分かれる)。比較は `!_` になりうるが、cases の条件の `!_` は『その行に当たらない』で、行の値の全域さは変わらない。"""
    return True


def _simple_total(e, defs):
    """仮引数・字面・+ - * / %(字面で割る)だけの式(読みも呼びも無い)。順序を入れ替えても変わらない。"""
    e = _strip(e)
    if not isinstance(e, tuple) or not e: return False
    t = e[0]
    if t == "lit": return isinstance(e[1], int) and not isinstance(e[1], bool) and (len(e) < 3 or e[2] != "Address")
    if t == "id": return len(e) == 2 and e[1] not in defs
    if t == "neg": return _simple_total(e[1], defs)
    if t == "bin" and len(e) == 4 and e[1] in SHARE_STRICT:
        if e[1] in ("/", "%"):
            d = _strip(e[3])
            if not (d[0] == "lit" and isinstance(d[1], int) and not isinstance(d[1], bool) and d[1] not in (0, -1)): return False
        return _simple_total(e[2], defs) and _simple_total(e[3], defs)
    return False


def scalarize_records(nodes):
    """`c .. [e0 .. ek-1] ..`(c の仮引数が `[a0 .. ak-1]` の形、または `v ' 0` のような字面の添字でしか使われない)を、
    要素を仮引数へそのまま渡す作業用の関数 `_sr_c…` の呼びにする。器を作らない。要素は全部、値が必ず決まる式に限る。"""
    defs = {}
    dup = set()
    for d in nodes:
        if isinstance(d, tuple) and d[0] == "def":
            if d[1] in defs: dup.add(d[1])
            defs[d[1]] = d
    for n in dup: defs.pop(n, None)
    totals = {}
    made = {}; newdefs = []
    shadow = [set()]                                       # いま見ている関数の仮引数(定義と同じ名前でも、仮引数が勝つ)
    def dv():
        return {k: v for k, v in defs.items() if k not in shadow[0]} if shadow[0] & set(defs) else defs
    def pnames(lam):
        o = set()
        for q in lam[1]:
            if q[0] == 'name': o.add(q[1])
            elif q[0] == 'destr': o |= set(q[1]) | ({q[2]} if q[2] else set())
        return o
    def uses_only_indexed(v, body):
        """仮引数 v が `v ' <字面>` の形でしか現れないなら、使う添字の集合。違えば None。"""
        idx = set(); ok = [True]
        def walk(t):
            if not ok[0]: return
            if isinstance(t, list):
                for x in t: walk(x)
                return
            if not isinstance(t, tuple) or not t: return
            if t[0] == "bin" and len(t) == 4 and t[1] == "'" and _strip(t[2]) == ("id", v):
                j = _strip(t[3])
                if j[0] == "lit" and isinstance(j[1], int) and not isinstance(j[1], bool) and j[1] >= 0: idx.add(j[1]); return
                ok[0] = False; return
            if t[0] == "id" and len(t) == 2 and t[1] == v: ok[0] = False; return
            if t[0] == "lam": ok[0] = False; return
            for x in t[1:] if isinstance(t[0], str) else t: walk(x)
        walk(body)
        return idx if ok[0] and idx else None
    def subst_index(t, v, names):
        if isinstance(t, list): return [subst_index(x, v, names) for x in t]
        if not isinstance(t, tuple) or not t: return t
        if t[0] == "bin" and len(t) == 4 and t[1] == "'" and _strip(t[2]) == ("id", v): return ("id", names[_strip(t[3])[1]])
        return tuple(subst_index(x, v, names) if isinstance(x, (tuple, list)) else x for x in t)
    def worker(c, pos, k):
        key = (c, pos, k)
        if key in made: return made[key]
        d = defs[c]; ps = d[2][1]; p = ps[pos]
        taken = {q[1] for q in ps if q[0] == "name"}
        if p[0] == "destr":
            if p[2] is not None or p[3] or p[4] or len(p[1]) != k or len(set(p[1])) != k or (set(p[1]) & taken): made[key] = None; return None
            nps = ps[:pos] + [("name", n, None) for n in p[1]] + ps[pos + 1:]
            body = d[2][2]
        else:
            idx = uses_only_indexed(p[1], d[2][2])
            if idx is None or max(idx) >= k: made[key] = None; return None
            names = ["%s_%d_" % (p[1], j) for j in range(k)]
            if set(names) & taken: made[key] = None; return None
            nps = ps[:pos] + [("name", n, None) for n in names] + ps[pos + 1:]
            body = subst_index(d[2][2], p[1], names)
        nm = "_sr_%s_%d_%d" % (c, pos, k)
        if nm in defs: made[key] = None; return None
        newdefs.append(("def", nm, ("lam", nps, body) + tuple(d[2][3:])))
        defs[nm] = newdefs[-1]
        made[key] = nm
        return nm
    def can_consume(c):
        d = defs.get(c)
        return d is not None and d[2][0] == "lam" and all(p[0] in ("name", "destr") for p in d[2][1])
    # --- 段 2: 器を作って返す関数(字面か、同じ種類の関数への末尾呼びか、その cases)を、受ける側の作業用の関数へ合成する ---
    rl_memo = {}
    def result_len(p, stack=()):
        """p の返す器の長さ(全部の返し方で同じ長さの字面。決まらなければ None)。自分たちへの再帰は無視する。"""
        if p in rl_memo: return rl_memo[p]
        if p in stack: return -1                                       # 輪: 他の返し方で決まる
        d = defs.get(p)
        if d is None or d[2][0] != "lam" or not all(q[0] in ("name", "destr") for q in d[2][1]): return None
        ks = set(); bad = [False]
        saved = shadow[0]; shadow[0] = pnames(d[2])
        def walk(R):
            b = _strip(R)
            if isinstance(b, tuple) and b and b[0] == "cases":
                for _c, e in b[1]: walk(e)
                return
            ll = _lit_list(b, dv())
            if ll is not None:
                if all(_scalar_total(x, defs, totals) for x in ll): ks.add(len(ll))
                else: bad[0] = True
                return
            if isinstance(b, tuple) and b and b[0] == "seq" and isinstance(b[1], list) and b[1]:
                h = _strip(b[1][0])
                if h[:1] == ("id",) and h[1] in dv() and defs[h[1]][2][0] == "lam" and len(defs[h[1]][2][1]) == len(b[1]) - 1:
                    k2 = result_len(h[1], stack + (p,))
                    if k2 is None: bad[0] = True
                    elif k2 != -1: ks.add(k2)
                    return
            bad[0] = True
        walk(d[2][2]); shadow[0] = saved
        r = None if bad[0] or len(ks) != 1 else next(iter(ks))
        if bad[0] or len(ks) > 1: rl_memo[p] = None; return None
        if not ks: return -1
        rl_memo[p] = r
        return r
    comp_memo = {}
    budget = [300]
    def compose(c, pos, k, p, nothers):
        key = (c, pos, k, p, nothers)
        if key in comp_memo: return comp_memo[key]
        cw = worker(c, pos, k)
        pd = defs[p]
        if cw is None or budget[0] <= 0 or result_len(p) not in (k, -1):
            comp_memo[key] = None; return None
        budget[0] -= 1
        nm = "_sc_%s_%s_%d_%d_%d" % (p, c, pos, k, nothers)
        if nm in defs: comp_memo[key] = None; return None
        comp_memo[key] = nm
        mark = len(newdefs)
        extra = ["_o%d_" % j for j in range(nothers)]
        taken = set()
        for q in pd[2][1]:
            taken |= {q[1]} if q[0] == "name" else set(q[1]) | ({q[2]} if q[2] else set())
        if set(extra) & taken: comp_memo[key] = None; return None
        ok = [True]
        def build_args(elems):
            out = []; oi = 0
            for i in range(len(defs[c][2][1])):
                if i == pos: out += elems
                else: out.append(("id", extra[oi])); oi += 1
            return out
        def T(R):
            b = _strip(R)
            if isinstance(b, tuple) and b and b[0] == "cases":
                return ("cases", [(cc, T(e)) for cc, e in b[1]]) + tuple(b[2:])
            ll = _lit_list(b, dv())
            if ll is not None and len(ll) == k:
                return ("seq", [("id", cw)] + build_args(ll))
            if isinstance(b, tuple) and b and b[0] == "seq" and isinstance(b[1], list):
                h = _strip(b[1][0])
                if h[:1] == ("id",) and h[1] in dv() and defs[h[1]][2][0] == "lam":
                    q = compose(c, pos, k, h[1], nothers)
                    if q is not None:
                        return ("seq", [("id", q)] + list(b[1][1:]) + [("id", x) for x in extra])
            ok[0] = False
            return R
        saved2 = shadow[0]; shadow[0] = pnames(pd[2])
        nb = T(pd[2][2]); shadow[0] = saved2
        if not ok[0]:
            # 失敗: この途中で作った物のうち、失敗した名前を使う物(輪の途中の物)を、不動点まで取り消す。使わない物は完成した関数なので残す
            failed = {nm}
            comp_memo[key] = None
            changed = True
            while changed:
                changed = False
                for d_ in list(newdefs[mark:]):
                    if d_[1] not in failed and any(f_ in repr(d_) for f_ in failed):
                        failed.add(d_[1]); newdefs.remove(d_); defs.pop(d_[1], None); changed = True
            for kk, vv in list(comp_memo.items()):
                if vv in failed: comp_memo[kk] = None
            return None
        nps = list(pd[2][1]) + [("name", x, None) for x in extra]
        newdefs.append(("def", nm, ("lam", nps, nb) + tuple(pd[2][3:])))
        defs[nm] = newdefs[-1]
        return nm
    def rw(t):
        if isinstance(t, list): return [rw(x) for x in t]
        if not isinstance(t, tuple) or not t: return t
        t = tuple(rw(x) if isinstance(x, (tuple, list)) else x for x in t)
        if t[0] == "seq" and isinstance(t[1], list) and len(t[1]) >= 2:
            h = _strip(t[1][0])
            if h[:1] == ("id",) and h[1] in dv() and can_consume(h[1]):
                c = h[1]; ps = defs[c][2][1]; args = t[1][1:]
                if len(args) == len(ps):
                    for pos, a in enumerate(args):
                        ll = _lit_list(a, dv())
                        if ll is not None:
                            if not all(_scalar_total(x, defs, totals) for x in ll): continue
                            w = worker(c, pos, len(ll))
                            if w is None: continue
                            return rw(("seq", [("id", w)] + args[:pos] + ll + args[pos + 1:]))
                        # 引数が、器を作って返す関数の呼び: その関数と合成する(連なりの途中の器を作らない)
                        ab = _strip(a)
                        if isinstance(ab, tuple) and ab and ab[0] == "seq" and isinstance(ab[1], list) and ab[1]:
                            ph = _strip(ab[1][0])
                            if ph[:1] == ("id",) and ph[1] in dv() and defs[ph[1]][2][0] == "lam" and len(defs[ph[1]][2][1]) == len(ab[1]) - 1:
                                k = result_len(ph[1])
                                others = args[:pos] + args[pos + 1:]
                                if k is not None and k > 0 and all(_simple_total(o, defs) for o in others):
                                    q = compose(c, pos, k, ph[1], len(others))
                                    if q is not None:
                                        return ("seq", [("id", q)] + list(ab[1][1:]) + others)
        return t
    def rw_top(n):
        if isinstance(n, tuple) and n and n[0] == 'def' and len(n) > 2 and n[2][0] == 'lam':
            shadow[0] = pnames(n[2])
            try: return rw(n)
            finally: shadow[0] = set()
        return rw(n)
    out = [rw_top(n) for n in nodes]
    if not newdefs: return nodes
    return _inline_forwarders(newdefs, out)


def _count_id(t, name):
    if isinstance(t, list): return sum(_count_id(x, name) for x in t)
    if not isinstance(t, tuple) or not t: return 0
    if t[0] == "id" and len(t) == 2: return 1 if t[1] == name else 0
    return sum(_count_id(x, name) for x in t[1:] if isinstance(x, (tuple, list)))


def _first_ids(t, names, out):
    """names のうち、評価の順(左から)に初めて現れる順を out へ。"""
    if isinstance(t, list):
        for x in t: _first_ids(x, names, out)
    elif isinstance(t, tuple) and t:
        if t[0] == "id" and len(t) == 2:
            if t[1] in names and t[1] not in out: out.append(t[1])
            return
        for x in t[1:]:
            if isinstance(x, (tuple, list)): _first_ids(x, names, out)


def _subst(t, m):
    if isinstance(t, list): return [_subst(x, m) for x in t]
    if not isinstance(t, tuple) or not t: return t
    if t[0] == "id" and len(t) == 2 and t[1] in m: return m[t[1]]
    return tuple(_subst(x, m) if isinstance(x, (tuple, list)) else x for x in t)


def _has_binder(t):
    if isinstance(t, list): return any(_has_binder(x) for x in t)
    if not isinstance(t, tuple) or not t: return False
    if t[0] in ("lam", "destr", "cases"): return True
    return any(_has_binder(x) for x in t[1:] if isinstance(x, (tuple, list)))


def _inline_forwarders(newdefs, out):
    """作った関数のうち、本体が別の関数の呼び 1 つだけ(引数を渡し直すだけ)のものを、呼ぶ所へ埋め込む。
    埋め込んでよいのは、呼ぶ所の実引数が、(a) 変数か字面、または (b) 仮引数が本体で 1 回だけ使われ、評価の順が変わらないとき(式を複製しない・順序を変えない)。
    埋め込んだ後に、どこからも呼ばれなくなった作った関数は消す。"""
    gen_names = {d[1] for d in newdefs}
    fn_names = {d[1] for d in list(newdefs) + list(out) if isinstance(d, tuple) and d[0] == "def"}
    fw = {}
    for d in newdefs:
        lam = d[2]
        if lam[0] != "lam" or not all(p[0] == "name" for p in lam[1]): continue
        b = _strip(lam[2])
        if not (isinstance(b, tuple) and b[0] == "seq" and isinstance(b[1], list) and len(b[1]) >= 2 and _strip(b[1][0])[:1] == ("id",)): continue
        if _has_binder(b) or _strip(b[1][0])[1] == d[1] or _strip(b[1][0])[1] not in fn_names or _strip(b[1][0])[1] in {p[1] for p in lam[1]}: continue      # 先頭が定義済みの名前でなければ、呼びでなく器の字面
        fw[d[1]] = ([p[1] for p in lam[1]], b)
    def simple(a):
        a = _strip(a)
        return isinstance(a, tuple) and a[:1] in (("id",), ("lit",))
    def expand(t):
        if isinstance(t, list): return [expand(x) for x in t]
        if not isinstance(t, tuple) or not t: return t
        t = tuple(expand(x) if isinstance(x, (tuple, list)) else x for x in t)
        if t[0] == "seq" and isinstance(t[1], list) and t[1]:
            h = _strip(t[1][0])
            if h[:1] == ("id",) and h[1] in fw and len(t[1]) - 1 == len(fw[h[1]][0]):
                ps, body = fw[h[1]]; args = t[1][1:]
                use = [_count_id(body, p) for p in ps]
                nonsimple = [p for p, a in zip(ps, args) if not simple(a)]
                ok = all(use[i] == 1 for i, p in enumerate(ps) if p in nonsimple)
                if ok and nonsimple:
                    order = []; _first_ids(body, set(nonsimple), order)
                    ok = order == nonsimple            # 式を持つ実引数の評価の順が、本体の中でも同じ
                if ok:
                    return expand(_subst(body, dict(zip(ps, args))))
        return t
    new_defs = [expand(d) for d in newdefs]
    new_out = [expand(n) for n in out]
    # どこからも呼ばれない作った関数を消す(生きている所から、呼びをたどる)
    alive = set()
    def refs(t):
        if isinstance(t, list):
            for x in t: refs(x)
        elif isinstance(t, tuple) and t:
            if t[0] == "id" and len(t) == 2: alive.add(t[1])
            for x in t[1:]:
                if isinstance(x, (tuple, list)): refs(x)
    for n in new_out: refs(n)
    for d in new_defs:
        if d[1] not in gen_names: refs(d[2])
    bynm = {d[1]: d for d in new_defs}
    todo = [nm for nm in alive if nm in gen_names]; done = set()
    while todo:
        nm = todo.pop()
        if nm in done: continue
        done.add(nm)
        before = set(alive); refs(bynm[nm][2])
        todo += [x for x in alive - before if x in gen_names]
    new_defs = [d for d in new_defs if d[1] in alive or d[1] not in gen_names]
    return new_defs + new_out


def main(argv):
    if not argv:
        print("使い方: python3 sign_fuse.py file.sn"); return 1
    import os
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import sign_interp, sign_asm
    path = argv[0]
    nodes = sign_interp.parse_source(open(path, encoding="utf-8").read(), path)
    if any(n[0] == "importspread" for n in nodes):
        try:
            sign_asm.IMPORT_DIR[0] = os.path.dirname(os.path.abspath(path))
            nodes = sign_asm.expand_imports(nodes)
        except Exception as e:
            print("取り込みを展開できません:", e); return 1
    a = Analysis(nodes)
    for nm in a.defs:
        i = a.info[nm]
        print("%-16s 純=%-5s 終わる=%-5s %s" % (nm, i.pure, i.terminates, "; ".join(i.reasons[:2])))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
