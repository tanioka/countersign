"""sign_inline.py — AArch64 出力(sign_asm.py)の前に、構文木を書き換える段。

【特殊化(ref の具体化)】
`$関数` で渡した関数を `@p 引数…` で呼ぶ形は、実行時に飛び先を決めない。呼び出しの所ごとに、渡された関数を
埋め込んだ実体(`F$G`)を作り、呼び出しをそちらへ付け替える。関数の番地の引数は消える。

    ap : f x ? @f x            ap$sq : x ? sq x
    ap $sq 3            →      ap$sq 3

仕様: stack_abi.md(クロージャ・部分適用 =「コンパイル時特殊化」)、type_system.md §4 の前置 `@`。
設計者の処理系(alpha/javascript)の compile.js `specializeRefCalls` と pass4.js の単相化に合わせた所:
  - 実体の名前は `元の名前$渡した関数の名前`(`$` は Sign の字句では演算子なので、利用者の識別子とぶつからない)
  - 再帰する関数も実体になる。実体の中で、関数の仮引数を自分へそのまま渡す呼び出しは、実体自身への呼び出しになる
  - 名前の無い関数(`$[x ? …]`・`$[+ 2]`)は最上位の定義へ持ち上げる。囲む関数の仮引数を捕まえていたら、
    それを前の仮引数として足し、呼び出しの所で渡す(実体は `cap$N` という仮引数で運ぶ)
  - `@p` に当てる引数が、渡した関数の仮引数より多い・少ない形は、名指しで断る
この実装だけの選択(利用者の裁定 2026-11-13):
  - 関数の仮引数を**別の**高階関数へ渡す形(`ap2 : f x ? ap f x`)も、渡し先の実体を作って付け替える
    (設計者は構文木の段では書き換えず、アセンブリの段の単相化で拾う)
  - 残る仮引数がゼロになる形(`apply5 : ref ? @ref 5` を `apply5 $sq`)は、実体を作らず、呼び出しの所へ本体を置く

書き換えた後の木には、特殊化した呼び出しの `addr` も `input` も残らない。sign_asm.py の解析とコード生成は
そのまま使える。関数を渡していない呼び出し・`$` で番地を取るだけの形には触らない(元の木のまま)。
"""


class SpecError(Exception):
    """特殊化できない形(名指しで断る)。sign_asm.py が AsmError に包み直す。"""


MAX_INSTANCES = 256


def _param_names(params):
    out = []
    for p in params:
        if p[0] == "name": out.append(p[1])
        elif p[0] == "destr":
            out += [nm for nm in p[1] if isinstance(nm, str)]
            if len(p) > 2 and isinstance(p[2], str): out.append(p[2])
            if len(p) > 4: out += [nm for nm in p[4] if isinstance(nm, str)]
    return out


def _ids(x, out):
    if isinstance(x, tuple):
        if x[:1] == ("id",) and len(x) == 2 and isinstance(x[1], str): out.append(x[1])
        for y in x: _ids(y, out)
    elif isinstance(x, list):
        for y in x: _ids(y, out)
    return out


class Specializer:
    def __init__(self, nodes):
        self.nodes = list(nodes)
        self.fns = {}                      # 名前 → (仮引数の並び, 本体)  最上位の関数(先に書いた方が勝つ)
        self.top = set()                   # 最上位で定義された名前
        for n in self.nodes:
            d = n[1] if n[0] == "export" and len(n) > 1 and isinstance(n[1], tuple) else n
            if d[0] == "def" and isinstance(d[1], str):
                self.top.add(d[1])
                if d[2][0] == "lam" and d[1] not in self.fns: self.fns[d[1]] = (d[2][1], d[2][2])
        self.caps = {}                     # 持ち上げた関数 → 捕まえた変数の数(前の仮引数)
        self.made = {}                     # (F, ((位置, G, 捕まえた数), …)) → 実体の名前
        self.new_defs = []
        self.nlam = 0
        self.changed = False

    # ---- 関数の参照 ("fnref", G, [捕まえた変数の式…]) ----
    def as_ref(self, a, scope, encl):
        """実引数 a が、コンパイル時に分かる関数なら ("fnref", G, caps)。でなければ None。"""
        if a[:1] == ("fnref",): return a
        if a[:1] != ("addr",) or len(a) != 2: return None
        x = a[1]
        if x[:1] == ("id",) and len(x) == 2:
            if x[1] in scope: return None                       # 仮引数と同じ名前の `$X` は、その仮引数(最上位の関数ではない)
            if x[1] in self.fns: return ("fnref", x[1], [])
            return None
        lam = None
        if x[:1] == ("block",) and len(x) == 2 and isinstance(x[1], tuple) and x[1][:1] == ("lam",): lam = x[1]
        elif x[:1] == ("sec",) and len(x) >= 4 and x[1] in ("left", "right") and x[3] is not None and not (len(x) > 4 and x[4]):
            v = "_sx"
            lam = ("lam", [("name", v, None)], ("bin", x[2], ("id", v), x[3]) if x[1] == "right" else ("bin", x[2], x[3], ("id", v)))
        if lam is None: return None
        return self.hoist(lam, scope, encl)

    def hoist(self, lam, scope, encl):
        """名前の無い関数を最上位の定義にする。囲む関数の仮引数を捕まえていたら、前の仮引数として足す。"""
        params, body = lam[1], lam[2]
        if not all(p[0] == "name" and p[2] is None for p in params):
            raise SpecError("%s: `$` で渡す名前の無い関数の仮引数は、名前だけのものが出せます(括り・既定値はまだ)" % (encl or "最上位"))
        own = set(_param_names(params))
        captured = []
        for nm in _ids(body, []):
            if nm in own or nm in captured: continue
            if nm in scope: captured.append(nm); continue
            if nm in self.top or nm in ("_", "__"): continue
            raise SpecError("%s: `$` で渡す名前の無い関数が、外の局所の名前 %s を使っています(捕まえられるのは囲む関数の仮引数だけ)" % (encl or "最上位", nm))
        self.nlam += 1
        name = "%s$lam%d" % (encl or "top", self.nlam)
        cps = [("name", "cap$%s" % c, None) for c in captured]
        ren = {c: ("id", "cap$%s" % c) for c in captured}
        body2 = self.subst_ids(body, ren)
        self.fns[name] = (cps + list(params), body2); self.top.add(name)
        self.caps[name] = len(captured)
        self.new_defs.append(("def", name, ("lam", cps + list(params), body2)))
        return ("fnref", name, [("id", c) for c in captured])

    def subst_ids(self, x, ren):
        if isinstance(x, tuple):
            if x[:1] == ("id",) and len(x) == 2 and x[1] in ren: return ren[x[1]]
            if x[:1] == ("lam",):
                inner = set(_param_names(x[1]))
                ren2 = {k: v for k, v in ren.items() if k not in inner}
                return ("lam", x[1], self.subst_ids(x[2], ren2)) + tuple(x[3:])
            return tuple(self.subst_ids(y, ren) for y in x)
        if isinstance(x, list): return [self.subst_ids(y, ren) for y in x]
        return x

    # ---- 木を歩いて、関数を渡す呼び出しを付け替える ----
    def rewrite(self, x, scope, encl):
        if isinstance(x, list): return [self.rewrite(y, scope, encl) for y in x]
        if not isinstance(x, tuple): return x
        if x[:1] == ("fnref",): return x
        if x[:1] == ("lam",):
            return ("lam", x[1], self.rewrite(x[2], scope | set(_param_names(x[1])), encl)) + tuple(x[3:])
        if x[:1] == ("seq",) and len(x) == 2 and isinstance(x[1], list):
            return self.rewrite_seq(x[1], scope, encl)
        return tuple(self.rewrite(y, scope, encl) for y in x)

    def rewrite_seq(self, items, scope, encl):
        out, i, n = [], 0, len(items)
        while i < n:
            it = items[i]
            # 1. `@p 引数…` で、p が渡された関数に決まっている(実体の本体の中)
            if it[:1] == ("input",) and len(it) == 2 and it[1][:1] == ("fnref",):
                _, G, caps = it[1]
                need = len(self.fns[G][0]) - len(caps)
                args = items[i + 1:i + 1 + need]
                if len(args) < need:
                    raise SpecError("%s: `@` で呼ぶ関数 %s は引数 %d 個ですが、%d 個しか当てていません(関数を返す形はまだ出せません)" % (encl or "最上位", G, need, len(args)))
                call = self.rewrite_seq([("id", G)] + list(caps) + list(args), scope, encl)
                rest = items[i + 1 + need:]
                if i == 0 and not rest: return call
                out.append(("block", call)); i += 1 + need; continue
            # 2. 最上位の関数 F の呼び出しで、実引数に関数がある
            if it[:1] == ("id",) and len(it) == 2 and it[1] in self.fns and it[1] not in scope:
                F = it[1]; params = self.fns[F][0]
                args = items[i + 1:i + 1 + len(params)]
                refs = [(j, self.as_ref(a, scope, encl)) for j, a in enumerate(args)]
                refs = [(j, r) for j, r in refs if r is not None]
                if refs:
                    if len(args) < len(params):
                        raise SpecError("%s: 関数を渡す呼び出し %s の実引数が足りません(仮引数 %d 個に %d 個。部分適用はまだ出せません)" % (encl or "最上位", F, len(params), len(args)))
                    for j, _ in refs:
                        if params[j][0] != "name" or params[j][2] is not None:
                            raise SpecError("%s: %s の %d 番目の仮引数は括りか既定値つきなので、関数を渡せません" % (encl or "最上位", F, j + 1))
                    rest_args = [self.rewrite(a, scope, encl) for j, a in enumerate(args) if j not in dict(refs)]
                    capx = [c for _, r in refs for c in r[2]]
                    key = (F, tuple((j, r[1], len(r[2])) for j, r in refs))
                    inst = self.instance(key)
                    self.changed = True
                    if inst is None:                               # 残る仮引数がゼロ: 本体をその場へ置く
                        body = self.inline_zero(F, refs, encl)
                        new = ("block", body)
                    else:
                        new = ("seq", [("id", inst)] + capx + rest_args)
                    tail = items[i + 1 + len(params):]
                    if i == 0 and not tail: return new
                    out.append(("block", new) if new[0] == "seq" else new); i += 1 + len(params); continue
            out.append(self.rewrite(it, scope, encl)); i += 1
        return ("seq", out)

    def bind(self, F, refs, capnames):
        """F の本体で、関数の仮引数を ("fnref", G, caps) に置き換える。"""
        params, body = self.fns[F]
        ren, k = {}, 0
        for j, r in refs:
            cs = [("id", capnames[k + m]) for m in range(len(r[2]))]; k += len(r[2])
            ren[params[j][1]] = ("fnref", r[1], cs)
        return self.subst_ids(body, ren)

    def instance(self, key):
        if key in self.made: return self.made[key]
        F, spec = key
        params = self.fns[F][0]
        drop = {j for j, _, _ in spec}
        rest = [p for j, p in enumerate(params) if j not in drop]
        ncap = sum(c for _, _, c in spec)
        if not rest and not ncap:
            self.made[key] = None; return None
        if len([v for v in self.made.values() if v]) >= MAX_INSTANCES:
            raise SpecError("関数を渡す呼び出しの実体が %d 個を超えました(%s)" % (MAX_INSTANCES, F))
        name = F + "".join("$" + G for _, G, _ in spec)
        while name in self.top: name += "$"
        self.made[key] = name; self.top.add(name)
        capnames = ["cap$%d" % m for m in range(ncap)]
        refs = [(j, ("fnref", G, [None] * c)) for j, G, c in spec]
        body = self.bind(F, refs, capnames)
        newp = [("name", c, None) for c in capnames] + rest
        self.fns[name] = (newp, body)
        body = self.rewrite(body, set(_param_names(newp)), name)
        self.check_left(body, name)
        self.fns[name] = (newp, body)
        self.new_defs.append(("def", name, ("lam", newp, body)))
        return name

    def inline_zero(self, F, refs, encl):
        params = self.fns[F][0]
        ren = {params[j][1]: r for j, r in refs}
        body = self.subst_ids(self.fns[F][1], ren)
        body = self.rewrite(body, set(), encl)
        self.check_left(body, encl or F)
        return body

    def check_left(self, x, where):
        """書き換えの後に残った関数の参照は、出せない使い方。"""
        if isinstance(x, tuple):
            if x[:1] == ("fnref",):
                raise SpecError("%s: 渡された関数 %s を、`@` で呼ぶ・高階関数へそのまま渡す以外に使っています(関数を値として持ち回る形はまだ出せません)" % (where, x[1]))
            if x[:1] == ("input",) and len(x) == 2 and x[1][:1] == ("fnref",):
                raise SpecError("%s: `@` で呼ぶ関数 %s に引数を当てていません(関数を返す形はまだ出せません)" % (where, x[1][1]))
            for y in x: self.check_left(y, where)
        elif isinstance(x, list):
            for y in x: self.check_left(y, where)

    def run(self):
        out = []
        for n in self.nodes:
            d = n[1] if n[0] == "export" and len(n) > 1 and isinstance(n[1], tuple) else n
            if d[0] == "def" and d[2][0] == "lam":
                lam = d[2]
                body = self.rewrite(lam[2], set(_param_names(lam[1])), d[1])
                nd = ("def", d[1], ("lam", lam[1], body) + tuple(lam[3:])) + tuple(d[3:])
                out.append(nd if d is n else (n[0], nd) + tuple(n[2:]))
            elif d[0] == "def":
                nd = ("def", d[1], self.rewrite(d[2], set(), d[1])) + tuple(d[3:])
                out.append(nd if d is n else (n[0], nd) + tuple(n[2:]))
            else:
                out.append(self.rewrite(n, set(), None))
        if not self.changed: return self.nodes
        # 関数を受ける元の定義は、もう誰も呼ばなければ落とす(本体の `@p …` はコード生成が読めない)
        generic = {F for (F, _), v in self.made.items()}
        used = set()
        for n in out + self.new_defs:
            d = n[1] if n[0] == "export" and len(n) > 1 and isinstance(n[1], tuple) else n
            own = d[1] if d[0] == "def" else None
            for nm in _ids(d[2] if d[0] == "def" else n, []):
                if nm != own: used.add(nm)
        kept = []
        for n in out:
            d = n[1] if n[0] == "export" and len(n) > 1 and isinstance(n[1], tuple) else n
            if d[0] == "def" and d[1] in generic and d[1] not in used and n[0] != "export": continue
            kept.append(n)
        # 新しい定義は、最初の式より前(定義の並びの後ろ)に置く
        k = next((i for i, n in enumerate(kept) if not (n[0] == "def" or n[0] == "export")), len(kept))
        return kept[:k] + self.new_defs + kept[k:]


def _is_const(x):
    """部分適用で束ねる実引数に置ける式: 字面だけ(定義の時点で値が決まる。副作用も、名前の解決の順もない)"""
    return isinstance(x, tuple) and x[:1] == ("lit",) and len(x) == 2


def partial_apply(nodes):
    """部分適用(`add3 : add 3`)を、名前の関数の定義へ直す(仕様 stack_abi.md「コンパイル時特殊化」: 実行時に構造体を作らない)。

        add : a b ? a + b         add3 : pa$0 ? add 3 pa$0
        add3 : add 3        →     (`add3 5` は `add 3 5` と同じ呼び出しになる)

    直す形: 最上位の `名前 : f 字面…` で、f が最上位の関数(仮引数が全部裸の名前で既定値なし)、実引数が仮引数より少ない。
    部分適用の上の部分適用(`add4 : add3 1`)は、上から順に直すので続けて働く。実引数が字面でない形(名前・式)・括りの仮引数の関数・
    既定値のある関数は直さない(元の木のまま。sign_asm.py の「部分適用はまだ出せません」の断りに残る)。"""
    arity = {}
    out = []; changed = False
    for n in nodes:
        if n[0] == "def" and len(n) == 3 and n[2][0] == "lam" and all(p[0] == "name" and p[2] is None for p in n[2][1]):
            arity[n[1]] = len(n[2][1])
        elif n[0] == "def" and len(n) == 3 and n[2][0] == "seq" and len(n[2][1]) >= 2 and n[2][1][0][0] == "id" and n[2][1][0][1] in arity \
                and all(_is_const(x) for x in n[2][1][1:]) and len(n[2][1]) - 1 < arity[n[2][1][0][1]]:
            f = n[2][1][0][1]; k = len(n[2][1]) - 1; rest = arity[f] - k
            ps = [("name", "pa$%d" % i, None) for i in range(rest)]
            n = ("def", n[1], ("lam", ps, ("seq", list(n[2][1]) + [("id", p[1]) for p in ps])))
            arity[n[1]] = rest; changed = True
        out.append(n)
    return out if changed else nodes


def specialize(nodes):
    """関数を渡す呼び出しを実体へ付け替えた木を返す。対象が無ければ、渡された並びをそのまま返す。"""
    nodes = partial_apply(nodes)
    if not any(_has_addr(n) for n in nodes): return nodes
    return Specializer(nodes).run()


def _has_addr(x):
    if isinstance(x, tuple):
        if x[:1] == ("addr",): return True
        return any(_has_addr(y) for y in x)
    if isinstance(x, list): return any(_has_addr(y) for y in x)
    return False
