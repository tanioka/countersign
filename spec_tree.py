"""仕様 §1.3「出力の木」の出力(部分実装)。読む段(余積の解決)のうち、1 行の並びの construct・apply・compose・unit と、根の中置の節を出す。
使い方: python3 spec_tree.py ファイル.sn      各行の木を出す(出せない形は「未対応」)
        tree_of(源, 定義の行の列) → 木の文字列 / None(未対応)
読まない形(関数の本体の実体 inst・defer、`!_` と分かる値の消去 R49・R137、部分適用、字下げの行)は None を返し、間違った木を出さない。"""
import re

TIGHT = ["'", "@", "<=", ">=", "<<", ">>", "==", "!==", "!=", "<", ">", "=", "+", "-", "*", "/", "%", "^", "~", "&&", "||", ";;"]
ROOT = [":", "|", "&", ";", ",", "#"]                       # 並びを切る段(P1 の 1〜9 のうち、ここで扱う物)。左ほど緩い
ROOT_SEP = {":": 1, ";": 2, "|": 3, "&": 4, ",": 8, "#": 5}
PAIR = {"(": ")", "[": "]", "{": "}"}

def tokens(s):
    """深さ 0 の語に切る(括りと文字列・文字は 1 語)。切れなければ None"""
    out, cur, depth, i, q = [], "", 0, 0, None
    while i < len(s):
        ch = s[i]
        if q:
            cur += ch
            if ch == "\\" and i + 1 < len(s): cur += s[i + 1]; i += 1
            elif ch == q: q = None
        elif ch in "\"'" and (ch == '"' or (cur == "" and i + 2 < len(s) and s[i + 2] == "'")) :
            q = ch; cur += ch
        elif ch in PAIR: depth += 1; cur += ch
        elif ch in ")]}": depth -= 1; cur += ch
        elif ch.isspace() and depth == 0:
            if cur: out.append(cur); cur = ""
        else: cur += ch
        i += 1
    if cur: out.append(cur)
    return out if depth == 0 and q is None else None

def arity_of(rhs):
    """`x y ?` の頭から口: 整数 / ('var', 最低の数)(最後の括りが 2 名以上か `~` を持つ=残りを丸ごと受ける、R64) / None"""
    m = re.match(r"^(.*?)\s*\?(?:\s|$)", rhs)
    if not m: return None
    ps = tokens(m.group(1))
    if ps is None or not ps: return None
    last = ps[-1]
    if last.startswith("["):
        inner = tokens(last[1:-1]) or []
        if len(inner) != 1 or "~" in last: return ("var", len(ps))
    return len(ps)

PREDEF = set()
def kinds_from(defs):
    """名前 → ('F', 口) / ('A',) / ('I',)(恒等射)。読めない定義の名前は載せない"""
    env = {}
    for d in defs:
        first = d.split("\n")[0]
        m = re.match(r"^#?([\w']+)\s*:\s*(.*)$", first)
        if not m: continue
        nm, rhs = m.group(1), m.group(2)
        if re.match(r"^\s*$", rhs) and "\n" in d: env[nm] = None; continue          # 字下げの本体は未対応
        r_ = rhs.strip()
        mv = re.fullmatch(r"\$([\w']+)", r_)
        if mv and (env.get(mv.group(1)) or ("",))[0] in ("A", "V"): env[nm] = ("V",); continue     # 値に付けた `$` は `!_` と分かる値(R99)
        if re.fullmatch(r"[a-z][\w']*", r_) and r_ not in env and r_ not in PREDEF: env[nm] = ("V",); continue   # 未定義の名前(R21)
        if re.fullmatch(r"[a-z][\w']*", r_) and (env.get(r_) or ("",))[0] == "V": env[nm] = ("V",); continue
        mi = re.fullmatch(r"([a-z][\w']*) ' ([a-z][\w']*)", r_)
        if mi and ((env.get(mi.group(1)) or ("",))[0] == "V" or (mi.group(2) not in env and mi.group(2) not in PREDEF and (env.get(mi.group(1)) or ("",))[0] == "A")): env[nm] = ("V",); continue
        a = arity_of(rhs)
        if a is not None: env[nm] = ("F", a, not re.search(r"\[", rhs.split("?")[0]))
        elif rhs.strip() == "_": env[nm] = ("I",)
        elif re.fullmatch(r"\$[\w']+", rhs.strip()): env[nm] = ("A",) if (env.get(rhs.strip()[1:]) or ("",))[0] in ("F", "I") else None   # 値に付けた `$` は `!_` と分かる値(R99)
        elif re.search(r"['@~]", rhs.strip()) and not rhs.strip().startswith('"') and "?" not in rhs: env[nm] = None   # 引いた物・ずらした物は `!_` になりうる(R26)
        elif re.fullmatch(r"[a-z][\w']*", rhs.strip()) and (env.get(rhs.strip()) is None or env[rhs.strip()][0] != "A"): env[nm] = None
        elif re.fullmatch(r"-?\d+(?: , -?\d+)*|0x[0-9A-Fa-f]+|\$[\w']+|[a-z][\w']*(?: [-+*/<>=!@'][=]? [\w']+)*|\[[^\[\]]*\]|\([^()]*\)|\"[^\"]*\"", rhs.strip()) and "?" not in rhs: env[nm] = ("A",)
        else: env[nm] = None
    return env

def leaf_text(t):
    """葉の綴り: 丸い括りは(入れ子も)角括りに、空白は 1 つに。文字列の中は変えない"""
    t = re.sub(r"\s+", " ", t.strip())
    out, q = [], False
    for ch in t:
        if ch == '"': q = not q
        out.append(("[" if ch == "(" else "]" if ch == ")" else ch) if not q else ch)
    return "".join(out)

def classify(tok, env):
    c = _classify(tok, env)
    if c and c[0] == "A" and re.fullmatch(r"\$[\w']+", tok):
        k = env.get(tok[1:])
        if k is None: return None
        if k[0] in ("A", "V"): return ("V", tok)                                # `$` の先が値: `!_` と分かる値(R99)
    return c
def _classify(tok, env):
    """語 → ('A', 綴り) / ('F', 口, 名前) / ('I', 名前) / ('V', 綴り) / None(未対応)"""
    if len(tok) > 1 and tok.endswith("~") and not tok.startswith("~") and "~" not in tok[:-1]:       # 後置 `~`(撒く、R51・R84)
        base = tok[:-1]
        if base.startswith("[") and base.endswith("]"):
            its = tokens(base[1:-1]) or []
            cs = [classify(x, env) for x in its]
            if its and all(c is not None for c in cs):
                if all(c[0] == "V" for c in cs): return ("V", tok)               # `!_` ばかりの器を撒けば消える
                if all(c[0] == "A" for c in cs): return ("A", leaf_text(tok))
            return None
        c = classify(base, env)
        if c is None: return None
        if c[0] == "V": return ("V", tok)
        if c[0] == "A": return ("A", leaf_text(tok))
        return None
    if re.fullmatch(r"-?\d+|0[xXbBrRuU][0-9A-Za-z]+|\d\dx[0-9A-Fa-f]+|\"[^\"]*\"|'.'|\$[\w']+|\$\$[\w']+", tok): return ("A", leaf_text(tok))
    if tok[0] == "[":
        sec = section(tok)
        if sec is not None: return sec
    if tok[0] == "(" and re.search(r"['@~]", tok):
        g = _eval_group(tok, env)
        if g is not None: return g
    if tok[0] in "([":
        inner = tokens(tok[1:-1])
        if inner is None or any(t in TIGHT + ROOT for t in inner) is False and False: return None
        if tok[0] == "(" and inner and len(inner) > 1 and not _plain(inner, env):
            cs = [_classify(t, env) if not (t in TIGHT or t in ROOT) else "op" for t in inner]
            if all(c is not None and c != "op" and c[0] != "V" for c in cs) and any(c[0] == "F" for c in cs):
                r = resolve_seq(inner, env)
                if r and r.startswith(("(apply", "(construct")) and "(unit" not in r: return ("A", leaf_text(tok))
        if tok[0] == "(" and len(inner) == 1 and not re.fullmatch(r"[^\w\s]+", inner[0]): return classify(inner[0], env) if inner[0][0] not in "([" else None
        if any(re.fullmatch(r"[^\w\s$\[\]()'\"~]+", t) or t in ("'",) for t in inner): return ("A", leaf_text(tok)) if _plain(inner, env) else None
        return ("A", leaf_text(tok)) if _plain(inner, env) else None
    if tok == "_": return ("I", "_")
    m = re.fullmatch(r"[\w']+", tok)
    if m:
        k = env.get(tok)
        if k is None: return None
        if k[0] == "V": return ("V", tok)
        if k[0] == "F": return ("F", k[1], tok)
        if k[0] == "I": return ("I", tok)
        return ("A", tok)
    return None

FOLDOPS = {"+", "-", "*", "/", "%", "^", "|", "&", ";", "<", "<=", "=", ">=", ">", "==", "||", ";;", "&&"}
PLAINOPS = {"<<", ">>", "'", "@", "!=", "!==", "~"}
def section(tok):
    """点なしの括り `[+]` `[+ 1]` `[' 0]` `[<<]` → ('F', 口, 綴り)。読めない形は None"""
    inner = tokens(tok[1:-1])
    if not inner or any("," in t for t in inner) or any(re.search(r"[A-Za-z_(\[$]", t) and not re.fullmatch(r"\$\w+|-?\d+", t) for t in inner): return None
    sp = re.sub(r"\s+", " ", tok)
    if len(inner) == 1 and inner[0] in FOLDOPS: return ("F", ("var", 1), sp)
    if len(inner) == 1 and inner[0] in PLAINOPS: return ("F", 2, sp)
    if len(inner) == 2 and (inner[0] in FOLDOPS | PLAINOPS) != (inner[1] in FOLDOPS | PLAINOPS): return ("F", 1, sp)
    return None
def _plain(inner, env):
    if any(re.search(r"['@~]", t) for t in inner): return False
    """括りの中が、字面・値の名前・点なしでない中置だけの時 True(中の木は出さず綴りで葉にする)"""
    for t in inner:
        if t in TIGHT: continue
        if re.fullmatch(r"-?\d+|0x[0-9A-Fa-f]+|\$[\w']+", t): continue
        if re.fullmatch(r"[\w']+", t):
            k = env.get(t)
            if k is None or k[0] != "A": return False
            continue
        if t[0] in "([":
            if not (_plain(tokens(t[1:-1]) or [], env)): return False
            continue
        return False
    return len(inner) > 0 and inner[0] not in TIGHT and inner[-1] not in TIGHT

def fold_tight(toks, env):
    """隣の語を中置でまとめた項の列にする。まとまった項は ('A', '[a + b]')。点なしの座・片側の欠けは None"""
    items, i = [], 0
    n = len(toks)
    while i < n:
        t = toks[i]
        if t in TIGHT or t in ROOT: return None
        j = i + 1
        grp = [t]
        while j + 1 < n and toks[j] in TIGHT and toks[j + 1] not in TIGHT and toks[j + 1] not in ROOT:
            grp += [toks[j], toks[j + 1]]; j += 2
        if len(grp) == 1: items.append(("tok", t))
        else: items.append(("fold", grp)); 
        i = j
    return items

def resolve_seq(toks, env, root_alone=False):
    """1 つの並び(根の演算子を含まない語の列)→ 木。root_alone: 並びが畳んだ中置 1 つだけなら (op a b) の節で出す"""
    items = fold_tight(toks, env)
    if items is None: return None
    if len(items) == 1 and items[0][0] == "fold" and root_alone:
        g = items[0][1]
        if len(g) != 3: return None
        a, b = operand(g[0], env, True), operand(g[2], env, True)
        return None if a is None or b is None else f"({g[1]} {a} {b})"
    terms = []
    for kind, v in items:
        if kind == "fold":
            g = v
            if any(x in ("'", "@", "~") for x in g): return None
            c = [classify(x, env) for x in g[::2]]
            if any(x is None or x[0] != "A" for x in c): return None
            t_ = leaf_text(g[0])
            for k_ in range(1, len(g), 2): t_ = f"({g[k_]} {t_} {leaf_text(g[k_ + 1])})"
            terms.append(("A", t_))
        else:
            c = classify(v, env)
            if c is None: return None
            terms.append(c)
    if any(t[0] == "V" for t in terms) and any(t[0] == "F" and not _plain_head(t[-1], env) for t in terms):
        if any(t[0] == "F" and not _plain_head(t[-1], env) and not t[-1].startswith("[") for t in terms): return None      # 名前のある関数の括りの口に入る位置の見分けは未対応(R122・R64)
        terms = [("A", t[1]) if t[0] == "V" else t for t in terms]               # 点なしの括りは `!_` と分かる値も受けるので木に残る(R95・R137)。参照の口・点なしの括りは `!_` と分かる値も受けるので木に残る(R95・R122)
    terms = [t for t in terms if t[0] != "V"]                                   # `!_` と分かる値は積の単位で消える(R49・R137)
    if not terms: return None
    return build(terms)
def _plain_head(name, env):
    return not name.startswith("[") and (env.get(name) is None or env[name][0] != "F" or len(env[name]) < 3 or env[name][2])

def operand(tok, env, root):
    c = classify(tok, env)
    if c is None:
        if root and re.fullmatch(r"~?-?\d+~?|[\w']+|[\[(][^?:]*[\])]", tok) and not (re.fullmatch(r"[\w']+", tok) and (env.get(tok) or ("",))[0] in ("F", "I")) and "_" != tok:
            return leaf_text(tok)                                              # 根の中置の被演算子は綴りのまま(値の読みに依らない)
        return None
    if c[0] == "A": return c[1]
    if c[0] == "V": return c[1]
    return f"(unit {c[-1]})"

def hole_rewrite(terms):
    """`f _ 2`(f の口が 2 以上で、口の数ちょうどの実引数のうち 1 つが穴 `_`)→ (unit (? [$p0] (apply f (construct … $p0 …))))。R16"""
    out, i = [], 0
    while i < len(terms):
        t = terms[i]
        if t[0] == "F" and isinstance(t[1], int) and t[1] >= 2 and i + t[1] < len(terms) + 0 and (i == len(terms) - 1 or True):
            seg = terms[i + 1:i + 1 + t[1]]
            if len(seg) == t[1] and sum(1 for x in seg if x[0] == "I" and x[1] == "_") == 1 and all(x[0] == "A" or (x[0] == "I" and x[1] == "_") for x in seg):
                args = ["$p0" if x[0] == "I" else x[1] for x in seg]
                out.append(("A", f"(unit (? [$p0] (apply {t[-1]} (construct {' '.join(args)}))))"))
                i += 1 + t[1]; continue
        out.append(t); i += 1
    return out
def build(terms):
    terms = hole_rewrite(terms)
    if len(terms) > 1 and any(t[0] == "I" and t[1] == "_" for t in terms): return None    # 並びの中の `_` は穴か恒等射か(R16・R44)で未対応
    out, i, n = [], 0, len(terms)
    while i < n:
        t = terms[i]
        if t[0] == "A": out.append(t[1]); i += 1; continue
        if i > 0 and t[0] == "I" and t[1] == "_": return None                 # 並びの途中の `_` は穴(R16)
        j = i
        while j < n and terms[j][0] in ("F", "I"): j += 1                      # 関数の連なり(合成)
        run = terms[i:j]
        args = []
        k = j
        while k < n and terms[k][0] == "A": args.append(terms[k][1]); k += 1
        tail = terms[k:]
        if any(x[0] == "A" for x in tail): return None                         # 適用の後ろにまた関数と値: 部分適用・畳みは未対応
        if not args:
            out += [f"(unit {r[-1]})" for r in run] if len(run) == 1 else [f"(unit (compose {' '.join(r[-1] for r in run)}))"]
            i = j; continue
        if run[0][0] == "I": return None                                     # 恒等射が頭の適用は R44・R74 の読みで未対応
        if len(run) > 1:
            if any(r[0] != "F" or isinstance(r[1], tuple) for r in run if r[0] == "F"): return None
            mouth = 1 + sum((r[1] if r[0] == "F" else 1) - 1 for r in run)
        else: mouth = run[0][1]
        head = run[0][-1] if len(run) == 1 else "(compose " + " ".join(r[-1] for r in run) + ")"
        spread = any(x.endswith("~") for x in args)
        if isinstance(mouth, tuple):
            if len(args) < mouth[1] and not spread: return None
            use, rest = len(args), []
        elif spread:
            use, rest = len(args), []                                          # 撒いた流れは口を埋めきる(R51)
        else:
            use, rest = (len(args), []) if len(args) < mouth else (mouth, args[mouth:])
        a = args[:use]
        app = f"(apply {head} {a[0] if len(a) == 1 else '(construct ' + ' '.join(a) + ')'})"
        if not isinstance(mouth, tuple) and not spread and len(args) < mouth: app = f"(unit {app})"          # 部分適用は口の開いた関数として残る(R136)
        out.append(app); out += rest
        out += [f"(unit {x[-1]})" for x in tail]
        i = n
    return out[0] if len(out) == 1 else "(construct " + " ".join(out) + ")"

def fold_chain(g, env):
    """畳んだ中置が 3 つ以上の語(同じ演算子の連なり)なら左結合の入れ子 `(+ (+ a b) c)`"""
    if len(g) < 3 or len(set(g[1::2])) != 1: return None
    ops = [operand(x, env, True) for x in g[::2]]
    if any(o is None for o in ops): return None
    t = ops[0]
    for o in ops[1:]: t = f"({g[1]} {t} {o})"
    return t

def tree_of(src, defs=(), kinds="eval"):
    """源(1 行)の木。出せない形は None。kinds: "text"(綴りから)/ "eval"(評価器に聞く、P1)"""
    if "\n" in src.strip(): return None
    env = kinds_from(list(defs)) if kinds == "text" else kinds_from_eval(list(defs))
    if env is None: return None
    toks = tokens(src.strip())
    if not toks: return None
    seps = [i for i, t in enumerate(toks) if t in ROOT_SEP]
    if seps and toks[seps[0]] == ":":
        return def_tree(toks, seps, env)
    if seps:
        if any(toks[i] != toks[seps[0]] for i in seps) or seps[0] == 0 or seps[-1] == len(toks) - 1: return None
        op = toks[seps[0]]
        parts, prev = [], 0
        for i in seps + [len(toks)]: parts.append(toks[prev:i]); prev = i + 1
        if any(not p for p in parts): return None
        sides = [resolve_seq(p, env, root_alone=True) for p in parts]
        if any(x is None for x in sides): return None
        if op == "," and any(_absorbs(p, env) for p in parts[:-1]): return None     # 辺の中で畳む(R19)
        t = sides[-1]
        for x in reversed(sides[:-1]): t = f"({op} {x} {t})"                   # `,` は右へ入れ子
        return t
    r = resolve_seq(toks, env, root_alone=True)
    if r is None:
        items = fold_tight(toks, env)
        if items and len(items) == 1 and items[0][0] == "fold": return fold_chain(items[0][1], env)
    return r

def _absorbs(p, env):
    """`,` の左の並びが、口の数の決まらない関数(残りを受ける・不明)を頭に持てば、右の辺まで受ける(R19・R66)"""
    for t in p:
        k = env.get(t) if re.fullmatch(r"[\w']+", t) else None
        if k and k[0] == "F" and (isinstance(k[1], tuple) or not k[2]): return True
        if t.startswith("["): return True
    return False
def def_tree(toks, seps, env):
    """`名前 : 右辺`。右辺が `仮引数 ? 本体`(仮引数は名前だけ)なら (? [仮引数] 本体)、値なら右辺の木"""
    if seps != [1] or len(toks) < 3: return None
    name, rhs = toks[0], toks[2:]
    if "?" in rhs:
        q = rhs.index("?")
        ps, body = rhs[:q], rhs[q + 1:]
        if not ps or not body or any(not re.fullmatch(r"[a-z][\w']*", p) for p in ps): return None
        e2 = dict(env)
        for p in ps: e2[p] = ("A",)
        if name in env and env[name] and env[name][0] == "F": e2[name] = env[name]
        else: e2[name] = ("F", len(ps), True)
        b = resolve_seq(body, e2, root_alone=True)
        if b is None: return None
        return f"(: {name} (? [{' '.join(ps)}] {b}))"
    r = resolve_seq(rhs, env, root_alone=True)
    return None if r is None else f"(: {name} {r})"

def kinds_from_eval(defs):
    """P1: 名前の種類を評価器に聞く。定義を strict で評価した Env から、Closure → F(口)、恒等射 → I、`!_` と分かる値(unit_like) → V、ほかの値 → A。
    評価に失敗した定義の名前は載せない(None=未対応。誤った木を出さない)。"""
    import sign_interp as S
    from fixblank import fix
    old = S.STRICT_GATES; S.STRICT_GATES = True
    env = {}
    try:
        e = S.Env(None)
        names = []
        try:
            nodes = S.parse_source(fix("\n\n".join(defs)) + "\n")
        except BaseException: return None
        for n in nodes:
            try: S.ev(n, e)
            except BaseException:
                if n and n[0] == "def": names.append((n[1], False)); continue
            if n and n[0] == "def": names.append((n[1], True))
        bad = {nm for nm, ok in names if not ok}
        for nm, ok in names:
            if nm in bad: env[nm] = None; continue
            v = e.vars.get(nm)
            if isinstance(v, S.Closure):
                ps = v.params
                if not isinstance(ps, (list, tuple)): env[nm] = None; continue
                dn = (e.__dict__.get("defnodes") or {}).get(nm)
                has_def = any((p[0] == "name" and p[2] is not None) or (p[0] == "destr" and len(p) > 3 and p[3]) for p in ps)
                if has_def or not (isinstance(dn, tuple) and dn and dn[0] == "lam"): env[nm] = None; continue     # 既定値のある口・括りでない定義(`z : @$inc`)の種類は仕様が「未知」
                last = ps[-1] if ps else None
                var = last is not None and last[0] == "destr" and (len(last[1]) > 1 or last[2])
                env[nm] = ("F", ("var", len(ps)) if var else len(ps), all(p[0] == "name" for p in ps))
            elif v is S.ID or type(v).__name__ == "_Id": env[nm] = ("I",)
            else:
                dn = (e.__dict__.get("defnodes") or {}).get(nm)
                try: vv = S.unit_like(("id", nm), e, set()) or (isinstance(dn, tuple) and dn and dn[0] == "addr" and S.unit_like(dn, e, set()))     # R49: `q : $w` のように `!_` と分かる値を右辺に持つ名前も(評価器の zeronames はまだ持たない→ OPEN_QUESTIONS)
                except BaseException: vv = False
                env[nm] = ("V",) if vv else ("A",)
        env["\0env"] = e
    finally: S.STRICT_GATES = old
    return env

def _eval_group(tok, env):
    """P2: `'`・`@`・`~` を含む括りの項を評価器に聞く。`!_` と分かる → ('V', 綴り)、閉じた式で値がある → ('A', 綴り)、分からない → None"""
    e = env.get("\0env")
    if e is None: return None
    import sign_interp as S
    mm = re.fullmatch(r"\(\s*(?:0x[0-9A-Fa-f]+|\d\dx[0-9A-Fa-f]+)\s*'\s*(.+?)\s*\)", tok)
    if mm and not re.search(r"(?<![0-9A-Za-z])[A-Za-z_]", re.sub(r"0x[0-9A-Fa-f]+", "", mm.group(1))): return ("A", leaf_text(tok))     # 番地を数や範囲で引いた中身は機械の読みで、解決器は `!_` と言わない(評価器は機械を持たず `!_` になる)
    old = S.STRICT_GATES; S.STRICT_GATES = True
    try:
        node = S.parse_source(tok + "\n")
        if len(node) != 1: return None
        node = node[0]
        if S.unit_like(node, e, set()): return ("V", leaf_text(tok))
        inner = node[1] if node[0] == "block" else node
        if S.closed_expr(inner, e, set()):
            v = S.quiet_ev(inner, e)
            if v is None or isinstance(v, S.Closure) or v is S.ID: return None      # 値が関数かもしれない括り(`(shape ' cube) 3`)は種類を言わない
            return ("A", leaf_text(tok))
    except BaseException: return None
    finally: S.STRICT_GATES = old
    return None

def items_of(text):
    """ファイルを、字下げの無い行で始まる項目(行番号, 本文の行の列)に分ける。空行と `--` の注釈だけの行は飛ばす"""
    out = []
    for no, ln in enumerate(text.split("\n"), 1):
        if not ln.strip(): continue
        if ln[0] in " \t" and out: out[-1][1].append(ln)
        elif not ln[0] in " \t": out.append([no, [ln]])
    return out

def main(argv):
    """`sign.py --tree ファイル.sn`: 定義を先に集め(P2)、各項目の木を出す。出せない形は理由を添えて「未対応」"""
    files = [a for a in argv if not a.startswith("-")]
    if not files: print("使い方: sign.py --tree ファイル.sn", file=__import__("sys").stderr); return 2
    try: text = open(files[0], encoding="utf-8").read()
    except OSError as e: print(f"エラー: {files[0]} を読めません({e})", file=__import__("sys").stderr); return 1
    its = items_of(text)
    defs = ["\n".join(b) for _, b in its if re.match(r"^#?[\w']+\s*:", b[0])]
    for no, b in its:
        t = None
        if len(b) == 1:
            try: t = tree_of(b[0], defs)
            except Exception: t = None
        print(f"{no}: {t if t is not None else '未対応'}")
    return 0

if __name__ == "__main__":
    import sys
    sys.exit(main(sys.argv[1:]))
