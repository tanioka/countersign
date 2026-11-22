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

def kinds_from(defs):
    """名前 → ('F', 口) / ('A',) / ('I',)(恒等射)。読めない定義の名前は載せない"""
    env = {}
    for d in defs:
        first = d.split("\n")[0]
        m = re.match(r"^#?([\w']+)\s*:\s*(.*)$", first)
        if not m: continue
        nm, rhs = m.group(1), m.group(2)
        if re.match(r"^\s*$", rhs) and "\n" in d: env[nm] = None; continue          # 字下げの本体は未対応
        a = arity_of(rhs)
        if a is not None: env[nm] = ("F", a)
        elif rhs.strip() == "_": env[nm] = ("I",)
        elif re.fullmatch(r"\$[\w']+", rhs.strip()): env[nm] = ("A",) if (env.get(rhs.strip()[1:]) or ("",))[0] in ("F", "I") else None   # 値に付けた `$` は `!_` と分かる値(R99)
        elif re.search(r"['@~]", rhs.strip()) and not rhs.strip().startswith('"') and "?" not in rhs: env[nm] = None   # 引いた物・ずらした物は `!_` になりうる(R26)
        elif re.fullmatch(r"[a-z][\w']*", rhs.strip()) and (env.get(rhs.strip()) is None or env[rhs.strip()][0] != "A"): env[nm] = None
        elif re.fullmatch(r"-?\d+(?: , -?\d+)*|0x[0-9A-Fa-f]+|\$[\w']+|[a-z][\w']*(?: [-+*/<>=!@'][=]? [\w']+)*|\[[^\[\]]*\]|\([^()]*\)|\"[^\"]*\"", rhs.strip()) and "?" not in rhs: env[nm] = ("A",)
        else: env[nm] = None
    return env

def leaf_text(t):
    """葉の綴り: 丸い括りは角括りに、空白は 1 つに"""
    t = re.sub(r"\s+", " ", t.strip())
    if t.startswith("(") and t.endswith(")"):
        inner = tokens(t[1:-1])
        if inner is not None: t = "[" + " ".join(inner) + "]"
    return t

def classify(tok, env):
    c = _classify(tok, env)
    if c and c[0] == "A" and re.fullmatch(r"\$[\w']+", tok) and (env.get(tok[1:]) is None or env[tok[1:]][0] == "A"): return None   # `$` の先が値: `!_` と分かる値(R99)は未対応
    return c
def _classify(tok, env):
    """語 → ('A', 綴り) / ('F', 口, 名前) / ('I', 名前) / None(未対応)"""
    if re.fullmatch(r"-?\d+|0[xXbBrRuU][0-9A-Za-z]+|\d\dx[0-9A-Fa-f]+|\"[^\"]*\"|'.'|\$[\w']+|\$\$[\w']+", tok): return ("A", leaf_text(tok))
    if tok[0] in "([":
        inner = tokens(tok[1:-1])
        if inner is None or any(t in TIGHT + ROOT for t in inner) is False and False: return None
        if tok[0] == "(" and len(inner) == 1 and not re.fullmatch(r"[^\w\s]+", inner[0]): return classify(inner[0], env) if inner[0][0] not in "([" else None
        if any(re.fullmatch(r"[^\w\s$\[\]()'\"~]+", t) or t in ("'",) for t in inner): return ("A", leaf_text(tok)) if _plain(inner, env) else None
        return ("A", leaf_text(tok)) if _plain(inner, env) else None
    if tok == "_": return ("I", "_")
    m = re.fullmatch(r"[\w']+", tok)
    if m:
        k = env.get(tok)
        if k is None: return None
        if k[0] == "F": return ("F", k[1], tok)
        if k[0] == "I": return ("I", tok)
        return ("A", tok)
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
    return build(terms)

def operand(tok, env, root):
    c = classify(tok, env)
    if c is None: return None
    if c[0] == "A": return c[1]
    return f"(unit {c[-1]})"

def build(terms):
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
        if len(run) > 1 and any(r[0] == "F" and r[1] != 1 for r in run): return None
        head = run[0][-1] if len(run) == 1 else "(compose " + " ".join(r[-1] for r in run) + ")"
        mouth = run[0][1] if run[0][0] == "F" else 1
        if len(run) > 1 and run[0][0] != "F": mouth = 1
        if isinstance(mouth, tuple):
            if len(args) < mouth[1]: return None
            use, rest = len(args), []
        elif True:
            if len(args) < mouth: return None                                  # 部分適用
            use, rest = mouth, args[mouth:]
        a = args[:use]
        app = f"(apply {head} {a[0] if len(a) == 1 else '(construct ' + ' '.join(a) + ')'})"
        out.append(app); out += rest
        out += [f"(unit {x[-1]})" for x in tail]
        i = n
    return out[0] if len(out) == 1 else "(construct " + " ".join(out) + ")"

def tree_of(src, defs=()):
    """源(1 行)の木。出せない形は None"""
    if "\n" in src.strip(): return None
    env = kinds_from(list(defs))
    toks = tokens(src.strip())
    if not toks: return None
    # 根の演算子で切る(1 つだけ)
    seps = [i for i, t in enumerate(toks) if t in ROOT_SEP]
    if len(seps) > 1: return None
    if seps:
        i = seps[0]; op = toks[i]
        if i == 0 or i == len(toks) - 1: return None
        if op == ":":
            return None                                                        # 定義の行の木(: 名前 右辺)は未対応(右辺が関数なら ? の節)
        l = resolve_seq(toks[:i], env, root_alone=True); r = resolve_seq(toks[i + 1:], env, root_alone=True)
        if l is None or r is None: return None
        if op == "," and ("(apply" in l or "(unit" in l or "(compose" in l): return None      # 辺の中で畳む(R19)
        return f"({op} {l} {r})"
    return resolve_seq(toks, env, root_alone=True)

if __name__ == "__main__":
    import sys
    for ln in open(sys.argv[1], encoding="utf-8"):
        ln = ln.rstrip("\n")
        if ln.strip() and not ln.startswith(" ") and not ln.startswith("\t"): print(ln, "=>", tree_of(ln) or "未対応")
