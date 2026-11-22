"""仕様書(coproduct_spec.md・value_spec.md)の見本を抜き出して、--strict の実装と突き合わせる。
使い方: python3 spec_audit.py 仕様書.md [-v]
見本の形: `- `源`（`定義`、`定義`）→ …、値 `X`、知らせ名…`。値・断りの名前・知らせの名前を比べ、読めない形は数えずに「読めず」とする。"""
import sys, re, os, importlib.util
sys.setrecursionlimit(20000)
here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("S", os.path.join(here, "sign_interp.py")); S = importlib.util.module_from_spec(spec); spec.loader.exec_module(S)
sys.path.insert(0, here)
from fixblank import fix as fixblank
CODE = re.compile(r"`([^`]*)`")
def to_src(span):
    return span.replace("⇥", "\t")
def spans_joined(s):
    """`a` ⏎ `b` ⏎ `c` → 'a\nb\nc'(⏎ でつながる code の並び)。つながらない所は None"""
    parts = re.split(r"\s*⏎\s*", s.strip())
    out = []
    for p in parts:
        m = re.fullmatch(r"`([^`]*)`", p.strip())
        if not m: return None
        out.append(to_src(m.group(1)))
    return "\n".join(out)
def split_top(s, sep="、"):
    out, cur, inside = [], "", False
    for ch in s:
        if ch == "`": inside = not inside
        if ch == sep and not inside: out.append(cur); cur = ""
        else: cur += ch
    out.append(cur); return out
def parse(line):
    m = re.match(r"^- (`[^→]*?)(?:（(.*)）)?\s*→\s*(.*)$", line)
    if not m: return None
    left, ctx, right = m.group(1), m.group(2), m.group(3)
    src = spans_joined(left.strip())
    if src is None: return None
    defs = []
    if ctx:
        for piece in split_top(ctx):
            d = spans_joined(piece.strip().rstrip("。"))
            if d is not None and re.match(r"^#?[\w']+\s*(:|\[|\w)", d): defs.append(d)
    return src, defs, right
WARN_NAMES = ("leftover-lambda", "bare-function-return", "dollar-non-function", "level-mismatch", "name-shadow", "address-number-mix", "address-without-arrow", "pointfree-not-folded")
def expect(right):
    """('val', tokens) / ('refuse', name) / None。知らせの名前の集合も返す"""
    right = re.sub(r"（[^）]*）", lambda m: m.group(0) if re.match(r"（値", m.group(0)) else "", right)       # 括弧の注釈は期待にしない(値の括弧だけ残す)
    right = re.sub(r"実装は[^）]*", "", right)                          # 「実装は …、§6.4」は設計者の JS 実装の注記で、仕様の期待ではない
    right = re.sub(r"（[^）]*(?:は|を)[^）]*）", lambda m: m.group(0) if "値" in m.group(0)[:3] else "", right) if False else right
    warns = set(re.findall(r"\b((?:leftover-lambda|bare-function-return|dollar-non-function|level-mismatch|name-shadow|address-number-mix|address-without-arrow|pointfree-not-folded|dollar-non-function))\b", right))
    none_w = "知らせ無し" in right
    mv = re.search(r"値\s*`([^`]*)`", right) or re.search(r"、値\s+(-?\d+|!_|\$\w+|0x[0-9A-Fa-f]+)(?=[、（\s]|$)", right)
    if mv:
        v = mv.group(1)
        if any(c in v for c in "[](){}`"): return None, warns, none_w
        return ("val", v.split()), warns, none_w
    mg = re.match(r"\s*(G\d+|[a-z]+(?:-[a-z]+)+)\b", right)
    if mg and mg.group(1) not in WARN_NAMES: return ("refuse", mg.group(1)), warns, none_w
    return None, warns, none_w
def norm_out(o):
    t = re.sub(r"[\[\],]", " ", o).split()
    return t
def run(src):
    S.STRICT_GATES = True
    try: S.WARNINGS.clear(); S.WARN_LINES.clear(); S.STORE_ROWS.clear()
    except Exception: pass
    try:
        r = S.run(src); out = S.show(r[-1]) if r else ""; err = None
    except BaseException as e:
        out = ""; err = str(e).split("\n")[0]
    return out, err, {k[0] for k in S.WARNINGS}
PRE = ("inc : x ? x + 1\ndouble : x ? x * 2\nd : x ? x * 10\ng : x ? x * 10\nadd : x y ? x + y\nf2 : x y ? x - y\nf3 : a b c ? a + b + c\nuse : f x ? @f x\n"
           "vs : 1 , 2 , 3\ni : _\npw : [a : 1]\nw : pw ' zz\n"
           "gq :\n\t\tx\n\t\ty : 1\n\t? x + y\n\ngd :\n\t\tys\n\t\tzs : 3\n\t? ys + zs\n")                    # §4 の前書きの共通の定義

def judge(exp, warns, none_w, out, err, ws):
    """期待(expect の結果)と実際(run の結果)を比べる。食い違いの理由を返す(一致なら None)。"""
    why = None
    if exp and exp[0] == "val":
        if err: why = f"断り: {err[:70]}"
        elif norm_out(out) != exp[1]: why = f"値 {out!r} (期待 {' '.join(exp[1])})"
    elif exp and exp[0] == "refuse":
        if not err or exp[1] not in err.split(":")[0] + err[:60]: why = f"断りのはずが {('断り: ' + err[:60]) if err else '値 ' + out}"
    if why is None and exp and exp[0] == "val" or (exp and exp[0] == "refuse" and why is None) or exp is None:
        if warns and not err:
            missing = warns - ws
            if missing: why = f"知らせ {sorted(missing)} が出ない(出た: {sorted(ws)})"
        if none_w and not warns and not err:
            extra = ws & {"bare-function-return", "level-mismatch"}                  # 仕様の前書き: 根に残った関数の leftover-lambda と値の `$` の dollar-non-function は、例で省いた所がある
            if extra and why is None: why = f"知らせ無しのはずが {sorted(extra)}"
    return why

if __name__ == "__main__":
    path = sys.argv[1]; verbose = "-v" in sys.argv
    stats = {"ok": 0, "ng": 0, "skip": 0}; ngs = []

    for ln_no, line in enumerate(open(path, encoding="utf-8"), 1):
        p = parse(line.rstrip("\n"))
        if not p: continue
        src, defs, right = p
        exp, warns, none_w = expect(right)
        if exp is None and not warns and not none_w: stats["skip"] += 1; continue
        user_names = {re.match(r"#?([\w']+)", d).group(1) for d in defs if re.match(r"#?([\w']+)", d)}
        pre = "".join(l + "\n" for l in PRE.splitlines() if l.split(" ")[0] not in user_names)
        prog = pre + "\n\n".join(defs) + ("\n\n" if defs else "") + src
        prog = fixblank(prog) + "\n"
        out, err, ws = run(prog)
        why = judge(exp, warns, none_w, out, err, ws)
        if why: stats["ng"] += 1; ngs.append((ln_no, line.strip()[:140], why))
        else: stats["ok"] += 1
    print(f"一致 {stats['ok']} / 食い違い {stats['ng']} / 読めず {stats['skip']}")
    for n, l, w in ngs: print(f"L{n}: {l}\n      → {w}")
