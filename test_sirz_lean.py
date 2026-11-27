"""SIR-Z の Lean の評価器(formal/lean/SirZ.lean の `ev`)と、sign_sir.py の `evaluate` を、乱数の閉じた項で突き合わせる。
Lean が無ければ(`lean` が PATH か SIRZ_LEAN に無い)飛ばす。食い違いがあれば exit 1。
使い方: python3 test_sirz_lean.py [個数] [種]"""
import os, random, shutil, subprocess, sys, tempfile
import sign_sir as S

M = 2**63 - 1
LIT = [0, 1, 2, 3, -1, -2, 5, 7, 10, -7, 100, M, M - 1, -M, -M + 1, 2**62, -(2**62)]
AO = {"+": "add", "-": "sub", "*": "mul", "/": "div", "%": "mod"}
CO = {"<": "lt", ">": "gt", "<=": "le", ">=": "ge", "=": "eq", "==": "eq", "!=": "ne"}

def gen(r, d):
    if d == 0 or r.random() < 0.2:
        return ("void",) if r.random() < 0.2 else ("int", r.choice(LIT) if r.random() < 0.7 else r.randint(-20, 20))
    k = r.choice(["op"] * 4 + ["neg", "abs", "cmp", "cmp", "chain", "and", "or", "rows"])
    g = lambda: gen(r, d - 1)
    if k == "op": return ("op", r.choice(list(AO)), g(), g())
    if k in ("neg", "abs"): return (k, g())
    if k == "cmp": return ("cmp", r.choice(["<", ">", "<=", ">=", "=", "!="]), g(), g())
    if k == "chain": return ("chain", r.choice([["<", "<"], ["<", "<="], ["<=", "<="], [">", ">"], [">=", ">"]]), [g(), g(), g()])
    if k in ("and", "or"): return (k, g(), g())
    rows = [((g() if r.random() < 0.8 else None), g()) for _ in range(r.randint(1, 3))]
    return ("rows", rows)

def lean(t):
    k = t[0]
    if k == "int": return f"(.int ({t[1]}))"
    if k == "void": return ".void"
    if k == "op": return f"(.op .{AO[t[1]]} {lean(t[2])} {lean(t[3])})"
    if k in ("neg", "abs"): return f"(.{k} {lean(t[1])})"
    if k == "cmp": return f"(.cmp .{CO[t[1]]} {lean(t[2])} {lean(t[3])})"
    if k == "chain": return f"(.chain3 .{CO[t[1][0]]} .{CO[t[1][1]]} {lean(t[2][0])} {lean(t[2][1])} {lean(t[2][2])})"
    if k in ("and", "or"): return f"(.{k} {lean(t[1])} {lean(t[2])})"
    rows = t[1]; acc = ".void"
    for c, v in reversed(rows):
        acc = f"(.rowD {lean(v)} {acc})" if c is None else f"(.rowC {lean(c)} {lean(v)} {acc})"
    return acc

def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    exe = os.environ.get("SIRZ_LEAN") or shutil.which("lean")
    if not exe: print("lean が無いので飛ばす"); return 0
    r = random.Random(seed)
    terms = [gen(r, r.randint(1, 4)) for _ in range(n)]
    py = []
    for t in terms:
        try:
            res = S.evaluate(S.Funcs(), t)
            py.append(res[1] if res[0] == "val" else None if res[0] == "void" else "unsup")
        except S.Unsup: py.append("unsup")
    src = open("formal/lean/SirZ.lean").read().split("#print axioms")[0]
    src += "\nopen SirZ\n" + "".join(f"#eval ev selLeft (fun _ => none) {lean(t)}\n" for t in terms)
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, "T.lean"); open(p, "w").write(src)
        out = subprocess.run([exe, p], capture_output=True, text=True).stdout.splitlines()
    err = [l for l in out if "error" in l]
    if err: print("Lean:", err[:3])
    out = [l for l in out if l.startswith(("none", "some"))]
    if len(out) != len(terms): print("Lean の出力が数に合わない", len(out), len(terms)); return 1
    bad = 0; cmp_n = 0
    for t, a, b in zip(terms, py, out):
        if a == "unsup": continue
        cmp_n += 1
        want = "none" if a is None else f"some {a}" if a >= 0 else f"some ({a})"
        if want != b.strip():
            bad += 1
            if bad <= 5: print("食い違い", t, "py:", a, "lean:", b)
    print(f"項 {len(terms)}(比べた {cmp_n}、Python が断った {len(terms)-cmp_n}): 食い違い {bad}")
    return 1 if bad else 0

if __name__ == "__main__": sys.exit(main())
