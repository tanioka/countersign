"""SIR-Z + 呼び(formal/lean/SirZCall.lean の `ev`)と、sign_sir.py の `evaluate` を、関数つきの乱数のプログラムで突き合わせる。
再帰・部分適用(実引数が `!_`)・`&`/`|` の左の部分適用(SIR の外 = unsup)を含む。
燃料の数え方が違う(Lean は深さ、Python は歩数)ので、片方が燃料切れの組は数えるだけ。それ以外の食い違いで exit 1。
Lean が無ければ(`lean` が PATH か SIRZ_LEAN に無い)飛ばす。使い方: python3 test_sirzc_lean.py [個数] [種]"""
import os, random, re, shutil, subprocess, sys, tempfile
import sign_sir as S
from test_sirz_lean import LIT, AO, CO

def gen(r, d, vars_, funcs):
    if d == 0 or r.random() < 0.18:
        x = r.random()
        if vars_ and x < 0.45: return ("var", r.choice(vars_))
        if x < 0.49: return ("void",)
        return ("int", r.choice(LIT) if r.random() < 0.25 else r.randint(-6, 12))
    ks = ["op"] * 4 + ["neg", "abs", "cmp", "cmp", "chain", "and", "or", "rows"] + (["call"] * 4 if funcs else [])
    k = r.choice(ks)
    g = lambda: gen(r, d - 1, vars_, funcs)
    if k == "op": return ("op", r.choice(list(AO)), g(), g())
    if k in ("neg", "abs"): return (k, g())
    if k == "cmp": return ("cmp", r.choice(["<", ">", "<=", ">=", "=", "!="]), g(), g())
    if k == "chain": return ("chain", r.choice([["<", "<"], ["<", "<="], ["<=", "<="], [">", ">"], [">=", ">"]]), [g(), g(), g()])
    if k in ("and", "or"): return (k, g(), g())
    if k == "call":
        f = r.choice(list(funcs)); return ("call", f, [g() for _ in funcs[f]])
    return ("rows", [((g() if r.random() < 0.8 else None), g()) for _ in range(r.randint(1, 3))])

def lean_t(t, params):
    k = t[0]
    if k == "int": return f"(.int ({t[1]}))"
    if k == "void": return ".void"
    if k == "var": return f"(.var {params.index(t[1])})"
    if k == "op": return f"(.op .{AO[t[1]]} {lean_t(t[2], params)} {lean_t(t[3], params)})"
    if k in ("neg", "abs"): return f"(.{k} {lean_t(t[1], params)})"
    if k == "cmp": return f"(.cmp .{CO[t[1]]} {lean_t(t[2], params)} {lean_t(t[3], params)})"
    if k == "chain": return f"(.chain3 .{CO[t[1][0]]} .{CO[t[1][1]]} {' '.join(lean_t(x, params) for x in t[2])})"
    if k in ("and", "or"): return f"(.{k} {lean_t(t[1], params)} {lean_t(t[2], params)})"
    if k == "call":
        acc = ".anil"
        for a in reversed(t[2]): acc = f"(.acons {lean_t(a, params)} {acc})"
        return f"(.call {t[1]} {acc})"
    acc = ".void"
    for c, v in reversed(t[1]):
        acc = f"(.rowD {lean_t(v, params)} {acc})" if c is None else f"(.rowC {lean_t(c, params)} {lean_t(v, params)} {acc})"
    return acc

def prog(r):
    """funcs: {番号: (仮引数名の列, 本体)}。番号 i の本体は番号 < i の関数と自分(再帰)を呼べる"""
    funcs, ar = {}, {}
    for i in range(r.randint(1, 3)):
        ps = [f"p{j}" for j in range(r.randint(1, 2))]
        body = gen(r, r.randint(1, 3), ps, dict(ar))
        if r.random() < 0.6:                        # 自分を呼ぶ(再帰)のは、止まる形の条件つきの行だけ(数が増えて爆発しないように)
            self_call = ("call", i, [("op", "-", ("var", ps[0]), ("int", 1))] + [("var", p) for p in ps[1:]])
            body = ("rows", [(("cmp", ">", ("var", ps[0]), ("int", 0)), ("op", "+", ("var", ps[0]), self_call)), (None, body)])
        funcs[i] = (ps, body); ar[i] = ps
    top = gen(r, r.randint(1, 3), [], ar)
    return funcs, ar, top

def to_py(t, nm):
    if t[0] == "call": return ("call", nm(t[1]), [to_py(a, nm) for a in t[2]])
    if t[0] == "rows": return ("rows", [((None if c is None else to_py(c, nm)), to_py(v, nm)) for c, v in t[1]])
    if t[0] in ("int", "void", "var"): return t
    if t[0] == "chain": return ("chain", t[1], [to_py(x, nm) for x in t[2]])
    return tuple([t[0]] + [x if isinstance(x, str) else to_py(x, nm) for x in t[1:]])

def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    exe = os.environ.get("SIRZ_LEAN") or shutil.which("lean")
    if not exe: print("lean が無いので飛ばす"); return 0
    r = random.Random(seed)
    progs = [prog(r) for _ in range(n)]
    py = []
    for funcs, ar, top in progs:
        F = S.Funcs()
        for i, (ps, b) in funcs.items(): F[f"f{i}"] = (ps, to_py(b, lambda j: f"f{j}"))
        try:
            res = S.evaluate(F, to_py(top, lambda j: f"f{j}"), fuel=200000)
            py.append(res[1] if res[0] == "val" else None if res[0] == "void" else "fuel" if res[0] == "fuel" else "unsup")
        except S.Unsup: py.append("unsup")
    src = open("formal/lean/SirZCall.lean").read().split("#print axioms")[0] + "\nopen SirZC\n"
    for k, (funcs, ar, top) in enumerate(progs):
        cases = "".join(f"  | {i} => some ({len(ps)}, {lean_t(b, ps)})\n" for i, (ps, b) in funcs.items())
        src += f"def fs{k} : Fs := fun f => match f with\n{cases}  | _ => none\n"
        src += f"#eval ev fs{k} selLeft 300 (fun _ => none) {lean_t(top, [])}\n"
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, "T.lean"); open(p, "w").write(src)
        out = subprocess.run([exe, p], capture_output=True, text=True).stdout.splitlines()
    err = [l for l in out if "error" in l]
    if err: print("Lean:", err[:3])
    out = [l.strip() for l in out if l.strip().startswith("SirZC.Res.")]
    if len(out) != len(progs): print("Lean の出力が数に合わない", len(out), len(progs)); return 1
    def parse(s):
        if s == "SirZC.Res.fuel": return "fuel"
        if s == "SirZC.Res.unsup": return "unsup"
        if s in ("SirZC.Res.pf",): return None
        m = re.fullmatch(r"SirZC\.Res\.v \(?(none|some \(?(-?\d+)\)?)\)?", s)
        if not m: return "?" + s
        return None if m.group(1) == "none" else int(m.group(2))
    bad = ok = skipped = 0
    for (funcs, ar, top), a, b in zip(progs, py, out):
        lv = parse(b)
        if a == "fuel" or lv == "fuel": skipped += 1; continue
        if a == lv: ok += 1; continue
        bad += 1
        if bad <= 5: print("食い違い", funcs, top, "py:", a, "lean:", b)
    print(f"プログラム {len(progs)}(一致 {ok}、燃料切れで比べない {skipped}): 食い違い {bad}")
    return 1 if bad else 0

if __name__ == "__main__": sys.exit(main())
