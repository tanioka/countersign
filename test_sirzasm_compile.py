"""Lean の `compileS`(formal/lean/SirZAsm.lean)の命令列が、`sign_asm.py`(--no-peephole --no-opt)の出力と同じ並びか、
乱数の式の木(字面・変数 x y z・`+ - * / %`)で突き合わせる。値域の解析 `nov` は「いつも溢れうる」(偽)にする
(`sign_asm.py` が溢れ無しを示せない式だけを使うので揃う。字面どうしの演算は避ける)。
使い方: SIRZ_LEAN=<lean の実行ファイル> python3 test_sirzasm_compile.py [個数] [種]   (lean が無ければ飛ばす)"""
import contextlib, io, os, random, re, subprocess, sys, tempfile
import sign_asm as A

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.environ.get("SIRZ_LEAN") or __import__("shutil").which("lean")
OPS = {"+": "add", "-": "sub", "*": "mul", "/": "div", "%": "mod"}
VARS = ["x", "y", "z"]
CMPS = {"<": "lt", "<=": "le", ">": "gt", ">=": "ge", "=": "eq"}

def gen(rnd, depth):
    if depth == 0 or rnd.random() < 0.25:
        return ("var", rnd.randrange(3)) if rnd.random() < 0.6 else ("lit", rnd.randrange(0, 10))
    if rnd.random() < 0.15: return ("neg", gen(rnd, depth - 1))
    if rnd.random() < 0.25:
        l, r = gen(rnd, depth - 1), gen(rnd, depth - 1)
        if l[0] == "lit" and r[0] == "lit": l = ("var", rnd.randrange(3))
        return ("cmp", rnd.choice(list(CMPS)), l, r)
    o = rnd.choice(list(OPS))
    l, r = gen(rnd, depth - 1), gen(rnd, depth - 1)
    # 字面どうしは畳み込みや値域の解析で形が変わるので、少なくとも片方に変数を含める
    if l[0] == "lit" and r[0] == "lit": l = ("var", rnd.randrange(3))
    return ("op", o, l, r)

def src(e):
    if e[0] == "var": return VARS[e[1]]
    if e[0] == "lit": return str(e[1])
    if e[0] == "neg": return "-%s" % (src(e[1]) if e[1][0] in ("var", "lit") else "(%s)" % src(e[1]))
    return "(%s %s %s)" % (src(e[2]), e[1], src(e[3]))   # op・cmp とも

def lean_term(e):
    if e[0] == "var": return "(E.var %d)" % e[1]
    if e[0] == "lit": return "(E.lit %d)" % e[1]
    if e[0] == "neg": return "(E.neg %s)" % lean_term(e[1])
    if e[0] == "cmp": return "(E.cmp .%s %s %s)" % (CMPS[e[1]], lean_term(e[2]), lean_term(e[3]))
    return "(E.op .%s %s %s)" % (OPS[e[1]], lean_term(e[2]), lean_term(e[3]))

HEAD = r'''import SirZAsm
open SirZAsm
def shc : Cond → String
  | .ne => "ne" | .eq => "eq" | .vs => "vs" | .lt => "lt" | .ge => "ge" | .gt => "gt" | .le => "le"
def sh : I → String
  | .movz d => s!"movz {d}" | .mov d a => s!"mov {d} {a}" | .cmpR a b => s!"cmpR {a} {b}" | .cmpI a n => s!"cmpI {a} {n}"
  | .cmpAsr a b s => s!"cmpAsr {a} {b} {s}" | .adds d a b => s!"adds {d} {a} {b}" | .subs d a b => s!"subs {d} {a} {b}"
  | .mul d a b => s!"mul {d} {a} {b}" | .smulh d a b => s!"smulh {d} {a} {b}" | .sdiv d a b => s!"sdiv {d} {a} {b}"
  | .msub d a b c => s!"msub {d} {a} {b} {c}" | .csel d a b c => s!"csel {d} {a} {b} {shc c}"
  | .bc c t => s!"bc {shc c} {t}" | .b t => s!"b {t}" | .movi d n => s!"movi {d} {n}" | .str a k => s!"str {a} {k}" | .ldr d k => s!"ldr {d} {k}" | .neg d a => s!"neg {d} {a}"
def out (p : Array I) : IO Unit := IO.println (String.intercalate ";" (p.toList.map sh))
'''

def asm_body(e):
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, "t.sn")
        open(p, "w").write("f : x y z ? %s\nf 8 2 1\n" % src(e))
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            A.main([p, "--no-peephole", "--no-opt"])
    ls = [re.sub(r"//.*", "", l).strip() for l in buf.getvalue().split("\n")]
    ls = [l for l in ls if l]
    a = ls.index("mov x29, sp")
    body = ls[a + 1:]
    body = body[3:]                         # 仮引数 3 つの str
    body = body[:next(i for i, l in enumerate(body) if l.startswith("ldp x29, x30"))]
    labels, idx = {}, 0
    for l in body:
        if l.endswith(":"): labels[l[:-1]] = idx
        else: idx += 1
    r = lambda s: int(s.strip()[1:]); slot = lambda s: (int(re.search(r"#(\d+)\]", s).group(1)) - 16) // 8
    out, cur = [], -1
    for l in body:
        if l.endswith(":"): continue
        cur += 1
        op, _, rest = l.partition(" ")
        a = [x.strip() for x in rest.split(",")]
        if op == "movz": out.append("movz %d" % r(a[0]))
        elif op == "neg": out.append("neg %d %d" % (r(a[0]), r(a[1])))
        elif op == "movn": out.append("movi %d %d" % (r(a[0]), -int(a[1][1:], 0) - 1))
        elif op == "mov" and a[1].startswith("#"): out.append("movi %d %d" % (r(a[0]), int(a[1][1:])))
        elif op == "mov": out.append("mov %d %d" % (r(a[0]), r(a[1])))
        elif op == "str": out.append("str %d %d" % (r(a[0]), slot(rest)))
        elif op == "ldr": out.append("ldr %d %d" % (r(a[0]), slot(rest)))
        elif op == "cmp" and len(a) == 3: out.append("cmpAsr %d %d 63" % (r(a[0]), r(a[1])))
        elif op == "cmp" and a[1].startswith("#"): out.append("cmpI %d %d" % (r(a[0]), int(a[1][1:])))
        elif op == "cmp": out.append("cmpR %d %d" % (r(a[0]), r(a[1])))
        elif op in ("adds", "subs", "mul", "smulh", "sdiv"): out.append("%s %d %d %d" % (op, r(a[0]), r(a[1]), r(a[2])))
        elif op == "msub": out.append("msub %d %d %d %d" % tuple(r(x) for x in a))
        elif op == "csel": out.append("csel %d %d %d %s" % (r(a[0]), r(a[1]), r(a[2]), a[3]))
        elif op.startswith("b."): out.append("bc %s %d" % (op[2:], labels[rest.strip()] - cur))
        elif op == "b": out.append("b %d" % (labels[rest.strip()] - cur))
        else: raise SystemExit("知らない命令: " + l)
    return ";".join(out)

def main(n=60, seed=1):
    if not LEAN or not os.path.exists(LEAN): print("lean が無いので飛ばす"); return 0
    rnd = random.Random(seed)
    trees = [gen(rnd, rnd.randrange(1, 4)) for _ in range(n)]
    with tempfile.TemporaryDirectory() as d:
        env = dict(os.environ, LEAN_PATH=d)
        subprocess.run([LEAN, "-o", os.path.join(d, "SirZAsm.olean"), os.path.join(HERE, "formal/lean/SirZAsm.lean")], check=True, capture_output=True, env=env)
        prog = HEAD + "".join("#eval out (compileS novR 3 0 %s)\n" % lean_term(t) for t in trees)
        f = os.path.join(d, "T.lean"); open(f, "w").write(prog)
        res = subprocess.run([LEAN, f], capture_output=True, text=True, env=env)
    got = [l for l in res.stdout.split("\n") if l]
    if len(got) != len(trees): print("Lean の出力が足りない:", res.stdout[-500:], res.stderr[-500:]); return 1
    bad = 0; skipped = 0
    for t, g in zip(trees, got):
        try: want = asm_body(t)
        except AsmErrorLike: skipped += 1; continue
        if want != g:
            bad += 1
            if bad <= 3: print("食い違い:", src(t), "\n  asm :", want, "\n  lean:", g)
    print("式 %d 個(出せない %d)、食い違い %d" % (len(trees), skipped, bad)); return 1 if bad else 0

AsmErrorLike = (A.AsmError, SystemExit, StopIteration, ValueError)
if __name__ == "__main__":
    sys.exit(main(*(int(a) for a in sys.argv[1:3])))
