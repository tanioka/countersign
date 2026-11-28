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

def gen_c(rnd, depth):
    """呼び(`f` は仮引数 2 つ)を葉に含む式。呼びの実引数も呼びを含みうる(字面だけの引数は避ける)。先頭が呼びだと末尾呼びになるので op か cmp で包む。"""
    def leaf(d):
        if d > 0 and rnd.random() < 0.5:
            return ("call", arg(d - 1), arg(d - 1))
        return ("var", rnd.randrange(3)) if rnd.random() < 0.7 else ("lit", rnd.randrange(1, 10))
    def arg(d):
        while True:
            t = ("op", rnd.choice(list(OPS)), leaf(d), leaf(d)) if rnd.random() < 0.6 else leaf(d)
            if t[0] != "lit" and not (t[0] == "op" and t[2][0] == "lit" and t[3][0] == "lit"): return t
    while True:
        l, r = leaf(depth), leaf(depth)
        if "call" not in (l[0], r[0]) or (l[0] == "lit" and r[0] == "lit"): continue
        if rnd.random() < 0.2: return ("cmp", rnd.choice(list(CMPS)), l, r)
        if rnd.random() < 0.15: return ("neg", ("op", rnd.choice(list(OPS)), l, r))
        return ("op", rnd.choice(list(OPS)), l, r)

def src(e):
    if e[0] == "call": return "(f %s %s)" % (src(e[1]), src(e[2]))
    if e[0] == "var": return VARS[e[1]]
    if e[0] == "lit": return str(e[1])
    if e[0] == "neg": return "-%s" % (src(e[1]) if e[1][0] in ("var", "lit") else "(%s)" % src(e[1]))
    return "(%s %s %s)" % (src(e[2]), e[1], src(e[3]))   # op・cmp とも

def lean_term(e):
    if e[0] == "call": return "(E.call2 0 %s %s)" % (lean_term(e[1]), lean_term(e[2]))
    if e[0] == "var": return "(E.var %d)" % e[1]
    if e[0] == "lit": return "(E.lit %d)" % e[1]
    if e[0] == "neg": return "(E.neg %s)" % lean_term(e[1])
    if e[0] == "cmp": return "(E.cmp .%s %s %s)" % (CMPS[e[1]], lean_term(e[2]), lean_term(e[3]))
    return "(E.op .%s %s %s)" % (OPS[e[1]], lean_term(e[2]), lean_term(e[3]))

def gen_cn(rnd, depth):
    if depth == 0 or rnd.random() < 0.4:
        e = gen(rnd, rnd.randrange(1, 3))
        if e[0] == "lit": e = ("var", rnd.randrange(3))
        return ("val", e)
    return (rnd.choice(["and", "or"]), gen_cn(rnd, depth - 1), gen_cn(rnd, depth - 1))

def src_cn(c):
    if c[0] == "val": return src(c[1])
    return "(%s %s %s)" % (src_cn(c[1]), "&" if c[0] == "and" else "|", src_cn(c[2]))

def lean_cn(c):
    if c[0] == "val": return "(Cn.val %s)" % lean_term(c[1])
    return "(Cn.%s %s %s)" % (c[0], lean_cn(c[1]), lean_cn(c[2]))

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
def sh2 : I2 → String
  | .base i => sh i | .enter => "enter" | .leave => "leave" | .bl t => s!"bl {t}" | .ret => "ret" | .bk t => s!"bk {t}"
def sh2b : I2 → String
  | .bl _ => "bl 0" | i => sh2 i
def outc (p : Array I2) : IO Unit := IO.println (String.intercalate ";" (p.toList.map sh2b))
def out2 (p : Array I2) : IO Unit := IO.println (String.intercalate ";" (p.toList.map sh2))
def out (p : Array I) : IO Unit := IO.println (String.intercalate ";" (p.toList.map sh))
'''

def gen_rows(rnd):
    rows = [(gen_cn(rnd, rnd.randrange(0, 3)), gen(rnd, rnd.randrange(0, 3))) for _ in range(rnd.randrange(1, 4))]
    return ("rows", rows, gen(rnd, rnd.randrange(0, 3)) if rnd.random() < 0.7 else None)

def src_rows(t):
    return "".join("\t%s : %s\n" % (src_cn(c), src(v)) for c, v in t[1]) + ("\t%s\n" % src(t[2]) if t[2] else "")

def lean_rows(t):
    r = "(Rows.dflt %s)" % lean_term(t[2]) if t[2] else "Rows.nil"
    for c, v in reversed(t[1]): r = "(Rows.row %s %s %s)" % (lean_cn(c), lean_term(v), r)
    return r

def asm_body(e, cond=None, full=False, site=None, withcall=False):
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, "t.sn")
        if withcall: open(p, "w").write("f : p q ? p + q\ng : x y z ? %s\ng 8 2 1\n" % src(e))
        elif site is not None: open(p, "w").write("f : p q ? p + q\ng : x y z ? (f (%s) (%s)) + 1\ng 8 2 1\n" % (src(site[0]), src(site[1])))
        elif e is not None and e[0] == "rows": open(p, "w").write("f : x y z ?\n%sf 8 2 1\n" % src_rows(e))
        elif cond is None: open(p, "w").write("f : x y z ? %s\nf 8 2 1\n" % src(e))
        else: open(p, "w").write("f : x y z ?\n\t%s : 1\n\t0\nf 8 2 1\n" % src_cn(cond))
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            A.main([p, "--no-peephole", "--no-opt"])
    ls = [re.sub(r"//.*", "", l).strip() for l in buf.getvalue().split("\n")]
    ls = [l for l in ls if l]
    if withcall:                            # 呼びを含む式 g の本体(3 つの str のあと ldp の前まで)
        a = ls.index("g:")
        body = ls[a + 1:]
        body = body[body.index("mov x29, sp") + 1:][3:]
        body = body[:next(i for i, l in enumerate(body) if l.startswith("ldp x29, x30"))]
    elif site is not None:                    # 呼ぶ側 g: 仮引数 3 つの str のあと、`bl f` と(あれば)`b 終わり`・`__` の行き先・終わりのラベルまで
        a = ls.index("g:")
        body = ls[a + 1:]
        body = body[body.index("mov x29, sp") + 1:][3:]
        j = next(i for i, l in enumerate(body) if l.startswith("bl "))
        k = j + 1
        if body[k].startswith("b "):
            k = next(i for i in range(k, len(body)) if body[i].endswith(":") and i > k + 1)
            k += 1
        body = body[:k]
    elif full:                                # 関数 f の全体: `stp`(enter)・仮引数の str・本体・`ldp`(leave)・`ret`
        a = ls.index("f:")
        body = ls[a + 1:]
        body = body[:next(i for i, l in enumerate(body) if l == "ret") + 1]
        body = [l for l in body if l != "mov x29, sp"]
    else:
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
        if op == "stp": out.append("enter")
        elif op == "ldp": out.append("leave")
        elif op == "ret": out.append("ret")
        elif op == "bl": out.append("bl 0")
        elif op == "movz": out.append("movz %d" % r(a[0]))
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
    if cond is not None:                    # 条件の後ろの `mov x0, #1`・`b 終わり`・`mov x0, #0` は外す(外れの飛び先は条件の大きさ + 2)
        assert out[-3] == "movi 0 1" and out[-1] == "movi 0 0", out[-3:]
        out = out[:-3]
    stores = [int(o.split()[2]) for o in out if o.startswith("str 0 ")]
    return ";".join(out), (min(stores) if stores else 3)      # 預けた枠のいちばん小さい番号 = 枠の底(行の条件では、器の都合で 3 でないことがある)

def main(n=60, seed=1):
    if not LEAN or not os.path.exists(LEAN): print("lean が無いので飛ばす"); return 0
    rnd = random.Random(seed)
    trees = [gen(rnd, rnd.randrange(1, 4)) for _ in range(n)]
    conds = [gen_cn(rnd, rnd.randrange(1, 4)) for _ in range(n)]
    rowss = [gen_rows(rnd) for _ in range(n)]
    funs = trees[:n // 2]                       # 関数全体(enter・仮引数・本体・leave・ret)
    def nonlit(): 
        while True:
            t = gen(rnd, rnd.randrange(1, 3))
            if t[0] != "lit" and not (t[0] == "neg" and t[1][0] == "lit"): return t
    sites = [("site", nonlit(), nonlit()) for _ in range(n // 2)]
    ctrees = [gen_c(rnd, rnd.randrange(1, 3)) for _ in range(n // 2)]
    items = []                                  # (見出し, 式の木か条件の木, asm の出力, 枠の底)
    skipped = 0
    for t in trees + conds + rowss + [("fun", x) for x in funs] + sites + [("ce", x) for x in ctrees]:
        isc = t[0] in ("val", "and", "or")
        try:
            if t[0] == "ce": want, base = asm_body(t[1], withcall=True)
            elif t[0] == "site": want, base = asm_body(None, None, False, (t[1], t[2]))
            elif t[0] == "fun": want, base = asm_body(t[1], None, True)
            else: want, base = asm_body(None, t) if isc else asm_body(t)
        except AsmErrorLike: skipped += 1; continue
        items.append(("呼びを含む式 " + src(t[1]) if t[0] == "ce" else "呼び f (%s) (%s)" % (src(t[1]), src(t[2])) if t[0] == "site" else "関数 " + src(t[1]) if t[0] == "fun" else src_cn(t) if isc else (src_rows(t) if t[0] == "rows" else src(t)), t, isc, want, base))
    with tempfile.TemporaryDirectory() as d:
        env = dict(os.environ, LEAN_PATH=d)
        subprocess.run([LEAN, "-o", os.path.join(d, "SirZAsm.olean"), os.path.join(HERE, "formal/lean/SirZAsm.lean")], check=True, capture_output=True, env=env)
        prog = HEAD + "".join(
            ("#eval let c := %s; out (compileC novR %d 0 ((compileC novR %d 0 0 c).size + 2) c)\n" % (lean_cn(t), b, b)) if isc
            else "#eval out (compileR novR %d 0 %s)\n" % (b, lean_rows(t)) if t[0] == "rows"
            else "#eval outc (compileS2 novR %d (fun _ => 0) 0 0 %s)\n" % (b, lean_term(t[1])) if t[0] == "ce"
            else "#eval out2 (site novR 3 [%s, %s] 0)\n" % (lean_term(t[1]), lean_term(t[2])) if t[0] == "site"
            else "#eval out2 (fcode novR 3 %s)\n" % (lean_term(t[1])) if t[0] == "fun"
            else "#eval out (compileS novR %d 0 %s)\n" % (b, lean_term(t)) for _, t, isc, _, b in items)
        f = os.path.join(d, "T.lean"); open(f, "w").write(prog)
        res = subprocess.run([LEAN, f], capture_output=True, text=True, env=env)
    got = [l for l in res.stdout.split("\n") if l]
    if len(got) != len(items): print("Lean の出力が足りない:", res.stdout[-500:], res.stderr[-500:]); return 1
    bad = 0
    for (name, t, isc, want, b), g in zip(items, got):
        if want != g:
            bad += 1
            if bad <= 3: print("食い違い:", name, "(底 %d)" % b, "\n  asm :", want, "\n  lean:", g)
    print("式 %d 個・条件 %d 個・行 %d 個・呼び %d 個・呼びを含む式 %d 個(出せない %d)、食い違い %d" % (len(trees), len(conds), len(rowss), len(sites), len(ctrees), skipped, bad)); return 1 if bad else 0

AsmErrorLike = (A.AsmError, SystemExit, StopIteration, ValueError)
if __name__ == "__main__":
    sys.exit(main(*(int(a) for a in sys.argv[1:3])))
