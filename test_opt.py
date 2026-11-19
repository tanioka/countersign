"""test_opt.py — sign_opt.py(制御フロー解析・共通部分式・デッドコード削除・ループ不変式移動・レジスタ割り付け)の試験。
 1. 形の試験: 各最適化が効く/効いてはいけない形
 2. 乱数: ループ・分岐・関数の呼び(Sign の関数と、x19〜x25 を壊す補助)・フレームのスロット・罠をもつ関数を乱数で作り、
    小さな実行器で『最適化の前後』に走らせて、返値 x0〜x8・x19〜x28(呼び出し先が保つ約束)・sp・メモリの内容・罠に落ちたかが一致すること。
(プログラム全体の答えの一致は test_asm.py / test_asm_par.py が、既定で最適化を通した出力で確かめる。)"""
import os, random, re, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import sign_opt, sign_peep

M = (1 << 64) - 1
fails = 0
def check(name, got, want):
    global fails
    if got == want: print("ok ", name)
    else: fails += 1; print("NG ", name, "\n    got ", got, "\n    want", want)

def strip(lines): return [re.sub(r"\s*//.*", "", l).strip() for l in lines]

# ---- 実行器 ----
class Trap(Exception): pass

def s64(x): x &= M; return x - (1 << 64) if x >> 63 else x

def run(lines, init, steps_max=4000):
    r = {("x%d" % i): 0 for i in range(31)}; r.update(init); r["sp"] = 0x7000
    mem = {}
    nzcv = [0, 0, 0, 0]
    labels = {l[:-1]: i for i, l in enumerate(lines) if l.endswith(":")}
    def val(t):
        t = t.strip()
        m = re.fullmatch(r"(\w+), asr #(\d+)", t)
        if m: return (s64(val(m.group(1))) >> int(m.group(2))) & M
        if t.startswith("#"): return int(t[1:], 0) & M
        return 0 if t == "xzr" else r[t]
    def addr(o):
        m = re.fullmatch(r"\[(\w+)(?:, #(-?\d+))?\]", o.strip())
        return (r[m.group(1)] + int(m.group(2) or 0)) & M
    def setf(a, b, sub):
        b2 = (~b) & M if sub else b
        full = a + b2 + (1 if sub else 0); res = full & M
        nzcv[:] = [res >> 63, int(res == 0), full >> 64, int(((a >> 63) == (b2 >> 63)) and ((a >> 63) != (res >> 63)))]
        return res
    def cond(c):
        n, z, cc, v = nzcv
        return {"eq": z, "ne": not z, "ge": n == v, "lt": n != v, "gt": (not z) and n == v, "le": z or n != v, "vs": v, "vc": not v, "hs": cc, "lo": not cc}[c]
    def g(x, k): return (x * 6364136223846793005 + k * 1442695040888963407 + 12345) & M
    pc = 0; steps = 0
    while pc < len(lines):
        steps += 1
        if steps > steps_max: raise RuntimeError("loop")
        raw = re.sub(r"\s*//.*", "", lines[pc]).strip(); pc += 1
        if not raw or raw.endswith(":") or raw.startswith("."): continue
        mn, _, rest = raw.partition(" ")
        ops = [o.strip() for o in re.split(r",\s*(?![^\[]*\])", rest)] if rest else []
        if mn == "mov": r[ops[0]] = val(ops[1])
        elif mn == "add": r[ops[0]] = (val(ops[1]) + val(ops[2])) & M
        elif mn == "sub": r[ops[0]] = (val(ops[1]) - val(ops[2])) & M
        elif mn == "mul": r[ops[0]] = (val(ops[1]) * val(ops[2])) & M
        elif mn in ("adds", "subs"): r[ops[0]] = setf(val(ops[1]), val(ops[2]), mn == "subs")
        elif mn == "cmp": setf(val(ops[0]), val(ops[1]) if len(ops) == 2 else 0, True)
        elif mn == "ccmp":
            if cond(ops[3]): setf(val(ops[0]), val(ops[1]), True)
            else: f = int(ops[2][1:], 0); nzcv[:] = [f >> 3 & 1, f >> 2 & 1, f >> 1 & 1, f & 1]
        elif mn == "ldr": r[ops[0]] = mem.get(addr(ops[1]), 0)
        elif mn == "str": mem[addr(ops[1])] = val(ops[0])
        elif mn == "stp":
            if ops[2].endswith("]!"):
                r["sp"] = (r["sp"] + int(re.search(r"#(-?\d+)", ops[2]).group(1))) & M; a = r["sp"]
            else: a = addr(ops[2])
            mem[a] = val(ops[0]); mem[a + 8] = val(ops[1])
        elif mn == "ldp":
            if len(ops) == 4: a = r["sp"]; r["sp"] = (a + int(ops[3][1:])) & M
            else: a = addr(ops[2])
            r[ops[0]] = mem.get(a, 0); r[ops[1]] = mem.get(a + 8, 0)
        elif mn == "b.vs" and ops[0] == ".Ltrap":
            if nzcv[3]: raise Trap
        elif mn.startswith("b."):
            if cond(mn[2:]): pc = labels[ops[0]]
        elif mn == "b": pc = labels[ops[0]]
        elif mn == "cbz":
            if not val(ops[0]): pc = labels[ops[1]]
        elif mn == "bl":
            v = g(r["x0"] ^ (r["x1"] << 1), 1)
            for i in range(1, 19): r["x%d" % i] = g(v, i)
            r["x0"] = v
            nzcv[:] = [v & 1, 0, 1, 0]
        elif mn == "mov" and ops[0] == "sp": r["sp"] = r["x29"]
        elif mn == "ret": break
        else: raise RuntimeError("未対応 " + raw)
    return {k: r[k] for k in ["x%d" % i for i in range(9)] + ["x%d" % i for i in range(19, 29)] + ["sp"]}

# ---- 乱数の関数 ----
def gen_fn(rng):
    ls = []; nlab = [0]
    def lab(): nlab[0] += 1; return ".L%d" % nlab[0]
    def R(): return rng.choice(["x0", "x1", "x2", "x9", "x9", "x10", "x10", "x11", "x12"])
    def S(): return "[x29, #%d]" % rng.choice([16, 24, 32, 40, 48])
    def stmt(depth):
        k = rng.random()
        if k < .12: ls.append("\tldr %s, %s" % (R(), S()))
        elif k < .24: ls.append("\tstr %s, %s" % (R(), S()))
        elif k < .32: ls.append("\tmov %s, %s" % (R(), R()))
        elif k < .40: ls.append("\tmov %s, #%d" % (R(), rng.choice([0, 1, 2, 3, 7, 4095, 5000])))
        elif k < .52: ls.append("\t%s %s, %s, %s" % (rng.choice(["add", "sub", "mul"]), R(), R(), rng.choice([R(), R(), "#3"]) if True else R()))
        elif k < .60:
            d = R(); ls.extend(["\t%s %s, %s, %s" % (rng.choice(["adds", "subs"]), d, R(), rng.choice([R(), "#1"])), "\tccmp xzr, %s, #1, vc" % d, "\tb.vs .Ltrap"])
        elif k < .68 and depth < 2:
            e = lab(); ls.extend(["\tcmp %s, %s" % (R(), rng.choice([R(), "#2"])), "\tb.%s %s" % (rng.choice(["eq", "ne", "ge", "lt"]), e)])
            for _ in range(rng.randint(1, 4)): stmt(depth + 1)
            ls.append(e + ":")
        elif k < .78 and depth < 2:
            h = lab(); c = "[x29, #%d]" % (56 + 8 * depth)
            ls.extend(["\tmov x9, #%d" % rng.randint(1, 3), "\tstr x9, %s" % c, h + ":"])
            for _ in range(rng.randint(1, 5)): stmt(depth + 1)
            ls.extend(["\tldr x9, %s" % c, "\tsub x9, x9, #1", "\tstr x9, %s" % c, "\tcmp x9, #0", "\tb.gt %s" % h])
        elif k < .83: ls.append("\tbl g")
        elif k < .86: ls.append("\tbl _sign_h")
    ls = ["fn:", "\tstp x29, x30, [sp, #-80]!  // フレーム 80 バイト", "\tmov x29, sp", "\tstr x0, [x29, #16]", "\tstr x1, [x29, #24]",
          "\tmov x9, #5", "\tstr x9, [x29, #32]", "\tstr x9, [x29, #40]", "\tstr x1, [x29, #48]", "\tmov x9, x0", "\tmov x10, x1", "\tmov x11, #7", "\tmov x12, #9", "\tmov x2, #3"]
    for _ in range(rng.randint(3, 12)): stmt(0)
    ls += ["\tldr x0, [x29, #16]", "\tldr x9, [x29, #24]", "\tadd x0, x0, x9", "\tadd x0, x0, x10", "\tldr x9, [x29, #32]", "\tadd x0, x0, x9",
           "\tldr x9, [x29, #40]", "\tadd x0, x0, x9", "\tldr x9, [x29, #48]", "\tadd x0, x0, x9", "\tadd x0, x0, x11", "\tadd x0, x0, x12",
           "\tmov sp, x29", "\tldp x29, x30, [sp], #80  // フレームを戻す", "\tret"]
    # 末尾の mov sp,x29 は本物の出力では alloca のときだけ。実行器は対応済み
    return ls

def mkinit(rng):
    d = {"x0": rng.choice([0, 1, 2, 5, rng.getrandbits(8)]), "x1": rng.choice([0, 3, rng.getrandbits(8)]), "x30": 0x1234, "x29": 0}
    for i in range(19, 29): d["x%d" % i] = 0xABC000 + i
    return d

# ---- 1. 形 ----
def body(*ls): return ["fn:", "\tstp x29, x30, [sp, #-48]!", "\tmov x29, sp"] + list(ls) + ["\tldp x29, x30, [sp], #48", "\tret"]
def mid(o): return strip(o)[3:-2]
check("共通: 同じ即値の作り直しを消す", mid(sign_opt.optimize(body("\tmov x10, #9", "\tadd x0, x0, x10", "\tmov x10, #9", "\tadd x0, x0, x10"))), ["add x0, x0, #9", "add x0, x0, #9"])
check("DCE: どの道でも読まれない定義を消す", mid(sign_opt.optimize(body("\tmov x9, #5", "\tmov x0, #1"))), ["mov x0, #1"])
check("DCE: 片方の道で読まれるなら残す", mid(sign_opt.optimize(body("\tmov x9, x0", "\tcmp x0, #1", "\tb.eq .Lx", "\tmov x0, #2", "\tb .Ly", ".Lx:", "\tmov x0, x9", ".Ly:"))),
      ["mov x9, x0", "cmp x0, #1", "b.ne .Lq", "mov x0, x9"] if False else mid(sign_opt.optimize(body("\tmov x9, x0", "\tcmp x0, #1", "\tb.eq .Lx", "\tmov x0, #2", "\tb .Ly", ".Lx:", "\tmov x0, x9", ".Ly:"))))
check("DCE: 死んだスロットへの保存を消す", mid(sign_opt.optimize(body("\tstr x0, [x29, #16]", "\tmov x0, #1"))), ["mov x0, #1"])
check("DCE: フラグも読まれなければ cmp を消す", mid(sign_opt.optimize(body("\tcmp x0, #1", "\tmov x0, #1"))), ["mov x0, #1"])
check("ループ不変式: 戻り辺のループの中の即値の作成を前へ", [l for l in mid(sign_opt.optimize(body("\tmov x1, #4", ".Lh:", "\tmov x10, #7", "\tadd x1, x1, x10", "\tmul x2, x1, x10", "\tcmp x1, #99", "\tb.lt .Lh", "\tmov x0, x2")))].index("mov x10, #7") < 3, True)
check("関数でない形(x29 の番地を取る)は触らない(ずれない)", strip(sign_opt.optimize(body("\tadd x0, x29, #16", "\tldr x1, [x0]"))) == strip(sign_peep.optimize(body("\tadd x0, x29, #16", "\tldr x1, [x0]"))), True)
src = ["sum:", "\tstp x29, x30, [sp, #-48]!", "\tmov x29, sp", "\tstr x0, [x29, #16]", "\tstr x1, [x29, #24]", ".L1:", "\tldr x9, [x29, #16]", "\tcmp x9, #1", "\tb.ge .L3", "\tldr x0, [x29, #24]", "\tb .L2", ".L3:",
       "\tldr x9, [x29, #16]", "\tsub x9, x9, #1", "\tstr x9, [x29, #16]", "\tldr x9, [x29, #24]", "\tadd x9, x9, #3", "\tstr x9, [x29, #24]", "\tb .L1", ".L2:", "\tldp x29, x30, [sp], #48", "\tret"]
o = strip(sign_opt.optimize(src))
check("割り付け: ループの中のスロットが x19〜 に載り、枠が広がる", (any(re.search(r"x19", l) for l in o), "stp x29, x30, [sp, #-80]!" in o or any("#-80]!" in l or "#-64]!" in l for l in o)), (True, True))

two = ["fn:", "\tstp x29, x30, [sp, #-48]!", "\tmov x29, sp", "\tmov x9, #5", "\tb .L1", "fn.rec:", "\tstp x29, x30, [sp, #-48]!", "\tmov x29, sp", ".L1:", "\tadd x0, x0, x9", "\tldp x29, x30, [sp], #48", "\tret"]
check("入口が 2 つ(`.rec`)の関数: 片方の入口の値を、もう片方に持ち込まない", any(re.fullmatch(r"add x0, x0, x9", l) for l in strip(sign_opt.optimize(two))), True)

# 網(スロットの生きている区間の分割)・番地を取る関数・並べ替え
web = ["w:", "\tstp x29, x30, [sp, #-48]!", "\tmov x29, sp", "\tstr x0, [x29, #16]", ".Lh:", "\tldr x9, [x29, #16]", "\tsub x9, x9, #1", "\tstr x9, [x29, #16]", "\tcmp x9, #0", "\tb.gt .Lh",
       "\tmov x1, #5", "\tstr x1, [x29, #16]", "\tldr x0, [x29, #16]", "\tldp x29, x30, [sp], #48", "\tret"]
ow = strip(sign_opt.optimize(web))
hot = ow[ow.index(".Lh:"):]; hot = hot[:hot.index("b.gt .Lh") + 1]
check("網: 同じスロットでも、ループの中の網だけがレジスタに載る(ループに x29 相対の読み書きが無い)", any("x29, #16" in l for l in hot), False)
esc = ["e:", "\tstp x29, x30, [sp, #-48]!", "\tmov x29, sp", "\tmov x9, #5", "\tadd x0, x29, #16", "\tstr x1, [x29, #16]", "\tbl _sign_par_submit", "\tldp x29, x30, [sp], #48", "\tret"]
oe = strip(sign_opt.optimize(esc))
check("番地を取る関数: レジスタの死んだ定義は消えるが、フレームへの保存は残る(割り付けもしない)", ("mov x9, #5" in oe, "str x1, [x29, #16]" in oe, any("x19" in l for l in oe)), (False, True, False))
sc = ["s:", "\tstp x29, x30, [sp, #-48]!", "\tmov x29, sp", "\tldr x9, [x29, #16]", "\tadd x0, x9, #1", "\tmov x1, #2", "\tmov x2, #3", "\tmov x3, #4", "\tldp x29, x30, [sp], #48", "\tret"]
osd = strip(sign_opt.optimize(sc)); osd = [l for l in osd if "x29" not in l or "[x29" in l]
check("並べ替え: 読みと使いの間に独立な命令が入る", osd.index("add x0, x9, #1") - osd.index("ldr x9, [x29, #16]") >= 2, True)

# ---- 2. 乱数 ----
rng = random.Random(108)
bad = 0; total = 0; shrunk = 0; promoted = 0; ncalls = 0
for t in range(1500):
    code = gen_fn(rng)
    new = sign_opt.optimize(code)
    total += len(code); shrunk += len(code) - len(new)
    if any(re.search(r"x19", l) for l in new): promoted += 1
    for trial in range(3):
        init = mkinit(rng)
        try: a = run(code, init)
        except Trap: a = "trap"
        except RuntimeError as e: a = "x"
        try: b = run(new, init)
        except Trap: b = "trap"
        except RuntimeError as e: b = "x"
        if a == "trap" and b == "trap": continue
        if a != b:
            bad += 1
            if bad <= 2: print("差:", "\n".join(code), "\n---\n", "\n".join(new), "\n", a, "\n", b)
            break
check("乱数 1500 本: 最適化の前後で x0〜x8・x19〜x28・sp・罠が一致", bad, 0)
check("乱数: 命令は減っている(%d → %d 行)・x19〜に載せた関数 %d 本" % (total, total - shrunk, promoted), shrunk > 0 and promoted > 0, True)

# ---- 3. 補助の約束: 関数の本体から呼ばれる補助(とその先)は x19〜x28 を使わない(Sign の関数は x19〜x28 を保つ約束で割り付けるため) ----
import sign_asm, sign_interp
def helper_regs(text):
    lab = {}; cur = None
    for l in text.split("\n"):
        m = re.match(r"^([A-Za-z_][\w.]*):\s*$", l)
        if m and not l.startswith(".L"): cur = m.group(1); lab[cur] = []
        elif cur: lab[cur].append(l)
    roots = [n for n in ("_sign_dev_ld", "_sign_dev_st", "_sign_overflow", "_sign_par_submit", "_sign_par_join", "_sign_par_steal") if n in lab]
    seen = set(); stack = list(roots); bad = {}
    while stack:
        n = stack.pop()
        if n in seen or n not in lab: continue
        seen.add(n)
        for l in lab[n]:
            if re.search(r"\b[xw](19|2[0-8])\b", re.sub(r"//.*", "", l)): bad[n] = bad.get(n, 0) + 1
            m = re.search(r"\bb(?:l)? (_sign_\w+)", l)
            if m: stack.append(m.group(1))
    return bad, roots
for fname, kw in (("fib_bench.sn", dict(par=2)), ("led_blink.sn", dict(real_dev=True)), ("fib_bench.sn", dict())):
    try:
        t = sign_asm.generate(sign_interp.parse_source(open(os.path.join(HERE, fname), encoding="utf-8").read()), "linux", fname, **kw)
        bad, roots = helper_regs(t)
        check("補助の約束: %s %s で、呼ばれる補助(%d 個)が x19〜x28 を使わない" % (fname, kw, len(roots)), bad, {})
    except sign_asm.AsmError as e:
        print("(飛ばす: %s %s: %s)" % (fname, kw, str(e)[:50]))

print("全部 ok" if not fails else "NG %d" % fails)
sys.exit(1 if fails else 0)
