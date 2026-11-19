"""test_peep.py — sign_peep.py(ピープホール最適化)の試験。
 1. 個々の形が期待どおりに縮む / 縮んではいけない形(あとで読まれる・w の形・分岐先で読まれる)が残る
 2. 乱数の命令列を、小さな実行器で『最適化の前後』に走らせ、終わりの x0〜x8・フレームの内容・罠に落ちたかが一致する
 3. 出力全体(sign_asm)で、--no-peephole と既定の行数を比べ、減っていること
(プログラム全体の答えの一致は test_asm.py / test_asm_par.py が、既定で最適化を通した出力で確かめる。)"""
import os, random, re, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import sign_peep

M = (1 << 64) - 1
fails = 0
def check(name, got, want):
    global fails
    if got == want: print("ok ", name)
    else: fails += 1; print("NG ", name, "\n    got ", got, "\n    want", want)

def opt(*ls): return sign_peep.optimize(["\t" + l if not l.endswith(":") else l for l in ls])
def strip(lines): return [re.sub(r"\s*//.*", "", l).strip() for l in lines]

RET = ["\tldp x29, x30, [sp], #48", "\tret"]
def body(*ls): return ["fn:", "\tstp x29, x30, [sp, #-48]!", "\tmov x29, sp"] + ["\t" + l if not l.endswith(":") else l for l in ls] + RET

# ---- 1. 形 ----
def tail(x): return strip(sign_peep.optimize(x))[3:-2]
check("P1 保存→読み込み(同じレジスタ)は読みを消す", tail(body("str x0, [x29, #24]", "ldr x0, [x29, #24]", "add x9, x0, #1", "mov x0, x9")), ["str x0, [x29, #24]", "add x0, x0, #1"])
check("P1 別のレジスタへの読みは mov に", tail(body("str x0, [x29, #24]", "ldr x9, [x29, #24]", "add x0, x9, #1")), ["str x0, [x29, #24]", "add x0, x0, #1"])
check("P1 同じ番地への新しい書き込みがあれば、新しいほうから転送する", tail(body("str x0, [x29, #24]", "str x1, [x29, #24]", "ldr x0, [x29, #24]")), ["str x0, [x29, #24]", "str x1, [x29, #24]", "mov x0, x1"])
check("P1 保存したレジスタが書き換わっていれば転送しない", tail(body("str x0, [x29, #24]", "mov x0, #5", "ldr x9, [x29, #24]", "add x0, x0, x9")), ["str x0, [x29, #24]", "mov x0, #5", "ldr x9, [x29, #24]", "add x0, x0, x9"])
check("P2 即値を命令に埋める", tail(body("ldr x9, [x29, #16]", "mov x10, #3", "subs x9, x9, x10", "mov x0, x9")), ["ldr x0, [x29, #16]", "subs x0, x0, #3"])
check("P2 4095 を超える即値は埋めない", tail(body("mov x10, #5000", "add x0, x9, x10")), ["mov x10, #5000", "add x0, x9, x10"])
check("P2 あとで x10 を読むなら mov を残す", tail(body("mov x10, #3", "add x9, x9, x10", "lsl x0, x9, x10")), ["mov x10, #3", "add x9, x9, #3", "lsl x0, x9, x10"])
check("P3/P4 コピーを消す", tail(body("mov x9, x0", "add x10, x9, #1", "mov x0, x10")), ["add x0, x0, #1"])
check("P4 あとで元のレジスタを読むなら付け替えない", tail(body("add x9, x1, #1", "mov x0, x9", "add x2, x9, #2")), ["add x9, x1, #1", "mov x0, x9", "add x2, x9, #2"])
check("w の形が絡むなら触らない", tail(body("mov x9, x0", "add w10, w9, #1", "mov x0, x10")), ["mov x9, x0", "add w10, w9, #1", "mov x0, x10"])
check("分岐先で読まれるなら消さない", tail(body("mov x9, #7", "cmp x0, #1", "b.eq .Lx", "mov x0, #2", "b .Ly", ".Lx:", "mov x0, x9", ".Ly:")),
      ["mov x9, #7", "cmp x0, #1", "b.eq .Lx", "mov x0, #2", "b .Ly", ".Lx:", "mov x0, x9", ".Ly:"])
check("罠への分岐は何も読まない(罠の先で x9 は要らない)", tail(body("ldr x9, [x29, #16]", "subs x9, x9, #1", "b.vs .Ltrap", "mov x0, x9")), ["ldr x0, [x29, #16]", "subs x0, x0, #1", "b.vs .Ltrap"])
check("次の行へ飛ぶだけの b を消す", tail(body("b .Lz", ".Lz:", "mov x0, #1")), [".Lz:", "mov x0, #1"])
check("b.cc A / b B / A: を反転", tail(body("cmp x0, #1", "b.ge .La", "b .Lb", ".La:", "mov x0, #1", ".Lb:")), ["cmp x0, #1", "b.lt .Lb", ".La:", "mov x0, #1", ".Lb:"])
check("関数呼びの前後では x9〜x12 は生きない(消せる)", tail(body("mov x10, #1", "add x0, x0, x10", "bl g")), ["add x0, x0, #1", "bl g"])
check("ただし x0〜x7 は呼びが読む", tail(body("mov x1, x0", "add x2, x1, #1", "bl g")), ["mov x1, x0", "add x2, x1, #1", "bl g"])
check("_sign_ の補助は何を読むか分からないので mov を残す", tail(body("mov x10, #1", "add x0, x0, x10", "bl _sign_par_join")), ["mov x10, #1", "add x0, x0, #1", "bl _sign_par_join"])

# ---- 2. 乱数: 最適化の前後で同じ終わりの状態 ----
class Trap(Exception): pass

def run(lines, regs, mem):
    r = dict(regs); m = dict(mem); nzcv = [0, 0, 0, 0]
    labels = {l[:-1]: i for i, l in enumerate(lines) if l.endswith(":")}
    def s64(x): x &= M; return x - (1 << 64) if x >> 63 else x
    def val(t):
        t = t.strip()
        if t.startswith("#"): return int(t[1:], 0) & M
        return 0 if t == "xzr" else r[t]
    def setf(a, b, sub):
        b2 = (~b) & M if sub else b
        full = a + b2 + (1 if sub else 0); res = full & M
        nzcv[:] = [res >> 63, int(res == 0), full >> 64, int(((a >> 63) == (b2 >> 63)) and ((a >> 63) != (res >> 63)))]
        return res
    def cond(c):
        n, z, cc, v = nzcv
        return {"eq": z, "ne": not z, "ge": n == v, "lt": n != v, "vs": v, "vc": not v, "hs": cc, "lo": not cc}[c]
    pc = 0; steps = 0
    while pc < len(lines):
        steps += 1
        if steps > 500: raise RuntimeError("loop")
        raw = re.sub(r"\s*//.*", "", lines[pc]).strip(); pc += 1
        if not raw or raw.endswith(":") or raw in ("ret", "mov x29, sp") or raw.startswith(("stp", "ldp")): continue
        mn, _, rest = raw.partition(" ")
        ops = [o.strip() for o in re.split(r",\s*(?![^\[]*\])", rest)] if rest else []
        if mn == "mov": r[ops[0]] = val(ops[1])
        elif mn in ("add", "sub"): r[ops[0]] = (val(ops[1]) + (val(ops[2]) if mn == "add" else -val(ops[2]))) & M
        elif mn in ("adds", "subs"): r[ops[0]] = setf(val(ops[1]), val(ops[2]), mn == "subs")
        elif mn == "cmp": setf(val(ops[0]), val(ops[1]), True)
        elif mn == "ccmp":
            if cond(ops[3]): setf(val(ops[0]), val(ops[1]), True)
            else: f = int(ops[2][1:], 0); nzcv[:] = [f >> 3 & 1, f >> 2 & 1, f >> 1 & 1, f & 1]
        elif mn == "ldr": r[ops[0]] = m.get(ops[1], 0)
        elif mn == "str": m[ops[1]] = val(ops[0])
        elif mn == "b.vs" and ops[0] == ".Ltrap":
            if nzcv[3]: raise Trap
        elif mn.startswith("b.") :
            if cond(mn[2:]): pc = labels[ops[0]]
        elif mn == "b": pc = labels[ops[0]]
        else: raise RuntimeError("未対応 " + raw)
    return {k: r[k] for k in ("x%d" % i for i in range(9))}, m

def gen(rng):
    ls = []; nlab = 0; pend = []
    def R(): return "x%d" % rng.choice([0, 0, 1, 2, 9, 9, 10, 10, 11, 12])
    def S(): return "[x29, #%d]" % rng.choice([16, 24, 32])
    for _ in range(rng.randint(3, 14)):
        k = rng.random()
        if k < .15: ls.append("ldr %s, %s" % (R(), S()))
        elif k < .3: ls.append("str %s, %s" % (R(), S()))
        elif k < .45: ls.append("mov %s, %s" % (R(), R()))
        elif k < .55: ls.append("mov %s, #%d" % (R(), rng.choice([0, 1, 2, 7, 4095, 5000])))
        elif k < .7: ls.append("%s %s, %s, %s" % (rng.choice(["add", "sub"]), R(), R(), rng.choice([R(), "#3"])))
        elif k < .8:
            d = R(); ls += ["%s %s, %s, %s" % (rng.choice(["adds", "subs"]), d, R(), rng.choice([R(), "#1"])), "ccmp xzr, %s, #1, vc" % d, "b.vs .Ltrap"]
        elif k < .86: ls.append("cmp %s, %s" % (R(), rng.choice([R(), "#2"])))
        elif k < .93 and not pend:
            nlab += 1; pend.append(".Lq%d" % nlab); ls.append("b.%s %s" % (rng.choice(["eq", "ne", "ge", "lt"]), pend[0]))
        elif pend and k < .97: ls.append(pend.pop() + ":")
    for p in pend: ls.append(p + ":")
    return ls

rng = random.Random(107)
bad = 0; shrunk = 0; total = 0
for t in range(3000):
    ls = gen(rng)
    code = ["fn:", "\tstp x29, x30, [sp, #-48]!", "\tmov x29, sp"] + [l if l.endswith(":") else "\t" + l for l in ls] + RET
    new = sign_peep.optimize(code)
    total += len(code); shrunk += len(code) - len(new)
    for trial in range(4):
        regs = {"x%d" % i: rng.choice([0, 1, 2, 3, (1 << 63) - 1, 1 << 63, M, rng.getrandbits(64)]) for i in range(13)}
        mem = {"[x29, #%d]" % o: rng.getrandbits(64) for o in (16, 24, 32)}
        try: a = run(code, regs, mem)
        except Trap: a = "trap"
        except RuntimeError as e: a = "x"
        try: b = run(new, regs, mem)
        except Trap: b = "trap"
        except RuntimeError as e: b = "x"
        if a != b:
            bad += 1
            if bad <= 2: print("差:", "\n".join(code), "\n---\n", "\n".join(new), "\n", a, b)
            break
check("乱数 3000 本: 最適化の前後で x0〜x8・フレーム・罠が一致", bad, 0)
check("乱数: 命令は減っている(%d → %d 行)" % (total, total - shrunk), shrunk > 0, True)

# ---- 3. 出力全体 ----
import sign_asm, sign_interp
src = open(os.path.join(HERE, "fib_bench.sn"), encoding="utf-8").read()
def lines_of(pe):
    sign_asm.PEEP[0] = pe
    try: t = sign_asm.generate(sign_interp.parse_source(src), "linux", "fib_bench.sn")
    finally: sign_asm.PEEP[0] = True
    return sum(1 for l in t.split("\n") if l.startswith("\t"))
a, b = lines_of(False), lines_of(True)
check("fib_bench: 命令が減る(%d → %d)" % (a, b), b < a, True)
print("全部 ok" if not fails else "NG %d" % fails)
sys.exit(1 if fails else 0)
