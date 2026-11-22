"""観測を値だけでなく『終わり方・値・メモリの最終状態・知らせ』の組に広げ、strict の評価器と機械語(エミュレータ)を乱数で比べる。
  python3 fuzz_obs.py [件数=300] [種=1]      終了コード: 誤答(両方が答えを出して食い違う)があれば 1
観測 Obs = (end, value, mem, warns)
  end   normal / trap(機械語の罠・評価器の `!_` にならない溢れ) / refuse(断り)
  value ("val", n) / ("void",) ; mem = {番地: 値}(書かれた番地の最終値)
  warns = 評価器が出した知らせの名前の集合(機械語は知らせを出さないので比べず、別に数える)
SIR は書き込みを持たない(unsup)ので、ここでは評価器と機械語だけ。"""
import sys, os, io, random
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.setrecursionlimit(20000)
import sign_interp as S, sign_asm, fuzz_sir as F
from fixblank import fix

BASE = 0x500000
def addr(r): return "0x%X" % (BASE + 8 * r.randint(0, 5))
def val(r):
    c = r.random()
    if c < .15: return "__"
    if c < .25: return "(3 > 5)"                           # `!_` と分かる値(書かない)
    if c < .45: return "(%s %s %s)" % (r.choice([1, 2, 7, 100]), r.choice("+-*"), r.choice([3, 5, 9]))
    if c < .55: return "(@%s)" % addr(r)                    # 読んだ値を書く(書いていなければ `__`)
    return str(r.choice([0, 1, -5, 7, 42, 255, 9223372036854775807]))
def program(r):
    lines = ["%s # %s" % (addr(r), val(r)) for _ in range(r.randint(1, 5))]
    k = r.random()
    if k < .5: last = "(@%s) + (@%s)" % (addr(r), addr(r))
    elif k < .75: last = "(@%s) | %s" % (addr(r), r.choice(["7", "(@%s)" % addr(r)]))
    else: last = "@%s" % addr(r)
    return "\n".join(lines + [last]) + "\n"

def obs_eval(t):
    S.STRICT_GATES = True
    try:
        S.MEMORY.clear(); S.WARNINGS.clear(); old = sys.stdout; sys.stdout = io.StringIO()
        try: res = S.run(t)
        finally: sys.stdout = old
        v = S.show(res[-1]) if res else "!_"
        mem = {a: x for a, x in S.MEMORY.items() if isinstance(a, int) and BASE <= a < BASE + 0x100 and isinstance(x, int)}
        ws = {k[0] for k in S.WARNINGS}
    except BaseException as e: return ("refuse", type(e).__name__), None, None
    finally: S.STRICT_GATES = False
    val_ = ("void",) if v == "!_" else (("val", int(v)) if v.lstrip("-").isdigit() else ("other", v[:20]))
    return ("normal",) + val_, mem, ws

def obs_machine(t):
    F.obs_asm("0\n")                                                    # エミュレータの準備
    Cpu = F._ns["Cpu"]
    try:
        sign_asm.STRICT[0] = True
        tree, rest = sign_asm.strict_rewrite(S.parse_source(t))
        if rest: return ("refuse", "strict_rewrite"), None, None
        cpu = Cpu(sign_asm.generate(tree, "linux"))
        try: cpu.run("_start")
        except F._ns["Trap"]: return ("trap",), None, None
    except (sign_asm.AsmError, sign_asm.StrictRefusal) as e: return ("refuse", str(e)[:30]), None, None
    except Exception as e: return ("refuse", "例外 " + type(e).__name__), None, None
    g = F._got(("exit", cpu.out.decode(), cpu.exit))
    mem = {}
    for a in range(BASE, BASE + 0x100, 8):
        if any((a + i) in cpu.mem for i in range(8)):
            v = sum(cpu.mem.get(a + i, 0) << (8 * i) for i in range(8))
            if v >= 1 << 63: v -= 1 << 64
            mem[a] = v
    return ("normal",) + g, mem, None

def judge(t):
    (e1, m1, w1), (e2, m2, _) = obs_eval(t), obs_machine(t)
    if e1[0] != "normal" or e2[0] != "normal": return "断り・罠(片方または両方)", (t, e1, m1, e2, m2)
    return ("一致" if e1 == e2 and m1 == m2 else "誤答"), (t, e1, m1, e2, m2)

def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 300; r = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    tally = {}; bad = []
    init = "".join("0x%X # 0\n" % (BASE + 8 * k) for k in range(6))                  # 先に全部の番地へ 0 を書く: 『書かれていない読み』を除いた比べ
    for _ in range(n):
        t0 = program(r)
        k, rec = judge(fix(init + t0))
        if k == "一致":
            k0, _r = judge(fix(t0))                                         # 元の形(書かれていない所を読みうる)
            if k0 == "誤答": k = "未決(書かれていない所の読み。処理系は __・機械語は 0。設計者への質問 (b))"
        tally[k] = tally.get(k, 0) + 1
        if k == "誤答": bad.append(rec)
    print(tally)
    for t, e1, m1, e2, m2 in bad[:6]: print("---\n" + t + f"評価器 {e1} {m1}\n機械語 {e2} {m2}")
    return 1 if bad else 0
if __name__ == "__main__": sys.exit(main())
