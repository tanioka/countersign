"""第二段階: strict の評価器・SIR の評価・生成した機械語(エミュレータ)の 3 者の観測を照合する。
観測(obs): ("val", 整数) / ("void",) / ("trap",) / ("refuse", 理由) / ("unsup", 理由)。
照合の問い 2 つ:
  前段 評価器 = SIR: SIR の下げ・評価が、strict の評価器と同じ答えか(SIR が意味を保存している証拠)
  後段 SIR = 機械語: 機械語が SIR と同じ答えか。断り・罠は許す(合っていない答えより良い)。答えを出して違えば「誤答」
使い方: python3 diff_observe.py [-v]      終了コード: 誤答があれば 1"""
import sys, os, io, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.setrecursionlimit(20000)
src = open(os.path.join(HERE, "test_asm.py"), encoding="utf-8").read()
ns = {"__file__": os.path.join(HERE, "test_asm.py"), "__name__": "emu"}
exec(compile(src[:src.index("# ---------------- 処理系の答え")], "emu", "exec"), ns)
import sign_asm, sign_interp as S, sign_sir as R
from fixblank import fix
sign_asm.STRICT[0] = True
verbose = "-v" in sys.argv

def obs_strict(t):
    S.STRICT_GATES = True
    try:
        S.MEMORY.clear(); S.WARNINGS.clear()
        old = sys.stdout; sys.stdout = io.StringIO()
        try: r = S.run(t)
        finally: sys.stdout = old
        v = S.show(r[-1]) if r else "!_"
    except BaseException as e: return ("refuse", type(e).__name__)
    finally: S.STRICT_GATES = False
    return ("void",) if v == "!_" else (("val", int(v)) if v.lstrip("-").isdigit() else ("unsup", "値 " + v[:20]))

def obs_sir(t):
    try:
        f, top = R.lower(S.parse_source(t))
        if top is None: return ("unsup", "最後の行が無い")
        return R.evaluate(f, top) if False else (lambda r: ("unsup", "fuel") if r == ("fuel",) else r)(R.evaluate(f, top))
    except R.Unsup as e: return ("unsup", str(e))

def obs_asm(t):
    try:
        tree, rest = sign_asm.strict_rewrite(S.parse_source(t))
        if rest: return ("refuse", "strict_rewrite: " + rest[0][1][:30])
        got = ns["run_asm"](sign_asm.generate(tree))
    except sign_asm.AsmError as e: return ("refuse", str(e)[:40])
    except Exception as e: return ("refuse", "例外 " + str(e)[:30])
    if got[0] == "trap": return ("trap",)
    if got[0] != "ok": return ("refuse", str(got)[:30])
    return ("void",) if got[1] == "__" else ("val", got[1])

i_ = src.index("MAX, MIN1 = "); j_ = src.index("\n]\n", src.index("CASES = [")) + 3
exec(src[i_:j_], ns)
front = collections.Counter(); back = collections.Counter(); unsup = collections.Counter(); bad = []
for name, t in ns["CASES"]:
    t2 = fix(t)
    a, b = obs_strict(t2), obs_sir(t2)
    if b[0] == "unsup": front["SIR 未対応"] += 1; unsup[b[1][:24]] += 1; continue
    if a == b: front["一致"] += 1
    elif a[0] == "void" and b[0] == "void": front["一致"] += 1
    elif a[0] == "refuse": front["評価器が断る"] += 1
    elif b == ("partial",): front["SIR: 部分適用(実引数が void)"] += 1
    else: front["食い違い"] += 1; bad.append(("前段", name, a, b))
    c = obs_asm(t2)
    if b in (("partial",),): continue
    if c == b: back["一致"] += 1
    elif c[0] == "refuse": back["機械語が断る"] += 1
    elif c[0] == "trap": back["機械語が罠(溢れ・部分適用)"] += 1
    else: back["誤答"] += 1; bad.append(("後段", name, b, c))
print("前段(評価器 = SIR):", dict(front)); print("後段(SIR = 機械語):", dict(back))
print("SIR に下げられない形(上位):", unsup.most_common(8))
for x in bad: print("NG", *x)
sys.exit(1 if [x for x in bad] else 0)
