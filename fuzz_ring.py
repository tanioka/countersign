# 輪・複数の累積・文字列の累積の乱数試験: 乱数で作った相互再帰(2〜3 個の関数、渡すだけの辺、伸びる辺、複数の累積)を、
# asm が受理したものだけ処理系と答えを比べる。使い方: python3 fuzz_ring.py 種 個数   最後の行: "fuzz_ring: 受理 N 断り M 不一致 K"
import sys, os, random, subprocess, tempfile
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
src = open(os.path.join(HERE, "test_asm.py"), encoding="utf-8").read()
ns = {"__file__": os.path.join(HERE, "test_asm.py"), "__name__": "emu"}
exec(compile(src[:src.index("# ---------------- 処理系の答え")], "emu", "exec"), ns)
import sign_asm, sign_interp
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1; count = int(sys.argv[2]) if len(sys.argv) > 2 else 40
rnd = random.Random(seed)
def lst(n): return "(" + " ".join(str(rnd.randint(1, 9)) for _ in range(n)) + ")"
def prog_counter():
    """カウンタ(i)を進める辺を持つ輪。どの辺も『ys を食う』か『i を進める』かの少なくとも一方をする(止まる)。i を 0 に戻す辺は ys を食う。"""
    nf = rnd.choice([2, 2, 3]); names = ["f%d" % k for k in range(nf)]; out = []
    for k, nm in enumerate(names):
        nxt = names[(k + 1) % nf]
        eat = rnd.random() < 0.5; count = (not eat) or rnd.random() < 0.5
        reset = eat and rnd.random() < 0.15
        ys = "(ys ' %d~)" % rnd.randint(1, 2) if eat else "ys"
        iv = "0" if reset else ("(i + %d)" % rnd.randint(1, 2) if count else "i")
        items = [rnd.choice(["(s ' i)", "(ys ' 0)", str(rnd.randint(1, 9)), "(s ' 0)"]) for _ in range(rnd.randint(1, 2))]
        acc = "acc" if rnd.random() < 0.2 else "(acc~ %s)" % " ".join(items)
        tail = rnd.choice(["acc", "acc~ 9"])
        out.append("%s : s ys i acc ?\n\t||ys|| < %d | i >= ||s|| : %s\n\t%s s %s %s %s\n" % (nm, rnd.randint(1, 2), tail, nxt, ys, iv, acc))
    return "".join(out) + "f0 %s %s %d %s\n" % (lst(rnd.randint(2, 5)), lst(rnd.randint(2, 9)), rnd.randint(0, 2), lst(rnd.randint(2, 3)))
def prog():
    if rnd.random() < 0.4: return prog_counter()
    nf = rnd.choice([2, 2, 3]); strmode = rnd.random() < 0.3; two = (not strmode) and rnd.random() < 0.35
    names = ["f%d" % k for k in range(nf)]
    accp = ["acc", "acc2"] if two else ["acc"]
    ps = "s ys " + " ".join(accp)
    out = []
    for k, nm in enumerate(names):
        nxt = names[(k + 1) % nf]
        ex = rnd.randint(1, 3)
        def grow(a):
            r = rnd.random()
            if r < 0.3: return a
            if strmode: return "(%s %s)" % (a, " ".join("`%s`" % ("x" * rnd.randint(1, 2)) for _ in range(rnd.randint(1, 2))))
            items = [rnd.choice(["(s ' 0)", "(ys ' 0)", str(rnd.randint(1, 9)), "(s ' -1)"]) for _ in range(rnd.randint(1, 3))]
            return "(%s~ %s)" % (a, " ".join(items))
        args = [grow(a) for a in accp]
        if k == 0 and all(x in accp for x in args) and rnd.random() < 0.8: args[0] = grow(accp[0]) if not strmode else "(acc `a`)"
        tail = rnd.choice(["acc", "acc"] + ([] if strmode else ["acc~ 9", "acc~ (acc2 ' 0)"] if two else ["acc~ 9"])) if not strmode else rnd.choice(["acc", "acc `!`"])
        out.append("%s : %s ?\n\t||ys|| < %d : %s\n\t%s s (ys ' %d~) %s\n" % (nm, ps, ex, tail, nxt, rnd.randint(1, 2), " ".join(args)))
    ys = "".join("z" for _ in range(rnd.randint(0, 9))) if strmode else None
    if strmode: call = "f0 `ab` `%s` `q`" % ("z" * rnd.randint(2, 9))
    else: call = "f0 %s %s %s" % (lst(rnd.randint(2, 4)), lst(rnd.randint(2, 9)), " ".join(lst(rnd.randint(2, 3)) for _ in accp))
    return "".join(out) + call + "\n"
acc = ref = bad = est_over = 0; why = {}
for _ in range(count):
    t = prog(); p = os.path.join(tempfile.mkdtemp(), "t.sn"); open(p, "w").write(t)
    want = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p], capture_output=True, text=True).stdout
    try: asm = sign_asm.generate(sign_interp.parse_source(t), "linux"); inf = list(sign_asm.LAST_INFOS)
    except sign_asm.AsmError as e: ref += 1; why[str(e).split(':',1)[-1].strip()[:44]] = why.get(str(e).split(':',1)[-1].strip()[:44], 0) + 1; continue
    except Exception as e: print("例外", e, repr(t)); bad += 1; continue
    try: got = ns["run_asm"](asm, linux=True)[1]
    except Exception as e: got = "EXC %s" % e
    acc += 1
    if os.environ.get("FUZZ_LLVM") != "0":                       # 別実装(llvm-mc)で組めるか(bare と linux の両方)
        import llvm_check
        for _tg in ("linux", "bare"):
            _a = asm if _tg == "linux" else sign_asm.generate(sign_interp.parse_source(t), "bare")
            _e = llvm_check.check(_a)
            if _e: bad += 1; print("llvm-mc が組めない(%s)" % _tg, repr(t), _e)
    if inf and got != want and got.endswith("__\n") and "work area overflow" in got: est_over += 1; continue         # 見積もりで通した形が見積もりを超えた: 仕様で許される `__`(診断つき)
    if got != want: bad += 1; print("不一致", repr(t), repr(got), repr(want))
print("fuzz_ring: 受理 %d 断り %d 不一致 %d(見積もり超過の `__` %d)" % (acc, ref, bad, est_over))
if os.environ.get("FUZZ_WHY"):
    for k, v in sorted(why.items(), key=lambda kv: -kv[1])[:8]: print("  断り理由 %3d  %s" % (v, k))
