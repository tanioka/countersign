# 回る回数(Int カウンタ・定数の上限・変わらない Int・器)の乱数試験。
# 規則: 証明で通した形(information なし)は処理系と同じ答えでなければならない。見積もりで通した形(information あり)は、同じ答えか、
# 見積もり超過の `__`(診断つき)のどちらか。使い方: python3 fuzz_cnt.py 種 個数    最後の行: "fuzz_cnt: 受理 N (証明 P / 見積もり E) 断り M 不一致 K"
import sys, os, random, subprocess, tempfile
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
src = open(os.path.join(HERE, "test_asm.py"), encoding="utf-8").read()
ns = {"__file__": os.path.join(HERE, "test_asm.py"), "__name__": "emu"}
exec(compile(src[:src.index("# ---------------- 処理系の答え")], "emu", "exec"), ns)
import sign_asm, sign_interp
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1; count = int(sys.argv[2]) if len(sys.argv) > 2 else 40
rnd = random.Random(seed)
def prog():
    r = rnd.random()
    if r < 0.25:                                   # 下向きのカウンタ(証明できる)
        lo = rnd.randint(-4, 3); st = rnd.randint(-5, 9); sp = rnd.randint(1, 3); op = rnd.choice(["<=", "<"])
        lit = lambda v: str(v) if v >= 0 else "(0 - %d)" % -v
        body = "f : n acc ?\n\tn %s %s : acc\n\tf (n - %d) (acc~ n %s)\n" % (op, lit(lo), sp, rnd.choice(["", "n"]))
        if rnd.random() < 0.4: return body + "g : k ?\n\tf k (7 7)\ng %s\n" % lit(st)
        return body + "f %s (7 7)\n" % lit(st)
    if r > 0.65:                                   # 二重ループ(内側が尽きたら外側を進めて内側を 0 に戻す)
        A, B = rnd.randint(1, 4), rnd.randint(1, 4); si, sj = rnd.randint(1, 2), rnd.randint(1, 2)
        gi = rnd.choice(["i >= %d" % A, "i > %d" % A]); gj = rnd.choice(["j >= %d" % B, "j > %d" % B, "j >= i"])
        grow_o = rnd.choice(["acc", "(acc~ i)"]); st = rnd.choice(["0 0", "0 0", "1 0", "0 1", "(0 - 1) 0"])
        return ("f : i j acc ?\n\t%s : acc\n\t%s : f (i + %d) 0 %s\n\tf i (j + %d) (acc~ %s)\nf %s (7 7)\n"
                % (gi, gj, si, grow_o, sj, rnd.choice(["j", "(i * 10 + j)", "5"]), st))
    wrap = r > 0.6
    t = prog0()
    if wrap and "f n" in t:                         # Int の仮引数を包みの関数から渡す
        i = t.rindex("\nf ") + 1; call = t[i:]
        parts = call.split(" ", 2)
        return t[:i] + "g : k ?\n\tf k %s" % parts[2] + "g %s\n" % parts[1]
    return t
def prog0():
    step = rnd.randint(1, 4); start = rnd.randint(-5, 6); hi = rnd.randint(0, 12)
    op = rnd.choice([">=", ">"]); useN = rnd.random() < 0.4; useX = rnd.random() < 0.4; nd = rnd.randint(1, 2)
    elem = rnd.choice(["i", "(i * 2)", "7"] + (["(xs ' 0)"] if useX else []))
    add = " ".join([elem] * nd)
    ps = ["i"] + (["n"] if useN else []) + (["xs"] if useX else []) + ["acc"]
    bound = "n" if useN else str(hi)
    call = ["(i + %d)" % step] + (["n"] if useN else []) + (["xs"] if useX else []) + ["(acc~ %s)" % add]
    first = [str(start) if start >= 0 else "(0 - %d)" % -start] + ([str(rnd.randint(0, 9))] if useN else []) + (["(4 5 6)"] if useX else []) + ["(7 7)"]
    return "f : %s ?\n\ti %s %s : acc\n\tf %s\nf %s\n" % (" ".join(ps), op, bound, " ".join(call), " ".join(first))
acc = pr = es = ref = bad = eq = 0
for _ in range(count):
    t = prog()
    p = os.path.join(tempfile.mkdtemp(), "t.sn"); open(p, "w").write(t)
    want = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p], capture_output=True, text=True).stdout
    try: asm = sign_asm.generate(sign_interp.parse_source(t), "linux"); inf = list(sign_asm.LAST_INFOS)
    except sign_asm.AsmError: ref += 1; continue
    except Exception as e: print("例外", e, repr(t)); bad += 1; continue
    try: r = ns["run_asm"](asm, linux=True)
    except Exception as e: r = (0, "EXC %s" % e)
    got = r[1]; acc += 1
    if os.environ.get("FUZZ_LLVM") != "0":                       # 別実装(llvm-mc)で組めるか(bare と linux の両方)
        import llvm_check
        for _tg in ("linux", "bare"):
            _a = asm if _tg == "linux" else sign_asm.generate(sign_interp.parse_source(t), "bare")
            _e = llvm_check.check(_a)
            if _e: bad += 1; print("llvm-mc が組めない(%s)" % _tg, repr(t), _e)
    if inf: es += 1; eq += (got == want)
    else: pr += 1
    ok = got == want or (inf and got.endswith("__\n"))
    if not ok: bad += 1; print("不一致", repr(t), repr(got), repr(want), bool(inf))
print("fuzz_cnt: 受理 %d (証明 %d / 見積もり %d、うち答えが一致 %d) 断り %d 不一致 %d" % (acc, pr, es, eq, ref, bad))
