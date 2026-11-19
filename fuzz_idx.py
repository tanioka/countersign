# 添字の範囲解析の乱数試験: 乱数で作った条件・添字・呼びの式で、受理された asm が処理系と同じ答えかを調べる。
# 使い方: python3 fuzz_idx.py 種 個数    出力の最後の行: "fuzz_idx: 受理 N 断り M 不一致 K"
import sys, os, random, subprocess, tempfile
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
src = open(os.path.join(HERE, "test_asm.py"), encoding="utf-8").read()
ns = {"__file__": os.path.join(HERE, "test_asm.py"), "__name__": "emu"}
exec(compile(src[:src.index("# ---------------- 処理系の答え")], "emu", "exec"), ns)
import sign_asm, sign_interp
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1; count = int(sys.argv[2]) if len(sys.argv) > 2 else 40
rnd = random.Random(seed)
def intx(d=0):
    c = rnd.random()
    if d > 1 or c < 0.3: return rnd.choice(["i", "j", "i", str(rnd.randint(-3, 4)), "||xs||"])
    op = rnd.choice(["+", "-", "+", "-", "*", "%", "/"])
    b = intx(d + 1)
    if op in "%/" : b = rnd.choice(["||xs||", "2", "3"])
    return "(%s %s %s)" % (intx(d + 1), op, b)
def cond():
    t = rnd.choice(["<", "<=", ">", ">=", "="])
    c = "%s %s %s" % (intx(1), t, intx(1))
    return c
def prog():
    if rnd.random() < 0.5:            # 簡単な添字と簡単な条件(下限が負になる事実を出しやすい)
        idx = rnd.choice(["i", "j", "(i + %d)" % rnd.randint(-4, 4), "(i - j)", "(j - i)", "(i - %d)" % rnd.randint(-4, 4), "(i + j)"])
        sc = lambda: "%s %s %s" % (rnd.choice(["i", "j", "(i - j)", "(i + %d)" % rnd.randint(-3, 3), "(j - %d)" % rnd.randint(-3, 3)]), rnd.choice(["<", "<=", ">", ">="]), rnd.choice(["i", "j", str(rnd.randint(-5, 5)), "||xs||", "(j + %d)" % rnd.randint(-5, 5)]))
    else: idx = intx() if rnd.random() < 0.6 else "(%s - ||xs||)" % intx(1); sc = cond
    step_i = rnd.choice(["i + 1", "i - 1", "i + 2", "i", "i * 2"]); step_j = rnd.choice(["j", "j + 1", "j - 1"])
    if rnd.random() < 0.15:           # 入れ子の内側の長さの下限(条件 ||m ' i|| < L の偽)で、内側の添字を守る形
        C = rnd.choice([0, 1, 1, 2, 2, 3, -1, -2, -3]); need = C + 1 if C >= 0 else -C
        L = need + rnd.choice([0, 0, 0, -1, 1])
        inner = " ".join("(" + " ".join(str(rnd.randint(1, 9)) for _ in range(rnd.randint(2, 4))) + ")" for _ in range(rnd.randint(2, 4)))
        return ("f : m ys i acc ?\n\t||ys|| < 2 | i >= ||m|| | i < 0 | ||m ' i|| < %d : acc\n\tf m (ys ' 1~) (i + 1) (acc~ ((m ' i) ' %d))\nf (%s) (1 2 3 4 5 6 7 8) %d (0 0)\n" % (L, C, inner, rnd.randint(0, 2)))
    m = rnd.random()
    if rnd.random() < 0.25:           # 末尾から数える添字 (A - ||xs||): A が 0 以上で ||xs|| 未満のときだけ範囲内
        A = rnd.choice(["i", "j", "(i + %d)" % rnd.randint(-2, 2), "(i %% %d)" % rnd.randint(1, 5), "(i - j)"])
        gs = ["%s < %d" % (A, rnd.choice([0, 0, 0, 1, -1])), "%s %s ||xs||%s" % (A, rnd.choice([">=", ">=", ">"]), rnd.choice(["", "", " + 1", " - 1"]))]
        if rnd.random() < 0.3: gs.append("i < %d" % rnd.randint(-2, 2))
        rnd.shuffle(gs)
        return ("f : xs ys i j acc ?\n\t||ys|| < 2 | %s : acc\n\tf xs (ys ' 1~) (%s) (%s) (acc~ (xs ' (%s - ||xs||)))\nf (%s) (1 2 3 4 5 6 7 8) %d %d (0 0)\n"
                % (" | ".join(gs), rnd.choice(["i + 1", "i + 2", "i - 1"]), rnd.choice(["j", "j + 1"]), A, " ".join(str(rnd.randint(1, 9)) for _ in range(rnd.randint(2, 6))), rnd.randint(-2, 5), rnd.randint(-2, 4)))
    if rnd.random() < 0.3:            # 上限の事実: 器の長さの下限と、Int の上限・下限(区間)で守る形
        e = rnd.choice(["i", "(i + %d)" % rnd.randint(-2, 3), "(i %% %d)" % rnd.randint(1, 4), "((i * %d) %% %d)" % (rnd.randint(1, 3), rnd.randint(1, 5)), "(i / %d)" % rnd.randint(1, 3), "(i - j)", "((i %% %d) + %d)" % (rnd.randint(1, 3), rnd.randint(-1, 2)), "(i * %d)" % rnd.randint(0, 2)])
        gs = ["||xs|| < %d" % rnd.randint(1, 4), "i < %d" % rnd.randint(-2, 2), "i > %d" % rnd.randint(0, 4)]
        if rnd.random() < 0.3: gs.append("j < %d" % rnd.randint(-2, 2))
        rnd.shuffle(gs)
        return ("f : xs ys i j acc ?\n\t||ys|| < 2 | %s : acc\n\tf xs (ys ' 1~) (%s) (%s) (acc~ (xs ' %s))\nf (%s) (1 2 3 4 5 6 7 8) %d %d (0 0)\n"
                % (" | ".join(gs), rnd.choice(["i + 1", "i + 2", "i - 1"]), rnd.choice(["j", "j + 1"]), e, " ".join(str(rnd.randint(1, 9)) for _ in range(rnd.randint(2, 6))), rnd.randint(-2, 4), rnd.randint(-2, 4)))
    if rnd.random() < 0.3:            # 狙い撃ち: 範囲の上側は守るが、下側は負の下限の事実(i ≥ -c、i ≥ j - c)だけで守る形
        idx = rnd.choice(["i", "(i - j)", "(i + %d)" % rnd.randint(-2, 2), "(i - j + %d)" % rnd.randint(-2, 2)])
        lo = rnd.choice(["i < %d" % -rnd.randint(0, 9), "i < j - %d" % rnd.randint(0, 9), "i < j + %d" % rnd.randint(-3, 3), "(i - j) < %d" % rnd.randint(-9, 2)])
        g = " | ".join(rnd.sample(["%s >= ||xs||" % idx, lo], 2))
        return ("f : xs ys i j acc ?\n\t||ys|| < 2 | %s : acc\n\tf xs (ys ' 1~) (%s) (%s) (acc~ (xs ' %s))\nf (%s) (1 2 3 4 5 6 7 8) %d %d (0 0)\n"
                % (g, rnd.choice(["i + 1", "i - 1", "i"]), rnd.choice(["j", "j + 1"]), idx, " ".join(str(rnd.randint(1, 9)) for _ in range(rnd.randint(2, 6))), rnd.randint(-4, 8), rnd.randint(-4, 8)))
    if m < 0.6:                       # 添字の式から導いた守り(ずらしたものは、範囲外を通しうる)
        d1, d2 = rnd.choice([0, 0, 0, 0, 1, -1]), rnd.choice([0, 0, 0, 0, 1, -1])
        gs = ["%s < %d" % (idx, d1), "%s >= ||xs|| + %d" % (idx, d2)]
        if rnd.random() < 0.7: gs += [sc() for _ in range(rnd.randint(1, 2))]
        rnd.shuffle(gs); g = " | ".join(gs)
    elif m < 0.8: g = " | ".join([sc() for _ in range(rnd.randint(1, 3))])
    else: g = sc() + " | " + sc()
    return ("f : xs ys i j acc ?\n\t||ys|| < 2 | %s : acc\n\tf xs (ys ' 1~) (%s) (%s) (acc~ (xs ' %s))\nf (%s) (1 2 3 4 5 6 7 8) %d %d (0 0)\n"
            % (g, step_i, step_j, idx, " ".join(str(rnd.randint(1, 9)) for _ in range(rnd.randint(2, 6))), rnd.randint(-4, 8), rnd.randint(-4, 8)))
def as_string(t):
    """リストの器 xs を文字列 s に、累積を文字列に直す(`__` の要素は並びから消える挙動が文字列でも同じかを見る)。"""
    import re
    t = t.replace("acc~ (xs ' ", "acc (xs ' ").replace("xs", "s")
    t = re.sub(r"\nf \(([0-9 ]+)\) ", lambda m: "\nf `%s` " % "".join(chr(96 + int(x)) for x in m.group(1).split()), t)
    return t.replace("(0 0)\n", "`q`\n")
def as_nested(t):
    """リスト xs を入れ子 m に直し、取り出す要素を内側の先頭・末尾・2 番目にする(内側は長さ 2 以上)。"""
    import re
    c = rnd.choice(["0", "-1", "1", "1", "2"])
    em = re.search(r"acc~ \(xs ' (.*)\)\)\n", t)
    if c in ("1", "2") and em and rnd.random() < 0.7:          # 内側の長さの下限を条件で与える(ずらしたものは範囲外を通しうる)
        lim = int(c) + 1 + rnd.choice([0, 0, 0, -1, 1])
        t = t.replace("||ys|| < 2 | ", "||ys|| < 2 | ||xs ' %s|| < %d | " % (em.group(1), lim), 1)
    t = re.sub(r"acc~ \(xs ' (.*)\)\)\n", lambda m: "acc~ ((xs ' %s) ' %s))\n" % (m.group(1), c), t)
    t = t.replace("xs", "m")
    return re.sub(r"\nf \(([0-9 ]+)\) ", lambda m: "\nf (%s) " % " ".join("(%d %d)" % (int(x), int(x) % 9 + 1) for x in m.group(1).split()), t)
acc = ref = bad = 0; why = {}
for _ in range(count):
    t = prog()
    r_ = rnd.random()
    if r_ < 0.2: t = as_string(t)
    elif r_ < 0.4: t = as_nested(t)
    p = os.path.join(tempfile.mkdtemp(), "t.sn"); open(p, "w").write(t)
    want = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p], capture_output=True, text=True).stdout
    try: asm = sign_asm.generate(sign_interp.parse_source(t), "linux")
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
    if got != want: bad += 1; print("不一致", repr(t), repr(got), repr(want))
print("fuzz_idx: 受理 %d 断り %d 不一致 %d" % (acc, ref, bad))
if os.environ.get("FUZZ_WHY"):
    for k, v in sorted(why.items(), key=lambda kv: -kv[1])[:8]: print("  断り理由 %3d  %s" % (v, k))
