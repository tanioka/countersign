"""test_asm_spec.py — --asm --par-spec(sign_asmpar.py の投機)。
`l | r`・`l & r`・`cond : v` の右・値(必ず終わると言える純粋な整数関数の呼び出し)を、左・条件を調べる間に別のスレッドで先に走らせる。
確かめること: (1) 答えが直列・--par と同じ(順番・強制切り替えを変えても)  (2) 要らない投機が罠にぶつかっても止まらない・要る所では直列と同じに止まる
(3) 巻き戻しが実際に起きた(入れ物の失敗の印)  (4) 『必ず終わる』の判定(終わると言えない物は投機にしない)  (5) 池が尽きる・走行中の投機を捨てる  (6) 組み立て。
疑似カーネルの協調スレッドで、本物の Linux・本物のスレッドではない(実機では未実行)。"""
import os, shutil, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import emu_dev, fake_kernel, sign_asm, sign_interp, sign_asmpar
fails = 0
def check(name, got, want):
    global fails
    if got == want: print("ok ", name)
    else: fails += 1; print("NG ", name, "\n    want", repr(want), "\n    got ", repr(got))
if os.environ.get("SPEC_ABORT_ALL"): sign_asm.SPEC_ABORT[0] = True      # 全部の試験を、投機専用の複製ありで回す
ABORT_DEFAULT = sign_asm.SPEC_ABORT[0]
CPU = emu_dev.load_cpu_class()["Cpu"]
LIMIT = 60_000_000

def run(src, par=4, spec=True, seed=None, every=None):
    k = fake_kernel.Kernel(); k.sched_seed = seed; k.thread_limit = LIMIT
    class KC(CPU):
        def syscall(self, n): return k.handle(self, n)
    text = sign_asm.generate(sign_interp.parse_source(src), "linux", par=par, par_spec=spec)
    cpu = KC(text)
    if every: k.preempt(cpu, every)
    try: cpu.run("_start", limit=LIMIT); cpu.stat = "ret"
    except SystemExit: cpu.stat = "exit"
    except BaseException as e: cpu.stat = type(e).__name__
    return cpu, k, text

def fail_flags(cpu):
    a = cpu.data.get("_sign_spec_pool")
    return [cpu.mem.get(a + 160 * i + 104, 0) for i in range(32)] if a is not None else []

PAIRS = ((None, None), (1, 11), (2, 29), (3, 7), (4, 3), (5, 101))
def matrix(name, src, want=None, trap=False):
    """直列(--par 無し)を基準に、--par-spec の全部の順番で 答え・止まり方 が同じ。"""
    base, _, _ = run(src, None, False)
    ref = (base.out, base.stat == "Trap", base.r.get("x16") if base.stat == "Trap" else 0)
    ok = True; flags = 0
    for sd, ev in PAIRS:
        cpu, k, t = run(src, 4, True, sd, ev)
        r = (cpu.out, cpu.stat == "Trap", cpu.r.get("x16") if cpu.stat == "Trap" else 0)
        flags += sum(fail_flags(cpu))
        if r != ref: ok = False; print("   NG", name, sd, ev, r, ref, cpu.stat)
    if want is not None and ref[0] != want: ok = False; print("   基準が違う", ref, want)
    if trap and not ref[1]: ok = False; print("   止まるはずが止まらない")
    check("%s: 直列と同じ(答え・止まり方。順番 %d 通り)" % (name, len(PAIRS)), ok, True)
    return flags

FIB = "fib : n ?\n\tn < 2 : n\n\t(fib (n - 1)) + (fib (n - 2))\ncnt : n ?\n\tn > 0 : 1 + (cnt (n - 1))\n\t0\nslow : n ? (fib n) - n\nov : n ? n * 4611686018427387904\n"
def has_spec(src, **kw): return "_sign_spec_alloc" in run(src, 4, True, **kw)[2]

# (1)(2) 答えと罠
matrix("| 左が決める・右は罠", FIB + "h : n ? (slow n) = 45 | (ov n)\nh 10\n", b"45\n")
matrix("| 左が __・右は罠(直列と同じに止まる)", FIB + "h : n ? (slow n) = 99 | (ov n)\nh 10\n", None, trap=True)
matrix("| 左が __・右が答え", FIB + "h : n ? (slow n) = 99 | (cnt 20)\nh 10\n", b"20\n")
matrix("& 左が __ なら __", FIB + "h : n ? ((slow n) = 99) & (cnt 20)\nh 10\n", b"__\n")
matrix("& 左が決まれば右", FIB + "h : n ? ((slow n) = 45) & (cnt 20)\nh 10\n", b"20\n")
matrix("& 左が決まる・右は罠(直列と同じに止まる)", FIB + "h : n ? ((slow n) = 45) & (ov n)\nh 10\n", None, trap=True)
matrix("& 左が __・右は罠(止まらない)", FIB + "h : n ? ((slow n) = 99) & (ov n)\nh 10\n", b"__\n")
matrix("枝 条件が成り立つ", FIB + "h : n ?\n\t(slow n) = 45 : cnt 30\n\t7\nh 10\n", b"30\n")
matrix("枝 条件が外れる", FIB + "h : n ?\n\t(slow n) = 5 : cnt 30\n\t7\nh 10\n", b"7\n")
matrix("枝 成り立つ・値は罠(止まる)", FIB + "h : n ?\n\t(slow n) = 45 : ov 3\n\t7\nh 10\n", None, trap=True)
matrix("枝 外れる・投機の罠は捨てる", FIB + "h : n ?\n\t(slow n) = 5 : ov 3\n\t7\nh 10\n", b"7\n")
matrix("枝 次の行も投機", FIB + "h : n ?\n\t(slow n) = 5 : cnt 30\n\t(slow n) = 45 : cnt 31\n\t7\nh 10\n", b"31\n")
matrix("枝 最後の行は既定", FIB + "h : n ?\n\t(slow n) = 1 : cnt 30\n\t(slow n) = 2 : cnt 31\n\t9\nh 10\n", b"9\n")
matrix("左が __ になる n・右の罠が要る(止まる)", FIB + "h : n ? (slow n) = 45 | (ov n)\nh 11\n", None, trap=True)
# 協力して止める: 捨てられた投機は、再帰する関数の入口で気づいて巻き戻して抜ける(入れ物の失敗の印が立つ)
sign_asm.SPEC_ABORT[0] = True
_tx = run(FIB + "h : n ?\n\t(slow n) = 5 : slow 22\n\t(slow 20) + (cnt 30)\nh 12\n", 4, True)[2]
_orig = _tx[_tx.index("\nfib:\n"):_tx.index("\nfib__sp:\n")]
check("複製ができ、元の関数には確認が入らない", ("\nfib__sp:\n" in _tx, "_sign_sa_" in _orig, "_sign_sa_fib:" in _tx), (True, False, True))
fl = matrix("捨てられた走行中の投機を止める", FIB + "h : n ?\n\t(slow n) = 5 : slow 22\n\t(slow 20) + (cnt 30)\nh 12\n", None)
check("捨てられた投機が入口で巻き戻した(失敗の印がどれかの順番で立つ)", fl > 0, True)
sign_asm.SPEC_ABORT[0] = ABORT_DEFAULT
# 先読み: 行の並びで、N 行先の値も先に走らせる(--spec-look)
sign_asm.SPEC_LOOK[0] = 3
_lk = FIB + "h : n ?\n\t(slow n) = 5 : cnt 30\n\t(slow n) = 6 : cnt 31\n\t(slow n) = 45 : cnt 32\n\t7\nh 10\n"
_ab = sign_asm.SPEC_ABORT[0]; sign_asm.SPEC_ABORT[0] = False      # 複製ありだと関数ごとに倍になるので、数えるときは切る
check("先読み: 投機の入れ物を行ごとに出す(3 つ)", run(_lk, 4, True)[2].count("bl _sign_spec_alloc"), 3)
sign_asm.SPEC_ABORT[0] = _ab
matrix("先読み 3 行目が成り立つ", _lk, b"32\n")
matrix("先読み 全部外れて既定", FIB + "h : n ?\n\t(slow n) = 5 : cnt 30\n\t(slow n) = 6 : cnt 31\n\tcnt 20\nh 10\n", b"20\n")
matrix("先読み 全部外れて既定が無い(__)", FIB + "h : n ?\n\t(slow n) = 5 : cnt 30\n\t(slow n) = 6 : cnt 31\nh 10\n", b"__\n")
matrix("先読み 1 行目が成り立つ(後ろは捨てる)", FIB + "h : n ?\n\t(slow n) = 45 : cnt 30\n\t(slow n) = 6 : cnt 31\n\t(slow n) = 45 : cnt 32\n\t7\nh 10\n", b"30\n")
fl2 = matrix("先読み 外れる行の値は罠(捨てる)", FIB + "h : n ?\n\t(slow n) = 5 : ov 3\n\t(slow n) = 6 : ov 4\n\t(slow n) = 45 : cnt 31\n\t7\nh 10\n", b"31\n")
matrix("先読み 成り立つ行の値は罠(止まる)", FIB + "h : n ?\n\t(slow n) = 5 : cnt 30\n\t(slow n) = 45 : ov 3\n\t7\nh 10\n", None, trap=True)
matrix("先読み 既定の値も投機", FIB + "h : n ?\n\t(slow n) = 5 : cnt 30\n\t(slow n) = 6 : cnt 31\n\tslow 12\nh 10\n", b"132\n")
check("先読み: 罠は巻き戻った(失敗の印が立つ)", fl2 > 0, True)
sign_asm.SPEC_LOOK[0] = 1
fl = matrix("巻き戻しの試し(左が 45)", FIB + "h : n ? (slow n) = 45 | (ov n)\nh 10\n", b"45\n")
check("巻き戻しが実際に起きた(入れ物の失敗の印。順番のどれかで)", fl > 0, True)
check("投機のコードが出ている", has_spec(FIB + "h : n ? (slow n) = 45 | (ov n)\nh 10\n"), True)
check("--par-spec 無しでは投機のコードが出ない", "_sign_spec_alloc" in sign_asm.generate(sign_interp.parse_source(FIB + "h : n ? (slow n) = 45 | (ov n)\nh 10\n"), "linux", par=4), False)

matrix("右が仮引数の算術の実引数で再帰関数を呼ぶ関数(slow n)", FIB + "h : n ? (cnt 40) = 0 | (slow (n + 1))\nh 9\n", b"%d\n" % (55 - 10))
matrix("枝の値が slow n", FIB + "h : n ?\n\t(cnt 40) = 0 : slow n\n\t(slow (n - 1))\nh 10\n", b"%d\n" % (34 - 9))
check("slow を使う所に投機のコードが出ている", has_spec(FIB + "h : n ? (cnt 40) = 0 | (slow (n + 1))\nh 9\n"), True)

# 今ある --par の答えを変えない(投機が入る所と入らない所が混ざる)
matrix("--par の連なり・| の右は入れない・投機が混ざる", FIB + "g : n ? ((fib n) | 5) + ((fib (n - 1)) | 7) * 2\nh : n ? (slow n) = 45 | (cnt 9)\n(g 12) + (h 10)\n")

# (4) 『必ず終わる』の判定
def term(src):
    sign_asm.PAR[0] = 4; sign_asm.SPEC[0] = True
    p = sign_asm.Program(sign_interp.parse_source(src)); p.generate("linux", None)
    return sign_asmpar.terminating(p, p.par_elig())
t = term(FIB + "loopy : n ? loopy (n + 1)\nup : n ?\n\tn < 100 : 1 + (up (n + 1))\n\t0\nmix : n ?\n\tn > 0 : mix (n - 1)\n\tn < 0 : mix (n + 1)\n\t0\n"
         "badc : n ? cnt (fib n)\nbadm : n ? cnt (n / 0)\nmx : n ? mz (n - 1)\nmz : n ? mx (n - 1)\nbad : n ? cnt n\nok1 : n ? cnt 5\nstep2 : n ?\n\tn > 0 : step2 (n - 2)\n\t0\ngrow : n ?\n\tn > 0 : grow (n + 1)\n\t0\nfx : n m ?\n\tm > 0 : fx n (m - 1)\n\t0\n0\n")
check("終わる: 再帰しない・下がる・上がる(上限つき)", sorted(k for k in ("fib", "cnt", "slow", "ov", "up", "step2", "ok1", "fx") if k in t), ["cnt", "fib", "fx", "ok1", "ov", "slow", "step2", "up"])
check("終わると言えない: 上限無しで増える・向きが混ざる・相互再帰・変わらない", sorted(k for k in ("loopy", "mix", "mx", "mz", "grow") if k in t), [])
check("再帰する関数を『仮引数の算術』の実引数で呼ぶ関数も投機にしてよい", ("bad" in t, "badc" in t, "badm" in t), (True, False, False))
check("字面の実引数なら投機にしてよい", "ok1" in t, True)
src_unprovable = "loopy : n ?\n\tn > 0 : loopy (n + 1)\n\t0\nh : n ? (loopy n) = 3 | (loopy 4)\nh 1\n"
check("終わると言えない物だけなら投機のコードを出さない", has_spec(src_unprovable), False)

# (5) 池が尽きる・走行中の投機を捨てる・何度も繰り返す
rep = FIB + "h : n ? (slow n) = 45 | (cnt 9)\nrep : k ?\n\tk < 1 : 0\n\t(h 10) + (rep (k - 1))\nrep 30\n"
matrix("池を何度も使い回す(30 回)", rep, b"%d\n" % (45 * 30))
longr = FIB + "h : n ? n = 3 | (slow 15)\nrep : k ?\n\tk < 1 : 0\n\t(h 3) + (rep (k - 1))\nrep 20\n"
matrix("左が速く決まり、長い投機は走行中に捨てる(20 回)", longr, b"60\n")
many = FIB + "h : n ? (slow n) = 99 | (cnt 7)\nrep : k ?\n\tk < 1 : 0\n\t(h 8) + (rep (k - 1))\nrep 40\n"
matrix("40 回(池 32 個より多い)", many, b"280\n")

# (6) 組み立て
sp = FIB + "h : n ? (slow n) = 45 | (cnt 9)\nh 10\n"
try: sign_asm.generate(sign_interp.parse_source(sp), "bare", par=4, par_spec=True); r = "通った"
except sign_asm.AsmError: r = "断った"
check("--par-spec も --target=linux だけ", r, "断った")
if shutil.which("clang"):
    d = tempfile.mkdtemp(); s_ = os.path.join(d, "p.s"); open(s_, "w").write(run(sp)[2])
    rr = subprocess.run(["clang", "--target=aarch64-linux-gnu", "-c", s_, "-o", os.path.join(d, "a.o")], capture_output=True, text=True)
    check("clang で組み立てられる(--par-spec)", (rr.returncode, rr.stderr.strip()), (0, ""))
    sign_asm.SPEC_ABORT[0] = True      # 複製ありも組み立てられる(関数の終わりの見つけ損ないで同じ名前が二重にならない)
    s2 = os.path.join(d, "p2.s"); open(s2, "w").write(run(FIB + "h : n ?\n\t(slow n) = 5 : slow 22\n\t(slow 20) + (cnt 30)\nh 12\n")[2])
    rr = subprocess.run(["clang", "--target=aarch64-linux-gnu", "-c", s2, "-o", os.path.join(d, "a2.o")], capture_output=True, text=True)
    check("clang で組み立てられる(--par-spec --spec-abort)", (rr.returncode, rr.stderr.strip()), (0, ""))
    sign_asm.SPEC_ABORT[0] = ABORT_DEFAULT
    open(os.path.join(d, "q.sn"), "w").write(sp)
    rr = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), "--asm", os.path.join(d, "q.sn"), "--target=linux", "--par-spec"], capture_output=True, text=True)
    check("sign.py --asm --par-spec で出る(--par 無しは 4 本)", (rr.returncode, "_sign_spec_alloc" in rr.stdout), (0, True))
else: print("-- clang が無いので、本物のアセンブラでの確認は省く")
print("\n全部 ok" if not fails else "\n失敗 %d 件" % fails); sys.exit(1 if fails else 0)
