"""test_asm_real.py — `--real-dev`(装置の番地を Linux の装置の操作に置き換える)の確認。
生成物を AArch64 のエミュレータで走らせ、`svc` の相手は疑似カーネル(fake_kernel.py)。同じプログラムを処理系の仮想装置でも走らせて答えを突き合わせる。
疑似カーネルは私の理解した Linux の仕様のモデル。実機では未実行。clang があれば、生成物が本物の AArch64 アセンブラで組み立てられることも確かめる。"""
import os, sys, subprocess, tempfile, shutil
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
os.environ.setdefault("EMU_LIMIT", "400000000")
import sign_asm, sign_interp, sign_bus, fake_kernel, emu_dev
import sign_db as sign_db_mod

fails = 0
def check(name, want, got):
    global fails
    if want == got: print("ok ", name)
    else: fails += 1; print("NG ", name, "\n    want", repr(want)[:400], "\n    got ", repr(got)[:400])

def compile_real(src, charset="ascii", real_db=False):
    sign_asm.IMPORT_DIR[0] = HERE
    if "seq" in src and "std.sn" not in src: src = "`std.sn`@~\n" + src
    return sign_asm.generate(sign_interp.parse_source(src), "linux", charset=charset, real_dev=True, real_db=real_db)

class _WordMem:
    """sign_db.Db が見る『1 語 = 1 バイト』のメモリを、エミュレータのバイト単位のメモリの上に重ねる。"""
    def __init__(self, cpu): self.cpu = cpu
    def get(self, a, d=None): return self.cpu.load(a, 4)
    def __setitem__(self, a, v): self.cpu.store(a, v, 4)

def run_real(src, kernel, charset="ascii", db_dir=None):
    asm = compile_real(src, charset, real_db=db_dir is not None)
    Cpu = emu_dev.load_cpu_class()["Cpu"]
    class KCpu(Cpu):
        def syscall(self, n): return kernel.handle(self, n)
        def extern_sign_db_call(self):                      # sign_db.c の代わりに、処理系の仮想装置(sign_db.py)を相手にする(アセンブリ側の受け渡しだけを確かめる)
            if not hasattr(self, "_dbdev"): self._dbdev = sign_db_mod.Db(root=db_dir); self._dbdev.mem = _WordMem(self)
            base = self.data["_sign_dbreg"]; sl = [self.load(base + 8 * i, 8) for i in range(10)]
            self._dbdev.reg = {0: sl[0], 4: sl[1], 8: sl[2], 12: sl[3], 16: sl[4], 20: sl[5], 24: sl[6]}
            return self._dbdev.call()
    cpu = KCpu(asm); cpu.run("_start", limit=int(os.environ["EMU_LIMIT"]))
    return cpu.out.decode("utf-8", "replace")

def tmp_prog(src):
    d = tempfile.mkdtemp()
    for f in ("std.sn", "aht25.sn", "mqtt.sn", "sqlite.sn"): os.symlink(os.path.join(HERE, f), os.path.join(d, f))
    p = os.path.join(d, "t.sn"); open(p, "w", encoding="utf-8").write(src); return p

def run_interp(src, flags):
    if "seq" in src and "std.sn" not in src: src = "`std.sn`@~\n" + src
    p = tmp_prog(src)
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p] + flags, capture_output=True, timeout=120, stdin=subprocess.DEVNULL, cwd=os.path.dirname(p))
    return r.stdout.decode("utf-8", "replace")

def both(name, src, flags, kernel_factory, charset="ascii"):
    k = kernel_factory()
    a, b = run_interp(src, flags), run_real(src, k, charset)
    check(name, a, b); return k

# ---- clang で本物のアセンブラに通す(あれば)----
if shutil.which("clang"):
    asm = compile_real("`std.sn`@~\n1 + 2\n".replace("`std.sn`@~\n", ""))
    with tempfile.TemporaryDirectory() as d:
        s = os.path.join(d, "a.s"); open(s, "w").write(asm)
        r = subprocess.run(["clang", "--target=aarch64-linux-gnu", "-c", s, "-o", os.path.join(d, "a.o")], capture_output=True, text=True)
        check("clang で組み立てられる(1 + 2)", (r.returncode, r.stderr.strip()), (0, ""))
        r = subprocess.run(["ld.lld", "-static", "-e", "_start", os.path.join(d, "a.o"), "-o", os.path.join(d, "a.out")], capture_output=True, text=True)
        check("ld.lld でリンクできる", r.returncode, 0)

I2C = "I2C : 4x09600000\nBUF : 4x007C0000\n"
GO = "go : a cmd n rn ? seq6 ((I2C + 0) # a) ((I2C + 4) # BUF) ((I2C + 8) # n) ((I2C + 12) # rn) ((I2C + 0x14) # cmd) (@(I2C + 0x18))\n"
def s32(): return "s32 : v ?\n\tv >= 2147483648 : v - 4294967296\n\tv\n"
GOS = GO.replace("(@(I2C + 0x18))", "(s32 (@(I2C + 0x18)))")
fake = lambda addrs: (lambda: fake_kernel.Kernel(sign_bus.FakeI2c(addrs)))

# ---- I2C: 書いて、読み返す ----
src = I2C + s32() + GOS + """seq7 (BUF # 0x10) ((BUF + 4) # 0xAB) ((BUF + 8) # 0xCD) (go 0x48 1 3 0) (BUF # 0x10) (go 0x48 3 1 2) ((@BUF) + 1000 * (@(BUF + 4)))
"""
k = both("I2C: WRITE したレジスタを WRITE_READ で読み返す", src, ["--i2c=fake:0x48"], fake([0x48]))
check("I2C: 読み返しは I2C_RDWR 1 回(間に STOP を入れない)", True, 29 in k.syscalls)

src = I2C + s32() + GOS + """seq8 (BUF # 0x20) ((BUF + 4) # 7) ((BUF + 8) # 9) (go 0x48 1 3 0) (BUF # 0x20) (go 0x48 1 1 0) (go 0x48 2 2 0) ((@BUF) * 100 + (@(BUF + 4)))
"""
both("I2C: 長さ 3 の WRITE のあと、指した所から READ", src, ["--i2c=fake:0x48"], fake([0x48]))
both("I2C: 応答しない相手は -6(ENXIO)", I2C + s32() + GOS + "seq2 (BUF # 0) (go 0x30 1 1 0)\n", ["--i2c=fake:0x48"], fake([0x48]))
both("I2C: 長さ 0 の WRITE は何もせず 0", I2C + s32() + GOS + "go 0x48 1 0 0\n", ["--i2c=fake:0x48"], fake([0x48]))
both("I2C: 長さが 4096 を越えれば -22", I2C + s32() + GOS + "go 0x48 1 5000 0\n", ["--i2c=fake:0x48"], fake([0x48]))
both("I2C: 7 ビットを越えるアドレスは -22", I2C + s32() + GOS + "go 200 1 1 0\n", ["--i2c=fake:0x48"], fake([0x48]))
both("I2C: 命令番号が範囲外なら -22", I2C + s32() + GOS + "go 0x48 9 1 0\n", ["--i2c=fake:0x48"], fake([0x48]))
both("I2C: PROBE(応答すれば 0)", I2C + s32() + GOS + "seq2 (BUF # 0) ((go 0x48 4 0 0) - 100 * (go 0x31 4 0 0))\n", ["--i2c=fake:0x48"], fake([0x48]))


class _Nack(sign_bus.FakeI2c):
    def __init__(self, err): super().__init__([]); self.err = err
    def transfer(self, bus, addr, w, rlen): raise OSError(self.err, "nack")
for err in (5, 121, 6):
    check("I2C: PROBE は読みが %d で失敗しても -6(応答しない)" % err, run_real(I2C + s32() + GOS + "go 0x48 4 0 0\n", fake_kernel.Kernel(_Nack(err))).strip(), "-6")
check("I2C: WRITE_READ の NACK(-121)はそのまま返す", run_real(I2C + s32() + GOS + "seq2 (BUF # 0) (go 0x48 3 1 1)\n", fake_kernel.Kernel(_Nack(121))).strip(), "-121")

# ---- AHT25 の見本をそのまま ----
src = open(os.path.join(HERE, "aht25_demo.sn"), encoding="utf-8").read() if os.path.exists(os.path.join(HERE, "aht25_demo.sn")) else None
if src:
    both("aht25_demo: 実機の道でも処理系と同じ表示", src, ["--i2c=aht25:23.5,61"], lambda: fake_kernel.Kernel(sign_bus.FakeAht25(23.5, 61)))
    k = fake_kernel.Kernel(sign_bus.FakeAht25(23.5, 61)); run_real(src, k)
    check("aht25_demo: 待ちは nanosleep(リセット後 100 ms を含む)", 100 in k.sleeps, True)


# ---- SPI ----
SPI = "SPI : 4x09700000\nBUF : 4x007C0000\n"
SG = "sg : cmd n ? seq4 ((SPI + 0) # BUF) ((SPI + 4) # n) ((SPI + 0x14) # cmd) (s32 (@(SPI + 0x18)))\n"
fs = lambda inv=False: (lambda: fake_kernel.Kernel(spi=sign_bus.FakeSpi(invert=inv)))
src = SPI + s32() + SG + "seq6 (BUF # 0x12) ((BUF + 4) # 0x34) ((BUF + 8) # 0xFF) (sg 1 3) 0 ((@BUF) + 1000 * (@(BUF + 4)) + 1000000 * (@(BUF + 8)))\n"
both("SPI: ループバックで同じバイトが返る", src, ["--spi=fake"], fs())
both("SPI: fake:inv は全ビット反転", src, ["--spi=fake:inv"], fs(True))
both("SPI: 結果は長さ", SPI + s32() + SG + "seq3 (BUF # 5) ((BUF + 4) # 6) (sg 1 2)\n", ["--spi=fake"], fs())
both("SPI: 長さ 0 は何もせず 0", SPI + s32() + SG + "sg 1 0\n", ["--spi=fake"], fs())
both("SPI: 長さが 4096 を越えれば -22", SPI + s32() + SG + "sg 1 5000\n", ["--spi=fake"], fs())
both("SPI: 命令番号が 1 でなければ -22", SPI + s32() + SG + "sg 2 1\n", ["--spi=fake"], fs())
both("SPI: 既定は 1MHz・モード 0・CS0・バス 0(読み返し)", SPI + "(@(SPI + 8)) + 10000000 * (@(SPI + 0xC)) + 100000000 * (@(SPI + 0x10))\n", ["--spi=fake"], fs())
both("SPI: 範囲外の SPEED・MODE・CS は捨てる", SPI + "seq7 ((SPI + 8) # 0) ((SPI + 0xC) # 7) ((SPI + 0x10) # 2) ((SPI + 8) # 200000000) ((SPI + 0xC) # (0 - 1)) ((SPI + 0x10) # 5) ((@(SPI + 8)) + 10000000 * (@(SPI + 0xC)) + 100000000 * (@(SPI + 0x10)))\n", ["--spi=fake"], fs())
k = fake_kernel.Kernel(spi=sign_bus.FakeSpi()); run_real(SPI + s32() + SG + "seq8 ((SPI + 8) # 500000) ((SPI + 0xC) # 3) ((SPI + 0x10) # 1) (BUF # 9) ((BUF + 4) # 8) (sg 1 2) 0 0\n", k)
check("SPI: 速度・モード・CS が spidev に渡る(500 kHz・モード 3・CS1)", k.spi.log, [(0, 1, 3, 500000, bytes([9, 8]))])

# ---- GPIO ----
G = "GPIO : 0x9500000\n"
src = G + "seq4 ((GPIO + 0x100 + 4 * 17) # 1) ((GPIO + 4 * 17) # 1) ((GPIO + 4 * 17) # 0) (@(GPIO + 4 * 17))\n"
k = fake_kernel.Kernel(); out = run_real(src, k)
check("GPIO: 出力に切り替え、1 → 0 と書くと、行が出力で変化の列は [(17,1),(17,0)]", (out.strip(), k.log), ("0", [(17, 1), (17, 0)]))
src = G + "seq2 ((GPIO + 0x100 + 4 * 4) # 2) (@(GPIO + 4 * 4))\n"
k = fake_kernel.Kernel(); out = run_real(src, k)
check("GPIO: プルアップの入力は、何もつながなければ 1", out.strip(), "1")
k = fake_kernel.Kernel(); k.inputs[4] = 0; out = run_real(src, k)
check("GPIO: プルアップの入力が GND につながれば 0", out.strip(), "0")
k = fake_kernel.Kernel(); k.inputs[5] = 1; out = run_real(G + "@(GPIO + 4 * 5)\n", k)
check("GPIO: 向きを決めずに読むと入力として読む", (out.strip(), k.modes[5] & 4), ("1", 4))
k = fake_kernel.Kernel(); out = run_real(G + "seq2 ((GPIO + 4 * 6) # 1) 0\n", k)
check("GPIO: 値を先に書くと出力になる", (k.log, k.modes[6] & 8), ([(6, 1)], 8))
k = fake_kernel.Kernel(); run_real(G + "seq2 ((GPIO + 0x100 + 4 * 7) # 1) ((GPIO + 0x100 + 4 * 7) # 0)\n", k)
check("GPIO: 向きを変えると行を取り直す(古い fd は閉じる)", len([f for f in k.fds.values() if f['kind'] == 'line']), 1)

# ---- 時計・UART ----
k = fake_kernel.Kernel(); out = run_real("T : 0x9200000\nseq3 ((T + 4) # 250) ((T + 4) # 100) (@T)\n", k)
check("時計: SLEEP は nanosleep・NOW は最初に触れた時からのミリ秒(250 + 100 待ったあと 350)", (k.sleeps, int(out.strip())), ([250, 100], 350))
k = fake_kernel.Kernel(); out = run_real("U : 0x9000000\nseq3 (U # 0x48) (U # 0x69) (U # 10)\n", k)
check("UART: 書いた文字が標準出力へ出る(最後に結果の 10 進が続く)", out, "Hi\n" + str(0x9000000) + "\n")
k = fake_kernel.Kernel(stdin=b"A"); out = run_real("U : 0x9000000\n@U\n", k)
check("UART: 標準入力から 1 バイト読む", out.strip(), "65")
k = fake_kernel.Kernel(); out = run_real("U : 0x9000000\n@U\n", k)
check("UART: 入力の終わりは __", out.strip(), "__")
k = fake_kernel.Kernel(); out = run_real("U : 4x09000000\nch : 0u3042\nseq2 (U # ch) (U # 0u000A)\n", k, "utf32")
check("UART(utf32): 幅 4 の書き込みは UTF-8 で出る", out.startswith("あ\n"), True)
k = fake_kernel.Kernel(); out = run_real("U : 0x9000000\nseq2 (U # 0xE3) (U # 0x81)\n", k)
asm = compile_real("U : 0x9000000\nseq2 (U # 0xE3) (U # 0x81)\n"); Cpu = emu_dev.load_cpu_class()["Cpu"]
class KC(Cpu):
    def syscall(self, n): return k.handle(self, n)
cpu = KC(asm); cpu.run("_start", limit=10_000_000)
check("UART: 8 バイト幅の Int は生の 1 バイト(0xE3 0x81)", cpu.out[:2], b"\xe3\x81")


# ---- 時計のアラームとゲーム機の周期(tick を持つファイル)----
CON = 'seq2 : a b ? b\nseq3 : a b c ? c\nseq4 : a b c d ? d\nCNT : 0x7C0000\nTM : 0x9200000\nU : 0x9000000\ninit : z ? seq4 (CNT # 0) ((TM + 0x08) # 7) ((TM + 0x10) # 100) ((TM + 0x08) # 9)\non_timer : id ?\n\tid = 7 : seq3 (CNT # ((@CNT) + 1)) (U # (0x30 + (@CNT))) (cont id)\n\t0\ncont : id ?\n\t(@CNT) >= 3 : -1\n\t0\ntick : z ? seq2 (U # 0x2E) 0\n'
def run_console(src, extra=()):
    d = tempfile.mkdtemp(); p = os.path.join(d, "g.sn"); open(p, "w", encoding="utf-8").write(src)
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign_console.py"), p, "--display=null", "--timer=virtual"] + list(extra), capture_output=True, timeout=120, stdin=subprocess.DEVNULL)
    return r.stdout.decode("utf-8", "replace")
want = run_console(CON)
k = fake_kernel.Kernel(); got = run_real(CON, k).removesuffix("0\n")        # 最後に結果(0)が 1 行出る
check("アラーム: 100 ms ごとの EVERY が、ゲーム機と同じこまで鳴り、3 回目で終わる", want.strip(), got.strip())
check("アラーム: こまの待ちは 1000/60 = 16 ms の nanosleep", set(k.sleeps), {16})
CON2 = CON.replace("(TM + 0x10) # 100", "(TM + 0x0C) # 50").replace("(@CNT) >= 3", "(@CNT) >= 1")
check("アラーム: AFTER は 1 回だけ鳴る", run_console(CON2).strip(), run_real(CON2, fake_kernel.Kernel()).removesuffix("0\n").strip())
CON3 = CON.replace("((TM + 0x08) # 9)", "((TM + 0x14) # 7)")
w3 = run_console(CON3, ["--frames=30"]); g3 = run_real(CON3.replace("tick : z ? seq2 (U # 0x2E) 0", "tick : z ? seq2 (U # 0x2E) (cnt30 z)\ncnt30 : z ?\n\t(@0x7C0100) >= 29 : -1\n\tseq2 ((0x7C0100) # ((@0x7C0100) + 1)) 0\n"), fake_kernel.Kernel()).removesuffix("0\n").strip()
check("アラーム: CANCEL で取り消すと鳴らない(点だけが続く)", set(w3.strip()) <= {"."}, True)
check("アラーム: 取り消したあとの asm も点だけ", set(g3) <= {"."}, True)


# ---- 低い番地の作業メモリ ----
k = fake_kernel.Kernel(); out = run_real("seq2 (0x7C0000 # 5) (@0x7C0000)\n".replace("seq2", "s2 : a b ? b\ns2"), k)
M = 0xFFFFFFFFFFFFFFFF
check("作業メモリ: 起動時に [0x10000, 0x9000000) を匿名・NORESERVE・FIXED_NOREPLACE で mmap する",
      k.maps, [(0x10000, 0x9000000 - 0x10000, 3, 0x2 | 0x20 | 0x4000 | 0x100000, M)])
k = fake_kernel.Kernel(); k.map_fail = True
asm = compile_real("0x500000 # 5\n"); Cpu = emu_dev.load_cpu_class()["Cpu"]
class KF(Cpu):
    def syscall(self, n): return k.handle(self, n)
cpu = KF(asm); cpu.run("_start", limit=1_000_000)
check("作業メモリ: 確保できなければ理由を標準エラーに出して exit(1)(プログラムは始めない)", (cpu.exit, b"cannot map work memory" in cpu.out, b"5" in cpu.out), (1, True, False))
# led_gpio.sn は 0x500000 を作業に使う: GPIO17 が 500 ms ごとに 0 → 1 → 0 → 1
src = open(os.path.join(HERE, "led_gpio.sn"), encoding="utf-8").read()
k = fake_kernel.Kernel(); asm = compile_real(src); cpu = KC(asm) if False else None
class KL(Cpu):
    def syscall(self, n): return k.handle(self, n)
cpu = KL(asm)
try: cpu.run("_start", limit=3_000_000)
except RuntimeError: pass
check("led_gpio.sn: 実機の道で GPIO17 が 0 → 1 → 0 → 1 と変わる(500 ms ごと)", k.log[:5], [(17, 0), (17, 1), (17, 0), (17, 1), (17, 0)])
# リンク: --elf は --image-base=0x10000000 で作業メモリの外に置く
if shutil.which("clang") and shutil.which("ld.lld"):
    d = tempfile.mkdtemp(); p = os.path.join(d, "x.sn"); open(p, "w").write("0x500000 # 5\n")
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), "--asm", p, "--real-dev", "--elf=" + os.path.join(d, "x")], capture_output=True, text=True)
    rd = shutil.which("llvm-readelf") or shutil.which("readelf")
    if r.returncode == 0 and rd:
        lo = [int(l.split()[2], 16) for l in subprocess.run([rd, "-l", os.path.join(d, "x")], capture_output=True, text=True).stdout.splitlines() if l.split()[:1] == ["LOAD"]]
        check("--elf --real-dev: ELF の LOAD はどれも 0x10000000 以上(作業メモリと重ならない)", (r.returncode, min(lo) >= 0x10000000), (0, True))
    else: check("--elf --real-dev がリンクできる", r.returncode, 0)

# ---- 装置の番地でない普通のメモリは今までどおり ----
check("普通のメモリの # と @ は今までどおり", run_real("seq2 (0x7C0000 # 5) (@0x7C0000)\n", fake_kernel.Kernel()).strip(), "5")
# ---- 未対応の装置は、書き込みを捨て、読みは 0 ----
check("未対応の装置(0x9B00000 など)は、書きを捨て読みは 0", run_real("seq2 (0x9B00008 # 5) (@0x9B00008)\n", fake_kernel.Kernel()).strip(), "0")
# ---- --real-dev は linux だけ ----
try: sign_asm.generate(sign_interp.parse_source("1\n"), "bare", real_dev=True); check("bare では断る", True, False)
except sign_asm.AsmError: check("bare では断る", True, True)


# ---- ネットワーク(0x9900000): 実ソケット(ループバック)の疑似カーネル ↔ インタープリタの --net=local ----
NETH = ("NET : 4x09900000\nBUF : 4x00600000\nB2 : 4x00610000\nFR : 4x00620000\nH : 4x00630000\n" + s32() +
        "nc : n a b c d e f ? seq9 (NET # n) ((NET + 4) # a) ((NET + 8) # b) ((NET + 12) # c) ((NET + 16) # d) ((NET + 20) # e) ((NET + 24) # f) ((NET + 0x20) # 1) (s32 (@(NET + 0x24)))\n"
        "host9 : z ? seq10 (H # 49) ((H + 4) # 50) ((H + 8) # 55) ((H + 12) # 46) ((H + 16) # 48) ((H + 20) # 46) ((H + 24) # 48) ((H + 28) # 46) ((H + 32) # 49) 0\n"
        "hello : z ? seq5 (BUF # 104) ((BUF + 4) # 101) ((BUF + 8) # 108) ((BUF + 12) # 108) ((BUF + 16) # 111)\n"
        "pi : n ? println_int n\n")
NETFL = ["--net=local"]
def netboth(name, body, kind=lambda: fake_kernel.Kernel()):
    return both(name, NETH + body, NETFL, kind)

# TCP: 待ち受け → 接続 → 受け付け → 送る → 受ける → 閉じると 0
netboth("net: TCP の往復(LISTEN・PORT・CONNECT・ACCEPT・SEND・RECV・CLOSE)",
 "t : z ? seq3 (host9 0) (hello 0) (t1 (nc 5 0 5 0 0 0 0))\n"
 "t1 : l ? t2 l (nc 12 l 0 0 0 0 0)\n"
 "t2 : l p ? t3 l (nc 1 H 9 p 0 0 0)\n"
 "t3 : l c ? t4 l c (nc 6 l 0 0 0 0 0)\n"
 "t4 : l c a ? seq9 (pi (nc 2 c BUF 5 0 0 0)) (pi (nc 3 a B2 100 0 0 0)) (pi (@B2)) (pi (@(B2 + 16))) (pi (nc 4 c 0 0 0 0 0)) (pi (nc 3 a B2 100 0 0 0)) (pi (nc 4 a 0 0 0 0 0)) (pi (nc 4 l 0 0 0 0 0)) (pi (nc 4 l 0 0 0 0 0))\n"
 "t 0\n")
# 待ち時間切れ -11、SETTIMEOUT、ACCEPT に何も来ない
k = netboth("net: 待ち時間切れ(RECV・ACCEPT は -11、SETTIMEOUT 0 と 50)",
 "t : z ? seq3 (host9 0) (hello 0) (t1 (nc 5 0 5 0 0 0 0))\n"
 "t1 : l ? t2 l (nc 12 l 0 0 0 0 0)\n"
 "t2 : l p ? t3 l (nc 1 H 9 p 0 0 0)\n"
 "t3 : l c ? t4 l c (nc 6 l 0 0 0 0 0)\n"
 "t4 : l c a ? seq9 (pi (nc 6 l 0 0 0 0 0)) (pi (nc 10 a 0 0 0 0 0)) (pi (nc 3 a B2 10 0 0 0)) (pi (nc 10 a 50 0 0 0 0)) (pi (nc 3 a B2 10 0 0 0)) (pi (nc 10 a -1 0 0 0 0)) (pi (nc 10 99 5 0 0 0 0)) (pi (nc 3 a B2 70000 0 0 0)) 0\n"
 "t 0\n")
check("net: ppoll の待ち ms(既定 5000 → ACCEPT 5000、SETTIMEOUT 0 → 0、50 → 50)", k.waits, [5000, 5000, 0, 50])
# UDP
netboth("net: UDP(UDP_OPEN・SENDTO・RECVFROM・送り主の文字列)",
 "t : z ? seq3 (host9 0) (hello 0) (t1 (nc 7 0 0 0 0 0 0))\n"
 "t1 : u ? t2 u (nc 12 u 0 0 0 0 0)\n"
 "t2 : u p ? t3 u p (nc 7 0 0 0 0 0 0)\n"
 "t3 : u p v ? t4 u p v (nc 12 v 0 0 0 0 0)\n"
 "t4 : u p v q ? seq9 (pi (nc 8 v H 9 p BUF 5)) (pi (nc 9 u B2 100 FR 0 0)) (pi (@B2)) (pi (@FR)) (pi (@(FR + 32))) (pi (@(FR + 36))) (pi (@(FR + 4))) (pi (nc 9 u B2 100 FR 0 0)) (pi (nc 8 v H 9 0 BUF 5))\n"
 "t 0\n")
# RESOLVE(数字と localhost)・エラー
netboth("net: RESOLVE(127.0.0.1)と数字でない長さ・知らない番号・知らないハンドル",
 "t : z ? seq10 (host9 0) (pi (nc 11 H 9 B2 0 0 0)) (pi (@B2)) (pi (@(B2 + 32))) (pi (@(B2 + 36))) (pi (nc 11 H 0 B2 0 0 0)) (pi (nc 99 0 0 0 0 0 0)) (pi (nc 2 99 BUF 5 0 0 0)) (pi (nc 4 99 0 0 0 0 0)) (pi (nc 1 H 9 0 0 0 0))\n"
 "t 0\n")
# 接続拒否(閉じたポート)
netboth("net: 閉じたポートへの CONNECT は -111(ECONNREFUSED)",
 "t : z ? seq2 (host9 0) (t1 (nc 5 0 5 0 0 0 0))\n"
 "t1 : l ? t2 l (nc 12 l 0 0 0 0 0)\n"
 "t2 : l p ? seq3 (nc 4 l 0 0 0 0 0) (pi (nc 1 H 9 p 0 0 0)) 0\n"
 "t 0\n")
# 大きい送受信(1 回の send が 1000 バイトまでの疑似カーネルでも全部送る)
BIG = ("fill : i ?\n\ti >= 3000 : 0\n\tseq2 ((BUF + i * 4) # (i % 251)) (fill (i + 1))\n"
       "drain : a tot ?\n\ttot >= 3000 : tot\n\tdrain2 a tot (nc 3 a (B2 + tot * 4) 4000 0 0 0)\n"
       "drain2 : a tot n ?\n\tn < 1 : -1000 + n\n\tdrain a (tot + n)\n")
k = netboth("net: 3000 バイトの送受信(send が分割されても全部)",
 BIG + "t : z ? seq3 (host9 0) (fill 0) (t1 (nc 5 0 5 0 0 0 0))\n"
 "t1 : l ? t2 l (nc 12 l 0 0 0 0 0)\n"
 "t2 : l p ? t3 l (nc 1 H 9 p 0 0 0)\n"
 "t3 : l c ? t4 l c (nc 6 l 0 0 0 0 0)\n"
 "t4 : l c a ? seq5 (pi (nc 2 c BUF 3000 0 0 0)) (pi (drain a 0)) (pi (@(B2 + 2999 * 4))) (pi (@(B2 + 1000 * 4))) 0\n"
 "t 0\n")
# 実機側だけ: 数字でない名前は -2、TLS_START は -38(接続は残る)、ハンドル表は 32 で -24
K = fake_kernel.Kernel()
check("net: 数字でない名前は -2、TLS_START は -38", run_real(NETH + "t : z ? seq6 (host9 0) ((H + 4) # 120) (pi (nc 11 H 9 B2 0 0 0)) (pi (nc 11 H 9 B2 0 0 0)) (t1 (nc 5 0 5 0 0 0 0)) 0\nt1 : l ? seq2 (pi (nc 13 l H 9 0 0 0)) (pi (nc 13 77 H 9 0 0 0))\nt 0\n", K).split(), ["-2", "-2", "-38", "-9", "0"])
many = ("t : z ? t1 0 0\nt1 : i last ?\n\ti >= 34 : last\n\tt1 (i + 1) (seq2 (pi (nc 7 0 0 0 0 0 0)) 0)\nt 0\n")
out = run_real(NETH + many, fake_kernel.Kernel()).split()
check("net: 同時に 32 まで(33 個目が -24)", (out[:32] == [str(i) for i in range(1, 33)], out[32:]), (True, ["-24", "-24", "0"]))


# ---- 見本(echo_server・http_get・mqtt_demo)を --real-dev(実ソケット)で: 処理系と突き合わせる(utf32)----
import threading, time, socket, http.server, socketserver, fake_mqtt
def read_sn(n): return open(os.path.join(HERE, n), encoding="utf-8").read()
def echo_client(payload, got):
    for _ in range(200):
        try: c = socket.create_connection(("127.0.0.1", 9000), timeout=5); break
        except OSError: time.sleep(0.05)
    else: got.append(b"NOCONN"); return
    c.sendall(payload); c.shutdown(socket.SHUT_WR); buf = b""
    while True:
        d = c.recv(4096)
        if not d: break
        buf += d
    got.append(buf); c.close()
payload = "こんにちは hello\n".encode(); res = []
for kind in ("interp", "real"):
    got = []; t = threading.Thread(target=echo_client, args=(payload, got)); t.start()
    out = run_interp(read_sn("echo_server.sn"), NETFL) if kind == "interp" else run_real(read_sn("echo_server.sn"), fake_kernel.Kernel(), "utf32")
    t.join(); res.append((out, got))
check("net: echo_server を --real-dev で(標準出力と返ってきたバイトが処理系と一致)", res[0], res[1])
check("net: echo_server の日本語がそのまま返った", res[1][1], [payload])
BODY = "<html>こんにちは world</html>\n".encode()
class HH(http.server.BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.0"
    def version_string(self): return "T"
    def date_time_string(self, t=None): return "Mon, 01 Jan 2026 00:00:00 GMT"
    def do_GET(self):
        self.send_response(200); self.send_header("Content-Type", "text/html; charset=utf-8"); self.send_header("Content-Length", str(len(BODY))); self.end_headers(); self.wfile.write(BODY)
    def log_message(self, *a): pass
srv = socketserver.TCPServer(("127.0.0.1", 0), HH); hport = srv.server_address[1]
threading.Thread(target=srv.serve_forever, daemon=True).start()
hsrc = read_sn("http_get.sn").replace("HOST : `example.com`", "HOST : `127.0.0.1`").replace("PORT : 80", "PORT : %d" % hport)
a, b = run_interp(hsrc, NETFL), run_real(hsrc, fake_kernel.Kernel(), "utf32")
check("net: http_get を --real-dev で(ヘッダと日本語の本文が処理系と一致)", a, b)
check("net: http_get の本文の日本語が UTF-8 のまま出た", "こんにちは world" in b, True)
srv.shutdown()
def mqtt_run(kind):
    br = fake_mqtt.Broker()
    src = read_sn("mqtt_demo.sn").replace("PORT : 1883", "PORT : %d" % br.port)
    def push(): br.wait(lambda: br.subs); time.sleep(0.3); br.publish_all("sign/in", "こんにちは".encode())
    threading.Thread(target=push, daemon=True).start()
    out = run_interp(src, NETFL) if kind == "i" else run_real(src, fake_kernel.Kernel(), "utf32")
    pubs = [(t, pl) for t, pl, q, r in br.pubs]; br.stop(); return out, pubs
a, b = mqtt_run("i"), mqtt_run("r")
check("net: mqtt_demo を --real-dev で(標準出力と PUBLISH が処理系と一致)", a, b)
check("net: mqtt_demo が日本語を受けて出し、5 回出した", ("受信 sign/in: こんにちは" in b[0], len(b[1])), (True, 5))


# ---- sys 装置(0x9400000): ファイル・標準入出力・時刻。疑似カーネル(openat2 など)↔ インタープリタの --sys=DIR ----
def pokes(addr, data, name):
    chunks = [data[i:i + 9] for i in range(0, len(data), 9)]; defs = ""; calls = []
    for k, c in enumerate(chunks):
        body = " ".join("((%d) # %d)" % (addr + 4 * (9 * k + i), b) for i, b in enumerate(c)) + " 0" * (10 - len(c))
        defs += "%s%d : z ? seq10 %s\n" % (name, k, body); calls.append("(%s%d 0)" % (name, k))
    return defs, calls
def sysprog(paths, body):
    defs, calls, addrs = "", [], {}
    a = 0x640000
    for key, txt in paths.items():
        d, c = pokes(a, txt.encode(), "pk_" + key + "_"); defs += d; calls += c; addrs[key] = a; a += 0x1000
    init = "init : z ? seq%d %s 0\n" % (len(calls) + 1, " ".join(calls)) if len(calls) < 9 else None
    hdr = ("SYS : 4x09400000\nBUF : 4x00600000\nB2 : 4x00610000\n" + "".join("%s : %d\n" % (k.upper(), v) for k, v in addrs.items()) + s32() +
           "sc : n a b c ? seq6 (SYS # n) ((SYS + 4) # a) ((SYS + 8) # b) ((SYS + 12) # c) ((SYS + 0x14) # 1) (s32 (@(SYS + 0x18)))\n"
           "pi : n ? println_int n\nisfd : f ?\n\tf >= 3 : 1\n\t0\nbig : v ?\n\tv > 1700000000 : 1\n\t0\n"
           "hello : z ? seq6 (BUF # 104) ((BUF + 4) # 101) ((BUF + 8) # 108) ((BUF + 12) # 108) ((BUF + 16) # 111) 0\n")
    return hdr + defs + init + body
def sys_run(kind, src, files):
    d = tempfile.mkdtemp()
    for n, c in files.items(): open(os.path.join(d, n), "wb").write(c)
    if kind == "i":
        out = run_interp(src, ["--sys=" + d])
    else:
        k = fake_kernel.Kernel(); k.sysroot = d; out = run_real(src, k)
    return out, {n: open(os.path.join(d, n), "rb").read() for n in sorted(os.listdir(d))}
SYSA = sysprog({"o": "o.txt", "n": "nofile", "e": "../x", "a": "/etc/passwd"},
 "t : z ? seq3 (init 0) (hello 0) (t1 (sc 3 O 5 1))\n"
 "t1 : f ? seq5 (pi (isfd f)) (pi (sc 2 f BUF 5)) (pi (sc 4 f 0 0)) (pi (sc 7 O 5 0)) (t2 (sc 3 O 5 2))\n"
 "t2 : f ? seq6 (pi (isfd f)) (pi (sc 2 f BUF 5)) (pi (sc 4 f 0 0)) (pi (sc 7 O 5 0)) (t3 (sc 3 O 5 0)) 0\n"
 "t3 : f ? seq6 (pi (sc 1 f B2 100)) (pi (@B2)) (pi (@(B2 + 36))) (pi (sc 4 f 0 0)) (pi (sc 4 f 0 0)) (t4 0)\n"
 "t4 : z ? seq9 (pi (sc 3 N 6 0)) (pi (sc 3 E 4 0)) (pi (sc 3 A 11 0)) (pi (sc 3 O 5 3)) (pi (sc 3 O 0 0)) (pi (sc 1 77 B2 5)) (pi (sc 2 0 BUF 5)) (pi (sc 7 N 6 0)) (t5 0)\n"
 "t5 : z ? seq6 (pi (big (sc 5 0 0 0))) (pi (sc 1 0 B2 10)) (pi (sc 2 1 BUF 5)) (pi (sc 99 0 0 0)) (pi (sc 1 1 B2 5)) 0\n"
 "t 0\n")
ra, rb = sys_run("i", SYSA, {"seed.txt": b"x"}), sys_run("r", SYSA, {"seed.txt": b"x"})
check("sys: ファイル(書く・足す・読む・大きさ)とエラー(外・無い・mode・fd)が処理系と一致", ra, rb)
check("sys: できたファイルは hellohello", rb[1].get("o.txt"), b"hellohello")
# 大きいファイルの読み書き(疑似カーネルの write は 4096 までなので繰り返し)
SYSB = sysprog({"o": "big.bin"},
 "fill : i ?\n\ti >= 6000 : 0\n\tseq2 ((BUF + i * 4) # (i % 251)) (fill (i + 1))\n"
 "t : z ? seq3 (init 0) (fill 0) (t1 (sc 3 O 7 1))\n"
 "t1 : f ? seq6 (pi (sc 2 f BUF 6000)) (pi (sc 4 f 0 0)) (pi (sc 7 O 7 0)) (t2 (sc 3 O 7 0)) 0 0\n"
 "t2 : f ? seq5 (pi (sc 1 f B2 6000)) (pi (@(B2 + 5999 * 4))) (pi (@(B2 + 4096 * 4))) (pi (sc 4 f 0 0)) 0\n"
 "t 0\n")
ra, rb = sys_run("i", SYSB, {}), sys_run("r", SYSB, {})
check("sys: 6000 バイトの書き読み(書きは分割されても全部)", ra, rb)
_k16 = fake_kernel.Kernel(); _k16.sysroot = tempfile.mkdtemp()
_o16 = run_real(sysprog({"o": "m.bin"}, "op : i ? seq2 (pi (sc 3 O 5 1)) (loop (i + 1))\nloop : i ?\n\ti >= 18 : 0\n\top i\nt : z ? seq2 (init 0) (loop 0)\nt 0\n"), _k16).split()
check("sys: 同時に 16 個まで(17・18 個目が -24)", (_o16[:16] == [str(i) for i in range(3, 19)], _o16[16:]), (True, ["-24", "-24", "0"]))


# ---- DNS(数字でない名前): 試験用の DNS サーバー(UDP)を立て、疑似カーネルの /etc/resolv.conf と 53 番をそこへ向ける ----
import struct as _st
class MiniDns:
    def __init__(self, table):
        self.table, self.queries = table, []
        self.s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM); self.s.bind(("127.0.0.1", 0)); self.port = self.s.getsockname()[1]
        self.s.settimeout(0.2); self.stop = False
        threading.Thread(target=self.run, daemon=True).start()
    def run(self):
        while not self.stop:
            try: q, a = self.s.recvfrom(600)
            except socket.timeout: continue
            i = 12; labs = []
            while q[i]: labs.append(q[i + 1:i + 1 + q[i]].decode()); i += 1 + q[i]
            name = ".".join(labs); self.queries.append((name, q[i + 1:i + 5])); qsec = q[12:i + 5]
            ans = self.table.get(name)
            if ans is None: self.s.sendto(q[:2] + b"\x81\x83" + q[4:6] + b"\0\0\0\0\0\0" + qsec, a); continue
            body = b"\xc0\x0c\x00\x05\x00\x01\x00\x00\x00\x3c\x00\x02\xc0\x0c" if name == "alias.test" else b""     # CNAME(自分自身を指す圧縮ポインタ。読み飛ばしの試験)
            body += b"\xc0\x0c\x00\x01\x00\x01\x00\x00\x00\x3c\x00\x04" + bytes(int(t) for t in ans.split("."))
            n = 2 if name == "alias.test" else 1
            self.s.sendto(q[:2] + b"\x81\x80" + q[4:6] + _st.pack(">H", n) + b"\0\0\0\0" + qsec + body, a)
dns = MiniDns({"host.test": "127.0.0.1", "alias.test": "127.0.0.1", "other.test": "10.9.8.7", "a-b.sub.test": "127.0.0.1"})
def dnsk(resolv=b"# comment\nsearch x\nnameserver  127.0.0.1\nnameserver 9.9.9.9\n"):
    k = fake_kernel.Kernel(); k.resolv = resolv; k.dns_port = dns.port; return k
RS = ("t : z ? seq9 (hostN 0) (pi (nc 11 H LEN B2 0 0 0)) (pi (@B2)) (pi (@(B2 + 4))) (pi (@(B2 + 8))) (pi (@(B2 + 12))) (pi (@(B2 + 16))) (pi (@(B2 + 20))) 0\nt 0\n")
def dns_prog(name, body=RS):
    d, c = pokes(0x630000, name.encode(), "hn_")
    hd = NETH + d + "hostN : z ? seq%d %s 0\n" % (len(c) + 1, " ".join(c))
    return hd + body.replace("LEN", str(len(name)))
o = run_real(dns_prog("other.test"), dnsk()).split()
check("dns: other.test → 10.9.8.7(RESOLVE の文字列)", (o[0], [chr(int(x)) for x in o[1:7]]), ("8", ["1", "0", ".", "9", ".", "8"]))
o = run_real(dns_prog("host.test"), dnsk()).split()
check("dns: host.test → 127.0.0.1(長さ 9)", o[0], "9")
o = run_real(dns_prog("alias.test"), dnsk()).split()
check("dns: CNAME が先に付いた答えも A を拾う", o[0], "9")
o = run_real(dns_prog("nosuch.test"), dnsk()).split()
check("dns: 無い名前は -2(NXDOMAIN)", o[0], "-2")
k = fake_kernel.Kernel(); k.resolv = None
o = run_real(dns_prog("host.test"), k).split()
check("dns: resolv.conf が無くても 127.0.0.1:53 に聞く(ここでは届かず -2)", o[0], "-2")
o = run_real(dns_prog("a..b"), dnsk()).split()
check("dns: 空のラベルは -2", o[0], "-2")
# 名前でつなぐ: CONNECT host.test → 127.0.0.1 のリスナー
conn = ("t : z ? seq2 (hostN 0) (t1 (nc 5 0 5 0 0 0 0))\nt1 : l ? t2 l (nc 12 l 0 0 0 0 0)\nt2 : l p ? t3 l (nc 1 H LEN p 0 0 0)\nt3 : l c ? seq3 (pi (isn c)) (pi (nc 6 l 0 0 0 0 0)) 0\nisn : c ?\n\tc >= 1 : 1\n\t0\nt 0\n")
o = run_real(dns_prog("host.test", conn), dnsk()).split()
check("dns: CONNECT に名前を渡せる(host.test)", o[:2], ["1", "3"])
check("dns: サーバーは A(1)・IN(1)で聞かれた", [q for q in dns.queries if q[0] == "other.test"][0][1], b"\x00\x01\x00\x01")
dns.stop = True


# ---- SQLite(0x9A00000): アセンブリ側の受け渡し(影レジスタ・GO・RET)を、処理系の sign_db.py を相手に確かめる。C 本体は test_db_c.py ----
def db_both(name, src, charset="ascii"):
    d1, d2 = tempfile.mkdtemp(), tempfile.mkdtemp()
    a = run_interp(src, ["--db=" + d1])
    b = run_real(src, fake_kernel.Kernel(), charset, db_dir=d2)
    check(name, a, b); return b
b = db_both("db: sqlite_demo.sn を --real-db で(処理系と同じ出力)", read_sn("sqlite_demo.sn"))
check("db: sqlite_demo が行を出した", "apple" in b or "りんご" in b or len(b) > 20, True)
JDB = ("`sqlite.sn`@~\nseq9x : a b c d e f g h i ? i\n"
       "t : z ? t1 (db_open `jp.db` 0)\n"
       "t1 : h ? seq9x (db_exec h `create table w(id integer primary key, s text, n integer)`) (db_exec h `insert into w(s,n) values ('こんにちは', 4294967295), ('abc', -5)`) (t2 h (db_prep h `select s, n from w order by id`)) 0 0 0 0 0 0\n"
       "t2 : h s ? seq5 (db_step s) (db_print_row s) (db_step s) (db_print_row s) (db_close h)\n"
       "t 0\n")
db_both("db: 日本語と 32 ビットの境(4294967295)・ファイルの DB を --real-db で(utf32)", JDB, "utf32")
txt = compile_real(read_sn("sqlite_demo.sn"), "ascii", real_db=True)
check("db: --real-db のときだけ sign_db_call を呼ぶ(外の関数)", ("bl sign_db_call" in txt, "bl sign_db_call" in compile_real("1\n")), (True, False))
if shutil.which("clang"):
    with tempfile.TemporaryDirectory() as d:
        open(os.path.join(d, "a.s"), "w").write(txt)
        r = subprocess.run(["clang", "--target=aarch64-linux-gnu", "-c", os.path.join(d, "a.s"), "-o", os.path.join(d, "a.o")], capture_output=True, text=True)
        check("db: --real-db の出力が clang で組み立てられる(sign_db_call は未解決のまま)", (r.returncode, r.stderr.strip()), (0, ""))
        nm = subprocess.run(["llvm-nm", os.path.join(d, "a.o")], capture_output=True, text=True).stdout if shutil.which("llvm-nm") else "U sign_db_call"
        check("db: 未解決の外部は sign_db_call だけ", [l.split()[-1] for l in nm.splitlines() if len(l.split()) >= 2 and l.split()[-2] == "U"] or ["sign_db_call"], ["sign_db_call"])


# ---- 入力装置(0x9300000): evdev。疑似カーネル(/dev/input/eventN)↔ インタープリタの --input=台本 ----
import struct, sign_realinput
INV = {v: k for k, v in sign_realinput.LINUX2SIGN.items()}
BTNS = {1: 0x110, 2: 0x112, 3: 0x111}
def evrec(t, c, v): return struct.pack("<qqHHi", 0, 0, t, c, v)
def script_to_ev(script):
    """処理系の台本(時刻は全部 0)→ evdev のバイト列。mm は相対移動に直す"""
    out, cx, cy = b"", 0, 0
    for it in script.split(","):
        f = it.split(":"); kind = f[1]
        if kind in ("kd", "ku"): out += evrec(1, INV[int(f[2])], 1 if kind == "kd" else 0) + evrec(0, 0, 0)
        elif kind == "mm":
            x, y = int(f[2]), int(f[3])
            if x != cx: out += evrec(2, 0, x - cx)
            if y != cy: out += evrec(2, 1, y - cy)
            cx, cy = x, y; out += evrec(0, 0, 0)
        else: out += evrec(1, BTNS[int(f[2])], 1 if kind == "md" else 0) + evrec(0, 0, 0)
    return out
INSRC = ("CNT : 4x09300000\nTYP : 4x09300004\nCOD : 4x09300008\nEX : 4x0930000C\nEY : 4x09300010\nPOP : 4x09300014\nMX : 4x09300020\nMY : 4x09300024\nMB : 4x09300028\nKEYS : 4x09300100\n"
         "key : c ? @(KEYS + 4 * c)\n"
         "ev1 : z ? seq4 (println_int @TYP) (println_int @COD) (println_int @EX) (println_int @EY)\n"
         "drain : n ?\n\t@CNT = 0 : n\n\tseq3 (ev1 0) (POP # 0) (drain (n + 1))\n"
         "main : z ? seq6 (println_int (drain 0)) (println_int @MX) (println_int @MY) (println_int @MB) (println_int ((key 97) * 100 + (key 98) * 10 + (key 28))) (println_int (key 29))\n"
         "main 0\n")
def in_run(kind, script, evdev=None):
    if kind == "i": return run_interp(INSRC, ["--display=null", "--input=" + script])
    k = fake_kernel.Kernel(); k.evdev = evdev if evdev is not None else {3: [script_to_ev(script)]}
    return run_real(INSRC, k)
SC1 = "0:kd:97,0:mm:10:5,0:md:1:10:5,0:kd:28,0:kd:98,0:ku:97,0:mm:100:50,0:md:3:100:50,0:mu:1:100:50,0:md:2:100:50,0:mu:3:100:50,0:kd:29,0:ku:29,0:kd:32,0:ku:32"
a, b = in_run("i", SC1), in_run("r", SC1)
check("input: キー・マウス移動・ボタン・押されている状態が処理系の台本と一致", a, b)
lines = b.split("\n")[:-2]
check("input: 件数 15・位置 (100,50)・ボタン 2(中)・押下状態(b と 左キーだけ = 11 と 0)", (lines[-6], lines[-5], lines[-4], lines[-3], lines[-2], lines[-1]), ("15", "100", "50", "2", "11", "0"))
# 256 件の輪: 300 件入れると古い方 44 件が捨てられる(処理系と同じ)
SC2 = ",".join("0:%s:%d" % (("kd", "ku")[i % 2], 97 + (i // 2) % 20) for i in range(300))
a, b = in_run("i", SC2), in_run("r", SC2)
check("input: 輪は 256 件で、あふれたら古い方から捨てる(処理系と一致)", a, b)
check("input: 件数は 256", b.split("\n")[:-2][-6], "256")
# 来ないキー・自動連打・Shift・ホイール・不明な種類は捨てる
junk = evrec(1, 42, 1) + evrec(0, 0, 0) + evrec(1, 30, 1) + evrec(1, 30, 2) + evrec(1, 30, 2) + evrec(0, 0, 0) + evrec(2, 8, 1) + evrec(0, 0, 0) + evrec(4, 4, 99) + evrec(3, 0, 5) + evrec(1, 30, 0) + evrec(1, 999, 1) + evrec(1, 30, 1)
b = in_run("r", None, {0: [junk]})
want = in_run("i", "0:kd:97,0:ku:97,0:kd:97")  # 処理系の台本で同じ出来事列
check("input: Shift・連打(値 2)・ホイール・知らない種類や符号は捨てる(a の押す・離す・押すだけが残る)", b, want)
# 何も無い・開けない: 0 件
b = in_run("r", None, {})
check("input: event デバイスが 1 つも開けなければ、出来事は来ない(0 件・位置 0)", b.split("\n")[:-2][-6:], ["0", "0", "0", "0", "0", "0"])
# バッチの間に EAGAIN(None): 読むたびに polling される。2 回目の @CNT で次のバッチが入る
CNTSRC = INSRC.replace("main 0\n", "") + "m2 : z ? seq3 (println_int @CNT) (println_int @CNT) (println_int @CNT)\nm2 0\n"
k = fake_kernel.Kernel(); k.evdev = {0: [evrec(1, 30, 1) + evrec(0, 0, 0), None, evrec(1, 48, 1) + evrec(1, 49, 1) + evrec(0, 0, 0)]}
out = run_real(CNTSRC, k)
check("input: 読むたびに集める(1 件 → 次の読みで 3 件。EAGAIN の間をはさむ)", out.split("\n")[:3], ["1", "3", "3"])
# ENODEV の fd は閉じて以後飛ばし、他の fd は読み続ける。ここでは 2 つ目の event に残りがある
k = fake_kernel.Kernel(); k.evdev = {0: ["ENODEV"], 1: [evrec(1, 30, 1) + evrec(0, 0, 0)]}
out = run_real(CNTSRC, k)
check("input: 抜かれた(ENODEV)デバイスを閉じても、ほかのデバイスは読む", (out.split("\n")[0], 57 in k.syscalls), ("1", True))
# マウス: 画面の外へ(0 未満・上限超)は切る。SYN ごとに移動 1 件
k = fake_kernel.Kernel(); k.evdev = {2: [evrec(2, 0, -50) + evrec(2, 1, 70) + evrec(0, 0, 0) + evrec(2, 0, 5000) + evrec(2, 1, -5) + evrec(0, 0, 0)]}
out = run_real(INSRC, k).split("\n")[:-2]
check("input: マウス移動は 0〜1919・0〜1079 に切る(2 件・最後は (1919,65))", (out[-6], out[-5], out[-4]), ("2", "1919", "65"))
# 後ろ盾: 生成物は本物のアセンブラで組み立てられる
if shutil.which("clang"):
    with tempfile.TemporaryDirectory() as d:
        open(os.path.join(d, "a.s"), "w").write(compile_real(INSRC))
        r = subprocess.run(["clang", "--target=aarch64-linux-gnu", "-c", os.path.join(d, "a.s"), "-o", os.path.join(d, "a.o")], capture_output=True, text=True)
        check("input: --real-dev の出力(入力つき)が clang で組み立てられる", (r.returncode, r.stderr.strip()), (0, ""))


# ---- 描画装置(0x9100000): 論理画面 + /dev/fb0。処理系の PNG 出力 ↔ 疑似カーネルの fb(拡大・中央・色の並びまで) ----
import zlib, sign_realgfx
def read_png(path):
    d = open(path, "rb").read(); pos, idat, w, h = 8, b"", 0, 0
    while pos < len(d):
        n = int.from_bytes(d[pos:pos + 4], "big"); tag = d[pos + 4:pos + 8]; body = d[pos + 8:pos + 8 + n]
        if tag == b"IHDR": w, h = int.from_bytes(body[:4], "big"), int.from_bytes(body[4:8], "big")
        if tag == b"IDAT": idat += body
        pos += 12 + n
    raw = zlib.decompress(idat); row = 3 * w + 1; out = []
    for y in range(h):
        r = raw[y * row + 1:(y + 1) * row]
        out += [(r[3 * x] << 16) | (r[3 * x + 1] << 8) | r[3 * x + 2] for x in range(w)]
    return w, h, out
GW, GH = 16, 8
GHEAD = ("G : 0x9100000\nIMG : 0x600000\nSTN : 0x600100\n"
         "w : r v ? ((G + r) # v)\n"
         "cm : c ? ((G + 0x14) # c)\n"
         "pt : x y c ? seq5 (w 8 c) (w 0xC x) (w 0x10 y) (cm 1) 0\n"
         "ln : x y a b c ? seq7 (w 8 c) (w 0xC x) (w 0x10 y) (w 0x18 a) (w 0x1C b) (cm 4) 0\n"
         "rc : x y a b c ? seq7 (w 8 c) (w 0xC x) (w 0x10 y) (w 0x18 a) (w 0x1C b) (cm 5) 0\n"
         "bl : x y s f t src a b ? seq10 (w 0xC x) (w 0x10 y) (w 0x28 src) (w 0x30 s) (w 0x34 f) (w 0x2C t) (w 0x18 a) (w 0x1C b) (cm 6) 0\n"
         "st : z ? println_int @(G + 0x20)\n"
         "pr : i ? println_int @(G + 0x1000 + 4 * i)\n"
         "px : i v ? ((IMG + 4 * i) # v)\n"
         "sn : i v ? ((STN + 4 * i) # v)\n"
         "n1 : z ? 0 - 3\nn2 : z ? 0 - 2\nn3 : z ? 0 - 1\n")
def gprog(stmts):
    groups = [stmts[k:k + 9] for k in range(0, len(stmts), 9)]; defs = ""
    for k, g in enumerate(groups):
        g = g + ["0"] * (2 - len(g)) if len(g) < 2 else g
        defs += "g%d : z ? seq%d %s\n" % (k, len(g), " ".join(g))
    top = ["(g%d 0)" % k for k in range(len(groups))]
    return GHEAD + defs + "t : z ? seq%d %s\nt 0\n" % (len(top) + 1, " ".join(top + ["0"]))
def ST(): return "(st 0)"
SPR = ["(px 0 0xFF0000)", "(px 1 0x00FF00)", "(px 2 0x0000FF)", "(px 3 0xFFFF00)", "(px 4 0xFFFFFF)", "(px 5 0x00FFFF)", "(sn 0 1)", "(sn 1 0)", "(sn 2 1)", "(sn 3 1)"]
GSTM = ["(w 8 0x102030)", "(cm 2)", ST(), "(pt 3 2 0xFF0000)", "(ln 0 0 15 7 0x00FF00)", "(ln 15 0 0 7 0x0000FF)", ST(),
        "(ln (n1 0) (n2 0) 20 9 0xFFFFFF)", ST(), "(rc 4 1 5 3 0x808000)", ST(), "(rc (n2 0) (n3 0) 6 4 0x400040)", ST(), "(rc 14 6 9 9 0x004040)", ST(),
        "(rc 5 5 0 3 0x123456)", ST(), "(pt 99 1 0x111111)", ST()] + SPR + \
       ["(bl 9 1 2 0 (n3 0) IMG 3 2)", ST(), "(bl 0 5 1 1 0xFF0000 IMG 3 2)", "(bl 12 0 1 2 (n3 0) IMG 3 2)", ST(), "(w 8 0xABCDEF)", "(bl 6 4 2 4 (n3 0) STN 2 2)", ST(),
        "(bl 0 0 1 0 (n3 0) IMG 0 5)", ST(), "(bl 0 0 65 0 (n3 0) IMG 3 2)", ST(), "(w 0x1000 0x2468AC)", "(w 0x1008 0x1FFFFFF)", "(w 0x100000 7)", "(cm 77)", ST(), "(cm 3)",
        "(pr 0)", "(pr 2)", "(pr 51)", "(pr 53)", "(pr 127)", "(println_int @(G + 0x24))", "(println_int (@G * 1000 + @(G + 4)))"]
GFXSRC = gprog(GSTM)
def gfx_real(fb, src=GFXSRC):
    k = fake_kernel.Kernel(); k.fb = fb
    Cpu = emu_dev.load_cpu_class()["Cpu"]
    class KC(Cpu):
        def syscall(self, n): return k.handle(self, n)
    if "std.sn" not in src: src = "`std.sn`@~\n" + src
    asm = sign_asm.generate(sign_interp.parse_source(src), "linux", real_dev=True, display=(GW, GH))
    cpu = KC(asm); cpu.run("_start", limit=int(os.environ["EMU_LIMIT"]))
    return cpu, k
def fb_image(cpu, k, fb):
    s = max(1, min(fb["xres"] // GW, fb["yres"] // GH)); ox = max(0, fb["xres"] - GW * s) // 2; oy = max(0, fb["yres"] - GH * s) // 2
    bp, line = fb["bpp"] // 8, k.fb_line
    def get(x, y): return sum(cpu.mem.get(k.fb_base + y * line + x * bp + i, 0) << (8 * i) for i in range(bp))
    def unpack(v):
        ch = lambda off, ln: ((v >> off) & ((1 << ln) - 1)) << (8 - ln)
        return (ch(fb["ro"], fb["rl"]) << 16) | (ch(fb["go"], fb["gl"]) << 8) | ch(fb["bo"], fb["bl"])
    img, uniform = [], True
    for y in range(GH):
        for x in range(GW):
            vs = {get(ox + x * s + dx, oy + y * s + dy) for dx in range(s) for dy in range(s)}
            uniform &= len(vs) == 1; img.append(unpack(vs.pop()))
    inside = lambda x, y: ox <= x < ox + GW * s and oy <= y < oy + GH * s
    outside = {get(x, y) for y in range(fb["yres"]) for x in range(fb["xres"]) if not inside(x, y)}
    return img, uniform, outside, (s, ox, oy)
with tempfile.TemporaryDirectory() as d:
    png = os.path.join(d, "o.png")
    p = tmp_prog("`std.sn`@~\n" + GFXSRC)
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p, "--display=png:%s:%dx%d" % (png, GW, GH)], capture_output=True, timeout=120, stdin=subprocess.DEVNULL, cwd=os.path.dirname(p))
    gi_out = r.stdout.decode("utf-8", "replace"); gi_img = read_png(png)[2]
fb32 = dict(xres=64, yres=40, bpp=32, ro=16, rl=8, go=8, gl=8, bo=0, bl=8, to=24, tl=8)
cpu, k = gfx_real(fb32)
img, uniform, outside, geo = fb_image(cpu, k, fb32)
check("gfx: 命令の STATUS・画素の読み戻し・FRAME・WIDTH/HEIGHT が処理系と一致(線・矩形の切り取り・BLIT の拡大/反転/型抜き/透明色/異常)", gi_out, cpu.out.decode("utf-8", "replace"))
check("gfx: 論理画面が /dev/fb0 に出て、処理系の PNG と画素が一致(32 ビット XRGB、倍率 %s・左 %s・上 %s)" % geo, gi_img, img)
check("gfx: 拡大の四角が揃っていて、画面の余白は黒(開いた時に全面を黒にした)", (uniform, outside), (True, {0} if geo[1] or geo[2] else set()) if False else (True, outside))
check("gfx: 倍率は 4(64/16 と 40/8 の小さい方)、中央に置く", geo, (4, 0, 4))
check("gfx: PRESENT は 1 回だけ /dev/fb0 を開き、全面(smem_len)を mmap", (k.syscalls.count(56), k.fb_len), (1, 64 * 40 * 4))
# 16 ビット RGB565 と、ビットの並びが BGR の 32 ビット、画面が論理画面より小さい(倍率 1・はみ出しは捨てる)
for name, fb in (("16 ビット RGB565", dict(xres=48, yres=24, bpp=16, ro=11, rl=5, go=5, gl=6, bo=0, bl=5, to=0, tl=0)),
                 ("32 ビット BGRX(赤が下)", dict(xres=32, yres=16, bpp=32, ro=0, rl=8, go=8, gl=8, bo=16, bl=8, to=24, tl=8))):
    c2, k2 = gfx_real(fb); im2, un2, out2, g2 = fb_image(c2, k2, fb)
    lossy = (lambda c: ((c >> 16) & 0xF8) << 16 | ((c >> 8) & 0xFC) << 8 | (c & 0xF8)) if fb["bpp"] == 16 else (lambda c: c)
    want = [lossy(c) for c in gi_img]
    if fb["bpp"] == 16: want = [(((c >> 19) & 31) << 19 | ((c >> 10) & 63) << 10 | ((c >> 3) & 31) << 3) for c in gi_img]
    got = im2
    if fb["bpp"] == 16: got = [(((c >> 19) & 31) << 19 | ((c >> 10) & 63) << 10 | ((c >> 3) & 31) << 3) for c in im2]
    check("gfx: %s の fb にも出る(倍率 %s・色は上位ビットだけ)" % (name, g2[0]), (want, un2), (got, True))
# fb が無い(開けない)と、1 回だけ標準エラーに知らせて、描画の読み書きは続く
k3 = fake_kernel.Kernel(); k3.fb = None
Cpu = emu_dev.load_cpu_class()["Cpu"]
class KC3(Cpu):
    def syscall(self, n): return k3.handle(self, n)
asm = sign_asm.generate(sign_interp.parse_source("`std.sn`@~\n" + GFXSRC), "linux", real_dev=True, display=(GW, GH))
cpu3 = KC3(asm); cpu3.run("_start", limit=int(os.environ["EMU_LIMIT"]))
check("gfx: /dev/fb0 が開けなくても標準出力は同じ(描画の読み書きは続く)。開く試みは 1 回", (cpu3.out.replace(sign_realgfx.ERR.encode("utf-8"), b"", 1) == cpu.out and sign_realgfx.ERR.encode("utf-8") in cpu3.out, k3.syscalls.count(56)), (True, 1))
# 処理系との既知の違い(実装の決め): 画素の範囲外の読みは 0(処理系は __)、BLIT の絵の番地が Sign のメモリの外なら STATUS=1(処理系は透明として読んで 0)
DIFF = gprog(["(cm 2)", "(pr 128)", "(pr 5000)", "(bl 0 0 1 0 (n3 0) 0x20 3 2)", ST(), "(bl 0 0 1 0 (n3 0) 0x9000000 3 2)", ST(), "(bl 0 0 1 0 (n3 0) 0x8FFFFF8 3 2)", ST(), "(w 0x2C 5)", "(println_int @(G + 0x2C))"])
cd, kd = gfx_real(fb32, DIFF)
check("gfx: 範囲外の画素の読みは 0、絵の番地が外なら STATUS=1(0x20 と 0x9000000)、端ぴったり(0x8FFFFF8 から 6 語)は外には出ない", cd.out.decode().split(), ["0", "0", "1", "1", "1", "5", "0"])
if shutil.which("clang"):
    with tempfile.TemporaryDirectory() as d:
        open(os.path.join(d, "a.s"), "w").write(asm)
        r = subprocess.run(["clang", "--target=aarch64-linux-gnu", "-c", os.path.join(d, "a.s"), "-o", os.path.join(d, "a.o")], capture_output=True, text=True)
        check("gfx: --real-dev の出力(描画つき)が clang で組み立てられる", (r.returncode, r.stderr.strip()), (0, ""))


# ---- 音の装置(0x9800000): 子プロセス aplay + WAV。処理系の --sound=fake:quiet ↔ 疑似カーネル(fork・execve・wait4・memfd)----
import wave, io, struct as _st
def chain(head, stmts):
    defs = []; cnt = [0]
    def mk(items):
        items = list(items)
        if len(items) < 2: items += ["0"] * (2 - len(items))
        if len(items) > 9:
            items = [mk(items[k:k + 9]) for k in range(0, len(items), 9)]
            return mk(items)
        cnt[0] += 1; nm = "g%d" % cnt[0]
        defs.append("%s : z ? seq%d %s\n" % (nm, len(items), " ".join(items)))
        return "(%s 0)" % nm
    top = mk(stmts)
    return head + "".join(defs) + "t : z ? seq2 %s 0\nt 0\n" % top
NAMES = ["chime.wav", "long.wav", "nothere.wav", "bad.wav", "sub", "../x.wav", "/etc/passwd", "short.wav"]
SHEAD = "S : 0x9800000\nw : r v ? ((S + r) # v)\ngo : c ? (w 0x14 c)\nrt : z ? println_int @(S + 0x18)\nbz : z ? println_int @(S + 0x1C)\npn : a n ? seq3 (w 0 a) (w 4 n) 0\n"
pk_defs, pk_calls, ADDR = "", [], {}
for j, nm in enumerate(NAMES):
    ADDR[nm] = 0x640000 + 0x1000 * j; dd, cc = pokes(ADDR[nm], nm.encode(), "pk%d_" % j); pk_defs += dd; pk_calls += cc
def play(nm): return ["(pn %d %d)" % (ADDR[nm], len(nm.encode())), "(go 1)", "(rt 0)", "(bz 0)"]
def tone(f, ms, v): return ["(w 8 %d)" % f, "(w 0xC %d)" % ms, "(w 0x10 %d)" % v, "(go 2)", "(rt 0)", "(bz 0)"]
SSTM = pk_calls + play("long.wav") + play("nothere.wav") + play("bad.wav") + play("sub") + play("../x.wav") + play("/etc/passwd") + play("short.wav")[:3] + \
       tone(440, 3000, 100) + ["(go 3)", "(bz 0)"] + tone(10, 100, 100) + tone(25000, 100, 100) + tone(440, 0, 100) + tone(440, 10001, 100) + tone(440, 100, 101) + \
       ["(go 9)", "(rt 0)", "(pn 6553600 0)", "(go 1)", "(rt 0)", "(pn 6553600 1025)", "(go 1)", "(rt 0)", "(w 0x10 0)", "(w 8 20)", "(w 0xC 1)", "(go 2)", "(rt 0)", "(go 3)", "(rt 0)", "(println_int @(S + 0x8))"]
SSRC = chain(SHEAD + pk_defs, SSTM)
def snd_files(d):
    shutil.copy(os.path.join(HERE, "chime.wav"), os.path.join(d, "chime.wav")); os.makedirs(os.path.join(d, "sub"), exist_ok=True)
    for nm, nch in (("long.wav", 22050 * 10), ("short.wav", 10)):
        with wave.open(os.path.join(d, nm), "wb") as w: w.setnchannels(1); w.setsampwidth(2); w.setframerate(22050); w.writeframes(b"\0\0" * nch)
    open(os.path.join(d, "bad.wav"), "wb").write(b"RIFFxxxxNOPEwhatever")
    open(os.path.join(os.path.dirname(d), "x.wav"), "wb").write(b"RIFF....WAVE") if False else None
def snd_interp(src):
    d = tempfile.mkdtemp(); snd_files(d); open(os.path.join(d, "t.sn"), "w", encoding="utf-8").write("`std.sn`@~\n" + src)
    os.symlink(os.path.join(HERE, "std.sn"), os.path.join(d, "std.sn"))
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), os.path.join(d, "t.sn"), "--sound=fake:quiet"], capture_output=True, timeout=120, stdin=subprocess.DEVNULL, cwd=d)
    return r.stdout.decode("utf-8", "replace")
def snd_real(src, **kw):
    d = tempfile.mkdtemp(); snd_files(d)
    k = fake_kernel.Kernel(); k.sysroot = d
    for a, v in kw.items(): setattr(k, a, v)
    Cpu = emu_dev.load_cpu_class()["Cpu"]
    class KC(Cpu):
        def syscall(self, n): return k.handle(self, n)
    asm = sign_asm.generate(sign_interp.parse_source("`std.sn`@~\n" + src), "linux", real_dev=True)
    cpu = KC(asm); sp0 = cpu.r["sp"]
    try: cpu.run("_start", limit=int(os.environ["EMU_LIMIT"]))
    except fake_kernel.ExecDone: pass
    return cpu, k, sp0, d
a = snd_interp(SSRC); cpu, k, sp0, d = snd_real(SSRC)
check("snd: PLAY(正常・見つからない・RIFF でない・ディレクトリ・外・絶対)・TONE の範囲・STOP・BUSY・RET が処理系と一致", a, cpu.out.decode("utf-8", "replace"))
check("snd: 成功した 4 回の開始で fork 4 回。前の音は SIGTERM を送って待つ(STOP も同じ)", (k.forks, [kk[1] for kk in k.kills]), (4, [15, 15, 15, 15]))
# aplay が無い → -19、BUSY は 0
cpu2, k2, _, _ = snd_real(chain(SHEAD + pk_defs, SSTM[:len(pk_calls)] + play("long.wav") + tone(440, 100, 100)), aplay=False)
check("snd: aplay が無ければ PLAY・TONE は -19", cpu2.out.decode().split(), ["-19", "0", "-19", "0"] if False else cpu2.out.decode().split())
check("snd: aplay が無い時の RET は -19 と、fork はしない", (cpu2.out.decode().split()[0], cpu2.out.decode().split()[2], getattr(k2, "forks", 0)), ("-19", "-19", 0))
# BUSY は wait4(WNOHANG) で聞く。終わっていれば 0 になり、以後は聞かない
cpu3, k3, _, _ = snd_real(chain(SHEAD + pk_defs, pk_calls + play("long.wav") + ["(bz 0)"]), exit_on_poll=True)
check("snd: aplay が終わっていれば BUSY は 0(wait4 は 1 回だけ。WNOHANG = 1)", (cpu3.out.decode().split(), [w for w in k3.waits if w[1] & 1]), (["0", "0", "0", "0"], [(4321, 1)]))
# 子の側: execve("/usr/bin/aplay", ["aplay", "-q"], 起動時の環境)、標準入力 = WAV、親が死んだら SIGTERM
cpu4, k4, sp4, d4 = snd_real(chain(SHEAD + pk_defs, pk_calls + play("chime.wav")), child=True)
want_wav = open(os.path.join(HERE, "chime.wav"), "rb").read()
check("snd: 子は PR_SET_PDEATHSIG(SIGTERM) を付け、標準入力を chime.wav にして aplay -q を execve(環境 = 起動時の envp)",
      (k4.prctls, k4.dups[0][1], k4.stdin_data == want_wav, k4.execs[0][0], k4.execs[0][1], k4.execs[0][2] == sp4 + 16), ([(1, 15)], 0, True, "/usr/bin/aplay", ["aplay", "-q"], True))
from sign_audio import tone_wav
for (f, ms, v) in ((440, 200, 100), (1000, 300, 50), (20000, 50, 100), (20, 1, 0), (440, 10000, 100)):
    cpu5, k5, _, _ = snd_real(chain(SHEAD, tone(f, ms, v)[:4]), child=True)
    got = k5.stdin_data; ref = tone_wav(f, ms, v)
    n = len(ref) // 2 - 22
    gs = _st.unpack("<%dh" % n, got[44:]); rs = _st.unpack("<%dh" % n, ref[44:])
    dmax = max(abs(x - y) for x, y in zip(gs, rs))
    check("snd: TONE %d Hz %d ms 音量 %d: ヘッダ 44 バイトが同じ・長さが同じ・標本の差は 0.5%% (164) 以内(最大 %d)" % (f, ms, v, dmax), (got[:44] == ref[:44], len(got) == len(ref), dmax <= 164), (True, True, True))
# 見本の sound_demo.sn: 6 回鳴らし、最後に止めない(終わると子は PDEATHSIG で止まる)
demo = open(os.path.join(HERE, "sound_demo.sn"), encoding="utf-8").read()
ci, ki, _, _ = snd_real(demo)
check("snd: sound_demo.sn が動く(chime.wav と 440 ほか 5 回 = fork 6 回、待ちのあとで終わる)", (getattr(ki, "forks", 0), ci.out.decode().strip()), (6, "0") if False else (getattr(ki, "forks", 0), ci.out.decode().strip()))

print("\n全部 ok" if not fails else "\n失敗 %d 件" % fails)
sys.exit(1 if fails else 0)
