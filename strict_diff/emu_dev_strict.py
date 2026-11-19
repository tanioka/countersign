"""emu_dev.py — test_asm.py のエミュレータ(Cpu)に、処理系と同じ仮想装置(sign_bus・sign_sys・sign_db・sign_gfx のタイマー)をつなぐ。
asm 版が装置の番地へ出す読み書きを、処理系が使うのと同じ Python の装置オブジェクトへ渡して、標準出力を処理系と突き合わせるための道具。
実機の代わりではない(装置はソフトの模擬)。UART(0x9000000)は書いた 1 バイトを標準出力へ、読みは与えた入力の次の 1 バイト(終わりは __)。"""
import os, sys, re, tempfile, subprocess
HERE = "/mnt/user-data/outputs"
sys.path.insert(0, HERE)
NICHE = 0x8000000000000000
M64 = (1 << 64) - 1
UART = 0x9000000


def load_cpu_class():
    src = open(os.path.join(HERE, "test_asm.py"), encoding="utf-8").read()
    head = src[:src.index("# ---------------- 処理系の答え")]
    ns = {"__file__": os.path.join(HERE, "test_asm.py"), "__name__": "emu"}
    exec(compile(head, "emu", "exec"), ns)
    return ns


class EmuMem:
    """装置が見るメモリ: 1 語 = 4 バイトのセル(sign_sys.py の約束)。書かれていないセルは None。"""
    def __init__(self, cpu): self.cpu = cpu
    def get(self, a, default=None):
        m = self.cpu.mem
        if not any((a + i) in m for i in range(4)): return default
        return self.cpu.load(a, 4)
    def __setitem__(self, a, v): self.cpu.store(a, v & 0xFFFFFFFF, 4)
    def __getitem__(self, a):
        v = self.get(a)
        if v is None: raise KeyError(a)
        return v


def make_devices(specs, workdir):
    """(timer を display と組にするため、display を先に探す)"""
    """specs: ["i2c=fake:0x48", "spi=fake", "sys", "db", "timer"] — 処理系の --i2c=… などと同じ意味。"""
    import sign_bus, sign_sys, sign_db, sign_gfx, sign_audio
    devs = []
    for sp in specs:
        k, _, v = sp.partition("=")
        if k == "i2c": devs.append(sign_bus.I2c(v or None))
        elif k == "spi": devs.append(sign_bus.Spi(v or None))
        elif k == "sys": devs.append(sign_sys.Sys(v or workdir))
        elif k == "db": devs.append(sign_db.Db(v or workdir))
        elif k == "timer": devs.append(sign_gfx.Timer(next((d for d in devs if isinstance(d, sign_gfx.Display)), None), True))
        elif k == "rtimer": devs.append(sign_gfx.Timer(next((d for d in devs if isinstance(d, sign_gfx.Display)), None), False))      # 実時間(処理系は装置があれば自動で付ける)
        elif k == "gpio": import sign_gpio; devs.append(sign_gpio.Gpio(v or None))
        elif k == "display": devs.append(sign_gfx.parse_spec(v))          # png:出力.png:幅x高さ(終わりに finish で書く)
        elif k == "net": import sign_net; devs.append(sign_net.Net(v or None))        # --net=local など(実際のソケット)
        elif k == "sound": devs.append(sign_audio.Sound(v or None))
        elif k == "input":                                  # --input=台本(タイマーが先に要る)
            tm = next(d for d in devs if isinstance(d, sign_gfx.Timer))
            devs.append(sign_gfx.Input(tm, v))
        else: raise ValueError(sp)
    return devs


def flags_for(specs, workdir):
    out = []
    for sp in specs:
        k, _, v = sp.partition("=")
        if k == "sys": out.append("--sys=" + (v or workdir))
        elif k == "db": out.append("--db=" + (v or workdir))
        elif k == "timer": out.append("--timer=virtual")
        elif k == "rtimer": pass
        elif k == "input": out.append("--input=" + v)
        else: out.append("--" + sp)
    return out


def run_emulated(asm, specs, stdin=b"", workdir=None):
    utf32 = "charset=utf32" in specs                   # utf32: UART へ書いた符号位置を UTF-8 にして出す(IO 境界は UTF-8)
    specs = [x for x in specs if not x.startswith("charset=")]
    ns = load_cpu_class()
    Cpu = ns["Cpu"]
    devs = make_devices(specs, workdir)
    inbuf = list(stdin)

    class DevCpu(Cpu):
        def _dev(self, a):
            for d in devs:
                if d.base <= a < d.base + d.size: return d
            return None
        def store(self, a, v, n=8):
            if a == UART:
                if utf32 and n == 4 and 0x80 <= v <= 0x10FFFF and not 0xD800 <= v <= 0xDFFF: self.out += chr(v).encode("utf-8")      # 4 byte = Char(符号位置)。8 byte の Int は下位 1 byte
                else: self.out += bytes([v & 0xFF])
                return
            d = self._dev(a)
            if d is not None:
                x = v if n < 8 or v < (1 << 63) else v - (1 << 64)
                d.write(a - d.base, x); return
            super().store(a, v, n)
        def load(self, a, n=8):
            if a == UART: return inbuf.pop(0) if inbuf else NICHE
            d = self._dev(a)
            if d is not None:
                x = d.read(a - d.base)
                if not isinstance(x, int) or isinstance(x, bool): return NICHE
                return x & M64 if n == 8 else x & ((1 << (8 * n)) - 1)
            return super().load(a, n)

    cpu = DevCpu(asm)
    for d in devs:                                      # 描画装置の timer 参照: 処理系は Timer(disp, …) と組にする
        pass
    em = EmuMem(cpu)
    for d in devs: d.mem = em
    import io
    notes = []                                       # 装置が自分で標準出力へ書いた分(sys の WRITE fd 1)。(そのときの cpu.out の長さ, 文字)
    class Buf:
        def write(self, b): notes.append((len(cpu.out), b.decode("utf-8", "replace"))); return len(b)
        def flush(self): pass
    class Tee(io.StringIO):
        buffer = Buf()
        def write(self, t): notes.append((len(cpu.out), t)); return len(t)
    old = sys.stdout; sys.stdout = Tee()
    try: cpu.run("_start", limit=int(os.environ.get("EMU_LIMIT", 2_000_000)))
    finally: sys.stdout = old
    for d in devs:
        if hasattr(d, "finish"):
            try: d.finish()
            except Exception: pass
    for d in devs:
        for m in ("release", "close"):
            if hasattr(d, m):
                try: getattr(d, m)()
                except Exception: pass
                break
    out = cpu.out
    for pos, t in reversed(notes): out = out[:pos] + t.encode() + out[pos:]
    return out.decode("utf-8", "replace")


def run_interp(prog, specs, stdin=b"", workdir=None):
    r = subprocess.run([sys.executable, "/tmp/strictmods/sign_strict.py", prog] + flags_for(specs, workdir), input=stdin, capture_output=True, timeout=120, cwd=workdir)
    return r.stdout.decode("utf-8", "replace")


def png_digest(d):
    import hashlib
    out = []
    for n in sorted(os.listdir(d)):
        if n.endswith(".png"): out.append("%s:%s" % (n, hashlib.sha1(open(os.path.join(d, n), "rb").read()).hexdigest()[:12]))
    return out


def compare(prog, specs, stdin=b""):
    """(処理系の標準出力, asm 版+エミュレータの標準出力)。作業フォルダは別々に作る(sys・db が作るファイルが混ざらないように)。"""
    import sign_asm, sign_interp
    path = prog if os.path.isabs(prog) else os.path.join(HERE, prog)
    d1, d2 = tempfile.mkdtemp(), tempfile.mkdtemp()
    want = run_interp(path, specs, stdin, d1)
    asm = sign_asm.generate(sign_asm.strict_rewrite(sign_interp.parse_source(open(path, encoding="utf-8").read()))[0], "linux", charset="utf32" if "charset=utf32" in specs else "ascii")
    old = os.getcwd(); os.chdir(d2)
    try: got = run_emulated(asm, specs, stdin, d2)
    finally: os.chdir(old)
    return want + "".join("\n[%s]" % x for x in png_digest(d1)), got + "".join("\n[%s]" % x for x in png_digest(d2))
