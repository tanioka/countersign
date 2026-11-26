"""make_expected.py — 17-27 をジャンパでつないだ状態を疑似カーネルで模して、各プログラムの期待を expected.json に書く。"""
import json, os, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE); sys.path.insert(0, ROOT)
import sign_asm, sign_interp, sign_bus, fake_kernel, emu_dev
sign_asm.IMPORT_DIR[0] = ROOT
class Jumper(fake_kernel.Kernel):
    """17 と 27 をつないだ線: 入力の電圧は、相手が出力ならその値。両方入力なら、プルの向きが勝つ(27 のプル)。"""
    def handle(self, cpu, n):
        for a, b in ((17, 27), (27, 17)):
            if self.modes.get(b, 0) & 8: self.inputs[a] = self.levels.get(b, 0)
        if not (self.modes.get(17, 0) & 8 or self.modes.get(27, 0) & 8):
            f = self.modes.get(27, 0); v = 1 if f & 0x100 else 0
            self.inputs[17] = self.inputs[27] = v
        return super().handle(cpu, n)
out = {}
for f in sorted(os.listdir(os.path.join(HERE, "src"))):
    name = f[:-3]
    src = open(os.path.join(HERE, "src", f), encoding="utf-8").read()
    k = Jumper(i2c=sign_bus.FakeI2c([]), spi=sign_bus.FakeSpi()); k.sysroot = tempfile.mkdtemp()
    Cpu = emu_dev.load_cpu_class()["Cpu"]
    class KC(Cpu):
        def syscall(self, n): return k.handle(self, n)
    cpu = KC(sign_asm.generate(sign_interp.parse_source(src), "linux", real_dev=True)); cpu.run("_start", limit=400000000)
    out[name] = {"stdout": cpu.out.decode(), "exit": cpu.exit}
json.dump(out, open(os.path.join(HERE, "expected.json"), "w"), ensure_ascii=False, indent=1)
for n, v in out.items(): print(n, repr(v["stdout"]))
