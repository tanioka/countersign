#!/usr/bin/env python3
"""I2C・SPI 装置(sign_bus.py)の試験。本物のバスは使わず fake バックエンドで確かめる。python test_bus.py"""
import os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import sign_bus as B

bad = 0
def check(name, got, want):
    global bad
    ok = got == want; bad += not ok
    print(("ok  " if ok else "NG  ") + name + ("" if ok else f"\n    得た: {got!r}\n    期待: {want!r}"))

BUF = 0x600000
def i2c(addrs=(0x48,)):
    be = B.FakeI2c(addrs); d = B.I2c(backend=be); d.mem = {}; return d, be
def setbuf(d, data, buf=BUF):
    for i, b in enumerate(data): d.mem[buf + 4 * i] = b
def getbuf(d, n, buf=BUF): return [d.mem.get(buf + 4 * i) for i in range(n)]
def i2c_do(d, cmd, addr=0x48, buf=BUF, n=0, rn=0, bus=None):
    d.write(d.ADDR, addr); d.write(d.BUF, buf); d.write(d.LEN, n); d.write(d.RDLEN, rn)
    if bus is not None: d.write(d.BUS, bus)
    d.write(d.GO, cmd); return d.read(d.RET)

# --- I2C ---
d, be = i2c()
setbuf(d, [5, 0xAA, 0xBB])
check("I2C WRITE: 結果は送ったバイト数、レジスタ 5 から書く", (i2c_do(d, 1, n=3), list(be.regs[0x48][5:7])), (3, [0xAA, 0xBB]))
setbuf(d, [5])
check("I2C WRITE_READ: レジスタ 5 を選んで 2 バイト読む", (i2c_do(d, 3, n=1, rn=2), getbuf(d, 2)), (2, [0xAA, 0xBB]))
check("I2C 既定のバスは 1", be.log[-1][0], 1)
i2c_do(d, 3, n=1, rn=1, bus=3)
check("I2C バス番号を変えられる", be.log[-1][0], 3)
check("I2C READ: 直前の続きから(ポインタが進んでいる)", (i2c_do(d, 2, n=1), getbuf(d, 1)), (1, [be.regs[0x48][6 + 1]]))
check("I2C PROBE: 応答する相手は 0、しない相手は -6(ENXIO)", (i2c_do(d, 4), i2c_do(d, 4, addr=0x50)), (0, -6))
check("I2C WRITE: 応答しない相手は -6", i2c_do(d, 1, addr=0x50, n=1), -6)
check("I2C 知らない命令は -22", i2c_do(d, 9, n=1), -22)
check("I2C アドレスが範囲外は -22", i2c_do(d, 4, addr=200), -22)
check("I2C 長さが範囲外・負は -22", (i2c_do(d, 1, n=5000), i2c_do(d, 1, n=-1)), (-22, -22))
d.mem[BUF + 4] = 300
check("I2C バッファに 0〜255 でない語があると -22", i2c_do(d, 1, n=2), -22)
check("I2C バッファが未書き込み(unit)でも -22", i2c_do(d, 1, buf=0x700000, n=1), -22)
before = dict(d.reg); d.write(d.ADDR, True); d.write(d.LEN, "3"); d.write(d.LEN, None)
check("I2C 整数でない書き込み(bool・文字列・unit)は捨てる", d.reg, before)
check("I2C 長さ 0 の WRITE は何もせず 0", i2c_do(d, 1, n=0), 0)
check("I2C RET の初期値は 0、未設定のレジスタは __", (B.I2c(backend=B.FakeI2c()).read(0x18), B.I2c(backend=B.FakeI2c()).read(0x00)), (0, None))
class Down(B.FakeI2c):
    def transfer(self, *a): raise ImportError("smbus2")
class Odd(B.FakeI2c):
    def transfer(self, *a): raise RuntimeError("x")
class Nack(B.FakeI2c):
    def transfer(self, *a): raise OSError(121, "nack")
for cls, want, nm in ((Down, -19, "ライブラリが無い = -19(ENODEV)"), (Odd, -5, "想定外の例外 = -5(EIO)"), (Nack, -121, "NACK(errno 121)はそのまま負にして返す")):
    dd = B.I2c(backend=cls((0x48,))); dd.mem = {BUF: 1}
    check("I2C バックエンドの失敗: " + nm, i2c_do(dd, 1, n=1), want)
try: B.make_i2c("nanika"); ok = False
except ValueError: ok = True
check("I2C 知らないバックエンド名はエラー", ok, True)
check("I2C fake:0x48,0x50 の指定", sorted(B.make_i2c("fake:0x48,0x50").regs), [0x48, 0x50])

# --- SPI ---
def spi(inv=False):
    be = B.FakeSpi(inv); d = B.Spi(backend=be); d.mem = {}; return d, be
def spi_do(d, data, cmd=1, n=None, **kw):
    setbuf(d, data)
    d.write(d.BUF, BUF); d.write(d.LEN, len(data) if n is None else n)
    for k, v in kw.items(): d.write(getattr(d, k.upper()), v)
    d.write(d.GO, cmd); return d.read(d.RET)
d, be = spi()
check("SPI TRANSFER: ループバックで同じバイトが返り、結果は長さ", (spi_do(d, [1, 2, 3, 4]), getbuf(d, 4)), (4, [1, 2, 3, 4]))
check("SPI 既定: 1MHz・モード 0・CS0・バス 0", be.log[-1], (0, 0, 0, 1000000, bytes([1, 2, 3, 4])))
spi_do(d, [9], speed=500000, mode=3, cs=1, bus=1)
check("SPI クロック・モード・CS・バスを変えられる", be.log[-1], (1, 1, 3, 500000, bytes([9])))
spi_do(d, [9], speed=0, mode=4, cs=2)
check("SPI 範囲外のクロック・モード・CS は捨てる", (d.read(d.SPEED), d.read(d.MODE), d.read(d.CS)), (500000, 3, 1))
d2, _ = spi(inv=True)
check("SPI fake:inv は全ビット反転", (spi_do(d2, [0, 255, 15]), getbuf(d2, 3)), (3, [255, 0, 240]))
check("SPI 知らない命令は -22", spi_do(d, [1], cmd=2), -22)
check("SPI 長さが範囲外は -22", spi_do(d, [1], n=5000), -22)
check("SPI 長さ 0 は 0", spi_do(d, [1], n=0), 0)
d.mem.pop(BUF)
d.write(d.BUF, BUF); d.write(d.LEN, 1); d.write(d.GO, 1)
check("SPI バッファが未書き込みなら -22", d.read(d.RET), -22)
class SDown(B.FakeSpi):
    def transfer(self, *a): raise ImportError("spidev")
ds = B.Spi(backend=SDown()); ds.mem = {BUF: 1}
check("SPI ライブラリが無い = -19", spi_do(ds, [1]), -19)
try: B.make_spi("nanika"); ok = False
except ValueError: ok = True
check("SPI 知らないバックエンド名はエラー", ok, True)

# --- Sign から(本物のインタープリタ) ---
def sign(f, *flags):
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), os.path.join(HERE, f), *flags], capture_output=True, timeout=60)
    return r.stdout.decode().split(), r.stderr.decode().strip()
check("i2c_scan.sn: 応答したアドレスだけ出す", sign("i2c_scan.sn", "--i2c=fake:0x48,0x50"), (["0x48", "0x50", "0"], ""))
check("i2c_scan.sn: 何も無ければ何も出さない", sign("i2c_scan.sn", "--i2c=fake"), (["0"], ""))
check("spi_loopback.sn: 1 2 3 4 が返る", sign("spi_loopback.sn", "--spi=fake"), (["1", "2", "3", "4", "0"], ""))
print("\n" + ("全部通った" if not bad else f"{bad} 件 食い違い")); sys.exit(1 if bad else 0)
