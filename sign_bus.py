"""sign_bus.py — I2C 装置と SPI 装置(Raspberry Pi のセンサー・ディスプレイ・メモリ IC と話す)。
仕様に定めの無い拡張で、sign_gfx.py・sign_sys.py・sign_gpio.py の装置と同じ位置づけ。付けたときだけ使える(`--i2c` `--spi`、それぞれ `=バックエンド`)。

  バッファ(buf)は、インタープリタのメモリの番地から 1 語 = 1 バイト(0〜255)・4 バイト刻み(sign_sys.py と同じ形。std.sn の str_ / arr_ と同じ置き方)。
  1 回の転送は 4096 バイトまで。GO に命令の番号を書くと実行され、RET を読むと結果が取れる(0 以上なら成功、負なら -エラー番号)。

■ I2C   I2C_BASE = 0x9600000
    base + 0x00  ADDR   RW  相手の 7 ビットのアドレス(0〜127)
    base + 0x04  BUF    RW  バッファの番地
    base + 0x08  LEN    RW  バイト数
    base + 0x0C  RDLEN  RW  命令 3 で読み返すバイト数
    base + 0x10  BUS    RW  バス番号(既定 1。ラズパイの GPIO2=SDA・GPIO3=SCL は 1)
    base + 0x14  GO     W   1 WRITE: BUF から LEN バイト送る。結果 LEN
                            2 READ: LEN バイト読んで BUF に入れる。結果 LEN
                            3 WRITE_READ: BUF から LEN バイト送り、(間に STOP を入れず)RDLEN バイト読んで BUF に入れる。結果 RDLEN(レジスタを選んで読むときの形)
                            4 PROBE: その相手が応答するか(応答すれば 0)
    base + 0x18  RET    R   結果
■ SPI   SPI_BASE = 0x9700000
    base + 0x00  BUF    RW  バッファの番地
    base + 0x04  LEN    RW  バイト数
    base + 0x08  SPEED  RW  クロック(Hz、1〜125000000、既定 1000000)
    base + 0x0C  MODE   RW  0〜3(CPOL・CPHA。既定 0)
    base + 0x10  CS     RW  チップセレクト 0 か 1(CE0・CE1。既定 0)
    base + 0x14  GO     W   1 TRANSFER: BUF から LEN バイト送ると同時に LEN バイト受け取り、BUF を受け取った内容で置き換える。結果 LEN
    base + 0x18  RET    R   結果
    base + 0x1C  BUS    RW  バス番号(既定 0)
  8 ビット固定・MSB 先。送るだけのときも受け取りは起きる(捨てるなら読まない)。受け取るだけのときは 0 を送る。

エラー番号(Linux の errno に合わせる): 5 EIO / 6 ENXIO(I2C: 相手が応答しない)/ 19 ENODEV(バスが無い・ライブラリが無い)/ 22 EINVAL(引数がおかしい)/ 110 ETIMEDOUT / 121 EREMOTEIO(I2C の NACK)
  バックエンドが出した OSError はその errno を負にして返す。それ以外の例外は -5。

バックエンド(--i2c=名前 / --spi=名前。省くと auto):
    auto     I2C は smbus2、SPI は spidev があればそれ、無ければ fake
    smbus2   smbus2(pip install smbus2)。 spidev: spidev(pip install spidev)。 /dev/i2c-1・/dev/spidev0.0 は raspi-config で有効にし、ユーザーが i2c・spi グループに入っていること
    fake     本物のバスを使わない(パソコンでの練習・試験)。
             I2C: fake:0x48,0x50 と書くとそのアドレスに「レジスタ 256 個の部品」がある(最初に送った 1 バイトがレジスタの位置、続く分はそこから書く。読むとそこから進む)。無いアドレスは ENXIO。
             SPI: 送ったバイトをそのまま返す(ループバック)。fake:inv なら全ビット反転して返す。
"""
import sys
from sign_mem import DevMem

I2C_BASE, SPI_BASE = 0x9600000, 0x9700000
MAXIO = 4096
ENXIO, EIO, ENODEV, EINVAL, EREMOTEIO = 6, 5, 19, 22, 121


class Mem(DevMem):
    """インタープリタのメモリ(sign_sys.py と同じ探し方)。"""
    def get_bytes(self, buf, n):
        mem = self.memory()
        if mem is None or n < 0 or n > MAXIO or not isinstance(buf, int): return None
        out = bytearray()
        for i in range(n):
            v = mem.get(buf + 4 * i)
            if not isinstance(v, int) or isinstance(v, bool) or not 0 <= v <= 255: return None
            out.append(v)
        return bytes(out)

    def err(self, e):
        return -(e.errno if isinstance(e, OSError) and isinstance(e.errno, int) and e.errno > 0 else EIO)


# ---------------- I2C ----------------
class FakeI2c:
    name = "fake"
    def __init__(self, addrs=()): self.regs, self.ptr, self.log = {a: bytearray(256) for a in addrs}, {a: 0 for a in addrs}, []
    def transfer(self, bus, addr, wdata, rlen):
        self.log.append((bus, addr, bytes(wdata), rlen))
        if addr not in self.regs: raise OSError(ENXIO, "no device")
        r = self.regs[addr]
        if wdata:
            self.ptr[addr] = wdata[0] % 256
            for b in wdata[1:]: r[self.ptr[addr]] = b; self.ptr[addr] = (self.ptr[addr] + 1) % 256
        out = bytearray()
        for _ in range(rlen): out.append(r[self.ptr[addr]]); self.ptr[addr] = (self.ptr[addr] + 1) % 256
        return bytes(out)
    def probe(self, bus, addr):
        if addr not in self.regs: raise OSError(ENXIO, "no device")
    def close(self): pass


class FakeAht25:
    """AHT25(温湿度センサー、アドレス 0x38)のまねをする練習用の部品。fake の素朴なレジスタ部品とは違い、命令で動く。
    0xBA = リセット、0x71 = 状態を読む、0xBE xx xx = 初期化(校正ビットが立つ)、0xAC 33 00 = 測定開始。
    測定開始のあと busy 回の読み出しは「忙しい」(状態の bit7)を返し、そのあと 7 バイト(状態・湿度 20 ビット・温度 20 ビット・CRC)を返す。
    練習用: 実物の時間や雑音は無い。温度 t(℃)と湿度 h(%)は属性で変えられる。"""
    name = "aht25"
    ADDR = 0x38
    def __init__(self, t=25.0, h=50.0, calibrated=True, busy=1):
        self.t, self.h, self.calibrated, self.busy, self.pending, self.log = t, h, calibrated, busy, 0, []
        self.corrupt = False
    def status(self): return (0x18 if self.calibrated else 0) | (0x80 if self.pending > 0 else 0)
    @staticmethod
    def crc8(data):
        c = 0xFF
        for b in data:
            c ^= b
            for _ in range(8): c = ((c << 1) ^ 0x31) & 0xFF if c & 0x80 else (c << 1) & 0xFF
        return c
    def frame(self):
        rh = max(0, min(0xFFFFF, round(self.h / 100 * (1 << 20)))); tr = max(0, min(0xFFFFF, round((self.t + 50) / 200 * (1 << 20))))
        d = [self.status(), rh >> 12, (rh >> 4) & 255, ((rh & 15) << 4) | (tr >> 16), (tr >> 8) & 255, tr & 255]
        c = self.crc8(d) ^ (0x55 if self.corrupt else 0)
        return bytes(d + [c])
    def transfer(self, bus, addr, wdata, rlen):
        self.log.append((bus, addr, bytes(wdata), rlen))
        if addr != self.ADDR: raise OSError(ENXIO, "no device")
        w = list(wdata)
        if w[:1] == [0xBA]: self.pending = 0; return b""          # リセット(校正の状態は変えない。校正されていない部品は calibrated=False で作る)
        if w[:1] == [0xBE]: self.calibrated = True; return b""
        if w[:1] == [0xAC]:
            self.pending = self.busy; return b""
        if w[:1] == [0x71]: return bytes([self.status()])[:rlen] if rlen else b""
        if w: raise OSError(EREMOTEIO, "bad command")
        if rlen == 0: return b""
        f = self.frame()
        if self.pending > 0: self.pending -= 1
        return f[:rlen]
    def probe(self, bus, addr):
        if addr != self.ADDR: raise OSError(ENXIO, "no device")
    def close(self): pass


class Smbus2Backend:
    name = "smbus2"
    def __init__(self):
        import smbus2
        self.m, self.buses = smbus2, {}
    def bus(self, n):
        if n not in self.buses: self.buses[n] = self.m.SMBus(n)
        return self.buses[n]
    def transfer(self, bus, addr, wdata, rlen):
        msgs, rd = [], None
        if wdata: msgs.append(self.m.i2c_msg.write(addr, list(wdata)))
        if rlen: rd = self.m.i2c_msg.read(addr, rlen); msgs.append(rd)
        if msgs: self.bus(bus).i2c_rdwr(*msgs)
        return bytes(list(rd)) if rd is not None else b""
    def probe(self, bus, addr): self.bus(bus).write_quick(addr)
    def close(self):
        for b in self.buses.values():
            try: b.close()
            except Exception: pass
        self.buses.clear()


def make_i2c(spec):
    name, _, opt = (spec or "auto").partition(":")
    if name in ("", "auto"):
        try: return make_i2c("smbus2")
        except ImportError:
            print("注意: smbus2 が見つからないので、練習用の fake を使います(本物の I2C は動かず、部品は 1 つも見つかりません)。本物を使うには smbus2 を入れます", file=sys.stderr)
            return FakeI2c()
    if name == "fake": return FakeI2c([int(x, 0) for x in opt.split(",") if x.strip()])
    if name == "smbus2": return Smbus2Backend()
    if name == "aht25":                                   # aht25:温度,湿度(練習用の AHT25。例 aht25:23.5,61)
        parts = [x.strip() for x in opt.split(",") if x.strip()]
        v = [float(x) for x in parts if x.replace(".", "", 1).lstrip("-").isdigit()]
        o = [x for x in parts if not x.replace(".", "", 1).lstrip("-").isdigit()]
        a = FakeAht25(*v[:2], calibrated="uncal" not in o)           # 付け足し: uncal = 校正されていない / badcrc = CRC を壊す / busy=N = N 回忙しい
        a.corrupt = "badcrc" in o
        for x in o:
            if x.startswith("busy="): a.busy = int(x[5:])
        return a
    raise ValueError(f"知らない I2C バックエンド: {spec}(auto / smbus2 / fake / aht25)")


class I2c(Mem):
    ADDR, BUF, LEN, RDLEN, BUS, GO, RET = 0x00, 0x04, 0x08, 0x0C, 0x10, 0x14, 0x18
    def __init__(self, spec=None, base=I2C_BASE, backend=None):
        self.base, self.size = base, 0x20
        self.be = backend or make_i2c(spec)
        self.reg, self.ret = {self.BUS: 1}, 0

    def read(self, off):
        if off == self.RET: return self.ret
        return self.reg.get(off)

    def write(self, off, v):
        if not isinstance(v, int) or isinstance(v, bool): return
        if off in (self.ADDR, self.BUF, self.LEN, self.RDLEN, self.BUS): self.reg[off] = v
        elif off == self.GO: self.ret = self.go(v)

    def go(self, cmd):
        r = self.reg
        addr, buf, n, rn, bus = r.get(self.ADDR), r.get(self.BUF), r.get(self.LEN, 0), r.get(self.RDLEN, 0), r.get(self.BUS, 1)
        if not isinstance(addr, int) or not 0 <= addr <= 127 or bus < 0: return -EINVAL
        try:
            if cmd == 4: self.be.probe(bus, addr); return 0
            if cmd not in (1, 2, 3) or not 0 <= n <= MAXIO or not 0 <= rn <= MAXIO: return -EINVAL
            if cmd in (1, 3):
                w = self.get_bytes(buf, n)
                if w is None: return -EINVAL
            else: w = b""
            rlen = n if cmd == 2 else rn if cmd == 3 else 0
            if cmd == 1 and n == 0 or cmd == 2 and n == 0: return 0
            data = self.be.transfer(bus, addr, w, rlen)
            if rlen:
                if len(data) != rlen: return -EIO
                if not self.put_bytes(buf, data): return -EINVAL
            return n if cmd in (1, 2) else rn
        except ImportError: return -ENODEV
        except Exception as e: return self.err(e)

    def finish(self): self.release()
    def release(self):
        try: self.be.close()
        except Exception: pass


# ---------------- SPI ----------------
class FakeSpi:
    name = "fake"
    def __init__(self, invert=False): self.invert, self.log = invert, []
    def transfer(self, bus, cs, mode, speed, data):
        self.log.append((bus, cs, mode, speed, bytes(data)))
        return bytes((b ^ 255) if self.invert else b for b in data)
    def close(self): pass


class SpidevBackend:
    name = "spidev"
    def __init__(self):
        import spidev
        self.m, self.devs = spidev, {}
    def transfer(self, bus, cs, mode, speed, data):
        d = self.devs.get((bus, cs))
        if d is None: d = self.devs[(bus, cs)] = self.m.SpiDev(); d.open(bus, cs)
        d.mode, d.max_speed_hz = mode, speed
        return bytes(d.xfer2(list(data)))
    def close(self):
        for d in self.devs.values():
            try: d.close()
            except Exception: pass
        self.devs.clear()


def make_spi(spec):
    name, _, opt = (spec or "auto").partition(":")
    if name in ("", "auto"):
        try: return make_spi("spidev")
        except ImportError:
            print("注意: spidev が見つからないので、練習用の fake を使います(本物の SPI は動かず、送った値がそのまま返ります)。本物を使うには spidev を入れます", file=sys.stderr)
            return FakeSpi()
    if name == "fake": return FakeSpi(invert=(opt == "inv"))
    if name == "spidev": return SpidevBackend()
    raise ValueError(f"知らない SPI バックエンド: {spec}(auto / spidev / fake)")


class Spi(Mem):
    BUF, LEN, SPEED, MODE, CS, GO, RET, BUS = 0x00, 0x04, 0x08, 0x0C, 0x10, 0x14, 0x18, 0x1C
    def __init__(self, spec=None, base=SPI_BASE, backend=None):
        self.base, self.size = base, 0x20
        self.be = backend or make_spi(spec)
        self.reg, self.ret = {self.SPEED: 1000000, self.MODE: 0, self.CS: 0, self.BUS: 0}, 0

    def read(self, off):
        if off == self.RET: return self.ret
        return self.reg.get(off)

    def write(self, off, v):
        if not isinstance(v, int) or isinstance(v, bool): return
        if off in (self.BUF, self.LEN, self.BUS): self.reg[off] = v
        elif off == self.SPEED:
            if 1 <= v <= 125000000: self.reg[off] = v
        elif off == self.MODE:
            if 0 <= v <= 3: self.reg[off] = v
        elif off == self.CS:
            if v in (0, 1): self.reg[off] = v
        elif off == self.GO: self.ret = self.go(v)

    def go(self, cmd):
        r = self.reg
        buf, n = r.get(self.BUF), r.get(self.LEN, 0)
        if cmd != 1 or not 0 <= n <= MAXIO or r[self.BUS] < 0: return -EINVAL
        data = self.get_bytes(buf, n)
        if data is None: return -EINVAL
        if n == 0: return 0
        try:
            got = self.be.transfer(r[self.BUS], r[self.CS], r[self.MODE], r[self.SPEED], data)
            if len(got) != n: return -EIO
            if not self.put_bytes(buf, got): return -EINVAL
            return n
        except ImportError: return -ENODEV
        except Exception as e: return self.err(e)

    def finish(self): self.release()
    def release(self):
        try: self.be.close()
        except Exception: pass
