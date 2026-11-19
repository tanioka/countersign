"""sign_gpio.py — GPIO 装置(Raspberry Pi のピンを番地で触る)。LED を点ける・スイッチを読む。
仕様に定めの無い拡張で、sign_gfx.py・sign_sys.py の装置と同じ位置づけ。付けたときだけ使える(`--gpio` か `--gpio=バックエンド`)。

    GPIO_BASE = 0x9500000      ピン番号は BCM 番号(ラズパイの GPIO17 なら 17。基板の端子の番号ではない)。0〜63
    base + 4*pin           RW  ピンの値(0 か 1)。書くとそのピンが「出力」になり、HIGH(1)/LOW(0)を出す。
                               読むと、出力のピンは最後に書いた値、入力のピンは今の電圧(未設定のピンを読むと「入力」にして読む)
    base + 0x100 + 4*pin   RW  ピンの向き。0 入力、1 出力、2 入力(内蔵プルアップ。スイッチを GND との間につなぐ形)、3 入力(プルダウン)、4 PWM 出力。
                               読むと設定した向き(未設定は __)
    base + 0x200 + 4*pin   RW  PWM の明るさ(デューティ比)。0〜1000(1000 = 100.0%。範囲外は 0〜1000 に丸める)。書くとそのピンが PWM の出力になる
                               (向きの読み出しは 4)。値のレジスタを読むと、PWM のピンは「デューティが 0 でなければ 1」。このレジスタを読むと今のデューティ(PWM でなければ __)
    base + 0x300 + 4*pin   RW  PWM の周波数(Hz。1〜100000、既定 1000)。範囲外は捨てる。PWM を始めたあとに書いてもすぐ効く
  0 でも 1 でもない値を値の番地に書くと、0 以外は 1 として扱う。整数でない値・範囲外の番地は黙って捨てる。
  バックエンドが失敗したとき(ピンが無い・権限が無い など)は、標準エラーに 1 度だけ理由を出して、その書き込みを捨てる。
  終わるとき(release)は、使ったピンをぜんぶ元に戻す(出力は LOW)。

バックエンド(--gpio=名前。省くと auto):
    auto      gpiozero があればそれ、無ければ RPi.GPIO、どちらも無ければ fake
    gpiozero  gpiozero(Raspberry Pi OS に入っている。Pi 5 でも動く)
    rpigpio   RPi.GPIO
    fake      本物のピンを使わない(パソコンでの試験・練習用)。ピンの変化を標準エラーに「[gpio] 17 = 1」と出す。fake:quiet なら出さない
"""
import sys

GPIO_BASE = 0x9500000
PINS = 64
MODE_OFF = 0x100
IN, OUT, IN_UP, IN_DOWN, PWM = 0, 1, 2, 3, 4
DUTY_OFF, FREQ_OFF, DUTY_MAX, FREQ_DEF = 0x200, 0x300, 1000, 1000


class FakeBackend:
    """本物のピンを使わない。levels に出力の値、inputs に(試験が入れる)入力の電圧を持つ。"""
    name = "fake"
    def __init__(self, quiet=False): self.quiet, self.levels, self.inputs, self.modes, self.log = quiet, {}, {}, {}, []
    def setup(self, pin, mode):
        self.modes[pin] = mode
        if mode == OUT: self.levels.setdefault(pin, 0)
    def output(self, pin, v):
        self.levels[pin] = v; self.log.append((pin, v))
        if not self.quiet: print(f"[gpio] {pin} = {v}", file=sys.stderr)
    def pwm(self, pin, duty, freq):
        self.levels[pin] = duty; self.log.append((pin, "pwm", duty, freq))
        if not self.quiet: print(f"[gpio] {pin} pwm {duty / 10:g}% {freq}Hz", file=sys.stderr)
    def input(self, pin):
        default = 1 if self.modes.get(pin) == IN_UP else 0
        return self.inputs.get(pin, default)
    def close(self):
        for p in list(self.modes): self.modes[p] = IN
        self.levels.clear()


class GpiozeroBackend:
    name = "gpiozero"
    def __init__(self):
        import gpiozero
        self.z, self.dev = gpiozero, {}
    def setup(self, pin, mode):
        self.drop(pin)
        z = self.z
        if mode == PWM: self.dev[pin] = z.PWMOutputDevice(pin, frequency=FREQ_DEF)
        elif mode == OUT: self.dev[pin] = z.DigitalOutputDevice(pin)
        elif mode == IN_UP: self.dev[pin] = z.DigitalInputDevice(pin, pull_up=True)
        elif mode == IN_DOWN: self.dev[pin] = z.DigitalInputDevice(pin, pull_up=False)
        else: self.dev[pin] = z.DigitalInputDevice(pin, pull_up=None, active_state=True)
    def output(self, pin, v): self.dev[pin].value = v
    def pwm(self, pin, duty, freq):
        d = self.dev[pin]
        if d.frequency != freq: d.frequency = freq
        d.value = duty / DUTY_MAX
    def input(self, pin): return 1 if self.dev[pin].pin.state else 0     # 生の電圧(1 = HIGH)。gpiozero の value はプルアップだと「押した = LOW = 1」に反転するので使わない
    def drop(self, pin):
        d = self.dev.pop(pin, None)
        if d is not None: d.close()
    def close(self):
        for p in list(self.dev): self.drop(p)


class RpigpioBackend:
    name = "rpigpio"
    def __init__(self):
        import RPi.GPIO as G
        self.G = G; G.setmode(G.BCM); G.setwarnings(False); self.used = set(); self.pw = {}
    def stop_pwm(self, pin):
        p = self.pw.pop(pin, None)
        if p is not None: p.stop()
    def setup(self, pin, mode):
        G = self.G
        self.stop_pwm(pin)
        if mode in (OUT, PWM): G.setup(pin, G.OUT, initial=G.LOW)
        else: G.setup(pin, G.IN, pull_up_down={IN_UP: G.PUD_UP, IN_DOWN: G.PUD_DOWN}.get(mode, G.PUD_OFF))
        self.used.add(pin)
    def output(self, pin, v): self.G.output(pin, self.G.HIGH if v else self.G.LOW)
    def pwm(self, pin, duty, freq):
        p = self.pw.get(pin)
        if p is None: p = self.pw[pin] = self.G.PWM(pin, freq); p.start(duty / 10)
        else: p.ChangeFrequency(freq); p.ChangeDutyCycle(duty / 10)
    def input(self, pin): return 1 if self.G.input(pin) else 0
    def close(self):
        for p in list(self.pw): self.stop_pwm(p)
        for p in self.used:
            try: self.G.output(p, self.G.LOW)
            except Exception: pass
        self.G.cleanup(list(self.used)); self.used.clear()


def make_backend(spec):
    name, _, opt = (spec or "auto").partition(":")
    if name in ("", "auto"):
        for n in ("gpiozero", "rpigpio"):
            try: return make_backend(n)
            except ImportError: pass
        print("注意: gpiozero も RPi.GPIO も見つからないので、練習用の fake を使います(本物のピンは動きません)。本物を使うには gpiozero か RPi.GPIO を入れます", file=sys.stderr)
        return FakeBackend()
    if name == "fake": return FakeBackend(quiet=(opt == "quiet"))
    if name == "gpiozero": return GpiozeroBackend()
    if name == "rpigpio": return RpigpioBackend()
    raise ValueError(f"知らない GPIO バックエンド: {spec}(auto / gpiozero / rpigpio / fake)")


class Gpio:
    def __init__(self, spec=None, base=GPIO_BASE, backend=None):
        self.base, self.size = base, 0x400
        self.be = backend or make_backend(spec)
        self.mode, self.out, self.freq, self.warned = {}, {}, {}, False

    # --- 装置の口 ---
    def read(self, off):
        if MODE_OFF <= off < MODE_OFF + 4 * PINS and off % 4 == 0: return self.mode.get((off - MODE_OFF) // 4)
        if DUTY_OFF <= off < DUTY_OFF + 4 * PINS and off % 4 == 0:
            pin = (off - DUTY_OFF) // 4
            return self.out.get(pin) if self.mode.get(pin) == PWM else None
        if FREQ_OFF <= off < FREQ_OFF + 4 * PINS and off % 4 == 0: return self.freq.get((off - FREQ_OFF) // 4, FREQ_DEF)
        if 0 <= off < 4 * PINS and off % 4 == 0:
            pin = off // 4
            if self.mode.get(pin) == PWM: return 1 if self.out.get(pin, 0) > 0 else 0
            if pin not in self.mode and not self.set_mode(pin, IN): return None
            if self.mode.get(pin) == OUT: return self.out.get(pin, 0)
            try: return self.be.input(pin)
            except Exception as e: self.fail(e); return None
        return None

    def write(self, off, v):
        if not isinstance(v, int) or isinstance(v, bool): return
        if MODE_OFF <= off < MODE_OFF + 4 * PINS and off % 4 == 0:
            if v in (IN, OUT, IN_UP, IN_DOWN, PWM): self.set_mode((off - MODE_OFF) // 4, v)
        elif DUTY_OFF <= off < DUTY_OFF + 4 * PINS and off % 4 == 0:
            pin = (off - DUTY_OFF) // 4
            if self.mode.get(pin) != PWM and not self.set_mode(pin, PWM): return
            self.out[pin] = max(0, min(DUTY_MAX, v))
            try: self.be.pwm(pin, self.out[pin], self.freq.get(pin, FREQ_DEF))
            except Exception as e: self.fail(e)
        elif FREQ_OFF <= off < FREQ_OFF + 4 * PINS and off % 4 == 0:
            pin = (off - FREQ_OFF) // 4
            if 1 <= v <= 100000:
                self.freq[pin] = v
                if self.mode.get(pin) == PWM:
                    try: self.be.pwm(pin, self.out.get(pin, 0), v)
                    except Exception as e: self.fail(e)
        elif 0 <= off < 4 * PINS and off % 4 == 0:
            pin = off // 4
            if self.mode.get(pin) != OUT and not self.set_mode(pin, OUT): return
            self.out[pin] = 1 if v else 0
            try: self.be.output(pin, self.out[pin])
            except Exception as e: self.fail(e)

    def set_mode(self, pin, mode):
        try: self.be.setup(pin, mode)
        except Exception as e: self.fail(e); return False
        self.mode[pin] = mode
        if mode in (OUT, PWM): self.out[pin] = 0
        return True

    def fail(self, e):
        if not self.warned: self.warned = True; print(f"GPIO: {type(e).__name__}: {e}", file=sys.stderr)

    def finish(self): self.release()
    def release(self):
        try: self.be.close()
        except Exception as e: self.fail(e)
        self.mode.clear(); self.out.clear(); self.freq.clear()
