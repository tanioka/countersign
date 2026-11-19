#!/usr/bin/env python3
"""GPIO 装置(sign_gpio.py)の試験。本物のピンは使わず fake バックエンドで確かめる。python test_gpio.py"""
import os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import sign_gpio as G

bad = 0
def check(name, got, want):
    global bad
    ok = got == want; bad += not ok
    print(("ok  " if ok else "NG  ") + name + ("" if ok else f"\n    得た: {got!r}\n    期待: {want!r}"))

B = G.GPIO_BASE
def dev():
    be = G.FakeBackend(quiet=True); return G.Gpio(backend=be), be
d, be = dev()
d.write(4 * 17, 1)
check("書くと出力になって HIGH", (be.levels.get(17), d.mode.get(17), be.log), (1, G.OUT, [(17, 1)]))
d.write(4 * 17, 0)
check("0 で LOW", be.levels.get(17), 0)
d.write(4 * 17, 7)
check("0 以外は 1", be.levels.get(17), 1)
check("出力のピンを読むと最後に書いた値", d.read(4 * 17), 1)
check("向きの読み出し", (d.read(G.MODE_OFF + 4 * 17), d.read(G.MODE_OFF + 4 * 5)), (G.OUT, None))
check("未設定のピンを読むと入力になる(既定 0)", (d.read(4 * 5), d.read(G.MODE_OFF + 4 * 5)), (0, G.IN))
be.inputs[5] = 1
check("入力は今の電圧", d.read(4 * 5), 1)
d.write(G.MODE_OFF + 4 * 6, G.IN_UP)
check("プルアップの入力は何もつながなければ 1", d.read(4 * 6), 1)
be.inputs[6] = 0
check("スイッチで GND につなぐと 0", d.read(4 * 6), 0)
d.write(G.MODE_OFF + 4 * 17, G.IN)
check("向きを入力に変える", (d.read(G.MODE_OFF + 4 * 17), be.modes[17]), (G.IN, G.IN))
d.write(4 * 9, True); d.write(4 * 9, "1"); d.write(4 * 9, None)
check("整数でない値は捨てる(bool・文字列・unit)", (9 in d.mode, be.levels.get(9)), (False, None))
d.write(G.MODE_OFF + 4 * 9, 9)
check("知らない向きは捨てる", 9 in d.mode, False)
check("範囲外・刻みでない番地は __", (d.read(4 * 64), d.read(2), d.read(0x1F0)), (None, None, None))
d.write(4 * 64, 1); d.write(3, 1)
check("範囲外の書き込みは何も起こさない", len(be.log), 3)
d.write(4 * 20, 1); d.release()
check("release: 出力は LOW に戻り、ピンの設定も消える", (be.levels, d.mode, d.out), ({}, {}, {}))

class Bad(G.FakeBackend):
    def setup(self, pin, mode): raise PermissionError("no access")
import io, contextlib
d = G.Gpio(backend=Bad()); e = io.StringIO()
with contextlib.redirect_stderr(e):
    d.write(4 * 3, 1); d.write(4 * 4, 1); r = d.read(4 * 3)
check("バックエンドの失敗: 落ちず、理由は 1 度だけ出す、読むと __", (r, e.getvalue().count("GPIO:"), "PermissionError" in e.getvalue()), (None, 1, True))
try: G.make_backend("nanika"); ok = False
except ValueError: ok = True
check("知らないバックエンド名はエラー", ok, True)
check("auto は(この環境に実機のライブラリが無ければ)fake", G.make_backend("auto").name in ("fake", "gpiozero", "rpigpio"), True)

# Sign から(本物のインタープリタ)
def sign(src, *flags):
    p = os.path.join(os.environ.get("TMPDIR", "/tmp"), "t_gpio.sn"); open(p, "w", encoding="utf-8").write(src)
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p, *flags], capture_output=True, timeout=60)
    return r.stdout.decode().strip(), r.stderr.decode().strip()
out, err = sign(f"a : {B + 4 * 17} # 1\nb : {B + 4 * 17} # 0\nc : {B + 4 * 17} # 1\n@{B + 4 * 17}", "--gpio=fake")
check("Sign から: 17 番に 1・0・1 を書き、読むと 1(変化が標準エラーに出る)", (out, err.splitlines()), ("1", ["[gpio] 17 = 1", "[gpio] 17 = 0", "[gpio] 17 = 1"]))
out, err = sign(f"a : {B + 4 * 17} # 1\n@{B + 4 * 17}", "--gpio=fake:quiet")
check("fake:quiet は出さない", (out, err), ("1", ""))
out, err = sign(f"@{B + 4 * 3}")
check("--gpio なしでは装置が無い(未書き込みの番地なので __)", err, "")
# ゲーム機から(led_gpio.sn。仮想時計で 140 こま = 約 2.2 秒 → 500 ミリ秒ごとに反転)
r = subprocess.run([sys.executable, os.path.join(HERE, "sign_console.py"), os.path.join(HERE, "led_gpio.sn"), "--display=null", "--gpio=fake", "--timer=virtual", "--frames=140"], capture_output=True, timeout=60)
lines = r.stderr.decode().splitlines()
check("led_gpio.sn: 初めに消灯、そのあと 500 ミリ秒ごとに 1,0,1,0", lines, ["[gpio] 17 = 0", "[gpio] 17 = 1", "[gpio] 17 = 0", "[gpio] 17 = 1", "[gpio] 17 = 0"])

# --- PWM ---
d, be = dev()
d.write(G.DUTY_OFF + 4 * 17, 250)
check("PWM: デューティを書くと PWM の出力になる(既定 1000Hz)", (be.log, d.mode.get(17), d.read(G.MODE_OFF + 4 * 17)), ([(17, "pwm", 250, 1000)], G.PWM, 4))
check("PWM: デューティの読み出し", d.read(G.DUTY_OFF + 4 * 17), 250)
check("PWM: 値のレジスタは「デューティ > 0 なら 1」", d.read(4 * 17), 1)
d.write(G.DUTY_OFF + 4 * 17, 0)
check("PWM: 0 なら値は 0", d.read(4 * 17), 0)
d.write(G.DUTY_OFF + 4 * 17, 5000); d.write(G.DUTY_OFF + 4 * 17, -3)
check("PWM: 範囲外は 0〜1000 に丸める", [e[2] for e in be.log[-2:]], [1000, 0])
d.write(G.FREQ_OFF + 4 * 17, 200)
check("PWM: 周波数を書くとすぐ効く", (be.log[-1], d.read(G.FREQ_OFF + 4 * 17)), ((17, "pwm", 0, 200), 200))
d.write(G.FREQ_OFF + 4 * 17, 0); d.write(G.FREQ_OFF + 4 * 17, 100001)
check("PWM: 周波数の範囲外(0・100001)は捨てる", d.read(G.FREQ_OFF + 4 * 17), 200)
check("PWM: 周波数の既定は 1000", d.read(G.FREQ_OFF + 4 * 3), 1000)
check("PWM でないピンのデューティは __", d.read(G.DUTY_OFF + 4 * 3), None)
d.write(G.FREQ_OFF + 4 * 8, 50); d.write(G.DUTY_OFF + 4 * 8, 500)
check("PWM: 先に周波数を決めてから始められる", be.log[-1], (8, "pwm", 500, 50))
n = len(be.log); d.write(G.DUTY_OFF + 4 * 17, "5"); d.write(G.DUTY_OFF + 4 * 64, 5)
check("PWM: 整数でない値・範囲外は捨てる", len(be.log), n)
d.write(4 * 17, 1)
check("PWM のピンに普通の値を書くと出力に戻る", (d.mode.get(17), be.log[-1], d.read(G.DUTY_OFF + 4 * 17)), (G.OUT, (17, 1), None))
d.release()
check("PWM: release で周波数の設定も消える", d.read(G.FREQ_OFF + 4 * 8), 1000)
out, err = sign(f"a : {B + 0x300 + 4 * 17} # 500\nb : {B + 0x200 + 4 * 17} # 500\n@{B + 0x200 + 4 * 17}", "--gpio=fake")
check("Sign から: 17 番に 50% の PWM(500Hz)", (out, err), ("500", "[gpio] 17 pwm 50% 500Hz"))
r = subprocess.run([sys.executable, os.path.join(HERE, "sign_console.py"), os.path.join(HERE, "led_pwm.sn"), "--display=null", "--gpio=fake", "--timer=virtual", "--frames=70"], capture_output=True, timeout=60)
lines = r.stderr.decode().splitlines()
check("led_pwm.sn: 0 から 2% ずつ上がっていく(20 ミリ秒ごと)", lines[:4], ["[gpio] 17 pwm 0% 1000Hz", "[gpio] 17 pwm 2% 1000Hz", "[gpio] 17 pwm 4% 1000Hz", "[gpio] 17 pwm 6% 1000Hz"])
# --- 装置を用意できないとき(名前の違うバックエンド・入っていない部品): トレースバックで落ちず、理由を知らせて終わる ---
for flag in ("--gpio=zzz", "--i2c=zzz", "--spi=zzz"):
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), os.path.join(HERE, "echo.sn"), flag], input=b"", capture_output=True, timeout=60)
    e = r.stderr.decode()
    check(f"{flag}: 理由を知らせて終わる(終了コード 1・トレースバックなし)", (r.returncode, "Traceback" in e, "エラー: 装置を用意できません" in e), (1, False, True))
r = subprocess.run([sys.executable, os.path.join(HERE, "sign_console.py"), os.path.join(HERE, "led_gpio.sn"), "--display=null", "--gpio=zzz"], capture_output=True, timeout=60)
e = r.stderr.decode()
check("sign_console.py --gpio=zzz: 理由を知らせて終わる(終了コード 1・トレースバックなし)", (r.returncode, "Traceback" in e, "エラー: 装置を用意できません" in e), (1, False, True))
print("\n" + ("全部通った" if not bad else f"{bad} 件 食い違い")); sys.exit(1 if bad else 0)
