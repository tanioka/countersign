#!/usr/bin/env python3
"""AHT25 ドライバ(aht25.sn)と練習用の偽センサー(sign_bus.FakeAht25)の試験。python test_aht25.py"""
import os, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import sign_bus as B

bad = 0
def check(name, got, want):
    global bad
    ok = got == want; bad += not ok
    print(("ok  " if ok else "NG  ") + name + ("" if ok else f"\n    得た: {got!r}\n    期待: {want!r}"))

# --- 偽センサー単体 ---
a = B.FakeAht25(25.0, 50.0)
check("CRC-8(多項式 0x31・初期値 0xFF)の定番の例 0xBE 0xEF → 0x92", B.FakeAht25.crc8(bytes([0xBE, 0xEF])), 0x92)
check("状態 0x71: 校正済みで 0x18", a.transfer(1, 0x38, b"\x71", 1), b"\x18")
a.transfer(1, 0x38, b"\xAC\x33\x00", 0)
check("測定開始の直後は忙しい(bit7)", a.transfer(1, 0x38, b"\x71", 1)[0] & 0x80, 0x80)
f1 = a.transfer(1, 0x38, b"", 7); f2 = a.transfer(1, 0x38, b"", 7)
check("1 回読むと終わる(次は忙しくない)", (f1[0] & 0x80, f2[0] & 0x80), (0x80, 0))
check("7 バイト・CRC が合う", (len(f2), B.FakeAht25.crc8(f2[:6]) == f2[6]), (7, True))
try: a.transfer(1, 0x39, b"", 1); r = None
except OSError as e: r = e.errno
check("別のアドレスは ENXIO(6)", r, 6)

# --- Sign のドライバ ---
def run(src, spec, timeout=60):
    with tempfile.NamedTemporaryFile("w", suffix=".sn", dir=HERE, delete=False) as f:
        f.write("`aht25.sn`@~\n" + src); p = f.name
    try:
        r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p, "--i2c=" + spec, "--timer=virtual"], capture_output=True, text=True, timeout=timeout, cwd=HERE)
        return (r.stdout + r.stderr).strip().splitlines()
    finally: os.unlink(p)

def one(spec, t=None):
    out = run("d : z ? seq6 (println_int (aht25_init 0)) (println_int (aht25_measure 0)) (println_int (aht25_temp 0)) (println_int (aht25_hum 0)) 0 0\nd 0", spec)
    return out[:4]

check("正常: 25.00 ℃ / 50.00 %", one("aht25:25,50"), ["0", "0", "2500", "5000"])
check("温度の小数と湿度", one("aht25:23.5,61"), ["0", "0", "2350", "6100"])
check("氷点下", one("aht25:-12.34,5"), ["0", "0", "-1234", "500"])
check("高温・高湿", one("aht25:85,99.5"), ["0", "0", "8500", "9950"])
check("下限 -40 ℃ / 0 %", one("aht25:-40,0"), ["0", "0", "-4000", "0"])
check("校正されていなければ初期化(0xBE)して成功", one("aht25:25,50,uncal"), ["0", "0", "2500", "5000"])
check("CRC が壊れていれば -74", one("aht25:25,50,badcrc")[:2], ["0", "-74"])
check("忙しいまま終わらなければ -110", one("aht25:25,50,busy=99")[:2], ["0", "-110"])
check("3 回忙しくても待って成功", one("aht25:25,50,busy=3"), ["0", "0", "2500", "5000"])
check("応答しない(別アドレスの部品)は -6", one("fake:0x48")[:1], ["-6"])
check("レジスタ部品(0x38 にあるが AHT25 でない)は初期化できず -5", one("fake:0x38")[:1], ["-5"])

# 変換の誤差: 多数の値で Python の浮動小数と 0.01 以内
import itertools
worst = 0
for t, h in itertools.product((-39.9, -5.55, 0, 0.01, 21.37, 36.6, 79.99, 124.9), (0.5, 12.34, 50, 87.65, 99.99)):
    out = one(f"aht25:{t},{h}")
    if out[:2] != ["0", "0"]: worst = 999; print("   失敗", t, h, out); continue
    worst = max(worst, abs(int(out[2]) / 100 - t), abs(int(out[3]) / 100 - h))
check("多数の値で誤差が 0.01 以内", worst <= 0.0101, True)

# 表示
out = run("d : z ? seq4 (aht25_init 0) (aht25_measure 0) (aht25_show 0) 0\nd 0", "aht25:-5.2,7.05")
check("aht25_show", out[0], "T=-5.20 C RH=7.05 %")
out = run("d : z ? seq3 (aht25_fmt 0x600000 (0 - 50)) (println_mem 0x600000) 0\nd 0", "aht25:25,50")
check("aht25_fmt -50 → -0.50", out[0], "-0.50")

# デモ
r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), os.path.join(HERE, "aht25_demo.sn"), "--i2c=aht25:23.5,61", "--timer=virtual"], capture_output=True, text=True, cwd=HERE, timeout=60)
check("aht25_demo.sn: 5 行", r.stdout.count("T=23.50 C RH=61.00 %"), 5)

print("\n全部 ok" if not bad else f"\n{bad} 件 NG"); sys.exit(1 if bad else 0)
