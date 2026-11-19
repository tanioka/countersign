#!/usr/bin/env python3
"""IoT デモ(iot_demo.sn)と練習用ブローカー(iot_broker.py)の試験。偽のセンサー・偽の GPIO・自前のブローカー・本物の SQLite で通しに確かめる。python test_iot.py"""
import os, socket, sqlite3, subprocess, sys, tempfile, threading, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import iot_broker as B

bad = 0
def check(name, got, want):
    global bad
    ok = got == want; bad += not ok
    print(("ok  " if ok else "NG  ") + name + ("" if ok else f"\n    得た: {got!r}\n    期待: {want!r}"))

# --- ブローカー単体 ---
check("match: + と #", [B.match("a/+/c", "a/b/c"), B.match("a/#", "a/b/c"), B.match("a/+", "a/b/c"), B.match("a/b", "a/b"), B.match("#", "x/y"), B.match("a/+/c", "a/c")], [True, True, False, True, True, False])
check("残りの長さの符号化", [B.rl(n) for n in (0, 127, 128, 16383, 16384)], [b"\x00", b"\x7f", b"\x80\x01", b"\xff\x7f", b"\x80\x80\x01"])

def client(port):
    c = socket.create_connection(("127.0.0.1", port), timeout=3)
    c.sendall(B.packet(0x10, b"\x00\x04MQTT\x04\x02\x00\x3c\x00\x01x")); B.read_packet(c); return c
def sub(c, flt): c.sendall(B.packet(0x82, b"\x00\x01" + len(flt).to_bytes(2, "big") + flt.encode() + b"\x00")); return B.read_packet(c)
def pub(c, topic, pl, retain=0, qos=0):
    t = topic.encode(); c.sendall(B.packet(0x30 | (qos << 1) | retain, len(t).to_bytes(2, "big") + t + (b"\x00\x09" if qos else b"") + pl))

import io
b = B.Broker(port=0, out=io.StringIO())
c1, c2 = client(b.port), client(b.port)
check("SUBACK", sub(c1, "s/+/t"), (0x90, b"\x00\x01\x00"))
pub(c2, "s/a/t", b"hello"); pk = B.read_packet(c1)
check("購読者へ届く", (pk[0], pk[1][2:]), (0x30, b"\x00\x05s/a/thello"[2:]))
pub(c2, "s/a/u", b"no")
pub(c2, "r/x", b"keep", retain=1); time.sleep(0.2)
c3 = client(b.port); sub(c3, "r/#"); pk = B.read_packet(c3)
check("保持されたメッセージは後から購読した人へ(retain ビットつき)", (pk[0], pk[1].endswith(b"keep")), (0x31, True))
pub(c2, "q/1", b"x", qos=1)
check("QoS 1 には PUBACK", B.read_packet(c2), (0x40, b"\x00\x09"))
c2.sendall(bytes([0xC0, 0])); check("PINGRESP", B.read_packet(c2), (0xD0, b""))
b.inject("s/z/t", b"cmd"); pk = B.read_packet(c1)
check("inject は購読者へ", pk[1].endswith(b"cmd"), True)
check("届いたものは記録される", [p for p in b.pubs if p[0] in ("s/a/t", "r/x")], [("s/a/t", b"hello"), ("r/x", b"keep")])
c1.close(); time.sleep(0.2); b.inject("s/z/t", b"after")
check("切れた購読者は外れる", len(b.subs) <= 1, True)

# --- デモを通しで ---
def demo(port, flags, cycles=4, period=300, extra=""):
    root = tempfile.mkdtemp()
    src = open(os.path.join(HERE, "iot_demo.sn"), encoding="utf-8").read()
    src = src.replace("PORT : 1883", f"PORT : {port}").replace("CYCLES : 6", f"CYCLES : {cycles}").replace("PERIOD : 1000", f"PERIOD : {period}")
    fd, p = tempfile.mkstemp(prefix="_iot_t", suffix=".sn", dir=HERE); os.close(fd); open(p, "w", encoding="utf-8").write(src)     # 名前は実行ごとに別(同時に動かしても取り合わない)
    try:
        r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p, f"--db={root}", "--net=local", *flags], capture_output=True, text=True, timeout=90, cwd=HERE)
    finally: os.unlink(p)
    return r, root

b = B.Broker(port=0, out=io.StringIO())
threading.Timer(0.5, b.inject, args=("sign/iot/cmd/threshold", b"2000")).start()       # 20.00 ℃ に下げる → LED が点く
threading.Timer(0.6, b.inject, args=("sign/iot/cmd/threshold", b"abc")).start()        # 整数でない → 無視
threading.Timer(0.7, b.inject, args=("sign/iot/cmd/other", b"1")).start()              # 別のトピック → 無視
threading.Timer(1.3, b.inject, args=("sign/iot/cmd/threshold", b"2500")).start()       # 25.00 ℃ に上げる → LED が消える
r, root = demo(b.port, ["--i2c=aht25:23.5,61", "--gpio=fake"], cycles=5)
lines = r.stdout.splitlines()
check("終了(エラー無し)", (r.returncode, "エラー" in r.stdout), (0, False))
check("5 回測って出す", sum(1 for x in lines if x == "T=23.50 C RH=61.00 %"), 5)
topics = [t for t, p in b.pubs]
check("温度・湿度を毎回送る", (topics.count("sign/iot/temp"), topics.count("sign/iot/hum")), (5, 5))
check("温度は×100 の整数、湿度も", {p for t, p in b.pubs if t == "sign/iot/temp"} | {p for t, p in b.pubs if t == "sign/iot/hum"}, {b"2350", b"6100"})
led = [p for t, p in b.pubs if t == "sign/iot/led"]
check("LED の送信は変わったときだけ: 0(23.5 ≤ 30)→1(しきい値 20)→0(しきい値 25)", led, [b"0", b"1", b"0"])
check("命令で来たしきい値だけ反映(abc と別トピックは無視)", [x for x in lines if x.startswith("しきい値")], ["しきい値を変えた(×100): 2000", "しきい値を変えた(×100): 2500"])
gp = [x for x in r.stderr.splitlines() if x.startswith("[gpio]")]
check("GPIO17: 0 → 1 → 0、終わりに消灯", gp, ["[gpio] 17 = 0", "[gpio] 17 = 1", "[gpio] 17 = 0", "[gpio] 17 = 0"])
check("retain つきで送っている(ブローカーが最新値を保持している)", sorted(b.retained), ["sign/iot/hum", "sign/iot/led", "sign/iot/temp"])
db = sqlite3.connect(os.path.join(root, "iot.db"))
rows = db.execute("SELECT ms, t, h FROM readings ORDER BY ms").fetchall()
check("SQLite に 5 行(温度 2350・湿度 6100)", ([(t, h) for _, t, h in rows], len(rows)), ([(2350, 6100)] * 5, 5))
ms = [m for m, _, _ in rows]
check("時刻(ms)が増えていき、間隔はおよそ PERIOD(300 ms)", (ms == sorted(ms), all(250 <= y - x <= 700 for x, y in zip(ms, ms[1:]))), (True, True))
check("終わりに集計を出す", any(x.startswith("記録 件数・最低・最高(×100): 5\t2350\t2350") for x in lines), True)
db.close()

# 2 回目の実行: 記録は追記される(CREATE TABLE IF NOT EXISTS)
r2, root2 = demo(b.port, ["--i2c=aht25:-3,40", "--gpio=fake"], cycles=2, period=200)
db = sqlite3.connect(os.path.join(root2, "iot.db")); n1 = db.execute("SELECT count(*) FROM readings").fetchone()[0]; db.close()
check("別のフォルダなら別の記録", n1, 2)
# 同じフォルダで 2 回
def twice():
    out = []
    root = tempfile.mkdtemp()
    for _ in range(2):
        src = open(os.path.join(HERE, "iot_demo.sn"), encoding="utf-8").read().replace("PORT : 1883", f"PORT : {b.port}").replace("CYCLES : 6", "CYCLES : 2").replace("PERIOD : 1000", "PERIOD : 200")
        fd, p = tempfile.mkstemp(prefix="_iot_t", suffix=".sn", dir=HERE); os.close(fd); open(p, "w", encoding="utf-8").write(src)     # 名前は実行ごとに別(同時に動かしても取り合わない)
        try: subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p, f"--db={root}", "--net=local", "--i2c=aht25:20,50", "--gpio=fake"], capture_output=True, text=True, timeout=60, cwd=HERE)
        finally: os.unlink(p)
    db = sqlite3.connect(os.path.join(root, "iot.db")); n = db.execute("SELECT count(*) FROM readings").fetchone()[0]; db.close(); return n
check("同じフォルダで 2 回動かすと記録が積み上がる(2+2)", twice(), 4)
b.srv.close()

# --- 失敗の道 ---
s = socket.socket(); s.bind(("127.0.0.1", 0)); dead = s.getsockname()[1]; s.close()
r, _ = demo(dead, ["--i2c=aht25:23.5,61", "--gpio=fake"], cycles=1)
check("ブローカーが居ない: メッセージを出して終わる", r.stdout.splitlines()[0], "ブローカーにつなげません: -111")
b = B.Broker(port=0, out=io.StringIO())
r, _ = demo(b.port, ["--i2c=fake:0x48", "--gpio=fake"], cycles=1)
check("センサーが居ない: 'センサーが使えません: -6'", r.stdout.splitlines()[0], "センサーが使えません: -6")
r, _ = demo(b.port, ["--i2c=aht25:23.5,61,badcrc", "--gpio=fake"], cycles=2, period=200)
check("センサーが壊れたデータ(CRC)を返しても止まらず次の回へ", (r.stdout.count("センサーのエラー: -74"), r.returncode), (2, 0))
b.srv.close()

print("\n全部 ok" if not bad else f"\n{bad} 件 NG"); sys.exit(1 if bad else 0)
