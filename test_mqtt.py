#!/usr/bin/env python3
"""mqtt.sn(Sign で書いた MQTT クライアント)の試験。自作の小さなブローカー(127.0.0.1)と、本物のインタープリタ・ネットワーク装置で確かめる。python test_mqtt.py"""
import os, socket, subprocess, sys, tempfile, threading, time
HERE = os.path.dirname(os.path.abspath(__file__))

bad = 0
def check(name, got, want):
    global bad
    ok = got == want; bad += not ok
    print(("ok  " if ok else "NG  ") + name + ("" if ok else f"\n    得た: {got!r}\n    期待: {want!r}"))

def exact(c, n):
    d = b""
    while len(d) < n:
        x = c.recv(n - len(d))
        if not x: raise OSError("閉じた")
        d += x
    return d
def read_packet(c):
    b0 = exact(c, 1)[0]; n, mult = 0, 1
    while True:
        b = exact(c, 1)[0]; n += (b & 127) * mult; mult *= 128
        if not b & 128: break
    return b0, exact(c, n) if n else b""
def rl(n):
    out = b""
    while True:
        b, n = n % 128, n // 128
        out += bytes([b | 128 if n else b])
        if not n: return out
def packet(b0, body): return bytes([b0]) + rl(len(body)) + body
def u16s(b): return len(b).to_bytes(2, "big") + b
def match(flt, topic):
    f, t = flt.split("/"), topic.split("/")
    for i, x in enumerate(f):
        if x == "#": return True
        if i >= len(t) or (x != "+" and x != t[i]): return False
    return len(f) == len(t)

class Broker:
    """MQTT 3.1.1 の最小のブローカー(試験用)。"""
    def __init__(self, rc=0, auth=None, suback=None, connack=None):
        self.rc, self.auth, self.suback, self.connack_override = rc, auth, suback, connack
        self.srv = socket.socket(); self.srv.bind(("127.0.0.1", 0)); self.srv.listen(5); self.port = self.srv.getsockname()[1]
        self.clients, self.log, self.pubs, self.acks, self.subs, self.raw = [], [], [], [], {}, []
        self.lock = threading.Lock()
        threading.Thread(target=self.accept, daemon=True).start()
    def accept(self):
        try:
            while True:
                c, _ = self.srv.accept(); self.clients.append(c)
                threading.Thread(target=self.handle, args=(c,), daemon=True).start()
        except OSError: pass
    def handle(self, c):
        try:
            while True:
                b0, body = read_packet(c); t = b0 >> 4; self.raw.append(packet(b0, body)); self.log.append(t)
                if t == 1:
                    pl = int.from_bytes(body[0:2], "big"); i = 2 + pl + 4; keep = int.from_bytes(body[i - 2:i], "big"); flags = body[i - 3]
                    cl = int.from_bytes(body[i:i + 2], "big"); cid = body[i + 2:i + 2 + cl]; i += 2 + cl; user = pw = None
                    if flags & 0x80: ul = int.from_bytes(body[i:i + 2], "big"); user = body[i + 2:i + 2 + ul].decode(); i += 2 + ul
                    if flags & 0x40: pl2 = int.from_bytes(body[i:i + 2], "big"); pw = body[i + 2:i + 2 + pl2].decode()
                    self.hello = dict(cid=cid.decode(), keep=keep, flags=flags, user=user, pw=pw)
                    rc = self.rc if self.auth is None or (user, pw) == self.auth else 4
                    c.sendall(self.connack_override or bytes([0x20, 2, 0, rc]))
                elif t == 3:
                    qos = (b0 >> 1) & 3; tl = int.from_bytes(body[0:2], "big"); topic = body[2:2 + tl].decode(); i = 2 + tl
                    pid = body[i:i + 2] if qos else b""; payload = body[i + len(pid):]
                    self.pubs.append((topic, payload, qos, b0 & 1))
                    if qos == 1: c.sendall(bytes([0x40, 2]) + pid)
                    for sc, flt, sq in list(self.subs.values()):
                        if match(flt, topic): self.deliver(sc, topic, payload, min(qos, sq))
                elif t == 4: self.acks.append(body)
                elif t == 8:
                    pid = body[0:2]; i = 2; granted = b""
                    while i < len(body):
                        fl = int.from_bytes(body[i:i + 2], "big"); flt = body[i + 2:i + 2 + fl].decode(); q = body[i + 2 + fl]; i += 3 + fl
                        self.subs[(id(c), flt)] = (c, flt, q); granted += bytes([self.suback if self.suback is not None else q])
                    c.sendall(packet(0x90, pid + granted))
                elif t == 12: c.sendall(bytes([0xD0, 0]))
                elif t == 14: c.close(); return
        except OSError: pass
    def deliver(self, c, topic, payload, qos=0, pid=77):
        body = u16s(topic.encode()) + (pid.to_bytes(2, "big") if qos else b"") + payload
        c.sendall(packet(0x30 | (qos << 1), body))
    def publish_all(self, topic, payload, qos=0):
        for c in list(self.clients): self.deliver(c, topic, payload, qos)
    def wait(self, cond, secs=5):
        end = time.time() + secs
        while time.time() < end:
            if cond(): return True
            time.sleep(0.02)
        return cond()
    def close_clients(self):
        for c in self.clients:
            try: c.shutdown(socket.SHUT_RDWR)
            except OSError: pass
            c.close()
    def stop(self): self.srv.close(); self.close_clients()

TMP = tempfile.mkdtemp()
def sign(body, port, flags=()):
    src = f"`{os.path.join(HERE, 'mqtt.sn')}`@~\n\nHB : 0x600000\nPLOAD : 0x610000\n" \
          "tcp : z ? seq2 (str_put HB `127.0.0.1`) (mq_net 1 HB 9 " + str(port) + " 0 0 0)\n" + body + "\n"
    p = os.path.join(TMP, "t.sn"); open(p, "w", encoding="utf-8").write(src)
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p, "--net=local", *flags], capture_output=True, timeout=60)
    return r.stdout.decode().replace("\r", "").split("\n"), r.stderr.decode().strip()
def vals(body, port):
    out, err = sign(body, port); return [x for x in out if x != ""], err
def run_async(body, port):                                    # 動かしたまま、こちらからブローカーを操作する
    p = os.path.join(TMP, "a.sn"); src = f"`{os.path.join(HERE, 'mqtt.sn')}`@~\n\nHB : 0x600000\nPLOAD : 0x610000\ntcp : z ? seq2 (str_put HB `127.0.0.1`) (mq_net 1 HB 9 {port} 0 0 0)\n{body}\n"
    open(p, "w", encoding="utf-8").write(src)
    return subprocess.Popen([sys.executable, os.path.join(HERE, "sign.py"), p, "--net=local"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)

# --- 規格の例(MQTT 3.1.1)で、残りの長さの符号化 ---
for n, want in ((0, [0]), (127, [127]), (128, [128, 1]), (16383, [255, 127]), (16384, [128, 128, 1]), (2097151, [255, 255, 127])):
    out, err = sign(f"main : z ? seq2 (mq_rl MQ_OUT 0 {n}) (mq_dump {len(want)})\nmq_dump : k ?\n\tk < 1 : 0\n\tseq2 (mq_dump (k - 1)) (println_int (@(MQ_OUT + ((k - 1) * 4))))\nmain 0", 1)
    check(f"残りの長さ {n} の符号化(規格の例)", [int(x) for x in out if x.lstrip('-').isdigit()][:len(want)], want)

# --- つなぐ ---
b = Broker()
out, err = vals("seq2 (println_int (mqtt_connect (tcp 0) `sign1` 60)) 0", b.port)
check("CONNECT: 受け付けられて 0(CONNACK を読む)", (out[0], err), ("0", ""))
check("CONNECT のバイト列は規格どおり(10 11 00 04 MQTT 04 02 003C 0005 sign1)", b.raw[0], bytes([0x10, 0x11, 0, 4]) + b"MQTT" + bytes([4, 2, 0, 60, 0, 5]) + b"sign1")
check("ブローカーから見たクライアント情報", b.hello, dict(cid="sign1", keep=60, flags=2, user=None, pw=None))
b.stop()
b = Broker(auth=("bob", "pw"))
out, err = vals("seq4 (println_int (mqtt_connect_auth (tcp 0) `c2` `bob` `pw` 30)) 0 0 0", b.port)
check("CONNECT(ユーザー名・パスワード): 認証が通って 0・フラグ 0xC2", (out[0], b.hello["flags"], b.hello["user"], b.hello["pw"]), ("0", 0xC2, "bob", "pw"))
b.stop()
b = Broker(auth=("bob", "pw"))
out, err = vals("seq2 (println_int (mqtt_connect_auth (tcp 0) `c2` `bob` `bad` 30)) 0", b.port)
check("CONNECT: パスワードが違えば戻りコード 4", out[0], "4")
b.stop()
b = Broker(rc=5)
out, err = vals("seq2 (println_int (mqtt_connect (tcp 0) `x` 10)) 0", b.port)
check("CONNECT: 認可なし(5)", out[0], "5")
b.stop()
b = Broker(connack=bytes([0x30, 2, 0, 0]))
out, err = vals("seq2 (println_int (mqtt_connect (tcp 0) `x` 10)) 0", b.port)
check("CONNECT: CONNACK でない返事は -74", out[0], "-74")
b.stop()
s = socket.socket(); s.bind(("127.0.0.1", 0)); dead = s.getsockname()[1]; s.close()
out, err = vals("seq2 (println_int (tcp 0)) 0", dead)
check("つながらないときは、ネットワーク装置のエラー -111 がハンドルの代わりに返る(呼ぶ側が負かどうかを見る)", out[0] if out else err, "-111")
out, err = vals("seq2 (println_int (mqtt_connect (0 - 111) `x` 10)) 0", dead)
check("負のハンドルを渡すと装置の -9(EBADF)がそのまま出る(固まらない)", out[0], "-9")

# --- 出す ---
b = Broker()
out, err = vals("main : h ? seq4 (mqtt_connect h `p` 60) (println_int (mqtt_publish h `a/b` `hi` 0 0)) (println_int (mqtt_publish h `t/r` `x` 0 1)) (println_int (mqtt_publish_int h `n` (0 - 42) 0 0))\nmain (tcp 0)", b.port)
b.wait(lambda: len(b.pubs) >= 3)
check("PUBLISH QoS 0 の結果 0 とブローカーが受け取った内容(トピック・本文・QoS・保持)", (out[:3], b.pubs), (["0", "0", "0"], [("a/b", b"hi", 0, 0), ("t/r", b"x", 0, 1), ("n", b"-42", 0, 0)]))
check("PUBLISH のバイト列は規格どおり(30 07 0003 a/b hi)", b.raw[1], bytes([0x30, 7, 0, 3]) + b"a/b" + b"hi")
check("保持つきの先頭バイトは 0x31", b.raw[2][0], 0x31)
b.stop()
b = Broker()
out, err = vals("main : h ? seq4 (mqtt_connect h `p` 60) (println_int (mqtt_publish h `q1` `data` 1 0)) (println_int (mqtt_publish h `q1` `more` 1 1)) 0\nmain (tcp 0)", b.port)
check("PUBLISH QoS 1: PUBACK を待って 0(パケット番号は 1 から増える)", (out[:2], [(x[0] >> 1) & 3 for x in b.raw[1:3]], [x[len(x) - 6:len(x) - 4] for x in b.raw[1:3]]), (["0", "0"], [1, 1], [bytes([0, 1]), bytes([0, 2])]) )
check("QoS 1 の先頭バイト 0x32・0x33(保持)", (b.raw[1][0], b.raw[2][0]), (0x32, 0x33))
b.stop()
b = Broker()
big = 5000
out, err = vals(f"main : h ? seq4 (mqtt_connect h `big` 60) (arr_fill PLOAD {big} 65) (println_int (mqtt_publish_bytes h (mq_lit MQ_S1 `big/t`) PLOAD {big} 0 0)) 0\nmain (tcp 0)", b.port)
b.wait(lambda: b.pubs)
check("大きな本文 5000 バイト(残りの長さが 2 バイト)", (out[0], len(b.pubs[0][1]), set(b.pubs[0][1]), b.raw[1][1:3]), ("0", big, {65}, rl(5000 + 2 + 5)))
b.stop()
b = Broker()
out, err = vals("main : h ? seq5 (mqtt_connect h `p` 60) (println_int (mqtt_publish h `t` `x` 2 0)) (println_int (mqtt_publish h `t` `x` 0 - 1 0)) (seq2 (MQ_S1 # 0) (println_int (mqtt_publish_mem h MQ_S1 (mq_lit MQ_S2 `x`) 0 0))) (println_int (mqtt_publish_bytes h (mq_lit MQ_S1 `t`) PLOAD 8000 0 0)) 0\nmain (tcp 0)", b.port)
# 空のトピック・フィルタは、空の文字列 `` を書くと値の口で消えて引数が足りなくなる(R83・R105)ので、メモリに終端の 0 だけを書いて作る
check("PUBLISH の引数の検査: QoS 2 は -22、トピックが空 -22、大きすぎは -90", (out[0], out[2], out[3], b.pubs), ("-22", "-22", "-90", []))
b.stop()

# --- 受ける ---
b = Broker()
p = run_async("main : h ? seq5 (mqtt_connect h `s` 60) (println_int (mqtt_subscribe h `sensors/#` 1)) (println_int (mqtt_poll h 5000)) (println_mem MQ_TOPIC) (seq3 (println_mem MQ_PAYLOAD) (println_int (@MQ_PLEN)) 0)\nmain (tcp 0)", b.port)
b.wait(lambda: b.subs)
time.sleep(0.2); b.publish_all("sensors/temp", b"23.5", qos=1)
out = p.communicate(timeout=20)[0].decode().split()
check("SUBSCRIBE: 許された QoS 1、メッセージ(3)が来てトピック・本文・長さが読める", out[:5], ["1", "3", "sensors/temp", "23.5", "4"])
check("SUBSCRIBE のバイト列(82 0F 0001 0009 sensors/# 01)", b.raw[1], bytes([0x82, 2 + 2 + 9 + 1, 0, 1]) + u16s(b"sensors/#") + bytes([1]))
check("QoS 1 のメッセージに自動で PUBACK(パケット番号 77)", b.wait(lambda: b.acks) and b.acks[0], bytes([0, 77]))
b.stop()
b = Broker(suback=128)
out, err = vals("main : h ? seq2 (mqtt_connect h `s` 60) (println_int (mqtt_subscribe h `x/y` 0))\nmain (tcp 0)", b.port)
check("SUBSCRIBE: 断られると 128", out[0], "128")
out, err = vals("main : h ? seq4 (mqtt_connect h `s` 60) (println_int (mqtt_subscribe h `x` 2)) (seq2 (MQ_S1 # 0) (println_int (mqtt_subscribe_mem h MQ_S1 0))) 0\nmain (tcp 0)", b.port)
check("SUBSCRIBE の引数の検査: QoS 2・空のフィルタは -22", out[:2], ["-22", "-22"])
b.stop()
b = Broker()
p = run_async("main : h ? seq5 (mqtt_connect h `s` 60) (mqtt_subscribe h `#` 0) (println_int (mqtt_poll h 5000)) (println_int (@MQ_PLEN)) (println_int (str_len MQ_PAYLOAD))\nmain (tcp 0)", b.port)
b.wait(lambda: b.subs); time.sleep(0.2); b.publish_all("big", b"B" * 3000)
out = p.communicate(timeout=20)[0].decode().split()
check("大きなメッセージ 3000 バイトを受け取る", out[:3], ["3", "3000", "3000"])
b.stop()
b = Broker()
p = run_async("main : h ? seq3 (mqtt_connect h `s` 60) (mqtt_subscribe h `#` 0) (println_int (mqtt_poll h 5000))\nmain (tcp 0)", b.port)
b.wait(lambda: b.subs); time.sleep(0.2); b.publish_all("huge", b"H" * 9000)
out = p.communicate(timeout=20)[0].decode().split()
check("大きすぎるメッセージ(9000 バイト)は -90", out[:1], ["-90"])
b.stop()

# --- 保つ・待つ ---
b = Broker()
out, err = vals("main : h ? seq5 (mqtt_connect h `k` 60) (println_int (mqtt_poll h 0)) (println_int (mqtt_poll h 50)) (println_int (mqtt_ping h)) (println_int (mqtt_poll h 3000))\nmain (tcp 0)", b.port)
check("何も来なければ POLL は 0(待たない・50 ミリ秒待つ)、PING のあと PINGRESP(13)", out[:4], ["0", "0", "0", "13"])
check("PINGREQ のバイト列(C0 00)", b.raw[1], bytes([0xC0, 0]))
b.stop()
b = Broker()
out, err = vals("main : h ? seq3 (mqtt_connect h `d` 60) (println_int (mqtt_disconnect h)) 0\nmain (tcp 0)", b.port)
check("DISCONNECT のバイト列(E0 00)", (out[0], b.wait(lambda: len(b.raw) >= 2) and b.raw[1]), ("0", bytes([0xE0, 0])))
b.stop()
b = Broker()
p = run_async("main : h ? seq3 (mqtt_connect h `s` 60) (mqtt_subscribe h `#` 0) (println_int (mqtt_poll h 5000))\nmain (tcp 0)", b.port)
b.wait(lambda: b.subs); time.sleep(0.2); b.close_clients()
out = p.communicate(timeout=20)[0].decode().split()
check("ブローカーが閉じたら POLL は -104", out[:1], ["-104"])
b.stop()
b = Broker()
p = run_async("main : h ? seq3 (mqtt_connect h `s` 60) (println_int (mqtt_publish h `t` `x` 1 0)) 0\nmain (tcp 0)", b.port)
b.wait(lambda: b.pubs); b.stop()
check("(参考)ブローカーが QoS 1 に答える前に落ちたら、待ち時間切れかエラーで終わる(固まらない)", p.wait(timeout=30) is not None, True)
print("\n" + ("全部通った" if not bad else f"{bad} 件 食い違い")); sys.exit(1 if bad else 0)
