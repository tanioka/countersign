#!/usr/bin/env python3
"""iot_broker.py — 練習用の小さな MQTT 3.1.1 ブローカー(本物の Mosquitto などの代わり。仕様に無い追加の道具)。
  python3 iot_broker.py [--host 127.0.0.1] [--port 1883] [--inject 秒:トピック:本文 ...]
  届いた PUBLISH を「[秒] トピック = 本文」と出す。QoS 0・1、購読(+ と # のワイルドカード)、保持(retain)、PINGREQ に対応。
  --inject 3:sign/iot/cmd/threshold:2000 は、起動して 3 秒後に、そのトピックの購読者へ本文を送る(何回でも書ける)。
  守り: 既定は自分のパソコン(127.0.0.1)だけで待つ。認証・暗号化・QoS 2・Will・セッションの引き継ぎは無い(練習用)。"""
import argparse, socket, sys, threading, time


def read_exact(c, n):
    d = b""
    while len(d) < n:
        x = c.recv(n - len(d))
        if not x: raise OSError("閉じた")
        d += x
    return d

def read_packet(c):
    b0 = read_exact(c, 1)[0]; n, mult = 0, 1
    while True:
        b = read_exact(c, 1)[0]; n += (b & 127) * mult; mult *= 128
        if not b & 128: break
        if mult > 128 ** 3: raise OSError("長すぎる")
    return b0, read_exact(c, n) if n else b""

def rl(n):
    out = bytearray()
    while True:
        b, n = n % 128, n // 128
        out.append(b | (128 if n else 0))
        if not n: return bytes(out)

def packet(b0, body): return bytes([b0]) + rl(len(body)) + body

def match(flt, topic):
    f, t = flt.split("/"), topic.split("/")
    for i, x in enumerate(f):
        if x == "#": return True
        if i >= len(t) or (x != "+" and x != t[i]): return False
    return len(f) == len(t)


class Broker:
    def __init__(self, host="127.0.0.1", port=1883, out=None):
        self.srv = socket.socket(); self.srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.srv.bind((host, port)); self.srv.listen(8); self.port = self.srv.getsockname()[1]
        self.subs, self.retained, self.pubs, self.lock, self.t0 = {}, {}, [], threading.Lock(), time.time()
        self.out = out or sys.stdout
        threading.Thread(target=self.accept, daemon=True).start()

    def say(self, s):
        print(f"[{time.time() - self.t0:5.1f}] {s}", file=self.out, flush=True)

    def accept(self):
        try:
            while True:
                c, _ = self.srv.accept()
                threading.Thread(target=self.handle, args=(c,), daemon=True).start()
        except OSError: pass

    def send(self, c, data):
        try:
            with self.lock: c.sendall(data)
        except OSError: pass

    def deliver(self, c, topic, payload, qos=0, retain=0, pid=1):
        t = topic.encode()
        self.send(c, packet(0x30 | (qos << 1) | retain, len(t).to_bytes(2, "big") + t + (pid.to_bytes(2, "big") if qos else b"") + payload))

    def inject(self, topic, payload):
        self.say(f"(命令) {topic} = {payload.decode(errors='replace')}")
        for (cid, flt), (c, q) in list(self.subs.items()):
            if match(flt, topic): self.deliver(c, topic, payload, 0)

    def handle(self, c):
        try:
            while True:
                b0, body = read_packet(c); t = b0 >> 4
                if t == 1: self.send(c, bytes([0x20, 2, 0, 0]))
                elif t == 3:
                    qos = (b0 >> 1) & 3; tl = int.from_bytes(body[0:2], "big"); topic = body[2:2 + tl].decode(errors="replace"); i = 2 + tl
                    pid = body[i:i + 2] if qos else b""; payload = body[i + len(pid):]
                    self.pubs.append((topic, payload)); self.say(f"{topic} = {payload.decode(errors='replace')}")
                    if qos == 1: self.send(c, bytes([0x40, 2]) + pid)
                    if b0 & 1:
                        if payload: self.retained[topic] = payload
                        else: self.retained.pop(topic, None)
                    for (cid, flt), (sc, sq) in list(self.subs.items()):
                        if match(flt, topic): self.deliver(sc, topic, payload, 0)
                elif t == 8:
                    pid = body[0:2]; i = 2; granted = b""; new = []
                    while i < len(body):
                        fl = int.from_bytes(body[i:i + 2], "big"); flt = body[i + 2:i + 2 + fl].decode(errors="replace"); q = min(body[i + 2 + fl], 1); i += 3 + fl
                        self.subs[(id(c), flt)] = (c, q); granted += bytes([q]); new.append(flt)
                    self.send(c, packet(0x90, pid + granted))
                    for flt in new:
                        for tp, pl in list(self.retained.items()):
                            if match(flt, tp): self.deliver(c, tp, pl, 0, 1)
                elif t == 12: self.send(c, bytes([0xD0, 0]))
                elif t == 14: break
        except OSError: pass
        finally:
            for k in [k for k in self.subs if k[0] == id(c)]: self.subs.pop(k, None)
            try: c.close()
            except OSError: pass


def main():
    ap = argparse.ArgumentParser(description="練習用の小さな MQTT ブローカー")
    ap.add_argument("--host", default="127.0.0.1"); ap.add_argument("--port", type=int, default=1883)
    ap.add_argument("--inject", action="append", default=[], metavar="秒:トピック:本文")
    a = ap.parse_args()
    jobs = []
    for x in a.inject:
        try: s, topic, payload = x.split(":", 2); jobs.append((float(s), topic, payload.encode()))
        except ValueError: ap.error(f"--inject は 秒:トピック:本文 の形で書く: {x}")
    b = Broker(a.host, a.port)
    b.say(f"待っています {a.host}:{b.port}(止めるのは Ctrl+C)")
    for s, topic, payload in sorted(jobs):
        d = s - (time.time() - b.t0)
        if d > 0: time.sleep(d)
        b.inject(topic, payload)
    try:
        while True: time.sleep(3600)
    except KeyboardInterrupt: pass

if __name__ == "__main__": main()
