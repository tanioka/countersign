"""fake_mqtt.py — 試験用の小さな MQTT 3.1.1 ブローカー(test_mqtt.py と同じ物。asm 版の突き合わせ test_asm_net.py でも使う)。"""
import socket, threading, time

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

