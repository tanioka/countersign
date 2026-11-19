#!/usr/bin/env python3
"""ネットワーク装置(sign_net.py)の試験。自分のパソコンの中(127.0.0.1)の通信だけを使う。外には出ない。python test_net.py"""
import os, socket, subprocess, sys, tempfile, threading, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import sign_net as N

bad = 0
def check(name, got, want):
    global bad
    ok = got == want; bad += not ok
    print(("ok  " if ok else "NG  ") + name + ("" if ok else f"\n    得た: {got!r}\n    期待: {want!r}"))

BUF, HB, FB = 0x600000, 0x610000, 0x620000
def dev(allow=None):
    d = N.Net(allow); d.mem = {}; return d
def put(d, data, buf):
    for i, b in enumerate(data): d.mem[buf + 4 * i] = b
def get(d, n, buf=BUF): return bytes(d.mem[buf + 4 * i] for i in range(n))
def cstr(d, buf): 
    out = bytearray(); i = 0
    while d.mem.get(buf + 4 * i): out.append(d.mem[buf + 4 * i]); i += 1
    return out.decode()
def call(d, nr, *a):
    d.write(N.NR, nr)
    for k, v in zip((N.A0, N.A1, N.A2, N.A3, N.A4, N.A5), a): d.write(k, v)
    d.write(N.GO, 1); return d.read(N.RET)
def connect(d, host, port):
    put(d, host.encode(), HB); return call(d, 1, HB, len(host), port)
def server():
    s = socket.socket(); s.bind(("127.0.0.1", 0)); s.listen(5); return s, s.getsockname()[1]

# --- TCP クライアント ---
srv, port = server()
conns = []
threading.Thread(target=lambda: conns.append(srv.accept()[0]), daemon=True).start()
d = dev()
h = connect(d, "127.0.0.1", port)
check("CONNECT: ハンドル(1 以上)", h >= 1, True)
time.sleep(0.1)
put(d, b"hello", BUF)
check("SEND: 送ったバイト数", call(d, 2, h, BUF, 5), 5)
check("サーバーに届く", conns[0].recv(100), b"hello")
conns[0].sendall(b"world!")
check("RECV: 受け取った数と中身", (call(d, 3, h, FB, 100), get(d, 6, FB)), (6, b"world!"))
check("SETTIMEOUT 50ms で何も来なければ RECV は -11", (call(d, 10, h, 50), call(d, 3, h, FB, 10)), (0, -11))
check("SETTIMEOUT 0(待たない)でも -11", (call(d, 10, h, 0), call(d, 3, h, FB, 10)), (0, -11))
check("SETTIMEOUT の負の値は -22", call(d, 10, h, -1), -22)
call(d, 10, h, 1000)
check("PORT: 自分側のポート番号", call(d, 12, h) > 0, True)
conns[0].close()
check("RECV: 相手が閉じたら 0", call(d, 3, h, FB, 10), 0)
check("CLOSE: 0、閉じたあとは -9(EBADF)", (call(d, 4, h), call(d, 4, h), call(d, 2, h, BUF, 1)), (0, -9, -9))
srv.close()
s2, p2 = server(); s2.close()
check("CONNECT: 閉じたポートは -111", connect(d, "127.0.0.1", p2), -111)
# --- 引数の検査 ---
check("CONNECT: ポートが範囲外は -22", (connect(d, "127.0.0.1", 0), connect(d, "127.0.0.1", 70000)), (-22, -22))
put(d, b"a b", HB); check("ホスト名に空白は -22", call(d, 1, HB, 3, 80), -22)
check("ホスト名が長すぎる(255 超)は -22", call(d, 1, HB, 300, 80), -22)
check("ホスト名の長さ 0 は -22", call(d, 1, HB, 0, 80), -22)
check("ホスト名のバッファが未書き込みは -22", call(d, 1, 0x700000, 5, 80), -22)
check("知らないハンドルは -9", (call(d, 2, 99, BUF, 1), call(d, 3, 99, BUF, 1), call(d, 6, 99), call(d, 10, 99, 5)), (-9, -9, -9, -9))
check("知らない番号は -38", call(d, 99), -38)
before = dict(d.reg); d.write(N.A0, True); d.write(N.A1, "x"); d.write(N.A2, None)
check("整数でない書き込み(bool・文字列・unit)は捨てる", d.reg, before)
# --- TCP サーバー ---
d = dev("local")
l = call(d, 5, 0, 5)
lp = call(d, 12, l)
check("LISTEN: port 0 で空いている番号を選び、PORT で聞ける", (l >= 1, lp > 0), (True, True))
check("ACCEPT: 誰も来ていなければ -11", (call(d, 10, l, 0), call(d, 6, l)), (0, -11))
cl = socket.create_connection(("127.0.0.1", lp)); time.sleep(0.1)
c = call(d, 6, l)
check("ACCEPT: 来た接続のハンドル", c >= 1 and c != l, True)
call(d, 10, c, 1000); cl.sendall(b"ping")
check("サーバー側の RECV", (call(d, 3, c, BUF, 100), get(d, 4)), (4, b"ping"))
put(d, b"pong", BUF); call(d, 2, c, BUF, 4)
check("サーバー側の SEND がクライアントに届く", cl.recv(10), b"pong")
check("--net=local の待ち受けは 127.0.0.1 だけ", d.socks[l].getsockname()[0], "127.0.0.1")
cl.close()
d.release(); check("release: ソケットを全部閉じる", d.socks, {})
check("LISTEN: ポートが範囲外は -22", call(dev(), 5, 70000, 5), -22)
d1, d2 = dev(), dev(); a = call(d1, 5, 0, 5); pa = call(d1, 12, a); b = call(d2, 5, pa, 5)
check("LISTEN: 使用中のポートは -98(EADDRINUSE)(または Windows の相当)", b, -98)
d1.release(); d2.release()
# --- UDP ---
d = dev("local"); u = call(d, 7, 0); up = call(d, 12, u)
cu = socket.socket(socket.AF_INET, socket.SOCK_DGRAM); cu.bind(("127.0.0.1", 0)); cu.settimeout(2)
check("UDP_OPEN", u >= 1 and up > 0, True)
check("RECVFROM: 来ていなければ -11", (call(d, 10, u, 0), call(d, 9, u, BUF, 100, FB)), (0, -11))
call(d, 10, u, 1000); cu.sendto(b"udp-hello", ("127.0.0.1", up))
n = call(d, 9, u, BUF, 100, FB)
check("RECVFROM: 中身と送り主(ア.ド.レ.ス:ポート)", (n, get(d, 9), cstr(d, FB)), (9, b"udp-hello", f"127.0.0.1:{cu.getsockname()[1]}"))
put(d, b"127.0.0.1", HB); put(d, b"back", BUF)
check("SENDTO", (call(d, 8, u, HB, 9, cu.getsockname()[1], BUF, 4), cu.recvfrom(10)[0]), (4, b"back"))
d.release(); cu.close()
# --- 名前の解決 ---
d = dev(); put(d, b"localhost", HB)
r = call(d, 11, HB, 9, FB)
check("RESOLVE: localhost → 127.0.0.1", (r, cstr(d, FB)), (9, "127.0.0.1"))
check("RESOLVE: 引けない名前は -2", (put(d, b"nonexistent.invalid", HB), call(d, 11, HB, 19, FB))[1], -2)
# --- 許可 ---
dl = dev("local")
check("--net=local: 外の名前への CONNECT・SENDTO・RESOLVE は -13", (connect(dl, "example.com", 80), (put(dl, b"example.com", HB), call(dl, 11, HB, 11, FB))[1], (put(dl, b"hi", BUF), call(dl, 8, call(dl, 7, 0), HB, 11, 9, BUF, 2))[1]), (-13, -13, -13))
check("--net=local: localhost・127.0.0.1 は通る", (put(dl, b"localhost", HB), call(dl, 11, HB, 9, FB))[1], 9)
da = dev("example.com, 127.0.0.1")
check("--net=名前,…: 並べた名前と、その名前が引いた先のアドレスで判断(localhost は 127.0.0.1 を引くので通る)", (put(da, b"localhost", HB), call(da, 11, HB, 9, FB))[1], 9)
check("--net=名前,…: 並べていない名前は -13", (put(da, b"example.org", HB), call(da, 11, HB, 11, FB))[1], -13)
check("--net=名前,…: 待ち受けは 127.0.0.1 だけ", da.socks[call(da, 5, 0, 5)].getsockname()[0], "127.0.0.1")
dd = dev(); check("--net(許可を絞らない)の待ち受けは 0.0.0.0", dd.socks[call(dd, 5, 0, 5)].getsockname()[0], "0.0.0.0"); dd.release()
# --- ハンドルの上限 ---
d = dev("local"); hs = [call(d, 7, 0) for _ in range(34)]
check("同時に 32 まで。33 個目は -24(EMFILE)", (hs[:32] == list(range(1, 33)), hs[32:]), (True, [-24, -24]))
d.release()

# --- Sign から(本物のインタープリタ) ---
def sign_server(script, port):
    src = open(os.path.join(HERE, script), encoding="utf-8").read()
    return src
srv, port = server()
def handler():
    c, _ = srv.accept(); data = c.recv(4096); c.sendall(b"HTTP/1.0 200 OK\r\nX: " + data.split(b"\r\n")[0] + b"\r\nHost-seen: " + data.split(b"Host: ")[1].split(b"\r\n")[0] + b"\r\n\r\nhello\r\n"); c.close()
threading.Thread(target=handler, daemon=True).start()
src = open(os.path.join(HERE, "http_get.sn"), encoding="utf-8").read().replace("`example.com`", "`127.0.0.1`").replace("PORT : 80", f"PORT : {port}").replace("`std.sn`", f"`{os.path.join(HERE, 'std.sn')}`")
tmp = tempfile.mkdtemp(); p = os.path.join(tmp, "g.sn"); open(p, "w", encoding="utf-8").write(src)
r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p, "--net=local"], capture_output=True, timeout=30)
out = r.stdout.decode()
check("http_get.sn: GET / HTTP/1.0 と Host ヘッダを送り、返事を出す", ("HTTP/1.0 200 OK" in out, "X: GET / HTTP/1.0" in out, "Host-seen: 127.0.0.1" in out, "hello" in out), (True, True, True, True))
r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p], capture_output=True, timeout=30)
check("--net を付けないと装置が無い(つなげないので何も出ない)", "HTTP/1.0 200" in r.stdout.decode(), False)
r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p, "--net=example.com"], capture_output=True, timeout=30)
check("許可の外(--net=example.com で 127.0.0.1 へ)は -13 と出る", "エラー -13" in r.stdout.decode(), True)
# echo_server.sn
_, fp = server()
src = open(os.path.join(HERE, "echo_server.sn"), encoding="utf-8").read().replace("PORT : 9000", f"PORT : {fp}").replace("`std.sn`", f"`{os.path.join(HERE, 'std.sn')}`")
p = os.path.join(tmp, "e.sn"); open(p, "w", encoding="utf-8").write(src)
proc = subprocess.Popen([sys.executable, os.path.join(HERE, "sign.py"), p, "--net=local"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
cl = None
for _ in range(100):
    try: cl = socket.create_connection(("127.0.0.1", fp), timeout=2); break
    except OSError: time.sleep(0.1)
if cl:
    cl.sendall(b"echo me"); got = cl.recv(100); cl.sendall(b"again"); got2 = cl.recv(100); cl.close()
else: got = got2 = None
try: out, err = proc.communicate(timeout=20)
except subprocess.TimeoutExpired: proc.kill(); out, err = proc.communicate()
check("echo_server.sn: 送ったものがそのまま返り、接続が閉じたら終わる", (got, got2, proc.returncode), (b"echo me", b"again", 0))

# ======================= TLS とプロキシ =======================
import ssl, select
CERTS = tempfile.mkdtemp()
def sh(*a): subprocess.run(a, cwd=CERTS, check=True, capture_output=True)
def make_certs():
    sh("openssl", "req", "-x509", "-newkey", "rsa:2048", "-nodes", "-keyout", "ca.key", "-out", "ca.pem", "-days", "2", "-subj", "/CN=Test CA", "-addext", "basicConstraints=critical,CA:TRUE", "-addext", "keyUsage=critical,keyCertSign")
    for name, san in (("srv", "DNS:localhost,IP:127.0.0.1"), ("wrongname", "DNS:other.example")):
        sh("openssl", "req", "-newkey", "rsa:2048", "-nodes", "-keyout", name + ".key", "-out", name + ".csr", "-subj", "/CN=" + name)
        open(os.path.join(CERTS, name + ".ext"), "w").write("subjectAltName=" + san + "\n")
        sh("openssl", "x509", "-req", "-in", name + ".csr", "-CA", "ca.pem", "-CAkey", "ca.key", "-CAcreateserial", "-out", name + ".pem", "-days", "2", "-extfile", name + ".ext")
    sh("openssl", "req", "-x509", "-newkey", "rsa:2048", "-nodes", "-keyout", "self.key", "-out", "self.pem", "-days", "2", "-subj", "/CN=localhost", "-addext", "subjectAltName=DNS:localhost,IP:127.0.0.1")
CA = os.path.join(CERTS, "ca.pem")
try: make_certs(); have_certs = True
except Exception as e: have_certs = False; print("(openssl が使えないので TLS の試験は飛ばします:", e, ")")

def tls_server(cert="srv"):
    ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER); ctx.load_cert_chain(os.path.join(CERTS, cert + ".pem"), os.path.join(CERTS, cert + ".key"))
    srv, port = server(); got = []
    def run():
        try:
            while True:
                c, _ = srv.accept()
                try:
                    t = ctx.wrap_socket(c, server_side=True); data = t.recv(4096); got.append(data); t.sendall(b"secure:" + data); t.settimeout(3); t.recv(1); t.close()
                except (ssl.SSLError, OSError): c.close()
        except OSError: pass
    threading.Thread(target=run, daemon=True).start()
    return srv, port, got

def relay(a, b):
    try:
        while True:
            r, _, _ = select.select([a, b], [], [], 5)
            if not r: return
            for x in r:
                data = x.recv(4096)
                if not data: return
                (b if x is a else a).sendall(data)
    except OSError: pass
    finally:
        a.close(); b.close()

def http_proxy(user=None, pw=None, status=None):
    srv, port = server(); log = []
    def handle(c):
        try:
            head = b""
            while b"\r\n\r\n" not in head: head += c.recv(1)
            lines = head.decode().split("\r\n"); method, target, _ = lines[0].split()
            log.append(target)
            auth = next((l.split(": ", 1)[1] for l in lines if l.lower().startswith("proxy-authorization")), None)
            import base64
            if status: c.sendall(f"HTTP/1.1 {status} X\r\n\r\n".encode()); c.close(); return
            if user is not None and auth != "Basic " + base64.b64encode(f"{user}:{pw}".encode()).decode():
                c.sendall(b"HTTP/1.1 407 Proxy Authentication Required\r\n\r\n"); c.close(); return
            h, p = target.rsplit(":", 1); up = socket.create_connection((h, int(p)), timeout=5)
            c.sendall(b"HTTP/1.1 200 Connection established\r\n\r\n"); relay(c, up)
        except Exception: c.close()
    def run():
        try:
            while True: threading.Thread(target=handle, args=(srv.accept()[0],), daemon=True).start()
        except OSError: pass
    threading.Thread(target=run, daemon=True).start()
    return srv, port, log

def socks_proxy(user=None, pw=None, names=None):
    srv, port = server(); log = []
    def exact(c, n):
        d = b""
        while len(d) < n:
            x = c.recv(n - len(d))
            if not x: raise OSError
            d += x
        return d
    def handle(c):
        try:
            ver, n = exact(c, 2); methods = exact(c, n)
            if user is not None:
                if 2 not in methods: c.sendall(b"\x05\xff"); c.close(); return
                c.sendall(b"\x05\x02"); exact(c, 1); ul = exact(c, 1)[0]; u = exact(c, ul).decode(); pl = exact(c, 1)[0]; p = exact(c, pl).decode()
                if (u, p) != (user, pw): c.sendall(b"\x01\x01"); c.close(); return
                c.sendall(b"\x01\x00")
            else: c.sendall(b"\x05\x00")
            _, cmd, _, atyp = exact(c, 4)
            host = exact(c, exact(c, 1)[0]).decode() if atyp == 3 else socket.inet_ntoa(exact(c, 4))
            port_ = int.from_bytes(exact(c, 2), "big"); log.append((atyp, host, port_))
            try: up = socket.create_connection(((names or {}).get(host, host), port_), timeout=5)
            except ConnectionRefusedError: c.sendall(b"\x05\x05\x00\x01\x00\x00\x00\x00\x00\x00"); c.close(); return
            c.sendall(b"\x05\x00\x00\x01\x00\x00\x00\x00\x00\x00"); relay(c, up)
        except Exception: c.close()
    def run():
        try:
            while True: threading.Thread(target=handle, args=(srv.accept()[0],), daemon=True).start()
        except OSError: pass
    threading.Thread(target=run, daemon=True).start()
    return srv, port, log

def plain_echo():
    srv, port = server()
    def run():
        try:
            while True:
                c, _ = srv.accept()
                try: c.sendall(b"echo:" + c.recv(100)); c.close()
                except OSError: pass
        except OSError: pass
    threading.Thread(target=run, daemon=True).start()
    return srv, port

def exchange(d, h, msg=b"hi"):
    put(d, msg, BUF); call(d, 2, h, BUF, len(msg)); n = call(d, 3, h, FB, 100)
    return get(d, n, FB) if n > 0 else n

# --- 引数の検査(証明書が要らない) ---
for bad_url in ("ftp://x:1", "http://", "socks4://h:1"):
    try: N.parse_proxy(bad_url); ok = False
    except ValueError: ok = True
    check(f"プロキシの指定がおかしければ ValueError({bad_url})", ok, True)
check("プロキシの解釈: user:pass と既定のポート", (N.parse_proxy("http://u:p%40w@h"), N.parse_proxy("socks5://h")), (("http", "h", 8080, "u", "p@w"), ("socks5", "h", 1080, None, None)))
dd = dev(); l = call(dd, 5, 0, 5); u = call(dd, 7, 0); put(dd, b"localhost", HB)
check("TLS_START: 待ち受け・UDP のハンドルは -22、知らないハンドルは -9、ホスト名の検査 -22", (call(dd, 13, l, HB, 9), call(dd, 13, u, HB, 9), call(dd, 13, 99, HB, 9), call(dd, 13, l, HB, 0)), (-22, -22, -9, -22))
check("ACCEPT: 待ち受けでないハンドルは -22", call(dd, 6, u), -22)
dd.release()

if have_certs:
    # --- TLS(クライアント) ---
    tsrv, tport, got = tls_server()
    d = dev(); d.ca, d.ctx = CA, None
    h = connect(d, "localhost", tport)
    check("TLS_START: 証明書の連鎖・名前を確認して 0", call(d, 13, h, HB, 9), 0)
    check("TLS: 暗号化されて送受信できる(サーバーには平文が届く)", (exchange(d, h), got[-1]), (b"secure:hi", b"hi"))
    check("TLS: 二度目の TLS_START は -22", call(d, 13, h, HB, 9), -22)
    call(d, 10, h, 0)
    check("TLS: 待たない RECV で何も来なければ -11", call(d, 3, h, FB, 10), -11)
    check("TLS: CLOSE", call(d, 4, h), 0)
    d.release()
    d = dev()                                                            # 試験用の CA を信じない
    h = connect(d, "localhost", tport)
    check("TLS: 信じない CA の証明書は -1(EPERM)、失敗した接続のハンドルは無くなる", (call(d, 13, h, HB, 9), call(d, 2, h, BUF, 1)), (-1, -9))
    d.release()
    wsrv, wport, _ = tls_server("wrongname")
    d = dev(); d.ca = CA
    h = connect(d, "localhost", wport)
    check("TLS: 証明書の名前が違えば -1", call(d, 13, h, HB, 9), -1)
    d.release()
    psrv, pport = plain_echo()
    d = dev(); d.ca = CA
    h = connect(d, "localhost", pport)
    call(d, 2, h, BUF, 0)
    check("TLS: 相手が TLS でなければ握手の失敗(-71 か相手が閉じた -104)", call(d, 13, h, HB, 9) in (-71, -104), True)
    d.release()
    put(d, b"localhost", HB)
    # --- HTTP プロキシ ---
    psrv, pport = plain_echo()
    xsrv, xport, xlog = http_proxy()
    d = dev(); d.proxy = N.parse_proxy(f"http://127.0.0.1:{xport}")
    h = connect(d, "127.0.0.1", pport)
    check("HTTP プロキシ: CONNECT でつながり、中身が通る", (h >= 1, exchange(d, h, b"x"), xlog), (True, b"echo:x", [f"127.0.0.1:{pport}"]))
    d.release()
    asrv, aport, alog = http_proxy("bob", "secret")
    d = dev(); d.proxy = N.parse_proxy(f"http://127.0.0.1:{aport}")
    check("HTTP プロキシ: 認証が要るのに無ければ -13(407)", connect(d, "127.0.0.1", pport), -13)
    d.proxy = N.parse_proxy(f"http://bob:wrong@127.0.0.1:{aport}")
    check("HTTP プロキシ: パスワードが違えば -13", connect(d, "127.0.0.1", pport), -13)
    d.proxy = N.parse_proxy(f"http://bob:secret@127.0.0.1:{aport}")
    h = connect(d, "127.0.0.1", pport)
    check("HTTP プロキシ: Basic 認証でつながる", exchange(d, h, b"y"), b"echo:y")
    d.release()
    bsrv, bport, _ = http_proxy(status=502)
    d = dev(); d.proxy = N.parse_proxy(f"http://127.0.0.1:{bport}")
    check("HTTP プロキシ: 502 など(認証以外の失敗)は -113", connect(d, "127.0.0.1", pport), -113)
    d = dev(); d.proxy = N.parse_proxy("http://127.0.0.1:1")
    check("プロキシ自体につながらなければ -111", connect(d, "127.0.0.1", pport), -111)
    # --- SOCKS5 ---
    ssrv, sport, slog = socks_proxy(names={"internal.test": "127.0.0.1"})
    d = dev(); d.proxy = N.parse_proxy(f"socks5://127.0.0.1:{sport}")
    h = connect(d, "internal.test", pport)
    check("SOCKS5: 名前のままプロキシに渡す(こちらで引かない)。つながって中身が通る", (h >= 1, exchange(d, h, b"z"), slog[-1]), (True, b"echo:z", (3, "internal.test", pport)))
    d.release()
    d = dev("internal.test"); d.proxy = N.parse_proxy(f"socks5://127.0.0.1:{sport}")
    h = connect(d, "internal.test", pport)
    check("許可の判断は、プロキシ越しなら「書いた名前」だけ(名前が引けなくても許可の名前なら通る)", h >= 1, True)
    check("許可にない名前は、プロキシ越しでも -13", connect(d, "other.test", pport), -13)
    d.release()
    s2, p2 = server(); s2.close()
    d = dev(); d.proxy = N.parse_proxy(f"socks5://127.0.0.1:{sport}")
    check("SOCKS5: 相手が拒否(ECONNREFUSED)は -111", connect(d, "127.0.0.1", p2), -111)
    usrv, uport, _ = socks_proxy("ann", "pw")
    d = dev(); d.proxy = N.parse_proxy(f"socks5://127.0.0.1:{uport}")
    check("SOCKS5: 認証が要るのに無ければ -13", connect(d, "127.0.0.1", pport), -13)
    d.proxy = N.parse_proxy(f"socks5://ann:bad@127.0.0.1:{uport}"); check("SOCKS5: パスワードが違えば -13", connect(d, "127.0.0.1", pport), -13)
    d.proxy = N.parse_proxy(f"socks5://ann:pw@127.0.0.1:{uport}"); h = connect(d, "127.0.0.1", pport)
    check("SOCKS5: ユーザー名とパスワードでつながる", exchange(d, h, b"w"), b"echo:w")
    d.release()
    # --- プロキシ越しの TLS ---
    d = dev(); d.ca = CA; d.proxy = N.parse_proxy(f"http://127.0.0.1:{xport}")
    h = connect(d, "localhost", tport)
    check("プロキシ越しに TLS(https): CONNECT のあと握手して通る", (call(d, 13, h, HB, 9), exchange(d, h, b"s"), xlog[-1]), (0, b"secure:s", f"localhost:{tport}"))
    d.release()
    # --- 環境変数(env) ---
    old = {k: os.environ.get(k) for k in ("ALL_PROXY", "all_proxy", "HTTPS_PROXY", "https_proxy", "HTTP_PROXY", "http_proxy", "NO_PROXY", "no_proxy")}
    for k in old: os.environ.pop(k, None)
    try:
        check("env: 環境変数が無ければプロキシなし", N.Net(proxy="env").proxy, None)
        os.environ["HTTPS_PROXY"] = f"http://127.0.0.1:{xport}"; n0 = len(xlog)
        d = dev(); d.proxy, d.proxy_env = N.env_proxy(), True
        h = connect(d, "127.0.0.1", pport)
        check("env: HTTPS_PROXY に従う", (h >= 1, len(xlog) - n0), (True, 1)); d.release()
        os.environ["NO_PROXY"] = "localhost, 127.0.0.1"; n0 = len(xlog)
        d = dev(); d.proxy, d.proxy_env = N.env_proxy(), True
        h = connect(d, "127.0.0.1", pport)
        check("env: NO_PROXY に挙げた相手はプロキシを通らない", (h >= 1, len(xlog) - n0, exchange(d, h, b"n")), (True, 0, b"echo:n")); d.release()
        check("NO_PROXY: 後ろの一致(.example.com)と *", (N.no_proxy("a.example.com") if os.environ.update(NO_PROXY=".example.com") is None else None, N.no_proxy("example.com"), N.no_proxy("badexample.com"), N.no_proxy("x") if os.environ.update(NO_PROXY="*") is None else None), (True, True, False, True))
    finally:
        for k, v in old.items():
            if v is None: os.environ.pop(k, None)
            else: os.environ[k] = v
    # --- Sign から: https_get(http_get.sn の TLS=1)を プロキシ越し・独自 CA で ---
    src = open(os.path.join(HERE, "http_get.sn"), encoding="utf-8").read().replace("`example.com`", "`localhost`").replace("PORT : 80", f"PORT : {tport}").replace("TLS : 0", "TLS : 1").replace("`std.sn`", f"`{os.path.join(HERE, 'std.sn')}`")
    p = os.path.join(tmp, "s.sn"); open(p, "w", encoding="utf-8").write(src)
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p, "--net=local,localhost", f"--net-ca={CA}"], capture_output=True, timeout=30)
    check("http_get.sn(TLS=1): https で取れる(サーバーが受け取った先頭は GET / HTTP/1.0)", ("secure:GET / HTTP/1.0" in r.stdout.decode(), got[-1].startswith(b"GET / HTTP/1.0")), (True, True))
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p, "--net=local,localhost"], capture_output=True, timeout=30)
    check("http_get.sn(TLS=1): CA を渡さなければ証明書エラー -1 と出る", "エラー -1" in r.stdout.decode(), True)
    n0 = len(xlog)
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p, "--net=localhost", f"--net-ca={CA}", f"--net-proxy=http://127.0.0.1:{xport}"], capture_output=True, timeout=30)
    check("http_get.sn(TLS=1): --net-proxy で プロキシ越し(プロキシの記録に出る)", ("secure:GET" in r.stdout.decode(), xlog[n0:]), (True, [f"localhost:{tport}"]))
print("\n" + ("全部通った" if not bad else f"{bad} 件 食い違い")); sys.exit(1 if bad else 0)
