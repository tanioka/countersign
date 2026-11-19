"""sign_net.py — ネットワーク装置(TCP・UDP のソケット。名前の解決つき)。Windows・Linux・macOS で動く(Python 標準の socket だけ)。
仕様に定めの無い拡張で、sign_sys.py などの装置と同じ位置づけ。付けたときだけ使える(`--net` か `--net=許可`)。
外へ出る通信なので、付けない限り何も起きない。許可を絞れる:
    --net             どこへでも(+ どこからでも受けられる)
    --net=local       自分自身(127.0.0.1・localhost・::1)だけ。待ち受けも 127.0.0.1 だけ
    --net=host1,host2 その名前・アドレスの相手だけ(例: --net=example.com,192.168.0.10)。local も並べられる。待ち受けは 127.0.0.1 だけ
  許可のない相手には CONNECT・SENDTO が -13(EACCES)。名前は「書いたとおり」と「引いたアドレス」のどちらかが許可の中にあればよい。
    --net-proxy=URL   TCP の CONNECT をプロキシ経由にする。http://[user:pass@]host:port(HTTP の CONNECT 方式)か socks5://[user:pass@]host:port(名前の解決もプロキシにまかせる)。
                      --net-proxy=env なら環境変数(ALL_PROXY・HTTPS_PROXY・HTTP_PROXY、NO_PROXY で除外)に従う。URL を明示したときは、自分自身への接続もプロキシを通る。
                      プロキシ越しの相手の許可は「書いた名前」だけで判断する(こちらで名前を引かない)。UDP と RESOLVE はプロキシを通らない(RESOLVE は手元で引く)。
    --net-ca=ファイル  TLS で、OS の証明書に加えて信じる CA(PEM)。社内の CA や、自分で作った試験用の CA に使う。

使い方(Sign から): 番号と引数の番地に書き、GO に何か書くと実行され、RET を読むと結果が取れる。
    NET_BASE = 0x9900000
    base + 0x00  NR    W   番号
    base + 0x04  ARG0, +0x08 ARG1, +0x0C ARG2, +0x10 ARG3, +0x14 ARG4, +0x18 ARG5   W   引数
    base + 0x20  GO    W   何か書くと実行
    base + 0x24  RET   R   結果。0 以上なら成功の値、負なら -エラー番号
  バッファ(buf)は、インタープリタのメモリの番地から 1 語 = 1 バイト(0〜255)・4 バイト刻み(sign_sys.py と同じ形)。ホスト名は「バッファ + 長さ」で渡す。1 回の送受信は 65536 バイトまで。

  番号  名前        引数                                   結果
   1   CONNECT     host_buf, host_len, port               ハンドル(TCP につないだ。つなぐ待ちは最大 10 秒)
   2   SEND        h, buf, n                              送ったバイト数(全部送る)
   3   RECV        h, buf, n                              受け取ったバイト数。0 = 相手が閉じた。待っても来なければ -11(EAGAIN。待つ長さは SETTIMEOUT、既定 5 秒)
   4   CLOSE       h                                      0
   5   LISTEN      port, backlog                          ハンドル(TCP の待ち受け。port 0 なら空いている番号を選ぶ。選んだ番号は 12 で聞く)
   6   ACCEPT      h                                      新しい接続のハンドル。来なければ -11
   7   UDP_OPEN    port                                   ハンドル(UDP。port 0 なら空いている番号)
   8   SENDTO      h, host_buf, host_len, port, buf, n    送ったバイト数(UDP)
   9   RECVFROM    h, buf, n, from_buf                    受け取ったバイト数。送り主を「ア.ド.レ.ス:ポート」の文字列(0 終わり、64 バイトまで)にして from_buf に書く。来なければ -11
  10   SETTIMEOUT  h, ms                                  0(ms = 0 なら待たない。1 以上でその長さ待つ。既定 5000)
  11   RESOLVE     host_buf, host_len, out_buf            名前を引いて IPv4 アドレスの文字列を out_buf に書いた長さ(0 終わりの 0 は含まない)
  12   PORT        h                                      そのソケットの自分側のポート番号
  13   TLS_START   h, host_buf, host_len                  つないである TCP のハンドル h を TLS(暗号化)にする。host は証明書の名前の確認と SNI に使う(CONNECT に書いた名前と同じものを渡す)。
                                                          証明書の連鎖・期限・名前をすべて確認する(確認しない設定は無い)。0 を返す。失敗すると、その接続は閉じてハンドルも無くなる。
                                                          そのあとの SEND・RECV・SETTIMEOUT・CLOSE・PORT は同じハンドルのまま、暗号化されて動く。TLS 1.2 以上。サーバー側の TLS は無い。

エラー番号(Linux の errno に合わせる): 1 EPERM 証明書を確認できない(信用できない CA・期限切れ・名前が違う)/ 71 EPROTO TLS の握手の失敗(相手が TLS でない・版が合わない など)/ 2 名前が引けない / 9 EBADF 知らないハンドル / 11 EAGAIN 待ち時間切れ / 13 EACCES 許可がない / 22 EINVAL 引数がおかしい /
  24 EMFILE 開きすぎ(同時に 32 まで)/ 38 ENOSYS 知らない番号 / 98 EADDRINUSE / 104 ECONNRESET / 110 ETIMEDOUT / 111 ECONNREFUSED / 113 EHOSTUNREACH。OSError はその errno を負にして返す(Windows の番号は Linux の番号に直す)。
  注意: 待つ呼び出し(CONNECT・RECV・ACCEPT)はその間インタープリタ全体が止まる。ゲーム機(sign_console.py)の tick の中では SETTIMEOUT を 0 にして、来ていなければ -11 のまま次のこまへ進むのがよい。
"""
import base64, errno as E, os, socket, ssl, sys
from sign_mem import DevMem

NET_BASE = 0x9900000
NR, A0, A1, A2, A3, A4, A5, GO, RET = 0x00, 0x04, 0x08, 0x0C, 0x10, 0x14, 0x18, 0x20, 0x24
MAXIO, MAXHOST, MAXH, DEF_TIMEOUT, CONNECT_TIMEOUT = 65536, 255, 32, 5000, 10.0
EAGAIN, EBADF, EACCES, EINVAL, EMFILE, ENOSYS, ENOENT, EPERM, EPROTO = 11, 9, 13, 22, 24, 38, 2, 1, 71
# Windows の WSA 番号を Linux の番号へ
WIN2LINUX = {10035: 11, 10036: 115, 10048: 98, 10049: 99, 10053: 103, 10054: 104, 10060: 110, 10061: 111, 10065: 113, 10051: 101, 10050: 100}


def parse_proxy(url):
    """'http://user:pass@host:port' か 'socks5://…' を (種類, host, port, user, pass) にする。"""
    from urllib.parse import urlsplit, unquote
    u = urlsplit(url if "://" in url else "http://" + url)
    kind = {"http": "http", "https": "http", "socks5": "socks5", "socks5h": "socks5"}.get(u.scheme)
    if kind is None or not u.hostname: raise ValueError(f"プロキシの指定がおかしい: {url}(http://host:port か socks5://host:port)")
    return (kind, u.hostname, u.port or (1080 if kind == "socks5" else 8080), unquote(u.username) if u.username else None, unquote(u.password) if u.password else None)


def env_proxy():
    for k in ("ALL_PROXY", "all_proxy", "HTTPS_PROXY", "https_proxy", "HTTP_PROXY", "http_proxy"):
        if os.environ.get(k): return parse_proxy(os.environ[k])
    return None


def no_proxy(host):
    items = [x.strip().lower().lstrip(".") for x in (os.environ.get("NO_PROXY") or os.environ.get("no_proxy") or "").split(",") if x.strip()]
    h = host.lower()
    return any(x == "*" or h == x or h.endswith("." + x) for x in items)


class ProxyError(OSError): pass


def read_until(s, end, limit=8192):
    data = b""
    while end not in data:
        c = s.recv(1)
        if not c: raise ProxyError(E.ECONNRESET, "プロキシが途中で閉じた")
        data += c
        if len(data) > limit: raise ProxyError(E.EPROTO, "プロキシの返事が長すぎる")
    return data


def recv_exact(s, n):
    data = b""
    while len(data) < n:
        c = s.recv(n - len(data))
        if not c: raise ProxyError(E.ECONNRESET, "プロキシが途中で閉じた")
        data += c
    return data


def via_http_proxy(s, host, port, user, pw):
    hp = f"{host}:{port}"
    req = f"CONNECT {hp} HTTP/1.1\r\nHost: {hp}\r\n"
    if user is not None: req += "Proxy-Authorization: Basic " + base64.b64encode(f"{user}:{pw or ''}".encode()).decode() + "\r\n"
    s.sendall((req + "\r\n").encode())
    head = read_until(s, b"\r\n\r\n").split(b"\r\n")[0].split()
    code = int(head[1]) if len(head) >= 2 and head[1].isdigit() else 0
    if 200 <= code < 300: return
    raise ProxyError(EACCES if code in (401, 403, 407) else E.EHOSTUNREACH, f"プロキシが {code} を返した")


SOCKS_ERR = {1: E.EIO, 2: EACCES, 3: E.ENETUNREACH, 4: E.EHOSTUNREACH, 5: E.ECONNREFUSED, 6: E.ETIMEDOUT, 7: E.EOPNOTSUPP, 8: E.EAFNOSUPPORT}
def via_socks5(s, host, port, user, pw):
    s.sendall(b"\x05\x02\x00\x02" if user is not None else b"\x05\x01\x00")
    ver, method = recv_exact(s, 2)
    if ver != 5 or method == 0xFF: raise ProxyError(EACCES, "SOCKS5: 認証方式が合わない")
    if method == 2:
        u, p = (user or "").encode(), (pw or "").encode()
        if len(u) > 255 or len(p) > 255: raise ProxyError(EINVAL, "ユーザー名かパスワードが長すぎる")
        s.sendall(b"\x01" + bytes([len(u)]) + u + bytes([len(p)]) + p)
        if recv_exact(s, 2)[1] != 0: raise ProxyError(EACCES, "SOCKS5: ユーザー名かパスワードが違う")
    elif method != 0: raise ProxyError(EACCES, "SOCKS5: 知らない認証方式")
    hb = host.encode("ascii")
    s.sendall(b"\x05\x01\x00\x03" + bytes([len(hb)]) + hb + port.to_bytes(2, "big"))
    ver, rep, _, atyp = recv_exact(s, 4)
    recv_exact(s, {1: 4, 4: 16}.get(atyp, 0) + (recv_exact(s, 1)[0] if atyp == 3 else 0) + 2)
    if rep != 0: raise ProxyError(SOCKS_ERR.get(rep, E.EIO), f"SOCKS5: 失敗 {rep}")


class Net(DevMem):
    def __init__(self, allow=None, base=NET_BASE, ca=None, proxy=None):
        self.base, self.size = base, 0x28
        self.ca, self.ctx = ca, None
        self.proxy = env_proxy() if proxy == "env" else (parse_proxy(proxy) if proxy else None)
        self.proxy_env = proxy == "env"
        self.kind = {}
        self.allow = None if allow in (None, "", "all", "*") else [x.strip().lower() for x in allow.split(",") if x.strip()]
        self.local_only = self.allow is not None
        self.reg, self.ret, self.socks, self.next_h = {}, 0, {}, 1

    # --- 装置の口 ---
    def read(self, off): return self.ret if off == RET else self.reg.get(off)
    def write(self, off, v):
        if not isinstance(v, int) or isinstance(v, bool): return
        if off in (NR, A0, A1, A2, A3, A4, A5): self.reg[off] = v
        elif off == GO: self.ret = self.call()

    def finish(self): self.release()
    def release(self):
        for s in self.socks.values():
            try: s.close()
            except OSError: pass
        self.socks.clear(); self.kind.clear()

    # --- 部品 ---
    def get_bytes(self, buf, n):
        mem = self.memory()
        if mem is None or not isinstance(buf, int) or not isinstance(n, int) or n < 0 or n > MAXIO: return None
        out = bytearray()
        for i in range(n):
            v = mem.get(buf + 4 * i)
            if not isinstance(v, int) or isinstance(v, bool) or not 0 <= v <= 255: return None
            out.append(v)
        return bytes(out)

    def host(self, buf, n):
        if not isinstance(n, int) or not 0 < n <= MAXHOST: return None
        raw = self.get_bytes(buf, n)
        if raw is None: return None
        try: h = raw.decode("ascii")
        except UnicodeDecodeError: return None
        return h if h.isprintable() and " " not in h else None

    def permitted(self, host, resolve=True):
        if self.allow is None: return True
        names = {host.lower()}
        if resolve:
            try: names |= {ai[4][0].lower() for ai in socket.getaddrinfo(host, None)}
            except OSError: pass
        if names & set(self.allow): return True
        if "local" in self.allow and (names & {"localhost", "127.0.0.1", "::1"} or any(n.startswith("127.") for n in names)): return True
        return False

    def errno_of(self, e):
        if isinstance(e, socket.gaierror): return ENOENT
        if isinstance(e, (socket.timeout, TimeoutError, ssl.SSLWantReadError, ssl.SSLWantWriteError)): return EAGAIN
        if isinstance(e, ssl.SSLCertVerificationError): return EPERM
        if isinstance(e, ssl.SSLEOFError): return E.ECONNRESET
        if isinstance(e, ssl.SSLError): return EPROTO
        n = getattr(e, "errno", None)
        if not isinstance(n, int) or n <= 0: n = getattr(e, "winerror", None) or EINVAL
        return WIN2LINUX.get(n, n if n < 10000 else 5)

    def new(self, s, kind="tcp"):
        if len(self.socks) >= MAXH: s.close(); return -EMFILE
        h = self.next_h; self.next_h += 1; self.socks[h] = s; self.kind[h] = kind
        s.settimeout(DEF_TIMEOUT / 1000)
        return h

    def sock(self, h): return self.socks.get(h) if isinstance(h, int) else None

    def call(self):
        r = self.reg; nr = r.get(NR); a = [r.get(k) for k in (A0, A1, A2, A3, A4, A5)]
        try:
            if nr == 1:                                                   # CONNECT
                host, port = self.host(a[0], a[1]), a[2]
                if host is None or not isinstance(port, int) or not 0 < port < 65536: return -EINVAL
                px = self.proxy if self.proxy and not (self.proxy_env and no_proxy(host)) else None
                if not self.permitted(host, resolve=px is None): return -EACCES
                if px is None: return self.new(socket.create_connection((host, port), timeout=CONNECT_TIMEOUT))
                kind, phost, pport, user, pw = px
                s = socket.create_connection((phost, pport), timeout=CONNECT_TIMEOUT)
                try: (via_http_proxy if kind == "http" else via_socks5)(s, host, port, user, pw)
                except BaseException: s.close(); raise
                return self.new(s)
            if nr == 5:                                                   # LISTEN
                port, backlog = a[0], a[1] if isinstance(a[1], int) and a[1] > 0 else 5
                if not isinstance(port, int) or not 0 <= port < 65536: return -EINVAL
                s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
                s.bind(("127.0.0.1" if self.local_only else "0.0.0.0", port)); s.listen(min(backlog, 128))
                return self.new(s, "listen")
            if nr == 7:                                                   # UDP_OPEN
                port = a[0]
                if not isinstance(port, int) or not 0 <= port < 65536: return -EINVAL
                s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
                s.bind(("127.0.0.1" if self.local_only else "0.0.0.0", port))
                return self.new(s, "udp")
            if nr == 8:                                                   # SENDTO
                s = self.sock(a[0])
                if s is None: return -EBADF
                host, port, data = self.host(a[1], a[2]), a[3], self.get_bytes(a[4], a[5])
                if host is None or data is None or not isinstance(port, int) or not 0 < port < 65536: return -EINVAL
                if not self.permitted(host): return -EACCES
                return s.sendto(data, (host, port))
            if nr == 11:                                                  # RESOLVE
                host = self.host(a[0], a[1])
                if host is None: return -EINVAL
                if not self.permitted(host): return -EACCES
                ip = socket.gethostbyname(host).encode()
                if not self.put_bytes(a[2], ip + b"\0"): return -EINVAL
                return len(ip)
            if nr in (2, 3, 4, 6, 9, 10, 12, 13):
                s = self.sock(a[0])
                if s is None: return -EBADF
                if nr == 4: del self.socks[a[0]]; self.kind.pop(a[0], None); s.close(); return 0
                if nr == 12: return s.getsockname()[1]
                if nr == 10:
                    if not isinstance(a[1], int) or a[1] < 0: return -EINVAL
                    s.settimeout(a[1] / 1000 if a[1] > 0 else 0.0); return 0
                if nr == 13:                                              # TLS_START
                    host = self.host(a[1], a[2])
                    if host is None or self.kind.get(a[0]) != "tcp": return -EINVAL
                    if self.ctx is None:
                        self.ctx = ssl.create_default_context()
                        if self.ca: self.ctx.load_verify_locations(self.ca)
                    s.settimeout(CONNECT_TIMEOUT)
                    try: t = self.ctx.wrap_socket(s, server_hostname=host)
                    except BaseException:
                        s.close(); del self.socks[a[0]]; self.kind.pop(a[0], None); raise
                    t.settimeout(DEF_TIMEOUT / 1000); self.socks[a[0]] = t; self.kind[a[0]] = "tls"
                    return 0
                if nr == 6:                                               # ACCEPT
                    if self.kind.get(a[0]) != "listen": return -EINVAL
                    c, _ = s.accept(); c.settimeout(DEF_TIMEOUT / 1000); return self.new(c)
                if nr == 2:                                               # SEND
                    data = self.get_bytes(a[1], a[2])
                    if data is None: return -EINVAL
                    s.sendall(data); return len(data)
                n = a[2]
                if not isinstance(n, int) or not 0 <= n <= MAXIO: return -EINVAL
                if nr == 3:                                               # RECV
                    data = s.recv(n)
                else:                                                     # RECVFROM
                    data, addr = s.recvfrom(n)
                    if not self.put_bytes(a[3], f"{addr[0]}:{addr[1]}".encode()[:63] + b"\0"): return -EINVAL
                if not self.put_bytes(a[1], data): return -EINVAL
                return len(data)
            return -ENOSYS
        except BlockingIOError: return -EAGAIN
        except Exception as e: return -self.errno_of(e)
