"""test_asm_net.py — ネットワーク・IoT の見本を、処理系と asm 版(エミュレータ+同じ仮想装置。ソケットは本物)で走らせて突き合わせる。
echo_server・http_get・mqtt_demo・iot_demo は charset: utf32(日本語の文字列を含む)。実機では未実行。"""
import os, sys, threading, time, socket, subprocess, tempfile, sqlite3, http.server, socketserver
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
os.environ.setdefault("EMU_LIMIT", "4000000000")
import emu_dev, sign_asm, sign_interp, fake_mqtt

fails = 0
def check(name, want, got):
    global fails
    if want == got: print("ok ", name)
    else: fails += 1; print("NG ", name, "\n    want", repr(want)[:300], "\n    got ", repr(got)[:300])

def interp(path, flags, cwd=None):
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), path] + flags, capture_output=True, timeout=120, stdin=subprocess.DEVNULL, cwd=cwd or HERE)
    return r.stdout.decode("utf-8", "replace")
def emulate(src, specs, wd=None):
    asm = sign_asm.generate(sign_interp.parse_source(src), "linux", charset="utf32")
    old = os.getcwd()
    if wd: os.chdir(wd)
    try: return emu_dev.run_emulated(asm, specs + ["charset=utf32"], b"", wd)
    finally: os.chdir(old)
def tmp_src(name, src):
    d = tempfile.mkdtemp(); p = os.path.join(d, name)
    for f in ("std.sn", "aht25.sn", "sqlite.sn", "mqtt.sn"):          # `名前`@~ は同じフォルダを見る
        os.symlink(os.path.join(HERE, f), os.path.join(d, f))
    open(p, "w", encoding="utf-8").write(src); return p

# ---- echo_server: 日本語を送って、そのまま返ってくる ----
def echo_client(payload, got):
    for _ in range(200):
        try: s = socket.create_connection(("127.0.0.1", 9000), timeout=5); break
        except OSError: time.sleep(0.05)
    else: got.append(b"NOCONN"); return
    s.sendall(payload); s.shutdown(socket.SHUT_WR); buf = b""
    while True:
        d = s.recv(4096)
        if not d: break
        buf += d
    got.append(buf); s.close()
src = open(os.path.join(HERE, "echo_server.sn"), encoding="utf-8").read()
payload = "こんにちは hello\n".encode()
res = []
for kind in ("interp", "emu"):
    got = []; t = threading.Thread(target=echo_client, args=(payload, got)); t.start()
    out = interp(os.path.join(HERE, "echo_server.sn"), ["--net=local"]) if kind == "interp" else emulate(src, ["net=local"])
    t.join(); res.append((out, got))
check("echo_server: 標準出力と、返ってきたバイトが処理系と一致", res[0], res[1])
check("echo_server: 日本語がそのまま返った", res[1][1], [payload])

# ---- http_get: 本文は UTF-8(日本語)。Date は固定 ----
BODY = "<html>こんにちは world</html>\n".encode()
class H(http.server.BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.0"
    def version_string(self): return "T"
    def date_time_string(self, t=None): return "Mon, 01 Jan 2026 00:00:00 GMT"
    def do_GET(self):
        self.send_response(200); self.send_header("Content-Type", "text/html; charset=utf-8"); self.send_header("Content-Length", str(len(BODY))); self.end_headers(); self.wfile.write(BODY)
    def log_message(self, *a): pass
srv = socketserver.TCPServer(("127.0.0.1", 0), H); port = srv.server_address[1]
threading.Thread(target=srv.serve_forever, daemon=True).start()
src = open(os.path.join(HERE, "http_get.sn"), encoding="utf-8").read().replace("HOST : `example.com`", "HOST : `127.0.0.1`").replace("PORT : 80", "PORT : %d" % port)
p = tmp_src("hg.sn", src)
a, b = interp(p, ["--net=local"]), emulate(src, ["net=local"])
check("http_get: 標準出力(ヘッダと日本語の本文)が処理系と一致", a, b)
check("http_get: 本文の日本語が UTF-8 のまま出た", "こんにちは world" in b, True)
srv.shutdown()

# ---- mqtt_demo: 購読して、来た日本語を出し、sign/count を 5 回出す ----
def mqtt_run(kind):
    br = fake_mqtt.Broker()
    src = open(os.path.join(HERE, "mqtt_demo.sn"), encoding="utf-8").read().replace("PORT : 1883", "PORT : %d" % br.port)
    p = tmp_src("md.sn", src)
    def push(): br.wait(lambda: br.subs); time.sleep(0.3); br.publish_all("sign/in", "こんにちは".encode())
    threading.Thread(target=push, daemon=True).start()
    out = interp(p, ["--net=local"]) if kind == "i" else emulate(src, ["net=local"])
    pubs = [(t, pl) for t, pl, q, r in br.pubs]; br.stop(); return out, pubs
a, b = mqtt_run("i"), mqtt_run("e")
check("mqtt_demo: 標準出力と、ブローカーが受けた PUBLISH が処理系と一致", a, b)
check("mqtt_demo: 日本語を受けて出した・5 回出した", ("受信 sign/in: こんにちは" in b[0], len(b[1])), (True, 5))

# ---- iot_demo: AHT25(偽)・SQLite・MQTT・GPIO(偽)。命令でしきい値を変える ----
def iot_run(kind):
    br = fake_mqtt.Broker(); wd = tempfile.mkdtemp()
    src = open(os.path.join(HERE, "iot_demo.sn"), encoding="utf-8").read().replace("PORT : 1883", "PORT : %d" % br.port)
    p = tmp_src("iot.sn", src)
    def push(): br.wait(lambda: br.subs); br.publish_all("sign/iot/cmd/threshold", b"2000")
    threading.Thread(target=push, daemon=True).start()
    if kind == "i": out = interp(p, ["--i2c=aht25:23.5,61", "--gpio=fake:quiet", "--db=" + wd, "--net=local"], cwd=wd)
    else: out = emulate(src, ["i2c=aht25:23.5,61", "gpio=fake:quiet", "db=" + wd, "net=local", "rtimer"], wd)
    try: rows = [r[1:] for r in sqlite3.connect(os.path.join(wd, "iot.db")).execute("select * from readings")]     # 時刻(ms)は実時間なので比べない
    except Exception as ex: rows = [str(ex)]
    pubs = list(br.pubs); br.stop(); return out, rows, pubs
a, b = iot_run("i"), iot_run("e")
check("iot_demo: 標準出力・DB の行・MQTT へ出したものが処理系と一致", a, b)
check("iot_demo: しきい値が変わり、6 件記録した", ("しきい値を変えた(×100): 2000" in b[0], len(b[1])), (True, 6))

print("\n全部 ok" if not fails else "\n失敗 %d 件" % fails)
sys.exit(1 if fails else 0)
