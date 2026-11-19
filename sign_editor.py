#!/usr/bin/env python3
"""sign_editor.py — ブロックエディタ(sign_blocks.html)を配り、本物の処理系で実行・型検査するサーバー。標準ライブラリだけ。

    python3 sign_editor.py              # http://127.0.0.1:8765/ を開く(自分の計算機の中だけ)
    python3 sign_editor.py --port 9000
    python3 sign_editor.py --no-open    # ブラウザを自動で開かない

ページから生成した Sign を送ると、sign_interp.py(実行)と sign_types.py(型の静的パス)の結果を返す。
実行は別のプロセスで、時間を区切って行う(止まらないプログラムでもサーバーは止まらない)。
盤の保存と読み込みは、このフォルダの sign_projects/ に JSON で置く。

    GET  /scratch                           Scratch 風のブロックでゲームを作るページ
    POST /api/game    {code}                → sign_projects/blocks_game.sn に書く(sign_console.py が保存を見て差し替える)
    POST /api/preview {code, frames}        → {png(base64), log}  ゲーム機で frames こま動かした最後の画面
    POST /api/run     {code, strict, opt}  → {results[], stdout, warnings[], error|null}
    POST /api/types   {code}               → {signatures[], errors[]}
    GET  /api/ping    → {ok}
    GET  /api/projects  /  GET|PUT /api/projects/<名前>
"""
import http.server, io, json, os, re, subprocess, sys, threading, webbrowser

HERE = os.path.dirname(os.path.abspath(__file__))
PAGE = os.path.join(HERE, "sign_blocks.html")
PROJECTS = os.path.join(HERE, "sign_projects")
SCRATCH = os.path.join(HERE, "sign_scratch.html")           # Scratch 風のブロックでゲームを作るページ(/scratch)
GAME = os.path.join(PROJECTS, "blocks_game.sn")             # そのページが書き出すゲーム。sign_console.py で動かす
RUN_TIMEOUT = 10                                  # 秒。これを越えたら実行を打ち切る
MAX_BODY = 1 << 20

# ------------------------------------------------------------------ 作業プロセス(実行・型検査)
def worker():
    """stdin の JSON を読み、結果を stdout の最後の行に JSON で書く(それより前の行は、プログラムの標準出力)。"""
    sys.path.insert(0, HERE)
    req = json.loads(sys.stdin.read())
    real_out, buf = sys.stdout, io.StringIO()
    sys.stdout = buf
    out = {}
    try:
        import sign_interp as S
        if req["op"] == "types":
            import sign_types as T
            chk = T.infer(req["code"], HERE)
            out = {"signatures": chk.signatures(), "errors": [f"[{k}] {w}: {d}" for k, w, d in chk.errors()]}
        else:
            S.STRICT_GATES = bool(req.get("strict"))
            S.OPT = bool(req.get("opt"))
            code = req["code"]
            result = {"results": [], "warnings": [], "error": None}
            def go():
                try:
                    nodes = S.parse_source(code)
                    S.IMPORT_STACK.clear()
                    res = S.run(code)
                    for n, v in zip(nodes, res):
                        d = n[1] if n[0] == "export" else n
                        if d[0] in ("def", "opdef", "importspread"): continue
                        if d[0] == "lit" and isinstance(d[1], str): continue          # 注釈の文字列
                        result["results"].append(S.show(v))
                except S.SignError as e:
                    loc = getattr(e, "loc", None)
                    result["error"] = {"message": str(e), "line": loc[1] if loc else None, "col": loc[2] if loc else None}
                except (SyntaxError, NotImplementedError) as e:
                    loc = getattr(e, "loc", None)
                    result["error"] = {"message": str(e), "line": loc[1] if loc else None, "col": loc[2] if loc else None}
                except RecursionError:
                    result["error"] = {"message": "再帰が深すぎます", "line": None, "col": None}
            S.run_with_big_stack(go)
            result["warnings"] = [f"{k}: {m}" for k, m in S.WARNINGS]
            out = result
    except Exception as e:                           # 作業プロセスの内部の失敗は、画面へそのまま返す
        out = {"error": {"message": f"{type(e).__name__}: {e}", "line": None, "col": None}, "results": [], "warnings": []}
    sys.stdout = real_out
    out["stdout"] = buf.getvalue()
    real_out.write("\n" + json.dumps(out, ensure_ascii=False) + "\n")
    real_out.flush()

def preview(code, frames):
    """ゲームを別のプロセスで frames こま動かし(窓なし・仮想の時計)、最後の画面の PNG を返す。"""
    import base64, tempfile
    frames = max(1, min(int(frames or 30), 300))
    with tempfile.TemporaryDirectory() as d:
        game = os.path.join(d, "game.sn")
        with open(game, "w", encoding="utf-8") as f: f.write(code)
        try:
            p = subprocess.run([sys.executable, os.path.join(HERE, "sign_console.py"), game, f"--display=png:{d}/f{{n}}.png:96x96",
                                "--timer=virtual", f"--frames={frames}"], capture_output=True, text=True, timeout=RUN_TIMEOUT * 2, cwd=HERE)
        except subprocess.TimeoutExpired:
            return {"error": f"{RUN_TIMEOUT * 2} 秒で打ち切りました"}
        pngs = sorted((f for f in os.listdir(d) if f.endswith(".png")), key=lambda f: int(re.findall(r"\d+", f)[0]))
        log = (p.stderr or "").strip()
        if not pngs: return {"error": log or "画面が出ませんでした(毎こま present されていません)"}
        with open(os.path.join(d, pngs[-1]), "rb") as f: png = base64.b64encode(f.read()).decode("ascii")
        return {"png": png, "log": log[-600:]}

def call_worker(op, payload):
    req = dict(payload, op=op)
    try:
        p = subprocess.run([sys.executable, os.path.abspath(__file__), "--worker"], input=json.dumps(req),
                           capture_output=True, text=True, timeout=RUN_TIMEOUT, cwd=HERE)
    except subprocess.TimeoutExpired:
        return {"results": [], "warnings": [], "stdout": "", "error": {"message": f"{RUN_TIMEOUT} 秒で打ち切りました(終わらない計算かもしれません)", "line": None, "col": None}}
    lines = p.stdout.rstrip("\n").split("\n")
    try:
        data = json.loads(lines[-1])
    except (ValueError, IndexError):
        return {"results": [], "warnings": [], "stdout": "", "error": {"message": "作業プロセスが答えませんでした: " + (p.stderr.strip()[-300:] or "(出力なし)"), "line": None, "col": None}}
    return data

# ------------------------------------------------------------------ 盤の保存
NAME_OK = re.compile(r"^[\w\-ぁ-んァ-ヶ一-龥ー ]{1,40}$")
def project_path(name):
    if not NAME_OK.match(name): return None
    return os.path.join(PROJECTS, name.strip() + ".json")

# ------------------------------------------------------------------ サーバー
class Handler(http.server.BaseHTTPRequestHandler):
    server_version = "SignEditor/1"
    def log_message(self, *a): pass

    def host_ok(self):                               # DNS 再束縛への備え: 自分の名前でない Host は断る
        h = (self.headers.get("Host") or "").split(":")[0]
        return h in ("127.0.0.1", "localhost", "[::1]")
    def origin_ok(self):
        o = self.headers.get("Origin")
        return o is None or re.match(r"^http://(127\.0\.0\.1|localhost)(:\d+)?$", o) is not None

    def send(self, code, body, ctype="application/json; charset=utf-8"):
        if isinstance(body, (dict, list)): body = json.dumps(body, ensure_ascii=False)
        if isinstance(body, str): body = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype); self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store"); self.end_headers()
        self.wfile.write(body)

    def body_json(self):
        if "application/json" not in (self.headers.get("Content-Type") or ""): raise ValueError("Content-Type は application/json です")
        n = int(self.headers.get("Content-Length") or 0)
        if n > MAX_BODY: raise ValueError("大きすぎます")
        return json.loads(self.rfile.read(n) or b"{}")

    def guard(self):
        if not self.host_ok() or not self.origin_ok():
            self.send(403, {"error": "forbidden"}); return False
        return True

    def missing(self, name):
        msg = (f'<!doctype html><meta charset="utf-8"><body style="font:16px system-ui;margin:2em"><h1>{name} が見つかりません</h1>'
               f'<p>sign_editor.py と同じフォルダ({HERE})に {name} を置いてください。</p></body>')
        self.send(404, msg, "text/html; charset=utf-8")

    def do_GET(self):
        if not self.guard(): return
        path = self.path.split("?")[0]
        if path in ("/", "/index.html"):
            if not os.path.exists(PAGE):                              # sign_blocks.html を置いていなくても、Scratch 風のページは使える
                if os.path.exists(SCRATCH):
                    self.send_response(302); self.send_header("Location", "/scratch"); self.end_headers(); return
                return self.missing("sign_blocks.html")
            html = open(PAGE, encoding="utf-8").read()
            page = ('<!doctype html><html lang="ja"><head><meta charset="utf-8">'
                    '<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover"></head><body style="margin:0">'
                    + html + "</body></html>")
            return self.send(200, page, "text/html; charset=utf-8")
        if path == "/scratch":
            if not os.path.exists(SCRATCH): return self.missing("sign_scratch.html")
            return self.send(200, open(SCRATCH, encoding="utf-8").read(), "text/html; charset=utf-8")
        if path == "/api/ping": return self.send(200, {"ok": True})
        if path == "/api/projects":
            os.makedirs(PROJECTS, exist_ok=True)
            return self.send(200, sorted(f[:-5] for f in os.listdir(PROJECTS) if f.endswith(".json")))
        m = re.match(r"^/api/projects/(.+)$", path)
        if m:
            from urllib.parse import unquote
            p = project_path(unquote(m.group(1)))
            if not p or not os.path.exists(p): return self.send(404, {"error": "見つかりません"})
            return self.send(200, open(p, encoding="utf-8").read())
        self.send(404, {"error": "not found"})

    def do_POST(self):
        if not self.guard(): return
        try: req = self.body_json()
        except Exception as e: return self.send(400, {"error": str(e)})
        code = req.get("code")
        if not isinstance(code, str): return self.send(400, {"error": "code が要ります"})
        if self.path == "/api/run": return self.send(200, call_worker("run", {"code": code, "strict": bool(req.get("strict")), "opt": bool(req.get("opt"))}))
        if self.path == "/api/game":
            os.makedirs(PROJECTS, exist_ok=True)
            tmp = GAME + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f: f.write(code)
            os.replace(tmp, GAME)                                           # 途中の書きかけをゲーム機が読まないように
            return self.send(200, {"ok": True, "path": os.path.relpath(GAME, HERE).replace(os.sep, "/")})
        if self.path == "/api/preview": return self.send(200, preview(code, req.get("frames")))
        if self.path == "/api/types": return self.send(200, call_worker("types", {"code": code}))
        self.send(404, {"error": "not found"})

    def do_PUT(self):
        if not self.guard(): return
        m = re.match(r"^/api/projects/(.+)$", self.path.split("?")[0])
        if not m: return self.send(404, {"error": "not found"})
        from urllib.parse import unquote
        p = project_path(unquote(m.group(1)))
        if not p: return self.send(400, {"error": "名前に使えない字があります(日本語・英数・- _ 空白、40 字まで)"})
        try: req = self.body_json()
        except Exception as e: return self.send(400, {"error": str(e)})
        os.makedirs(PROJECTS, exist_ok=True)
        with open(p, "w", encoding="utf-8") as f: json.dump(req, f, ensure_ascii=False)
        self.send(200, {"ok": True})

def serve(port, open_browser):
    srv = http.server.ThreadingHTTPServer(("127.0.0.1", port), Handler)
    url = f"http://127.0.0.1:{port}/"
    print(f"ブロックエディタ: {url}   Scratch 風のゲーム作り: {url}scratch   (止めるには Ctrl+C)")
    if open_browser: threading.Timer(0.4, lambda: webbrowser.open(url)).start()
    try: srv.serve_forever()
    except KeyboardInterrupt: print()

if __name__ == "__main__":
    if "--worker" in sys.argv: worker(); sys.exit(0)
    port = 8765
    if "--port" in sys.argv: port = int(sys.argv[sys.argv.index("--port") + 1])
    serve(port, "--no-open" not in sys.argv)
