#!/usr/bin/env python3
"""sign_editor.py の試験: 実行・型検査・打ち切り・盤の保存・守り(Host/Origin/Content-Type)。python3 test_editor.py"""
import http.client, json, os, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
PORT = 8793
proc = subprocess.Popen([sys.executable, os.path.join(HERE, "sign_editor.py"), "--no-open", "--port", str(PORT)],
                        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
time.sleep(1.0)
fails = []

def req(method, path, body=None, headers=None, host=None):
    c = http.client.HTTPConnection("127.0.0.1", PORT, timeout=30)
    h = {"Content-Type": "application/json"}
    h.update(headers or {})
    if host: h["Host"] = host
    c.request(method, path, json.dumps(body) if body is not None else None, h)
    r = c.getresponse()
    data = r.read().decode("utf-8")
    try: return r.status, json.loads(data)
    except ValueError: return r.status, data

def check(name, ok, info=""):
    print(("ok  " if ok else "NG  ") + name + ("" if ok else "  " + str(info)))
    if not ok: fails.append(name)

PJ = "/api/projects/%E8%A9%A6%E9%A8%93%E3%81%AE%E7%9B%A4"           # 「試験の盤」
try:
    st, j = req("GET", "/api/ping"); check("ping", st == 200 and j["ok"])
    st, html = req("GET", "/"); check("ページが出る", st == 200 and "ブロックエディタ" in html)
    st, j = req("POST", "/api/run", {"code": "inc : x ? x + 1\n`注釈`\n5 + __\ninc 3\n0x9000000 # 0u41"})
    check("実行: 値と標準出力", j["results"] == ["5", "4", "150994944"] and j["stdout"] == "A" and j["error"] is None, j)
    st, j = req("POST", "/api/run", {"code": "f : n ?\n\tn > 0 :\n\t\tn > 5 : 3\n\t\t2\n\t0\n(f 7) + (f 1)", "opt": True})
    check("最適化つき(入れ子の条件)", j["results"] == ["5"], j)
    st, j = req("POST", "/api/run", {"code": "inc : x ? x + 1\n5 inc", "strict": True})
    check("厳密の警告", any("leftover" in w for w in j["warnings"]), j)
    st, j = req("POST", "/api/run", {"code": "x : (1 +"}); check("構文エラーの場所", j["error"] and j["error"]["line"] == 1, j)
    st, j = req("POST", "/api/types", {"code": "sum : n a ?\n\tn <= 0 : a\n\tsum (n - 1) (a + n)\nsum 100 0\n"})
    check("型の静的パス", j["signatures"] == ["sum : Int Int -> Int"], j)
    t0 = time.time()
    st, j = req("POST", "/api/run", {"code": "loop : n a ?\n\tloop (n + 1) a\nloop 0 0\n"})
    check("止まらない計算は打ち切る", j["error"] and "打ち切" in j["error"]["message"] and time.time() - t0 < 20, j)
    st, j = req("GET", "/api/ping", host="evil.example"); check("Host が違えば断る", st == 403)
    st, j = req("POST", "/api/run", {"code": "1"}, headers={"Origin": "http://evil.example"}); check("Origin が違えば断る", st == 403)
    st, j = req("POST", "/api/run", {"code": "1"}, headers={"Content-Type": "text/plain"}); check("Content-Type が違えば断る", st == 400)
    st, j = req("PUT", "/api/projects/..%2Fx", {"a": 1}); check("名前に ../ は使えない", st == 400)
    st, j = req("PUT", PJ, {"S": {"tabs": []}, "D": {}}); check("盤を保存", st == 200, j)
    st, j = req("GET", "/api/projects"); check("盤の一覧", "試験の盤" in j, j)
    st, j = req("GET", PJ); check("盤を読む", st == 200 and j["S"] == {"tabs": []}, j)
finally:
    proc.terminate()
    p = os.path.join(HERE, "sign_projects", "試験の盤.json")
    if os.path.exists(p): os.remove(p)
print("\n全部通った" if not fails else f"\n{len(fails)} 件が失敗: {fails}")
sys.exit(1 if fails else 0)
