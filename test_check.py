#!/usr/bin/env python3
"""静的検査 sign_check.py の試験。python test_check.py"""
import json, os, subprocess, sys, tempfile
from fixblank import fix as _fixblank          # --strict は定義のブロックの後に空行を要る(alpha1/README.md)ので、strict の源は空行を補う
HERE = os.path.dirname(os.path.abspath(__file__))
TMP = tempfile.mkdtemp()
bad = 0
def check(name, got, want):
    global bad
    ok = got == want; bad += not ok
    print(("ok  " if ok else "NG  ") + name + ("" if ok else f"\n    得た: {got!r}\n    期待: {want!r}"))
def run(src, *flags):
    p = os.path.join(TMP, "t.sn"); open(p, "w", encoding="utf-8").write(_fixblank(src) if "--strict" in flags else src)
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign_check.py"), p, *flags], capture_output=True, text=True, cwd=HERE, timeout=120)
    return r.returncode, r.stdout
def js(src, *flags):
    rc, out = run(src, "--json", *flags); return rc, json.loads(out)

rc, j = js("f : x ?\n\tx + 1\nf 2\n")
check("整合している: 終了 0・報告なし", (rc, j["ok"], j["reports"]), (0, True, []))
rc, j = js("f : x ?\n\tx + zz\nf 2\n")
check("未定義の識別子は note・行番号つき・終了 0", (rc, [(r["severity"], r["kind"], r["line"], r["message"]) for r in j["reports"]]), (0, [("note", "undefined-identifier", 2, "zz")]))
rc, j = js("f : x ?\n\tx + zz\nf 2\n", "--werror")
check("--werror なら note でも終了 1", rc, 1)
G_SRC = "f : x y ?\n\tx + y\ng : a ?\n\tf a\ng 1\n"
rc, j = js(G_SRC)
check("関数を返す定義は既定では note・終了 0(既定の道では動く形)", (rc, [(r["severity"], r["kind"], r.get("strict_only")) for r in j["reports"]], j["reports"][0]["line"]), (0, [("note", "function-return-without-address", True)], 3))
check("根拠 basis が付く", js(G_SRC)[1]["reports"][0]["basis"], "static-only")
rc, j = js(G_SRC, "--strict")
check("--strict を付けると error・終了 1", (rc, [r["kind"] for r in j["reports"] if r["severity"] == "error"]), (1, ["function-return-without-address"]))
check("既定で note の文面に --strict の案内", "--strict なら断り" in js(G_SRC)[1]["reports"][0]["message"], True)
rc, j = js("f : x ?\n\ta : b + 1\n\tb : a + 1\n\ta\nf 1\n")
check("局所の名前の輪は既定では note", [(r["severity"]) for r in j["reports"] if r["kind"] == "name-cycle"], ["note"])
rc, j = js("f : x ?\n\ta : b + 1\n\tb : a + 1\n\ta\nf 1\n", "--strict")
check("局所の名前の輪は --strict で error", [(r["severity"]) for r in j["reports"] if r["kind"] == "name-cycle"], ["error"])
# 残りの種類: 常に error か strict だけか(実行で確かめた分け方)
for nm_, src_, kind_, sev_ in (
    ("range-no-progress", "r : x ?\n\t[0 ~+ 0 ~ 5]\nr 1\n", "range-no-progress", None),
    ("struct-runtime-index", "f : k ?\n\t[1 \\a 2.5] ' k\nf 1\n", "struct-runtime-index", "note"),
    ("instance-nest-limit", "f : g n ?\n\tn = 0 : 0\n\tf $g (n - 1)\ninc : x ?\n\tx + 1\nf $inc 3\n", "instance-nest-limit", "note")):
    rc, j = js(src_)
    sv = [r["severity"] for r in j["reports"] if r["kind"] == kind_]
    if sev_: check(f"{nm_}: 既定では note・--strict で error", (sv, [r["severity"] for r in js(src_, "--strict")[1]["reports"] if r["kind"] == kind_]), ([sev_], ["error"]))
rc, j = js("f : x ?\n\tx + 1.5\nf 1\n", "--layer", "1")
check("float-literal-layer は層を指せばいつも error", [(r["kind"], r["severity"]) for r in j["reports"]], [("float-literal-layer", "error")])
rc, j = js("f : x ?\n\t(x +\n")
check("構文の誤りは --strict なしでも error", (rc, j["reports"][0]["severity"]), (2, "error"))
rc, j = js("k : 1\nf : x ?\n\tx\nk : 2\nf k\n")
check("重複した定義は hint", [(r["kind"], r["line"]) for r in j["reports"] if r["severity"] == "hint"], [("duplicate-definition", 4)])
rc, j = js("k : 1\nf : x ?\n\tx\nk : 2\nf k\n", "--no-hint")
check("--no-hint で hint は出ない", j["reports"], [])
rc, j = js("f : x ?\n\tx\ng : x ?\n\tx\nf 1\n", "--unused")
check("--unused で使われない定義を出す", [(r["kind"], r["where"]) for r in j["reports"]], [("unused-definition", "g")])
rc, j = js("f : x ?\n\tx\ng : x ?\n\tx\nf 1\n")
check("既定では使われない定義は出さない", j["reports"], [])
rc, j = js("#pub : x ?\n\tx\nf : x ?\n\tx\nf 1\n", "--unused")
check("公開 # の定義は使われていなくてよい", [r["where"] for r in j["reports"]], [])
rc, j = js("f : x ?\n\t(x +\n")
check("構文の誤りは終了 2・行番号つき", (rc, j["reports"][0]["kind"], j["reports"][0]["line"]), (2, "syntax", 2))
rc, out = run("f : x ?\n\tx + zz\nf 2\n")
check("文面の形 file:行: 種類 [kind] 場所: 説明", out.split("\n")[0].split(": ", 1)[1], "note [undefined-identifier] f: zz")
rc, out = run("f : x ?\n\tx\nf 1\n")
check("整合の知らせ", "整合しています" in out, True)
# --strict の断りのうち静的に決まる物: 検査の結果と、本物の --strict 実行の断りが一致する(順・自分の名前・入れ子の違いも)
def strict_run(src):
    pth = os.path.join(TMP, "s.sn"); open(pth, "w", encoding="utf-8").write(_fixblank(src))
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), pth, "--strict"], capture_output=True, text=True, cwd=HERE, timeout=120)
    return r.stderr
# Q87(寄せ5 で R135 に決まった。2026-11-06): --strict では、複数行の括りに仮引数のブロックを書いた4つの形は、場所(行・桁)つきで前処理が止め、reason は param-block-bracket。ふつうの字下げの誤りは案内なし
for nm_, src_, ln_ in [("仮引数1つ", "r : [\n\t\tx\n\t? x + 1\n] 5\n", 3), ("仮引数2つ", "g : [\n\t\tx\n\t\ty\n\t? x + y\n]\ng 5 2\n", 4),
                       ("既定値つき", "g : [\n\t\tx\n\t\ty : 1\n\t? x + y\n]\ng 5\n", 4), ("? の下に枝", "g : [\n\t\tx\n\t? x > 0 : 1\n\t\t2\n]\ng 5\n", 3)]:
    err_ = strict_run(src_)
    check("R135 " + nm_, (":%d:2:" % ln_ in err_.splitlines()[0], "param-block-bracket" in err_), (True, True))
err_ = strict_run("g : [\n\t\ta : 1\n\tb : 2\n]\ng\n")
check("Q87 でない字下げの誤りは案内なし(場所は付く)", (":3:2:" in err_.splitlines()[0], "Q87" in err_), (True, False))
CASES = [
    ("g : y ?\n\ty\ninc : x ?\n\tx + 1\ng 1\n", None, "name-shadow"),
    ("f : x ?\n\t!_ + 1\nf 1\n", "strict-parse", "void-written"),
    ("f : x ?\n\t~1 2 3\nf 1\n", None, "G4"),
    ("f : x ?\n\tx + 1\nf 2\n", None, "G"),
    ("f : a a ? a\nf 1 2\n", "strict-name-duplicate", "name-duplicate"),             # R133・P2: 同じ関数の仮引数の同名(実行と同じ断り)
    ("k : [a b] a ? a\nk 1 2\n", "strict-name-duplicate", "name-duplicate"),         # 括りの中の名前と、並びの名前の重なり
]
for src, kind, key in CASES:
    rc, j = js(src, "--strict", "--no-hint")
    got = sorted({r["kind"] for r in j["reports"] if r["kind"].startswith("strict-")})
    err = strict_run(src)
    check("strict " + src.replace("\n", "|").replace("\t", "")[:44], (got, key in err), ([kind] if kind else [], bool(kind)))
# R133: 仮引数の隠しは断りでなく information `name-shadow`。検査は note、本物の --strict 実行も断らず知らせを出す
for src in ("inc : x ?\n\tx + 1\ng : inc ?\n\tinc\ng 1\n", "g : inc ?\n\tinc\ninc : x ?\n\tx + 1\ng 1\n",
            "f : [a ~f2] ?\n\ta\nf2 : x ?\n\tx\nf [1 2]\n", "f : f ?\n\tf\nf 1\n"):
    rc, j = js(src, "--strict", "--no-hint")
    sev = sorted({(r["kind"], r["severity"]) for r in j["reports"] if r["kind"] == "name-shadow"})
    err = strict_run(src)
    check("R133 " + src.replace("\n", "|").replace("\t", "")[:40], (sev, "name-shadow" in err and "エラー" not in err), ([("name-shadow", "note")], True))
rc, j = js("inc : x ?\n\tx\ng : inc ?\n\tinc\n")
check("--strict なしでは strict の断りは出ない", [r["kind"] for r in j["reports"]], [])
# 呼び出しを見るまで知らせを重くしない: `[@p,]` の p に、呼び出しが関数でない字面(数・文字列)だけを渡すなら、--strict でも note(実行も断らない。R50「ほかは未知」)。関数や名前を渡す呼び出しが 1 つでもあれば、従来どおり --strict で error
G7_BASE = "g : p xs ?\n\t[@p,] xs\n\n"
for nm_, call_, want_ in [("字面だけ", "g 5 [1 2 3]\n", (["note"], ["note"], False)), ("字面が 2 つ", "g 5 [1 2 3]\ng 7 [4]\n", (["note"], ["note"], False)),
                          ("関数を渡す呼び出し", "add2 : a b ? a + b\n\ng $add2 [1 2 3]\n", (["note"], ["error"], True)), ("字面と関数", "add2 : a b ? a + b\n\ng 5 [1 2 3]\ng $add2 [1]\n", (["note"], ["error"], True)),
                          ("名前を渡す(先は関数)", "add2 : a b ? a + b\n\nh : q ?\n\tg q [1]\n\nh $add2\n", (["note"], ["error"], True)), ("呼び出しが無い", "", (["note"], ["error"], False)),
                          ("名前を渡す(先は字面)", "h : q ?\n\tg q [1]\n\nh 5\n", (["note"], ["note"], False)), ("字面を束ねた名前", "v : 5\n\ng v [1 2]\n", (["note"], ["note"], False)),
                          ("関数を束ねた名前", "add2 : a b ? a + b\n\nv : $add2\n\ng v [1 2 3]\n", (["note"], ["error"], True)), ("2 段の仮引数(先は字面)", "h : q ?\n\tg q [1]\n\nk : r ?\n\th r\n\nk 5\n", (["note"], ["note"], False)),
                          ("2 段の仮引数(先は関数)", "add2 : a b ? a + b\n\nh : q ?\n\tg q [1]\n\nk : r ?\n\th r\n\nk $add2\n", (["note"], ["error"], True)), ("輪の中で仮引数を回す", "h : q n ?\n\tn = 0 : g q [1]\n\th q (n - 1)\n\nh 5 3\n", (["note"], ["note"], False)),
                          ("途中の定義が呼ばれない", "h : q ?\n\tg q [1]\n", (["note"], ["error"], False)),
                          ("口が 1 つの関数を渡す", "inc : x ? x + 1\n\ng $inc [1 2 3]\n", (["note"], ["note"], False)), ("口が 1 つの関数を束ねた名前", "inc : x ? x + 1\n\nv : $inc\n\ng v [1 2 3]\n", (["note"], ["note"], False)),
                          ("口が 1 つの関数と口が 2 つの関数", "inc : x ? x + 1\nadd2 : a b ? a + b\n\ng $inc [1]\ng $add2 [1 2 3]\n", (["note"], ["error"], True)),
                          ("可変長 [~l] の関数", "v1 : [~l] ? l\n\ng $v1 [1 2 3]\n", (["note"], ["note"], False)), ("括りの仮引数 1 つ([a b c])", "b3 : [a b c] ? a\n\ng $b3 [1 2 3]\n", (["note"], ["note"], False)),
                          ("名前と括りの 2 口", "m2 : x [y] ? x\n\ng $m2 [1 2 3]\n", (["note"], ["error"], True))]:
    src_ = G7_BASE + call_
    sv_ = lambda *fl: [r["severity"] for r in js(src_, *fl)[1]["reports"] if r["kind"].startswith("unknown-input")]
    check(f"G7 の重さ(呼び出しを見る): {nm_}", (sv_(), sv_("--strict"), "G7" in strict_run(src_)), want_)
# G19(`@p xs~`)も同じ: p に字面だけを渡す呼び出しなら note(実行は断らない)、関数(口が 3 つ以上)を渡せば error
G19_BASE = "add3 : a b c ? a + b + c\n\ng : p xs ?\n\t@p xs~\n\n"
for nm_, call_, want_ in [("字面", "g 5 [1 2 3]\n", (["note"], ["note"], False)), ("関数(口 3 つ)", "g $add3 [1 2 3]\n", (["note"], ["error"], True)), ("呼び出しが無い", "", (["note"], ["error"], False)),
                          ("関数(口 1 つ)", "inc : x ? x + 1\n\ng $inc [1 2 3]\n", (["note"], ["note"], False)), ("関数(口 2 つ)", "add2 : a b ? a + b\n\ng $add2 [1 2 3]\n", (["note"], ["note"], False)),
                          ("括りの仮引数 1 つ([a b c])", "b3 : [a b c] ? a\n\ng $b3 [1 2 3]\n", (["note"], ["note"], False)), ("名前と括りの 2 口", "m2 : x [y] ? x\n\ng $m2 [1 2 3]\n", (["note"], ["note"], False)),
                          ("可変長 [~l] の関数", "v1 : [~l] ? l\n\ng $v1 [1 2 3]\n", (["note"], ["note"], False))]:
    src_ = G19_BASE + call_
    sv_ = lambda *fl: [r["severity"] for r in js(src_, *fl)[1]["reports"] if r["kind"].startswith("unknown-input")]
    check(f"G19 の重さ(呼び出しを見る): {nm_}", (sv_(), sv_("--strict"), "G19" in strict_run(src_)), want_)
# unknown-input の G6・G19・G7: 既定の実行は断らず、--strict の実行は断る(本物の実行で確かめた)。検査は既定で note・--strict で error
UI = [("G19", "add3 : a b c ?\n\ta + b + c\ng : p xs ?\n\t@p xs~\ng $add3 [1 2 3]\n"),
      ("G7", "add2 : a b ?\n\ta + b\ng : p xs ?\n\t[@p,] xs\ng $add2 [1 2 3]\n"),
      ]                                                                       # G6 は R126 で廃止(先の分からない `y @p` は断らず、検査も知らせない)
for key, src_ in UI:
    pth = os.path.join(TMP, "u.sn"); open(pth, "w", encoding="utf-8").write(src_)
    d = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), pth], capture_output=True, text=True, cwd=HERE, timeout=120)
    st = strict_run(src_)
    sv0 = [r["severity"] for r in js(src_)[1]["reports"] if r["kind"] == "unknown-input"]
    sv1 = [r["severity"] for r in js(src_, "--strict")[1]["reports"] if r["kind"] == "unknown-input"]
    check(f"unknown-input {key}: 既定の実行は断らず・--strict の実行は断る・検査は note/error", (key in d.stderr, key in st, sv0, sv1), (False, True, ["note"], ["error"]))
# G19(口が 3 つ以上と分かる最上位の関数に撒く形): 検査と本物の --strict の実行が一致する
A3 = "add3 : a b c ?\n\ta + b + c\nadd4 : a b c d ?\n\ta + b + c + d\nadd2 : a b ?\n\ta + b\n"
G19 = [
    (A3 + "add3 [1 2 3]~\n", True), (A3 + "add4 1 [2 3 4]~\n", True), (A3 + "add4 [1 2 3 4]~\n", True), (A3 + "add3 []~\n", False),
    (A3 + "add3 1 [2 3]~\n", False), (A3 + "add3 1 2 [3]~\n", False), (A3 + "add4 1 2 [3 4]~\n", False), (A3 + "add2 [1 2 3]~\n", False),
    (A3 + "g : add3 xs ?\n\tadd3 xs~\ng add2 [1 2]\n", False),                     # 仮引数が同じ名前を隠す
    (A3 + "g : xs ?\n\tadd3 xs~\ng [1 2 3]\n", True),                            # 関数の中でも
    (A3 + "g : xs ?\n\tadd3 : a b ? a + b\n\tadd3 xs~\ng [1 2 3]\n", True),    # R128: 本体の `名前 : 値` は枝で局所の定義は無い(外の add3 のまま)
]
# 既知の食い違い: 実行で空になる変数の撒きは本物は断らないが、静的には分からないので出る
src_ = A3 + "g : xs ?\n\tadd3 xs~\ng []\n"
check("G19 既知の食い違い(実行で空の変数): 検査は出し・本物は断らない", (any(r["kind"] == "strict-G19" for r in js(src_, "--strict", "--no-hint")[1]["reports"]), "G19" in strict_run(src_)), (True, False))
for src_, want in G19:
    got = any(r["kind"] == "strict-G19" for r in js(src_, "--strict", "--no-hint")[1]["reports"])
    real = "G19" in strict_run(src_)
    check("G19 " + src_[len(A3):].replace("\n", "|").replace("\t", "")[:40], (got, real), (want, want))
# --check の呼び口(sign.py・sign_interp.py の両方)
for launcher in ("sign.py", "sign_interp.py"):
    pth = os.path.join(TMP, "t.sn")
    open(pth, "w", encoding="utf-8").write("f : x ?\n\tx + zz\nf 2\n")
    r = subprocess.run([sys.executable, os.path.join(HERE, launcher), "--check", pth, "--json"], capture_output=True, text=True, cwd=HERE, timeout=120)
    j = json.loads(r.stdout)
    check(f"{launcher} --check", (r.returncode, j["notes"], j["reports"][0]["line"]), (0, 1, 2))
    r = subprocess.run([sys.executable, os.path.join(HERE, launcher), pth], capture_output=True, text=True, cwd=HERE, timeout=120)
    check(f"{launcher} --check なしは今までどおり実行する", (r.returncode, r.stdout.strip()), (0, "2"))
# 同梱の物が読める(落ちない)
for fn in ("fib_bench.sn", "draw_circle.sn", "suika.sn", "std.sn", "font.sn"):
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign_check.py"), os.path.join(HERE, fn), "--json"], capture_output=True, text=True, cwd=HERE, timeout=120)
    check(f"{fn} を検査できる", r.returncode in (0, 1) and "reports" in json.loads(r.stdout), True)
print("\n全部 ok" if bad == 0 else f"\n{bad} 件 NG"); sys.exit(1 if bad else 0)
