#!/usr/bin/env python3
"""SQLite 装置(sign_db.py)と sqlite.sn の試験。python test_db.py"""
import os, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import sign_db as D

bad = 0
def check(name, got, want):
    global bad
    ok = got == want; bad += not ok
    print(("ok  " if ok else "NG  ") + name + ("" if ok else f"\n    得た: {got!r}\n    期待: {want!r}"))

ROOT = tempfile.mkdtemp()
d = D.Db(ROOT); d.mem = {}
P, Q, OUT = 0x600000, 0x610000, 0x620000
def putstr(p, s):
    b = s.encode("utf-8") if isinstance(s, str) else s
    for i, x in enumerate(b): d.mem[p + 4 * i] = x
    d.mem[p + 4 * len(b)] = 0
def getstr(p):
    o = bytearray(); i = 0
    while d.mem.get(p + 4 * i, 0): o.append(d.mem[p + 4 * i]); i += 1
    return o.decode("utf-8")
def call(n, a=0, b=0, c=0, e=0):
    for off, v in zip((D.NR, D.A0, D.A1, D.A2, D.A3), (n, a, b, c, e)): d.write(off, v)
    d.write(D.GO, 1); return d.read(D.RET)
def openm(name=":memory:", flags=0): putstr(P, name); return call(1, P, flags)
def sql(h, s): putstr(Q, s); return call(3, h, Q)
def prep(h, s): putstr(Q, s); return call(4, h, Q)

h = openm()
check("OPEN :memory: は 1 以上の番号", h >= 1, True)
check("EXEC CREATE は 0", sql(h, "CREATE TABLE t(id INTEGER PRIMARY KEY, name TEXT NOT NULL UNIQUE, n INTEGER, b BLOB)"), 0)
check("EXEC INSERT は変えた行数 1", sql(h, "INSERT INTO t(name, n) VALUES ('a', 1)"), 1)
check("LAST_ROWID", call(17, h), 1)
check("EXEC UPDATE 複数行", (sql(h, "INSERT INTO t(name, n) VALUES ('b', 2)"), sql(h, "UPDATE t SET n = n + 10")), (1, 2))
check("CHANGES", call(18, h), 2)
check("制約違反(UNIQUE)は -17", sql(h, "INSERT INTO t(name, n) VALUES ('a', 9)"), -17)
putstr(OUT, ""); n = call(19, h, OUT, 200)
check("ERRMSG に文面が入る", ("UNIQUE" in getstr(OUT), n == len(getstr(OUT))), (True, True))
check("NOT NULL 違反も -17", sql(h, "INSERT INTO t(name) VALUES (NULL)"), -17)
check("文法の誤りは -22", sql(h, "SELEC 1"), -22)
check("存在しない表は -22", sql(h, "SELECT * FROM nothing"), -22)
check("文が 2 つは -22(1 つずつ)", sql(h, "SELECT 1; SELECT 2"), -22)
check("空の SQL は -22", sql(h, "   "), -22)
check("存在しない h は -9", sql(99, "SELECT 1"), -9)

# --- 準備した文・束縛・読み出し ---
s = prep(h, "SELECT id, name, n FROM t WHERE n > ? ORDER BY id")
check("PREPARE は文の番号", s > h, True)
check("束縛なしの ? は NULL(比較は偽 → 行なし)", call(9, s), 0)
call(15, s); call(5, s, 1, 10)
check("STEP: 1 行目", call(9, s), 1)
check("COL_COUNT=3", call(10, s), 3)
check("COL_INT id", call(12, s, 0), 1)
check("COL_TYPE 整数/文字列", (call(11, s, 0), call(11, s, 1)), (1, 3))
check("COL_TEXT 'a'", (call(13, s, 1, OUT, 100), getstr(OUT)), (1, "a"))
check("COL_NAME", (call(14, s, 2, OUT, 100), getstr(OUT)), (1, "n"))
check("STEP: 2 行目、3 行目は無い", (call(9, s), call(12, s, 2), call(9, s), call(9, s)), (1, 12, 0, 0))
check("RESET でやり直し", (call(15, s), call(9, s), call(12, s, 0)), (0, 1, 1))
check("列番号の範囲外は -22", call(12, s, 7), -22)
check("FINALIZE のあとは -9", (call(16, s), call(9, s)), (0, -9))

# 束縛の安全(SQL 文字列に埋め込まない)
s = prep(h, "INSERT INTO t(name, n) VALUES (?, ?)")
putstr(Q, "x'); DROP TABLE t; --")
check("BIND_TEXT に SQL 風の文字列を入れても表は壊れない", (call(6, s, 1, Q), call(5, s, 2, 7), call(9, s), call(16, s)), (0, 0, 0, 0))
check("表は残っている", sql(h, "DELETE FROM t WHERE n = 7"), 1)
s = prep(h, "INSERT INTO t(name, n, b) VALUES ('z', ?, ?)")
check("BIND_INT 64 ビット端", (call(5, s, 1, 2**63 - 1), call(5, s, 1, -2**63)), (0, 0))
check("BIND_INT 範囲外は -75", (call(5, s, 1, 2**63), call(5, s, 1, -2**63 - 1)), (-75, -75))
check("BIND の番号 0 や ? の数より大は -22", (call(5, s, 0, 1), call(5, s, 3, 1)), (-22, -22))
for i, x in enumerate([0, 1, 255, 7]): d.mem[Q + 4 * i] = x
call(5, s, 1, 5); call(8, s, 2, Q, 4); call(9, s); call(16, s)
s = prep(h, "SELECT n, b, typeof(b) FROM t WHERE name = 'z'")
check("BLOB を入れて読む(バイト列は COL_TEXT でそのまま)", (call(9, s), call(11, s, 1), call(13, s, 1, OUT, 100), [d.mem[OUT + 4 * i] for i in range(4)]), (1, 4, 4, [0, 1, 255, 7]))
call(16, s)
s = prep(h, "SELECT ?"); d.mem[Q] = 300
check("BIND_BLOB に 0〜255 でない語は -22", call(8, s, 1, Q, 1), -22)
check("? の数より大きい番号は -22", call(5, s, 2, 1), -22)
call(16, s)

# 型いろいろ
s = prep(h, "SELECT NULL, 2.75, 'abc12', '  42xyz', x'00'")
call(9, s)
check("COL_TYPE: NULL/小数/文字/文字/バイト列", [call(11, s, i) for i in range(5)], [5, 2, 3, 3, 4])
check("COL_INT: NULL=0 小数は切る 文字は先頭の整数なし=0 空白つき=42 バイト列=0", [call(12, s, i) for i in range(5)], [0, 2, 0, 42, 0])
check("COL_TEXT 小数", (call(13, s, 1, OUT, 100), getstr(OUT)), (4, "2.75"))
check("COL_TEXT NULL は空で長さ 0", (call(13, s, 0, OUT, 100), getstr(OUT)), (0, ""))
call(16, s)
s = prep(h, "SELECT 'abcdefghij'")
call(9, s)
check("COL_TEXT: 小さいバッファは切って 0 終わり、返すのは本当の長さ", (call(13, s, 0, OUT, 4), getstr(OUT)), (10, "abc"))
check("COL_TEXT: max 0 は -22", call(13, s, 0, OUT, 0), -22)
s = prep(h, "SELECT -9223372036854775807 - 1, 1e30")
call(9, s)
check("COL_INT: 巨大な小数は範囲に収める", (call(12, s, 0), call(12, s, 1)), (-2**63, 2**63 - 1))
call(16, s)

# UTF-8
s = prep(h, "INSERT INTO t(name, n) VALUES (?, 0)")
putstr(Q, "日本語"); call(6, s, 1, Q); call(9, s); call(16, s)
s = prep(h, "SELECT name FROM t WHERE n = 0"); call(9, s)
n = call(13, s, 0, OUT, 100)
check("UTF-8 の往復(バイト数 9)", (n, getstr(OUT)), (9, "日本語"))

# 閉じる
s = prep(h, "SELECT 1")
check("CLOSE: 0、そのあと h も文も -9", (call(2, h), sql(h, "SELECT 1"), call(9, s)), (0, -9, -9))
check("CLOSE 二重は -9", call(2, h), -9)

# 取引
h = openm()
sql(h, "CREATE TABLE u(x)"); sql(h, "BEGIN"); sql(h, "INSERT INTO u VALUES (1)"); sql(h, "ROLLBACK")
s = prep(h, "SELECT count(*) FROM u"); call(9, s)
check("BEGIN/ROLLBACK で戻る", call(12, s, 0), 0)
sql(h, "BEGIN"); sql(h, "INSERT INTO u VALUES (1)"); sql(h, "COMMIT"); call(15, s); call(9, s)
check("COMMIT で残る", call(12, s, 0), 1)

# 守り
check("ATTACH は -95", sql(h, f"ATTACH DATABASE '{ROOT}/x.db' AS x"), -95)
check("VACUUM INTO は -95", sql(h, f"VACUUM INTO '{ROOT}/y.db'"), -95)
check("ATTACH したファイルが作られていない", sorted(os.listdir(ROOT)), [])
for bad_path in ("/etc/passwd", "../x.db", "a/../../x.db", "file:x.db", "C:x.db", "\\x.db", ""):
    check(f"OPEN {bad_path!r} は拒否", openm(bad_path), -95 if bad_path else -22)
check("OPEN flags が 0/1 以外は -22", openm("a.db", 2), -22)
check("読むだけで無いファイルは -2", openm("none.db", 1), -2)
check("フォルダの下に作れる", (openm("a.db") >= 1, os.path.exists(os.path.join(ROOT, "a.db"))), (True, True))
os.makedirs(os.path.join(ROOT, "sub")); check("下のフォルダも可", openm("sub/b.db") >= 1, True)
try: os.symlink("/tmp", os.path.join(ROOT, "link"))
except OSError: pass
check("シンボリックリンクで外へ出る名前は拒否", openm("link/evil.db"), -95)

# 永続と読むだけ
h = openm("p.db"); sql(h, "CREATE TABLE k(v)"); sql(h, "INSERT INTO k VALUES (5)"); call(2, h)
h2 = openm("p.db", 1)
s = prep(h2, "SELECT v FROM k"); call(9, s)
check("閉じて開き直すとデータが残る(読むだけで)", call(12, s, 0), 5)
check("読むだけに書くと -30", sql(h2, "INSERT INTO k VALUES (6)"), -30)

# 数の上限
d2 = D.Db(ROOT); d2.mem = d.mem
d.release()
d2.reg = {}
def call2(n, a=0, b=0, c=0, e=0):
    for off, v in zip((D.NR, D.A0, D.A1, D.A2, D.A3), (n, a, b, c, e)): d2.write(off, v)
    d2.write(D.GO, 1); return d2.read(D.RET)
putstr(P, ":memory:")
rs = [call2(1, P, 0) for _ in range(D.MAXOBJ + 1)]
check("開ける数に上限(64)、超えると -12", (rs[-2] > 0, rs[-1]), (True, -12))
d2.release()

# ゴミの引数で落ちない
d3 = D.Db(ROOT); d3.mem = {}
def call3(n, *a):
    d3.write(D.NR, n)
    for off, v in zip((D.A0, D.A1, D.A2, D.A3), a): d3.write(off, v)
    d3.write(D.GO, 1); return d3.read(D.RET)
check("未知の命令は -22", call3(99), -22)
check("アドレスが無効(メモリに無い)は -22", call3(1, 0x700000, 0), -22)
check("空の引数でも落ちない", [call3(n) for n in range(1, 20)].count(None), 0)

# --- Sign から ---
def run(src, *flags, root=None):
    with tempfile.NamedTemporaryFile("w", suffix=".sn", dir=HERE, delete=False) as f:
        f.write("`sqlite.sn`@~\n" + src); p = f.name
    try:
        r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p, "--db" + (f"={root}" if root else ""), *flags], capture_output=True, text=True, timeout=60, cwd=HERE)
        return (r.stdout + r.stderr).strip().splitlines()
    finally: os.unlink(p)

r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), os.path.join(HERE, "sqlite_demo.sn"), "--db"], capture_output=True, text=True, cwd=HERE, timeout=60)
check("sqlite_demo.sn", r.stdout.splitlines()[:2], ["2\tbanana\t12", "3\tcherry\t7"])
out = run("t : h ? seq4 (db_exec h `CREATE TABLE q(a, b)`) (db_exec h `INSERT INTO q VALUES (1, NULL), (2, 'x')`) (qq (db_prep h `SELECT a, b FROM q ORDER BY a`)) 0\nqq : s ?\n\t(db_step s) = 1 : seq2 (db_print_row s) (qq s)\n\t0\nt (db_open `:memory:` 0)")
check("db_print_row: NULL は空、タブ区切り", out[:2], ["1\t", "2\tx"])
out = run("t : z ? seq3 (println_int (db_open `/etc/passwd` 0)) (println_int (db_open `../x` 0)) (println_int (db_open `ok.db` 1)) 0\nt 0", root=ROOT)
check("Sign から拒否と -2", out[:3], ["-95", "-95", "-2"])
out = run("t : h ? seq4 (db_exec h `CREATE TABLE w(v)`) (add h 5) (add h 7) (println_int (db_close h)) 0\nadd : h v ? seq3 (db_bind_int (db_prep h `INSERT INTO w VALUES (?)`) 1 v) (db_step 3) 0\nt (db_open `s.db` 0)", root=ROOT)
check("Sign からファイルへ書く(文の番号は 1 つの h の次から)", os.path.exists(os.path.join(ROOT, "s.db")), True)
out = run("t : h ? seq3 (db_prep h `SELEC`) (db_errmsg h DB_TMP 200) (println_mem DB_TMP) 0\nt (db_open `:memory:` 0)")
check("Sign から ERRMSG(文法の誤りの文面)", "syntax" in " ".join(out), True)
out = run("t : z ? println_int (db_exec 1 `SELECT 1`)\nt 0")
check("開いていないのに使うと -9", out[0], "-9")

print("\n全部 ok" if not bad else f"\n{bad} 件 NG"); sys.exit(1 if bad else 0)
