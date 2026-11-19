#!/usr/bin/env python3
"""速い道(run_pure)を、括りの仮引数(`[h ~t]`・`[~board]`)の扱い(残りが空・整数を渡す)と `!__` の条件に広げた分の試験(n_queens の形)。速い道あり(既定)と無し(SIGN_NO_PURE=1)で、
同じ入力が同じ出力になることを確かめる(固定の例と乱数の例)。python test_pure_str.py"""
import os, random, subprocess, sys, tempfile, time
HERE = os.path.dirname(os.path.abspath(__file__))
bad = 0; N = [0]
def check(name, got, want):
    global bad
    ok = got == want; bad += not ok; N[0] += 1
    if not ok or "-v" in sys.argv: print(("ok  " if ok else "NG  ") + name + ("" if ok else f"\n    得た: {got!r}\n    期待: {want!r}"))
TMP = tempfile.mkdtemp()
import itertools
from concurrent.futures import ThreadPoolExecutor
_ctr = itertools.count()
def run(src, pure, timeout=120):
    p = os.path.join(TMP, "t%d.sn" % next(_ctr)); open(p, "w", encoding="utf-8").write(src)
    env = dict(os.environ); env["SIGN_NO_PURE"] = "0" if pure else "1"
    t = time.time()
    try: r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p], capture_output=True, text=True, timeout=timeout, env=env, cwd=HERE)
    except subprocess.TimeoutExpired: return ("timeout",), timeout
    return (r.returncode, r.stdout, r.stderr.replace(p, "T")), time.time() - t
PENDING = []
def same(name, src): PENDING.append((name, src))
def flush():
    def one(x): return x[0], run(x[1], True)[0], run(x[1], False)[0]
    with ThreadPoolExecutor(8) as ex:
        for name, a, b in ex.map(one, PENDING): check(name, a, b)
    PENDING.clear()

import itertools as _it
# --- n_queens(全解を数える形) ---
CNT = open(os.path.join(HERE, "nq_count.sn")).read() if os.path.exists(os.path.join(HERE, "nq_count.sn")) else None
NQ = """conflict : col dist [h ~t] ?
	h = col : !__
	h - col = dist : !__
	col - h = dist : !__
	conflict col (dist + 1) t

cnt_col : col row n [~board] ?
	col > n : 0
	(conflict col 1 board) : cnt_col (col + 1) row n board
	(place (row + 1) n (col board~)) + (cnt_col (col + 1) row n board)

place : row n [~board] ?
	row > n : 1
	cnt_col 1 row n board

first_row : col n ?
	col > n : 0
	(place 2 n col) + (first_row (col + 1) n)

first_row 1 %d
"""
for n in range(1, 8): same(f"n_queens 全解 n={n}", NQ % n)
# --- 括りの仮引数: 渡す形と残り ---
ARGS = ["5", "[5]", "[5 6]", "[5 6 7]", "[3 1 2 4]", "0", "(0 - 3)", "[1.5 2]", "[1.5]", "2.5"]
PATS = ["[~r]", "[h ~r]", "[a b ~r]", "[a b c ~r]", "[h]", "[a b]"]
BODIES = {
 "長さ": "||r||", "先頭": "h", "残りを渡す": "g r", "足す": "h + (g r)", "条件": "||r|| = 0 : 1\n\t2",
}
for pat in PATS:
    names = [x for x in pat.strip("[]").replace("~", " ").split()]
    for a in ARGS:
        for tag, b in (("長さ", "||%s||"), ("先頭", "%s ' 0"), ("そのまま", "%s")):
            for nm in names[-1:]:
                same(f"括り {pat} に {a} / {tag} {nm}", f"f : {pat} ?\n\t{b % nm}\nf {a}\n")
        if "~r" in pat:
            h = [x for x in names if x != "r"]
            first = h[0] if h else "0"
            same(f"括り {pat} の輪 {a}", f"g : {pat} acc ?\n\t||r|| = 0 : acc\n\tg r (acc + 1)\ng {a} 0\n".replace("g r (acc + 1)", "g r (acc + 1)"))
            same(f"括り {pat} の再帰(空で終わる) {a}", f"g : {pat} ?\n\t{first} + (g r)\ng {a}\n")
            same(f"括り {pat} の再帰(条件) {a}", f"g : {pat} ?\n\t||r|| = 0 : {first}\n\t{first} + (g r)\ng {a}\n")
            same(f"括り {pat} の呼び出し(条件) {a}", f"c : x {pat} ?\n\t{first} = x : !__\n\tc x r\nf : x l ?\n\t(c x l) : 1\n\t0\nf 3 {a}\n")
# --- `!__` ---
same("!__ を返す", "f : x ?\n\tx = 1 : !__\n\t5\nf 1\n")
same("!__ の条件", "c : x ?\n\tx = 1 : !__\nf : x ?\n\t(c x) : 10\n\t20\nseq2 (println_int (f 1)) (println_int (f 2))\n")
same("!__ を足す", "c : x ?\n\tx = 1 : !__\nf : x ?\n\t(c x) + 1\nf 1\n")
same("!__ を返す関数の値", "c : x ?\n\tx = 1 : !__\nf : x ?\n\tc x\nseq2 (println (show (f 1))) (println (show (f 2)))\n")
same("!__ と数の行", "c : x ?\n\tx = 1 : !__\n\tx = 2 : 7\nf : x ?\n\t(c x) : 10\n\t20\nf 2\n")
same("!__ を比べる", "c : x ?\n\tx = 1 : !__\nf : x ?\n\t(c x) = (c 1) : 1\n\t0\nf 1\n")
same("!__ を撒く", "c : x ?\n\tx = 1 : !__\nf : x ?\n\t(c x)~\nf 1\n")
same("!__ を括りに", "c : x ?\n\tx = 1 : !__\nf : x ?\n\t[(c x) 1]\nf 1\n")
same("!__ を再帰で", "c : x n ?\n\tn = 0 : !__\n\tx = n : 5\n\tc x (n - 1)\nf : x ?\n\t(c x 3) : 1\n\t0\nf 9\n")
# --- 最初の解を探す形(`|` と `__`。元の n_queens) ---
NQ1 = open("/dev/null").read() + """conflict : col dist [h ~t] ?
	h = col : !__
	h - col = dist : !__
	col - h = dist : !__
	conflict col (dist + 1) t

try_col : col row n [~board] ?
	col > n : __
	(conflict col 1 board) : try_col (col + 1) row n board
	(place (row + 1) n (col board~)) | try_col (col + 1) row n board

place : row n [~board] ?
	row > n : board
	try_col 1 row n board

first_row : col n ?
	col > n : __
	(place 2 n col) | first_row (col + 1) n

solve : n ? first_row 1 n

solve %d
"""
for n in range(1, 10): same(f"n_queens 最初の解 n={n}", NQ1 % n)
# --- 値の `a | b` と単位 `__` ---
same("| 左が値", "f : x ?\n\tx | 5\nf 3\n")
same("| 左が単位", "g : x ?\n\tx = 1 : 7\nf : x ?\n\t(g x) | 5\nseq2 (println_int (f 1)) (println_int (f 2))\n")
same("| 右も単位", "g : x ?\n\tx = 1 : 7\nf : x ?\n\t(g x) | (g 2)\nseq2 (println (show (f 1))) (println (show (f 2)))\n")
same("| 並べる", "g : x ?\n\tx = 1 : 7\nf : x ?\n\t(g x) | (g 3) | 9\nseq2 (println_int (f 1)) (println_int (f 2))\n")
same("| List", "g : x ?\n\tx = 1 : [7 8]\nf : x ?\n\t(g x) | [1 2]\nseq2 (println (show (f 1))) (println (show (f 2)))\n")
same("| 小数", "g : x ?\n\tx = 1 : 7.5\nf : x ?\n\t(g x) | 2\nseq2 (println (show (f 1))) (println (show (f 2)))\n")
same("| 文字", "g : x ?\n\tx = 1 : \\a\nf : x ?\n\t(g x) | \\b\nseq2 (println (show (f 1))) (println (show (f 2)))\n")
same("| 右は必要なときだけ(書き込み)", "g : x ?\n\tx = 1 : 7\nf : x ?\n\t(g x) | (0x4000 # 5)\nseq2 (println_int (f 1)) (println_int (@0x4000))\n")
same("| 右は必要なときだけ(書き込み 2)", "g : x ?\n\tx = 1 : 7\nf : x ?\n\t(g x) | (0x4000 # 5)\nseq2 (println_int (f 2)) (println_int (@0x4000))\n")
same("| 左の書き込み", "f : x ?\n\t(0x4000 # x) | 3\nseq2 (println_int (f 8)) (println_int (@0x4000))\n")
same("| 条件の中", "g : x ?\n\tx = 1 : 7\nf : x ?\n\t((g x) | (g 1)) = 7 : 1\n\t0\nf 2\n")
same("| 輪", "h : n acc ?\n\tn = 0 : acc\n\th (n - 1) (acc + 1)\ng : x ?\n\tx = 1 : 7\nf : x n ?\n\t(g x) | (h n 0)\nf 2 50\n")
same("__ を返す", "f : x ?\n\tx = 1 : __\n\t5\nseq2 (println (show (f 1))) (println_int (f 2))\n")
same("__ を渡す", "g : x ?\n\tx\nf : x ?\n\tg __\nf 1\n")
same("__ に足す", "f : x ?\n\tx + __\nf 1\n")
same("__ を括りに", "f : x ?\n\t[x __]\nf 1\n")
same("__ の行", "f : x ?\n\tx = 1 : __\n\tx = 2 : 7\n\t8\nseq2 (println (show (f 1))) (seq2 (println_int (f 2)) (println_int (f 3)))\n")
# --- 乱数 ---
rng = random.Random(int(next((a.split("=")[1] for a in sys.argv if a.startswith("--seed=")), "7")))
NR = int(next((a.split("=")[1] for a in sys.argv if a.startswith("--n=")), "60"))
EXPR = ["h", "a", "b", "||r||", "(h + 1)", "(a - b)", "col", "d", "(d + 1)", "(col + h)"]
CMP = ["=", "!=", "<", ">", "<=", ">="]
for t in range(NR):
    pat = rng.choice(["[h ~r]", "[a b ~r]", "[~r]", "[h ~r]"])
    nm = [x for x in pat.strip("[]").replace("~", " ").split() if x != "r"]
    pool = [e for e in EXPR if all(x in e or True for x in nm)]
    def ex():
        e = rng.choice(EXPR)
        for bad in ("h", "a", "b"):
            if bad in e.replace("||r||", "") and bad not in nm: e = "col"
        return e
    c1 = f"{ex()} {rng.choice(CMP)} {ex()}"; c2 = f"{ex()} {rng.choice(CMP)} {ex()}"
    r1 = rng.choice(["!__", "1", "col", "d"]); r2 = rng.choice(["!__", "2", "d", "col"])
    tail = rng.choice(["c col (d + 1) r", "c col d r", "c (col + 1) d r"])
    src = f"c : col d {pat} ?\n\t{c1} : {r1}\n\t{c2} : {r2}\n\t{tail}\nf : col d l ?\n\t(c col d l) : 100\n\t200\nf {rng.randint(0, 3)} {rng.randint(0, 2)} {rng.choice(ARGS)}\n"
    same(f"乱数 {t}: {src.splitlines()[1:4]} {src.splitlines()[-1]}", src)
flush()
b9 = NQ1 % 16
ra, ta = run(b9, True); rb, tb = run(b9, False)
check("n_queens 16 最初の解の答え", ra, rb); print(f"      n_queens(16 クイーンの最初の解): 速い道 {ta:.2f}s / 普通の道 {tb:.2f}s")
c8 = NQ % 8
ra, ta = run(c8, True); rb, tb = run(c8, False)
check("n_queens 8 全解の答え", ra, rb); print(f"      n_queens(8 クイーンの全解 92 通り): 速い道 {ta:.2f}s / 普通の道 {tb:.2f}s")
print(f"\n{N[0]} 件中 {bad} 件の食い違い"); print("全部 ok" if not bad else "NG あり"); sys.exit(1 if bad else 0)
