#!/usr/bin/env python3
"""速い道(run_pure)を小数・小数の混ざる List に広げた分の試験。速い道あり(既定)と無し(SIGN_NO_PURE=1)で、
同じ入力が同じ出力になることを、端の値(0 で割る・1.0/0.0 の witness・整数と小数の混在・輪の途中で小数に変わる・-0.0 など)で確かめる。python test_pure_float.py"""
import os, random, subprocess, sys, tempfile, time
HERE = os.path.dirname(os.path.abspath(__file__))
bad = 0
def check(name, got, want):
    global bad
    ok = got == want; bad += not ok
    print(("ok  " if ok else "NG  ") + name + ("" if ok else f"\n    得た: {got!r}\n    期待: {want!r}"))
TMP = tempfile.mkdtemp()
def run(src, pure, timeout=120, dbg=False):
    p = os.path.join(TMP, "t.sn"); open(p, "w", encoding="utf-8").write(src)
    env = dict(os.environ); env["SIGN_NO_PURE"] = "0" if pure else "1"
    if dbg: env["SIGN_PURE_DEBUG"] = "1"
    t = time.time()
    try: r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p], capture_output=True, text=True, timeout=timeout, env=env, cwd=HERE)
    except subprocess.TimeoutExpired: return ("timeout",), timeout
    return (r.returncode, r.stdout, r.stderr), time.time() - t
def same(name, src):
    a, _ = run(src, True); b, _ = run(src, False)
    check(name, a, b); return a
def fast(name, src, fname):
    """速い道に乗る(乗らない旨の知らせが出ない)ことも確かめる"""
    a, _ = run(src, True, dbg=True)
    check(name + " (速い道に乗る)", fname in a[2] and "速い道に乗らない" in a[2].split(fname)[0][-80:] + a[2].split(fname)[1][:5] if False else ("速い道に乗らない: " + fname) not in a[2], True)

# --- 四則・割り算・剰余 ---
for op in "+-*/%":
    for a, b in (("7", "2"), ("7.0", "2"), ("7", "2.0"), ("7.5", "2.5"), ("0.0", "3"), ("0 - 7.5", "2"), ("7", "0 - 2.0"), ("7", "0"), ("7.5", "0.0"), ("7.5", "0"), ("0", "0.0")):
        same(f"{a} {op} {b}", f"f : x y ?\n\tx {op} y\nf ({a}) ({b})\n")
same("符号", "f : x ?\n\t(0 - x)\nseq2 (println (f 1.5)) (println (f 0.0))\n")
same("負の 0.0", "f : x ?\n\t-x\nprintln (f 0.0)\n")
same("abs", "f : x ?\n\t|x|\nseq2 (println (f (0 - 2.5))) (println (f (0 - 3)))\n")
same("ビット演算に小数", "f : x y ?\n\tx && y\nf 3.0 1\n")
same("ビット演算(整数のまま)", "f : x y ?\n\tx && y\nf 3 1\n")

# --- 比べ・witness ---
LT = "lt : a b ?\n\ta < b\n"
for a, b in (("0.0", "5"), ("1.0", "5.5"), ("1", "5.5"), ("7.5", "5"), ("3.0", "3"), ("0", "0.0"), ("1.0", "1")): same(f"比べの値 lt {a} {b}", LT + f"lt {a} {b}\n")
for op in ("<", "<=", "=", "!=", ">", ">="):
    for a, b in (("1.5", "1.5"), ("1", "1.0"), ("2.5", "1"), ("1", "2.5")):
        same(f"行の条件 {a} {op} {b}", f"f : x y ?\n\tx {op} y : 10\n\t20\nf {a} {b}\n")
same("= で 1 要素の List と小数", "f : x ?\n\tx = 1.5 : 10\n\t20\nf [1.5]\n")
same("List どうしの =", "f : x y ?\n\tx = y : 10\n\t20\nf [1.5 2] [1.5 2]\n")
same("List どうしの = (整数と小数)", "f : x y ?\n\tx = y : 10\n\t20\nf [1 2] [1.0 2]\n")

# --- 再帰・輪 ---
same("輪の途中で小数に変わる", "h : x n ?\n\tn = 0 : x\n\th (x / 2 + 0.5) (n - 1)\nh 7 10\n")
same("整数のまま回る", "h : x n ?\n\tn = 0 : x\n\th (x + 3) (n - 1)\nh 7 10\n")
same("小数が先", "h : x n ?\n\tn = 0 : x\n\th (x * 0.5) (n - 1)\nh 64.0 10\n")
same("輪の途中で 0 割り", "h : x n ?\n\tn = 0 : x\n\th (10.0 / (x - 3)) (n - 1)\nh 5 4\n")
same("非末尾再帰(小数)", "f : x ?\n\tx < 0.01 : x\n\t(f (x / 2)) + x\nf 3.0\n")
same("fib 風(小数)", "f : x ?\n\tx < 2.0 : x\n\t(f (x - 1)) + (f (x - 2))\nf 12.5\n")
same("整数の fib と小数の fib を同じ関数で", "f : x ?\n\tx < 2 : x\n\t(f (x - 1)) + (f (x - 2))\nseq2 (println (f 15)) (println (f 15.0))\n")
same("メモ(1 と 1.0 を同じ鍵にしない)", "f : x ?\n\tx < 2 : x / 2\n\t(f (x - 1)) + (f (x - 1))\nseq2 (println (f 3)) (println (f 3.0))\n")
same("相互再帰(小数)", "ev : x ?\n\tx < 1 : x\n\tod (x - 1.5)\nod : x ?\n\tx < 1 : x + 0.25\n\tev (x - 0.5)\nev 9.0\n")
same("外の小数", "k : 0.25\nf : x ?\n\tx + k\nf 1\n")
same("外の小数 List", "ks : [0.5 1 2.5]\nf : i ?\n\tks ' i\nseq2 (println (f 0)) (println (f 2))\n")

# --- 小数・混在の List ---
S = "s : rs ?\n\t||rs|| <= 1 : rs ' 0\n\t(rs ' 0) + (s (rs ' 1~))\n"
for l in ("[1.5]", "[1.5 2 3.25]", "[1 2 3]", "[0.5 0.25]", "[2 0.5]"): same(f"小数の List の和 {l}", S + f"s {l}\n")
same("範囲外の添字", "f : rs i ?\n\trs ' i\nseq2 (println (f [1.5 2 3] 2)) (println (f [1.5 2 3] 3))\n")
same("残りが空になる", "f : rs ?\n\t(rs ' 3~) | 77\nf [1.5 2 3]\n")
same("残り", "f : rs ?\n\trs ' 1~\nf [1.5 2 3.5]\n")
same("||x|| (小数は 1)", "f : x ?\n\t||x||\nseq2 (println_int (f 5.5)) (println_int (f [1.5 2 3]))\n")
same("括りの分解(小数)", "f : [a b ~r] ?\n\tr = 0 : a + b\n\t(f r) + a\nf [1.5 2 3 0.5]\n")
same("括りの分解(整数の List が小数に変わる)", "f : [a b ~r] ?\n\t||r|| < 1 : a + b\n\tf [(a + 0.5) (b * 2) r]\nf [1 2 3 4]\n")
same("acc~ で小数を足す", "m : xs acc ?\n\t||xs|| = 0 : acc\n\tm (xs ' 1~) acc~ ((xs ' 0) * 1.5)\nm [1 2 3] [0]\n")
same("acc~ (整数 List に小数を足す)", "m : xs acc ?\n\t||xs|| = 0 : acc\n\tm (xs ' 1~) acc~ ((xs ' 0) / 2.0)\nm [1 2 3] [9]\n")
same("acc~ (小数 List に整数を足す)", "m : xs acc ?\n\t||xs|| = 0 : acc\n\tm (xs ' 1~) acc~ ((xs ' 0) + 1)\nm [1 2 3] [0.5]\n")
same("値の並びに小数", "f : x ?\n\t[x (x * 2.0) 3]\nf 1.5\n")
same("値の並びに小数(整数も)", "f : x ?\n\t[x (x * 2) 3]\nf 2\n")
same("List の要素が bool 的な値", "f : xs ?\n\txs ' 0\nf [1 2.0]\n")
same("空の List", S + "s []\n")
same("文字が混ざる List は普通の道", S + "s [1.5 `a` 3]\n")

# --- メモリ ---
same("小数をメモリへ書く・読む", "f : a v ?\n\tseq2 (a # v) (@a)\nf 0x4000 1.5\n")
same("小数を書く(読みは整数)", "f : a v ?\n\tseq2 (a # v) (@a + 1)\nf 0x4000 3\n")
same("小数を書いて整数として読む", "f : a v ?\n\tseq2 (a # v) (@a + 1)\nf 0x4000 3.5\n")
same("小数を画面へ書く", "f : v ?\n\t0x9100000 # v\nf 1.5\n")

# --- 乱数 ---
rng = random.Random(7)
def rnum():
    r = rng.random()
    if r < .25: return str(rng.randint(0, 5))
    if r < .5: return "%d.%d" % (rng.randint(0, 5), rng.randint(0, 9))
    if r < .6: return "0.0"
    return rng.choice(["x", "y", "x", "y", "k"])
def rexpr(d=0):
    if d > 2 or rng.random() < .35: return rnum()
    op = rng.choice("+-*/%+-*")
    return "(%s %s %s)" % (rexpr(d + 1), op, rexpr(d + 1))
N = 0
for t in range(120):
    ce = rng.choice(["<", "<=", "=", ">", "!="])
    src = "k : %s\nf : x y ?\n\t%s %s %s : %s\n\t%s\n" % (rng.choice(["2", "0.5", "3.0"]), rexpr(1), ce, rexpr(1), rexpr(), rexpr())
    args = " ".join(rng.choice(["0", "1", "2", "7", "0.0", "1.0", "2.5", "7.25", "3"]) for _ in range(2))
    a, _ = run(src + f"f {args}\n", True); b, _ = run(src + f"f {args}\n", False)
    if a != b: check("乱数の式 " + repr(src) + args, a, b)
    N += 1
for t in range(60):
    f1 = rng.choice(["x * 0.5", "x / 2", "x + 1", "x / 3.0", "x - 0.75", "x * 3 + 1", "x % 7", "x % 2.5"])
    c = rng.choice(["n = 0", "n <= 0"])
    src = "h : x n ?\n\t%s : x\n\th (%s) (n - 1)\n" % (c, f1)
    a0 = rng.choice(["7", "64.0", "3.5", "0", "0.0"]); n0 = rng.randint(0, 12)
    a, _ = run(src + f"h {a0} {n0}\n", True); b, _ = run(src + f"h {a0} {n0}\n", False)
    if a != b: check("乱数の輪 " + repr(src) + a0, a, b)
    N += 1
for t in range(40):
    vs = " ".join(rng.choice(["1", "2", "3", "1.5", "0.25", "4.0"]) for _ in range(rng.randint(1, 6)))
    src = S + f"s [{vs}]\n"
    a, _ = run(src, True); b, _ = run(src, False)
    if a != b: check("乱数の List の和 " + vs, a, b)
    N += 1
print(f"ok  乱数 {N} 件を速い道あり/なしで比べた(食い違いなし)" if bad == 0 else "")

# --- 速さ ---
src = "h : x n ?\n\tn = 0 : x\n\th (x * 0.999 + 0.001) (n - 1)\nh 100.0 300000\n"
a, ta = run(src, True); b, tb = run(src, False)
check("速さの試験の答え", a, b)
print(f"      小数の輪 30万回: 速い道 {ta:.2f}s / 普通の道 {tb:.2f}s")
print("\n全部 ok" if bad == 0 else f"\n{bad} 件 NG"); sys.exit(1 if bad else 0)
