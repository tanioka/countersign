#!/usr/bin/env python3
"""速い道(run_pure)を文字(Char)・文字が混ざる List に広げた分の試験。速い道あり(既定)と無し(SIGN_NO_PURE=1)で、
同じ入力が同じ出力になることを確かめる(文字の算術・域の外・文字どうしの比べ・文字と数の比べ・混在 List・文字列に結合される並び)。python test_pure_char.py"""
import os, random, subprocess, sys, tempfile, time
HERE = os.path.dirname(os.path.abspath(__file__))
bad = 0
def check(name, got, want):
    global bad
    ok = got == want; bad += not ok
    print(("ok  " if ok else "NG  ") + name + ("" if ok else f"\n    得た: {got!r}\n    期待: {want!r}"))
TMP = tempfile.mkdtemp()
def run(src, pure, timeout=120):
    p = os.path.join(TMP, "t.sn"); open(p, "w", encoding="utf-8").write(src)
    env = dict(os.environ); env["SIGN_NO_PURE"] = "0" if pure else "1"
    t = time.time()
    try: r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p], capture_output=True, text=True, timeout=timeout, env=env, cwd=HERE)
    except subprocess.TimeoutExpired: return ("timeout",), timeout
    return (r.returncode, r.stdout, r.stderr), time.time() - t
def same(name, src):
    a, _ = run(src, True); b, _ = run(src, False)
    check(name, a, b); return a

CH = [r"\a", r"\b", r"\z", r"\A", r"\0", r"\ ", r"\~"]
# --- 文字の算術 ---
for op in "+-*/%":
    for a, b in ((r"\a", r"\b"), (r"\a", "3"), ("3", r"\a"), (r"\a", "0"), (r"\a", "1.5"), (r"\~", "1"), (r"\a", "0 - 100")):
        same(f"{a} {op} {b}", f"f : x y ?\n\tx {op} y\nf ({a}) ({b})\n")
# --- 比べ ---
for op in ("<", "<=", "=", "!=", ">", ">="):
    for a, b in ((r"\a", r"\b"), (r"\b", r"\b"), (r"\a", "97"), ("97", r"\a"), (r"\a", "1.5")):
        same(f"行の条件 {a} {op} {b}", f"f : x y ?\n\tx {op} y : 10\n\t20\nf ({a}) ({b})\n")
        same(f"値の比べ {a} {op} {b}", f"f : x y ?\n\tx {op} y\nf ({a}) ({b})\n")
# --- 輪・再帰 ---
same("文字をずらす輪", "h : c n ?\n\tn = 0 : c\n\th (c + 1) (n - 1)\nh \\a 5\n")
same("域の外に出る輪", "h : c n ?\n\tn = 0 : c\n\th (c + 20) (n - 1)\nh \\a 9\n")
same("文字の隔たりの和", "d : cs ?\n\t||cs|| < 2 : 0\n\t((cs ' 1) - (cs ' 0)) + (d (cs ' 1~))\nd [\\a \\c \\f \\b]\n")
same("文字の List の添字", "f : cs i ?\n\tcs ' i\nseq2 (println (f [\\a \\b \\c] 1)) (println (f [\\a \\b \\c] 3))\n")
same("文字の List の残り", "f : cs ?\n\tcs ' 1~\nf [\\a \\b \\c]\n")
same("文字の List の長さ", "f : cs ?\n\t||cs||\nseq2 (println_int (f [\\a \\b \\c])) (println_int (f \\a))\n")
same("文字の List どうしの =", "f : x y ?\n\tx = y : 10\n\t20\nf [\\a \\b] [\\a \\b]\n")
same("混在 List の和(数と文字)", "s : rs ?\n\t||rs|| <= 1 : rs ' 0\n\t(rs ' 0) + (s (rs ' 1~))\ns [1 \\a 2.5]\n")
same("混在 List の和(数だけ+小数)", "s : rs ?\n\t||rs|| <= 1 : rs ' 0\n\t(rs ' 0) + (s (rs ' 1~))\ns [1 2.5]\n")
same("混在 List の和(文字だけ)", "s : rs ?\n\t||rs|| <= 1 : rs ' 0\n\t(rs ' 0) + (s (rs ' 1~))\ns [\\a \\b]\n")
same("括りの分解(文字)", "f : [a b ~r] ?\n\tr = 0 : a - b\n\t(f r) + 1\nf [\\z \\a \\b \\c]\n")
same("文字を返す関数を非末尾で", "g : c ?\n\tc < \\z : c + 1\n\tc\nf : c ?\n\t(g c) = \\z : 1\n\t0\nf \\y\n")
same("文字を返す関数の答えを足す", "g : c ?\n\tc + 1\nh : c ?\n\t(g c) - \\a\nh \\c\n")
same("外の文字", "k : \\c\nf : x ?\n\tx - k\nf \\z\n")
same("外の文字の List", "ks : [\\a \\b]\nf : i ?\n\tks ' i\nf 1\n")
# --- 文字列に結合される並び(速い道に入れない) ---
same("文字の並び", "f : c ?\n\t[c c]\nf \\a\n")
same("文字と数の並び", "f : c ?\n\t[c 1]\nf \\a\n")
same("acc~ で文字を足す", "m : xs acc ?\n\t||xs|| = 0 : acc\n\tm (xs ' 1~) acc~ (xs ' 0)\nm [\\a \\b] [\\z]\n")
same("acc~ で文字を足す(整数 List へ)", "m : xs acc ?\n\t||xs|| = 0 : acc\n\tm (xs ' 1~) acc~ (xs ' 0)\nm [\\a \\b] [1]\n")
same("文字をメモリへ書く", "f : a v ?\n\tseq2 (a # v) (@a)\nf 0x4000 \\a\n")
same("文字を画面へ書く", "f : v ?\n\t0x9100000 # v\nf \\a\n")
same("文字列を渡す", "f : s ?\n\ts ' 0\nf `abc`\n")
same("負の文字", "f : c ?\n\t-c\nf \\a\n")
same("abs の文字", "f : c ?\n\t|c|\nf \\a\n")

# --- 乱数 ---
rng = random.Random(11)
def rv():
    r = rng.random()
    if r < .3: return rng.choice(["x", "y"])
    if r < .5: return rng.choice(["1", "2", "0", "3", "0 - 1"])
    if r < .6: return rng.choice(["1.5", "0.5"])
    return rng.choice([r"\a", r"\b", r"\c", r"\A", r"\~"])
def rexpr(d=0):
    if d > 2 or rng.random() < .4: return rv()
    return "(%s %s %s)" % (rexpr(d + 1), rng.choice("+-*+-/%"), rexpr(d + 1))
N = 0
for t in range(150):
    ce = rng.choice(["<", "<=", "=", ">", "!="])
    src = "f : x y ?\n\t%s %s %s : %s\n\t%s\n" % (rexpr(1), ce, rexpr(1), rexpr(), rexpr())
    args = " ".join(rng.choice([r"\a", r"\b", r"\z", "3", "0", "2.5", r"\ "]) for _ in range(2))
    a, _ = run(src + f"f {args}\n", True); b, _ = run(src + f"f {args}\n", False)
    if a != b: check("乱数の式 " + repr(src) + args, a, b)
    N += 1
for t in range(50):
    items = " ".join(rng.choice([r"\a", r"\b", r"\c", "1", "2", "2.5"]) for _ in range(rng.randint(1, 6)))
    S = rng.choice(["s : rs ?\n\t||rs|| <= 1 : rs ' 0\n\t(rs ' 0) + (s (rs ' 1~))\n", "d : rs ?\n\t||rs|| < 2 : 0\n\t((rs ' 1) - (rs ' 0)) + (d (rs ' 1~))\n"])
    nm = "s" if S.startswith("s") else "d"
    src = S + f"{nm} [{items}]\n"
    a, _ = run(src, True); b, _ = run(src, False)
    if a != b: check("乱数の List " + items, a, b)
    N += 1
print(f"ok  乱数 {N} 件を速い道あり/なしで比べた(食い違いなし)" if bad == 0 else "")

# --- 速さ ---
src = "h : c n ?\n\tn = 0 : c\n\th (c - 1 + 1) (n - 1)\nh \\h 300000\n"
a, ta = run(src, True); b, tb = run(src, False)
check("速さの試験の答え", a, b)
print(f"      文字の輪 30万回: 速い道 {ta:.2f}s / 普通の道 {tb:.2f}s")
print("\n全部 ok" if bad == 0 else f"\n{bad} 件 NG"); sys.exit(1 if bad else 0)
