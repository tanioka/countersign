#!/usr/bin/env python3
"""速い道(run_pure)を撒き `x~` と List の連結に広げた分の試験。速い道あり(既定)と無し(SIGN_NO_PURE=1)で同じ出力になることを確かめる。python test_pure_cat.py"""
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

FORMS = ["[x~ y~]", "x~ y~", "[x~ 5 y~]", "[5 x~]", "x~ 5", "[x~ y]", "[x y~]", "[x y]", "x~ y~ x~", "5 6 x~ 7", "[x~ (y ' 0)]", "[x~ 1.5 y~]", "x~ y~ 2.5",
         "[(x ' 1~)~ y~]", "[x~ (y ' 5~)~]", "[x~ (y ' 5~)]", "(x ' 0) y~", "[x~]", "x~", "||[x~ y~]||", "([x~ y~]) ' 2", "[x~ y~] ' 9"]
ARGS = [("[1 2]", "[3 4]"), ("[1 2 3]", "[4]"), ("[1.5 2]", "[3 4]"), ("[1]", "[2.5]"), ("[1 2]", "5"), ("5", "[1 2]"), ("5", "6"), ("[]", "[1]"), ("[1 \\a]", "[2]"), ("[\\a]", "[\\b]")]
for f in FORMS:
    for x, y in ARGS:
        same(f"{f} / {x} {y}", f"r : x y ?\n\t{f}\nr {x} {y}\n")
# 空の残り
same("残りが空", "r : xs ?\n\t[(xs ' 3~)~ 5]\nr [1 2 3]\n")
same("残りが空でない", "r : xs ?\n\t[(xs ' 1~)~ 5]\nr [1 2 3]\n")
# 輪(acc~)。引数の `acc~ …` は括弧で 1 つの引数にする
same("acc~ y~", "m : xs acc ?\n\t||xs|| = 0 : acc\n\tm (xs ' 1~) (acc~ [(xs ' 0) (xs ' 0)]~)\nm [1 2 3] [0 0]\n")
same("acc~ 別の List", "m : n acc ys ?\n\tn = 0 : acc\n\tm (n - 1) (acc~ ys~ 1) ys\nm 3 [0 1] [7 8]\n")
same("acc~ 別の List(撒きだけ)", "m : n acc ys ?\n\tn = 0 : acc\n\tm (n - 1) (acc~ ys~) ys\nm 3 [0 1] [7 8]\n")
same("acc~ 小数の List", "m : n acc ys ?\n\tn = 0 : acc\n\tm (n - 1) (acc~ ys~) ys\nm 3 [0 1] [7.5 8]\n")
same("acc~ 整数の List に小数の List", "m : n acc ys ?\n\tn = 0 : acc\n\tm (n - 1) (acc~ ys~ 1) ys\nm 3 [0 1] [7.5 8]\n")
same("acc~ 文字の List", "m : n acc ys ?\n\tn = 0 : acc\n\tm (n - 1) (acc~ ys~) ys\nm 3 [\\a \\b] [\\c \\d]\n")
same("2 つの List に足す(共有しない)", "m : n a b ?\n\tn = 0 : [a~ b~]\n\tm (n - 1) (b~ 1) (a~ 2)\nm 3 [0 5] [9 4]\n")
same("2 つの List に足す(撒きだけ)", "m : n a b ?\n\tn = 0 : [a~ b~]\n\tm (n - 1) (b~ 1) (a~ 1)\nm 3 [0 5] [9 4]\n")
same("acc に acc を足す", "m : n acc ?\n\tn = 0 : acc\n\tm (n - 1) (acc~ acc~)\nm 4 [1 2]\n")
same("acc に 添字の List を足す", "m : n acc ?\n\tn = 0 : acc\n\tm (n - 1) (acc~ (acc ' 1~)~)\nm 4 [1 2 3]\n")
same("連結を返す再帰", "c : n ?\n\tn = 0 : [9]\n\t[(c (n - 1))~ n]\nc 5\n")
same("連結を返す再帰(前)", "c : n ?\n\tn = 0 : [9]\n\t[n (c (n - 1))~]\nc 5\n")
same("文字列に結合される並び", "r : c ?\n\t[c~ 1]\nr \\a\n")
same("文字の List の連結", "r : x y ?\n\tx~ y~\nr [\\a \\b] [\\c]\n")
same("文字の List に整数", "r : x y ?\n\tx~ y\nr [\\a \\b] 1\n")
# 乱数
rng = random.Random(5)
def item(d):
    r = rng.random()
    if r < .3: return rng.choice(["x~", "y~"])
    if r < .5: return rng.choice(["1", "2", "7", "1.5"])
    if r < .6: return "(x ' 0)"
    if r < .7: return "(y ' 0)"
    if r < .8: return "(x ' 1~)~"
    return rng.choice(["x", "y"])
N = 0
for t in range(120):
    its = " ".join(item(0) for _ in range(rng.randint(2, 5)))
    f = rng.choice(["[%s]", "%s", "||[%s]||", "[%s] ' 1", "[%s] ' 4"]) % its
    x, y = rng.choice(ARGS)
    src = f"r : x y ?\n\t{f}\nr {x} {y}\n"
    a, _ = run(src, True); b, _ = run(src, False)
    if a != b: check("乱数 " + repr(src), a, b)
    N += 1
print(f"ok  乱数 {N} 件を速い道あり/なしで比べた(食い違いなし)" if bad == 0 else "")
# 速さ
src = "m : n acc ys ?\n\tn = 0 : ||acc||\n\tm (n - 1) (acc~ ys~) ys\nm 20000 [0 1] [7 8 9]\n"
a, ta = run(src, True); b, tb = run(src, False)
check("速さの試験の答え", a, b)
print(f"      acc~ ys~ 2万回: 速い道 {ta:.2f}s / 普通の道 {tb:.2f}s")
print("\n全部 ok" if bad == 0 else f"\n{bad} 件 NG"); sys.exit(1 if bad else 0)
