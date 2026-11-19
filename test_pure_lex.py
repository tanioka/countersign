#!/usr/bin/env python3
"""字句解析器(bench/lex_big.sn の定義部)を使い、String を分解して渡す形(`[~s]`・`[c ~rest]`・`!s`)が
速い道あり/無しで同じ出力になることを確かめる。固定の例+乱数の文字列+lex_big.sn そのもの。python test_pure_lex.py"""
import os, random, sys
sys.argv_saved = sys.argv
import importlib.util
spec = importlib.util.spec_from_file_location("tps", os.path.join(os.path.dirname(os.path.abspath(__file__)), "test_pure_str.py"))
HERE = os.path.dirname(os.path.abspath(__file__))
# test_pure_str は読み込み時に全試験を走らせるので使わず、同じ小さな道具をここに持つ
import subprocess, tempfile, itertools
from concurrent.futures import ThreadPoolExecutor
TMP = tempfile.mkdtemp(); _c = itertools.count(); bad = 0
def run(src, pure):
    p = os.path.join(TMP, "t%d.sn" % next(_c)); open(p, "w", encoding="utf-8").write(src)
    env = dict(os.environ); env["SIGN_NO_PURE"] = "0" if pure else "1"
    try: r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p], capture_output=True, text=True, timeout=180, env=env, cwd=HERE)
    except subprocess.TimeoutExpired: return ("timeout",)
    return (r.returncode, r.stdout, r.stderr.replace(p, "T"))
src_lex = open(os.path.join(HERE, "bench", "lex_big.sn"), encoding="utf-8").read()
defs = src_lex.split("`実行例`")[0]
cases = [("lex_big", src_lex)]
fixed = ["", " ", "a", "foo 123 + bar42", "(x y) z", "[a [b c]] d", "`s t` u", "a `x y`", "`abc", "(a b", "a)", "  a   b  ",
         "f : x ?\n\tx + 1", "a\\b c", "{ } [ ] ( )", "a `b` `c d` e"]
alpha = list("ab 1+()[]{}`\\\n\t_")
rnd = random.Random(7)
for _ in range(80): fixed.append("".join(rnd.choice(alpha) for _ in range(rnd.randint(0, 30))))
for i, s in enumerate(fixed):
    if "`" in s and s.count("`") % 2: continue
    lit = "`" + s.replace("`", "") + "`" if "`" not in s else None
    if lit is None: continue
    if "\n" in s or "\t" in s: continue
    cases.append((f"tokens#{i} {s!r}", defs + f"println_int ||tokens {lit}||\n"))
    cases.append((f"take_word#{i} {s!r}", defs + f"println_int ||take_word 0 {lit}||\n"))
    cases.append((f"drop_space#{i} {s!r}", defs + f"println_int ||drop_space {lit}||\n"))
def one(c): return c[0], run(c[1], True), run(c[1], False)
n = 0
with ThreadPoolExecutor(8) as ex:
    for name, a, b in ex.map(one, cases):
        n += 1
        if a != b: bad += 1; print("NG", name, "\n  fast:", a, "\n  slow:", b)
print(f"{n} 件中 {bad} 件の不一致")
sys.exit(1 if bad else 0)
