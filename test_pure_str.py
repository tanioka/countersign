#!/usr/bin/env python3
"""速い道(run_pure)を String の引数、文字が混ざる List の `acc~`・連結に広げた分の試験。速い道あり(既定)と無し(SIGN_NO_PURE=1)で、
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

# --- String の引数 ---
S = ["`abc`", "`a`", "`abcabca`", "`zzz`", "`ab c`", "`あいう`", "`1a2`"]
for s in S:
    same(f"添字 {s}", f"f : s i ?\n\ts ' i\nseq2 (println (f {s} 0)) (println (f {s} 2))\n")
    same(f"長さ {s}", f"f : s ?\n\t||s||\nprintln_int (f {s})\n")
    same(f"残り {s}", f"f : s ?\n\ts ' 1~\nf {s}\n")
    same(f"範囲外 {s}", f"f : s i ?\n\ts ' i\nf {s} 9\n")
    same(f"負の添字 {s}", f"f : s i ?\n\ts ' i\nf {s} (0 - 1)\n")
    same(f"残りの後ろ {s}", f"f : s ?\n\ts ' 9~\nf {s}\n")
    for op in ("=", "!=", "<", "<=", ">", ">="):
        for t in S[:4] + [r"\a", r"\b"]:
            same(f"行の比べ {s} {op} {t}", f"f : s t ?\n\ts {op} t : 10\n\t20\nf {s} {t}\n")
    same(f"文字との比べ {s}", f"f : s ?\n\t(s ' 0) = \\a : 1\n\t0\nf {s}\n")
    same(f"文字の算術 {s}", f"f : s ?\n\t(s ' 0) + 1\nf {s}\n")
    same(f"文字の算術2 {s}", f"f : s ?\n\t(s ' 0) - (s ' 1)\nf {s}\n")
    same(f"そのまま返す {s}", f"f : s ?\n\ts\nf {s}\n")
    same(f"数と足す {s}", f"f : s ?\n\ts + 1\nf {s}\n")
    same(f"s と s の足し {s}", f"f : s ?\n\ts + s\nf {s}\n")
    same(f"値の並び {s}", f"f : s ?\n\t[s s]\nf {s}\n")
    same(f"値の比べ {s}", f"f : s t ?\n\ts = t\nf {s} {s}\n")
    same(f"撒き {s}", f"f : s ?\n\ts~\nf {s}\n")
    same(f"撒きの連結 {s}", f"f : s ?\n\ts~ s~\nf {s}\n")
    same(f"括りに渡す {s}", f"f : [a b ~r] ?\n\ta\nf {s}\n")
    same(f"メモリへ {s}", f"f : s ?\n\t0x4000 # s\nf {s}\n")
# 輪・再帰
same("文字を数える輪", "cnt : s i n ?\n\ti = ||s|| : n\n\t(s ' i) = \\a : cnt s (i + 1) (n + 1)\n\tcnt s (i + 1) n\ncnt `abcabcabca` 0 0\n")
same("残りで数える", "cnt : s n ?\n\t(s ' 0) = \\z : n\n\tcnt (s ' 1~) (n + 1)\ncnt `abcabcz` 0\n")
same("残りで数える(最後まで)", "cnt : s n ?\n\t||s|| = 0 : n\n\tcnt (s ' 1~) (n + 1)\ncnt `abcabc` 0\n")
same("残りが空になる", "cnt : s n ?\n\t(s ' 0) = \\z : n\n\tcnt (s ' 1~) (n + 1)\ncnt `abc` 0\n")
same("文字コードの和", "sm : s i acc ?\n\ti = ||s|| : acc\n\tsm s (i + 1) (acc + (s ' i))\nsm `abc` 0 0\n")
same("文字コードの和(整数)", "sm : s i acc ?\n\ti = ||s|| : acc\n\tsm s (i + 1) (acc + ((s ' i) - \\a))\nsm `abc` 0 0\n")
same("String を返す再帰", "f : s n ?\n\tn = 0 : s\n\tf (s ' 1~) (n - 1)\nf `abcdef` 2\n")
same("String を返す再帰(空になる)", "f : s n ?\n\tn = 0 : s\n\tf (s ' 1~) (n - 1)\nf `abcdef` 9\n")
same("String を返さない行がある", "f : s n ?\n\tn = 0 : s\n\t0\nf `ab` 1\n")
same("String か単位", "f : s n ?\n\tn = 0 : s\nf `ab` 1\n")
same("String を受ける別の関数", "g : s ?\n\t||s||\nf : s ?\n\t(g s) + (g (s ' 1~))\nf `abcd`\n")
same("String を返す関数を呼ぶ", "g : s ?\n\ts ' 1~\nf : s ?\n\t||g s||\nf `abcd`\n")
same("String を返す関数の比べ", "g : s ?\n\ts ' 1~\nf : s ?\n\t(g s) = `bcd` : 1\n\t0\nf `abcd`\n")
same("外の String", "k : `abc`\nf : i ?\n\tk ' i\nf 1\n")
same("外の String(String の引数あり)", "k : `abc`\nf : s i ?\n\t(s ' i) = (k ' i) : 1\n\t0\nf `xbz` 1\n")
same("リテラルの String", "f : s ?\n\ts = `abc` : 1\n\t0\nf `abc`\n")
same("リテラルの String の比べ(異なる)", "f : s ?\n\ts = `abd` : 1\n\t0\nf `abc`\n")
same("空の String", "f : s ?\n\t||s||\nf ``\n")
same("1文字の String と文字", "f : s ?\n\ts = \\a : 1\n\t0\nf `a`\n")
same("残りが 1 文字", "f : s ?\n\t(s ' 1~) = \\b : 1\n\t0\nf `ab`\n")
same("残りの残り", "f : s ?\n\t(s ' 1~) ' 1~\nf `abc`\n")
same("残りの添字", "f : s ?\n\t(s ' 1~) ' 1\nf `abc`\n")
same("添字が式", "f : s i ?\n\ts ' (i + 1)\nf `abc` 1\n")
same("残りの位置が式", "f : s i ?\n\ts ' (i + 1)~\nf `abc` 1\n")
same("String と List を両方", "f : s xs ?\n\t(s ' 0) = (xs ' 0) : 1\n\t0\nf `a` [\\a \\b]\n")
same("String と数の比べ", "f : s ?\n\ts = 1 : 1\n\t0\nf `a`\n")
same("String と List の比べ", "f : s xs ?\n\ts = xs : 1\n\t0\nf `ab` [\\a \\b]\n")

# --- 文字が混ざる List の acc~・連結 ---
same("acc~ 文字の List(撒き)", "m : n acc ys ?\n\tn = 0 : acc\n\tm (n - 1) (acc~ ys~) ys\nm 3 [\\a \\b] [\\c \\d]\n")
same("acc~ 文字 1 つ", "m : n acc c ?\n\tn = 0 : acc\n\tm (n - 1) (acc~ c) c\nm 3 [1 2] \\c\n")
same("acc~ 文字 1 つ(文字の List へ)", "m : n acc c ?\n\tn = 0 : acc\n\tm (n - 1) (acc~ c) c\nm 3 [\\a \\b] \\c\n")
same("acc~ 文字 2 つ(結合される)", "m : n acc c d ?\n\tn = 0 : acc\n\tm (n - 1) (acc~ c d) c d\nm 3 [\\a \\b] \\c \\d\n")
same("acc~ 文字 2 つ(数の List)", "m : n acc c d ?\n\tn = 0 : acc\n\tm (n - 1) (acc~ c d) c d\nm 3 [1 2] \\c \\d\n")
same("acc~ 数 文字", "m : n acc c ?\n\tn = 0 : acc\n\tm (n - 1) (acc~ 1 c) c\nm 3 [1 2] \\c\n")
same("acc~ 文字 数", "m : n acc c ?\n\tn = 0 : acc\n\tm (n - 1) (acc~ c 1) c\nm 3 [1 2] \\c\n")
same("acc~ 数 数", "m : n acc c ?\n\tn = 0 : acc\n\tm (n - 1) (acc~ 1 2) c\nm 3 [\\a \\b] \\c\n")
same("acc~ 撒き 文字", "m : n acc ys c ?\n\tn = 0 : acc\n\tm (n - 1) (acc~ ys~ c) ys c\nm 3 [\\a \\b] [1 2] \\c\n")
same("acc~ 文字 撒き", "m : n acc ys c ?\n\tn = 0 : acc\n\tm (n - 1) (acc~ c ys~) ys c\nm 3 [\\a \\b] [1 2] \\c\n")
same("acc~ 撒き 文字 撒き", "m : n acc ys c ?\n\tn = 0 : acc\n\tm (n - 1) (acc~ ys~ c ys~) ys c\nm 3 [\\a \\b] [1 2] \\c\n")
same("acc~ 文字 + 1", "m : n acc c ?\n\tn = 0 : acc\n\tm (n - 1) (acc~ (c + 1)) (c + 1)\nm 3 [\\a \\b] \\c\n")
same("acc~ 添字で文字", "m : xs acc i ?\n\ti = ||xs|| : acc\n\tm xs (acc~ (xs ' i)) (i + 1)\nm [\\a \\b \\c] [\\z \\y] 0\n")
same("acc~ 添字で文字(数の List へ)", "m : xs acc i ?\n\ti = ||xs|| : acc\n\tm xs (acc~ (xs ' i)) (i + 1)\nm [\\a \\b \\c] [1 2] 0\n")
same("acc~ String の添字", "m : s acc i ?\n\ti = ||s|| : acc\n\tm s (acc~ (s ' i)) (i + 1)\nm `abc` [\\z \\y] 0\n")
same("acc~ String の添字(数の List へ)", "m : s acc i ?\n\ti = ||s|| : acc\n\tm s (acc~ (s ' i)) (i + 1)\nm `abc` [1 2] 0\n")
same("acc~ String の添字 2 つ", "m : s acc i ?\n\ti = ||s|| - 1 : acc\n\tm s (acc~ (s ' i) (s ' (i + 1))) (i + 1)\nm `abc` [\\z \\y] 0\n")
same("acc~ 小数と文字", "m : n acc c ?\n\tn = 0 : acc\n\tm (n - 1) (acc~ 1.5 c) c\nm 3 [1 2] \\c\n")
same("acc~ 小数 小数", "m : n acc ?\n\tn = 0 : acc\n\tm (n - 1) (acc~ 1.5 2.5)\nm 3 [\\a \\b]\n")
same("連結 文字の List どうし", "f : xs ys ?\n\txs~ ys~\nf [\\a \\b] [\\c \\d]\n")
same("連結 文字の List と数の List", "f : xs ys ?\n\txs~ ys~\nf [\\a \\b] [1 2]\n")
same("連結 文字の List と文字", "f : xs c ?\n\txs~ c\nf [\\a \\b] \\c\n")
same("連結 文字と文字の List", "f : xs c ?\n\tc xs~\nf [\\a \\b] \\c\n")
same("連結 文字 2 つ", "f : xs c d ?\n\txs~ c d\nf [\\a \\b] \\c \\d\n")
same("連結 数の List と文字 2 つ", "f : xs c d ?\n\txs~ c d\nf [1 2] \\c \\d\n")
same("連結 数と文字", "f : xs c ?\n\txs~ 1 c\nf [\\a \\b] \\c\n")
same("連結 文字と数", "f : xs c ?\n\txs~ c 1\nf [\\a \\b] \\c\n")
same("連結 文字の List と String の撒き", "f : xs s ?\n\txs~ s~\nf [\\a \\b] `cd`\n")
same("連結 String を要素に", "f : xs s ?\n\txs~ s\nf [\\a \\b] `cd`\n")

# --- 外の String(自由変数)・String の字面を、整数だけの引数の関数が読む ---
same("自由変数 添字", "k : `abc`\nf : i ?\n\tk ' i\nseq2 (println (f 0)) (println (f 2))\n")
same("自由変数 範囲外", "k : `abc`\nf : i ?\n\tk ' i\nf 5\n")
same("自由変数 長さ", "k : `abc`\nf : i ?\n\t||k|| + i\nf 5\n")
same("自由変数 残り", "k : `abc`\nf : i ?\n\tk ' 1~\nf 5\n")
same("自由変数 文字との比べ", "k : `abc`\nf : i ?\n\t(k ' i) = \\b : 1\n\t0\nf 1\n")
same("自由変数 算術", "k : `abc`\nf : i ?\n\t(k ' i) + 1\nf 1\n")
same("自由変数 整数の答え", "k : `abc`\nf : i ?\n\t((k ' i) - \\a) * 2\nf 2\n")
same("自由変数 そのまま返す", "k : `abc`\nf : i ?\n\tk\nf 1\n")
same("自由変数 輪", "k : `abcabcabc`\ncnt : i n ?\n\ti = ||k|| : n\n\t(k ' i) = \\a : cnt (i + 1) (n + 1)\n\tcnt (i + 1) n\ncnt 0 0\n")
same("自由変数 String と String の比べ", "k : `abc`\nf : i ?\n\tk = `abc` : 1\n\t0\nf 1\n")
same("自由変数 String 2 つ", "k : `abc`\nj : `abd`\nf : i ?\n\tk < j : i\n\t0\nf 1\n")
same("自由変数 空の String", "k : ``\nf : i ?\n\t||k||\nf 1\n")
same("自由変数 List と String", "k : `abc`\nl : [1 2 3]\nf : i ?\n\t(l ' i) + (k ' i)\nf 1\n")
same("字面 String", "f : i ?\n\t`abc` ' i\nf 1\n")
same("字面 String の比べ", "f : i ?\n\t`abc` = `abc` : i\n\t0\nf 1\n")
same("字面 String の長さ", "f : i ?\n\t||`abcd`|| + i\nf 1\n")
same("自由変数 関数の中の関数", "k : `abc`\ng : i ?\n\tk ' i\nf : i ?\n\t(g i) = \\c : 1\n\t0\nf 2\n")
same("自由変数 小数との算術", "k : `abc`\nf : x ?\n\t(k ' 0) + x\nf 1.5\n")
same("自由変数 書き込み", "k : `abc`\nf : i ?\n\t0x4000 # (k ' i)\nf 1\n")
t0 = time.time()
b3 = "k : `" + "abcabcabcabcabcabcabcabcabcabc" + "`\ncnt : i n ?\n\ti = ||k|| : n\n\t(k ' i) = \\a : cnt (i + 1) (n + 1)\n\tcnt (i + 1) n\nrep : r ?\n\tr = 0 : 0\n\t(cnt 0 0) + (rep (r - 1))\nrep 5000\n"
same("自由変数の速さの例の答え", b3)
flush()
ra, ta = run(b3, True); rb, tb = run(b3, False)
print(f"      外の String を読む輪 5000 回: 速い道 {ta:.2f}s / 普通の道 {tb:.2f}s")
# --- String が初期値の acc(Char の List に直して足す) ---
for acc0 in ("`zy`", "`z`", "[1 2]"):
    for ret in ("acc", "||acc||", "acc ' 0", "acc ' 1", "acc ' 1~", "(acc ' 0) + 1"):
        for add in ("(s ' i)", "(s ' i) 7", "7 (s ' i)", "1.5", "(i + 1)", "(s ' i) (s ' i)", "[7 8]~", "[7 8]~ (s ' i)", "(s ' i) [7 8]~", "s~", "(s ' 1~)", "\\q", "\\q \\r", "acc~", "acc ' 0", "(acc ' 0)", "acc"):
            same(f"String acc {acc0} {ret} / acc~ {add}", f"m : s acc i ?\n\ti = ||s|| : {ret}\n\tm s (acc~ {add}) (i + 1)\nm `abc` {acc0} 0\n")
        same(f"String acc {acc0} {ret} / 0 回", f"m : s acc i ?\n\ti = ||s|| : {ret}\n\tm s (acc~ (s ' i)) (i + 1)\nm `` {acc0} 0\n")
for r in ("acc", "||acc||"):
    same(f"String acc 単独の関数 {r}", f"m : acc i ?\n\ti = 3 : {r}\n\tm (acc~ (i + 1)) (i + 1)\nm `zy` 0\n")
    same(f"String acc 単独 0 回 {r}", f"m : acc i ?\n\ti = 0 : {r}\n\tm (acc~ (i + 1)) (i + 1)\nm `zy` 0\n")
    same(f"String acc 途中で別の値 {r}", f"m : acc i ?\n\ti = 3 : {r}\n\tm `ab` (i + 1)\nm `zy` 0\n")
    same(f"String acc 呼び出し側から {r}", f"m : acc i ?\n\ti = 3 : {r}\n\tm (acc~ (i + 1)) (i + 1)\nf : x ?\n\tm x 0\nf `zy`\n")
    same(f"String acc 別の関数に渡す {r}", f"g : a ?\n\t||a||\nm : acc i ?\n\ti = 3 : {r}\n\t(g acc) = 9 : 5\n\tm (acc~ (i + 1)) (i + 1)\nm `zy` 0\n")
    same(f"String acc 比べる {r}", f"m : acc i ?\n\tacc = `zy` : 5\n\ti = 3 : {r}\n\tm (acc~ (i + 1)) (i + 1)\nm `zy` 0\n")
    same(f"String acc を二重に使う {r}", f"m : acc i ?\n\ti = 3 : {r}\n\tm (acc~ acc~) (i + 1)\nm `zy` 0\n")
    same(f"String acc 2つ {r}", f"m : a b i ?\n\ti = 3 : {r.replace('acc','a')}\n\tm (a~ (i + 1)) (b~ 5) (i + 1)\nm `zy` `xw` 0\n")
# --- 負のシフト量(仕様は未決。落とさず __ にする) ---
for op in ("<<", ">>"):
    for b in ("(0 - 1)", "(0 - 70)", "0", "3"):
        same(f"シフト {op} {b} (字面)", f"1 {op} {b}\n")
        same(f"シフト {op} {b} (関数)", f"f : a k ?\n\ta {op} k\nf 8 {b}\n")
        same(f"シフト {op} {b} (行の条件)", f"f : a k ?\n\t(a {op} k) = 4 : 1\n\t0\nf 8 {b}\n")
        same(f"シフト {op} {b} (輪)", f"g : a k n ?\n\tn = 0 : a\n\tg (a {op} k) k (n - 1)\ng 8 {b} 3\n")
# --- 乱数 ---
rng = random.Random(int(next((a.split("=")[1] for a in sys.argv if a.startswith("--seed=")), "5")))
NR = int(next((a.split("=")[1] for a in sys.argv if a.startswith("--n=")), "60"))
VALS = {"xs": ["[1 2 3]", "[\\a \\b \\c]", "[1.5 2]", "[1 \\a]~", "[\\a 1.5]~"], "ys": ["[7 8]", "[\\x \\y]", "[0.5 4]", "[\\p 2]~"],
        "c": [r"\q", r"\r", "5", "2.5"], "d": [r"\s", "7", "0.5"]}
ITEMS = ["xs~", "ys~", "c", "d", "1", "2.5", "(c + 1)", "(n + 1)", "(xs ' 0)", "(ys ' 1)", "\\z"]
for t in range(NR):
    k = rng.randint(1, 4)
    items = [rng.choice(ITEMS) for _ in range(k)]
    if not any(x.endswith("~") for x in items): items.append(rng.choice(["xs~", "ys~"]))
    a = {n: rng.choice(v) for n, v in VALS.items()}
    body = " ".join(items)
    same(f"乱数連結 {t}: {body} | {a}", f"f : xs ys c d n ?\n\t{body}\nf {a['xs']} {a['ys']} ({a['c']}) ({a['d']}) 3\n")
    same(f"乱数 acc~ {t}: {body} | {a}", f"m : k acc xs ys c d n ?\n\tk = 0 : acc\n\tm (k - 1) (acc~ {body}) xs ys c d (n + 1)\nm 3 [\\a \\b] {a['xs']} {a['ys']} ({a['c']}) ({a['d']}) 0\n")
# 乱数の String の関数
OPS = ["s", "(s ' 1~)", "(s ' i)", "||s||", "i", "(i + 1)", "(s ' 0)", "\\a", "`ab`", "(s ' (i + 1))", "(s ' i~)", "n"]
CMP = ["=", "!=", "<", "<=", ">", ">="]
for t in range(NR):
    s = rng.choice(S + ["`aab`", "`abab`"]); i = rng.randint(0, 3)
    c1 = f"{rng.choice(OPS)} {rng.choice(CMP)} {rng.choice(OPS)}"
    c2 = f"{rng.choice(OPS)} {rng.choice(CMP)} {rng.choice(OPS)}"
    r1 = rng.choice(["s", "(s ' 1~)", "(s ' 0)", "i", "n", "(n + 1)", "((s ' 0) + 1)"])
    r2 = rng.choice(["s", "(s ' 1~)", "(s ' 0)", "i", "n", "(n + 1)", "(f (s ' 1~) (i + 1) (n + 1))", "(f s (i + 1) (n + 1))"])
    r3 = rng.choice(["0", "n", "(f (s ' 1~) i (n + 1))", "s", "||s||"])
    src = f"f : s i n ?\n\t{c1} : {r1}\n\t{c2} : {r2}\n\t{r3}\nf {s} {i} 0\n"
    same(f"乱数 String {t}: {src.splitlines()[1:4]} {s} {i}", src)

for t in range(NR):
    k_ = rng.choice(["`abc`", "`abcabca`", "`aab`", "`zz`"]); i = rng.randint(0, 3)
    OP2 = ["k", "(k ' 1~)", "(k ' i)", "||k||", "i", "(i + 1)", "(k ' 0)", "\\a", "`ab`", "n"]
    c1 = f"{rng.choice(OP2)} {rng.choice(CMP)} {rng.choice(OP2)}"
    r1 = rng.choice(["k", "(k ' 1~)", "(k ' 0)", "i", "n", "(n + 1)", "((k ' 0) + 1)"])
    r2 = rng.choice(["0", "n", "(f i (n + 1))", "k", "||k||", "(f (i + 1) (n + 1))"])
    src = f"k : {k_}\nf : i n ?\n\t{c1} : {r1}\n\t{r2}\nf {i} 0\n"
    same(f"乱数 自由変数 {t}: {src.splitlines()[2:4]} {k_} {i}", src)
# --- String の acc に項を 2 つ以上足す `acc~ c1 c2` ---
for init in ["`x`", "`xy`", "`あ`"]:
    for terms in [r"\a \b", r"\a `bc`", r"`ab` `cd`", r"`ab` \z", r"\a \b \c"]:
        for n in (0, 1, 2, 5):
            same(f"acc 複数 {init} {terms} n={n}", f"rep : n acc ?\n\tn = 0 : acc\n\trep (n - 1) (acc~ {terms})\nprintln (rep {n} {init})\nprintln_int ||rep {n} {init}||\n")
    for n in (1, 3):
        same(f"acc 数が混ざる {init} n={n}", f"rep : n acc ?\n\tn = 0 : acc\n\trep (n - 1) (acc~ \\a 1)\n||rep {n} {init}||\n")
        same(f"acc 添字 {init} n={n}", f"rep : n acc ?\n\tn = 0 : acc ' 1\n\trep (n - 1) (acc~ \\a \\b)\nrep {n} {init}\n")
        same(f"acc 名前の項 {init} n={n}", f"rep : n acc c ?\n\tn = 0 : acc\n\trep (n - 1) (acc~ c c) c\nprintln (rep {n} {init} \\q)\n")
flush()
# --- 速さ ---
b1 = "cnt : s i n ?\n\ti = ||s|| : n\n\t(s ' i) = \\a : cnt s (i + 1) (n + 1)\n\tcnt s (i + 1) n\nrep : k s ?\n\tk = 0 : 0\n\t(cnt s 0 0) + (rep (k - 1) s)\nrep 3000 `abcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabc`\n"
ra, ta = run(b1, True); rb, tb = run(b1, False)
check("速さの例の答え", ra, rb); print(f"      文字を数える(String の添字)速い道 {ta:.2f}s / 普通の道 {tb:.2f}s")
b2 = "m : s acc i ?\n\ti = ||s|| : ||acc||\n\tm s (acc~ (s ' i)) (i + 1)\nm `" + "abcdefghij" * 3000 + "` [1 2] 0\n"
ra, ta = run(b2, True); rb, tb = run(b2, False)
check("速さの例の答え(acc~ で String の文字を足す)", ra, rb); print(f"      acc~ で String の文字 3万個を List に足す: 速い道 {ta:.2f}s / 普通の道 {tb:.2f}s")
print(f"\n{N[0]} 件中 {bad} 件の食い違い"); print("全部 ok" if not bad else "NG あり"); sys.exit(1 if bad else 0)
