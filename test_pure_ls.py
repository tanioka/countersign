#!/usr/bin/env python3
"""Stringの List(字句のならび)を引数に取る形(bench/par_big.sn の定義部=構文解析器)が、速い道あり/無しで
同じ出力になることを確かめる。(約 9 分。`--quick` なら約 1 分、`-j` で同時数、`-k 名前` で絞る)`(表 ' (ts ' k)~) ' 欄` の構造体引き、`ts ' k`、`||ts||`、`ts ' k~`、`==` の条件。python test_pure_ls.py"""
import os, random, sys, subprocess, itertools, tempfile, shutil, time, argparse, collections
from concurrent.futures import ThreadPoolExecutor
HERE = os.path.dirname(os.path.abspath(__file__))
ap = argparse.ArgumentParser(description=__doc__.split("。python")[0])
ap.add_argument("--quick", action="store_true", help="10 件に 1 件だけ走らせる(約 1 分)")
ap.add_argument("-j", type=int, default=os.cpu_count() or 2, help="同時に走らせる数(既定: CPU の数)")
ap.add_argument("-k", default="", help="名前にこの文字を含む件だけ走らせる(例: -k tier_at)")
ap.add_argument("--timeout", type=int, default=180, help="1 回の実行の秒数の上限")
args = ap.parse_args()
TMP = tempfile.mkdtemp(prefix="test_pure_ls_"); _c = itertools.count()
shutil.copy(os.path.join(HERE, "bench", "operator_table.sn"), TMP)      # 定義部が `operator_table.sn`@~ で読む表。一時ファイルと同じ所に置く
def run(src, pure):
    """速い道あり(pure)/無しで 1 つのプログラムを走らせる。一時ファイルは TMP の中だけに作り、最後に TMP ごと消す"""
    p = os.path.join(TMP, "c%d.sn" % next(_c))
    open(p, "w", encoding="utf-8").write(src)
    env = dict(os.environ); env["SIGN_NO_PURE"] = "0" if pure else "1"
    try: r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p], capture_output=True, text=True, timeout=args.timeout, env=env, cwd=HERE)
    except subprocess.TimeoutExpired: return ("timeout",)
    finally: os.remove(p)
    return (r.returncode, r.stdout, r.stderr.replace(p, "T"))
big = open(os.path.join(HERE, "bench", "par_big.sn"), encoding="utf-8").read()
lines = big.split("\n")
cut = max(i for i, l in enumerate(lines) if l.startswith("expr ["))
defs = "\n".join(lines[:cut]) + "\n"
ops = ["+", "-", "*", "/", "=", "<", "&", "|", ":", "?", "'", "@", ";", ",", "~", "=="]
atoms = ["1", "2", "x", "yy", "foo", "0", "`s`"]
rnd = random.Random(11)
def lit(ts): return "[" + " , ".join("`" + t.strip("`") + "`" for t in ts) + "]"
cases = []
fixed = [["1", "+", "2", "*", "3"], ["1"], ["x", "y"], ["1", "?", "2"], ["a", "'", "b", "@", "c"], ["~", "x"], ["1", "+"], ["+", "1"], ["a", "b", "c"], ["1", "==", "2"]]
toks = list(fixed)
for _ in range(120):
    n = rnd.randint(1, 9); toks.append([rnd.choice(atoms if i % 2 == 0 else ops) if rnd.random() < .85 else rnd.choice(atoms + ops) for i in range(n)])
for i, t in enumerate(toks):
    L = lit(t); n = len(t)
    cases.append((f"expr#{i} {t}", defs + f"expr {L}\n"))
    for k in sorted({0, n // 2, n - 1, n, n + 1}):
        cases.append((f"tier_at#{i}/{k}", defs + f"println_int (tier_at {L} {k})\n"))
        cases.append((f"end_of#{i}/{k}", defs + f"println_int (end_of {L} {k} 2)\n"))
    cases.append((f"has_tok#{i}", defs + f"println_int (has_tok `+` {L})\n"))
    cases.append((f"mixed#{i}", defs + f"println_int (mixed_get {L})\n"))
    cases.append((f"stream#{i}", defs + f"println_int (bare_stream {L})\n"))
    cases.append((f"op_word#{i}", defs + f"println_int (op_word {L} ' 0)\n"))
# 正しい式(演算子と項が交互)で AST の出力(out 系)を確かめる
good_ops = ["+", "-", "*", "/", "=", "<", "&", "|", ":", "'", "@", ";", "=="]
for i in range(150):
    m = rnd.randint(0, 5); t = [rnd.choice(["1", "2", "x", "yy", "0"])]
    for _ in range(m): t += [rnd.choice(good_ops), rnd.choice(["1", "2", "x", "yy", "0"])]
    cases.append((f"ast#{i} {t}", defs + f"expr {lit(t)}\n"))
    cases.append((f"out#{i} {t}", defs + f"out {lit(t)} 0 {len(t)} 2\n"))
# 相互再帰で Stringの List の残りを位置で渡す(`g t (ts \' k~)`)
for i in range(40):
    t = [rnd.choice(["a", "b", "c", "+"]) for _ in range(rnd.randint(1, 9))]
    for key in ("a", "b", "c", "z"):
        for kk in (1, 2):
            cases.append((f"mutual#{i}/{key}/{kk} {t}", f"f : t [~ts] ?\n\tts ' 0 == t : 1\n\tg t (ts ' {kk}~)\ng : t [~ts] ?\n\tts ' 0 == t : 2\n\tf t (ts ' 1~)\nprintln_int (f `{key}` {lit(t)})\n"))
        cases.append((f"mutual_rest#{i}/{key} {t}", f"f : t [a ~ts] ?\n\ta == t : 1\n\tg t ts\ng : t [~ts] ?\n\tts ' 0 == t : 2\n\t!ts : 0\n\tf t ts\nprintln_int (f `{key}` {lit(t)})\n"))
cases.append(("par_big", big))
if args.k: cases = [c for c in cases if args.k in c[0]]
if args.quick: cases = cases[::10]
def one(c): return c[0], run(c[1], True), run(c[1], False)
bad = n = slow_to = both_err = 0; kinds = collections.Counter(); t0 = time.time()
try:
    with ThreadPoolExecutor(args.j) as ex:
        for name, a, b in ex.map(one, cases):
            n += 1; kind = name.split("#")[0].split(" ")[0]; kinds[kind] += 1
            if a == ("timeout",) or b == ("timeout",):
                slow_to += 1; print("TIMEOUT", name, "(速い道:", "timeout" if a == ("timeout",) else "ok", "/ 普通の道:", "timeout" if b == ("timeout",) else "ok", ")")
            elif a != b: bad += 1; print("NG", name, "\n  fast:", str(a)[:300], "\n  slow:", str(b)[:300])
            elif a[0] != 0: both_err += 1
            if n % 500 == 0: print(f"  … {n}/{len(cases)} ({time.time() - t0:.0f} 秒)", flush=True)
finally:
    shutil.rmtree(TMP, ignore_errors=True)
print("種類ごとの件数:", ", ".join(f"{k} {v}" for k, v in sorted(kinds.items())))
print(f"{n} 件中 {bad} 件の不一致、{slow_to} 件の時間切れ(両方とも終了コード 0 でなかった件: {both_err})  {time.time() - t0:.0f} 秒")
sys.exit(1 if bad or slow_to else 0)
