#!/usr/bin/env python3
"""sign_plan.py(並列実行のプラン)の試験。小さな Sign の式を書いて、プランの判定を確かめる。python test_plan.py"""
import glob, json, os, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
sys.setrecursionlimit(20000)
import sign_plan as SP

bad = 0
def check(name, got, want):
    global bad
    ok = got == want; bad += not ok
    print(("ok  " if ok else "NG  ") + name + ("" if ok else f"\n    得た: {got!r}\n    期待: {want!r}"))

TMP = tempfile.mkdtemp()
def plan(src, **kw):
    p = os.path.join(TMP, "t.sn"); open(p, "w", encoding="utf-8").write(src)
    return SP.Planner(SP.load(p), **kw).analyse()
HEAD = "seq2 : a b ? b\nseq3 : a b c ? c\nslow : n ?\n\tn < 1 : 0\n\tslow (n - 1)\nA : 0x500\nUART : 0x9000000\n"
def opps(P, where=None): return [o for o in P.opps if where is None or o["where"] == where]
def blocks(P, where=None): return [b for b in P.blocks if where is None or b[0] == where]

# --- 副作用の分類 ---
P = plan(HEAD + "pure : x ? (x * 2) + 1\nrd : z ? @A\nwr : z ? A # 5\nuart : z ? UART # 65\nwhoknows : p ? p # 1\nrd2 : z ? rd 0\nwr2 : z ? seq2 (wr 0) 0\nmut1 : n ? mut2 n\nmut2 : n ? seq2 (A # 1) (mut1 n)\n0")
kinds = {f: P.summ[f].kind() for f in ("pure", "rd", "wr", "uart", "whoknows", "rd2", "wr2", "mut1", "mut2")}
check("副作用の分類(純粋・読む・書く)と、呼び出しを通した伝わり方、相互再帰", kinds, dict(pure="純粋", rd="読む", wr="書く", uart="書く", whoknows="書く", rd2="読む", wr2="書く", mut1="書く", mut2="書く"))
check("書く番地: 定数(名前つき)・デバイス・計算で決まる(*)", ([sorted(P.summ["wr"].w), sorted(P.summ["uart"].w, key=str), sorted(P.summ["whoknows"].w)]), [[0x500], [("dev", 0x9000000 >> 20)], ["*"]])
# --- 番地による判定 ---
P = plan(HEAD + "go : z ? seq3 ((A # (slow 50)) | 0) (((A + 4) # (slow 60)) | 0) 0\ngo 0")
check("別の定数番地への書き込み(A と A+4)は同時にできる", (len(opps(P, "go")), blocks(P, "go")), (1, []))
P = plan(HEAD + "go : z ? seq3 ((A # (slow 50)) | 0) ((A # (slow 60)) | 0) 0\ngo 0")
check("同じ番地への書き込みは順番(理由に番地)", (opps(P, "go"), [b[3] for b in blocks(P, "go")]), ([], ["どちらも番地 0x500 を使う"]))
P = plan(HEAD + "go : p ? seq3 ((p # (slow 50)) | 0) (((p + 4) # (slow 60)) | 0) 0\ngo 0")
check("引数で決まる番地は安全側(順番)", ([o for o in opps(P, "go")], [b[3] for b in blocks(P, "go")]), ([], ["どちらも番地が計算で決まる(*)ので、重なるかもしれない"]))
P = plan(HEAD + "go : z ? seq3 ((UART # 65) | 0) ((UART # 66) | 0) 0\ngo 0")
check("デバイスへの書き込みは順番(入出力の順)", [b[3] for b in blocks(P, "go")], ["どちらも同じデバイスを使う(入出力は順番に意味がある)"])
P = plan(HEAD + "go : z ? seq2 ((A # (slow 50)) | 0) (@A)\ngo 0")
check("書いてから同じ番地を読むのは順番", [b[3] for b in blocks(P, "go")], ["前が書いて後が読む番地 0x500 を使う"])
P = plan(HEAD + "go : z ? seq2 (@A) ((A # (slow 50)) | 0)\ngo 0")
check("読んでから書くのも順番", [b[3] for b in blocks(P, "go")], ["前が読んで後が書く番地 0x500 を使う"])
P = plan(HEAD + "go : z ? seq2 ((slow 50) + (@A)) ((slow 60) + (@(A + 4)))\ngo 0")
check("読みどうしは同時にできる", len(opps(P, "go")), 1)
P = plan(HEAD + "go : z ? seq2 ((A # 1) | 0) ((slow 50) + (slow 60))\ngo 0")
check("書き込みと、メモリを触らない純粋な計算は同時にできる", len(opps(P, "go")), 1)
# --- 波(順番を保つ) ---
P = plan(HEAD + "go : z ? seq3 ((A # (slow 50)) | 0) ((A # (slow 60)) | 0) (((A + 8) # (slow 70)) | 0)\ngo 0")
call = P.fn_plans["go"]
check("3 つのうち前の 2 つが衝突: 波は [1 つ][2 つ]の順(最後は前と別の番地で、同じ波に入る)", [len([x for x in w if not x.trivial()]) for w in call.waves[:2]], [1, 2])
# --- 分割統治 ---
P = plan("fib : n ?\n\tn < 2 : n\n\t(fib (n - 1)) + (fib (n - 2))\nfib 10")
check("fib: 分割統治の再帰を見つける", [(o["where"], o["kind"]) for o in opps(P, "fib")], [("fib", "分割統治の再帰")])
P = plan("sum : n acc ?\n\tn < 1 : acc\n\tsum (n - 1) (acc + n)\nsum 100 0")
check("末尾再帰のループ(自己呼び出し 1 つ)は分割統治ではない", [o for o in opps(P, "sum") if o["kind"] == "分割統治の再帰"], [])
P = plan("f : n ?\n\tn < 2 : n\n\t(f (n - 1)) + (f (n - 2))\nf 5", min_work=100000)
check("--min-work が大きければ、軽い組は対象にしない", P.opps, [])
a = plan("f : n ?\n\tn < 2 : n\n\t(f (n - 1)) + (f (n - 2))\nf 5", rec_w=10).fn_plans["f"].work
b = plan("f : n ?\n\tn < 2 : n\n\t(f (n - 1)) + (f (n - 2))\nf 5", rec_w=300).fn_plans["f"].work
check("--rec-weight で再帰の重さの仮定が変わる", a < b, True)
# --- 行(cases)・短絡 ---
P = plan(HEAD + "hv : n ? ((n * n) + (n * n * n)) + ((n * 7) - (n * 3))\npick : n ?\n\tn < 1 : (hv 100) + (hv 5)\n\tn < 2 : (hv 200) + (hv 7)\n\t(hv 300) + (hv 9)\npick 1")
check("条件の行は順番(波が 1 つずつ)、重い値が 2 つ以上あれば投機として挙げる", ([o["kind"] for o in opps(P, "pick") if "投機" in o["kind"]], [len(w) for w in P.fn_plans["pick"].waves]), (["投機(行の値の先読み)"], [1, 1]))
P = plan(HEAD + "g : z ? ((A # 1) | (A # 2))\ng 0")
check("`|` の右が書き込みなら順番(短絡の可能性)", [len(w) for w in P.fn_plans["g"].waves], [1, 1])
P = plan(HEAD + "rec : n ?\n\tn < 1 : 0\n\tn < 2 : rec (n - 1)\n\trec (n - 2)\nrec 5")
check("再帰を含む行は、投機の先読みの対象にしない(止まらなくなるかもしれない)", [o for o in P.opps if "投機" in o["kind"]], [])
# --- 知らない関数・引数の関数 ---
P = plan(HEAD + "ap : f x ? f x\nuse : z ? seq2 ((ap slow 3) | 0) ((A # 1) | 0)\nuse 0")
check("引数で渡された関数を呼ぶ関数は、副作用ありとして順番を守る", (P.summ["ap"].kind(), [b[3] for b in blocks(P, "use")] != []), ("書く", True))
# --- 取り込み・サンプル ---
P = SP.Planner(SP.load(os.path.join(HERE, "std_demo.sn"))).analyse()
check("取り込み(std.sn)の関数も表に入る", ("arr_sort" in P.defs, "str_put" in P.defs, P.summ["arr_get"].kind()), (True, True, "読む"))
check("std.sn の副作用: arr_set は書く(番地が計算で決まる)、abs は純粋", (P.summ["arr_set"].kind(), "*" in P.summ["arr_set"].w, P.summ["abs"].kind()), ("書く", True, "純粋"))
# --- 出力形式 ---
src = os.path.join(HERE, "std_demo.sn")
j = json.loads(subprocess.run([sys.executable, os.path.join(HERE, "sign_plan.py"), src, "--json"], capture_output=True, timeout=120).stdout.decode())
check("--json: functions・opportunities・blocked・plan がある", sorted(j), ["blocked", "functions", "opportunities", "plan"])
d = subprocess.run([sys.executable, os.path.join(HERE, "sign_plan.py"), src, "--dot"], capture_output=True, timeout=120).stdout.decode()
check("--dot: digraph になる", (d.startswith("digraph plan {"), d.rstrip().endswith("}")), (True, True))
t = subprocess.run([sys.executable, os.path.join(HERE, "sign_plan.py"), src], capture_output=True, timeout=120).stdout.decode()
check("本文: 4 つの節が出る", all(x in t for x in ("■ 1.", "■ 2.", "■ 3.", "■ 4.")), True)
r = subprocess.run([sys.executable, os.path.join(HERE, "sign_plan.py")], capture_output=True, timeout=30)
check("引数なしは使い方を出して 2 で終わる", r.returncode, 2)
# --- すべての見本で落ちない ---
fails = []
for f in sorted(glob.glob(os.path.join(HERE, "*.sn"))):
    try: SP.Planner(SP.load(f)).analyse()
    except Exception as e: fails.append((os.path.basename(f), type(e).__name__, str(e)[:80]))
check("ディレクトリの *.sn をすべて解析できる(落ちない)", fails, [])
print("\n" + ("全部通った" if not bad else f"{bad} 件 食い違い")); sys.exit(1 if bad else 0)
