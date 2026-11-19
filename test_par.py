"""test_par.py — --par(sign_par.py。純粋な関数の並列実行)。直列と並列で出力が同じか、分けるべき所で分けて分けない所で分けないか。"""
import os, subprocess, sys, tempfile, time
HERE = os.path.dirname(os.path.abspath(__file__)); fails = 0
def run(src, *opts, probe=None, timeout=300):
    d = tempfile.mkdtemp(); p = os.path.join(d, "t.sn"); open(p, "w", encoding="utf-8").write(src)
    env = dict(os.environ)
    if probe is not None: env["SIGN_PAR_PROBE_MS"] = str(probe)
    t = time.time()
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p, *opts], capture_output=True, timeout=timeout, env=env, cwd=d, stdin=subprocess.DEVNULL)
    return r.stdout.decode("utf-8", "replace"), r.stderr.decode("utf-8", "replace"), r.returncode, time.time() - t
def check(name, got, want):
    global fails
    if got == want: print("ok ", name)
    else: fails += 1; print("NG ", name, "\n    want", repr(want), "\n    got ", repr(got))
def stat(err, key):
    for ln in err.splitlines():
        if ln.startswith("[par]   " + key + ":"): return int(ln.split(":")[1])
    return 0

CL = "clen : n s ?\n\tn = 1 : s\n\t(n % 2) = 0 : clen (n / 2) (s + 1)\n\tclen (3 * n + 1) (s + 1)\n"
TOT = CL + "tot : lo hi acc ?\n\tlo > hi : acc\n\ttot (lo + 1) hi (acc + (clen lo 0))\n"
DC = CL + "dc : lo hi ?\n\tlo = hi : clen lo 0\n\t(dc lo ((lo + hi) / 2)) + (dc (((lo + hi) / 2) + 1) hi)\n"
FIB = "fib : n ?\n\tn < 2 : n\n\t(fib (n - 1)) + (fib (n - 2))\n"
MEM = "rd : n ?\n\tn = 0 : @0x7000000\n\t(rd (n - 1)) + (rd (n - 1))\n"
CMB = TOT + "comb : a b ? a * 3 + b\n"
more = {
    "連なり(項 4 つの和)": TOT + "(tot 1 1500 0) + (tot 1501 3000 0) + (tot 3001 4500 0) + (tot 4501 6000 0)\n",
    "連なり(積)": TOT + "(tot 1 40 0) * (tot 41 80 0) * (tot 81 120 0)\n",
    "連なり(項に定数が混ざる = 分けない)": TOT + "(tot 1 1500 0) + (tot 1501 3000 0) + 5\n",
    "実引数の呼び出しどうし": CMB + "comb (tot 1 2500 0) (tot 2501 5000 0)\n",
    "実引数 3 つの呼び出し": TOT + "add3 : a b c ? a + b * c\nadd3 (tot 1 1500 0) (tot 1501 3000 0) (tot 3001 4500 0)\n",
    "呼び出し + 別の式(右が式)": TOT + "(tot 1 3000 0) + (3 * (tot 3001 6000 0))\n",
    "呼び出し + 別の式(左が式)": TOT + "(3 * (tot 1 3000 0)) + (tot 3001 6000 0)\n",
    "呼び出し - 別の式(左が式)": TOT + "((tot 1 3000 0) * 2) - (tot 3001 6000 0)\n",
    "割り算": TOT + "(tot 1 3000 0) / (tot 3001 3010 0)\n",
    "剰余": TOT + "(tot 1 3000 0) % (tot 3001 3010 0)\n",
    "ビット and": TOT + "(tot 1 3000 0) && (tot 3001 6000 0)\n",
    "0 で割る": TOT + "(tot 1 3000 0) / (tot 5 4 0)\n",
}
for name, src in more.items():
    base = run(src)
    for n in (2, 4, 8):
        for probe in (None, 0):
            o = run(src, "--par=%d" % n, probe=probe)
            check("%s: --par=%d probe=%s の出力が直列と同じ" % (name, n, probe), (o[0], o[2]), (base[0], base[2]))
o = run(more["連なり(項 4 つの和)"], "--par=4", "--par-stats", probe=0)
check("項 4 つの和は 3 つ以上に分ける(子 3 つ以上)", (stat(o[1], "3 つ以上に分けた") >= 1, stat(o[1], "仕事を出した") >= 3), (True, True))
o = run(more["連なり(項に定数が混ざる = 分けない)"], "--par=4", "--par-stats", probe=0)
check("定数が混ざる連なりは分けない", stat(o[1], "3 つ以上に分けた"), 0)
o = run(more["実引数の呼び出しどうし"], "--par=2", "--par-stats", probe=0)
check("実引数の呼び出しどうしを分ける", stat(o[1], "式を分けた") >= 1, True)
o2 = run(TOT + "(3 * (tot 1 3000 0)) + (tot 3001 6000 0)\n", "--par=2", "--par-stats", probe=0)
check("片方だけ呼び出し(左が式)でも呼び出しを分ける", stat(o2[1], "呼び出し + 別の式") >= 1, True)
o2 = run(TOT + "(tot 1 3000 0) + 5\n", "--par=2", "--par-stats", probe=0)
check("もう片方が呼び出しを含まない式なら分けない", stat(o2[1], "呼び出し + 別の式"), 0)
o = run(more["割り算"], "--par=2", "--par-stats", probe=0)
check("割り算の両辺も分ける", stat(o[1], "式を分けた") >= 1, True)
o = run(progs_dc := (DC + "dc 1 1200\n"), "--par=4", "--par-stats", probe=0)
check("N=4: 子にもコアを渡し、子が自分で分ける(子の子が出る)", (stat(o[1], "子にも分けるコアを渡した") >= 1, stat(o[1], "子を起動") >= 4), (True, True))
o = run(progs_dc, "--par=2", "--par-stats", probe=0)
check("N=2: 子にはコアを渡さない", stat(o[1], "子にも分けるコアを渡した"), 0)

progs = {
    "兄弟 2 本(範囲の和)": TOT + "(tot 1 3000 0) + (tot 3001 6000 0)\n",
    "差と積": TOT + "((tot 1 2000 0) * (tot 2001 2002 0)) - (tot 1 500 0) * 2\n",
    "分割統治(一段の呼び出しから開く)": DC + "dc 1 1200\n",
    "fib(軽い)": FIB + "fib 15\n",
    "和の後ろに別の式": TOT + "x : (tot 1 800 0) + (tot 801 1600 0)\nx + 1\n",
    "引数に式": TOT + "a : 7\n(tot (a - 6) (a * 100) 0) + (tot (a * 100 + 1) (a * 200) 0)\n",
    "メモリを読む関数(分けない)": "0x7000000 # 5\n" + MEM + "rd 3\n",
}
for name, src in progs.items():
    base = run(src)
    for n in (2, 3, 8):
        for probe in (None, 0):
            o = run(src, "--par=%d" % n, probe=probe)
            check("%s: --par=%d probe=%s の出力が直列と同じ" % (name, n, probe), (o[0], o[2]), (base[0], base[2]))
# 分けているか
o = run(progs["兄弟 2 本(範囲の和)"], "--par=2", "--par-stats", probe=0)
check("兄弟 2 本: 式を分けて子を 1 つ起動した", (stat(o[1], "式を分けた") >= 1, stat(o[1], "子を起動") >= 1), (True, True))
o = run(progs["分割統治(一段の呼び出しから開く)"], "--par=4", "--par-stats", probe=0)
check("分割統治 N=4: 3 段まで開き、子を 3 つ以上起動した", (stat(o[1], "式を分けた") >= 3, stat(o[1], "子を起動") >= 3, stat(o[1], "同時に走った最大") <= 3), (True, True, True))
o = run(progs["メモリを読む関数(分けない)"], "--par=4", "--par-stats", probe=0)
check("メモリを読む関数は分けない(子 0)", stat(o[1], "子を起動"), 0)
o = run(progs["fib(軽い)"], "--par=4", "--par-stats")
check("軽い式はプローブで済む(式を分けない)", stat(o[1], "式を分けた"), 0)
# 待ち行列(N=2 で段が深い)でも子は 1 つまで
o = run(progs["分割統治(一段の呼び出しから開く)"], "--par=2", "--par-stats", probe=0)
check("N=2: 同時に走る子は 1 つまで", stat(o[1], "同時に走った最大"), 1)
# 速さ(CPU が 2 つ以上あるときだけ)
if (os.cpu_count() or 1) >= 2:
    big = TOT + "(tot 1 30000 0) + (tot 30001 60000 0)\n"
    a = run(big); b = run(big, "--par=2")
    check("速さ: 2 本の等しい仕事が 1.4 倍以上速い(直列 %.2f 秒 → 並列 %.2f 秒)" % (a[3], b[3]), (a[0] == b[0], a[3] / b[3] >= 1.4), (True, True))
# 異常な指定でも落ちない
o = run("1 + 2\n", "--par=x"); check("--par=x は注意を出して動く", (o[0].strip(), o[2], "--par=N" in o[1]), ("3", 0, True))
o = run("1 + 2\n", "--par=1"); check("--par=1 は何もしない", (o[0].strip(), o[2], o[1]), ("3", 0, ""))
o = run("1 + 2\n", "--par=4", "--strict"); q = run("1 + 2\n", "--strict"); check("--strict とは使えず、注意を出して直列(--strict だけの時)と同じに動く", (o[0], o[2], "--strict" in o[1]), (q[0], 0, True))
# 子が残らない
o = run(progs["分割統治(一段の呼び出しから開く)"], "--par=4", probe=0)
check("終了コード 0", o[2], 0)
print("\n全部 ok" if not fails else "\n失敗 %d 件" % fails); sys.exit(1 if fails else 0)
