"""run_on_pi.py — 命令の並べ替えの効果を測る(既定 5 回、中央値)。プログラムごとに _o(最適化なし)・_n(並べ替えだけ無し)・_s(全部あり)を、
「全部の変種を 1 周 → 次の周」と交互に回す(温度のぶれが変種に偏らない)。答えは毎回 expected.json と照合する。
記録: 機種・CPU の周波数・温度(前後)。report.txt に書く。使い方: python3 run_on_pi.py [回数]   (他の処理を止めて、できれば冷えた状態で)
見るところ: 「_a」があれば「s/a」が 1 より大きいとき A53 向けの並べ替えが既定より速い。「_n / _s」が 1 より大きければ、並べ替えが速くした。1 前後なら、A72 は並べ替えなしでも同じ(out-of-order で隠れる)。"""
import json, os, statistics, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
N = int(sys.argv[1]) if len(sys.argv) > 1 else 5
exp = json.load(open(os.path.join(HERE, "expected.json")))
progs = sorted({b.rsplit("_", 1)[0] for b in exp}); sufs = [x for x in ["o", "n", "s", "a"] if all(os.path.exists(os.path.join(HERE, "bin", p + "_" + x)) for p in progs)]
def rd(p):
    try: return open(p).read().strip()
    except Exception: return "?"
def temp(): t = rd("/sys/class/thermal/thermal_zone0/temp"); return "%.1f℃" % (int(t) / 1000) if t.isdigit() else "?"
def freq(): f = rd("/sys/devices/system/cpu/cpu0/cpufreq/scaling_cur_freq"); return "%d MHz" % (int(f) // 1000) if f.isdigit() else "?"
L = ["# 命令の並べ替えの効果(%d 回の中央値)" % N, "機種: " + rd("/proc/device-tree/model").strip("\0"), "governor: " + rd("/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor"),
     "開始: 温度 %s / 周波数 %s / 負荷 %s" % (temp(), freq(), rd("/proc/loadavg"))]
t = {(p, s): [] for p in progs for s in sufs}; bad = 0
for rnd in range(N):
    for p in progs:
        for s in sufs:
            b = p + "_" + s; t0 = time.time()
            r = subprocess.run([os.path.join(HERE, "bin", b)], capture_output=True, timeout=600); dt = (time.time() - t0) * 1000
            if r.stdout.decode(errors="replace") != exp[b]["stdout"] or r.returncode != 0:
                bad += 1; L.append("食い違い %s 周%d: %r rc=%d" % (b, rnd, r.stdout.decode(errors="replace")[:60], r.returncode))
            t[(p, s)].append(dt)
    L.append("周 %d 終了: 温度 %s / 周波数 %s" % (rnd + 1, temp(), freq()))
L += ["", "## 中央値 ms(最小〜最大)。o = 最適化なし / n = 並べ替えだけ無し / s = 全部あり(既定の並べ替え) / a = A53 向けの並べ替え", ""]
for p in progs:
    m = {s: statistics.median(t[(p, s)]) for s in sufs}
    ex = (" / a %d (%d〜%d)  →  A53 向けの並べ替え s/a = x%.3f" % (m["a"], min(t[(p, "a")]), max(t[(p, "a")]), m["s"] / m["a"] if m["a"] else 0)) if "a" in m else ""
    L.append("%s: o %d (%d〜%d) / n %d (%d〜%d) / s %d (%d〜%d)  →  並べ替えの効果 n/s = x%.3f  並べ替え以外 o/n = x%.3f" % (
        p, m["o"], min(t[(p, "o")]), max(t[(p, "o")]), m["n"], min(t[(p, "n")]), max(t[(p, "n")]), m["s"], min(t[(p, "s")]), max(t[(p, "s")]),
        m["n"] / m["s"] if m["s"] else 0, m["o"] / m["n"] if m["n"] else 0) + ex)
L.append("\n答えの食い違い %d 件" % bad)
open(os.path.join(HERE, "report.txt"), "w").write("\n".join(L) + "\n"); print("\n".join(L))
