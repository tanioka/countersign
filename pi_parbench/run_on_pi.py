"""run_on_pi.py — --par の時間を複数回測る(既定 5 回、中央値)。
直列(_s)・--par=2・3・4 を、プログラムごとに「全部の変種を 1 周 → 次の周」と交互に回す(温度や他の処理のぶれが、特定の変種に偏らない)。
答えは毎回 expected.json と照合する。記録: 機種・CPU の周波数・温度(前後)・負荷。report.txt に書く。
使い方: python3 run_on_pi.py [回数]   (他の処理を止めて、できれば冷えた状態で)"""
import json, os, statistics, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
N = int(sys.argv[1]) if len(sys.argv) > 1 else 5
exp = json.load(open(os.path.join(HERE, "expected.json")))
progs = sorted({b.rsplit("_", 1)[0] for b in exp}); sufs = ["s", "p2", "p3", "p4"]
def rd(p):
    try: return open(p).read().strip()
    except Exception: return "?"
def temp(): t = rd("/sys/class/thermal/thermal_zone0/temp"); return "%.1f℃" % (int(t) / 1000) if t.isdigit() else "?"
def freq(): f = rd("/sys/devices/system/cpu/cpu0/cpufreq/scaling_cur_freq"); return "%d MHz" % (int(f) // 1000) if f.isdigit() else "?"
L = ["# --par の時間(%d 回の中央値)" % N, "機種: " + rd("/proc/device-tree/model").strip("\0"), "nproc: %d" % (os.cpu_count() or 0), "governor: " + rd("/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor"),
     "開始: 温度 %s / 周波数 %s / 負荷 %s" % (temp(), freq(), rd("/proc/loadavg"))]
t = {(p, s): [] for p in progs for s in sufs}; bad = 0
for rnd in range(N):
    for p in progs:
        for s in sufs:
            b = p + "_" + s; t0 = time.time()
            r = subprocess.run([os.path.join(HERE, "bin", b)], capture_output=True, timeout=300); dt = (time.time() - t0) * 1000
            if r.stdout.decode(errors="replace") != exp[b]["stdout"] or r.returncode != 0: bad += 1; L.append("食い違い %s 周%d: %r rc=%d" % (b, rnd, r.stdout[:40], r.returncode))
            t[(p, s)].append(dt)
    L.append("周 %d 終了: 温度 %s / 周波数 %s" % (rnd + 1, temp(), freq()))
L.append(""); L.append("## 中央値 ms(最小〜最大)と、直列に対する比(中央値どうし)")
for p in progs:
    base = statistics.median(t[(p, "s")]); row = ["%s: 直列 %d (%d〜%d)" % (p, base, min(t[(p, "s")]), max(t[(p, "s")]))]
    for s in sufs[1:]:
        m = statistics.median(t[(p, s)]); row.append("%s %d (%d〜%d) x%.2f" % (s, m, min(t[(p, s)]), max(t[(p, s)]), base / m if m else 0))
    L.append(" / ".join(row))
L.append("\n答えの食い違い %d 件" % bad)
open(os.path.join(HERE, "report.txt"), "w").write("\n".join(L) + "\n"); print("\n".join(L))
