"""run_on_pi.py — Int の List の NEON 化の見積もり(手書きのカーネル): スカラー(溢れは adds + csel)と NEON(2 レーン、溢れは粘着ビット + スカラーでやり直し)の時間を比べる。
bench0: 溢れなしのデータ(100 万要素 × 200 回)を 5 回走らせた中央値。bench1: 溢れ・niche ちょうど・境の値を含むデータで、NEON 版(検出 → やり直し)の答えがスカラー版と同じか。
できた report.txt を返してください。"""
import os, statistics, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
N = int(sys.argv[1]) if len(sys.argv) > 1 else 5
EXP = {0: {"scalar_map": 1051322, "scalar_fold": 1373}, 1: {"scalar_map": 1109476, "scalar_fold": -9223372036854771995}}   # Python のモデルで出した指紋(参考。比べの本体は NEON = スカラー)
def run(m):
    r = subprocess.run([os.path.join(HERE, "bin", "bench%d" % m)], capture_output=True, timeout=600, text=True)
    d = {}
    for l in r.stdout.splitlines():
        p = l.split()
        if len(p) == 3: d[p[0]] = (int(p[1]), int(p[2]))
    return d, r.returncode
def rd(p):
    try: return open(p).read().strip()
    except Exception: return "?"
L = ["# Int の List の NEON 化の見積もり", "機種: " + rd("/proc/device-tree/model").strip("\0"), "governor: " + rd("/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor"), ""]
runs = []
for i in range(N):
    d, rc = run(0); runs.append(d)
    L.append("周 %d: " % (i + 1) + ", ".join("%s %d ms" % (k, v[0]) for k, v in sorted(d.items())) + (" rc=%d" % rc if rc else ""))
med = {k: statistics.median(r[k][0] for r in runs if k in r) for k in runs[0]}
L.append("\n## 中央値(ms。100 万要素 × 200 回)")
for k in ("scalar_map", "neon_map", "scalar_fold", "neon_fold"): L.append("%s: %d ms" % (k, med.get(k, -1)))
L.append("map: NEON はスカラーの x%.2f 倍の速さ / fold: x%.2f" % (med["scalar_map"] / med["neon_map"], med["scalar_fold"] / med["neon_fold"]))
bad = 0
for m in (0, 1):
    d, rc = run(m)
    for a, b in (("scalar_map", "neon_map"), ("scalar_fold", "neon_fold")):
        ok = d.get(a, (0, None))[1] == d.get(b, (0, None))[1]; bad += not ok
        L.append("bench%d %s = %s: %s (%s / %s)%s" % (m, a, b, "一致" if ok else "食い違い", d.get(a, (0, "?"))[1], d.get(b, (0, "?"))[1], "" if d.get(a, (0, 0))[1] == EXP[m][a] else "  ※ Python のモデルの指紋 %s と違う" % EXP[m][a]))
L.append("\n食い違い %d 件" % bad)
open(os.path.join(HERE, "report.txt"), "w").write("\n".join(L) + "\n"); print("\n".join(L))
