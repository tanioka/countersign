"""run_on_pi.py — Pi 4 で NEON(n…)と --par(t_par…)の ELF を走らせ、expected.json と突き合わせる。report.txt に書く。
NEON: 処理系(--check-f32)と出力が一致するか。par: 答えが直列と同じか、時間(ms)が直列に比べて縮むか。"""
import json, os, subprocess, time, sys
HERE = os.path.dirname(os.path.abspath(__file__))
exp = json.load(open(os.path.join(HERE, "expected.json")))
L = ["# NEON と --par の実機照合", "機種: " + (open("/proc/device-tree/model", "rb").read().decode(errors="replace").strip("\0") if os.path.exists("/proc/device-tree/model") else "?"), "nproc: %d" % (os.cpu_count() or 0), ""]
bad = 0; ms = {}
for b in sorted(exp):
    t0 = time.time()
    try: r = subprocess.run([os.path.join(HERE, "bin", b)], capture_output=True, timeout=120); out, rc, err = r.stdout.decode(errors="replace"), r.returncode, r.stderr.decode(errors="replace").strip()
    except subprocess.TimeoutExpired: out, rc, err = "", 124, "timeout"
    dt = int((time.time() - t0) * 1000); ms[b] = dt
    ok = out == exp[b]["stdout"] and rc == 0; bad += not ok
    L.append("%s %s [%s] %d ms%s" % ("一致" if ok else "食い違い", b, exp[b]["name"], dt, "" if ok else "  実機 %r (rc %d) / 期待 %r %s" % (out, rc, exp[b]["stdout"], err[:120])))
L.append("")
L.append("## --par の時間(直列に対する比)")
for prog in sorted({b.rsplit("_", 1)[0] for b in exp if exp[b].get("par")}):
    s = ms.get(prog + "_s", 0)
    L.append("%s: 直列 %d ms / " % (prog, s) + " / ".join("%s %d ms (x%.2f)" % (k, ms[prog + "_" + k], (s / ms[prog + "_" + k]) if ms.get(prog + "_" + k) else 0) for k in ("p2", "p3", "p4") if prog + "_" + k in ms))
L.append("\n食い違い %d 件" % bad)
open(os.path.join(HERE, "report.txt"), "w").write("\n".join(L) + "\n"); print("\n".join(L))
