"""run_on_pi.py — Pi 4 で GPIO17 と GPIO27 をジャンパ 1 本でつないで走らせる。bin/ の各プログラムを走らせ、expected.json と突き合わせて report.txt に書く。
使い方: python3 run_on_pi.py   (gpio グループのユーザーで。sudo は要らない)"""
import json, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
exp = json.load(open(os.path.join(HERE, "expected.json")))
lines = ["# GPIO17-27 ジャンパの実機照合", ""]; bad = 0
lines.append("機種: " + (open("/proc/device-tree/model", "rb").read().decode(errors="replace").strip("\0") if os.path.exists("/proc/device-tree/model") else "?"))
lines.append("chip: " + " ".join(sorted(f for f in os.listdir("/dev") if f.startswith("gpiochip"))) + "\n")
for name in sorted(exp):
    p = os.path.join(HERE, "bin", name)
    try:
        r = subprocess.run([p], capture_output=True, timeout=60); out, rc, err = r.stdout.decode(errors="replace"), r.returncode, r.stderr.decode(errors="replace").strip()
    except subprocess.TimeoutExpired: out, rc, err = "", 124, "timeout"
    ok = out == exp[name]["stdout"] and rc == exp[name]["exit"]
    bad += not ok
    lines.append("%s %s: 実機 %r (rc %d) / 期待 %r %s" % ("一致" if ok else "食い違い", name, out, rc, exp[name]["stdout"], err[:200]))
lines.append("\n食い違い %d 件" % bad)
open(os.path.join(HERE, "report.txt"), "w").write("\n".join(lines) + "\n"); print("\n".join(lines))
