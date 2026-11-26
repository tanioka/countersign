"""make.py — src/*.sn を、3 通りの最適化で --target=linux の静的 ELF にする(Pi 4 で run_on_pi.py が測る)。
  _o = --no-opt(最適化を全部切る)  _n = 最適化あり・命令の並べ替えだけ切る(SIGN_SCHED=0)  _s = 全部あり(既定)
  _n と _s の差が「並べ替えの効果」、_o と _n の差が「並べ替え以外の最適化の効果」。答えは処理系(インタープリタ)で出して expected.json に置く。"""
import json, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)
os.makedirs(os.path.join(HERE, "bin"), exist_ok=True)
VARS = {"o": ([ "--no-opt"], {"SIGN_OPT": "0"}), "n": ([], {"SIGN_SCHED": "0"}), "s": ([], {})}
exp = {}; bad = 0
for f in sorted(os.listdir(os.path.join(HERE, "src"))):
    if not f.endswith(".sn"): continue
    p = os.path.join(HERE, "src", f); name = f[:-3]
    want = subprocess.run([sys.executable, os.path.join(ROOT, "sign.py"), p], capture_output=True, text=True, timeout=300).stdout
    for v, (flags, env) in VARS.items():
        b = "%s_%s" % (name, v); out = os.path.join(HERE, "bin", b)
        r = subprocess.run([sys.executable, os.path.join(ROOT, "sign.py"), "--asm", p, "--target=linux", "--elf=" + out] + flags,
                           capture_output=True, text=True, env=dict(os.environ, **env))
        if r.returncode != 0 or not os.path.exists(out): bad += 1; print("組めず", b, r.stderr.strip().splitlines()[-1:])
        else: exp[b] = {"stdout": want, "exit": 0}
json.dump(exp, open(os.path.join(HERE, "expected.json"), "w"), ensure_ascii=False, indent=1)
print("ELF", len(exp), "本 / 組めず", bad)
