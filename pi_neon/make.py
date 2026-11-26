"""make.py — test_neon.py の same_linux の事例(約 50 本。融合を含む)を集めて、--target=linux の静的 ELF にし、処理系(--check-f32)の出力を expected.json に書く。
Pi 4 で run_on_pi.py を走らせ、NEON の命令の結果が処理系と同じか(binary32 のビットまで)を確かめる。"""
import json, os, re, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE); sys.path.insert(0, ROOT)
os.makedirs(os.path.join(HERE, "bin"), exist_ok=True); os.makedirs(os.path.join(HERE, "src"), exist_ok=True)
text = open(os.path.join(ROOT, "test_neon.py"), encoding="utf-8").read()
import random
cases = []
def same_linux(name, src): cases.append((name, src))
ns = {"same_linux": same_linux, "random": random}
# 変数の定義(V1 V2 VN G Z4 MM flist)と same_linux の行・融合の for 文だけを取り出して実行する
lines = text.splitlines(); keep = []; i = 0
while i < len(lines):
    l = lines[i]
    if re.match(r"(V1, V2|VN|G|Z4|MM) = ", l) or l.startswith("def flist") or (l.startswith("    r = random.Random(seed)") and keep and keep[-1].startswith("def flist")): keep.append(l)
    elif l.startswith("same_linux("): keep.append(l)
    elif l.startswith("for n in (2, 3, 5, 6, 7, 8, 9, 16, 33):"):
        keep.append(l); i += 1
        while i < len(lines) and lines[i].startswith("    "): keep.append(lines[i]); i += 1
        continue
    i += 1
exec("\n".join(l for l in keep if "if False" not in l), ns)
print(len(cases), "本")
exp = {}; d = tempfile.mkdtemp(); fails = 0
for k, (name, src) in enumerate(cases):
    b = "n%03d" % k
    p = os.path.join(d, b + ".sn"); open(p, "w", encoding="utf-8").write(src)
    open(os.path.join(HERE, "src", b + ".sn"), "w", encoding="utf-8").write("`" + name + "\n" + src)
    r = subprocess.run([sys.executable, os.path.join(ROOT, "sign.py"), "--asm", p, "--target=linux", "--elf=" + os.path.join(HERE, "bin", b)], capture_output=True, text=True)
    if r.returncode != 0 or not os.path.exists(os.path.join(HERE, "bin", b)): print("組めず", b, name, r.stderr.strip().splitlines()[-1:]); fails += 1; continue
    w = subprocess.run([sys.executable, os.path.join(ROOT, "sign.py"), p, "--check-f32"], capture_output=True, text=True, timeout=60).stdout
    exp[b] = {"name": name, "stdout": w, "exit": 0}
json.dump(exp, open(os.path.join(HERE, "expected.json"), "w"), ensure_ascii=False, indent=1)
print("ELF", len(exp), "本 / 組めず", fails)

# ---- --par: pi_check/src_par の各プログラムを、直列(_s)・--par=2・3・4 で。答えは pi_check/expected.json(処理系の答え / 手計算)
pe = json.load(open(os.path.join(ROOT, "pi_check", "expected.json")))
import shutil
for f in sorted(os.listdir(os.path.join(ROOT, "pi_check", "src_par"))):
    if not f.endswith(".sn"): continue
    p = os.path.join(d, f); shutil.copy(os.path.join(ROOT, "pi_check", "src_par", f), p)
    for suf, opt in (("_s", []), ("_p2", ["--par=2"]), ("_p3", ["--par=3"]), ("_p4", ["--par=4"])):
        b = f[:-3] + suf
        r = subprocess.run([sys.executable, os.path.join(ROOT, "sign.py"), "--asm", p, "--target=linux"] + opt + ["--elf=" + os.path.join(HERE, "bin", b)], capture_output=True, text=True)
        if r.returncode != 0: print("組めず", b, r.stderr.strip().splitlines()[-1:]); continue
        exp[b] = {"name": "par " + b, "stdout": pe[b]["stdout"], "exit": 0, "par": True}
json.dump(exp, open(os.path.join(HERE, "expected.json"), "w"), ensure_ascii=False, indent=1)
print("合計", len(exp), "本")
