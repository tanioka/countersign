"""build.py — src/*.sn を --real-dev で AArch64 の静的 ELF にして bin/ に置く(この箱で clang と ld.lld が要る)。"""
import os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)
os.makedirs(os.path.join(HERE, "bin"), exist_ok=True)
import shutil, tempfile
bad = 0
tmpd = tempfile.mkdtemp()
for dep in ("std.sn", "aht25.sn", "sqlite.sn"): shutil.copy(os.path.join(ROOT, dep), os.path.join(tmpd, dep))      # 取り込みは同じ箱から
for f in sorted(os.listdir(os.path.join(HERE, "src"))):
    if not f.endswith(".sn"): continue
    src = os.path.join(tmpd, f); shutil.copy(os.path.join(HERE, "src", f), src); out = os.path.join(HERE, "bin", f[:-3])
    r = subprocess.run([sys.executable, os.path.join(ROOT, "sign.py"), "--asm", src, "--real-dev", "--elf=" + out], capture_output=True, text=True)
    print(("ok " if r.returncode == 0 else "NG ") + f, (r.stderr.strip().splitlines() or [""])[-1][:100]); bad += r.returncode != 0
# 並列(--par): src_par/ の各プログラムを、直列(_s)・--par=2(_p2)・--par=3(_p3)・--par=4(_p4 = 既定の深さ方式・境 100、_p4site = 前の既定の位置ごとの数え・境 1000、_p4l1000 = 深さ方式で境 1000、_p4l0 = 軽さ判定なし)で bin/ に置く(--real-dev なしの linux)
if os.path.isdir(os.path.join(HERE, "src_par")):
    for f in sorted(os.listdir(os.path.join(HERE, "src_par"))):
        if not f.endswith(".sn"): continue
        src = os.path.join(tmpd, f); shutil.copy(os.path.join(HERE, "src_par", f), src)
        for suf, opt in (("_s", []), ("_p2", ["--par=2"]), ("_p3", ["--par=3"]), ("_p4", ["--par=4"]), ("_p4site", ["--par=4", "--par-site-light"]), ("_p4l1000", ["--par=4", "--par-light=1000"]), ("_p4l0", ["--par=4", "--par-light=0"])):
            out = os.path.join(HERE, "bin", f[:-3] + suf)
            r = subprocess.run([sys.executable, os.path.join(ROOT, "sign.py"), "--asm", src, "--target=linux"] + opt + ["--elf=" + out], capture_output=True, text=True)
            print(("ok " if r.returncode == 0 else "NG ") + f + suf, (r.stderr.strip().splitlines() or [""])[-1][:100]); bad += r.returncode != 0
# 最適化の効果(第108段): src_opt/ の各プログラムを、最適化あり(_opt)となし(--no-opt、_noopt)で bin/ に置く(linux)
if os.path.isdir(os.path.join(HERE, "src_opt")):
    for f in sorted(os.listdir(os.path.join(HERE, "src_opt"))):
        if not f.endswith(".sn"): continue
        src = os.path.join(tmpd, f); shutil.copy(os.path.join(HERE, "src_opt", f), src)
        for suf, opt in (("_opt", []), ("_noopt", ["--no-opt"])):
            out = os.path.join(HERE, "bin", f[:-3] + suf)
            r = subprocess.run([sys.executable, os.path.join(ROOT, "sign.py"), "--asm", src, "--target=linux"] + opt + ["--elf=" + out], capture_output=True, text=True)
            print(("ok " if r.returncode == 0 else "NG ") + f + suf, (r.stderr.strip().splitlines() or [""])[-1][:100]); bad += r.returncode != 0
# 特殊化(第110段): src_hof/ の高階関数の版(_hof)と、手で特殊化した版(_dir)を bin/ に置く(linux)。t_hof_par は直列(_s)・--par=2(_p2)・--par=4(_p4)
if os.path.isdir(os.path.join(HERE, "src_hof")):
    for f in sorted(os.listdir(os.path.join(HERE, "src_hof"))):
        if not f.endswith(".sn"): continue
        src = os.path.join(tmpd, f); shutil.copy(os.path.join(HERE, "src_hof", f), src)
        for suf, opt in ((("_s", []), ("_p2", ["--par=2"]), ("_p4", ["--par=4"])) if f == "t_hof_par.sn" else (("", []),)):
            out = os.path.join(HERE, "bin", f[:-3] + suf)
            r = subprocess.run([sys.executable, os.path.join(ROOT, "sign.py"), "--asm", src, "--target=linux"] + opt + ["--elf=" + out], capture_output=True, text=True)
            print(("ok " if r.returncode == 0 else "NG ") + f + suf, (r.stderr.strip().splitlines() or [""])[-1][:100]); bad += r.returncode != 0
# 投機(第109段 --par-spec): src_spec/ の各プログラムを、直列(_s)・--par=4(_p4。投機なし)・--par-spec(_spec。4 本)で bin/ に置く(linux)
if os.path.isdir(os.path.join(HERE, "src_spec")):
    for f in sorted(os.listdir(os.path.join(HERE, "src_spec"))):
        if not f.endswith(".sn"): continue
        src = os.path.join(tmpd, f); shutil.copy(os.path.join(HERE, "src_spec", f), src)
        for suf, opt in (("_s", []), ("_p4", ["--par=4"]), ("_spec", ["--par-spec"]), ("_p2", ["--par=2"]), ("_p2spec", ["--par=2", "--par-spec"]), ("_p3", ["--par=3"]), ("_p3spec", ["--par=3", "--par-spec"]), ("_specab", ["--par-spec", "--spec-abort"]), ("_p3specab", ["--par=3", "--par-spec", "--spec-abort"])) + ((("_look", ["--par-spec", "--spec-look=3"]), ("_p3look", ["--par=3", "--par-spec", "--spec-look=3"])) if f == "t_spec_rows.sn" else ()):
            out = os.path.join(HERE, "bin", f[:-3] + suf)
            r = subprocess.run([sys.executable, os.path.join(ROOT, "sign.py"), "--asm", src, "--target=linux"] + opt + ["--elf=" + out], capture_output=True, text=True)
            print(("ok " if r.returncode == 0 else "NG ") + f + suf, (r.stderr.strip().splitlines() or [""])[-1][:100]); bad += r.returncode != 0
# --real-db: gcc で作る一式(libsqlite3 が要る)を dbbundle/ に
if os.path.isdir(os.path.join(HERE, "src_db")):
    for f in sorted(os.listdir(os.path.join(HERE, "src_db"))):
        if not f.endswith(".sn"): continue
        src = os.path.join(tmpd, f); shutil.copy(os.path.join(HERE, "src_db", f), src); out = os.path.join(HERE, "dbbundle", f[:-3])
        r = subprocess.run([sys.executable, os.path.join(ROOT, "sign.py"), "--asm", src, "--pi-bundle=" + out], capture_output=True, text=True)
        print(("ok " if r.returncode == 0 else "NG ") + "db/" + f, (r.stderr.strip().splitlines() or [""])[-1][:100]); bad += r.returncode != 0
sys.exit(1 if bad else 0)
