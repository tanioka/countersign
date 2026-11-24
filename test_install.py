#!/usr/bin/env python3
"""test_install.py — 簡単インストーラ(install.sh・install_manifest.txt・install.ps1)の試験。
  1. install_manifest.txt が、sign.py から import と _tool(...) をたどった物(コンパイラ sign_asm 系を除く)と一致する
  2. install.sh で別の場所に入れて動く・もう一度入れても動く・消せる・他人のフォルダは消さない
  3. install.ps1 は Windows でないと動かせないので、ここでは中身の取り決め(マニフェストを読む・UTF-8・消す前の目印)だけ見る"""
import os, re, subprocess, sys, tempfile, shutil
HERE = os.path.dirname(os.path.abspath(__file__))
bad = 0
def check(name, got, want):
    global bad
    ok = got == want
    print(("ok  " if ok else "NG  ") + name)
    if not ok: bad += 1; print("    得た:", got); print("    期待:", want)

def manifest():
    return [l.strip() for l in open(os.path.join(HERE, "install_manifest.txt"), encoding="utf-8") if l.strip() and not l.startswith("#")]

# --- 1. マニフェストが足りていて、余計な物が無い ---
mods = {f[:-3] for f in os.listdir(HERE) if f.endswith(".py")}
def deps(m):
    s = open(os.path.join(HERE, m + ".py"), encoding="utf-8").read()
    return {x for x in re.findall(r"^\s*(?:import|from)\s+([A-Za-z_]\w*)", s, re.M) if x in mods}
interp = open(os.path.join(HERE, "sign_interp.py"), encoding="utf-8").read()
EXCLUDED = {"sign_asm"}                       # コンパイラ(--asm)は入れない
need, todo = set(), {"sign", "sign_interp"} | (set(re.findall(r'_tool\("([a-z_0-9]+)"\)', interp)) - EXCLUDED)
while todo:
    m = todo.pop()
    if m in need or m not in mods: continue
    need.add(m); todo |= deps(m) - EXCLUDED
files = manifest()
check("マニフェストの .py は、sign.py からたどれる物と同じ", sorted(f[:-3] for f in files if f.endswith(".py")), sorted(need))
check("std.sn が入る", "std.sn" in files, True)
check("マニフェストの全部が実在する", [f for f in files if not os.path.isfile(os.path.join(HERE, f))], [])
sh = open(os.path.join(HERE, "install.sh"), encoding="utf-8").read()
ps = open(os.path.join(HERE, "install.ps1"), encoding="utf-8").read()
check("install.ps1 もマニフェストを読む", "install_manifest.txt" in ps and "install_manifest.txt" in sh, True)
check("install.ps1 は消す前に目印を見る", ".sign-installed" in ps and "PYTHONUTF8" in ps, True)

# --- 2. install.sh ---
def run(*args, **kw):
    return subprocess.run(["sh", os.path.join(HERE, "install.sh"), *args], capture_output=True, text=True, timeout=120, **kw)
tmp = tempfile.mkdtemp()
try:
    pre, bin_ = os.path.join(tmp, "p"), os.path.join(tmp, "b")
    r = run("--prefix", pre, "--bin", bin_)
    check("入れる: 終了コード 0", r.returncode, 0)
    check("マニフェストの全部が置かれる", sorted(x for x in os.listdir(pre) if x != ".sign-installed" and x != "__pycache__"), sorted(files))
    prog = os.path.join(tmp, "t.sn"); open(prog, "w", encoding="utf-8").write("6 * 7\n")
    r2 = subprocess.run([os.path.join(bin_, "sign"), prog], capture_output=True, text=True, timeout=60)
    check("sign コマンドで実行できる(6 * 7)", (r2.returncode, r2.stdout.strip()), (0, "42"))
    r3 = subprocess.run([os.path.join(bin_, "sign"), "--strict", prog], capture_output=True, text=True, timeout=60)
    check("--strict も動く(値は出さない)", (r3.returncode, r3.stdout.strip()), (0, ""))
    check("もう一度入れても動く", run("--prefix", pre, "--bin", bin_).returncode, 0)
    r4 = run("--uninstall", "--prefix", pre, "--bin", bin_)
    check("消せる", (r4.returncode, os.path.exists(pre), os.path.exists(os.path.join(bin_, "sign"))), (0, False, False))
    other = os.path.join(tmp, "other"); os.makedirs(other); open(os.path.join(other, "mine.txt"), "w").write("x")
    r5 = run("--prefix", other, "--bin", bin_)
    check("他人のフォルダには入れない", (r5.returncode != 0, os.listdir(other)), (True, ["mine.txt"]))
    r6 = run("--uninstall", "--prefix", other, "--bin", bin_)
    check("他人のフォルダは消さない", (r6.returncode, os.path.isfile(os.path.join(other, "mine.txt"))), (0, True))
    check("危ない置き場所(/)は断る", run("--prefix", "/", "--bin", bin_).returncode, 2)
    check("知らないオプションは断る", run("--nope").returncode, 2)
finally:
    shutil.rmtree(tmp, ignore_errors=True)
print("\n全部 ok" if not bad else f"\n{bad} 件 NG"); sys.exit(1 if bad else 0)
