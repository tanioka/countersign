"""test_str_eq.py — 文字列どうしの `=`(条件の位置)。処理系と機械の答えが同じであることを見る。断る形は断ること。"""
import os, subprocess, sys, tempfile
import emu_dev, fake_kernel, sign_asm, sign_interp
CPU = emu_dev.load_cpu_class()["Cpu"]
HERE = os.path.dirname(os.path.abspath(__file__)); FAIL = []

def asm_run(src, limit=30_000_000):
    k = fake_kernel.Kernel(); k.thread_limit = limit
    class KC(CPU):
        def syscall(self, n): return k.handle(self, n)
    cpu = KC(sign_asm.generate(sign_interp.parse_source(src), "linux"))
    try: cpu.run("_start", limit=limit)
    except SystemExit: pass
    return cpu.out.decode("utf-8", "replace").strip()

def interp(src):
    d = tempfile.mkdtemp(); p = os.path.join(d, "t.sn"); open(p, "w", encoding="utf-8").write(src)
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign_interp.py"), p], capture_output=True, text=True, timeout=60)
    return r.stdout.strip().splitlines()[-1] if r.stdout.strip() else ""

SAME = [
 ("2 枝", "f : s ?\n\ts = `ab` : 1\n\ts = `cd` : 2\n\t0\n(f `ab`) + (f `cd`) * 10 + (f `zz`) * 100\n"),
 ("長さ違い", "f : s ?\n\ts = `abc` : 1\n\t0\n(f `ab`) + (f `abcd`) * 10 + (f `abc`) * 100\n"),
 ("仮引数どうし", "f : a b ?\n\ta = b : 1\n\t0\n(f `xy` `xy`) + (f `xy` `xz`) * 10\n"),
 ("切り出し", "f : [~s] ?\n\ts ' 1~ = `bc` : 1\n\t0\n(f `abc`) + (f `abd`) * 10\n"),
 ("先頭が同じで最後が違う", "f : s ?\n\ts = `abcd` : 1\n\t0\n(f `abcd`) + (f `abce`) * 10\n"),
]
for name, src in SAME:
    try: got = asm_run(src)
    except Exception as e: got = "ERR " + str(e)[:60]
    exp = interp(src)
    if got != exp: FAIL.append(name); print("NG ", name, "機械", got, "処理系", exp)
if FAIL: print("失敗", len(FAIL)); sys.exit(1)
print("全部 ok")
