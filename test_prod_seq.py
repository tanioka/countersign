"""test_prod_seq.py — Int だけの積 `a , b` を並置 `a b` と同じに出す(type_system.md §3.x: 要素の型が揃えば List(T))。
処理系と機械の答えが同じであることを見る。リスト・文字列が混ざる積は断る。"""
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
 ("2 つの積(演算つき)", "g : a b ?\n\ta + 1 , b\n||g 1 2||\n"),
 ("3 つの積", "g : a b c ?\n\ta , b , c\n||g 1 2 3||\n"),
 ("積の総和", "g : a b ?\n\t[+] (a , b * 2)\n(g 3 4)\n"),
]
for name, src in SAME:
    try: got = asm_run(src)
    except Exception as e: got = "ERR " + str(e)[:60]
    exp = interp(src)
    if got != exp: FAIL.append(name); print("NG ", name, "機械", got, "処理系", exp)
# リストが混ざる積は断る(入れ子になる。誤った答えは出さない)
try: asm_run("g : a ?\n\ta , [1 2]\n||g 1||\n"); FAIL.append("混ざる積"); print("NG  混ざる積が通った")
except Exception: pass
if FAIL: print("失敗", len(FAIL)); sys.exit(1)
print("全部 ok")
