"""test_import_export.py — `#` 付きの公開の印を持つファイルの、コンパイル時の取り込み。
公開した名前だけが取り込む側に出る。非公開の名前は取り込む側の同名の定義とぶつからない。処理系と機械の答えが同じであることを見る。"""
import os, subprocess, sys, tempfile
import emu_dev, fake_kernel, sign_asm, sign_interp
CPU = emu_dev.load_cpu_class()["Cpu"]
FAIL = []
HERE = os.path.dirname(os.path.abspath(__file__))

def asm_run(path, limit=30_000_000):
    src = open(path, encoding="utf-8").read()
    sign_asm.IMPORT_DIR[0] = os.path.dirname(path)
    k = fake_kernel.Kernel(); k.thread_limit = limit
    class KC(CPU):
        def syscall(self, n): return k.handle(self, n)
    text = sign_asm.generate(sign_interp.parse_source(src), "linux")
    cpu = KC(text)
    try: cpu.run("_start", limit=limit)
    except SystemExit: pass
    return cpu.out.decode("utf-8", "replace").strip()

def interp(path):
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign_interp.py"), path], capture_output=True, text=True, timeout=60)
    return r.stdout.strip().splitlines()[-1] if r.stdout.strip() else ""

def case(name, lib, main, want=None, refuse=None):
    d = tempfile.mkdtemp()
    open(os.path.join(d, "lib.sn"), "w", encoding="utf-8").write(lib)
    p = os.path.join(d, "main.sn"); open(p, "w", encoding="utf-8").write(main)
    try:
        got = asm_run(p)
    except Exception as e:
        if refuse and refuse in str(e): return
        FAIL.append(name); print("NG ", name, "断り方:", str(e)[:100]); return
    if refuse: FAIL.append(name); print("NG ", name, "断るはずが通った", got); return
    exp = interp(p)
    if got != exp or (want is not None and got != want):
        FAIL.append(name); print("NG ", name, "機械", got, "処理系", exp, "期待", want)

IMP = "`lib.sn`@~\n"
case("公開の関数が非公開を呼ぶ", "#pub : x ? (priv x) + 1\npriv : x ? x * 10\n",
     IMP + "priv : x ? x + 100\n(pub 3) + (priv 1)\n", "132")
case("公開の値の定義", "helper : 5\n#pub2 : helper\n", IMP + "helper : 7\npub2 + helper\n", "12")
case("公開だけが見える", "#a : x ? x + 1\nb : x ? x + 2\n", IMP + "b : x ? x + 3\na (b 1)\n", "5")
case("本体の公開の印", "#a : x ? x + 1\n", "#m : x ? x * 2\n(m 3)\n", "6")
if FAIL: print("失敗", len(FAIL)); sys.exit(1)
print("全部 ok")
