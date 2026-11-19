"""make_expected.py — 各プログラムを疑似カーネル(fake_kernel.py)で走らせた出力を expected.json に書く(『疑似カーネルの予想』)。
実機の結果をこれと突き合わせて、食い違いを洗い出す。"""
import json, os, sys, shutil, tempfile
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE); sys.path.insert(0, ROOT)
os.environ.setdefault("EMU_LIMIT", "400000000")
import sign_asm, sign_interp, sign_bus, fake_kernel, emu_dev
sign_asm.IMPORT_DIR[0] = ROOT
out = {}
for f in sorted(os.listdir(os.path.join(HERE, "src"))):
    if not f.endswith(".sn"): continue
    name = f[:-3]
    src = open(os.path.join(HERE, "src", f), encoding="utf-8").read()
    k = fake_kernel.Kernel(i2c=sign_bus.FakeI2c([]), spi=sign_bus.FakeSpi())             # I2C は相手が誰もいない・SPI はループバック(MOSI と MISO をつないだ状態)
    import tempfile; k.sysroot = tempfile.mkdtemp()
    Cpu = emu_dev.load_cpu_class()["Cpu"]
    class KC(Cpu):
        def syscall(self, n): return k.handle(self, n)
    cpu = KC(sign_asm.generate(sign_interp.parse_source(src), "linux", real_dev=True)); cpu.run("_start", limit=int(os.environ["EMU_LIMIT"]))
    out[name] = {"stdout": cpu.out.decode("utf-8", "replace"), "exit": cpu.exit}
import subprocess, tempfile
for f in sorted(os.listdir(os.path.join(HERE, "src_db"))) if os.path.isdir(os.path.join(HERE, "src_db")) else []:       # DB: 処理系の仮想装置(--db)の出力が『予想』
    d = tempfile.mkdtemp()
    for dep in ("std.sn", "sqlite.sn"): shutil.copy(os.path.join(ROOT, dep), os.path.join(d, dep))
    shutil.copy(os.path.join(HERE, "src_db", f), os.path.join(d, f))
    r = subprocess.run([sys.executable, os.path.join(ROOT, "sign.py"), os.path.join(d, f), "--db=" + d], capture_output=True, cwd=d)
    out[f[:-3]] = {"stdout": r.stdout.decode("utf-8", "replace"), "exit": r.returncode}
for f in sorted(os.listdir(os.path.join(HERE, "src_par"))) if os.path.isdir(os.path.join(HERE, "src_par")) else []:       # 並列: 処理系(メモ化した速い道)の答えが『予想』。直列・--par=2・3・4 の全部とも同じはず
    d = tempfile.mkdtemp(); shutil.copy(os.path.join(HERE, "src_par", f), os.path.join(d, f))
    if f == "t_par_loop.sn":        # 2 億回の輪は処理系では遅いので、答えは手計算: 4 * (200000000 * 200000001 / 2)
        r = type("R", (), {"stdout": b"%d\n" % (4 * (200000000 * 200000001 // 2)), "returncode": 0})()
    else: r = subprocess.run([sys.executable, os.path.join(ROOT, "sign.py"), os.path.join(d, f)], capture_output=True, cwd=d)
    for suf in ("_s", "_p2", "_p3", "_p4", "_p4site", "_p4l1000", "_p4l0"): out[f[:-3] + suf] = {"stdout": r.stdout.decode("utf-8", "replace"), "exit": r.returncode}
for n_, ans in (("t_opt_fib", 14930352), ("t_opt_loop", 3 * (100000000 * 100000001 // 2)), ("t_opt_list", 3000000 * 55)):       # 最適化の効果: 答えは手計算(処理系では遅い)
    for suf in ("_opt", "_noopt"): out[n_ + suf] = {"stdout": "%d\n" % ans, "exit": 0}
for n_, ans in (("t_spec_or", 9227465), ("t_spec_gfalse", 3524578), ("t_spec_gtrue", 9227465), ("t_spec_trap", 14930352), ("t_spec_rows", 9227465)):       # 投機: 答えは手計算(fib 36=14930352・fib 35=9227465・fib 33=3524578)
    for suf in ("_s", "_p4", "_spec", "_p2", "_p2spec", "_p3", "_p3spec", "_specab", "_p3specab", "_look", "_p3look"): out[n_ + suf] = {"stdout": "%d\n" % ans, "exit": 0}
for n_, ans in (("t_hof_rep", 300000000), ("t_hof_fold", 165000000), ("t_hof_map", 110000000), ("t_hof_cap", 495000000)):       # 特殊化(第110段): 答えは手計算(処理系では遅い)。小さい回数では処理系・疑似カーネルと一致を確認済み
    for suf in ("_hof", "_dir"): out[n_ + suf] = {"stdout": "%d\n" % ans, "exit": 0}
for suf in ("_s", "_p2", "_p4"): out["t_hof_par" + suf] = {"stdout": "48315634\n", "exit": 0}
json.dump(out, open(os.path.join(HERE, "expected.json"), "w"), ensure_ascii=False, indent=1)
for n, v in out.items(): print(n, repr(v["stdout"]))
