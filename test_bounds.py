#!/usr/bin/env python3
"""番地の境界検査(--check-bounds / --ram)の試験。装置の帯の手前・終端の先、宣言した範囲、UART、速い道、検査を付けないときの挙動。python test_bounds.py"""
import os, sys
sys.setrecursionlimit(20000); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sign_interp as S, sign_gfx as G

def run(src, on=True, guard=0x100, rams=()):
    S.DEVICES.clear(); S.MEMORY.clear(); S._PURE_OV.clear()
    d = G.Display(8, 4, "null"); S.DEVICES.append(d)
    S.BOUNDS[0] = on; S.BOUNDS[1] = guard; S.BOUNDS[2][:] = list(rams)
    try: return S.show(S.run(src)[-1]), d
    except S.SignError as e: return "ERR " + str(e), d
    finally: S.BOUNDS[0] = False; S.BOUNDS[2][:] = []
bad = 0
def check(name, got, want):
    global bad
    ok = got == want; bad += not ok
    print(("ok  " if ok else "NG  ") + name + ("" if ok else f"  got {got!r} want {want!r}"))
def has(name, got, frag):
    global bad
    ok = frag in got; bad += not ok
    print(("ok  " if ok else "NG  ") + name + ("" if ok else f"  got {got!r} want ...{frag}..."))

d0 = G.Display(8, 4, "null"); B, Z = d0.base, d0.size; END = B + Z
check("帯の中の書き込みは通る", run(f"a : {B + 8} # 5\n@{B + 0}")[0] != "", True)
has("終端の先への書き込み", run(f"{END} # 1")[0], "終端から 1 番地先")
has("終端の先への読み込み", run(f"@{END + 4}")[0], "読み込み")
has("終端の先への読み込み(番地)", run(f"@{END + 4}")[0], "終端から 5 番地先")
has("帯の手前への書き込み", run(f"{B - 4} # 1")[0], "手前 4 番地")
check("見張る幅の外は普通のメモリ", run(f"a : {END + 0x1000} # 7\n@{END + 0x1000}")[0], "7")
check("検査を付けなければ終端の先も通る", run(f"a : {END} # 7\n@{END}", on=False)[0], "7")
has("見張る幅を狭めると外は通る / 内は断る", run(f"{END + 8} # 1", guard=4)[0] + "x", "x")
check("見張る幅を狭めると外は通る", run(f"a : {END + 8} # 1\n@{END + 8}", guard=4)[0], "1")
check("UART は通る", run(f"{S.UART} # 65\n0")[0], "0")
has("--ram: 宣言の外はエラー", run("a : 4096 # 1\n0", rams=[(0x10000, 0x100)])[0], "どれにも入っていません")
check("--ram: 宣言の中は通る", run("a : 65536 # 9\n@65536", rams=[(0x10000, 0x100)])[0], "9")
check("--ram: 帯の中も通る", run(f"a : {B + 8} # 5\n0", rams=[(0x10000, 0x100)])[0], "0")
has("--ram: 宣言の終端の先", run("a : 65792 # 1\n0", rams=[(0x10000, 0x100)])[0], "どれにも入っていません")
# 速い道(関数の中の整数だけの書き込み・読み込み)でも同じ
fill = f"fill : a n ?\n\tn = 0 : a\n\tfill (a + 4) (n - 1) # 0\n"
has("速い道: 帯をはみ出す書き込みの輪", run(f"w : a n ?\n\tn = 0 : a\n\t(a # n) ; w (a + 4) (n - 1)\nw {END - 8} 4")[0], "終端")
check("速い道: 帯の中だけなら通る", run(f"w : a n ?\n\tn = 0 : a\n\t(a # n) ; w (a + 4) (n - 1)\nw {END + 0x1000} 3")[0] != "", True)
has("速い道: はみ出す読み込み", run(f"r : a n ?\n\tn = 0 : 0\n\t(@a) + (r (a + 4) (n - 1))\nr {END - 4} 3")[0], "読み込み")
# 命令行(--check-bounds / --ram)。位置つきのエラーで終了コード 1
import subprocess, tempfile
def cli(src, *flags):
    with tempfile.NamedTemporaryFile("w", suffix=".sn", delete=False, encoding="utf-8") as f: f.write(src); n = f.name
    try:
        r = subprocess.run([sys.executable, os.path.join(os.path.dirname(os.path.abspath(__file__)), "sign.py"), *flags, "--display=null", n], capture_output=True, text=True, timeout=60)
        return r.returncode, r.stdout + r.stderr
    finally: os.unlink(n)
d1 = G.parse_spec("null"); E1 = d1.base + d1.size
rc, out = cli(f"a : {E1} # 1\n0\n", "--check-bounds"); check("CLI: はみ出しは終了コード1", rc, 1); has("CLI: 位置つきの文面", out, "終端から 1 番地先")
check("CLI: 付けなければ通る", cli(f"a : {E1} # 1\n0\n")[0], 0)
check("CLI: 帯の中は通る", cli(f"a : {d1.base + 8} # 1\n0\n", "--check-bounds")[0], 0)
check("CLI: --ram の外は断る", cli("a : 4096 # 1\n0\n", "--ram=0x2000:0x100")[0], 1)
check("CLI: --ram の中は通る", cli("a : 8192 # 1\n0\n", "--ram=0x2000:0x100")[0], 0)
# 静的検査(sign_check.py)。決まる番地には実行時の検査と同じ答え、決まらない番地は黙る
import random, sign_check as C
def static(src, rams=(), guard=0x100, w=8, h=4):
    d = G.Display(w, h, "null")
    return [r for r in C.check(src, bounds={"bands": [(d.base, d.size, "Display")], "guard": guard, "rams": list(rams)}) if r["kind"] == "bounds-static"]
check("静的: 字面の終端の先", len(static(f"{END} # 1\n0\n")), 1)
check("静的: 帯の中は無し", len(static(f"{B + 8} # 1\n0\n")), 0)
check("静的: 名前の定数の算術", len(static(f"E : {END}\nS : 4\n(E + S) # 3\n0\n")), 1)
check("静的: 読み込みも", len(static(f"@({END} + 8)\n")), 1)
check("静的: 引数は呼び出しが無ければ決まらない", len(static(f"w : a ? a # 1\n0\n")), 0)
check("静的: 局所の名前が定数を隠す", len(static(f"E : {END}\nw : E ? E # 1\n0\n")), 0)
check("静的: 位置つき", static(f"0\n{END} # 1\n")[0]["line"], 2)
check("静的: --ram の外", len(static("4096 # 1\n0\n", rams=[(0x2000, 0x100)])), 1)
check("静的: --ram の中", len(static("8192 # 1\n0\n", rams=[(0x2000, 0x100)])), 0)
rnd = random.Random(5); mism = 0
for _ in range(120):                                # 字面の番地: 静的の判定と実行時の判定が一致する
    a = rnd.choice([B + rnd.randint(-0x180, 0x20), END + rnd.randint(-0x20, 0x180), rnd.randint(0, 0x20000), B + rnd.randint(0, Z - 1)])
    if a < 0: continue
    for form, src in (("write", f"{a} # 1\n0\n"), ("read", f"@{a}\n")):
        s = len(static(src)) > 0; r = run(src)[0].startswith("ERR")
        if s != r: mism += 1; print("  不一致", form, hex(a), "静的", s, "実行", r)
check("静的と実行時の判定が字面の番地で一致", mism, 0)
# 領域(意図した参照範囲)と Iterator・スライス
def reg(src, regions, **kw):
    return [r for r in C.check(src, bounds={"bands": [], "guard": 0x100, "rams": [], "regions": regions}) if r["kind"].startswith("bounds")]
R = {"fb": (None, 0x100)}
check("領域: 範囲の中", len(reg("fb : 0x1000\n(fb + 0xFC) # 2\n0\n", R)), 0)
check("領域: 終端の先", len(reg("fb : 0x1000\n(fb + 0x100) # 2\n0\n", R)), 1)
check("領域: 手前", len(reg("fb : 0x1000\n@(fb - 4)\n", R)), 1)
check("領域: 差は数に戻る", len(reg("fb : 0x1000\nn : (fb + 8) - fb\n(fb + n) # 1\n0\n", R)), 0)
check("領域: 引数は決めない", len(reg("fb : 0x1000\nw : a ? (fb + a) # 1\n0\n", R)), 0)
check("領域: 仮引数が名前を隠す", len(reg("fb : 0x1000\nw : fb ? (fb + 0x200) # 1\n0\n", R)), 0)
check("領域: 始まりを宣言と一緒に", len(reg("fb : 0x1000\n(fb + 0x100) # 2\n0\n", {"fb": (0x1000, 0x100)})), 1)
check("Iterator: 刻み付き範囲の中", len(reg("fb : 0x1000\nr : [fb ~+ 4 ~ fb + 0xFC]\n0\n", R)), 0)
check("Iterator: 刻み付き範囲の最後が外", len(reg("fb : 0x1000\nr : [fb ~+ 4 ~ fb + 0x100]\n0\n", R)), 1)
check("Iterator: 刻みで終わりを越えない", len(reg("fb : 0x1000\nr : [fb ~+ 8 ~ fb + 0x100]\n0\n", R)), 1)
check("スライス: 範囲の中", len(reg("fb : 0x1000\nr : [fb ~ fb + 0x40]\n0\n", R)), 0)
check("スライス: 範囲の外", len(reg("fb : 0x1000\nr : [fb ~ fb + 0x200]\n0\n", R)), 1)
check("スライス: 逆向きの範囲", len(reg("fb : 0x1000\nr : [fb + 0x40 ~ fb]\n0\n", R)), 0)
check("領域: 領域を持たない名前の範囲は見ない", len(reg("g : 0x1000\nr : [g ~ g + 0x200]\n0\n", R)), 0)
# option.ms と命令行
import tempfile, shutil, subprocess
dd = tempfile.mkdtemp(); open(os.path.join(dd, "option.ms"), "w").write("region.fb : 0x1000:0x100\n")
open(os.path.join(dd, "a.sn"), "w").write("fb : 0x1000\n(fb + 0x100) # 1\n0\n")
r_ = subprocess.run([sys.executable, os.path.join(os.path.dirname(os.path.abspath(__file__)), "sign_check.py"), os.path.join(dd, "a.sn")], capture_output=True, text=True)
check("option.ms の region が効く", r_.returncode, 1); has("option.ms: 文面", r_.stdout, "領域 fb")
r_ = subprocess.run([sys.executable, os.path.join(os.path.dirname(os.path.abspath(__file__)), "sign_check.py"), os.path.join(dd, "a.sn"), "--region=fb:0x10000"], capture_output=True, text=True)
check("命令行の --region は option.ms より先", r_.returncode, 0)
shutil.rmtree(dd)
# 区間解析(引数・輪の回数で決まる番地): 確実なはみ出し(error)が、実行時の検査と一致する
def sim(src, **kw):
    return [r for r in static(src, **kw) if r["severity"] == "error"]
rnd2 = random.Random(9); mism2 = 0
for _ in range(60):
    base = rnd2.choice([END - 4 * rnd2.randint(1, 12), B + 0x1000 + 4 * rnd2.randint(0, 20), END + 4 * rnd2.randint(0, 30), B - 4 * rnd2.randint(1, 8)])
    step = rnd2.choice([4, 8, -4]); n = rnd2.randint(0, 14)
    src = f"fill : a n ?\n\tn = 0 : a\n\t(a # n) : fill (a + {step}) (n - 1)\nfill {base} {n}\n" if step > 0 else f"fill : a n ?\n\tn = 0 : a\n\t(a # n) : fill (a - {-step}) (n - 1)\nfill {base} {n}\n"
    s = len(sim(src)) > 0; r_txt = run(src)[0]; r = "境界" in r_txt
    if s != r: mism2 += 1; print("  不一致", base, step, n, "静的", s, "実行", r_txt[:60])
check("区間: 輪の書き込みで静的と実行時が一致", mism2, 0)
check("区間: 引数が定数でなければ通す", len(sim(f"fill : a n ?\n\tn = 0 : a\n\t(a # n) : fill (a + 4) (n - 1)\n0\n")), 0)
check("区間: 入口の定数の引数で呼ぶ", len(sim(f"w : a ?\n\ta # 1\nw {END}\n")), 1)
check("区間: 局所の定義を通る", len(sim(f"w : a b ?\n\tc : a + b\n\tc # 1\nw {END - 8} 8\n")), 1)
check("区間: 局所の定義で帯の中", len(sim(f"w : a b ?\n\tc : a + b\n\tc # 1\nw {END - 8} 4\n")), 0)
check("区間: 入れ子の呼び(非末尾)", len(sim(f"g : a ?\n\ta # 1\nh : a ?\n\tg (a + 8)\nh {END - 8}\n")), 1)
check("区間: 決まらない条件で止まる", len(sim(f"w : a ?\n\t(@a) = 0 : (a + {Z}) # 1\n\t0\nw {B + 8}\n")), 0)
check("区間: 同じ行は1件にまとめる", len(sim(f"fill : a n ?\n\tn = 0 : a\n\t(a # n) : fill (a + 4) (n - 1)\nfill {END} 5\n")), 1)
check("区間: 到達しない関数は見ない", len(sim(f"unused : a ?\n\ta # 1\n0\n")), 0)
print("不一致", bad); sys.exit(1 if bad else 0)
