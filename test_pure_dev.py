#!/usr/bin/env python3
"""速い道(run_pure)が描画装置への書き込みを記録して、成功したあと順に再生する分の試験。
速い道あり(既定)と無し(SIGN_NO_PURE=1)で、描画装置の ascii 出力・標準出力・終了コードが同じになることを確かめる。python test_pure_dev.py"""
import os, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
bad = 0
def check(name, got, want):
    global bad
    ok = got == want; bad += not ok
    print(("ok  " if ok else "NG  ") + name + ("" if ok else f"\n    得た: {got!r}\n    期待: {want!r}"))
TMP = tempfile.mkdtemp()
def run(src, pure, flags=("--display=ascii",)):
    p = os.path.join(TMP, "t.sn"); open(p, "w", encoding="utf-8").write(src)
    env = dict(os.environ); env["SIGN_NO_PURE"] = "0" if pure else "1"
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p, *flags], capture_output=True, text=True, timeout=120, env=env, cwd=HERE)
    return (r.returncode, r.stdout, r.stderr)
def same(name, src, flags=("--display=ascii",)):
    a = run(src, True, flags); b = run(src, False, flags)
    check(name, a, b); return a
G = open(os.path.join(HERE, "draw_gfx.sn"), encoding="utf-8").read().split("clear 0x000040")[0]
same("四角を重ねて描く", G + "d : i ?\n\ti >= 8 : 0\n\tseq2 (rect (i * 3) (i * 2) 10 6 (i * 0x20000F)) (d (i + 1))\nseq3 (clear 0) (d 0) (present 0)\n")
same("線と四角と present を 2 回", G + "d : i ?\n\ti >= 5 : 0\n\tseq3 (line 0 i 63 (31 - i) 0xFFFFFF) (rect i i 3 3 0xFF0000) (d (i + 1))\nseq5 (clear 0) (d 0) (present 0) (d 2) (present 0)\n")
same("描いたあと 0 で割って外れる: 描画が二重にならない", G + "d : i ?\n\ti >= 4 : (100 / (i - 4))\n\tseq2 (rect (i * 8) 0 6 6 0xFF00FF) (d (i + 1))\nseq3 (clear 0) (d 0) (present 0)\n")
same("描いたあと外れる(単位の実引数)", G + "d : i ?\n\ti >= 4 : 0\n\tseq2 (rect (i * 8) 0 6 6 0xFF00FF) (d (i + 1))\nq : x ? x > 3 : x\nseq3 (clear 0) (d (q 1)) (present 0)\n")
same("装置の読み(STATUS)は普通の道", G + "st : z ? @(gfx + 0x20)\nd : i ?\n\ti >= 3 : (st 0)\n\tseq2 (rect (i * 30) 0 40 6 5) (d (i + 1))\nseq3 (clear 0) (println_int (d 0)) (present 0)\n")
same("はみ出して STATUS が立つ", G + "st : z ? @(gfx + 0x20)\nseq3 (clear 0) (rect 60 30 10 10 0xFFFFFF) (println_int (st 0))\n")
same("PLOT を並べる", G + "pl : x y c ? seq3 (px # x) (py # y) (seq2 (color # c) (cmd # 1))\nd : i ?\n\ti >= 20 : 0\n\tseq2 (pl i (i / 2) 0xFFFFFF) (d (i + 1))\nseq3 (clear 0) (d 0) (present 0)\n")
same("BLIT はメモリを読むので普通の道(順が変わらない)", G + "R : 0x6000\nsrc : gfx + 0x28\nsp : i ? (R + (i * 4)) # 0xFF0000\nseq8 (clear 0) (sp 0) (sp 1) (sp 2) (sp 3) (src # R) (arg0 # 2) (arg1 # 2)\n")
same("List を引く描画", G + "boxes : bs ?\n\t||bs|| < 4 : 0\n\tseq2 (rect (bs ' 0) (bs ' 1) (bs ' 2) (bs ' 3) 0x00FF00) (boxes (bs ' 4~))\nseq3 (clear 0) (boxes [1 1 5 5 10 10 8 8 30 20 20 6]) (present 0)\n")
# 実際のゲーム: Suika を速い道あり・なしで比べる(短い台本)
def suika(pure):
    env = dict(os.environ); env["SIGN_NO_PURE"] = "0" if pure else "1"
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), "suika.sn", "--display=png:" + os.path.join(TMP, "s%d_{n}.png" % pure), "--timer=virtual",
                        "--input=300:kd:32,340:ku:32,700:kd:37,900:ku:37,1000:kd:32,1040:ku:32,1500:close"], capture_output=True, text=True, timeout=600, env=env, cwd=HERE)
    return r.returncode, r.stdout.strip()
a = suika(True); b = suika(False)
check("Suika の出力が同じ", a, b)
import glob, hashlib
fa = sorted(glob.glob(os.path.join(TMP, "s1_*.png"))); fb = sorted(glob.glob(os.path.join(TMP, "s0_*.png")))
check("Suika の画面(PNG)の枚数が同じ", len(fa), len(fb))
h = lambda fs: [hashlib.md5(open(f, "rb").read()).hexdigest() for f in fs]
check("Suika の画面(PNG)が全部同じ", h(fa), h(fb))
check("Suika の画面を 20 枚以上比べた", len(fa) >= 20, True)
print("\n全部 ok" if not bad else f"\n{bad} 件 NG"); sys.exit(1 if bad else 0)
