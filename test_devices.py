#!/usr/bin/env python3
"""装置(sign_gfx.py)の試験: 描画・タイマー・入力のレジスタを Sign から番地で触る。python test_devices.py"""
import os, sys
sys.setrecursionlimit(20000); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sign_interp as S, sign_gfx as G

def run(src, script="", w=8, h=4):
    S.DEVICES.clear()
    d = G.Display(w, h, "null"); t = G.Timer(d, virtual=True); i = G.Input(t, script); d.on_event = i.push
    S.DEVICES.extend([d, t, i]); S.MEMORY.clear()
    return S.show(S.run(src)[-1]), d, t, i

G_, T_, I_ = 0x9100000, 0x9200000, 0x9300000
bad = 0
def check(name, got, want):
    global bad
    ok = got == want; bad += not ok
    print(("ok  " if ok else "NG  ") + name + ("" if ok else f"  got {got!r} want {want!r}"))

check("幅と高さ", run(f"(@{G_ + 0}) , (@{G_ + 4})")[0], "[8, 4]")
check("PLOT の画素を直に読む", run(f"a : {G_ + 8} # 0xABCDEF\nb : {G_ + 12} # 3\nc : {G_ + 16} # 2\nd : {G_ + 20} # 1\n@{G_ + 0x1000 + 4 * (2 * 8 + 3)}")[0], str(0xABCDEF))
check("CLEAR", run(f"a : {G_ + 8} # 0x112233\nb : {G_ + 20} # 2\n@{G_ + 0x1000 + 4 * 31}")[0], str(0x112233))
check("範囲外は STATUS=1", run(f"a : {G_ + 12} # 99\nb : {G_ + 20} # 1\n@{G_ + 0x20}")[0], "1")
check("知らない命令は STATUS=2", run(f"a : {G_ + 20} # 77\n@{G_ + 0x20}")[0], "2")
r, d, *_ = run(f"a : {G_ + 8} # 0xFFFFFF\nb : {G_ + 12} # 0\nc : {G_ + 16} # 0\nd : {G_ + 24} # 7\ne : {G_ + 28} # 3\nf : {G_ + 20} # 4\n0")
check("LINE の端", (d.pix[0], d.pix[3 * 8 + 7]), (0xFFFFFF, 0xFFFFFF))
check("SLEEP は仮想時計を進める", run(f"a : {T_ + 4} # 120\nb : {T_ + 4} # 30\n@{T_}")[0], "150")
check("負の SLEEP は無視", run(f"a : {T_ + 4} # 0 - 5\n@{T_}")[0], "0")
check("入力: 時刻前は空", run(f"@{I_}", "100:kd:97")[0], "0")
check("入力: 時刻が来ると届く", run(f"a : {T_ + 4} # 100\n(@{I_ + 4}) , (@{I_ + 8})", "100:kd:a")[0], "[1, 97]")
check("入力: POP で先頭が進む", run(f"a : {T_ + 4} # 100\nb : {I_ + 20} # 0\n@{I_ + 8}", "10:kd:a,20:kd:b")[0], "98")
check("入力: キーの押下状態", run(f"a : {T_ + 4} # 100\n@{I_ + 0x100 + 4 * 97}", "10:kd:a")[0], "1")
check("入力: 離すと 0", run(f"a : {T_ + 4} # 100\n@{I_ + 0x100 + 4 * 97}", "10:kd:a,20:ku:a")[0], "0")
check("入力: マウスの位置とボタン", run(f"a : {T_ + 4} # 100\n(@{I_ + 0x20}) , (@{I_ + 0x24}) , (@{I_ + 0x28})", "10:md:1:5:2")[0], "[5, 2, 1]")
check("入力: 閉じる", run(f"a : {T_ + 4} # 100\n@{I_ + 4}", "10:close")[0], "6")
import subprocess, tempfile, os
def uart(src, data):
    with tempfile.NamedTemporaryFile("w", suffix=".sn", delete=False, encoding="utf-8") as f: f.write(src); n = f.name
    try: return subprocess.run([sys.executable, os.path.join(os.path.dirname(os.path.abspath(__file__)), "sign.py"), n], input=data, capture_output=True, timeout=60).stdout.decode("utf-8", "replace")
    finally: os.unlink(n)
check("UART: 標準入力を 1 バイト読む", uart("@0x9000000", b"A").strip(), "65")
check("UART: 続けて読むと次のバイト", uart("(@0x9000000) , (@0x9000000)", b"AB").strip(), "[65, 66]")
check("UART: 入力の終わりは __", uart("@0x9000000", b"").strip(), "__")
check("UART: echo.sn は入力をそのまま返す", uart(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "echo.sn"), encoding="utf-8").read(), b"hi\n").split("\n")[0], "hi")
# --- BLIT(スプライト) ---
IMG = 0x600000
def img(words, base=IMG):
    return "".join(f"i{k} : {base + 4 * k} # {v}\n" for k, v in enumerate(words) if v is not None)
def blit(words, w, h, x, y, extra="", dw=8, dh=6):
    src = img(words) + f"s0 : {G_ + 0x28} # {IMG}\ns1 : {G_ + 0x18} # {w}\ns2 : {G_ + 0x1C} # {h}\ns3 : {G_ + 0x0C} # {x}\ns4 : {G_ + 16} # {y}\n" + extra + f"s9 : {G_ + 0x14} # 6\n@{G_ + 0x20}"
    r, d, *_ = run(src, w=dw, h=dh)
    return r, d
A, B, C, D, F = 0xAA0000, 0x00BB00, 0x0000CC, 0xDD00DD, 0xFFFF00
r, d = blit([A, B, C, D, None, F], 3, 2, 2, 1)
check("BLIT: 絵が (X,Y) に出る", (d.pix[1 * 8 + 2], d.pix[1 * 8 + 3], d.pix[1 * 8 + 4], d.pix[2 * 8 + 2], d.pix[2 * 8 + 4]), (A, B, C, D, F))
check("BLIT: 未書き込みの語は透明(下の画素が残る)", (d.pix[2 * 8 + 3], r), (0, "0"))
r, d = blit([A, B, C, D, 0x123456, F], 3, 2, 0, 0, extra=f"t : {G_ + 0x2C} # {0x123456}\n")
check("BLIT: TRANS の色は透明", d.pix[1 * 8 + 1], 0)
r, d = blit([A, -1, C, D, 5, F], 3, 2, 0, 0)
check("BLIT: 負の語は透明", (d.pix[1], d.pix[1 * 8 + 1]), (0, 5))
r, d = blit([A, B, C, D, 5, F], 3, 2, 0, 0, extra=f"f : {G_ + 0x34} # 1\n")
check("BLIT: 左右反転", (d.pix[0], d.pix[2], d.pix[1 * 8 + 0], d.pix[1 * 8 + 2]), (C, A, F, D))
r, d = blit([A, B, C, D, 5, F], 3, 2, 0, 0, extra=f"f : {G_ + 0x34} # 2\n")
check("BLIT: 上下反転", (d.pix[0], d.pix[2], d.pix[1 * 8 + 0], d.pix[1 * 8 + 2]), (D, F, A, C))
r, d = blit([A, B, C, D, 5, F], 3, 2, 0, 0, extra=f"f : {G_ + 0x34} # 3\n")
check("BLIT: 上下と左右", (d.pix[0], d.pix[1 * 8 + 2]), (F, A))
r, d = blit([A, B, C, D, 5, F], 3, 2, 1, 1, extra=f"z : {G_ + 0x30} # 2\n", dw=10, dh=8)
check("BLIT: 拡大(2×2 の四角)", (d.pix[1 * 10 + 1], d.pix[1 * 10 + 2], d.pix[2 * 10 + 2], d.pix[1 * 10 + 3], d.pix[3 * 10 + 1], d.pix[3 * 10 + 4], d.pix[4 * 10 + 5]), (A, A, A, B, D, 5, F))
r, d = blit([A, B, C, D, 5, F], 3, 2, 6, 4)
check("BLIT: はみ出しは捨てて STATUS=1", (d.pix[4 * 8 + 6], d.pix[4 * 8 + 7], r), (A, B, "1"))
r, d = blit([A, B, C, D, 5, F], 3, 2, -1, -1)
check("BLIT: 左上へはみ出し", (d.pix[0], d.pix[1], r), (5, F, "1"))
r, d = blit([A, B], 0, 2, 0, 0)
check("BLIT: 幅 0 は何もせず STATUS=1", (d.pix[0], r), (0, "1"))
r, d = blit([A], 300, 300, 0, 0)
check("BLIT: 大きすぎる絵は何もしない", (d.pix[0], r), (0, "1"))
r, d = blit([0x1FFFFFF, B, C, D, 5, F], 3, 2, 0, 0)
check("BLIT: 色は 24 ビットに丸める", d.pix[0], 0xFFFFFF)
print("\n" + ("全部通った" if not bad else f"{bad} 件 食い違い")); sys.exit(1 if bad else 0)
