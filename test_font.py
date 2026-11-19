#!/usr/bin/env python3
"""文字フォント(font.sn と BLIT の型抜き)の試験。python test_font.py"""
import os, re, sys
sys.setrecursionlimit(20000); HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import sign_interp as S, sign_gfx as G

G_ = 0x9100000
FONT = os.path.join(HERE, "font.sn")
bad = 0
def check(name, got, want):
    global bad
    ok = got == want; bad += not ok
    print(("ok  " if ok else "NG  ") + name + ("" if ok else f"\n    得た: {got!r}\n    期待: {want!r}"))

def run(body, w=64, h=32):
    S.DEVICES.clear()
    d = G.Display(w, h, "null"); t = G.Timer(d, virtual=True); i = G.Input(t, ""); d.on_event = i.push
    S.DEVICES.extend([d, t, i]); S.MEMORY.clear(); S.IMPORT_STACK.clear()
    r = S.run(f"`{FONT}`@~\n" + body)
    return S.show(r[-1]), d
def rows(d, x, y, w=5, h=7, on=0xFFFFFF):          # 画面の一部を文字の絵にする
    return ["".join("#" if d.pix[(y + j) * d.w + x + i] == on else "." for i in range(w)) for j in range(h)]

# 字の表(font.sn の 35 ビットの数)を読む
src = open(FONT, encoding="utf-8").read()
TAB = {int(c): int(v, 16) for c, v in re.findall(r"\tc = (\d+) : 0x([0-9A-Fa-f]+)", src)}
check("字の表: 32〜126 の 95 字", sorted(TAB) == list(range(32, 127)), True)
def art(c): return ["".join("#" if (TAB[c] >> (34 - (5 * y + x))) & 1 else "." for x in range(5)) for y in range(7)]

r, d = run("font_char 65 1 1 1 0xFFFFFF")
check("A の形", rows(d, 1, 1), [".###.", "#...#", "#...#", "#####", "#...#", "#...#", "#...#"])
check("font_char は次の x(x+6)を返す", r, "7")
check("ほかの画素は触らない", (d.pix[0], d.pix[0 * 64 + 7]), (0, 0))
r, d = run("font_char 65 0 0 2 0xFF0000")
check("倍率 2: 返す x は 12", r, "12")
check("倍率 2: 最初の行(.###.)", ["#" if d.pix[0 * 64 + i] else "." for i in range(10)], list("..######.."))
check("倍率 2: 2 行ぶん同じ", [d.pix[1 * 64 + i] for i in range(10)], [d.pix[0 * 64 + i] for i in range(10)])
r, d = run("font_char 200 3 3 1 0xFFFFFF")
check("範囲外の番号: 何も描かず x+6", (r, sum(1 for p in d.pix if p)), ("9", 0))
r, d = run("font_char 32 3 3 1 0xFFFFFF")
check("空白: 何も描かず x+6", (r, sum(1 for p in d.pix if p)), ("9", 0))

# SCALE・FLIP が元に戻り、COLOR は引数の色になる
r, d = run(f"font_char 65 0 0 3 0xABCDEF\n(@{G_ + 0x30}) , (@{G_ + 0x34}) , (@{G_ + 0x08})")
check("描いた後: SCALE=1・FLIP=0・COLOR=引数", r, f"[1, 0, {0xABCDEF}]")

# 全 95 字を並べ、各字の画素数が表と合う
sheet = " ".join(f"(font_char {c} {1 + ((c - 32) % 10) * 6} {1 + ((c - 32) // 10) * 8} 1 0xFFFFFF)" for c in range(32, 127))
r, d = run("seq" + str(95) + " " + sheet, w=64, h=80)
ok = True
for c in range(32, 127):
    gx, gy = 1 + ((c - 32) % 10) * 6, 1 + ((c - 32) // 10) * 8
    if rows(d, gx, gy) != art(c): ok = False; print("  不一致:", c, chr(c))
check("全 95 字が表どおりに描ける", ok, True)

# 文字列
r, d = run("seq2 (str_put 0x600000 `Hi`) (font_text 0x600000 2 3 1 0x00FF00)")
check("font_text: 'Hi' を描き、次の x を返す", (r, rows(d, 2, 3, 5, 7, 0x00FF00) == art(72), rows(d, 8, 3, 5, 7, 0x00FF00) == art(105)), ("14", True, True))
r, d = run("font_print `AB` 1 1 1 0xFFFFFF")
check("font_print(Sign の文字列)", (r, rows(d, 1, 1) == art(65), rows(d, 7, 1) == art(66)), ("13", True, True))
r, d = run("font_int 305 0 0 1 0xFFFFFF")
check("font_int: 3 桁", (r, [rows(d, 6 * k, 0) == art(48 + n) for k, n in enumerate((3, 0, 5))]), ("18", [True, True, True]))
r, d = run("font_int (0 - 7) 0 0 1 0xFFFFFF")
check("font_int: 負の数は '-' から", (rows(d, 0, 0) == art(45), rows(d, 6, 0) == art(55)), (True, True))
# 改行(10)
r, d = run("seq5 (0x600000 # 65) (0x600004 # 10) (0x600008 # 66) (0x60000C # 0) (font_text 0x600000 2 2 1 0xFFFFFF)")
check("font_text: 改行で x を戻して 8 画素下へ", (rows(d, 2, 2) == art(65), rows(d, 2, 10) == art(66), r), (True, True, "8"))
r, d = run("seq2 (str_put 0x600000 `abc`) (font_width 0x600000 1)")
check("font_width: 3 文字 = 17", r, "17")
r, d = run("seq2 (str_put 0x600000 `abc`) (font_width 0x600000 3)")
check("font_width: 倍率 3 = 51", r, "51")

# 画面の端(はみ出しは捨てる)
r, d = run("font_char 65 61 29 1 0xFFFFFF")
check("はみ出しは捨てる(落ちない)", (d.pix[29 * 64 + 62], d.pix[29 * 64 + 63]), (0xFFFFFF, 0xFFFFFF))

# BLIT の型抜き(FLIP ビット 2)
S.DEVICES.clear(); S.MEMORY.clear()
d = G.Display(6, 3, "null"); S.DEVICES.append(d)
src = "".join(f"i{k} : {0x600000 + 4 * k} # {v}\n" for k, v in enumerate([5, 0, -1, 0x123456, None, 1])) + \
      f"a : {G_ + 8} # 0x00FF00\nb : {G_ + 0x28} # {0x600000}\nc : {G_ + 0x18} # 3\ne : {G_ + 0x1C} # 2\nf : {G_ + 0x34} # 4\ng : {G_ + 0x14} # 6\n@{G_ + 0x20}"
r = S.show(S.run(src)[-1])
check("型抜き: 0 でない語は COLOR、0・負・未書き込みは透明", ([d.pix[i] for i in range(3)], [d.pix[6 + i] for i in range(3)], r), ([0x00FF00, 0, 0], [0x00FF00, 0, 0x00FF00], "0"))
d.pix[:] = [0] * 18
src2 = src.replace(f"f : {G_ + 0x34} # 4", f"f : {G_ + 0x34} # 5")
S.MEMORY.clear(); S.run(src2)
check("型抜き + 左右反転", ([d.pix[i] for i in range(3)], [d.pix[6 + i] for i in range(3)]), ([0, 0, 0x00FF00], [0x00FF00, 0, 0x00FF00]))
print(f"\n{'全部 ok' if not bad else str(bad) + ' 件 NG'}"); sys.exit(1 if bad else 0)
