"""sign_realinput.py — `--real-dev` の入力装置(0x9300000)の中継ルーチン(AArch64 アセンブリ)。

処理系の Input 装置(sign_gfx.py の Input)と同じ番地の並びを、Linux の evdev(/dev/input/event0〜31)で動かす。
  base + 0x00 COUNT / 0x04 TYPE / 0x08 CODE / 0x0C EX / 0x10 EY(先頭の出来事)/ 0x14 POP(書くと先頭を捨てる)/ 0x20 MX / 0x24 MY / 0x28 MBTN /
  0x100 + 4*符号 = そのキーがいま押されていれば 1。種類は 1 キー押下 2 キー離す 3 マウス移動 4 マウス押下 5 マウス離す(6 閉じる は出ない)。
読み書きのたびに(処理系の poll と同じ)全 fd を O_NONBLOCK で空になるまで読み、出来事を 256 件の輪(あふれたら古い方を捨てる)へ入れる。
最初に触れた時に /dev/input/event0〜31 を O_RDONLY|O_NONBLOCK で開く(開けないもの = 権限が無い・無いは黙って飛ばす。input グループが要る。
開けたのが 0 個なら、出来事は来ず、COUNT は 0 のまま)。ENODEV(抜かれた)の fd は閉じて以後飛ばす。fd は最大 16 個。
変換(実装の決めで、仕様に定めは無い):
  - キー: EV_KEY の値 1(押す)と 0(離す)だけ。2(自動連打)は捨てる(処理系の Tk の窓は連打も KeyPress で出す = 違い)。
    Linux のキー符号 → Sign の符号は表 _sign_inmap(a〜z は 97〜122、数字 48〜57、記号 `- = [ ] ; ' ` \\ , . /`、Esc 27、Enter 13、Backspace 8、Tab 9、Space 32、
    左 0x1C 右 0x1D 上 0x1E 下 0x1F)。表に無いキー(Shift・Ctrl・F キー・テンキーなど)は捨てる。Shift を見ないので、文字は常に小文字(Tk の窓は大文字も出す = 違い)。
  - マウス: BTN_LEFT→1・BTN_MIDDLE→2・BTN_RIGHT→3 の押下・離す(位置はそのときの MX・MY)。相対移動(REL_X・REL_Y)は MX・MY に足し、
    0〜1919・0〜1079 に切る(画面の大きさを知らないので決め打ち)。SYN_REPORT で 1 回の「マウス移動」を出す。ホイール・絶対座標(タッチ)は無視。
  - 「閉じる」(6)は出ない。
これは実装の決めで、仕様に定めはない。実機では未実行(疑似カーネルで確認)。
"""

MAXX, MAXY = 1919, 1079
QOFF, KOFF, EVOFF, SIZE = 1024, 640, 256, 5120
# 状態 _sign_in: +0 初期化済み / +8 fd の数 / +16 fd[16] / +144 輪の先頭 / +152 件数 / +160 MX / +168 MY / +176 MBTN / +256 evbuf(384) / +640 キーの表(256 バイト) / +1024 輪(256 × 16)

LINUX2SIGN = {1: 27, 12: ord("-"), 13: ord("="), 14: 8, 15: 9, 26: ord("["), 27: ord("]"), 28: 13, 39: ord(";"), 40: ord("'"), 41: ord("`"), 43: ord("\\"),
              51: ord(","), 52: ord("."), 53: ord("/"), 57: 32, 103: 0x1E, 105: 0x1C, 106: 0x1D, 108: 0x1F}
for i, c in enumerate("1234567890"): LINUX2SIGN[2 + i] = ord(c)
for i, c in enumerate("qwertyuiop"): LINUX2SIGN[16 + i] = ord(c)
for i, c in enumerate("asdfghjkl"): LINUX2SIGN[30 + i] = ord(c)
for i, c in enumerate("zxcvbnm"): LINUX2SIGN[44 + i] = ord(c)


def _imm(reg, v):
    from sign_asm import emit_imm
    out = []; emit_imm(out, reg, v); return out


def _adr(reg, sym):
    return ["\tadrp %s, %s" % (reg, sym), "\tadd %s, %s, :lo12:%s" % (reg, reg, sym)]


def shim():
    L = []
    add = lambda *xs: L.extend(xs)
    add("// ===== 入力 (0x93…) =====", "")
    # 輪へ 1 件: x0 = 種類, x1 = 符号, x2 = x, x3 = y(x4〜x8 を使う)
    add("_sign_dev_ipush:")
    add(*_adr("x4", "_sign_in"))
    add("\tldr x5, [x4, #144]", "\tldr x6, [x4, #152]", "\tcmp x6, #256", "\tb.lo 1f", "\tadd x5, x5, #1", "\tand x5, x5, #255", "\tstr x5, [x4, #144]", "\tsub x6, x6, #1",
        "1:", "\tadd x7, x5, x6", "\tand x7, x7, #255", "\tadd x8, x4, #%d" % QOFF, "\tadd x8, x8, x7, lsl #4",
        "\tstr w0, [x8]", "\tstr w1, [x8, #4]", "\tstr w2, [x8, #8]", "\tstr w3, [x8, #12]", "\tadd x6, x6, #1", "\tstr x6, [x4, #152]", "\tret", "")
    # 先頭を捨てる
    add("_sign_dev_ipop:")
    add(*_adr("x4", "_sign_in"))
    add("\tldr x6, [x4, #152]", "\tcbz x6, 1f", "\tldr x5, [x4, #144]", "\tadd x5, x5, #1", "\tand x5, x5, #255", "\tstr x5, [x4, #144]", "\tsub x6, x6, #1", "\tstr x6, [x4, #152]", "1:", "\tret", "")
    # 読み: x0 = 領域の中の位置 → x0
    add("_sign_dev_iget:")
    add(*_adr("x15", "_sign_in"))
    add("\tcmp x0, #0x500", "\tb.hs 9f", "\tcmp x0, #0x100", "\tb.lo 1f", "\tsub x0, x0, #0x100", "\tlsr x0, x0, #2", "\tadd x1, x15, #%d" % KOFF, "\tldrb w0, [x1, x0]", "\tret",
        "1:", "\tldr x2, [x15, #152]", "\tcmp x0, #0", "\tb.ne 2f", "\tmov x0, x2", "\tret",
        "2:", "\tcmp x0, #0x20", "\tb.ne 3f", "\tldr x0, [x15, #160]", "\tret",
        "3:", "\tcmp x0, #0x24", "\tb.ne 4f", "\tldr x0, [x15, #168]", "\tret",
        "4:", "\tcmp x0, #0x28", "\tb.ne 5f", "\tldr x0, [x15, #176]", "\tret",
        "5:", "\tcbz x2, 9f", "\tldr x3, [x15, #144]", "\tadd x4, x15, #%d" % QOFF, "\tadd x4, x4, x3, lsl #4",
        "\tcmp x0, #4", "\tb.ne 6f", "\tldr w0, [x4]", "\tret",
        "6:", "\tcmp x0, #8", "\tb.ne 7f", "\tldr w0, [x4, #4]", "\tret",
        "7:", "\tcmp x0, #0xC", "\tb.ne 8f", "\tldr w0, [x4, #8]", "\tret",
        "8:", "\tcmp x0, #0x10", "\tb.ne 9f", "\tldr w0, [x4, #12]", "\tret",
        "9:", "\tmov x0, #0", "\tret", "")
    # 集める。枠: +16 パス(32 バイト)
    pre = int.from_bytes(b"/dev/inp", "little"), int.from_bytes(b"ut/event", "little")
    add("_sign_dev_ipoll:", "\tstp x29, x30, [sp, #-64]!", "\tmov x29, sp")
    add(*_adr("x15", "_sign_in"))
    add("\tldr x0, [x15]", "\tcbnz x0, 20f", "\tmov x0, #1", "\tstr x0, [x15]")
    add(*_imm("x5", pre[0])); add(*_imm("x6", pre[1]))
    add("\tmov x14, #0",
        "10:", "\tmov x1, #10", "\tudiv x2, x14, x1", "\tmsub x3, x2, x1, x14", "\tadd x4, sp, #16", "\tstr x5, [x4]", "\tstr x6, [x4, #8]", "\tcbz x2, 11f",
        "\tadd x2, x2, #48", "\tstrb w2, [x4, #16]", "\tadd x3, x3, #48", "\tstrb w3, [x4, #17]", "\tstrb wzr, [x4, #18]", "\tb 12f",
        "11:", "\tadd x3, x3, #48", "\tstrb w3, [x4, #16]", "\tstrb wzr, [x4, #17]",
        "12:", "\tmov x0, #-100", "\tmov x1, x4", "\tmov x2, #0x800", "\tmovk x2, #8, lsl #16", "\tmov x3, #0", "\tmov x8, #56", "\tsvc #0",     # O_RDONLY|O_NONBLOCK|O_CLOEXEC
        "\tcmp x0, #0", "\tb.lt 13f", "\tldr x1, [x15, #8]", "\tcmp x1, #16", "\tb.hs 14f", "\tadd x2, x15, #16", "\tlsl x3, x1, #3", "\tadd x2, x2, x3", "\tstr x0, [x2]",
        "\tadd x1, x1, #1", "\tstr x1, [x15, #8]", "\tb 13f",
        "14:", "\tmov x8, #57", "\tsvc #0",
        "13:", "\tadd x14, x14, #1", "\tcmp x14, #32", "\tb.ne 10b")
    add("20:", "\tmov x14, #0", "\tmov x11, #0",
        "21:", "\tldr x1, [x15, #8]", "\tcmp x14, x1", "\tb.hs 90f", "\tadd x2, x15, #16", "\tlsl x3, x14, #3", "\tadd x2, x2, x3", "\tldr x13, [x2]", "\tcmp x13, #0", "\tb.lt 29f",
        "22:", "\tmov x0, x13", "\tadd x1, x15, #%d" % EVOFF, "\tmov x2, #384", "\tmov x8, #63", "\tsvc #0", "\tcmp x0, #24", "\tb.ge 23f",
        "\tmov x4, #-19", "\tcmp x0, x4", "\tb.ne 29f", "\tmov x0, x13", "\tmov x8, #57", "\tsvc #0", "\tadd x2, x15, #16", "\tlsl x3, x14, #3", "\tadd x2, x2, x3", "\tmov x4, #-1", "\tstr x4, [x2]", "\tb 29f",
        "23:", "\tmov x12, x0", "\tadd x9, x15, #%d" % EVOFF,
        "24:", "\tldrh w4, [x9, #16]", "\tldrh w5, [x9, #18]", "\tldr w6, [x9, #20]", "\tlsl x6, x6, #32", "\tasr x6, x6, #32",
        "\tcmp x4, #1", "\tb.eq 30f", "\tcmp x4, #2", "\tb.eq 40f", "\tcbnz x4, 28f",
        "\tcbnz x5, 28f", "\tcbz x11, 28f", "\tmov x11, #0", "\tmov x0, #3", "\tmov x1, #0", "\tldr x2, [x15, #160]", "\tldr x3, [x15, #168]", "\tbl _sign_dev_ipush", "\tb 28f",
        # EV_KEY
        "30:", "\tcmp x6, #2", "\tb.eq 28f", "\tsub x7, x5, #0x110", "\tcmp x7, #3", "\tb.lo 35f", "\tcmp x5, #256", "\tb.hs 28f")
    add(*_adr("x7", "_sign_inmap"))
    add("\tldrb w7, [x7, x5]", "\tcbz x7, 28f", "\tadd x8, x15, #%d" % KOFF, "\tcmp x6, #0", "\tb.eq 31f", "\tmov x4, #1", "\tstrb w4, [x8, x7]", "\tmov x0, #1", "\tmov x1, x7", "\tmov x2, #0", "\tmov x3, #0", "\tbl _sign_dev_ipush", "\tb 28f",
        "31:", "\tstrb wzr, [x8, x7]", "\tmov x0, #2", "\tmov x1, x7", "\tmov x2, #0", "\tmov x3, #0", "\tbl _sign_dev_ipush", "\tb 28f",
        # マウスのボタン: x7 = 0 左 / 1 右 / 2 中 → Sign の 1 左 2 中 3 右
        "35:", "\tmov x0, #1", "\tmov x1, #3", "\tcmp x7, #0", "\tcsel x0, x0, x1, eq", "\tmov x1, #2", "\tcmp x7, #2", "\tcsel x0, x1, x0, eq",
        "\tsub x1, x0, #1", "\tmov x2, #1", "\tlsl x2, x2, x1", "\tldr x3, [x15, #176]", "\tcmp x6, #0", "\tb.eq 36f", "\torr x3, x3, x2", "\tmov x4, #4", "\tb 37f",
        "36:", "\tand x5, x3, x2", "\tsub x3, x3, x5", "\tmov x4, #5",
        "37:", "\tstr x3, [x15, #176]", "\tmov x1, x0", "\tmov x0, x4", "\tldr x2, [x15, #160]", "\tldr x3, [x15, #168]", "\tbl _sign_dev_ipush", "\tb 28f",
        # EV_REL
        "40:", "\tcmp x5, #0", "\tb.ne 41f", "\tldr x7, [x15, #160]", "\tadd x7, x7, x6", "\tcmp x7, #0", "\tcsel x7, xzr, x7, lt", "\tmov x8, #%d" % MAXX, "\tcmp x7, x8", "\tcsel x7, x8, x7, gt", "\tstr x7, [x15, #160]", "\tmov x11, #1", "\tb 28f",
        "41:", "\tcmp x5, #1", "\tb.ne 28f", "\tldr x7, [x15, #168]", "\tadd x7, x7, x6", "\tcmp x7, #0", "\tcsel x7, xzr, x7, lt", "\tmov x8, #%d" % MAXY, "\tcmp x7, x8", "\tcsel x7, x8, x7, gt", "\tstr x7, [x15, #168]", "\tmov x11, #1", "\tb 28f",
        "28:", "\tadd x9, x9, #24", "\tsub x12, x12, #24", "\tcmp x12, #24", "\tb.hs 24b", "\tb 22b",
        "29:", "\tadd x14, x14, #1", "\tb 21b",
        "90:", "\tldp x29, x30, [sp], #64", "\tret", "")
    return L


def data_lines():
    ro = ["\t.section .rodata", "_sign_inmap:", "\t.byte " + ", ".join(str(LINUX2SIGN.get(i, 0)) for i in range(256))]
    return ro, ["_sign_in:", "\t.skip %d" % SIZE]
