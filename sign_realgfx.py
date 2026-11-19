"""sign_realgfx.py — `--real-dev` の描画装置(0x9100000)の中継ルーチン(AArch64 アセンブリ)。

処理系の Display(sign_gfx.py)と同じ番地の並び(WIDTH HEIGHT COLOR X Y CMD ARG0 ARG1 STATUS FRAME SRC TRANS SCALE FLIP と 0x1000 からの画素)・同じ命令
(PLOT CLEAR PRESENT LINE RECT BLIT)を、**論理画面**(既定 64×32。`--display=幅x高さ`)を .bss に持って描き、PRESENT で Linux の fbdev(/dev/fb0)へ出す。
  - 画素は 1 画素 1 語(4 バイト、0xRRGGBB)。範囲外は黙って捨てて STATUS=1(処理系と同じ)。
  - PRESENT: 最初の 1 回で /dev/fb0 を O_RDWR で開き、FBIOGET_VSCREENINFO・FBIOGET_FSCREENINFO を聞いて mmap し、全面を黒にする。
    論理画面を、画面に収まる最大の整数倍(1 以上)に拡大し、中央に置く(処理系の window[:倍率] と同じ考え方)。色は fb のビット配置(32 ビットと 16 ビット)に詰める。
    開けない・対応しない形式(24 ビットなど)なら、1 度だけ標準エラーに知らせて、以後の PRESENT は何もしない(画素は読み書きできる)。FBIOPAN_DISPLAY・同期待ちはしない。
  - 実装の決め(処理系との違い): ① 未書き込みの語を読むと 0(処理系は __)。BLIT の絵では、**値 0 の語は透明**(処理系は未書き込みの語だけ透明で、書いた 0 = 黒は黒。こちらは両者を区別できないので、
    sprite_demo.sn のように「置かなかった語 = 透明」の絵が処理系と同じに見えるほうを取った)。黒を描きたいときは 0x010101 のように 0 でない色にする。
    ② BLIT の絵の番地が Sign のメモリの外(0x10000 未満・0x9000000 を越える)なら STATUS=1 で何もしない(処理系は透明として読む)。
    ③ 入力の「閉じる」は出ない。④ 画面の更新はコンソール(tty)で見える。Wayland・X のデスクトップが /dev/fb0 を握っていると見えない。video グループが要る。
実機では未実行(疑似カーネルで確認)。"""

STATE = 256
# 状態 _sign_gfx(8 バイトの項): 0 初期化済み / 8 COLOR / 16 X / 24 Y / 32 ARG0 / 40 ARG1 / 48 STATUS / 56 FRAME / 64 SRC / 72 TRANS(-1 = 無し) / 80 SCALE / 88 FLIP /
#   96 fd / 104 mmap / 112 xres / 120 yres / 128 line_length / 136 bpp / 144 roff 152 rlen 160 goff 168 glen 176 boff 184 blen / 192 smem_len / 200 状態(0 まだ 1 使える 2 だめ) / 208 toff 216 tlen
ERR = "エラー: /dev/fb0 が使えません(開けない・24 ビットなど未対応の形式・権限は video グループ)。画面への出力は行いません(描画の読み書きはできます)\n"


def _adr(reg, sym):
    return ["\tadrp %s, %s" % (reg, sym), "\tadd %s, %s, :lo12:%s" % (reg, reg, sym)]


def shim(W, H):
    L = []
    add = lambda *xs: L.extend(xs)
    n = W * H
    add("// ===== 描画 (0x91…) 論理画面 %d x %d =====" % (W, H), "")
    # 初期化(最初に触れたとき): x15 = 状態の番地 を返す
    add("_sign_dev_ginit:")
    add(*_adr("x15", "_sign_gfx"))
    add("\tldr x2, [x15]", "\tcbnz x2, 1f", "\tmov x2, #1", "\tstr x2, [x15]", "\tmov x2, #0xFFFF", "\tmovk x2, #0xFF, lsl #16", "\tstr x2, [x15, #8]", "\tmov x2, #-1", "\tstr x2, [x15, #72]", "1:", "\tret", "")
    # 点 (x0, x1) に x2。範囲外は STATUS=1。x3〜x7 を使う
    add("_sign_dev_gput:", "\tmov x3, #%d" % W, "\tcmp x0, x3", "\tb.hs 1f", "\tmov x4, #%d" % H, "\tcmp x1, x4", "\tb.hs 1f",
        "\tmul x4, x1, x3", "\tadd x4, x4, x0", "\tlsl x4, x4, #2")
    add(*_adr("x5", "_sign_gpix"))
    add("\tstr w2, [x5, x4]", "\tret", "1:")
    add(*_adr("x6", "_sign_gfx"))
    add("\tmov x7, #1", "\tstr x7, [x6, #48]", "\tret", "")
    # 書き: x0 = 領域の中の位置, x1 = 値
    add("_sign_dev_gst:", "\tstp x29, x30, [sp, #-32]!", "\tmov x29, sp", "\tstr x0, [sp, #16]", "\tstr x1, [sp, #24]", "\tbl _sign_dev_ginit", "\tldr x0, [sp, #16]", "\tldr x1, [sp, #24]",
        "\tcmp x0, #0x1000", "\tb.lo 2f", "\tsub x2, x0, #0x1000", "\tlsr x2, x2, #2", "\tmov x3, #%d" % (n & 0xFFFF))
    if n > 0xFFFF: add("\tmovk x3, #%d, lsl #16" % (n >> 16))
    add("\tcmp x2, x3", "\tb.hs 9f", "\tand x1, x1, #0xFFFFFF", "\tlsl x2, x2, #2")
    add(*_adr("x3", "_sign_gpix"))
    add("\tstr w1, [x3, x2]", "\tb 9f", "2:", "\tcmp x0, #0x14", "\tb.ne 3f", "\tmov x0, x1", "\tbl _sign_dev_gcmd", "\tb 9f", "3:")
    for off, slot in ((8, 8), (0xC, 16), (0x10, 24), (0x18, 32), (0x1C, 40), (0x28, 64), (0x2C, 72), (0x30, 80), (0x34, 88)):
        add("\tcmp x0, #%d" % off, "\tb.ne 4f", "\tmov x3, #%d" % slot, "\tb 5f", "4:")
    add("\tb 9f", "5:", "\tcmp x3, #8", "\tb.ne 6f", "\tand x1, x1, #0xFFFFFF", "6:", "\tstr x1, [x15, x3]", "9:", "\tldp x29, x30, [sp], #32", "\tret", "")
    # 読み: x0 = 領域の中の位置 → x0
    add("_sign_dev_gld:", "\tstp x29, x30, [sp, #-32]!", "\tmov x29, sp", "\tstr x0, [sp, #16]", "\tbl _sign_dev_ginit", "\tldr x0, [sp, #16]",
        "\tcmp x0, #0x1000", "\tb.lo 2f", "\tsub x2, x0, #0x1000", "\tlsr x2, x2, #2", "\tmov x3, #%d" % (n & 0xFFFF))
    if n > 0xFFFF: add("\tmovk x3, #%d, lsl #16" % (n >> 16))
    add("\tcmp x2, x3", "\tb.hs 8f", "\tlsl x2, x2, #2")
    add(*_adr("x3", "_sign_gpix"))
    add("\tldr w0, [x3, x2]", "\tb 9f", "2:", "\tcmp x0, #0", "\tb.ne 3f", "\tmov x0, #%d" % W, "\tb 9f", "3:", "\tcmp x0, #4", "\tb.ne 4f", "\tmov x0, #%d" % H, "\tb 9f", "4:")
    for off, slot in ((8, 8), (0xC, 16), (0x10, 24), (0x18, 32), (0x1C, 40), (0x20, 48), (0x24, 56), (0x28, 64), (0x2C, 72), (0x30, 80), (0x34, 88)):
        add("\tcmp x0, #%d" % off, "\tb.ne 5f", "\tldr x0, [x15, #%d]" % slot, "\tb 9f", "5:")
    add("8:", "\tmov x0, #0", "9:", "\tldp x29, x30, [sp], #32", "\tret", "")
    # 命令。x0 = 命令。x10 X, x11 Y, x12 COLOR, x13 ARG0, x14 ARG1, x15 状態。枠: +16 dx +24 dy +32 sx +40 sy +48 err
    add("_sign_dev_gcmd:", "\tstp x29, x30, [sp, #-80]!", "\tmov x29, sp", "\tstp x16, x17, [sp, #64]")
    add(*_adr("x15", "_sign_gfx"))
    add("\tstr xzr, [x15, #48]", "\tldr x10, [x15, #16]", "\tldr x11, [x15, #24]", "\tldr x12, [x15, #8]", "\tldr x13, [x15, #32]", "\tldr x14, [x15, #40]")
    for c, lab in ((1, "plot"), (2, "clear"), (3, "present"), (4, "line"), (5, "rect"), (6, "blit")):
        add("\tcmp x0, #%d" % c, "\tb.eq .Lg_%s" % lab)
    add("\tmov x0, #2", "\tstr x0, [x15, #48]", ".Lg_ret:", "\tldp x16, x17, [sp, #64]", "\tldp x29, x30, [sp], #80", "\tret")
    add(".Lg_plot:", "\tmov x0, x10", "\tmov x1, x11", "\tmov x2, x12", "\tbl _sign_dev_gput", "\tb .Lg_ret")
    add(".Lg_clear:", "\tmov x1, #%d" % (n & 0xFFFF))
    if n > 0xFFFF: add("\tmovk x1, #%d, lsl #16" % (n >> 16))
    add(*_adr("x2", "_sign_gpix"))
    add("1:", "\tsub x1, x1, #1", "\tlsl x3, x1, #2", "\tstr w12, [x2, x3]", "\tcbnz x1, 1b", "\tb .Lg_ret")
    add(".Lg_present:", "\tldr x0, [x15, #56]", "\tadd x0, x0, #1", "\tstr x0, [x15, #56]", "\tbl _sign_dev_gpresent", "\tb .Lg_ret")
    # LINE(Bresenham。処理系と同じ手順)
    add(".Lg_line:", "\tsub x3, x13, x10", "\tneg x3, x3", "\tsub x4, x13, x10", "\tcmp x4, #0", "\tcsel x3, x4, x3, gt",                       # |a0 - x|: x4 が正ならそのまま、そうでなければ x3 = -x4 に
        "\tstr x3, [sp, #16]",                                                                                                                    # dx
        "\tsub x3, x14, x11", "\tneg x3, x3", "\tsub x4, x14, x11", "\tcmp x4, #0", "\tcsel x3, x4, x3, gt", "\tneg x3, x3", "\tstr x3, [sp, #24]",    # dy = -|a1 - y|
        "\tmov x3, #1", "\tmov x4, #-1", "\tcmp x10, x13", "\tcsel x5, x3, x4, lt", "\tstr x5, [sp, #32]", "\tcmp x11, x14", "\tcsel x5, x3, x4, lt", "\tstr x5, [sp, #40]",
        "\tldr x3, [sp, #16]", "\tldr x4, [sp, #24]", "\tadd x3, x3, x4", "\tstr x3, [sp, #48]",
        "1:", "\tmov x0, x10", "\tmov x1, x11", "\tmov x2, x12", "\tbl _sign_dev_gput",
        "\tcmp x10, x13", "\tb.ne 2f", "\tcmp x11, x14", "\tb.eq .Lg_ret",
        "2:", "\tldr x3, [sp, #48]", "\tlsl x3, x3, #1", "\tldr x4, [sp, #24]", "\tldr x5, [sp, #16]", "\tldr x6, [sp, #48]",
        "\tcmp x3, x4", "\tb.lt 3f", "\tadd x6, x6, x4", "\tldr x7, [sp, #32]", "\tadd x10, x10, x7",
        "3:", "\tcmp x3, x5", "\tb.gt 4f", "\tadd x6, x6, x5", "\tldr x7, [sp, #40]", "\tadd x11, x11, x7",
        "4:", "\tstr x6, [sp, #48]", "\tb 1b")
    # RECT
    add(".Lg_rect:", "\tcmp x13, #0", "\tb.le .Lg_ret", "\tcmp x14, #0", "\tb.le .Lg_ret",
        "\tcmp x10, #0", "\tcsel x2, x10, xzr, gt", "\tadd x3, x10, x13", "\tmov x4, #%d" % W, "\tcmp x3, x4", "\tcsel x3, x3, x4, lt",
        "\tcmp x11, #0", "\tcsel x5, x11, xzr, gt", "\tadd x6, x11, x14", "\tmov x7, #%d" % H, "\tcmp x6, x7", "\tcsel x6, x6, x7, lt",
        "\tadd x8, x10, x13", "\tcmp x2, x10", "\tb.ne 1f", "\tcmp x3, x8", "\tb.ne 1f", "\tadd x8, x11, x14", "\tcmp x5, x11", "\tb.ne 1f", "\tcmp x6, x8", "\tb.eq 2f",
        "1:", "\tmov x8, #1", "\tstr x8, [x15, #48]",
        "2:", "\tcmp x2, x3", "\tb.ge .Lg_ret", "\tcmp x5, x6", "\tb.ge .Lg_ret")
    add(*_adr("x9", "_sign_gpix"))
    add("3:", "\tmov x7, #%d" % W, "\tmul x7, x5, x7", "\tmov x8, x2",
        "4:", "\tadd x0, x7, x8", "\tlsl x0, x0, #2", "\tstr w12, [x9, x0]", "\tadd x8, x8, #1", "\tcmp x8, x3", "\tb.lt 4b",
        "\tadd x5, x5, #1", "\tcmp x5, x6", "\tb.lt 3b", "\tb .Lg_ret")
    # BLIT。x16 行, x17 列
    add(".Lg_blit:", "\tcmp x13, #0", "\tb.le 8f", "\tcmp x14, #0", "\tb.le 8f", "\tmul x2, x13, x14", "\tmov x3, #0x10000", "\tcmp x2, x3", "\tb.hi 8f",
        "\tldr x3, [x15, #80]", "\tcmp x3, #0", "\tmov x4, #1", "\tcsel x3, x4, x3, eq", "\tstr x3, [sp, #16]", "\tcmp x3, #1", "\tb.lt 8f", "\tcmp x3, #64", "\tb.gt 8f",
        "\tldr x3, [x15, #64]", "\tmov x4, #0x10000", "\tcmp x3, x4", "\tb.lt 8f", "\tlsl x2, x2, #2", "\tadd x2, x2, x3", "\tmov x4, #0x9000000", "\tcmp x2, x4", "\tb.hi 8f",
        "\tmov x16, #0",
        "1:", "\tcmp x16, x14", "\tb.ge .Lg_ret", "\tmov x17, #0",
        "2:", "\tcmp x17, x13", "\tb.ge 7f",
        "\tldr x2, [x15, #88]", "\tsub x3, x14, #1", "\tsub x3, x3, x16", "\tand x4, x2, #2", "\tcmp x4, #0", "\tcsel x4, x3, x16, ne",
        "\tsub x5, x13, #1", "\tsub x5, x5, x17", "\tand x6, x2, #1", "\tcmp x6, #0", "\tcsel x5, x5, x17, ne",
        "\tmul x4, x4, x13", "\tadd x4, x4, x5", "\tlsl x4, x4, #2", "\tldr x7, [x15, #64]", "\tadd x7, x7, x4", "\tldr w6, [x7]",
        "\tcbz x6, 6f", "\tldr x3, [x15, #72]", "\tcmp x6, x3", "\tb.eq 6f", "\tand x4, x2, #4", "\tcbz x4, 3f", "\tmov x6, x12",
        "3:", "\tand x6, x6, #0xFFFFFF", "\tldr x3, [sp, #16]",
        "\tmul x4, x17, x3", "\tadd x4, x4, x10", "\tmul x5, x16, x3", "\tadd x5, x5, x11", "\tmov x7, #0",
        "4:", "\tcmp x7, x3", "\tb.ge 6f", "\tmov x2, #0",
        "5:", "\tcmp x2, x3", "\tb.ge 9f", "\tadd x0, x4, x2", "\tadd x1, x5, x7", "\tmov x8, #%d" % W, "\tcmp x0, x8", "\tb.hs 10f", "\tmov x8, #%d" % H, "\tcmp x1, x8", "\tb.hs 10f",
        "\tmov x8, #%d" % W, "\tmul x8, x1, x8", "\tadd x8, x8, x0", "\tlsl x8, x8, #2")
    add(*_adr("x9", "_sign_gpix"))
    add("\tstr w6, [x9, x8]", "\tb 11f", "10:", "\tmov x8, #1", "\tstr x8, [x15, #48]", "11:", "\tadd x2, x2, #1", "\tb 5b",
        "9:", "\tadd x7, x7, #1", "\tb 4b",
        "6:", "\tadd x17, x17, #1", "\tb 2b",
        "7:", "\tadd x16, x16, #1", "\tb 1b",
        "8:", "\tmov x0, #1", "\tstr x0, [x15, #48]", "\tb .Lg_ret", "")
    # PRESENT → /dev/fb0。枠: +16 vinfo(160) +176 finfo(80)
    add("_sign_dev_gpresent:", "\tstp x29, x30, [sp, #-272]!", "\tmov x29, sp")
    add(*_adr("x15", "_sign_gfx"))
    add("\tldr x0, [x15, #200]", "\tcmp x0, #1", "\tb.eq .Lgp_draw", "\tcmp x0, #2", "\tb.eq .Lgp_ret",
        "\tmov x0, #-100")
    add(*_adr("x1", "_sign_gfx_path"))
    add("\tmov x2, #2", "\tmovk x2, #8, lsl #16", "\tmov x3, #0", "\tmov x8, #56", "\tsvc #0", "\tcmp x0, #0", "\tb.lt .Lgp_fail", "\tstr x0, [x15, #96]",
        "\tmov x1, #0x4600", "\tadd x2, sp, #16", "\tmov x8, #29", "\tsvc #0", "\tcmp x0, #0", "\tb.lt .Lgp_fail",
        "\tldr x0, [x15, #96]", "\tmov x1, #0x4602", "\tadd x2, sp, #176", "\tmov x8, #29", "\tsvc #0", "\tcmp x0, #0", "\tb.lt .Lgp_fail",
        "\tldr w3, [sp, #40]", "\tcmp x3, #32", "\tb.eq 1f", "\tcmp x3, #16", "\tb.ne .Lgp_fail", "1:", "\tstr x3, [x15, #136]",
        "\tldr w1, [sp, #16]", "\tstr x1, [x15, #112]", "\tldr w1, [sp, #20]", "\tstr x1, [x15, #120]", "\tldr w1, [sp, #224]", "\tstr x1, [x15, #128]", "\tldr w1, [sp, #200]", "\tstr x1, [x15, #192]")
    for src, slot in ((48, 144), (52, 152), (60, 160), (64, 168), (72, 176), (76, 184), (84, 208), (88, 216)):
        add("\tldr w1, [sp, #%d]" % src, "\tstr x1, [x15, #%d]" % slot)
    add("\tmov x0, #0", "\tldr x1, [x15, #192]", "\tmov x2, #3", "\tmov x3, #1", "\tldr x4, [x15, #96]", "\tmov x5, #0", "\tmov x8, #222", "\tsvc #0",
        "\tmov x1, #-4096", "\tcmp x0, x1", "\tb.hi .Lgp_fail", "\tstr x0, [x15, #104]",
        "\tldr x1, [x15, #192]", "\tlsr x1, x1, #3", "\tmov x2, x0", "2:", "\tcbz x1, 3f", "\tstr xzr, [x2]", "\tadd x2, x2, #8", "\tsub x1, x1, #1", "\tb 2b",
        "3:", "\tmov x0, #1", "\tstr x0, [x15, #200]", "\tb .Lgp_draw",
        ".Lgp_fail:", "\tmov x0, #2", "\tstr x0, [x15, #200]", "\tmov x0, #2")
    add(*_adr("x1", "_sign_gfx_err"))
    add("\tmov x2, #%d" % len(ERR.encode("utf-8")), "\tmov x8, #64", "\tsvc #0", ".Lgp_ret:", "\tldp x29, x30, [sp], #272", "\tret",
        ".Lgp_draw:",
        # 倍率 s = min(xres / W, yres / H)(1 以上)。ox, oy は中央
        "\tldr x1, [x15, #112]", "\tmov x2, #%d" % W, "\tudiv x11, x1, x2", "\tldr x1, [x15, #120]", "\tmov x2, #%d" % H, "\tudiv x3, x1, x2", "\tcmp x3, x11", "\tcsel x11, x3, x11, lo",
        "\tcmp x11, #1", "\tmov x3, #1", "\tcsel x11, x3, x11, lo",
        "\tldr x1, [x15, #112]", "\tmov x2, #%d" % W, "\tmul x2, x2, x11", "\tsub x1, x1, x2", "\tcmp x1, #0", "\tcsel x1, x1, xzr, gt", "\tlsr x9, x1, #1",
        "\tldr x1, [x15, #120]", "\tmov x2, #%d" % H, "\tmul x2, x2, x11", "\tsub x1, x1, x2", "\tcmp x1, #0", "\tcsel x1, x1, xzr, gt", "\tlsr x1, x1, #1", "\tstr x1, [sp, #264]",
        "\tldr x10, [x15, #136]", "\tlsr x10, x10, #3", "\tldr x16, [x15, #128]", "\tldr x17, [x15, #104]", "\tmov x14, #0",
        "5:", "\tmov x13, #0",
        "6:", "\tmov x0, #%d" % W, "\tmul x0, x14, x0", "\tadd x0, x0, x13", "\tlsl x0, x0, #2")
    add(*_adr("x1", "_sign_gpix"))
    add("\tldr w0, [x1, x0]")
    # 色を fb の並びへ(R・G・B それぞれ 上位 len ビットを off へ。alpha があれば 0xFF)
    add("\tmov x12, #0")
    for sh, lslot, oslot in ((16, 152, 144), (8, 168, 160), (0, 184, 176)):
        add("\tlsr x1, x0, #%d" % sh, "\tand x1, x1, #255", "\tldr x2, [x15, #%d]" % lslot, "\tmov x3, #8", "\tsub x3, x3, x2", "\tlsr x1, x1, x3", "\tldr x2, [x15, #%d]" % oslot, "\tlsl x1, x1, x2", "\torr x12, x12, x1")
    add("\tldr x2, [x15, #216]", "\tcmp x2, #8", "\tb.ne 7f", "\tmov x1, #255", "\tldr x2, [x15, #208]", "\tlsl x1, x1, x2", "\torr x12, x12, x1", "7:",
        "\tmov x7, #0",
        "8:", "\tcmp x7, x11", "\tb.ge 14f",
        "\tldr x1, [sp, #264]", "\tmul x2, x14, x11", "\tadd x1, x1, x2", "\tadd x1, x1, x7", "\tldr x2, [x15, #120]", "\tcmp x1, x2", "\tb.hs 14f",
        "\tmul x1, x1, x16", "\tadd x1, x1, x17", "\tmul x2, x13, x11", "\tadd x2, x2, x9", "\tmov x3, #0",
        "9:", "\tcmp x3, x11", "\tb.ge 13f", "\tadd x4, x2, x3", "\tldr x5, [x15, #112]", "\tcmp x4, x5", "\tb.hs 12f", "\tmul x4, x4, x10", "\tadd x4, x4, x1",
        "\tcmp x10, #4", "\tb.ne 10f", "\tstr w12, [x4]", "\tb 12f", "10:", "\tstrh w12, [x4]",
        "12:", "\tadd x3, x3, #1", "\tb 9b",
        "13:", "\tadd x7, x7, #1", "\tb 8b",
        "14:", "\tadd x13, x13, #1", "\tmov x0, #%d" % W, "\tcmp x13, x0", "\tb.lt 6b",
        "\tadd x14, x14, #1", "\tmov x0, #%d" % H, "\tcmp x14, x0", "\tb.lt 5b", "\tb .Lgp_ret", "")
    return L


def data_lines(W, H):
    ro = ["\t.section .rodata", "_sign_gfx_path:", "\t.byte " + ", ".join(str(b) for b in b"/dev/fb0\0"), "_sign_gfx_err:", "\t.byte " + ", ".join(str(b) for b in ERR.encode("utf-8"))]
    return ro, ["\t.balign 8", "_sign_gfx:", "\t.skip %d" % STATE, "_sign_gpix:", "\t.skip %d" % (4 * W * H)]
