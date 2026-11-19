#!/usr/bin/env python3
"""sign_fmt.py — Float の十進表記を書く実行時ルーチン(AArch64 アセンブリ)を出す。整数命令だけ(FPU を使わない)。

`_sign_fmt_float`: x0 = ビット列、x1 = 0(binary64)/ 1(binary32)、x2 = 書き込み先 → x0 = 書いた長さ。
表記は処理系と同じ:
  - binary64 は Python の `repr`(最短で読み戻せる十進。-4 <= 指数 < 16 は固定小数、それ以外は `1e-05`・`1.5e+20`)。
    `inf`・`-inf`・`nan`・`0.0`・`-0.0`。
  - binary32 は `f32_repr`(binary32 として読み戻せる最短。同じ綴り)。
作り方は Burger–Dybvig の free-format(Steele–White / dragon4): 1280 ビットの多倍長(32 ビットの肢 40 本)で
r, s, m+, m- を持ち、桁を 1 つずつ出す。丸めの同点は偶数へ(処理系の %g と同じ)。
参照実装は /tmp ではなく test_fmt.py の中の Python 版(同じ手順)で、repr / f32_repr と 12 万件突き合わせた。"""

N = 40                     # 肢の数(1 本 = 32 ビット)
BN = 4 * N                 # 1 つの多倍長のバイト数

def routine():
    L = []
    def e(s, c=""): L.append("\t" + s + (("\t// " + c) if c else ""))
    def lab(s): L.append(s + ":")
    def func(name, body): lab(name); body()

    # ---- 多倍長の部品(x0〜x7 だけ使う。呼ぶ側は x19〜x28 を持ち続ける) ----
    def zero_loop(p, tag):
        e("mov x5, #0"); lab(".Lz%s" % tag)
        e("str wzr, [%s, x5, lsl #2]" % p); e("add x5, x5, #1"); e("cmp x5, #%d" % N); e("b.ne .Lz%s" % tag)

    lab("_fb_zero"); zero_loop("x0", "a"); e("ret")
    lab("_fb_copy")
    e("mov x5, #0"); lab(".Lcp")
    e("ldr w6, [x1, x5, lsl #2]"); e("str w6, [x0, x5, lsl #2]"); e("add x5, x5, #1"); e("cmp x5, #%d" % N); e("b.ne .Lcp"); e("ret")
    lab("_fb_setbit")                                                    # x0 = 置き場、x1 = ビット番号: 0 にして 2^n を立てる
    zero_loop("x0", "b")
    e("lsr x5, x1, #5"); e("and x6, x1, #31"); e("mov x7, #1"); e("lsl x7, x7, x6"); e("str w7, [x0, x5, lsl #2]"); e("ret")
    lab("_fb_mulsmall")                                                  # x0 = 置き場、x1 = 小さい数(2^32 未満)を掛ける
    e("mov x2, #0"); e("mov x5, #0"); lab(".Lms")
    e("ldr w3, [x0, x5, lsl #2]"); e("mul x3, x3, x1"); e("add x3, x3, x2"); e("str w3, [x0, x5, lsl #2]"); e("lsr x2, x3, #32")
    e("add x5, x5, #1"); e("cmp x5, #%d" % N); e("b.ne .Lms"); e("ret")
    lab("_fb_add")                                                       # x0 += x1
    e("mov x2, #0"); e("mov x5, #0"); lab(".Lad")
    e("ldr w3, [x0, x5, lsl #2]"); e("ldr w4, [x1, x5, lsl #2]"); e("add x3, x3, x4"); e("add x3, x3, x2"); e("str w3, [x0, x5, lsl #2]"); e("lsr x2, x3, #32")
    e("add x5, x5, #1"); e("cmp x5, #%d" % N); e("b.ne .Lad"); e("ret")
    lab("_fb_sub")                                                       # x0 -= x1(x0 >= x1)
    e("mov x2, #0"); e("mov x5, #0"); lab(".Lsb")
    e("ldr w3, [x0, x5, lsl #2]"); e("ldr w4, [x1, x5, lsl #2]"); e("sub x3, x3, x4"); e("sub x3, x3, x2"); e("str w3, [x0, x5, lsl #2]"); e("lsr x2, x3, #63")
    e("add x5, x5, #1"); e("cmp x5, #%d" % N); e("b.ne .Lsb"); e("ret")
    lab("_fb_cmp")                                                       # x0 と x1 を比べる → x0 = 1(>)・0(=)・-1(<)
    e("mov x5, #%d" % (N - 1)); lab(".Lcm")
    e("ldr w3, [x0, x5, lsl #2]"); e("ldr w4, [x1, x5, lsl #2]"); e("cmp w3, w4"); e("b.ne .Lcmd")
    e("subs x5, x5, #1"); e("b.pl .Lcm"); e("mov x0, #0"); e("ret")
    lab(".Lcmd"); e("b.hi .Lcmg"); e("mov x0, #-1"); e("ret"); lab(".Lcmg"); e("mov x0, #1"); e("ret")
    lab("_fb_loadshift")                                                 # x0 = 置き場、x1 = f(64 ビット)、x2 = 左へ送るビット数
    e("stp x29, x30, [sp, #-32]!"); e("mov x29, sp"); e("stp x19, x20, [sp, #16]")
    e("mov x19, x0"); e("mov x20, x2")
    zero_loop("x0", "c")
    e("str w1, [x19]"); e("lsr x3, x1, #32"); e("str w3, [x19, #4]")
    lab(".Lls1"); e("cmp x20, #31"); e("b.lt .Lls2")
    e("mov x0, x19"); e("mov x1, #1"); e("lsl x1, x1, #31"); e("bl _fb_mulsmall"); e("sub x20, x20, #31"); e("b .Lls1")
    lab(".Lls2"); e("cbz x20, .Lls3"); e("mov x0, x19"); e("mov x1, #1"); e("lsl x1, x1, x20"); e("bl _fb_mulsmall")
    lab(".Lls3"); e("ldp x19, x20, [sp, #16]"); e("ldp x29, x30, [sp], #32"); e("ret")
    lab("_fb_pow10")                                                     # x0 = 置き場、x1 = n: 10^n を掛ける
    e("stp x29, x30, [sp, #-32]!"); e("mov x29, sp"); e("stp x19, x20, [sp, #16]")
    e("mov x19, x0"); e("mov x20, x1")
    lab(".Lp1"); e("cmp x20, #9"); e("b.lt .Lp2")
    e("mov x0, x19"); e("movz x1, #0xCA00"); e("movk x1, #0x3B9A, lsl #16"); e("bl _fb_mulsmall"); e("sub x20, x20, #9"); e("b .Lp1")      # 10^9 = 0x3B9ACA00
    lab(".Lp2"); e("cbz x20, .Lp3"); e("mov x0, x19"); e("mov x1, #10"); e("bl _fb_mulsmall"); e("sub x20, x20, #1"); e("b .Lp2")
    lab(".Lp3"); e("ldp x19, x20, [sp, #16]"); e("ldp x29, x30, [sp], #32"); e("ret")

    # ---- 本体 ----
    R, S, MP, MM, T = 0, BN, 2 * BN, 3 * BN, 4 * BN
    def bnp(reg, off):            # x28 + off → reg
        if off: e("add %s, x28, #%d" % (reg, off))
        else: e("mov %s, x28" % reg)
    def putc_imm(ch):
        e("mov w3, #%d" % ord(ch)); e("strb w3, [x25]"); e("add x25, x25, #1")
    def puts(s):
        for ch in s: putc_imm(ch)

    lab("_sign_fmt_float")
    e("stp x29, x30, [sp, #-112]!"); e("mov x29, sp")
    e("stp x19, x20, [sp, #16]"); e("stp x21, x22, [sp, #32]"); e("stp x23, x24, [sp, #48]"); e("stp x25, x26, [sp, #64]"); e("stp x27, x28, [sp, #80]")
    e("str x2, [sp, #96]"); e("mov x25, x2"); e("mov x24, x1")
    e("adrp x28, _fmt_bn"); e("add x28, x28, :lo12:_fmt_bn")
    e("cbnz x24, .Ld32")
    # f64
    e("lsr x6, x0, #63"); e("lsr x21, x0, #52"); e("and x21, x21, #0x7ff")
    e("mov x7, #1"); e("lsl x7, x7, #52"); e("mov x27, x7"); e("sub x7, x7, #1"); e("and x20, x0, x7")
    e("mov x22, #1075"); e("mov x23, #2047"); e("b .Ldd")
    lab(".Ld32")
    e("lsr x6, x0, #31"); e("lsr x21, x0, #23"); e("and x21, x21, #0xff")
    e("mov x7, #1"); e("lsl x7, x7, #23"); e("mov x27, x7"); e("sub x7, x7, #1"); e("and x20, x0, x7")
    e("mov x22, #150"); e("mov x23, #255")
    lab(".Ldd")                    # x6 符号、x21 ex、x20 fr、x27 隠れた 1、x22 BIAS、x23 ex の最大
    e("cmp x21, x23"); e("b.ne .Lfin")
    e("cbz x20, .Linf"); puts("nan"); e("b .Lout")
    lab(".Linf"); e("cbz x6, .Linf2"); putc_imm("-"); lab(".Linf2"); puts("inf"); e("b .Lout")
    lab(".Lfin"); e("cbz x6, .Lsg"); putc_imm("-"); lab(".Lsg")
    e("orr x5, x21, x20"); e("cbnz x5, .Lnz"); puts("0.0"); e("b .Lout")
    lab(".Lnz")
    e("mov x5, #0"); e("cmp x21, #1"); e("cset_le")   # placeholder replaced below
    L.pop()
    e("cmp x21, #1"); e("mov x26, #0"); e("b.hi .Lmx"); e("mov x26, #1"); lab(".Lmx")     # x26 = 最小の指数か
    e("cbnz x21, .Lnorm"); e("mov x19, x20"); e("mov x20, #1"); e("sub x20, x20, x22"); e("b .Ldec")
    lab(".Lnorm"); e("orr x19, x20, x27"); e("sub x20, x21, x22")
    lab(".Ldec")                   # x19 = f、x20 = e(符号つき)、x26 = 最小の指数、x27 = 隠れた 1
    e("and x22, x19, #1"); e("eor x22, x22, #1")        # x22 = 偶数か
    e("cmp x20, #0"); e("b.lt .Lneg")
    e("cmp x19, x27"); e("b.eq .Lp2pos")
    bnp("x0", R); e("mov x1, x19"); e("add x2, x20, #1"); e("bl _fb_loadshift")
    bnp("x0", S); e("mov x1, #1"); e("bl _fb_setbit")
    bnp("x0", MP); e("mov x1, x20"); e("bl _fb_setbit")
    bnp("x0", MM); e("mov x1, x20"); e("bl _fb_setbit"); e("b .Lscale")
    lab(".Lp2pos")
    bnp("x0", R); e("mov x1, x19"); e("add x2, x20, #2"); e("bl _fb_loadshift")
    bnp("x0", S); e("mov x1, #2"); e("bl _fb_setbit")
    bnp("x0", MP); e("add x1, x20, #1"); e("bl _fb_setbit")
    bnp("x0", MM); e("mov x1, x20"); e("bl _fb_setbit"); e("b .Lscale")
    lab(".Lneg")
    e("cbnz x26, .Lneg1"); e("cmp x19, x27"); e("b.ne .Lneg1")
    bnp("x0", R); e("mov x1, x19"); e("mov x2, #2"); e("bl _fb_loadshift")
    bnp("x0", S); e("mov x1, #2"); e("sub x1, x1, x20"); e("bl _fb_setbit")
    bnp("x0", MP); e("mov x1, #1"); e("bl _fb_setbit")
    bnp("x0", MM); e("mov x1, #0"); e("bl _fb_setbit"); e("b .Lscale")
    lab(".Lneg1")
    bnp("x0", R); e("mov x1, x19"); e("mov x2, #1"); e("bl _fb_loadshift")
    bnp("x0", S); e("mov x1, #1"); e("sub x1, x1, x20"); e("bl _fb_setbit")
    bnp("x0", MP); e("mov x1, #0"); e("bl _fb_setbit")
    bnp("x0", MM); e("mov x1, #0"); e("bl _fb_setbit")
    lab(".Lscale")
    # (neg 1 の MP/MM は 2^0 = 1、neg 2 の MP は 2^1 = 2。setbit は 2^n を立てる)
    # k の見積もり
    e("mov x1, x19"); e("mov x2, #0"); lab(".Lbl"); e("cbz x1, .Lbl2"); e("lsr x1, x1, #1"); e("add x2, x2, #1"); e("b .Lbl"); lab(".Lbl2")
    e("add x3, x20, x2"); e("sub x3, x3, #1"); e("movz x4, #0x3441"); e("movk x4, #1, lsl #16"); e("mul x3, x3, x4"); e("asr x21, x3, #18")      # 78913 = 0x13441
    e("cmp x21, #0"); e("b.lt .Lsc2")
    bnp("x0", S); e("mov x1, x21"); e("bl _fb_pow10"); e("b .Lfix")
    lab(".Lsc2"); e("neg x27, x21")
    for off in (R, MP, MM):
        bnp("x0", off); e("mov x1, x27"); e("bl _fb_pow10")
    lab(".Lfix")
    def sum_cmp():                # T = R + MP を S と比べる → x0
        bnp("x0", T); bnp("x1", R); e("bl _fb_copy"); bnp("x0", T); bnp("x1", MP); e("bl _fb_add")
        bnp("x0", T); bnp("x1", S); e("bl _fb_cmp")
    lab(".Lf1"); sum_cmp()
    e("cmp x0, #0"); e("b.gt .Lf1i"); e("b.lt .Lf2"); e("cbz x22, .Lf2")
    lab(".Lf1i"); e("add x21, x21, #1"); bnp("x0", S); e("mov x1, #10"); e("bl _fb_mulsmall"); e("b .Lf1")
    lab(".Lf2")
    bnp("x0", T); bnp("x1", R); e("bl _fb_copy"); bnp("x0", T); bnp("x1", MP); e("bl _fb_add"); bnp("x0", T); e("mov x1, #10"); e("bl _fb_mulsmall")
    bnp("x0", T); bnp("x1", S); e("bl _fb_cmp")
    e("cmp x0, #0"); e("b.lt .Lf2d"); e("b.gt .Lf3"); e("cbnz x22, .Lf3")
    lab(".Lf2d"); e("sub x21, x21, #1")
    for off in (R, MP, MM):
        bnp("x0", off); e("mov x1, #10"); e("bl _fb_mulsmall")
    e("b .Lf2")
    lab(".Lf3")
    # 桁を出す
    e("adrp x27, _fmt_dig"); e("add x27, x27, :lo12:_fmt_dig"); e("mov x23, #0")
    lab(".Lg1")
    for off in (R, MP, MM):
        bnp("x0", off); e("mov x1, #10"); e("bl _fb_mulsmall")
    e("mov x24, #0")                                         # d
    lab(".Lg2"); bnp("x0", R); bnp("x1", S); e("bl _fb_cmp"); e("cmp x0, #0"); e("b.lt .Lg3")
    bnp("x0", R); bnp("x1", S); e("bl _fb_sub"); e("add x24, x24, #1"); e("b .Lg2")
    lab(".Lg3")
    bnp("x0", R); bnp("x1", MM); e("bl _fb_cmp")                                          # tc1 = R < MM か (R = MM かつ偶数)
    e("mov x19, #0"); e("cmp x0, #0"); e("b.lt .Lt1"); e("b.gt .Lt1n"); e("cbz x22, .Lt1n"); lab(".Lt1"); e("mov x19, #1"); lab(".Lt1n")
    sum_cmp()                                                                              # tc2 = R + MP > S か (= かつ偶数)
    e("mov x20, #0"); e("cmp x0, #0"); e("b.gt .Lt2"); e("b.lt .Lt2n"); e("cbz x22, .Lt2n"); lab(".Lt2"); e("mov x20, #1"); lab(".Lt2n")
    e("orr x5, x19, x20"); e("cbnz x5, .Lg4")
    e("strb w24, [x27, x23]"); e("add x23, x23, #1"); e("b .Lg1")                          # どちらでもない: d を出して続ける
    lab(".Lg4")
    e("cbz x20, .Lg5")                                                                    # tc2 のみ → d+1、両方 → 2R と S で
    e("cbz x19, .Lg6")
    bnp("x0", T); bnp("x1", R); e("bl _fb_copy"); bnp("x0", T); e("mov x1, #2"); e("bl _fb_mulsmall"); bnp("x0", T); bnp("x1", S); e("bl _fb_cmp")
    e("cmp x0, #0"); e("b.lt .Lg5"); e("b.gt .Lg6"); e("tbz x24, #0, .Lg5")
    lab(".Lg6"); e("add x24, x24, #1")
    lab(".Lg5"); e("strb w24, [x27, x23]"); e("add x23, x23, #1")
    # 10 の繰り上がり
    e("sub x5, x23, #1"); lab(".Lc1")
    e("ldrb w6, [x27, x5]"); e("cmp w6, #10"); e("b.ne .Lc9")
    e("strb wzr, [x27, x5]"); e("cbz x5, .Lc2"); e("sub x5, x5, #1"); e("ldrb w6, [x27, x5]"); e("add w6, w6, #1"); e("strb w6, [x27, x5]"); e("b .Lc1")
    lab(".Lc2")                                                                           # 先頭が溢れた: 1 を前に足す
    e("mov x6, x23"); lab(".Lc3"); e("cbz x6, .Lc4"); e("sub x7, x6, #1"); e("ldrb w3, [x27, x7]"); e("strb w3, [x27, x6]"); e("sub x6, x6, #1"); e("b .Lc3")
    lab(".Lc4"); e("mov w3, #1"); e("strb w3, [x27]"); e("add x23, x23, #1"); e("add x21, x21, #1")
    lab(".Lc9")
    lab(".Ls1"); e("cmp x23, #1"); e("b.ls .Ls2"); e("sub x5, x23, #1"); e("ldrb w6, [x27, x5]"); e("cbnz w6, .Ls2"); e("sub x23, x23, #1"); e("b .Ls1")
    lab(".Ls2")
    # 表記: x21 = k、x23 = 桁数、x27 = 桁の配列、x25 = 書く所
    def digit_at(idx, tmp="w6"):   # idx の桁を '0'+d にして putc
        e("ldrb %s, [x27, %s]" % (tmp, idx)); e("add %s, %s, #48" % (tmp, tmp)); e("strb %s, [x25]" % tmp); e("add x25, x25, #1")
    e("sub x4, x21, #1")                                     # x4 = 指数 x(科学表記の 10 の冪)
    e("cmp x4, #-4"); e("b.lt .Lex")                          # x < -4
    e("cmp x4, #16"); e("b.ge .Lex")
    e("cmp x4, #0"); e("b.lt .Lfn")
    # 固定・整数部あり: 0..x の桁(足りなければ 0)
    e("mov x5, #0"); lab(".Lfi")
    e("cmp x5, x23"); e("b.lt .Lfi1"); putc_imm("0"); e("b .Lfi2"); lab(".Lfi1"); digit_at("x5"); lab(".Lfi2")
    e("add x5, x5, #1"); e("cmp x5, x4"); e("b.le .Lfi")
    putc_imm(".")
    e("cmp x23, x5"); e("b.le .Lfz")                          # n > x+1: 残りの桁
    lab(".Lfr"); digit_at("x5"); e("add x5, x5, #1"); e("cmp x5, x23"); e("b.lt .Lfr"); e("b .Lout")
    lab(".Lfz"); putc_imm("0"); e("b .Lout")
    lab(".Lfn")                                              # 0.000ddd
    puts("0."); e("neg x5, x4"); e("sub x5, x5, #1"); lab(".Lfn1"); e("cbz x5, .Lfn2"); putc_imm("0"); e("sub x5, x5, #1"); e("b .Lfn1")
    lab(".Lfn2"); e("mov x5, #0"); lab(".Lfn3"); digit_at("x5"); e("add x5, x5, #1"); e("cmp x5, x23"); e("b.lt .Lfn3"); e("b .Lout")
    lab(".Lex")                                              # d.ddde+XX
    e("mov x5, #0"); digit_at("x5"); e("mov x5, #1"); e("cmp x23, #1"); e("b.le .Lex2"); putc_imm(".")
    lab(".Lex1"); digit_at("x5"); e("add x5, x5, #1"); e("cmp x5, x23"); e("b.lt .Lex1")
    lab(".Lex2"); putc_imm("e"); e("cmp x4, #0"); e("b.ge .Lex3"); putc_imm("-"); e("neg x4, x4"); e("b .Lex4"); lab(".Lex3"); putc_imm("+")
    lab(".Lex4"); e("cmp x4, #100"); e("b.lt .Lex5")
    e("mov x7, #100"); e("udiv x5, x4, x7"); e("msub x4, x5, x7, x4"); e("add w5, w5, #48"); e("strb w5, [x25]"); e("add x25, x25, #1")
    lab(".Lex5"); e("mov x7, #10"); e("udiv x5, x4, x7"); e("msub x4, x5, x7, x4"); e("add w5, w5, #48"); e("strb w5, [x25]"); e("add x25, x25, #1")
    e("add w4, w4, #48"); e("strb w4, [x25]"); e("add x25, x25, #1")
    lab(".Lout")
    e("ldr x5, [sp, #96]"); e("sub x0, x25, x5")
    e("ldp x19, x20, [sp, #16]"); e("ldp x21, x22, [sp, #32]"); e("ldp x23, x24, [sp, #48]"); e("ldp x25, x26, [sp, #64]"); e("ldp x27, x28, [sp, #80]"); e("ldp x29, x30, [sp], #112"); e("ret")
    return "\n".join(L) + "\n"

def data():
    return "\t.section .bss\n\t.balign 16\n_fmt_bn:\n\t.skip %d\n_fmt_dig:\n\t.skip 64\n" % (5 * BN)

if __name__ == "__main__":
    print("\t.text"); print(routine(), end=""); print(data(), end="")
