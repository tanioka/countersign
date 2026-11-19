"""sign_realnet.py — `--real-dev` のネットワーク装置(0x9900000)の中継ルーチン(AArch64 アセンブリ)。

番号と引数を影レジスタに書き、GO(+0x20)で Linux のソケットのシステムコールに置き換える。RET(+0x24)に結果(0 以上 = 成功、負 = -errno)。
  1 CONNECT   socket(198) → setsockopt SO_SNDTIMEO 10 秒(208) → connect(203)。EINPROGRESS は -110 にそろえる
  2 SEND      sendto(206)(MSG_NOSIGNAL)を全部送るまで繰り返す
  3 RECV      ppoll(73)で待ち時間(SETTIMEOUT、既定 5000 ms)だけ待ち、recvfrom(207)(MSG_DONTWAIT)。来なければ -11
  4 CLOSE     close(57)
  5 LISTEN    socket → SO_REUSEADDR → bind(200)(0.0.0.0)→ listen(201)
  6 ACCEPT    ppoll → accept(202)。7 UDP_OPEN: socket(2,2) → bind。8 SENDTO / 9 RECVFROM: sendto・recvfrom(送り主を「ア.ド.レ.ス:ポート」で書く)
  10 SETTIMEOUT(表に持つ)/ 12 PORT: getsockname(204)/ 11 RESOLVE
  13 TLS_START は -38(ENOSYS)。TLS はライブラリ(暗号・証明書の確認)が要り、システムコールだけでは作れない。接続は閉じない。
ハンドルは 1〜32(表の位置 + 1)。同時に 32 まで、あふれると -24。バッファは 1 語 = 1 バイト(4 バイト刻み)。1 回の送受信は 65536 バイトまで。
名前の解決は IPv4 の「a.b.c.d」・"localhost"・それ以外(DNS: /etc/resolv.conf の最初の nameserver(IPv4)へ UDP で A を問い合わせる。/etc/hosts は読まない。引けなければ -2)。
--net の許可の絞り込み(local・host 指定)と --net-proxy は無い: 実機ではネットワークの許可は OS 側(ファイアウォールなど)で決める。
これは実装の決めで、仕様に定めはない。実機では未実行(疑似カーネル = 実ソケットで確認)。
"""

SIZE_REG = 0x40          # 影レジスタの大きさ(NR ARG0..5 GO RET)
NBUF = 65536


def _imm(reg, v):
    from sign_asm import emit_imm
    out = []; emit_imm(out, reg, v); return out


def _adr(reg, sym):
    return ["\tadrp %s, %s" % (reg, sym), "\tadd %s, %s, :lo12:%s" % (reg, reg, sym)]



DNS = [
 "// 名前 → ip(DNS): x1 = 長さ(名前は _sign_nhs)→ x0 = ip か -2。/etc/resolv.conf の最初の nameserver(IPv4)に UDP で A を聞く(2 回、各 2 秒)。/etc/hosts は読まない",
 "_sign_dev_ndns:", "\tstp x29, x30, [sp, #-96]!", "\tmov x29, sp", "\tstr x1, [sp, #24]", "\tmov x1, #-1", "\tstr x1, [sp, #16]",
 "\tmov x0, #-100", "\tadrp x1, _sign_dns_path", "\tadd x1, x1, :lo12:_sign_dns_path", "\tmov x2, #0", "\tmov x3, #0", "\tmov x8, #56", "\tsvc #0",
] + _imm("x1", 0x0100007F) + [
 "\tstr x1, [sp, #32]", "\tcmp x0, #0", "\tb.lt .Ldns_build", "\tstr x0, [sp, #40]",
 "\tadrp x1, _sign_dnsc", "\tadd x1, x1, :lo12:_sign_dnsc", "\tmov x2, #2000", "\tmov x8, #63", "\tsvc #0", "\tstr x0, [sp, #48]",
 "\tldr x0, [sp, #40]", "\tmov x8, #57", "\tsvc #0", "\tldr x4, [sp, #48]", "\tcmp x4, #0", "\tb.le .Ldns_build",
 "\tadrp x2, _sign_dnsc", "\tadd x2, x2, :lo12:_sign_dnsc", "\tadd x3, x2, x4", "\tstrb wzr, [x3]",
 ".Ldns_line:", "\tcmp x2, x3", "\tb.hs .Ldns_build", "\tadrp x6, _sign_dns_kw", "\tadd x6, x6, :lo12:_sign_dns_kw", "\tmov x7, #0",
 "1:", "\tadd x13, x2, x7", "\tldrb w10, [x13]", "\tadd x13, x6, x7", "\tldrb w11, [x13]", "\tcmp x10, x11", "\tb.ne .Ldns_next", "\tadd x7, x7, #1", "\tcmp x7, #10", "\tb.ne 1b",
 "\tadd x2, x2, #10",
 "2:", "\tcmp x2, x3", "\tb.hs .Ldns_build", "\tldrb w10, [x2]", "\tcmp x10, #32", "\tb.eq 3f", "\tcmp x10, #9", "\tb.ne 4f", "3:", "\tadd x2, x2, #1", "\tb 2b",
 "4:", "\tmov x4, x2",
 "5:", "\tcmp x4, x3", "\tb.hs 6f", "\tldrb w10, [x4]", "\tcmp x10, #33", "\tb.lo 6f", "\tadd x4, x4, #1", "\tb 5b",
 "6:", "\tstp x3, x4, [sp, #56]", "\tmov x3, x4", "\tbl _sign_dev_nparse", "\tldp x3, x4, [sp, #56]", "\tcmp x0, #0", "\tb.lt 7f", "\tstr x0, [sp, #32]", "\tb .Ldns_build",
 "7:", "\tmov x2, x4",
 ".Ldns_next:", "\tcmp x2, x3", "\tb.hs .Ldns_build", "\tldrb w10, [x2]", "\tadd x2, x2, #1", "\tcmp x10, #10", "\tb.ne .Ldns_next", "\tb .Ldns_line",
 # --- 問い合わせの組み立て ---
 ".Ldns_build:", "\tadrp x5, _sign_dnsq", "\tadd x5, x5, :lo12:_sign_dnsq", "\tadrp x6, _sign_dns_hdr", "\tadd x6, x6, :lo12:_sign_dns_hdr", "\tmov x7, #0",
 "1:", "\tadd x13, x6, x7", "\tldrb w10, [x13]", "\tadd x13, x5, x7", "\tstrb w10, [x13]", "\tadd x7, x7, #1", "\tcmp x7, #12", "\tb.ne 1b",
 "\tadd x5, x5, #12", "\tadrp x3, _sign_nhs", "\tadd x3, x3, :lo12:_sign_nhs", "\tldr x4, [sp, #24]", "\tadd x4, x3, x4",
 ".Ldns_lab:", "\tmov x6, x3",
 "7:", "\tcmp x3, x4", "\tb.hs 8f", "\tldrb w10, [x3]", "\tcmp x10, #46", "\tb.eq 8f", "\tadd x3, x3, #1", "\tb 7b",
 "8:", "\tsub x7, x3, x6", "\tcbz x7, .Ldns_bad", "\tcmp x7, #63", "\tb.hi .Ldns_bad", "\tstrb w7, [x5]", "\tadd x5, x5, #1",
 "9:", "\tcbz x7, 10f", "\tldrb w10, [x6]", "\tstrb w10, [x5]", "\tadd x6, x6, #1", "\tadd x5, x5, #1", "\tsub x7, x7, #1", "\tb 9b",
 "10:", "\tcmp x3, x4", "\tb.hs 11f", "\tadd x3, x3, #1", "\tcmp x3, x4", "\tb.hs 11f", "\tb .Ldns_lab",
 "11:", "\tstrb wzr, [x5]", "\tmov x10, #0", "\tstrb w10, [x5, #1]", "\tmov x10, #1", "\tstrb w10, [x5, #2]", "\tmov x10, #0", "\tstrb w10, [x5, #3]", "\tmov x10, #1", "\tstrb w10, [x5, #4]",
 "\tadd x5, x5, #5", "\tadrp x2, _sign_dnsq", "\tadd x2, x2, :lo12:_sign_dnsq", "\tsub x5, x5, x2", "\tstr x5, [sp, #48]",
 "\tmov x0, #2", "\tmov x1, #2", "\tmov x2, #0", "\tmov x8, #198", "\tsvc #0", "\tcmp x0, #0", "\tb.lt .Ldns_bad", "\tstr x0, [sp, #16]",
 "\tldr x0, [sp, #32]", "\tmov x1, #53", "\tadd x2, sp, #64", "\tbl _sign_dev_nsa", "\tmov x1, #2", "\tstr x1, [sp, #40]",
 ".Ldns_try:", "\tldr x0, [sp, #16]", "\tadrp x1, _sign_dnsq", "\tadd x1, x1, :lo12:_sign_dnsq", "\tldr x2, [sp, #48]", "\tmov x3, #0", "\tadd x4, sp, #64", "\tmov x5, #16", "\tmov x8, #206", "\tsvc #0",
 "\tcmp x0, #0", "\tb.lt .Ldns_fail",
 "\tldr x0, [sp, #16]", "\tmov x1, #2000", "\tbl _sign_dev_nwait", "\tcmp x0, #0", "\tb.ne .Ldns_retry",
 "\tldr x0, [sp, #16]", "\tadrp x1, _sign_dnsr", "\tadd x1, x1, :lo12:_sign_dnsr", "\tmov x2, #512", "\tmov x3, #0x40", "\tmov x4, #0", "\tmov x5, #0", "\tmov x8, #207", "\tsvc #0",
 "\tcmp x0, #12", "\tb.lt .Ldns_retry", "\tstr x0, [sp, #48]",
 "\tadrp x2, _sign_dnsr", "\tadd x2, x2, :lo12:_sign_dnsr", "\tldrb w10, [x2]", "\tcmp x10, #0x5a", "\tb.ne .Ldns_retry", "\tldrb w10, [x2, #1]", "\tcmp x10, #0x1d", "\tb.ne .Ldns_retry",
 "\tldrb w10, [x2, #2]", "\tand x11, x10, #0x80", "\tcbz x11, .Ldns_retry", "\tldrb w10, [x2, #3]", "\tand x10, x10, #0xF", "\tcbnz x10, .Ldns_fail",
 "\tldrb w9, [x2, #6]", "\tldrb w10, [x2, #7]", "\tlsl x9, x9, #8", "\torr x9, x9, x10", "\tcmp x9, #64", "\tb.ls 1f", "\tmov x9, #64",
 "1:", "\tldr x4, [sp, #48]", "\tadd x4, x2, x4", "\tadd x3, x2, #12", "\tbl _sign_dev_dskip", "\tcmp x0, #0", "\tb.lt .Ldns_fail", "\tadd x3, x3, #4",
 ".Ldns_ans:", "\tcbz x9, .Ldns_fail", "\tbl _sign_dev_dskip", "\tcmp x0, #0", "\tb.lt .Ldns_fail", "\tadd x12, x3, #10", "\tcmp x12, x4", "\tb.hi .Ldns_fail",
 "\tldrb w10, [x3]", "\tldrb w11, [x3, #1]", "\tlsl x10, x10, #8", "\torr x10, x10, x11", "\tldrb w13, [x3, #8]", "\tldrb w14, [x3, #9]", "\tlsl x13, x13, #8", "\torr x13, x13, x14",
 "\tadd x3, x3, #10", "\tadd x14, x3, x13", "\tcmp x14, x4", "\tb.hi .Ldns_fail", "\tcmp x10, #1", "\tb.ne 2f", "\tcmp x13, #4", "\tb.ne 2f",
 "\tldr w0, [x3]", "\tstr x0, [sp, #56]", "\tldr x0, [sp, #16]", "\tmov x8, #57", "\tsvc #0", "\tldr x0, [sp, #56]", "\tb .Ldns_ret",
 "2:", "\tmov x3, x14", "\tsub x9, x9, #1", "\tb .Ldns_ans",
 ".Ldns_retry:", "\tldr x1, [sp, #40]", "\tsub x1, x1, #1", "\tstr x1, [sp, #40]", "\tcbnz x1, .Ldns_try",
 ".Ldns_fail:", "\tldr x0, [sp, #16]", "\tmov x8, #57", "\tsvc #0",
 ".Ldns_bad:", "\tmov x0, #-2", ".Ldns_ret:", "\tldp x29, x30, [sp], #96", "\tret", "",
 "// 名前を飛ばす(ラベル列か圧縮ポインタ): x3 = 位置, x4 = 終わり → x3 が進む, x0 = 0 か -1",
 "_sign_dev_dskip:", "1:", "\tcmp x3, x4", "\tb.hs 4f", "\tldrb w10, [x3]", "\tcbnz x10, 2f", "\tadd x3, x3, #1", "\tmov x0, #0", "\tret",
 "2:", "\tand x11, x10, #0xC0", "\tcmp x11, #0xC0", "\tb.ne 3f", "\tadd x3, x3, #2", "\tmov x0, #0", "\tret",
 "3:", "\tadd x3, x3, x10", "\tadd x3, x3, #1", "\tb 1b", "4:", "\tmov x0, #-1", "\tret", "",
]


def shim():
    L = []
    add = lambda *xs: L.extend(xs)
    add("// ===== ネットワーク (0x99…) =====", "")
    # --- 10 進の書き出し: x0 = 値, x1 = 書き先(バイト)→ x1 が進む。x2〜x6 を壊す ---
    add("_sign_dev_nu:", "\tsub sp, sp, #16", "\tadd x2, sp, #16", "\tmov x3, #10",
        "1:", "\tudiv x4, x0, x3", "\tmsub x5, x4, x3, x0", "\tadd x5, x5, #48", "\tsub x2, x2, #1", "\tstrb w5, [x2]", "\tmov x0, x4", "\tcbnz x0, 1b",
        "\tadd x6, sp, #16",
        "2:", "\tldrb w5, [x2]", "\tstrb w5, [x1]", "\tadd x2, x2, #1", "\tadd x1, x1, #1", "\tcmp x2, x6", "\tb.ne 2b", "\tadd sp, sp, #16", "\tret", "")
    # --- ア.ド.レ.ス の書き出し: x0 = ip(メモリ上の並びで a が最下位), x1 = 書き先 → x1 が進む ---
    add("_sign_dev_nip:", "\tstp x29, x30, [sp, #-32]!", "\tmov x29, sp", "\tstr x0, [sp, #16]", "\tmov x13, #0",
        "1:", "\tldr x0, [sp, #16]", "\tlsl x2, x13, #3", "\tlsr x0, x0, x2", "\tand x0, x0, #0xFF", "\tbl _sign_dev_nu",
        "\tadd x13, x13, #1", "\tcmp x13, #4", "\tb.eq 2f", "\tmov x2, #46", "\tstrb w2, [x1]", "\tadd x1, x1, #1", "\tb 1b",
        "2:", "\tldp x29, x30, [sp], #32", "\tret", "")
    # --- 16 ビットの前後入れ替え: x0 → x0 ---
    add("_sign_dev_nbe:", "\tand x0, x0, #0xFFFF", "\tlsr x1, x0, #8", "\tand x2, x0, #0xFF", "\tlsl x2, x2, #8", "\torr x0, x1, x2", "\tret", "")
    # --- ホスト名 → ip。x0 = 語の列, x1 = 長さ → x0 = ip(0 以上)か -22(長さ)か -2(引けない)。数字・localhost・それ以外は DNS ---
    add("_sign_dev_nhost:", "\tstp x29, x30, [sp, #-32]!", "\tmov x29, sp",
        "\tsub x2, x1, #1", "\tcmp x2, #255", "\tb.lo 1f", "\tmov x0, #-22", "\tb .Lnh_ret", "1:", "\tstr x1, [sp, #16]", "\tmov x2, x1")
    add(*_adr("x1", "_sign_nhs"))
    add("\tbl _sign_dev_pack", "\tldr x1, [sp, #16]")
    add(*_adr("x2", "_sign_nhs"))
    add("\tadd x3, x2, x1", "\tcmp x1, #9", "\tb.ne .Lnh_parse")
    add(*_adr("x6", "_sign_nlh"))
    add("\tmov x7, #0",
        "2:", "\tadd x13, x2, x7", "\tldrb w10, [x13]", "\tadd x13, x6, x7", "\tldrb w11, [x13]", "\tcmp x10, x11", "\tb.ne .Lnh_parse",
        "\tadd x7, x7, #1", "\tcmp x7, #9", "\tb.ne 2b")
    add(*_imm("x0", 0x0100007F))
    add("\tb .Lnh_ret", ".Lnh_parse:")
    add(*_adr("x2", "_sign_nhs"))
    add("\tldr x1, [sp, #16]", "\tadd x3, x2, x1", "\tbl _sign_dev_nparse", "\tcmp x0, #0", "\tb.ge .Lnh_ret",
        "\tldr x1, [sp, #16]", "\tbl _sign_dev_ndns",
        ".Lnh_ret:", "\tldp x29, x30, [sp], #32", "\tret", "")
    # 数字 a.b.c.d の読み: x2 = 先頭, x3 = 終わり → x0 = ip か -2
    add("_sign_dev_nparse:", "\tmov x4, #0", "\tmov x5, #0",
        ".Lnh_oct:", "\tcmp x2, x3", "\tb.hs .Lnh_bad", "\tmov x6, #0", "\tmov x7, #0",
        ".Lnh_dig:", "\tcmp x2, x3", "\tb.hs .Lnh_end", "\tldrb w10, [x2]", "\tsub x11, x10, #48", "\tcmp x11, #10", "\tb.hs .Lnh_end",
        "\tmov x12, #10", "\tmul x6, x6, x12", "\tadd x6, x6, x11", "\tadd x7, x7, #1", "\tcmp x6, #255", "\tb.hi .Lnh_bad", "\tadd x2, x2, #1", "\tb .Lnh_dig",
        ".Lnh_end:", "\tcbz x7, .Lnh_bad", "\tlsl x12, x5, #3", "\tlsl x6, x6, x12", "\torr x4, x4, x6", "\tadd x5, x5, #1", "\tcmp x5, #4", "\tb.eq .Lnh_last",
        "\tcmp x2, x3", "\tb.hs .Lnh_bad", "\tldrb w10, [x2]", "\tcmp x10, #46", "\tb.ne .Lnh_bad", "\tadd x2, x2, #1", "\tb .Lnh_oct",
        ".Lnh_last:", "\tcmp x2, x3", "\tb.ne .Lnh_bad", "\tmov x0, x4", "\tret",
        ".Lnh_bad:", "\tmov x0, #-2", "\tret", "")
    add(*DNS)
    # --- ハンドルの表(32 個 × 24 バイト: fd+1・種類(1 TCP / 2 待ち受け / 3 UDP)・待ち ms)---
    add("// x0 = fd, x1 = 種類 → x0 = ハンドル(1〜32)か -24(いっぱい。fd は閉じる)",
        "_sign_dev_nnew:")
    add(*_adr("x2", "_sign_nh"))
    add("\tmov x3, #0", "\tmov x6, #24",
        "1:", "\tmul x7, x3, x6", "\tadd x5, x2, x7", "\tldr x4, [x5]", "\tcbz x4, 2f", "\tadd x3, x3, #1", "\tcmp x3, #32", "\tb.ne 1b",
        "\tmov x8, #57", "\tsvc #0", "\tmov x0, #-24", "\tret",
        "2:", "\tadd x4, x0, #1", "\tstr x4, [x5]", "\tstr x1, [x5, #8]", "\tmov x6, #5000", "\tstr x6, [x5, #16]", "\tadd x0, x3, #1", "\tret", "")
    add("// x0 = ハンドル → x0 = fd か -9, x5 = 表の項",
        "_sign_dev_nget:", "\tsub x1, x0, #1", "\tcmp x1, #32", "\tb.hs 1f")
    add(*_adr("x2", "_sign_nh"))
    add("\tmov x6, #24", "\tmul x7, x1, x6", "\tadd x5, x2, x7", "\tldr x4, [x5]", "\tcbz x4, 1f", "\tsub x0, x4, #1", "\tret",
        "1:", "\tmov x0, #-9", "\tret", "")
    # --- 待ち: x0 = fd, x1 = ms → 0(読める)か -11(待ち時間切れ)か -errno ---
    add("_sign_dev_nwait:", "\tstp x29, x30, [sp, #-48]!", "\tmov x29, sp",
        "\tstr w0, [sp, #16]", "\tmov x2, #1", "\tstrh w2, [sp, #20]", "\tmov x2, #0", "\tstrh w2, [sp, #22]",
        "\tmov x3, #1000", "\tudiv x4, x1, x3", "\tmsub x5, x4, x3, x1", "\tmov x6, #1000", "\tmul x5, x5, x6", "\tmul x5, x5, x6",
        "\tstr x4, [sp, #24]", "\tstr x5, [sp, #32]",
        "\tadd x0, sp, #16", "\tmov x1, #1", "\tadd x2, sp, #24", "\tmov x3, #0", "\tmov x4, #8", "\tmov x8, #73", "\tsvc #0",
        "\tcmp x0, #0", "\tb.gt 2f", "\tb.eq 1f", "\tb 3f",
        "1:", "\tmov x0, #-11", "\tb 3f", "2:", "\tmov x0, #0", "3:", "\tldp x29, x30, [sp], #48", "\tret", "")
    # --- sockaddr_in の用意: x0 = ip, x1 = port, x2 = 書き先 ---
    add("_sign_dev_nsa:", "\tstp x29, x30, [sp, #-32]!", "\tmov x29, sp", "\tstp x0, x2, [sp, #16]", "\tmov x0, x1", "\tbl _sign_dev_nbe", "\tldp x1, x2, [sp, #16]",
        "\tmov x3, #2", "\tstrh w3, [x2]", "\tstrh w0, [x2, #2]", "\tstr w1, [x2, #4]", "\tstr xzr, [x2, #8]", "\tldp x29, x30, [sp], #32", "\tret", "")
    # --- 本体 ---
    # 枠: +16 NR, +24..+64 ARG0..5, +72 fd, +80 ip, +88 cur, +96 rem, +104 補助, +112 sockaddr(16), +128 長さ, +136 補助
    add("// x0 = 番号。結果 = x0",
        "_sign_dev_net:", "\tstp x29, x30, [sp, #-160]!", "\tmov x29, sp", "\tstr x0, [sp, #16]")
    add(*_adr("x11", "_sign_dreg"))
    add("\tadd x11, x11, #0x3000")
    for i in range(6):
        add("\tldr w1, [x11, #%d]" % (4 + 4 * i), "\tstr x1, [sp, #%d]" % (24 + 8 * i))
    cases = [(1, "conn"), (2, "send"), (3, "recv"), (4, "close"), (5, "listen"), (6, "accept"), (7, "udp"), (8, "sendto"), (9, "recvfrom"), (10, "settmo"), (11, "resolve"), (12, "port"), (13, "tls")]
    for n, name in cases:
        add("\tcmp x0, #%d" % n, "\tb.eq .Lnet_%s" % name)
    add("\tmov x0, #-38", "\tb .Lnet_ret",
        ".Lnet_einval:", "\tmov x0, #-22", ".Lnet_ret:", "\tldp x29, x30, [sp], #160", "\tret", "")
    # 失敗したら fd を閉じて戻る(x0 = -errno を保つ)
    add(".Lnet_failclose:", "\tstr x0, [sp, #104]", "\tldr x0, [sp, #72]", "\tmov x8, #57", "\tsvc #0", "\tldr x0, [sp, #104]", "\tb .Lnet_ret")
    # ハンドル → fd(x0 = ARG0)。失敗は -9 で戻る
    getfd = ["\tldr x0, [sp, #24]", "\tbl _sign_dev_nget", "\tcmp x0, #0", "\tb.lt .Lnet_ret", "\tstr x0, [sp, #72]", "\tstr x5, [sp, #136]"]
    # CONNECT
    add(".Lnet_conn:", "\tldr x0, [sp, #24]", "\tldr x1, [sp, #32]", "\tbl _sign_dev_nhost", "\tcmp x0, #0", "\tb.lt .Lnet_ret", "\tstr x0, [sp, #80]",
        "\tldr x1, [sp, #40]", "\tsub x2, x1, #1", "\tmov x3, #65535", "\tcmp x2, x3", "\tb.hs .Lnet_einval",
        "\tmov x0, #2", "\tmov x1, #1", "\tmov x2, #0", "\tmov x8, #198", "\tsvc #0", "\tcmp x0, #0", "\tb.lt .Lnet_ret", "\tstr x0, [sp, #72]",
        "\tmov x1, #10", "\tstr x1, [sp, #112]", "\tstr xzr, [sp, #120]",
        "\tmov x1, #1", "\tmov x2, #21", "\tadd x3, sp, #112", "\tmov x4, #16", "\tmov x8, #208", "\tsvc #0",
        "\tldr x0, [sp, #80]", "\tldr x1, [sp, #40]", "\tadd x2, sp, #112", "\tbl _sign_dev_nsa",
        "\tldr x0, [sp, #72]", "\tadd x1, sp, #112", "\tmov x2, #16", "\tmov x8, #203", "\tsvc #0",
        "\tcmp x0, #0", "\tb.ge 1f", "\tmov x2, #-115", "\tcmp x0, x2", "\tb.ne .Lnet_failclose", "\tmov x0, #-110", "\tb .Lnet_failclose",
        "1:", "\tldr x0, [sp, #72]", "\tmov x1, #1", "\tbl _sign_dev_nnew", "\tb .Lnet_ret")
    # SEND(h, buf, n)
    add(".Lnet_send:", *getfd)
    add("\tldr x2, [sp, #40]", "\tmov x3, #%d" % NBUF, "\tcmp x2, x3", "\tb.hi .Lnet_einval", "\tcmp x2, #0", "\tb.lt .Lnet_einval", "\tstr x2, [sp, #96]",
        "\tldr x0, [sp, #32]")
    add(*_adr("x1", "_sign_nbuf"))
    add("\tstr x1, [sp, #88]", "\tbl _sign_dev_pack",
        "1:", "\tldr x2, [sp, #96]", "\tcbz x2, 2f", "\tldr x0, [sp, #72]", "\tldr x1, [sp, #88]", "\tmov x3, #0x4000", "\tmov x4, #0", "\tmov x5, #0", "\tmov x8, #206", "\tsvc #0",
        "\tcmp x0, #0", "\tb.le .Lnet_sendend", "\tldr x1, [sp, #88]", "\tadd x1, x1, x0", "\tstr x1, [sp, #88]", "\tldr x2, [sp, #96]", "\tsub x2, x2, x0", "\tstr x2, [sp, #96]", "\tb 1b",
        "2:", "\tldr x0, [sp, #40]", "\tb .Lnet_ret",
        ".Lnet_sendend:", "\tcmp x0, #0", "\tb.lt .Lnet_ret", "\tmov x0, #-5", "\tb .Lnet_ret")
    # RECV(h, buf, n)
    add(".Lnet_recv:", *getfd)
    add("\tldr x2, [sp, #40]", "\tmov x3, #%d" % NBUF, "\tcmp x2, x3", "\tb.hi .Lnet_einval", "\tcmp x2, #0", "\tb.lt .Lnet_einval",
        "\tldr x5, [sp, #136]", "\tldr x1, [x5, #16]", "\tldr x0, [sp, #72]", "\tbl _sign_dev_nwait", "\tcmp x0, #0", "\tb.lt .Lnet_ret",
        "\tldr x0, [sp, #72]")
    add(*_adr("x1", "_sign_nbuf"))
    add("\tldr x2, [sp, #40]", "\tmov x3, #0x40", "\tmov x4, #0", "\tmov x5, #0", "\tmov x8, #207", "\tsvc #0", "\tcmp x0, #0", "\tb.le .Lnet_ret",
        "\tstr x0, [sp, #104]", "\tmov x2, x0")
    add(*_adr("x0", "_sign_nbuf"))
    add("\tldr x1, [sp, #32]", "\tbl _sign_dev_unpack", "\tldr x0, [sp, #104]", "\tb .Lnet_ret")
    # CLOSE(h)
    add(".Lnet_close:", *getfd)
    add("\tmov x8, #57", "\tsvc #0", "\tldr x5, [sp, #136]", "\tstr xzr, [x5]", "\tmov x0, #0", "\tb .Lnet_ret")
    # LISTEN(port, backlog)
    add(".Lnet_listen:", "\tldr x1, [sp, #24]", "\tmov x3, #65535", "\tcmp x1, x3", "\tb.hi .Lnet_einval", "\tcmp x1, #0", "\tb.lt .Lnet_einval",
        "\tmov x0, #2", "\tmov x1, #1", "\tmov x2, #0", "\tmov x8, #198", "\tsvc #0", "\tcmp x0, #0", "\tb.lt .Lnet_ret", "\tstr x0, [sp, #72]",
        "\tmov x1, #1", "\tstr x1, [sp, #112]", "\tmov x1, #1", "\tmov x2, #2", "\tadd x3, sp, #112", "\tmov x4, #4", "\tmov x8, #208", "\tsvc #0",
        "\tmov x0, #0", "\tldr x1, [sp, #24]", "\tadd x2, sp, #112", "\tbl _sign_dev_nsa",
        "\tldr x0, [sp, #72]", "\tadd x1, sp, #112", "\tmov x2, #16", "\tmov x8, #200", "\tsvc #0", "\tcmp x0, #0", "\tb.lt .Lnet_failclose",
        "\tldr x1, [sp, #32]", "\tcmp x1, #0", "\tb.gt 1f", "\tmov x1, #5", "1:", "\tcmp x1, #128", "\tb.ls 2f", "\tmov x1, #128",
        "2:", "\tldr x0, [sp, #72]", "\tmov x8, #201", "\tsvc #0", "\tcmp x0, #0", "\tb.lt .Lnet_failclose",
        "\tldr x0, [sp, #72]", "\tmov x1, #2", "\tbl _sign_dev_nnew", "\tb .Lnet_ret")
    # ACCEPT(h)
    add(".Lnet_accept:", *getfd)
    add("\tldr x5, [sp, #136]", "\tldr x4, [x5, #8]", "\tcmp x4, #2", "\tb.ne .Lnet_einval", "\tldr x1, [x5, #16]", "\tldr x0, [sp, #72]", "\tbl _sign_dev_nwait", "\tcmp x0, #0", "\tb.lt .Lnet_ret",
        "\tldr x0, [sp, #72]", "\tmov x1, #0", "\tmov x2, #0", "\tmov x8, #202", "\tsvc #0", "\tcmp x0, #0", "\tb.lt .Lnet_ret", "\tmov x1, #1", "\tbl _sign_dev_nnew", "\tb .Lnet_ret")
    # UDP_OPEN(port)
    add(".Lnet_udp:", "\tldr x1, [sp, #24]", "\tmov x3, #65535", "\tcmp x1, x3", "\tb.hi .Lnet_einval", "\tcmp x1, #0", "\tb.lt .Lnet_einval",
        "\tmov x0, #2", "\tmov x1, #2", "\tmov x2, #0", "\tmov x8, #198", "\tsvc #0", "\tcmp x0, #0", "\tb.lt .Lnet_ret", "\tstr x0, [sp, #72]",
        "\tmov x0, #0", "\tldr x1, [sp, #24]", "\tadd x2, sp, #112", "\tbl _sign_dev_nsa",
        "\tldr x0, [sp, #72]", "\tadd x1, sp, #112", "\tmov x2, #16", "\tmov x8, #200", "\tsvc #0", "\tcmp x0, #0", "\tb.lt .Lnet_failclose",
        "\tldr x0, [sp, #72]", "\tmov x1, #3", "\tbl _sign_dev_nnew", "\tb .Lnet_ret")
    # SENDTO(h, host, hlen, port, buf, n)
    add(".Lnet_sendto:", *getfd)
    add("\tldr x0, [sp, #32]", "\tldr x1, [sp, #40]", "\tbl _sign_dev_nhost", "\tcmp x0, #0", "\tb.lt .Lnet_ret", "\tstr x0, [sp, #80]",
        "\tldr x1, [sp, #48]", "\tsub x2, x1, #1", "\tmov x3, #65535", "\tcmp x2, x3", "\tb.hs .Lnet_einval",
        "\tldr x2, [sp, #64]", "\tmov x3, #%d" % NBUF, "\tcmp x2, x3", "\tb.hi .Lnet_einval", "\tcmp x2, #0", "\tb.lt .Lnet_einval",
        "\tldr x0, [sp, #56]")
    add(*_adr("x1", "_sign_nbuf"))
    add("\tldr x2, [sp, #64]", "\tbl _sign_dev_pack", "\tldr x0, [sp, #80]", "\tldr x1, [sp, #48]", "\tadd x2, sp, #112", "\tbl _sign_dev_nsa",
        "\tldr x0, [sp, #72]")
    add(*_adr("x1", "_sign_nbuf"))
    add("\tldr x2, [sp, #64]", "\tmov x3, #0x4000", "\tadd x4, sp, #112", "\tmov x5, #16", "\tmov x8, #206", "\tsvc #0", "\tb .Lnet_ret")
    # RECVFROM(h, buf, n, from_buf)
    add(".Lnet_recvfrom:", *getfd)
    add("\tldr x2, [sp, #40]", "\tmov x3, #%d" % NBUF, "\tcmp x2, x3", "\tb.hi .Lnet_einval", "\tcmp x2, #0", "\tb.lt .Lnet_einval",
        "\tldr x5, [sp, #136]", "\tldr x1, [x5, #16]", "\tldr x0, [sp, #72]", "\tbl _sign_dev_nwait", "\tcmp x0, #0", "\tb.lt .Lnet_ret",
        "\tmov x1, #16", "\tstr x1, [sp, #128]", "\tldr x0, [sp, #72]")
    add(*_adr("x1", "_sign_nbuf"))
    add("\tldr x2, [sp, #40]", "\tmov x3, #0x40", "\tadd x4, sp, #112", "\tadd x5, sp, #128", "\tmov x8, #207", "\tsvc #0", "\tcmp x0, #0", "\tb.lt .Lnet_ret",
        "\tstr x0, [sp, #104]", "\tmov x2, x0")
    add(*_adr("x0", "_sign_nbuf"))
    add("\tldr x1, [sp, #32]", "\tbl _sign_dev_unpack",
        "\tldr w0, [sp, #116]")
    add(*_adr("x1", "_sign_nhs"))
    add("\tbl _sign_dev_nip", "\tmov x2, #58", "\tstrb w2, [x1]", "\tadd x1, x1, #1", "\tstr x1, [sp, #88]", "\tldrh w0, [sp, #114]", "\tbl _sign_dev_nbe",
        "\tldr x1, [sp, #88]", "\tbl _sign_dev_nu", "\tstrb wzr, [x1]", "\tadd x1, x1, #1")
    add(*_adr("x0", "_sign_nhs"))
    add("\tsub x2, x1, x0", "\tldr x1, [sp, #48]", "\tbl _sign_dev_unpack", "\tldr x0, [sp, #104]", "\tb .Lnet_ret")
    # SETTIMEOUT(h, ms)
    add(".Lnet_settmo:", *getfd)
    add("\tldr x1, [sp, #32]", "\tcmp x1, #0", "\tb.lt .Lnet_einval", "\tldr x5, [sp, #136]", "\tstr x1, [x5, #16]", "\tmov x0, #0", "\tb .Lnet_ret")
    # RESOLVE(host, len, out)
    add(".Lnet_resolve:", "\tldr x0, [sp, #24]", "\tldr x1, [sp, #32]", "\tbl _sign_dev_nhost", "\tcmp x0, #0", "\tb.lt .Lnet_ret")
    add(*_adr("x1", "_sign_nhs"))
    add("\tbl _sign_dev_nip", "\tstrb wzr, [x1]")
    add(*_adr("x0", "_sign_nhs"))
    add("\tsub x2, x1, x0", "\tstr x2, [sp, #104]", "\tadd x2, x2, #1", "\tldr x1, [sp, #40]", "\tbl _sign_dev_unpack", "\tldr x0, [sp, #104]", "\tb .Lnet_ret")
    # PORT(h)
    add(".Lnet_port:", *getfd)
    add("\tmov x1, #16", "\tstr x1, [sp, #128]", "\tldr x0, [sp, #72]", "\tadd x1, sp, #112", "\tadd x2, sp, #128", "\tmov x8, #204", "\tsvc #0", "\tcmp x0, #0", "\tb.lt .Lnet_ret",
        "\tldrh w0, [sp, #114]", "\tbl _sign_dev_nbe", "\tb .Lnet_ret")
    # TLS_START(h, host, len)
    add(".Lnet_tls:", *getfd)
    add("\tmov x0, #-38", "\tb .Lnet_ret", "")
    return L


def data_lines():
    rodata = ["_sign_nlh:", "\t.byte " + ", ".join(str(b) for b in b"localhost"),
              "_sign_dns_path:", "\t.byte " + ", ".join(str(b) for b in b"/etc/resolv.conf\0"),
              "_sign_dns_kw:", "\t.byte " + ", ".join(str(b) for b in b"nameserver"),
              "_sign_dns_hdr:", "\t.byte " + ", ".join(str(b) for b in bytes([0x5A, 0x1D, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0]))]
    bss = []
    for n, sz in (("_sign_nbuf", NBUF), ("_sign_nhs", 512), ("_sign_nh", 32 * 24), ("_sign_dnsq", 600), ("_sign_dnsr", 600), ("_sign_dnsc", 2048)):
        bss += ["%s:" % n, "\t.skip %d" % sz]
    return rodata, bss
