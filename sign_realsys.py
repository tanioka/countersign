"""sign_realsys.py — `--real-dev` のシステムコール装置(0x9400000)の中継ルーチン(AArch64 アセンブリ)。

番号と引数を影レジスタ(NR 0, ARG0 4, ARG1 8, ARG2 0xC, GO 0x14, RET 0x18)に書き、GO で Linux のシステムコールに置き換える。
  1 READ  read(63)(fd 0 = 標準入力。ある分だけ、1 バイト以上待つ)/ 2 WRITE  write(64)(fd 1・2 = 標準出力・標準エラー。全部書くまで繰り返す)
  3 OPEN  openat2(437)で開く(mode 0 読む / 1 書く(作り直す)/ 2 足して書く)。RESOLVE_BENEATH(0x08)なので、カレントディレクトリの外へ出る
          (絶対パス・`..`・外へ向かうシンボリックリンク)と EXDEV で失敗し、それを -13(EACCES)にそろえる。5.6 以上の Linux が要る(無ければ -38)。
  4 CLOSE close(57)/ 5 TIME_S・6 TIME_MS  clock_gettime(113)(REALTIME)/ 7 SIZE  openat2 → lseek(62, SEEK_END) → close
fd は 3〜18(表 16 個の位置 + 3。閉じたら再利用)。あふれると -24。1 回の入出力は 1 MiB まで、パスは 1024 バイトまで(超えは -22)。
処理系との違い: 作業フォルダの「中」の判定はカーネルが行う(カレントディレクトリが root)/ パスが UTF-8 として正しいかは調べない /
  ディレクトリを OPEN(読む)しても成功し、READ が -21(EISDIR)になる(処理系は OPEN が -22)。
これは実装の決めで、仕様に定めはない。実機では未実行(疑似カーネルで確認)。
"""

MAXIO = 1 << 20
SBUF = MAXIO


def _imm(reg, v):
    from sign_asm import emit_imm
    out = []; emit_imm(out, reg, v); return out


def _adr(reg, sym):
    return ["\tadrp %s, %s" % (reg, sym), "\tadd %s, %s, :lo12:%s" % (reg, reg, sym)]


def shim():
    L = []
    add = lambda *xs: L.extend(xs)
    add("// ===== sys (0x94…) =====", "")
    # x0 = 語の列, x1 = 長さ(1〜1024 と確認済み)→ _sign_sbuf にバイトを詰めて 0 終わりにする。x0 = 0 か -22(0 のバイトを含む)
    add("_sign_dev_spath:", "\tstp x29, x30, [sp, #-32]!", "\tmov x29, sp", "\tstr x1, [sp, #16]", "\tmov x2, x1")
    add(*_adr("x1", "_sign_sbuf"))
    add("\tbl _sign_dev_pack", "\tldr x1, [sp, #16]")
    add(*_adr("x2", "_sign_sbuf"))
    add("\tadd x3, x2, x1", "1:", "\tcmp x2, x3", "\tb.hs 2f", "\tldrb w4, [x2]", "\tcbz x4, 3f", "\tadd x2, x2, #1", "\tb 1b",
        "2:", "\tstrb wzr, [x3]", "\tmov x0, #0", "\tb 4f", "3:", "\tmov x0, #-22", "4:", "\tldp x29, x30, [sp], #32", "\tret", "")
    # x0 = 引数の fd(3〜18)→ x0 = 本物の fd か -9, x5 = 表の項
    add("_sign_dev_sfd:", "\tsub x1, x0, #3", "\tcmp x1, #16", "\tb.hs 1f")
    add(*_adr("x2", "_sign_sfd"))
    add("\tlsl x3, x1, #3", "\tadd x5, x2, x3", "\tldr x4, [x5]", "\tcbz x4, 1f", "\tsub x0, x4, #1", "\tret", "1:", "\tmov x0, #-9", "\tret", "")
    # 空きの項を探す → x0 = 位置(0〜15)か -24, x5 = 項
    add("_sign_dev_sfree:")
    add(*_adr("x2", "_sign_sfd"))
    add("\tmov x1, #0", "1:", "\tlsl x3, x1, #3", "\tadd x5, x2, x3", "\tldr x4, [x5]", "\tcbz x4, 2f", "\tadd x1, x1, #1", "\tcmp x1, #16", "\tb.ne 1b", "\tmov x0, #-24", "\tret",
        "2:", "\tmov x0, x1", "\tret", "")
    # openat2: x0 = mode(0 読む / 1 / 2)→ x0 = fd か -errno(パスは _sign_sbuf)
    add("_sign_dev_open2:", "\tstp x29, x30, [sp, #-64]!", "\tmov x29, sp", "\tmov x1, #0", "\tmov x2, #0", "\tcmp x0, #0", "\tb.eq 1f",
        "\tmov x1, #0x241", "\tmov x2, #0x1A4", "\tcmp x0, #1", "\tb.eq 1f", "\tmov x1, #0x441",
        "1:", "\tstr x1, [sp, #16]", "\tstr x2, [sp, #24]", "\tmov x3, #8", "\tstr x3, [sp, #32]",
        "\tmov x0, #-100")
    add(*_adr("x1", "_sign_sbuf"))
    add("\tadd x2, sp, #16", "\tmov x3, #24", "\tmov x8, #437", "\tsvc #0", "\tmov x2, #-18", "\tcmp x0, x2", "\tb.ne 2f", "\tmov x0, #-13",
        "2:", "\tldp x29, x30, [sp], #64", "\tret", "")
    # 本体。枠: +16 NR, +24 a0, +32 a1, +40 a2, +48 fd, +56 補助, +64 timespec(16)
    add("_sign_dev_sys:", "\tstp x29, x30, [sp, #-96]!", "\tmov x29, sp", "\tstr x0, [sp, #16]")
    add(*_adr("x11", "_sign_dreg"))
    add("\tadd x11, x11, #0x4000")
    for i in range(3):
        add("\tldr w1, [x11, #%d]" % (4 + 4 * i), "\tstr x1, [sp, #%d]" % (24 + 8 * i))
    for n, name in ((1, "read"), (2, "write"), (3, "open"), (4, "close"), (5, "times"), (6, "timems"), (7, "size")):
        add("\tcmp x0, #%d" % n, "\tb.eq .Lsys_%s" % name)
    add("\tmov x0, #-38", "\tb .Lsys_ret", ".Lsys_einval:", "\tmov x0, #-22", ".Lsys_ret:", "\tldp x29, x30, [sp], #96", "\tret", "")
    # 時刻
    add(".Lsys_times:", "\tmov x0, #0", "\tadd x1, sp, #64", "\tmov x8, #113", "\tsvc #0", "\tldr x0, [sp, #64]", "\tb .Lsys_ret",
        ".Lsys_timems:", "\tmov x0, #0", "\tadd x1, sp, #64", "\tmov x8, #113", "\tsvc #0", "\tldr x0, [sp, #64]", "\tmov x1, #1000", "\tmul x0, x0, x1",
        "\tldr x2, [sp, #72]", "\tmov x3, #1000", "\tmul x3, x3, x1", "\tudiv x2, x2, x3", "\tadd x0, x0, x2", "\tb .Lsys_ret")
    # 入出力の共通: fd → x0(0 なら標準入力の読み、1・2 は書きのみ)
    add(".Lsys_read:", "\tldr x2, [sp, #40]")
    add(*_imm("x3", MAXIO))
    add("\tcmp x2, x3", "\tb.hi .Lsys_einval", "\tldr x0, [sp, #24]", "\tcbz x0, 1f", "\tcmp x0, #3", "\tb.hs 2f", "\tmov x0, #-9", "\tb .Lsys_ret",
        "2:", "\tbl _sign_dev_sfd", "\tcmp x0, #0", "\tb.lt .Lsys_ret", "1:")
    add(*_adr("x1", "_sign_sbuf"))
    add("\tldr x2, [sp, #40]", "\tmov x8, #63", "\tsvc #0", "\tcmp x0, #0", "\tb.le .Lsys_ret", "\tstr x0, [sp, #56]", "\tmov x2, x0")
    add(*_adr("x0", "_sign_sbuf"))
    add("\tldr x1, [sp, #32]", "\tbl _sign_dev_unpack", "\tldr x0, [sp, #56]", "\tb .Lsys_ret")
    add(".Lsys_write:", "\tldr x2, [sp, #40]")
    add(*_imm("x3", MAXIO))
    add("\tcmp x2, x3", "\tb.hi .Lsys_einval", "\tldr x0, [sp, #24]", "\tcbnz x0, 1f", "\tmov x0, #-9", "\tb .Lsys_ret",
        "1:", "\tcmp x0, #3", "\tb.hs 2f", "\tstr x0, [sp, #48]", "\tb 3f", "2:", "\tbl _sign_dev_sfd", "\tcmp x0, #0", "\tb.lt .Lsys_ret", "\tstr x0, [sp, #48]",
        "3:", "\tldr x0, [sp, #32]")
    add(*_adr("x1", "_sign_sbuf"))
    add("\tldr x2, [sp, #40]", "\tbl _sign_dev_pack", "\tldr x3, [sp, #40]", "\tstr x3, [sp, #56]")
    add(*_adr("x4", "_sign_sbuf"))
    add("\tstr x4, [sp, #64]",
        "4:", "\tldr x2, [sp, #56]", "\tcbz x2, 5f", "\tldr x0, [sp, #48]", "\tldr x1, [sp, #64]", "\tmov x8, #64", "\tsvc #0", "\tcmp x0, #0", "\tb.le .Lsys_wend",
        "\tldr x1, [sp, #64]", "\tadd x1, x1, x0", "\tstr x1, [sp, #64]", "\tldr x2, [sp, #56]", "\tsub x2, x2, x0", "\tstr x2, [sp, #56]", "\tb 4b",
        "5:", "\tldr x0, [sp, #40]", "\tb .Lsys_ret",
        ".Lsys_wend:", "\tcmp x0, #0", "\tb.lt .Lsys_ret", "\tmov x0, #-5", "\tb .Lsys_ret")
    # OPEN(path, len, mode)
    add(".Lsys_open:", "\tldr x2, [sp, #40]", "\tcmp x2, #2", "\tb.hi .Lsys_einval", "\tbl _sign_dev_sfree", "\tcmp x0, #0", "\tb.lt .Lsys_ret", "\tstr x0, [sp, #56]", "\tstr x5, [sp, #48]",
        "\tldr x1, [sp, #32]", "\tsub x2, x1, #1", "\tcmp x2, #1024", "\tb.hs .Lsys_einval", "\tldr x0, [sp, #24]", "\tbl _sign_dev_spath", "\tcmp x0, #0", "\tb.lt .Lsys_ret",
        "\tldr x0, [sp, #40]", "\tbl _sign_dev_open2", "\tcmp x0, #0", "\tb.lt .Lsys_ret", "\tadd x0, x0, #1", "\tldr x5, [sp, #48]", "\tstr x0, [x5]", "\tldr x0, [sp, #56]", "\tadd x0, x0, #3", "\tb .Lsys_ret")
    # CLOSE(fd)
    add(".Lsys_close:", "\tldr x0, [sp, #24]", "\tbl _sign_dev_sfd", "\tcmp x0, #0", "\tb.lt .Lsys_ret", "\tstr x5, [sp, #48]", "\tmov x8, #57", "\tsvc #0",
        "\tldr x5, [sp, #48]", "\tstr xzr, [x5]", "\tmov x0, #0", "\tb .Lsys_ret")
    # SIZE(path, len)
    add(".Lsys_size:", "\tldr x1, [sp, #32]", "\tsub x2, x1, #1", "\tcmp x2, #1024", "\tb.hs .Lsys_einval", "\tldr x0, [sp, #24]", "\tbl _sign_dev_spath", "\tcmp x0, #0", "\tb.lt .Lsys_ret",
        "\tmov x0, #0", "\tbl _sign_dev_open2", "\tcmp x0, #0", "\tb.lt .Lsys_ret", "\tstr x0, [sp, #48]", "\tmov x1, #0", "\tmov x2, #2", "\tmov x8, #62", "\tsvc #0", "\tstr x0, [sp, #56]",
        "\tldr x0, [sp, #48]", "\tmov x8, #57", "\tsvc #0", "\tldr x0, [sp, #56]", "\tb .Lsys_ret", "")
    return L


def data_lines():
    return [], ["_sign_sbuf:", "\t.skip %d" % (SBUF + 8), "_sign_sfd:", "\t.skip %d" % (16 * 8)]
