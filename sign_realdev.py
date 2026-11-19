"""sign_realdev.py — `--target=linux --real-dev` で足す、実機の装置の中継ルーチン(AArch64 アセンブリ)。

処理系の仮想装置の番地(0x9000000 以上)への `a # v` と `@a` を、実行時にここへ回す。実機(Raspberry Pi OS)では番地そのものは実在しないので、
  - レジスタは .bss の「影」に持ち、GO などの引き金の書き込みで、本物の Linux のシステムコールに置き換える。
  - I2C   0x96…  /dev/i2c-N を openat → ioctl(I2C_SLAVE か I2C_RDWR) → read/write → close(転送ごとに開け閉めする)。バッファは 1 語 = 1 バイト(4 バイト刻み)。
  - GPIO  0x95…  /dev/gpiochip0 の GPIO v2(GPIO_V2_GET_LINE_IOCTL / GET・SET_VALUES)。ピンごとに行(line)の fd を持つ。PWM(向き 4・0x200・0x300)は未対応(無視)。
  - 時計  0x92…  NOW = clock_gettime(MONOTONIC)(初回呼びからのミリ秒)、SLEEP = nanosleep。アラーム(ID・AFTER・EVERY・CANCEL)は 16 個の表で持つ。鳴ったものを取り出す DUE(0x9200018 の読み)はこの実装の足しで、ゲーム機の周期(--real-dev で tick を持つプログラム)が使う。
  - UART  0x9000000  書き込み = 標準出力(Char 幅 4 の utf32 は UTF-8、それ以外は下位 1 バイト)、読み = 標準入力 1 バイト(終わりは __)。
  - SPI   0x97…  /dev/spidevB.C を openat → ioctl(SPI_IOC_WR_MODE)・ioctl(SPI_IOC_MESSAGE(1)) → close(転送ごとに開け閉め。1 バイトずつ 8 ビット)。
  - ネット  0x99…  TCP・UDP のソケット(sign_realnet.py)。TLS は未対応(-38)、名前は IPv4 の数字と localhost だけ。
  - sys  0x94…  標準入出力・時刻・ファイル(sign_realsys.py。カレントディレクトリの外は openat2 RESOLVE_BENEATH で断る)。
  - DB  0x9A…  `--real-db` のときだけ。GO で C の long sign_db_call(const unsigned long *r)(sign_db.c、libsqlite3)を呼ぶ。gcc でリンクする(sign.py --pi-bundle=DIR)。
  - 入力  0x93…  /dev/input/event0〜31(evdev。sign_realinput.py。キーとマウスの出来事を輪に入れる)。
  - 描画  0x91…  論理画面(.bss)+ PRESENT で /dev/fb0(sign_realgfx.py)。音  0x98…  aplay の子プロセス(sign_realsound.py)。: 書き込みは捨て、読みは 0。
  - 低い番地の作業メモリ: 起動時に [0x10000, 0x9000000) を mmap(匿名・NORESERVE・FIXED_NOREPLACE)で確保する。ELF は --image-base=0x10000000 でその外に置く(--elf は自動)。0x10000 未満(mmap_min_addr の下)は使えない。
これは実装の決めで、仕様に定めはない。実機では未実行(エミュレータの疑似カーネルで確認)。
呼び出しの約束: _sign_dev_st は x9 = 番地, x0 = 値, x1 = 幅(4 か 8)で、x9 を保つ。_sign_dev_ld は x0 = 番地, x1 = 幅で、x0 に値を返す。
"""

I2C_SLAVE, I2C_RDWR = 0x0703, 0x0707
GPIO_GET_LINE, GPIO_GET_VALUES, GPIO_SET_VALUES = 0xC250B407, 0xC010B40E, 0xC010B40F
NICHE = 0x8000000000000000
MAPMSG = b"sign: cannot map work memory at 0x10000-0x9000000 (link with --image-base above it; check vm.overcommit_memory and mmap_min_addr)\n"


def _imm(reg, v):
    from sign_asm import emit_imm
    out = []; emit_imm(out, reg, v); return out


def _adr(reg, sym):
    return ["\tadrp %s, %s" % (reg, sym), "\tadd %s, %s, :lo12:%s" % (reg, reg, sym)]


def shim(utf8_putc, cw, db=False, gfx=None):
    """utf8_putc: 変換つきの _sign_putc の行(utf32 のとき)。ascii のときは使わない。"""
    L = []
    a = L.append
    def add(*xs): L.extend(xs)

    add("// ===== 実機の装置の中継 (--real-dev) =====", "")
    add("// 低い番地の作業メモリ: [0x10000, 0x9000000) を匿名メモリで確保する(プログラムが `0x7C0000` のような絶対番地を作業場に使うため)。",
        "// ELF は --image-base=0x10000000 などでこの外に置く。確保できなければ理由を標準エラーに出して exit(1)。",
        "_sign_dev_map:", "\tldr x9, [sp]", "\tadd x10, sp, #16", "\tadd x10, x10, x9, lsl #3", "\tadrp x11, _sign_envp", "\tadd x11, x11, :lo12:_sign_envp", "\tstr x10, [x11]",     # 環境変数の表(音の aplay に渡す)
        "\tmov x0, #0x10000")
    add(*_imm("x1", 0x9000000 - 0x10000))
    add("\tmov x2, #3")
    add(*_imm("x3", 0x2 | 0x20 | 0x4000 | 0x100000))              # PRIVATE | ANONYMOUS | NORESERVE | FIXED_NOREPLACE
    add("\tmov x4, #-1", "\tmov x5, #0", "\tmov x8, #222", "\tsvc #0", "\tmov x10, #0x10000", "\tcmp x0, x10", "\tb.ne 1f", "\tret", "1:",
        "\tmov x0, #2")
    add(*_adr("x1", "_sign_dev_mapmsg"))
    add("\tmov x2, #%d" % len(MAPMSG), "\tmov x8, #64", "\tsvc #0", "\tmov x0, #1", "\tmov x8, #93", "\tsvc #0", "")
    # ---------- 影レジスタへの書き込み・読み(葉)----------
    add("// x11 = 影の先頭, x10 = 先頭からの位置, x0 = 値, x1 = 幅",
        "_sign_dev_sh_st:", "\tadd x12, x11, x10", "\tcmp x1, #4", "\tb.ne 1f", "\tstr w0, [x12]", "\tret", "1:", "\tstr x0, [x12]", "\tret", "",
        "_sign_dev_sh_ld:", "\tadd x12, x11, x10", "\tcmp x1, #4", "\tb.ne 1f", "\tldr w0, [x12]", "\tret", "1:", "\tldr x0, [x12]", "\tret", "")
    # ---------- バイト列 <-> 語の列 ----------
    add("// x0 = 語の列(4 バイト刻み), x1 = バイト列, x2 = 個数 : 各語の下位 1 バイトを詰める",
        "_sign_dev_pack:", "\tcbz x2, 2f", "1:", "\tldr w3, [x0]", "\tstrb w3, [x1]", "\tadd x0, x0, #4", "\tadd x1, x1, #1", "\tsub x2, x2, #1", "\tcbnz x2, 1b", "2:", "\tret", "",
        "// x0 = バイト列, x1 = 語の列(4 バイト刻み), x2 = 個数 : 1 バイトずつ 1 語に広げる",
        "_sign_dev_unpack:", "\tcbz x2, 2f", "1:", "\tldrb w3, [x0]", "\tstr w3, [x1]", "\tadd x0, x0, #1", "\tadd x1, x1, #4", "\tsub x2, x2, #1", "\tcbnz x2, 1b", "2:", "\tret", "")
    # ---------- I2C ----------
    # 結果は x0(0 以上 = 成功、負 = -errno)。cmd = x0
    add("// I2C: x0 = 命令番号(1 WRITE / 2 READ / 3 WRITE_READ / 4 PROBE)。影の ADDR BUF LEN RDLEN BUS を読む。結果 = 長さか -errno",
        "_sign_dev_i2c:", "\tstp x29, x30, [sp, #-160]!", "\tmov x29, sp", "\tstr x0, [sp, #24]")
    add(*_adr("x11", "_sign_dreg"))
    add("\tldr w1, [x11, #0]", "\tstr x1, [sp, #32]", "\tldr w1, [x11, #4]", "\tstr x1, [sp, #40]", "\tldr w1, [x11, #8]", "\tstr x1, [sp, #48]",
        "\tldr w1, [x11, #12]", "\tstr x1, [sp, #56]", "\tldr w1, [x11, #16]", "\tstr x1, [sp, #64]",
        "\tcmp x0, #1", "\tb.lo .Ldi_inval", "\tcmp x0, #4", "\tb.hi .Ldi_inval",
        "\tldr x1, [sp, #32]", "\tcmp x1, #127", "\tb.hi .Ldi_inval",
        "\tmov x2, #4096", "\tldr x1, [sp, #48]", "\tcmp x1, x2", "\tb.hi .Ldi_inval",
        "\tcmp x0, #3", "\tb.ne 1f", "\tldr x1, [sp, #56]", "\tcmp x1, x2", "\tb.hi .Ldi_inval", "1:",
        "\tcmp x0, #1", "\tb.ne 2f", "\tldr x1, [sp, #48]", "\tcbz x1, .Ldi_zero", "2:",
        "\tldr x1, [sp, #64]", "\tcmp x1, #99", "\tb.hi .Ldi_nodev")
    add("// パス \"/dev/i2c-N\"")
    add(*_imm("x1", 0x6332692F7665642F))                                    # "/dev/i2c"
    add("\tstr x1, [sp, #72]", "\tmov w5, #0x2d", "\tstrb w5, [sp, #80]",
        "\tldr x1, [sp, #64]", "\tmov x2, #10", "\tudiv x3, x1, x2", "\tmsub x4, x3, x2, x1",
        "\tcbz x3, 3f", "\tadd w5, w3, #48", "\tstrb w5, [sp, #81]", "\tadd w5, w4, #48", "\tstrb w5, [sp, #82]", "\tstrb wzr, [sp, #83]", "\tb 4f",
        "3:", "\tadd w5, w4, #48", "\tstrb w5, [sp, #81]", "\tstrb wzr, [sp, #82]", "4:",
        "\tmov x0, #-100", "\tadd x1, sp, #72", "\tmov x2, #2", "\tmov x3, #0", "\tmov x8, #56", "\tsvc #0",
        "\tcmp x0, #0", "\tb.lt .Ldi_ret", "\tstr x0, [sp, #16]",
        "\tldr x1, [sp, #24]", "\tcmp x1, #3", "\tb.eq .Ldi_rdwr",
        "\tldr x0, [sp, #16]")
    add(*_imm("x1", I2C_SLAVE))
    add("\tldr x2, [sp, #32]", "\tmov x8, #29", "\tsvc #0", "\tcmp x0, #0", "\tb.lt .Ldi_close",
        "\tldr x1, [sp, #24]", "\tcmp x1, #1", "\tb.eq .Ldi_wr", "\tcmp x1, #2", "\tb.eq .Ldi_rd",
        "// 4 PROBE: 1 バイト読めれば 0。読めなければ理由を問わず -6(応答しない)",
        "\tldr x0, [sp, #16]")
    add(*_adr("x1", "_sign_drd"))
    add("\tmov x2, #1", "\tmov x8, #63", "\tsvc #0", "\tcmp x0, #0", "\tb.ge 1f", "\tmov x0, #-6", "\tb .Ldi_close", "1:", "\tmov x0, #0", "\tb .Ldi_close",       # 応答しない = どの失敗も -6(実機の bcm2835 は -5、RDWR だと -121 を返し、見分けられない)
        ".Ldi_wr:", "\tldr x0, [sp, #40]")
    add(*_adr("x1", "_sign_dwr"))
    add("\tldr x2, [sp, #48]", "\tbl _sign_dev_pack", "\tldr x0, [sp, #16]")
    add(*_adr("x1", "_sign_dwr"))
    add("\tldr x2, [sp, #48]", "\tmov x8, #64", "\tsvc #0", "\tcmp x0, #0", "\tb.lt .Ldi_close",
        "\tldr x1, [sp, #48]", "\tcmp x0, x1", "\tb.eq .Ldi_close", "\tmov x0, #-5", "\tb .Ldi_close",
        ".Ldi_rd:", "\tldr x0, [sp, #16]")
    add(*_adr("x1", "_sign_drd"))
    add("\tldr x2, [sp, #48]", "\tmov x8, #63", "\tsvc #0", "\tcmp x0, #0", "\tb.lt .Ldi_close",
        "\tldr x1, [sp, #48]", "\tcmp x0, x1", "\tb.eq 1f", "\tmov x0, #-5", "\tb .Ldi_close", "1:")
    add(*_adr("x0", "_sign_drd"))
    add("\tldr x1, [sp, #40]", "\tldr x2, [sp, #48]", "\tbl _sign_dev_unpack", "\tldr x0, [sp, #48]", "\tb .Ldi_close")
    add("// 3 WRITE_READ: I2C_RDWR で 2 つのメッセージ(間に STOP を入れない)。LEN = 0 なら読みだけ、RDLEN = 0 なら書きだけ",
        ".Ldi_rdwr:", "\tldr x1, [sp, #48]", "\tldr x2, [sp, #56]", "\torr x3, x1, x2", "\tcbz x3, .Ldi_zero_close",
        "\tldr x0, [sp, #40]")
    add(*_adr("x1", "_sign_dwr"))
    add("\tldr x2, [sp, #48]", "\tbl _sign_dev_pack",
        "\tldr x3, [sp, #32]",                                                 # msgs[0] = {addr, flags 0, len, pad, buf}
        "\tstrh w3, [sp, #96]", "\tstrh wzr, [sp, #98]", "\tldr x4, [sp, #48]", "\tstrh w4, [sp, #100]", "\tstrh wzr, [sp, #102]")
    add(*_adr("x5", "_sign_dwr"))
    add("\tstr x5, [sp, #104]",
        "\tstrh w3, [sp, #112]", "\tmov w6, #1", "\tstrh w6, [sp, #114]", "\tldr x4, [sp, #56]", "\tstrh w4, [sp, #116]", "\tstrh wzr, [sp, #118]")  # msgs[1] = 読み
    add(*_adr("x5", "_sign_drd"))
    add("\tstr x5, [sp, #120]",
        "\tadd x6, sp, #96", "\tmov x7, #2",                                    # 既定: 両方
        "\tldr x4, [sp, #48]", "\tcbnz x4, 1f", "\tadd x6, sp, #112", "\tmov x7, #1", "\tb 2f",      # LEN = 0: 読みだけ
        "1:", "\tldr x4, [sp, #56]", "\tcbnz x4, 2f", "\tmov x7, #1",                              # RDLEN = 0: 書きだけ
        "2:", "\tstr x6, [sp, #128]", "\tstr x7, [sp, #136]",
        "\tldr x0, [sp, #16]")
    add(*_imm("x1", I2C_RDWR))
    add("\tadd x2, sp, #128", "\tmov x8, #29", "\tsvc #0", "\tcmp x0, #0", "\tb.lt .Ldi_close",
        "\tldr x2, [sp, #56]", "\tcbz x2, 3f")
    add(*_adr("x0", "_sign_drd"))
    add("\tldr x1, [sp, #40]", "\tbl _sign_dev_unpack", "3:", "\tldr x0, [sp, #56]", "\tb .Ldi_close",
        ".Ldi_zero_close:", "\tmov x0, #0",
        ".Ldi_close:", "\tstr x0, [sp, #24]", "\tldr x0, [sp, #16]", "\tmov x8, #57", "\tsvc #0", "\tldr x0, [sp, #24]",
        ".Ldi_ret:", "\tldp x29, x30, [sp], #160", "\tret",
        ".Ldi_inval:", "\tmov x0, #-22", "\tb .Ldi_ret", ".Ldi_nodev:", "\tmov x0, #-19", "\tb .Ldi_ret", ".Ldi_zero:", "\tmov x0, #0", "\tb .Ldi_ret", "")
    add("// SPI の影の既定: SPEED 1 MHz(MODE・CS・BUS は 0)。最初の 1 回だけ",
        "_sign_dev_spi_init:")
    add(*_adr("x12", "_sign_dinit2"))
    add("\tldr x13, [x12]", "\tcbnz x13, 1f", "\tmov x13, #1", "\tstr x13, [x12]")
    add(*_adr("x11", "_sign_dreg"))
    add(*_imm("x14", 1000000))
    add("\tstr x14, [x11, #0x2008]", "1:", "\tret", "")
    # ---------- SPI ----------
    add("// SPI: x0 = 命令番号(1 TRANSFER)。影の BUF LEN SPEED MODE CS BUS を読む。結果 = 長さか -errno",
        "_sign_dev_spi:", "\tstp x29, x30, [sp, #-160]!", "\tmov x29, sp", "\tstr x0, [sp, #24]")
    add(*_adr("x11", "_sign_dreg"))
    add("\tadd x11, x11, #0x2000", "\tldr w1, [x11, #0]", "\tstr x1, [sp, #32]", "\tldr w1, [x11, #4]", "\tstr x1, [sp, #40]", "\tldr w1, [x11, #8]", "\tstr x1, [sp, #48]",
        "\tldr w1, [x11, #12]", "\tstr x1, [sp, #56]", "\tldr w1, [x11, #16]", "\tstr x1, [sp, #64]", "\tldr w1, [x11, #28]", "\tstr x1, [sp, #72]",
        "\tcmp x0, #1", "\tb.ne .Lsp_inval",
        "\tmov x2, #4096", "\tldr x1, [sp, #40]", "\tcmp x1, x2", "\tb.hi .Lsp_inval", "\tcbz x1, .Lsp_zero",
        "\tldr x1, [sp, #72]", "\tcmp x1, #9", "\tb.hi .Lsp_nodev",
        "// パス \"/dev/spidevB.C\"")
    add(*_imm("x1", 0x6970732F7665642F))                                    # "/dev/spi"
    add("\tstr x1, [sp, #80]", "\tmov w5, #0x64", "\tstrb w5, [sp, #88]", "\tmov w5, #0x65", "\tstrb w5, [sp, #89]", "\tmov w5, #0x76", "\tstrb w5, [sp, #90]",
        "\tldr x1, [sp, #72]", "\tadd w5, w1, #48", "\tstrb w5, [sp, #91]", "\tmov w5, #0x2e", "\tstrb w5, [sp, #92]",
        "\tldr x1, [sp, #64]", "\tadd w5, w1, #48", "\tstrb w5, [sp, #93]", "\tstrb wzr, [sp, #94]",
        "\tmov x0, #-100", "\tadd x1, sp, #80", "\tmov x2, #2", "\tmov x3, #0", "\tmov x8, #56", "\tsvc #0", "\tcmp x0, #0", "\tb.lt .Lsp_ret", "\tstr x0, [sp, #16]",
        "// モード(CPOL・CPHA)", "\tldr x1, [sp, #56]", "\tstrb w1, [sp, #96]", "\tldr x0, [sp, #16]")
    add(*_imm("x1", 0x40016B01))
    add("\tadd x2, sp, #96", "\tmov x8, #29", "\tsvc #0", "\tcmp x0, #0", "\tb.lt .Lsp_close",
        "\tldr x0, [sp, #32]")
    add(*_adr("x1", "_sign_dwr"))
    add("\tldr x2, [sp, #40]", "\tbl _sign_dev_pack",
        "// struct spi_ioc_transfer(32 バイト): tx_buf rx_buf len speed_hz delay_usecs bits_per_word …")
    add(*_adr("x5", "_sign_dwr"))
    add("\tstr x5, [sp, #104]")
    add(*_adr("x5", "_sign_drd"))
    add("\tstr x5, [sp, #112]", "\tldr x1, [sp, #40]", "\tstr w1, [sp, #120]", "\tldr x1, [sp, #48]", "\tstr w1, [sp, #124]",
        "\tstr xzr, [sp, #128]", "\tmov w5, #8", "\tstrb w5, [sp, #129]",
        "\tldr x0, [sp, #16]")
    add(*_imm("x1", 0x40206B00))
    add("\tadd x2, sp, #104", "\tmov x8, #29", "\tsvc #0", "\tcmp x0, #0", "\tb.lt .Lsp_close",
        "\tldr x1, [sp, #40]", "\tcmp x0, x1", "\tb.eq 1f", "\tmov x0, #-5", "\tb .Lsp_close", "1:")
    add(*_adr("x0", "_sign_drd"))
    add("\tldr x1, [sp, #32]", "\tldr x2, [sp, #40]", "\tbl _sign_dev_unpack", "\tldr x0, [sp, #40]",
        ".Lsp_close:", "\tstr x0, [sp, #24]", "\tldr x0, [sp, #16]", "\tmov x8, #57", "\tsvc #0", "\tldr x0, [sp, #24]",
        ".Lsp_ret:", "\tldp x29, x30, [sp], #160", "\tret",
        ".Lsp_inval:", "\tmov x0, #-22", "\tb .Lsp_ret", ".Lsp_nodev:", "\tmov x0, #-19", "\tb .Lsp_ret", ".Lsp_zero:", "\tmov x0, #0", "\tb .Lsp_ret", "")
    # ---------- GPIO ----------
    add("// GPIO の行の要求: x0 = ピン, x1 = フラグ(INPUT 4 / OUTPUT 8 / +PULL_UP 0x100 / +PULL_DOWN 0x200)。結果 0 か負",
        "_sign_dev_gp_req:", "\tstp x29, x30, [sp, #-48]!", "\tmov x29, sp", "\tstp x0, x1, [sp, #16]")
    add(*_adr("x2", "_sign_gfd"))
    add("\tldr x3, [sp, #16]", "\tlsl x3, x3, #3", "\tadd x2, x2, x3", "\tstr x2, [sp, #32]",
        "\tldr x0, [x2]", "\tcbz x0, 1f", "\tsub x0, x0, #1", "\tmov x8, #57", "\tsvc #0", "\tldr x2, [sp, #32]", "\tstr xzr, [x2]", "1:",
        "\tmov x0, #-100")
    add(*_adr("x1", "_sign_dev_gchip"))
    add("\tmov x2, #2", "\tmov x3, #0", "\tmov x8, #56", "\tsvc #0", "\tcmp x0, #0", "\tb.lt .Ldg_ret", "\tstr x0, [sp, #40]")
    add(*_adr("x4", "_sign_greq"))
    add("\tmov x5, #74", "\tmov x6, x4", "2:", "\tstr xzr, [x6]", "\tadd x6, x6, #8", "\tsub x5, x5, #1", "\tcbnz x5, 2b",
        "\tldr x1, [sp, #16]", "\tstr w1, [x4]", "\tmov x6, #0x6973", "\tmovk x6, #0x6e67, lsl #16", "\tstr w6, [x4, #256]",
        "\tldr x1, [sp, #24]", "\tstr x1, [x4, #288]", "\tmov x6, #1", "\tstr w6, [x4, #560]", "\tldr x0, [sp, #40]")
    add(*_imm("x1", GPIO_GET_LINE))
    add("\tmov x2, x4", "\tmov x8, #29", "\tsvc #0", "\tstr x0, [sp, #24]", "\tldr x0, [sp, #40]", "\tmov x8, #57", "\tsvc #0",
        "\tldr x0, [sp, #24]", "\tcmp x0, #0", "\tb.lt .Ldg_ret")
    add(*_adr("x4", "_sign_greq"))
    add("\tldr w5, [x4, #588]", "\tadd x5, x5, #1", "\tldr x2, [sp, #32]", "\tstr x5, [x2]", "\tmov x0, #0",
        ".Ldg_ret:", "\tldp x29, x30, [sp], #48", "\tret", "")
    add("// GPIO: x0 = 操作(0 向きを設定 / 1 値を書く / 2 値を読む), x1 = ピン, x2 = 引数(0: フラグ, 1: 値)",
        "_sign_dev_gp:", "\tstp x29, x30, [sp, #-80]!", "\tmov x29, sp", "\tstp x0, x1, [sp, #16]", "\tstr x2, [sp, #32]")
    add(*_adr("x3", "_sign_gst"))
    add("\tadd x3, x3, x1", "\tstr x3, [sp, #40]", "\tcbnz x0, 1f",
        "\tmov x0, x1", "\tmov x1, x2", "\tbl _sign_dev_gp_req", "\tcmp x0, #0", "\tb.lt .Ldp_end",
        "\tldr x3, [sp, #40]", "\tldr x2, [sp, #32]", "\tmov w4, #1", "\ttbz x2, #3, 5f", "\tmov w4, #2", "5:", "\tstrb w4, [x3]", "\tb .Ldp_end",
        "1:", "\tldr x3, [sp, #40]", "\tldrb w4, [x3]", "\tcmp x0, #1", "\tb.ne .Ldp_read",
        "\tcmp w4, #2", "\tb.eq .Ldp_setv", "\tldr x0, [sp, #24]", "\tmov x1, #8", "\tbl _sign_dev_gp_req", "\tcmp x0, #0", "\tb.lt .Ldp_end",
        "\tldr x3, [sp, #40]", "\tmov w4, #2", "\tstrb w4, [x3]",
        ".Ldp_setv:", "\tldr x2, [sp, #32]", "\tmov x4, #0", "\tcbz x2, 6f", "\tmov x4, #1", "6:", "\tstr x4, [sp, #48]", "\tmov x5, #1", "\tstr x5, [sp, #56]")
    add(*_adr("x6", "_sign_gfd"))
    add("\tldr x7, [sp, #24]", "\tlsl x7, x7, #3", "\tldr x0, [x6, x7]", "\tsub x0, x0, #1")
    add(*_imm("x1", GPIO_SET_VALUES))
    add("\tadd x2, sp, #48", "\tmov x8, #29", "\tsvc #0", "\tb .Ldp_end",
        ".Ldp_read:", "\tcbnz w4, 7f", "\tldr x0, [sp, #24]", "\tmov x1, #4", "\tbl _sign_dev_gp_req", "\tcmp x0, #0", "\tb.lt .Ldp_end",
        "\tldr x3, [sp, #40]", "\tmov w4, #1", "\tstrb w4, [x3]", "7:", "\tstr xzr, [sp, #48]", "\tmov x5, #1", "\tstr x5, [sp, #56]")
    add(*_adr("x6", "_sign_gfd"))
    add("\tldr x7, [sp, #24]", "\tlsl x7, x7, #3", "\tldr x0, [x6, x7]", "\tsub x0, x0, #1")
    add(*_imm("x1", GPIO_GET_VALUES))
    add("\tadd x2, sp, #48", "\tmov x8, #29", "\tsvc #0", "\tcmp x0, #0", "\tb.lt .Ldp_end", "\tldr x0, [sp, #48]", "\tand x0, x0, #1",
        ".Ldp_end:", "\tldp x29, x30, [sp], #80", "\tret", "")
    # ---------- UART の出力(変換つき)----------
    add("// x0 の下位 1 バイト(utf32 で幅 4 のときは符号位置 → UTF-8)を標準出力へ")
    add(*utf8_putc)
    add("")
    add("// 時計: 最初に触れた時からのミリ秒(最初の呼びで基準を決める)→ x0",
        "_sign_dev_tnow:", "\tstp x29, x30, [sp, #-48]!", "\tmov x29, sp", "\tmov x0, #1", "\tadd x1, sp, #16", "\tmov x8, #113", "\tsvc #0",
        "\tldr x2, [sp, #16]", "\tldr x3, [sp, #24]", "\tmov x4, #1000", "\tmul x2, x2, x4", "\tmov x5, #1000", "\tmul x5, x5, x4", "\tudiv x3, x3, x5", "\tadd x2, x2, x3")
    add(*_adr("x6", "_sign_dt0"))
    add("\tldr x7, [x6]", "\tcbnz x7, 1f", "\tadd x7, x2, #1", "\tstr x7, [x6]", "1:", "\tsub x0, x2, x7", "\tadd x0, x0, #1", "\tldp x29, x30, [sp], #48", "\tret", "")
    # ---------- 書き込み ----------
    add("// 装置の番地への書き込み: x9 = 番地, x0 = 値, x1 = 幅。x9 は保つ",
        "_sign_dev_st:", "\tstp x29, x30, [sp, #-48]!", "\tmov x29, sp", "\tstp x9, x1, [sp, #16]", "\tstr x0, [sp, #32]",
        "\tlsr x10, x9, #20", "\tcmp x10, #0x96", "\tb.eq .Lds_i2c", "\tcmp x10, #0x95", "\tb.eq .Lds_gpio", "\tcmp x10, #0x92", "\tb.eq .Lds_timer",
        "\tcmp x10, #0x97", "\tb.eq .Lds_spi", "\tcmp x10, #0x99", "\tb.eq .Lds_net", "\tcmp x10, #0x94", "\tb.eq .Lds_sys", "\tcmp x10, #0x93", "\tb.eq .Lds_in", "\tcmp x10, #0x98", "\tb.eq .Lds_snd", *(["\tcmp x10, #0x91", "\tb.eq .Lds_gfx"] if gfx else []), *(["\tcmp x10, #0x9A", "\tb.eq .Lds_db"] if db else []), "\tcmp x10, #0x90", "\tb.ne .Lds_end",
        "\tmov x10, #0x9000000", "\tcmp x9, x10", "\tb.ne .Lds_end",
        "\tcmp x1, #4", "\tb.ne 1f")
    add("\tbl _sign_dev_putc", "\tb .Lds_end", "1:", "\tand x0, x0, #0xFF", "\tcmp x0, #0x80", "\tb.lo 2f",       # Int ≥ 0x80 は生の 1 バイト
        "\tsub sp, sp, #16", "\tstrb w0, [sp]", "\tmov x0, #1", "\tmov x1, sp", "\tmov x2, #1", "\tmov x8, #64", "\tsvc #0", "\tadd sp, sp, #16", "\tb .Lds_end",
        "2:", "\tbl _sign_dev_putc", "\tb .Lds_end")
    add(".Lds_timer:", "\tand x10, x9, #0xFFF", "\tcmp x10, #4", "\tb.eq .Lds_t_sleep", "\tcmp x10, #8", "\tb.eq .Lds_t_id",
        "\tcmp x10, #0xC", "\tb.eq .Lds_t_after", "\tcmp x10, #0x10", "\tb.eq .Lds_t_every", "\tcmp x10, #0x14", "\tb.eq .Lds_t_cancel", "\tb .Lds_end",
        ".Lds_t_sleep:", "\tcmp x0, #0", "\tb.lt .Lds_end", "\tbl _sign_dev_tnow", "\tldr x0, [sp, #32]", "\tmov x1, #1000", "\tudiv x2, x0, x1", "\tmsub x3, x2, x1, x0", "\tmov x4, #1000", "\tmul x3, x3, x4", "\tmul x3, x3, x4",
        "\tstr x2, [sp, #32]", "\tstr x3, [sp, #40]", "\tadd x0, sp, #32", "\tmov x1, #0", "\tmov x8, #101", "\tsvc #0", "\tb .Lds_end",
        "// アラーム(AFTER・EVERY・CANCEL・ID)。表は 16 個: 番号・時刻・周期(0 = 1 回)・使用中",
        ".Lds_t_id:")
    add(*_adr("x11", "_sign_dalm"))
    add("\tstr x0, [x11]", "\tb .Lds_end",
        ".Lds_t_after:", "\tcmp x0, #0", "\tb.lt .Lds_end", "\tmov x2, #0", "\tb .Lds_t_set",
        ".Lds_t_every:", "\tcmp x0, #1", "\tb.lt .Lds_end", "\tmov x2, x0", "\tb .Lds_t_set",
        ".Lds_t_set:", "\tstr x2, [sp, #40]", "\tbl _sign_dev_tnow", "\tldr x3, [sp, #32]", "\tadd x3, x0, x3", "\tldr x4, [sp, #40]")
    add(*_adr("x11", "_sign_dalm"))
    add("\tldr x5, [x11]", "\tadd x6, x11, #8", "\tmov x7, #16", "\tmov x14, #0",
        "1:", "\tldr x12, [x6, #24]", "\tcbz x12, 2f", "\tldr x13, [x6]", "\tcmp x13, x5", "\tb.eq 4f", "\tb 3f",
        "2:", "\tcbnz x14, 3f", "\tmov x14, x6",
        "3:", "\tadd x6, x6, #32", "\tsub x7, x7, #1", "\tcbnz x7, 1b",
        "\tcbz x14, .Lds_end", "\tmov x6, x14",
        "4:", "\tstr x5, [x6]", "\tstr x3, [x6, #8]", "\tstr x4, [x6, #16]", "\tmov x12, #1", "\tstr x12, [x6, #24]", "\tb .Lds_end",
        ".Lds_t_cancel:")
    add(*_adr("x11", "_sign_dalm"))
    add("\tadd x6, x11, #8", "\tmov x7, #16",
        "1:", "\tldr x12, [x6, #24]", "\tcbz x12, 2f", "\tldr x13, [x6]", "\tcmp x13, x0", "\tb.ne 2f", "\tstr xzr, [x6, #24]",
        "2:", "\tadd x6, x6, #32", "\tsub x7, x7, #1", "\tcbnz x7, 1b", "\tb .Lds_end")
    add(".Lds_i2c:")
    add(*_adr("x11", "_sign_dreg"))
    add(*_adr("x12", "_sign_dinit"))
    add("\tldr x13, [x12]", "\tcbnz x13, 1f", "\tmov x13, #1", "\tstr x13, [x12]", "\tstr x13, [x11, #16]", "1:",   # BUS の既定は 1
        "\tand x10, x9, #0xFFF", "\tcmp x10, #0x20", "\tb.hs .Lds_end", "\tldr x0, [sp, #32]", "\tldr x1, [sp, #24]", "\tbl _sign_dev_sh_st",
        "\tcmp x10, #0x14", "\tb.ne .Lds_end", "\tldr x0, [sp, #32]", "\tbl _sign_dev_i2c")
    add(*_adr("x11", "_sign_dreg"))
    add("\tstr x0, [x11, #0x18]", "\tb .Lds_end")
    add(".Lds_spi:", "\tbl _sign_dev_spi_init")
    add(*_adr("x11", "_sign_dreg"))
    add("\tadd x11, x11, #0x2000")
    add("\tand x10, x9, #0xFFF", "\tcmp x10, #0x20", "\tb.hs .Lds_end", "\tldr x0, [sp, #32]", "\tldr x1, [sp, #24]",
        "\tcmp x10, #8", "\tb.ne 2f", "\tcmp x0, #1", "\tb.lt .Lds_end")
    add(*_imm("x14", 125000000))
    add("\tcmp x0, x14", "\tb.gt .Lds_end", "\tb 5f",
        "2:", "\tcmp x10, #0xC", "\tb.ne 3f", "\tcmp x0, #0", "\tb.lt .Lds_end", "\tcmp x0, #3", "\tb.gt .Lds_end", "\tb 5f",
        "3:", "\tcmp x10, #0x10", "\tb.ne 4f", "\tcmp x0, #0", "\tb.lt .Lds_end", "\tcmp x0, #1", "\tb.gt .Lds_end", "\tb 5f",
        "4:", "\tcmp x10, #0x14", "\tb.eq 6f", "\tcmp x10, #0x18", "\tb.eq .Lds_end",                     # RET は読むだけ
        "5:", "\tbl _sign_dev_sh_st", "\tb .Lds_end",
        "6:", "\tldr x0, [sp, #32]", "\tbl _sign_dev_spi")
    add(*_adr("x11", "_sign_dreg"))
    add("\tadd x11, x11, #0x2000", "\tstr x0, [x11, #0x18]", "\tb .Lds_end")
    add(".Lds_gpio:")
    add(*_adr("x11", "_sign_dreg"))
    add("\tadd x11, x11, #0x1000", "\tand x10, x9, #0xFFF", "\tcmp x10, #0x400", "\tb.hs .Lds_end", "\tldr x0, [sp, #32]", "\tldr x1, [sp, #24]", "\tbl _sign_dev_sh_st",
        "\tlsr x12, x10, #8", "\tand x13, x10, #0xFF", "\tlsr x13, x13, #2",
        "\tcbz x12, 1f", "\tcmp x12, #1", "\tb.ne .Lds_end",
        "\tldr x2, [sp, #32]", "\tmov x3, #0x104", "\tcmp x2, #2", "\tb.eq 3f", "\tmov x3, #0x204", "\tcmp x2, #3", "\tb.eq 3f",
        "\tmov x3, #4", "\tcmp x2, #0", "\tb.eq 3f", "\tmov x3, #8", "\tcmp x2, #1", "\tb.ne .Lds_end",
        "3:", "\tmov x0, #0", "\tmov x1, x13", "\tmov x2, x3", "\tbl _sign_dev_gp", "\tb .Lds_end",
        "1:", "\tldr x2, [sp, #32]", "\tcmp x2, #0", "\tb.eq 2f", "\tmov x2, #1", "2:", "\tmov x0, #1", "\tmov x1, x13", "\tbl _sign_dev_gp", "\tb .Lds_end")
    add(".Lds_net:")
    add(*_adr("x11", "_sign_dreg"))
    add("\tadd x11, x11, #0x3000", "\tand x10, x9, #0xFFF", "\tcmp x10, #0x28", "\tb.hs .Lds_end", "\tcmp x10, #0x24", "\tb.eq .Lds_end",
        "\tldr x0, [sp, #32]", "\tldr x1, [sp, #24]", "\tbl _sign_dev_sh_st", "\tcmp x10, #0x20", "\tb.ne .Lds_end",
        "\tldr w0, [x11]", "\tbl _sign_dev_net")
    add(*_adr("x11", "_sign_dreg"))
    add("\tadd x11, x11, #0x3000", "\tstr x0, [x11, #0x24]", "\tb .Lds_end")
    if db:
        add(".Lds_db:")
        add(*_adr("x11", "_sign_dbreg"))
        add("\tand x10, x9, #0xFFF", "\tcmp x10, #0x28", "\tb.hs .Lds_end", "\tcmp x10, #0x24", "\tb.eq .Lds_end", "\tand x13, x10, #3", "\tcbnz x13, .Lds_end",
            "\tlsl x12, x10, #1", "\tadd x12, x11, x12", "\tldr x0, [sp, #32]", "\tldr x1, [sp, #24]", "\tcmp x1, #4", "\tb.ne 1f", "\tand x0, x0, #0xFFFFFFFF",
            "1:", "\tstr x0, [x12]", "\tcmp x10, #0x20", "\tb.ne .Lds_end", "\tmov x0, x11", "\tbl sign_db_call")
        add(*_adr("x11", "_sign_dbreg"))
        add("\tstr x0, [x11, #0x48]", "\tb .Lds_end")
    add(".Lds_sys:")
    add(*_adr("x11", "_sign_dreg"))
    add("\tadd x11, x11, #0x4000", "\tand x10, x9, #0xFFF", "\tcmp x10, #0x1C", "\tb.hs .Lds_end", "\tcmp x10, #0x18", "\tb.eq .Lds_end",
        "\tldr x0, [sp, #32]", "\tldr x1, [sp, #24]", "\tbl _sign_dev_sh_st", "\tcmp x10, #0x14", "\tb.ne .Lds_end",
        "\tldr w0, [x11]", "\tbl _sign_dev_sys")
    add(*_adr("x11", "_sign_dreg"))
    add("\tadd x11, x11, #0x4000", "\tstr x0, [x11, #0x18]", "\tb .Lds_end")
    if gfx:
        add(".Lds_gfx:", "\tldr x9, [sp, #16]", "\tmovz x10, #0xFFFF", "\tmovk x10, #0xF, lsl #16", "\tand x0, x9, x10", "\tldr x1, [sp, #32]", "\tldr x2, [sp, #24]", "\tcmp x2, #4", "\tb.ne 1f", "\tand x1, x1, #0xFFFFFFFF", "1:", "\tbl _sign_dev_gst", "\tb .Lds_end")
        add(".Ldl_gfx:", "\tldr x0, [sp, #16]", "\tmovz x10, #0xFFFF", "\tmovk x10, #0xF, lsl #16", "\tand x0, x0, x10", "\tbl _sign_dev_gld", "\tb .Ldl_end")
    add(".Lds_snd:", "\tldr x9, [sp, #16]", "\tmovz x10, #0xFFFF", "\tmovk x10, #0xF, lsl #16", "\tand x0, x9, x10", "\tldr x1, [sp, #32]", "\tldr x2, [sp, #24]", "\tcmp x2, #4", "\tb.ne 1f", "\tand x1, x1, #0xFFFFFFFF", "1:", "\tbl _sign_dev_snd_st", "\tb .Lds_end")
    add(".Ldl_snd:", "\tldr x0, [sp, #16]", "\tmovz x10, #0xFFFF", "\tmovk x10, #0xF, lsl #16", "\tand x0, x0, x10", "\tbl _sign_dev_snd_ld", "\tldr x1, [sp, #24]", "\tcmp x1, #4", "\tb.ne .Ldl_end", "\tand x0, x0, #0xFFFFFFFF", "\tb .Ldl_end")
    add(".Lds_in:", "\tbl _sign_dev_ipoll", "\tldr x9, [sp, #16]", "\tmovz x10, #0xFFFF", "\tmovk x10, #0xF, lsl #16", "\tand x10, x9, x10", "\tcmp x10, #0x14", "\tb.ne .Lds_end", "\tbl _sign_dev_ipop", "\tb .Lds_end")
    add(".Lds_end:", "\tldp x9, x1, [sp, #16]", "\tldp x29, x30, [sp], #48", "\tret", "")
    # ---------- 読み ----------
    add("// 装置の番地の読み: x0 = 番地, x1 = 幅 → x0",
        "_sign_dev_ld:", "\tstp x29, x30, [sp, #-48]!", "\tmov x29, sp", "\tstp x0, x1, [sp, #16]",
        "\tlsr x10, x0, #20", "\tcmp x10, #0x96", "\tb.eq .Ldl_i2c", "\tcmp x10, #0x95", "\tb.eq .Ldl_gpio", "\tcmp x10, #0x92", "\tb.eq .Ldl_timer",
        "\tcmp x10, #0x97", "\tb.eq .Ldl_spi", "\tcmp x10, #0x99", "\tb.eq .Ldl_net", "\tcmp x10, #0x94", "\tb.eq .Ldl_sys", "\tcmp x10, #0x93", "\tb.eq .Ldl_in", "\tcmp x10, #0x98", "\tb.eq .Ldl_snd", *(["\tcmp x10, #0x91", "\tb.eq .Ldl_gfx"] if gfx else []), *(["\tcmp x10, #0x9A", "\tb.eq .Ldl_db"] if db else []), "\tcmp x10, #0x90", "\tb.eq .Ldl_uart", ".Ldl_zero:", "\tmov x0, #0", ".Ldl_end:", "\tldp x29, x30, [sp], #48", "\tret")
    add(".Ldl_i2c:")
    add(*_adr("x11", "_sign_dreg"))
    add("\tand x10, x0, #0xFFF", "\tcmp x10, #0x20", "\tb.hs .Ldl_zero", "\tbl _sign_dev_sh_ld", "\tb .Ldl_end")
    if db:
        add(".Ldl_db:")
        add(*_adr("x11", "_sign_dbreg"))
        add("\tand x10, x0, #0xFFF", "\tcmp x10, #0x28", "\tb.hs .Ldl_zero", "\tand x13, x10, #3", "\tcbnz x13, .Ldl_zero", "\tlsl x12, x10, #1", "\tadd x12, x11, x12", "\tldr x0, [x12]",
            "\tldr x1, [sp, #24]", "\tcmp x1, #4", "\tb.ne .Ldl_end", "\tand x0, x0, #0xFFFFFFFF", "\tb .Ldl_end")
    add(".Ldl_in:", "\tbl _sign_dev_ipoll", "\tldr x0, [sp, #16]", "\tmovz x10, #0xFFFF", "\tmovk x10, #0xF, lsl #16", "\tand x0, x0, x10", "\tbl _sign_dev_iget", "\tb .Ldl_end")
    add(".Ldl_sys:")
    add(*_adr("x11", "_sign_dreg"))
    add("\tadd x11, x11, #0x4000", "\tand x10, x0, #0xFFF", "\tcmp x10, #0x1C", "\tb.hs .Ldl_zero", "\tbl _sign_dev_sh_ld", "\tb .Ldl_end")
    add(".Ldl_net:")
    add(*_adr("x11", "_sign_dreg"))
    add("\tadd x11, x11, #0x3000", "\tand x10, x0, #0xFFF", "\tcmp x10, #0x28", "\tb.hs .Ldl_zero", "\tbl _sign_dev_sh_ld", "\tb .Ldl_end")
    add(".Ldl_spi:", "\tstr x0, [sp, #32]", "\tbl _sign_dev_spi_init", "\tldr x0, [sp, #32]")
    add(*_adr("x11", "_sign_dreg"))
    add("\tadd x11, x11, #0x2000", "\tand x10, x0, #0xFFF", "\tcmp x10, #0x20", "\tb.hs .Ldl_zero", "\tbl _sign_dev_sh_ld", "\tb .Ldl_end")
    add(".Ldl_gpio:", "\tand x10, x0, #0xFFF", "\tcmp x10, #0x400", "\tb.hs .Ldl_zero", "\tcmp x10, #0x100", "\tb.hs 1f",
        "\tlsr x1, x10, #2", "\tmov x0, #2", "\tmov x2, #0", "\tbl _sign_dev_gp", "\tb .Ldl_end", "1:")
    add(*_adr("x11", "_sign_dreg"))
    add("\tadd x11, x11, #0x1000", "\tldr x1, [sp, #24]", "\tbl _sign_dev_sh_ld", "\tb .Ldl_end")
    add(".Ldl_timer:", "\tand x10, x0, #0xFFF", "\tcbnz x10, 1f", "\tbl _sign_dev_tnow", "\tb .Ldl_end",
        "1:", "\tcmp x10, #8", "\tb.ne 2f")
    add(*_adr("x11", "_sign_dalm"))
    add("\tldr x0, [x11]", "\tb .Ldl_end",
        "// 0x18 DUE(この実装の足し)… 時刻が来たアラームのうち一番早いものの番号を取り出す(1 回きりは消え、くり返しは次へ進む)。無ければ -1",
        "2:", "\tcmp x10, #0x18", "\tb.ne .Ldl_zero", "\tbl _sign_dev_tnow", "\tmov x4, x0")
    add(*_adr("x11", "_sign_dalm"))
    add("\tadd x6, x11, #8", "\tmov x7, #16", "\tmov x5, #0",
        "1:", "\tldr x12, [x6, #24]", "\tcbz x12, 3f", "\tldr x13, [x6, #8]", "\tcmp x13, x4", "\tb.gt 3f",
        "\tcbz x5, 2f", "\tldr x14, [x5, #8]", "\tcmp x13, x14", "\tb.ge 3f",
        "2:", "\tmov x5, x6",
        "3:", "\tadd x6, x6, #32", "\tsub x7, x7, #1", "\tcbnz x7, 1b",
        "\tcbnz x5, 4f", "\tmov x0, #-1", "\tb .Ldl_end",
        "4:", "\tldr x0, [x5]", "\tldr x12, [x5, #16]", "\tcbnz x12, 5f", "\tstr xzr, [x5, #24]", "\tb .Ldl_end",
        "5:", "\tldr x13, [x5, #8]",
        "6:", "\tadd x13, x13, x12", "\tcmp x13, x4", "\tb.le 6b", "\tstr x13, [x5, #8]", "\tb .Ldl_end")
    add(".Ldl_uart:", "\tmov x10, #0x9000000", "\tcmp x0, x10", "\tb.ne .Ldl_zero",
        "\tmov x0, #0", "\tadd x1, sp, #32", "\tmov x2, #1", "\tmov x8, #63", "\tsvc #0",
        "\tcmp x0, #1", "\tb.ne 1f", "\tldrb w0, [sp, #32]", "\tb .Ldl_end", "1:")
    add(*_imm("x0", NICHE))
    add("\tb .Ldl_end", "")
    import sign_realnet
    L.extend(sign_realnet.shim())
    import sign_realsys
    L.extend(sign_realsys.shim())
    import sign_realinput
    L.extend(sign_realinput.shim())
    if gfx:
        import sign_realgfx
        L.extend(sign_realgfx.shim(*gfx))
    import sign_realsound
    L.extend(sign_realsound.shim())
    return L


def data_lines(db=False, gfx=None):
    """.rodata(チップのパス)と .bss(影レジスタ・バッファ・行の fd 表)。"""
    path = list("/dev/gpiochip0".encode()) + [0]
    import sign_realnet
    nro, nbss = sign_realnet.data_lines()
    import sign_realsys
    nbss = nbss + sign_realsys.data_lines()[1]
    import sign_realinput
    iro, ibss = sign_realinput.data_lines()
    nro = nro + iro; nbss = nbss + ["\t.balign 8"] + ibss
    import sign_realsound
    sro, sbss = sign_realsound.data_lines()
    nro = nro + sro; nbss = nbss + sbss
    if gfx:
        import sign_realgfx
        gro, gbss = sign_realgfx.data_lines(*gfx)
        nro = nro + gro; nbss = nbss + gbss
    return (["\t.section .rodata", "_sign_dev_gchip:", "\t.byte " + ", ".join(str(b) for b in path), "_sign_dev_mapmsg:", "\t.byte " + ", ".join(str(b) for b in MAPMSG)] + nro + [""],
            ["\t.section .bss", "\t.balign 8"] + sum([["%s:" % n, "\t.skip %d" % sz] for n, sz in
             (("_sign_dreg", 0x5000), ("_sign_dwr", 4096), ("_sign_drd", 4096), ("_sign_gfd", 512), ("_sign_gst", 64), ("_sign_greq", 592), ("_sign_dinit", 8), ("_sign_dinit2", 8), ("_sign_dalm", 544), ("_sign_dt0", 8))], []) + nbss + (["_sign_dbreg:", "\t.skip 128"] if db else []) + [""])
