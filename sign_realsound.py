"""sign_realsound.py — `--real-dev` の音の装置(0x9800000)の中継ルーチン(AArch64 アセンブリ)。

処理系の Sound(sign_audio.py)と同じ番地の並び(PATH PLEN FREQ MS VOL GO RET BUSY)・同じ命令(1 PLAY 2 TONE 3 STOP)・同じエラー番号を、
Linux の子プロセス `/usr/bin/aplay -q`(alsa-utils。Raspberry Pi OS には入っている)で動かす。ALSA を直に叩く代わりに、WAV を aplay の標準入力に渡す。
  - PLAY: 名前(PATH・PLEN。作業フォルダの中だけ。openat2 + RESOLVE_BENEATH。sys 装置と同じ検査)を開き、先頭 12 バイトが RIFF....WAVE であること・64 MiB 以下であることを確かめ、
    その fd を aplay の標準入力にして fork + execve。すぐ戻る。
  - TONE: FREQ(20〜20000)・MS(1〜10000)・VOL(0〜100)の正弦波(16 ビット・モノラル・22050 Hz。両端 5 ミリ秒は音量を上げ下げ)を memfd に WAV として作って渡す。
  - STOP / 鳴らしている最中の新しい PLAY・TONE: 前の aplay に SIGTERM を送って待つ。BUSY: wait4(WNOHANG) で aplay が生きているか聞く。
  - 子は prctl(PR_SET_PDEATHSIG, SIGTERM) を付けるので、プログラムが終わると鳴りやむ(処理系の close と同じ)。
  - エラー: 引数が範囲外・WAV でない -22、見つからない -2(ディレクトリも)、作業フォルダの外 -13、aplay が無い -19、memfd や fork の失敗 -5。
実装の決め(処理系との違い): ① 音を出す手段は aplay だけ(paplay・pw-play・ffplay は探さない)。aplay が音の装置を開けなかった場合は、BUSY がすぐ 0 になるだけで RET は 0 のまま。
  ② 正弦波は 1024 点の表を位相の累積で引く(補間なし)ので、処理系の計算とは数の最後の桁が少し違う(振幅の 0.3% 以内)。
  ③ 環境変数は起動時のものをそのまま aplay に渡す(PipeWire・PulseAudio の接続に XDG_RUNTIME_DIR が要るため)。
  ④ 名前の UTF-8 の正しさは見ない(sys 装置と同じ)。
実機では未実行(疑似カーネルで確認)。"""
import math

RATE = 22050
SNDPATH = b"/usr/bin/aplay\0"


def _imm(reg, v):
    from sign_asm import emit_imm
    out = []; emit_imm(out, reg, v); return out


def _adr(reg, sym):
    return ["\tadrp %s, %s" % (reg, sym), "\tadd %s, %s, :lo12:%s" % (reg, reg, sym)]


def shim():
    L = []
    add = lambda *xs: L.extend(xs)
    add("// ===== 音 (0x98…) =====", "")
    # 状態 _sign_snd: 0 PATH / 8 PLEN / 16 FREQ / 24 MS / 32 VOL / 40 RET / 48 pid / 56 初期化済み
    add("_sign_dev_snd_init:")
    add(*_adr("x15", "_sign_snd"))
    add("\tldr x2, [x15, #56]", "\tcbnz x2, 1f", "\tmov x2, #1", "\tstr x2, [x15, #56]", "\tmov x2, #440", "\tstr x2, [x15, #16]", "\tmov x2, #200", "\tstr x2, [x15, #24]", "\tmov x2, #100", "\tstr x2, [x15, #32]", "1:", "\tret", "")
    # 前の aplay を止める
    add("_sign_dev_snd_stop:", "\tstp x29, x30, [sp, #-48]!", "\tmov x29, sp")
    add(*_adr("x15", "_sign_snd"))
    add("\tldr x0, [x15, #48]", "\tcbz x0, 1f", "\tstr xzr, [x15, #48]", "\tstr x0, [sp, #16]", "\tmov x1, #15", "\tmov x8, #129", "\tsvc #0",
        "\tldr x0, [sp, #16]", "\tadd x1, sp, #24", "\tmov x2, #0", "\tmov x3, #0", "\tmov x8, #260", "\tsvc #0", "1:", "\tldp x29, x30, [sp], #48", "\tret", "")
    # 鳴っているか → x0
    add("_sign_dev_snd_busy:", "\tstp x29, x30, [sp, #-48]!", "\tmov x29, sp")
    add(*_adr("x15", "_sign_snd"))
    add("\tldr x0, [x15, #48]", "\tcbz x0, 2f", "\tadd x1, sp, #16", "\tmov x2, #1", "\tmov x3, #0", "\tmov x8, #260", "\tsvc #0", "\tcbz x0, 3f",
        "\tstr xzr, [x15, #48]", "2:", "\tmov x0, #0", "\tb 4f", "3:", "\tmov x0, #1", "4:", "\tldp x29, x30, [sp], #48", "\tret", "")
    # 起動: x0 = 標準入力にする fd → x0 = 0 か -19(aplay が無い)か -5(fork 失敗)。fd は閉じない
    add("_sign_dev_snd_start:", "\tstp x29, x30, [sp, #-64]!", "\tmov x29, sp", "\tstr x0, [sp, #16]", "\tmov x0, #-100")
    add(*_adr("x1", "_sign_snd_path"))
    add("\tmov x2, #1", "\tmov x3, #0", "\tmov x8, #48", "\tsvc #0", "\tcmp x0, #0", "\tb.ge 1f", "\tmov x0, #-19", "\tb 9f",
        "1:", "\tbl _sign_dev_snd_stop", "\tmov x0, #17", "\tmov x1, #0", "\tmov x2, #0", "\tmov x3, #0", "\tmov x4, #0", "\tmov x8, #220", "\tsvc #0",
        "\tcmp x0, #0", "\tb.lt 8f", "\tb.eq 5f")
    add(*_adr("x15", "_sign_snd"))
    add("\tstr x0, [x15, #48]", "\tmov x0, #0", "\tb 9f",
        "8:", "\tmov x0, #-5", "\tb 9f",
        "5:", "\tmov x0, #1", "\tmov x1, #15", "\tmov x8, #167", "\tsvc #0",                         # 子: 親が死んだら SIGTERM
        "\tldr x0, [sp, #16]", "\tmov x1, #0", "\tmov x2, #0", "\tmov x8, #24", "\tsvc #0")           # dup3(fd, 0, 0)
    add(*_adr("x1", "_sign_snd_a0"))
    add("\tstr x1, [sp, #24]")
    add(*_adr("x1", "_sign_snd_a1"))
    add("\tstr x1, [sp, #32]", "\tstr xzr, [sp, #40]")
    add(*_adr("x0", "_sign_snd_path"))
    add("\tadd x1, sp, #24")
    add(*_adr("x2", "_sign_envp"))
    add("\tldr x2, [x2]", "\tmov x8, #221", "\tsvc #0", "\tmov x0, #127", "\tmov x8, #94", "\tsvc #0",
        "9:", "\tldp x29, x30, [sp], #64", "\tret", "")
    # 命令。x0 = GO の値 → x0。枠: +16 fd +24 結果 +32 補助
    add("_sign_dev_snd_go:", "\tstp x29, x30, [sp, #-64]!", "\tmov x29, sp")
    add(*_adr("x15", "_sign_snd"))
    add("\tcmp x0, #3", "\tb.ne 1f", "\tbl _sign_dev_snd_stop", "\tmov x0, #0", "\tb .Lsg_ret",
        "1:", "\tcmp x0, #1", "\tb.eq .Lsg_play", "\tcmp x0, #2", "\tb.eq .Lsg_tone",
        ".Lsg_einval:", "\tmov x0, #-22", ".Lsg_ret:", "\tldp x29, x30, [sp], #64", "\tret")
    # PLAY
    add(".Lsg_play:", "\tldr x1, [x15, #8]", "\tsub x2, x1, #1", "\tcmp x2, #1024", "\tb.hs .Lsg_einval", "\tldr x0, [x15]", "\tbl _sign_dev_spath", "\tcmp x0, #0", "\tb.lt .Lsg_ret",
        "\tmov x0, #0", "\tbl _sign_dev_open2", "\tcmp x0, #0", "\tb.lt .Lsg_ret", "\tstr x0, [sp, #16]")
    add(*_adr("x1", "_sign_sbuf"))
    add("\tmov x2, #12", "\tmov x8, #63", "\tsvc #0", "\tcmp x0, #12", "\tb.ge 2f", "\tmov x1, #-21", "\tcmp x0, x1", "\tb.ne 3f", "\tmov x0, #-2", "\tb 5f", "3:", "\tmov x0, #-22", "\tb 5f", "2:")
    add(*_adr("x1", "_sign_sbuf"))
    add("\tldr w2, [x1]", "\tmov w3, #0x4952", "\tmovk w3, #0x4646, lsl #16", "\tcmp w2, w3", "\tb.ne 4f", "\tldr w2, [x1, #8]", "\tmov w3, #0x4157", "\tmovk w3, #0x4556, lsl #16", "\tcmp w2, w3", "\tb.ne 4f",
        "\tldr x0, [sp, #16]", "\tmov x1, #0", "\tmov x2, #2", "\tmov x8, #62", "\tsvc #0", "\tmov x1, #0x4000000", "\tcmp x0, x1", "\tb.hi 4f",
        "\tldr x0, [sp, #16]", "\tmov x1, #0", "\tmov x2, #0", "\tmov x8, #62", "\tsvc #0",
        "\tldr x0, [sp, #16]", "\tbl _sign_dev_snd_start", "\tb 5f",
        "4:", "\tmov x0, #-22",
        "5:", "\tstr x0, [sp, #24]", "\tldr x0, [sp, #16]", "\tmov x8, #57", "\tsvc #0", "\tldr x0, [sp, #24]", "\tb .Lsg_ret")
    # TONE
    add(".Lsg_tone:", "\tldr x1, [x15, #16]", "\tsub x1, x1, #20", "\tmov x2, #19980", "\tcmp x1, x2", "\tb.hi .Lsg_einval",
        "\tldr x1, [x15, #24]", "\tsub x1, x1, #1", "\tmov x2, #9999", "\tcmp x1, x2", "\tb.hi .Lsg_einval", "\tldr x1, [x15, #32]", "\tcmp x1, #100", "\tb.hi .Lsg_einval",
        "\tmov x0, #0")
    add(*_adr("x0", "_sign_snd_a1"))
    add("\tmov x1, #1", "\tmov x8, #279", "\tsvc #0", "\tcmp x0, #0", "\tb.ge 1f", "\tmov x0, #-5", "\tb .Lsg_ret", "1:", "\tstr x0, [sp, #16]")
    add(*_adr("x15", "_sign_snd"))
    add("\tldr x2, [x15, #24]", "\tmov x1, #%d" % RATE, "\tmul x3, x1, x2", "\tmov x1, #1000", "\tudiv x3, x3, x1",            # x3 = n
        "\tldr x2, [x15, #32]", "\tmov x1, #32767", "\tmul x6, x1, x2", "\tmov x1, #100", "\tudiv x6, x6, x1", "\tmov x1, #8", "\tmul x6, x6, x1", "\tmov x1, #10", "\tudiv x6, x6, x1",   # x6 = 振幅
        "\tldr x2, [x15, #16]", "\tlsl x5, x2, #32", "\tmov x1, #%d" % RATE, "\tudiv x5, x5, x1",                                  # x5 = 位相の刻み
        "\tlsl x13, x3, #1", "\tstr x13, [sp, #32]")                                                                                 # データの長さ
    add(*_adr("x9", "_sign_sbuf"))
    add("\tmov x1, #0")
    add(*_adr("x7", "_sign_snd_hdr"))
    add("1:", "\tldrb w2, [x7, x1]", "\tstrb w2, [x9, x1]", "\tadd x1, x1, #1", "\tcmp x1, #44", "\tb.ne 1b",
        "\tadd x2, x13, #36", "\tstr w2, [x9, #4]", "\tstr w13, [x9, #40]", "\tadd x9, x9, #44")
    add(*_adr("x7", "_sign_snd_tbl"))
    add("\tmov x2, #0", "\tmov x4, #0",
        "2:", "\tcmp x2, x3", "\tb.ge 3f", "\tsub x10, x3, #1", "\tsub x10, x10, x2", "\tcmp x2, x10", "\tcsel x10, x2, x10, lt", "\tmov x11, #110", "\tcmp x10, x11", "\tcsel x10, x10, x11, lt",
        "\tmov x11, #0x200000", "\tadd x11, x11, x4", "\tlsr x11, x11, #22", "\tand x11, x11, #1023", "\tlsl x11, x11, #2", "\tldr w12, [x7, x11]", "\tlsl x12, x12, #32", "\tasr x12, x12, #32",
        "\tmul x12, x12, x6", "\tmul x12, x12, x10")
    add(*_imm("x11", 32767 * 110))
    add("\tsdiv x12, x12, x11", "\tlsl x14, x2, #1", "\tstrh w12, [x9, x14]", "\tadd x4, x4, x5", "\tand x4, x4, #0xFFFFFFFF", "\tadd x2, x2, #1", "\tb 2b",
        "3:", "\tldr x13, [sp, #32]", "\tadd x13, x13, #44")                                                                           # 送る全長
    add(*_adr("x9", "_sign_sbuf"))
    add("\tmov x14, #0",
        "4:", "\tcmp x14, x13", "\tb.ge 5f", "\tldr x0, [sp, #16]", "\tadd x1, x9, x14", "\tsub x2, x13, x14", "\tmov x8, #64", "\tsvc #0", "\tcmp x0, #0", "\tb.le 6f", "\tadd x14, x14, x0", "\tb 4b",
        "5:", "\tldr x0, [sp, #16]", "\tmov x1, #0", "\tmov x2, #0", "\tmov x8, #62", "\tsvc #0", "\tldr x0, [sp, #16]", "\tbl _sign_dev_snd_start", "\tb 7f",
        "6:", "\tmov x0, #-5",
        "7:", "\tstr x0, [sp, #24]", "\tldr x0, [sp, #16]", "\tmov x8, #57", "\tsvc #0", "\tldr x0, [sp, #24]", "\tb .Lsg_ret", "")
    # 書き: x0 = 領域の中の位置, x1 = 値
    add("_sign_dev_snd_st:", "\tstp x29, x30, [sp, #-32]!", "\tmov x29, sp", "\tstr x0, [sp, #16]", "\tstr x1, [sp, #24]", "\tbl _sign_dev_snd_init", "\tldr x0, [sp, #16]", "\tldr x1, [sp, #24]",
        "\tcmp x0, #0x14", "\tb.ne 1f", "\tmov x0, x1", "\tbl _sign_dev_snd_go")
    add(*_adr("x15", "_sign_snd"))
    add("\tstr x0, [x15, #40]", "\tb 9f", "1:", "\tcmp x0, #0x10", "\tb.hi 9f", "\tand x2, x0, #3", "\tcbnz x2, 9f", "\tlsl x0, x0, #1", "\tstr x1, [x15, x0]", "9:", "\tldp x29, x30, [sp], #32", "\tret", "")
    # 読み: x0 = 領域の中の位置 → x0
    add("_sign_dev_snd_ld:", "\tstp x29, x30, [sp, #-32]!", "\tmov x29, sp", "\tstr x0, [sp, #16]", "\tbl _sign_dev_snd_init", "\tldr x0, [sp, #16]",
        "\tcmp x0, #0x18", "\tb.ne 1f", "\tldr x0, [x15, #40]", "\tb 9f", "1:", "\tcmp x0, #0x1C", "\tb.ne 2f", "\tbl _sign_dev_snd_busy", "\tb 9f",
        "2:", "\tcmp x0, #0x10", "\tb.hi 8f", "\tand x2, x0, #3", "\tcbnz x2, 8f", "\tlsl x0, x0, #1", "\tldr x0, [x15, x0]", "\tb 9f", "8:", "\tmov x0, #0", "9:", "\tldp x29, x30, [sp], #32", "\tret", "")
    return L


def hdr():
    le = lambda v, n: list(int(v).to_bytes(n, "little"))
    return list(b"RIFF") + le(0, 4) + list(b"WAVEfmt ") + le(16, 4) + le(1, 2) + le(1, 2) + le(RATE, 4) + le(RATE * 2, 4) + le(2, 2) + le(16, 2) + list(b"data") + le(0, 4)


def data_lines():
    tbl = [round(32767 * math.sin(2 * math.pi * k / 1024)) & 0xFFFFFFFF for k in range(1024)]
    ro = ["\t.section .rodata", "_sign_snd_path:", "\t.byte " + ", ".join(str(b) for b in SNDPATH), "_sign_snd_a0:", "\t.byte " + ", ".join(str(b) for b in b"aplay\0"),
          "_sign_snd_a1:", "\t.byte " + ", ".join(str(b) for b in b"-q\0"), "_sign_snd_hdr:", "\t.byte " + ", ".join(str(b) for b in hdr()),
          "\t.balign 4", "_sign_snd_tbl:"] + ["\t.word " + ", ".join(str(v) for v in tbl[i:i + 16]) for i in range(0, 1024, 16)]
    return ro, ["\t.balign 8", "_sign_snd:", "\t.skip 64", "_sign_envp:", "\t.skip 8"]
