// Sign — AArch64 (AAPCS64)
// source: t_db_basic.sn
	.text

seq2:
	stp x29, x30, [sp, #-32]!  // フレーム 32 バイト
	mov x29, sp
	mov x0, x1  // b
	ldp x29, x30, [sp], #32  // フレームを戻す
	ret

seq3:
	stp x29, x30, [sp, #-48]!  // フレーム 48 バイト
	mov x29, sp
	mov x0, x2  // c
	ldp x29, x30, [sp], #48  // フレームを戻す
	ret

seq7:
	stp x29, x30, [sp, #-80]!  // フレーム 80 バイト
	mov x29, sp
	mov x0, x6  // g
	ldp x29, x30, [sp], #80  // フレームを戻す
	ret

seq9:
	stp x29, x30, [sp, #-96]!  // フレーム 96 バイト
	mov x29, sp
	ldr x0, [x29, #96]  // スタックで渡された仮引数 i(呼ぶ側の sp = フレームの上)
	ldp x29, x30, [sp], #96  // フレームを戻す
	ret

str_put:
	stp x29, x30, [sp, #-80]!  // フレーム 80 バイト
	mov x29, sp
	mov x3, #0  // 実引数(字面)
	bl std_sput
	ldp x29, x30, [sp], #80  // フレームを戻す
	ret

std_sput:
	stp x29, x30, [sp, #-80]!  // フレーム 80 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 dst
	str x1, [x29, #24]  // 仮引数 s.ptr
	str x2, [x29, #32]  // 仮引数 s.len
	str x3, [x29, #40]  // 仮引数 i
.L6:
	ldr x9, [x29, #24]  // s.ptr
	ldr x0, [x29, #32]  // s.len
	str x0, [x29, #48]  // 比べる項
	ldr x9, [x29, #40]  // i
	cmp x9, x0
	b.lt .L8
	ldr x0, [x29, #16]  // dst
	str x0, [x29, #48]  // 途中の値はフレームへ
	mov x0, #4  // STD_W4
	ldr x10, [x29, #40]  // i
	mul x11, x0, x10
	smulh x12, x0, x10  // 積の上の語
	cmp x12, x11, asr #63  // 上の語が下の語の符号の伸びでなければ溢れた
	ccmp xzr, x11, #1, eq
	b.vs .Ltrap
	ldr x9, [x29, #48]
	adds x9, x9, x11
	ccmp xzr, x9, #1, vc  // 溢れずに INT64_MIN に着いた結果も罠
	b.vs .Ltrap
	str x9, [x29, #48]  // 番地
	mov x0, #0
	movz x10, #0x900, lsl #16
	cmp x9, x10
	b.lo .L10
	mov x1, #4  // 幅
	bl _sign_dev_st  // 装置への書き込み(実機の中継。sign_realdev.py)
	b .L11
.L10:
	str w0, [x9]  // 幅 4 byte で書く(value_representation.md §5。値はその幅へ切れる)
.L11:
.L9:
	str x9, [x29, #48]  // 実引数
	ldr x0, [x29, #40]  // i
	str x0, [x29, #56]  // 実引数
	ldr x0, [x29, #48]
	ldr x1, [x29, #56]
	ldp x29, x30, [sp], #80  // フレームを戻す
	b seq2  // 兄弟への末尾呼び出し
	b .L7
.L8:
	ldr x0, [x29, #16]  // dst
	str x0, [x29, #48]  // 途中の値はフレームへ
	mov x0, #4  // STD_W4
	ldr x10, [x29, #40]  // i
	mul x11, x0, x10
	smulh x12, x0, x10  // 積の上の語
	cmp x12, x11, asr #63  // 上の語が下の語の符号の伸びでなければ溢れた
	ccmp xzr, x11, #1, eq
	b.vs .Ltrap
	ldr x9, [x29, #48]
	adds x9, x9, x11
	ccmp xzr, x9, #1, vc  // 溢れずに INT64_MIN に着いた結果も罠
	b.vs .Ltrap
	str x9, [x29, #48]  // 番地
	ldr x11, [x29, #40]  // i
	ldr x9, [x29, #24]  // s.ptr
	ldr x10, [x29, #32]  // s.len
	cmp x11, #0
	b.ge .L15
	add x11, x11, x10  // 負の添字は後ろから
.L15:
	cmp x11, x10
	b.hs .L13  // 範囲の外(符号なしで比べると、後ろからでも足りない負の数も外れる)。読まない
	ldrb w0, [x9, x11]  // 文字(ASCII の 1 バイト)
	b .L14
.L13:
	mov x0, #0  // Char の `__` は U+0000(niche)
.L14:
	str x0, [x29, #56]  // 左の文字
	mov x0, #0  // 文字
	ldr x9, [x29, #56]
	cbz x9, .L16  // Char の __ は U+0000(字面の U+0000 は __ ではない)
	sub x0, x9, x0  // 符号位置の差は Int の値域に収まる
	b .L17
.L16:
	movz x0, #0x8000, lsl #48  // __
.L17:
	ldr x9, [x29, #48]
	movz x13, #0x8000, lsl #48  // __
	cmp x0, x13
	b.eq .L18  // 値が __ なら何も書かない(番地は返る)
	movz x10, #0x900, lsl #16
	cmp x9, x10
	b.lo .L19
	mov x1, #4  // 幅
	bl _sign_dev_st  // 装置への書き込み(実機の中継。sign_realdev.py)
	b .L20
.L19:
	str w0, [x9]  // 幅 4 byte で書く(value_representation.md §5。値はその幅へ切れる)
.L20:
.L18:
	ldr x0, [x29, #16]  // dst
	str x0, [x29, #48]  // 実引数
	ldr x0, [x29, #24]  // s.ptr
	ldr x1, [x29, #32]  // s.len
	str x0, [x29, #56]  // 実引数(ptr)
	str x1, [x29, #64]  // 実引数(len)
	ldr x0, [x29, #40]  // i
	adds x9, x0, #1
	ccmp xzr, x9, #1, vc  // 溢れずに INT64_MIN に着いた結果も罠
	b.vs .Ltrap
	str x9, [x29, #72]  // 実引数
	ldr x9, [x29, #48]
	str x9, [x29, #16]  // 仮引数 dst を更新
	ldr x9, [x29, #56]
	str x9, [x29, #24]  // 仮引数 s を更新
	ldr x9, [x29, #64]
	str x9, [x29, #32]  // 仮引数 s を更新
	ldr x9, [x29, #72]
	str x9, [x29, #40]  // 仮引数 i を更新
	b .L6  // 自分への末尾呼び出し
	b .L7
.L12:
	movz x0, #0x8000, lsl #48  // __
.L7:
	ldp x29, x30, [sp], #80  // フレームを戻す
	ret

str_int:
	stp x29, x30, [sp, #-48]!  // フレーム 48 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 dst
	str x1, [x29, #24]  // 仮引数 n
	mov x9, x1  // n
	mov x10, #0
	cmp x9, #0
	b.ge .L23
	ldr x0, [x29, #16]  // dst
	str x0, [x29, #32]  // 実引数
	ldr x0, [x29, #24]  // n
	str x0, [x29, #40]  // 実引数
	ldr x0, [x29, #32]
	ldr x1, [x29, #40]
	ldp x29, x30, [sp], #48  // フレームを戻す
	b std_neg  // 兄弟への末尾呼び出し
	b .L22
.L23:
	ldr x0, [x29, #16]  // dst
	str x0, [x29, #32]  // 実引数
	ldr x0, [x29, #24]  // n
	str x0, [x29, #40]  // 実引数
	ldr x0, [x29, #32]
	ldr x1, [x29, #40]
	ldp x29, x30, [sp], #48  // フレームを戻す
	b std_uint  // 兄弟への末尾呼び出し
.L22:
	ldp x29, x30, [sp], #48  // フレームを戻す
	ret

std_neg:
	stp x29, x30, [sp, #-64]!  // フレーム 64 バイト
	mov x29, sp
	str x0, [x29, #32]  // 番地
	ldr x9, [x29, #32]
	str x0, [x29, #16]  // 仮引数 dst
	movz x10, #0x900, lsl #16
	str x1, [x29, #24]  // 仮引数 n
	mov x0, #45
	cmp x9, x10
	b.lo .L28
	mov x1, #4  // 幅
	bl _sign_dev_st  // 装置への書き込み(実機の中継。sign_realdev.py)
	b .L29
.L28:
	str w0, [x9]  // 幅 4 byte で書く(value_representation.md §5。値はその幅へ切れる)
.L29:
.L27:
	mov x0, #1
	str x0, [x29, #32]  // 途中の値はフレームへ
	ldr x0, [x29, #16]  // dst
	ldr x10, [x29, #24]  // n
	adds x9, x0, #4
	ccmp xzr, x9, #1, vc  // 溢れずに INT64_MIN に着いた結果も罠
	b.vs .Ltrap
	mov x0, #0
	subs x1, x0, x10
	str x9, [x29, #40]  // 実引数
	ccmp xzr, x1, #1, vc
	b.vs .Ltrap
	mov x0, x9
	bl std_uint
	ldr x9, [x29, #32]
	movz x13, #0x8000, lsl #48  // __
	cmp x0, x13
	b.ne .L31
	mov x0, x9
	b .L30
.L31:
	adds x9, x9, x0
	ccmp xzr, x9, #1, vc  // 溢れずに INT64_MIN に着いた結果も罠
	b.vs .Ltrap
	mov x0, x9
.L30:
	b .L25
.L26:
	movz x0, #0x8000, lsl #48  // __
.L25:
	ldp x29, x30, [sp], #64  // フレームを戻す
	ret

std_ndig:
	stp x29, x30, [sp, #-64]!  // フレーム 48 バイト
	mov x29, sp
	stp x19, x20, [x29, #48]  // 呼ぶ側のために保存(x19〜x28 は呼び出し先が保つ約束)
	mov x19, x0  // 仮引数 n
	mov x20, x1  // 仮引数 d
	mov x10, #10
.L32:
	cmp x19, #10
	b.ge .L34
	mov x0, x20  // d
	b .L33
.L34:
	sdiv x0, x19, x10  // 商は被除数を超えず、値域は対称なので溢れない(integer_overflow.md §1.1)
	adds x9, x20, #1
	ccmp xzr, x9, #1, vc  // 溢れずに INT64_MIN に着いた結果も罠
	b.vs .Ltrap
	mov x20, x9  // 仮引数 d を更新
	mov x19, x0  // 実引数
	b .L32  // 自分への末尾呼び出し
.L33:
	ldp x19, x20, [x29, #48]  // 保存したレジスタを戻す
	ldp x29, x30, [sp], #64  // フレームを戻す
	ret

std_uint:
	stp x29, x30, [sp, #-64]!  // フレーム 64 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 dst
	str x1, [x29, #24]  // 仮引数 n
	ldr x0, [x29, #16]  // dst
	str x0, [x29, #32]  // 実引数
	ldr x0, [x29, #24]  // n
	str x0, [x29, #40]  // 実引数
	ldr x0, [x29, #24]  // n
	str x0, [x29, #48]  // 実引数
	mov x1, #1  // 実引数(字面)
	bl std_ndig
	str x0, [x29, #48]  // 実引数
	ldr x0, [x29, #32]
	ldr x1, [x29, #40]
	ldr x2, [x29, #48]
	ldp x29, x30, [sp], #64  // フレームを戻す
	b std_uint2  // 兄弟への末尾呼び出し
	ldp x29, x30, [sp], #64  // フレームを戻す
	ret

std_uint2:
	stp x29, x30, [sp, #-80]!  // フレーム 80 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 dst
	str x0, [x29, #40]  // 途中の値はフレームへ
	mov x0, #4  // STD_W4
	mul x11, x0, x2
	smulh x12, x0, x2  // 積の上の語
	ldr x9, [x29, #40]
	str x1, [x29, #24]  // 仮引数 n
	cmp x12, x11, asr #63  // 上の語が下の語の符号の伸びでなければ溢れた
	str x2, [x29, #32]  // 仮引数 nd
	ccmp xzr, x11, #1, eq
	b.vs .Ltrap
	adds x9, x9, x11
	ccmp xzr, x9, #1, vc  // 溢れずに INT64_MIN に着いた結果も罠
	b.vs .Ltrap
	movz x10, #0x900, lsl #16
	mov x0, #0
	cmp x9, x10
	b.lo .L38
	mov x1, #4  // 幅
	bl _sign_dev_st  // 装置への書き込み(実機の中継。sign_realdev.py)
	b .L39
.L38:
	str w0, [x9]  // 幅 4 byte で書く(value_representation.md §5。値はその幅へ切れる)
.L39:
.L37:
	ldr x0, [x29, #16]  // dst
	str x9, [x29, #40]  // 実引数
	str x0, [x29, #48]  // 実引数
	ldr x0, [x29, #24]  // n
	str x0, [x29, #56]  // 実引数
	ldr x0, [x29, #32]  // nd
	ldr x1, [x29, #56]
	str x0, [x29, #64]  // 実引数
	ldr x0, [x29, #48]
	ldr x2, [x29, #64]
	bl std_uw
	str x0, [x29, #48]  // 実引数
	ldr x0, [x29, #32]  // nd
	ldr x9, [x29, #48]
	movz x13, #0x8000, lsl #48  // __
	str x0, [x29, #56]  // 実引数
	cmp x9, x13
	b.eq .L40  // 引数が __ なら呼び全体が __
	ldr x0, [x29, #40]
	ldr x2, [x29, #56]
	mov x1, x9
	bl seq3
	b .L41
.L40:
	movz x0, #0x8000, lsl #48  // __
.L41:
	ldp x29, x30, [sp], #80  // フレームを戻す
	ret

std_uw:
	stp x29, x30, [sp, #-112]!  // フレーム 64 バイト
	mov x29, sp
	stp x26, x27, [x29, #80]  // 呼ぶ側のために保存(x19〜x28 は呼び出し先が保つ約束)
	str x28, [x29, #96]  // 呼ぶ側のために保存(x19〜x28 は呼び出し先が保つ約束)
	stp x19, x20, [x29, #64]  // 呼ぶ側のために保存(x19〜x28 は呼び出し先が保つ約束)
	mov x28, x0  // 仮引数 dst
	mov x27, x1  // 仮引数 n
	mov x26, x2  // 仮引数 i
.L42:
	cmp x26, #0
	b.gt .L44
	mov x0, #0
	b .L43
.L44:
	mov x0, #4  // STD_W4
	mov x20, x0  // 途中の値はフレームへ
	subs x9, x26, #1
	mul x11, x20, x9
	smulh x12, x20, x9  // 積の上の語
	ccmp xzr, x9, #1, vc
	b.vs .Ltrap
	cmp x12, x11, asr #63  // 上の語が下の語の符号の伸びでなければ溢れた
	ccmp xzr, x11, #1, eq
	b.vs .Ltrap
	adds x9, x28, x11
	mov x10, #10
	sdiv x11, x27, x10
	mov x0, #48
	mov x20, x0  // 途中の値はフレームへ
	ccmp xzr, x9, #1, vc  // 溢れずに INT64_MIN に着いた結果も罠
	b.vs .Ltrap
	mov x19, x9  // 番地
	mov x9, x19
	msub x0, x11, x10, x27  // 余り = 被除数 - 商 × 割る数
	adds x0, x20, x0
	ccmp xzr, x0, #1, vc  // 溢れずに INT64_MIN に着いた結果も罠
	b.vs .Ltrap
	movz x10, #0x900, lsl #16
	cmp x19, x10
	b.lo .L47
	mov x1, #4  // 幅
	bl _sign_dev_st  // 装置への書き込み(実機の中継。sign_realdev.py)
	b .L48
.L47:
	str w0, [x9]  // 幅 4 byte で書く(value_representation.md §5。値はその幅へ切れる)
.L48:
.L46:
	mov x10, #10
	sdiv x0, x27, x10  // 商は被除数を超えず、値域は対称なので溢れない(integer_overflow.md §1.1)
	subs x9, x26, #1
	ccmp xzr, x9, #1, vc
	b.vs .Ltrap
	mov x26, x9  // 仮引数 i を更新
	mov x19, x0  // 実引数
	mov x27, x19  // 仮引数 n を更新
	b .L42  // 自分への末尾呼び出し
	b .L43
.L45:
	movz x0, #0x8000, lsl #48  // __
.L43:
	ldr x28, [x29, #96]  // 保存したレジスタを戻す
	ldp x19, x20, [x29, #64]  // 保存したレジスタを戻す
	ldp x26, x27, [x29, #80]  // 保存したレジスタを戻す
	ldp x29, x30, [sp], #112  // フレームを戻す
	ret

print:
	stp x29, x30, [sp, #-64]!  // フレーム 64 バイト
	mov x29, sp
	mov x2, #0  // 実引数(字面)
	bl std_pr
	ldp x29, x30, [sp], #64  // フレームを戻す
	ret

std_pr:
	stp x29, x30, [sp, #-96]!  // フレーム 64 バイト
	mov x29, sp
	stp x19, x26, [x29, #64]  // 呼ぶ側のために保存(x19〜x28 は呼び出し先が保つ約束)
	stp x27, x28, [x29, #80]  // 呼ぶ側のために保存(x19〜x28 は呼び出し先が保つ約束)
	mov x27, x0  // 仮引数 s.ptr
	mov x28, x1  // 仮引数 s.len
	mov x26, x2  // 仮引数 i
.L50:
	cmp x26, x28
	b.lt .L52
	mov x0, #0
	b .L51
.L52:
	movz x0, #0x900, lsl #16  // STD_UART
	mov x19, x0  // 番地
	mov x11, x26
	mov x9, x27  // s.ptr
	cmp x26, #0
	b.ge .L56
	add x11, x11, x28  // 負の添字は後ろから
.L56:
	cmp x11, x28
	b.hs .L54  // 範囲の外(符号なしで比べると、後ろからでも足りない負の数も外れる)。読まない
	ldrb w0, [x9, x11]  // 文字(ASCII の 1 バイト)
	b .L55
.L54:
	mov x0, #0  // Char の `__` は U+0000(niche)
.L55:
	movz x10, #0x900, lsl #16
	mov x9, x19
	cmp x19, x10
	b.lo .L58
	mov x1, #8  // 幅
	bl _sign_dev_st  // 装置への書き込み(実機の中継。sign_realdev.py)
	b .L59
.L58:
	str x0, [x19]  // 64 ビットで書く(装置・普通のメモリの区別は処理系の仮想装置の領分。実機では番地が実在することが前提)
.L59:
.L57:
	adds x9, x26, #1
	ccmp xzr, x9, #1, vc  // 溢れずに INT64_MIN に着いた結果も罠
	mov x1, x28  // s.len
	b.vs .Ltrap
	mov x26, x9  // 仮引数 i を更新
	b .L50  // 自分への末尾呼び出し
	b .L51
.L53:
	mov x0, #0
.L51:
	ldp x19, x26, [x29, #64]  // 保存したレジスタを戻す
	ldp x27, x28, [x29, #80]  // 保存したレジスタを戻す
	ldp x29, x30, [sp], #96  // フレームを戻す
	ret

print_mem:
	stp x29, x30, [sp, #-32]!  // フレーム 32 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 p
	str x0, [x29, #24]  // 実引数
	ldp x29, x30, [sp], #32  // フレームを戻す
	b std_pm  // 兄弟への末尾呼び出し
	ldp x29, x30, [sp], #32  // フレームを戻す
	ret

std_pm:
	stp x29, x30, [sp, #-48]!  // フレーム 32 バイト
	mov x29, sp
	stp x26, x27, [x29, #32]  // 呼ぶ側のために保存(x19〜x28 は呼び出し先が保つ約束)
	mov x26, x0  // 仮引数 p
.L61:
	movz x10, #0x900, lsl #16
	mov x0, x26  // p
	cmp x26, x10
	b.lo .L64
	mov x1, #4  // 幅
	bl _sign_dev_ld  // 装置からの読み(実機の中継。sign_realdev.py)
	b .L65
.L64:
	ldr w0, [x0]  // 幅 4 byte で読む(ゼロ拡張)
.L65:
	movz x13, #0x8000, lsl #48  // __
	mov x9, x0
	cmp x0, x13
	b.eq .L63  // __ との比較は外れ
	cmp x0, #0
	b.ne .L63
	mov x0, #0
	b .L62
.L63:
	movz x0, #0x900, lsl #16  // STD_UART
	mov x27, x0  // 番地
	movz x10, #0x900, lsl #16
	mov x0, x26  // p
	cmp x26, x10
	b.lo .L67
	mov x1, #4  // 幅
	bl _sign_dev_ld  // 装置からの読み(実機の中継。sign_realdev.py)
	b .L68
.L67:
	ldr w0, [x0]  // 幅 4 byte で読む(ゼロ拡張)
.L68:
	movz x13, #0x8000, lsl #48  // __
	mov x9, x27
	cmp x0, x13
	b.eq .L69  // 値が __ なら何も書かない(番地は返る)
	movz x10, #0x900, lsl #16
	cmp x27, x10
	b.lo .L70
	mov x1, #8  // 幅
	bl _sign_dev_st  // 装置への書き込み(実機の中継。sign_realdev.py)
	b .L71
.L70:
	str x0, [x27]  // 64 ビットで書く(装置・普通のメモリの区別は処理系の仮想装置の領分。実機では番地が実在することが前提)
.L71:
.L69:
	adds x9, x26, #4
	ccmp xzr, x9, #1, vc  // 溢れずに INT64_MIN に着いた結果も罠
	b.vs .Ltrap
	mov x26, x9  // 仮引数 p を更新
	b .L61  // 自分への末尾呼び出し
	b .L62
.L66:
	movz x0, #0x8000, lsl #48  // __
.L62:
	ldp x26, x27, [x29, #32]  // 保存したレジスタを戻す
	ldp x29, x30, [sp], #48  // フレームを戻す
	ret

print_int:
	stp x29, x30, [sp, #-48]!  // フレーム 48 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 n
	bl std_isi
	movz x13, #0x8000, lsl #48  // __
	cmp x0, x13
	b.eq .L74  // __ は偽
	movz x0, #0x7f, lsl #16  // STD_TMP
	str x0, [x29, #24]  // 実引数
	ldr x0, [x29, #16]  // n
	str x0, [x29, #32]  // 実引数
	ldr x0, [x29, #24]
	ldr x1, [x29, #32]
	bl str_int
	str x0, [x29, #24]  // 実引数
	movz x0, #0x7f, lsl #16  // STD_TMP
	bl print_mem
	ldr x9, [x29, #24]
	movz x13, #0x8000, lsl #48  // __
	cmp x9, x13
	b.eq .L75  // 引数が __ なら呼び全体が __
	mov x9, x0
	cmp x0, x13
	b.eq .L75  // 引数が __ なら呼び全体が __
	ldr x0, [x29, #24]
	mov x1, x9
	bl seq2
	b .L76
.L75:
	movz x0, #0x8000, lsl #48  // __
.L76:
	b .L73
.L74:
	movz x0, #0x8000, lsl #48  // __
.L73:
	ldp x29, x30, [sp], #48  // フレームを戻す
	ret

println_int:
	stp x29, x30, [sp, #-48]!  // フレーム 48 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 n
	bl std_isi
	movz x13, #0x8000, lsl #48  // __
	cmp x0, x13
	b.eq .L79  // __ は偽
	ldr x0, [x29, #16]  // n
	bl print_int
	str x0, [x29, #24]  // 実引数
	movz x0, #0x900, lsl #16  // STD_UART
	str x0, [x29, #32]  // 番地
	ldr x9, [x29, #32]
	movz x10, #0x900, lsl #16
	mov x0, #10
	cmp x9, x10
	b.lo .L81
	mov x1, #8  // 幅
	bl _sign_dev_st  // 装置への書き込み(実機の中継。sign_realdev.py)
	b .L82
.L81:
	str x0, [x9]  // 64 ビットで書く(装置・普通のメモリの区別は処理系の仮想装置の領分。実機では番地が実在することが前提)
.L82:
.L80:
	mov x0, x9  // 答えは番地
	mov x1, #0  // 実引数(字面)
	bl seq2
	ldr x9, [x29, #24]
	movz x13, #0x8000, lsl #48  // __
	str x0, [x29, #32]  // 実引数
	cmp x9, x13
	b.eq .L83  // 引数が __ なら呼び全体が __
	mov x0, x9
	ldr x1, [x29, #32]
	bl seq2
	b .L84
.L83:
	movz x0, #0x8000, lsl #48  // __
.L84:
	b .L78
.L79:
	movz x0, #0x8000, lsl #48  // __
.L78:
	ldp x29, x30, [sp], #48  // フレームを戻す
	ret

newline:
	stp x29, x30, [sp, #-48]!  // フレーム 48 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 z
	movz x0, #0x900, lsl #16  // STD_UART
	str x0, [x29, #24]  // 番地
	mov x0, #10
	ldr x9, [x29, #24]
	movz x10, #0x900, lsl #16
	cmp x9, x10
	b.lo .L87
	mov x1, #8  // 幅
	bl _sign_dev_st  // 装置への書き込み(実機の中継。sign_realdev.py)
	b .L88
.L87:
	str x0, [x9]  // 64 ビットで書く(装置・普通のメモリの区別は処理系の仮想装置の領分。実機では番地が実在することが前提)
.L88:
.L86:
	mov x0, x9  // 答えは番地
	str x0, [x29, #24]  // 実引数
	mov x1, #0  // 実引数(字面)
	ldp x29, x30, [sp], #48  // フレームを戻す
	b seq2  // 兄弟への末尾呼び出し
	ldp x29, x30, [sp], #48  // フレームを戻す
	ret

std_isi:
	stp x29, x30, [sp, #-32]!  // フレーム 32 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 n
	mov x9, x0
	mov x10, x0  // n
	and x0, x9, x10
	movz x13, #0x8000, lsl #48  // __
	cmp x0, x13
	b.eq .Ltrap  // 結果が __ の印と同じ値(INT64_MIN)は値域の外
	str x0, [x29, #24]  // 実引数
	ldp x29, x30, [sp], #32  // フレームを戻す
	b std_isi1  // 兄弟への末尾呼び出し
	ldp x29, x30, [sp], #32  // フレームを戻す
	ret

std_isi1:
	stp x29, x30, [sp, #-32]!  // フレーム 32 バイト
	mov x29, sp
	cmp x0, #0
	b.lt .L94
.L93:
	cmp x0, #0
	b.lt .L92
.L94:
	mov x0, #1
	b .L91
.L92:
	movz x0, #0x8000, lsl #48  // __
.L91:
	ldp x29, x30, [sp], #32  // フレームを戻す
	ret

db_s32:
	stp x29, x30, [sp, #-32]!  // フレーム 32 バイト
	mov x29, sp
	movz x10, #0x8000, lsl #16
	cmp x0, x10
	b.lt .L97
	movz x10, #0x1, lsl #32
	subs x0, x0, x10
	ccmp xzr, x0, #1, vc
	b.vs .Ltrap
	b .L96
.L97:
.L96:
	ldp x29, x30, [sp], #32  // フレームを戻す
	ret

db_call:
	stp x29, x30, [sp, #-112]!  // フレーム 112 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 n
	movz x0, #0x9a0, lsl #16  // DB_DEV
	str x0, [x29, #56]  // 番地
	ldr x9, [x29, #56]
	ldr x0, [x29, #16]  // n
	movz x10, #0x900, lsl #16
	str x1, [x29, #24]  // 仮引数 a
	str x2, [x29, #32]  // 仮引数 b
	str x3, [x29, #40]  // 仮引数 c
	str x4, [x29, #48]  // 仮引数 d
	cmp x9, x10
	b.lo .L100
	mov x1, #4  // 幅
	bl _sign_dev_st  // 装置への書き込み(実機の中継。sign_realdev.py)
	b .L101
.L100:
	str w0, [x9]  // 幅 4 byte で書く(value_representation.md §5。値はその幅へ切れる)
.L101:
.L99:
	str x9, [x29, #56]  // 実引数
	movz x0, #0x9a0, lsl #16  // DB_DEV
	adds x9, x0, #4
	ldr x0, [x29, #24]  // a
	ccmp xzr, x9, #1, vc  // 溢れずに INT64_MIN に着いた結果も罠
	b.vs .Ltrap
	movz x10, #0x900, lsl #16
	cmp x9, x10
	b.lo .L103
	mov x1, #4  // 幅
	bl _sign_dev_st  // 装置への書き込み(実機の中継。sign_realdev.py)
	b .L104
.L103:
	str w0, [x9]  // 幅 4 byte で書く(value_representation.md §5。値はその幅へ切れる)
.L104:
.L102:
	str x9, [x29, #64]  // 実引数
	movz x0, #0x9a0, lsl #16  // DB_DEV
	adds x9, x0, #8
	ldr x0, [x29, #32]  // b
	ccmp xzr, x9, #1, vc  // 溢れずに INT64_MIN に着いた結果も罠
	b.vs .Ltrap
	movz x10, #0x900, lsl #16
	cmp x9, x10
	b.lo .L106
	mov x1, #4  // 幅
	bl _sign_dev_st  // 装置への書き込み(実機の中継。sign_realdev.py)
	b .L107
.L106:
	str w0, [x9]  // 幅 4 byte で書く(value_representation.md §5。値はその幅へ切れる)
.L107:
.L105:
	str x9, [x29, #72]  // 実引数
	movz x0, #0x9a0, lsl #16  // DB_DEV
	adds x9, x0, #12
	ldr x0, [x29, #40]  // c
	ccmp xzr, x9, #1, vc  // 溢れずに INT64_MIN に着いた結果も罠
	b.vs .Ltrap
	movz x10, #0x900, lsl #16
	cmp x9, x10
	b.lo .L109
	mov x1, #4  // 幅
	bl _sign_dev_st  // 装置への書き込み(実機の中継。sign_realdev.py)
	b .L110
.L109:
	str w0, [x9]  // 幅 4 byte で書く(value_representation.md §5。値はその幅へ切れる)
.L110:
.L108:
	str x9, [x29, #80]  // 実引数
	movz x0, #0x9a0, lsl #16  // DB_DEV
	adds x9, x0, #16
	ldr x0, [x29, #48]  // d
	ccmp xzr, x9, #1, vc  // 溢れずに INT64_MIN に着いた結果も罠
	b.vs .Ltrap
	movz x10, #0x900, lsl #16
	cmp x9, x10
	b.lo .L112
	mov x1, #4  // 幅
	bl _sign_dev_st  // 装置への書き込み(実機の中継。sign_realdev.py)
	b .L113
.L112:
	str w0, [x9]  // 幅 4 byte で書く(value_representation.md §5。値はその幅へ切れる)
.L113:
.L111:
	str x9, [x29, #88]  // 実引数
	movz x0, #0x9a0, lsl #16  // DB_DEV
	adds x9, x0, #32
	ccmp xzr, x9, #1, vc  // 溢れずに INT64_MIN に着いた結果も罠
	b.vs .Ltrap
	movz x10, #0x900, lsl #16
	mov x0, #1
	cmp x9, x10
	b.lo .L115
	mov x1, #4  // 幅
	bl _sign_dev_st  // 装置への書き込み(実機の中継。sign_realdev.py)
	b .L116
.L115:
	str w0, [x9]  // 幅 4 byte で書く(value_representation.md §5。値はその幅へ切れる)
.L116:
.L114:
	str x9, [x29, #96]  // 実引数
	movz x0, #0x9a0, lsl #16  // DB_DEV
	adds x9, x0, #36
	ccmp xzr, x9, #1, vc  // 溢れずに INT64_MIN に着いた結果も罠
	b.vs .Ltrap
	mov x0, x9
	movz x10, #0x900, lsl #16
	cmp x0, x10
	b.lo .L117
	mov x1, #4  // 幅
	bl _sign_dev_ld  // 装置からの読み(実機の中継。sign_realdev.py)
	b .L118
.L117:
	ldr w0, [x0]  // 幅 4 byte で読む(ゼロ拡張)
.L118:
	movz x13, #0x8000, lsl #48  // __
	cmp x0, x13
	b.eq .L119  // 引数が __ なら呼び全体が __
	bl db_s32
	b .L120
.L119:
	movz x0, #0x8000, lsl #48  // __
.L120:
	movz x13, #0x8000, lsl #48  // __
	mov x9, x0
	cmp x0, x13
	b.eq .L121  // 引数が __ なら呼び全体が __
	ldr x0, [x29, #56]
	ldr x1, [x29, #64]
	ldr x2, [x29, #72]
	ldr x3, [x29, #80]
	ldr x4, [x29, #88]
	ldr x5, [x29, #96]
	mov x6, x9
	bl seq7
	b .L122
.L121:
	movz x0, #0x8000, lsl #48  // __
.L122:
	ldp x29, x30, [sp], #112  // フレームを戻す
	ret

db_str:
	stp x29, x30, [sp, #-96]!  // フレーム 96 バイト
	mov x29, sp
	mov x4, x2
	bl db_str2
	ldp x29, x30, [sp], #96  // フレームを戻す
	ret

db_str2:
	stp x29, x30, [sp, #-80]!  // フレーム 80 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 buf
	mov x10, #4
	sdiv x0, x3, x10  // 商は被除数を超えず、値域は対称なので溢れない(integer_overflow.md §1.1)
	cmp x4, x0
	b.ge .L126
	ldr x0, [x29, #16]  // buf
	bl str_put
	str x0, [x29, #56]  // 実引数
	ldr x0, [x29, #16]  // buf
	ldr x9, [x29, #56]
	movz x13, #0x8000, lsl #48  // __
	str x0, [x29, #64]  // 実引数
	cmp x9, x13
	b.eq .L127  // 引数が __ なら呼び全体が __
	mov x0, x9
	ldr x1, [x29, #64]
	bl seq2
	b .L128
.L127:
	movz x0, #0x8000, lsl #48  // __
.L128:
	b .L125
.L126:
	movz x0, #0x8000, lsl #48  // __
.L125:
	ldp x29, x30, [sp], #80  // フレームを戻す
	ret

db_open_mem:
	stp x29, x30, [sp, #-80]!  // フレーム 80 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 p
	str x1, [x29, #24]  // 仮引数 flags
	ldr x0, [x29, #16]  // p
	str x0, [x29, #40]  // 実引数
	ldr x0, [x29, #24]  // flags
	str x0, [x29, #48]  // 実引数
	mov x0, #1  // 実引数(字面)
	ldr x1, [x29, #40]
	ldr x2, [x29, #48]
	mov x3, #0  // 実引数(字面)
	mov x4, #0  // 実引数(字面)
	ldp x29, x30, [sp], #80  // フレームを戻す
	b db_call  // 兄弟への末尾呼び出し
	ldp x29, x30, [sp], #80  // フレームを戻す
	ret

db_open:
	stp x29, x30, [sp, #-80]!  // フレーム 80 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 path.ptr
	movz x0, #0x2000  // DB_PATH
	movk x0, #0x7c, lsl #16
	str x0, [x29, #40]  // 実引数
	ldr x0, [x29, #16]  // path.ptr
	str x2, [x29, #32]  // 仮引数 flags
	str x1, [x29, #56]  // 実引数(len)
	ldr x2, [x29, #56]
	str x0, [x29, #48]  // 実引数(ptr)
	mov x0, #4096
	str x0, [x29, #64]  // 実引数
	ldr x0, [x29, #40]
	ldr x1, [x29, #48]
	ldr x3, [x29, #64]
	bl db_str
	str x0, [x29, #40]  // 実引数
	ldr x0, [x29, #32]  // flags
	ldr x9, [x29, #40]
	movz x13, #0x8000, lsl #48  // __
	str x0, [x29, #48]  // 実引数
	cmp x9, x13
	b.eq .L131  // 引数が __ なら呼び全体が __
	mov x0, x9
	ldr x1, [x29, #48]
	bl db_open_mem
	b .L132
.L131:
	movz x0, #0x8000, lsl #48  // __
.L132:
	ldp x29, x30, [sp], #80  // フレームを戻す
	ret

db_close:
	stp x29, x30, [sp, #-64]!  // フレーム 64 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 h
	str x0, [x29, #32]  // 実引数
	mov x0, #2  // 実引数(字面)
	ldr x1, [x29, #32]
	mov x2, #0  // 実引数(字面)
	mov x3, #0  // 実引数(字面)
	mov x4, #0  // 実引数(字面)
	ldp x29, x30, [sp], #64  // フレームを戻す
	b db_call  // 兄弟への末尾呼び出し
	ldp x29, x30, [sp], #64  // フレームを戻す
	ret

db_exec_mem:
	stp x29, x30, [sp, #-80]!  // フレーム 80 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 h
	str x1, [x29, #24]  // 仮引数 p
	ldr x0, [x29, #16]  // h
	str x0, [x29, #40]  // 実引数
	ldr x0, [x29, #24]  // p
	str x0, [x29, #48]  // 実引数
	mov x0, #3  // 実引数(字面)
	ldr x1, [x29, #40]
	ldr x2, [x29, #48]
	mov x3, #0  // 実引数(字面)
	mov x4, #0  // 実引数(字面)
	ldp x29, x30, [sp], #80  // フレームを戻す
	b db_call  // 兄弟への末尾呼び出し
	ldp x29, x30, [sp], #80  // フレームを戻す
	ret

db_exec:
	stp x29, x30, [sp, #-80]!  // フレーム 80 バイト
	mov x29, sp
	str x0, [x29, #40]  // 実引数
	movz x0, #0x7d, lsl #16  // DB_SQL
	str x0, [x29, #48]  // 実引数
	movz x0, #0x1, lsl #16
	str x0, [x29, #72]  // 実引数
	ldr x0, [x29, #48]
	ldr x3, [x29, #72]
	bl db_str
	movz x13, #0x8000, lsl #48  // __
	mov x9, x0
	cmp x0, x13
	b.eq .L136  // 引数が __ なら呼び全体が __
	ldr x0, [x29, #40]
	mov x1, x9
	bl db_exec_mem
	b .L137
.L136:
	movz x0, #0x8000, lsl #48  // __
.L137:
	ldp x29, x30, [sp], #80  // フレームを戻す
	ret

db_prep_mem:
	stp x29, x30, [sp, #-80]!  // フレーム 80 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 h
	str x1, [x29, #24]  // 仮引数 p
	ldr x0, [x29, #16]  // h
	str x0, [x29, #40]  // 実引数
	ldr x0, [x29, #24]  // p
	str x0, [x29, #48]  // 実引数
	mov x0, #4  // 実引数(字面)
	ldr x1, [x29, #40]
	ldr x2, [x29, #48]
	mov x3, #0  // 実引数(字面)
	mov x4, #0  // 実引数(字面)
	ldp x29, x30, [sp], #80  // フレームを戻す
	b db_call  // 兄弟への末尾呼び出し
	ldp x29, x30, [sp], #80  // フレームを戻す
	ret

db_prep:
	stp x29, x30, [sp, #-80]!  // フレーム 80 バイト
	mov x29, sp
	str x0, [x29, #40]  // 実引数
	movz x0, #0x7d, lsl #16  // DB_SQL
	str x0, [x29, #48]  // 実引数
	movz x0, #0x1, lsl #16
	str x0, [x29, #72]  // 実引数
	ldr x0, [x29, #48]
	ldr x3, [x29, #72]
	bl db_str
	movz x13, #0x8000, lsl #48  // __
	mov x9, x0
	cmp x0, x13
	b.eq .L140  // 引数が __ なら呼び全体が __
	ldr x0, [x29, #40]
	mov x1, x9
	bl db_prep_mem
	b .L141
.L140:
	movz x0, #0x8000, lsl #48  // __
.L141:
	ldp x29, x30, [sp], #80  // フレームを戻す
	ret

db_step:
	stp x29, x30, [sp, #-64]!  // フレーム 64 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 s
	str x0, [x29, #32]  // 実引数
	mov x0, #9  // 実引数(字面)
	ldr x1, [x29, #32]
	mov x2, #0  // 実引数(字面)
	mov x3, #0  // 実引数(字面)
	mov x4, #0  // 実引数(字面)
	ldp x29, x30, [sp], #64  // フレームを戻す
	b db_call  // 兄弟への末尾呼び出し
	ldp x29, x30, [sp], #64  // フレームを戻す
	ret

db_cols:
	stp x29, x30, [sp, #-64]!  // フレーム 64 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 s
	str x0, [x29, #32]  // 実引数
	mov x0, #10  // 実引数(字面)
	ldr x1, [x29, #32]
	mov x2, #0  // 実引数(字面)
	mov x3, #0  // 実引数(字面)
	mov x4, #0  // 実引数(字面)
	ldp x29, x30, [sp], #64  // フレームを戻す
	b db_call  // 兄弟への末尾呼び出し
	ldp x29, x30, [sp], #64  // フレームを戻す
	ret

db_text:
	stp x29, x30, [sp, #-96]!  // フレーム 96 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 s
	str x1, [x29, #24]  // 仮引数 i
	str x2, [x29, #32]  // 仮引数 dst
	str x3, [x29, #40]  // 仮引数 max_
	ldr x0, [x29, #16]  // s
	str x0, [x29, #56]  // 実引数
	ldr x0, [x29, #24]  // i
	str x0, [x29, #64]  // 実引数
	ldr x0, [x29, #32]  // dst
	str x0, [x29, #72]  // 実引数
	ldr x0, [x29, #40]  // max_
	str x0, [x29, #80]  // 実引数
	mov x0, #13  // 実引数(字面)
	ldr x1, [x29, #56]
	ldr x2, [x29, #64]
	ldr x3, [x29, #72]
	ldr x4, [x29, #80]
	ldp x29, x30, [sp], #96  // フレームを戻す
	b db_call  // 兄弟への末尾呼び出し
	ldp x29, x30, [sp], #96  // フレームを戻す
	ret

db_rowid:
	stp x29, x30, [sp, #-64]!  // フレーム 64 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 h
	str x0, [x29, #32]  // 実引数
	mov x0, #17  // 実引数(字面)
	ldr x1, [x29, #32]
	mov x2, #0  // 実引数(字面)
	mov x3, #0  // 実引数(字面)
	mov x4, #0  // 実引数(字面)
	ldp x29, x30, [sp], #64  // フレームを戻す
	b db_call  // 兄弟への末尾呼び出し
	ldp x29, x30, [sp], #64  // フレームを戻す
	ret

db_changes:
	stp x29, x30, [sp, #-64]!  // フレーム 64 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 h
	str x0, [x29, #32]  // 実引数
	mov x0, #18  // 実引数(字面)
	ldr x1, [x29, #32]
	mov x2, #0  // 実引数(字面)
	mov x3, #0  // 実引数(字面)
	mov x4, #0  // 実引数(字面)
	ldp x29, x30, [sp], #64  // フレームを戻す
	b db_call  // 兄弟への末尾呼び出し
	ldp x29, x30, [sp], #64  // フレームを戻す
	ret

db_print_cols:
	stp x29, x30, [sp, #-96]!  // フレーム 96 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 s
	cmp x1, x2
	b.lt .L149
	mov x0, #0
	b .L148
.L149:
	str x0, [x29, #40]  // 実引数
	ldr x0, [x29, #16]  // s
	str x2, [x29, #56]  // 実引数
	str x1, [x29, #48]  // 実引数
	mov x3, #4096  // 実引数(字面)
	str x0, [x29, #64]  // 実引数
	movz x0, #0x1000  // DB_TMP
	movk x0, #0x7c, lsl #16
	str x0, [x29, #80]  // 実引数
	ldr x0, [x29, #64]
	ldr x2, [x29, #80]
	bl db_text
	movz x13, #0x8000, lsl #48  // __
	mov x9, x0
	cmp x0, x13
	b.eq .L150  // 引数が __ なら呼び全体が __
	ldr x0, [x29, #40]
	ldr x1, [x29, #48]
	ldr x2, [x29, #56]
	mov x3, x9
	bl db_print_col
	b .L151
.L150:
	movz x0, #0x8000, lsl #48  // __
.L151:
.L148:
	ldp x29, x30, [sp], #96  // フレームを戻す
	ret

db_print_col:
	stp x29, x30, [sp, #-96]!  // フレーム 96 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 s
	str x1, [x29, #24]  // 仮引数 i
	str x2, [x29, #32]  // 仮引数 n
	cmp x3, #0
	b.ge .L154
	mov x0, x3  // r
	b .L153
.L154:
	movz x0, #0x1000  // DB_TMP
	movk x0, #0x7c, lsl #16
	bl print_mem
	str x0, [x29, #48]  // 実引数
	ldr x0, [x29, #16]  // s
	str x0, [x29, #56]  // 実引数
	ldr x0, [x29, #24]  // i
	str x0, [x29, #64]  // 実引数
	ldr x0, [x29, #32]  // n
	ldr x1, [x29, #64]
	str x0, [x29, #72]  // 実引数
	ldr x0, [x29, #56]
	ldr x2, [x29, #72]
	bl db_tab
	str x0, [x29, #56]  // 実引数
	ldr x0, [x29, #16]  // s
	str x0, [x29, #64]  // 実引数
	ldr x0, [x29, #24]  // i
	adds x1, x0, #1
	ldr x0, [x29, #32]  // n
	ccmp xzr, x1, #1, vc  // 溢れずに INT64_MIN に着いた結果も罠
	b.vs .Ltrap
	str x0, [x29, #80]  // 実引数
	ldr x0, [x29, #64]
	ldr x2, [x29, #80]
	bl db_print_cols
	ldr x9, [x29, #48]
	movz x13, #0x8000, lsl #48  // __
	cmp x9, x13
	b.eq .L155  // 引数が __ なら呼び全体が __
	mov x9, x0
	cmp x0, x13
	b.eq .L155  // 引数が __ なら呼び全体が __
	ldr x0, [x29, #48]
	ldr x1, [x29, #56]
	mov x2, x9
	bl seq3
	b .L156
.L155:
	movz x0, #0x8000, lsl #48  // __
.L156:
.L153:
	ldp x29, x30, [sp], #96  // フレームを戻す
	ret

db_tab:
	stp x29, x30, [sp, #-64]!  // フレーム 64 バイト
	mov x29, sp
	adds x9, x1, #1
	ccmp xzr, x9, #1, vc  // 溢れずに INT64_MIN に着いた結果も罠
	b.vs .Ltrap
	cmp x9, x2
	b.ge .L159
	adrp x0, .Lstr0  // リストの像(.rodata)
	add x0, x0, :lo12:.Lstr0
	mov x1, #1  // 長さ
	bl print
	b .L158
.L159:
	mov x0, #0
.L158:
	ldp x29, x30, [sp], #64  // フレームを戻す
	ret

db_print_row:
	stp x29, x30, [sp, #-48]!  // フレーム 48 バイト
	mov x29, sp
	str x0, [x29, #24]  // 実引数
	bl db_cols
	movz x13, #0x8000, lsl #48  // __
	mov x9, x0
	cmp x0, x13
	b.eq .L161  // 引数が __ なら呼び全体が __
	ldr x0, [x29, #24]
	mov x1, #0  // 実引数(字面)
	mov x2, x9
	bl db_print_cols
	b .L162
.L161:
	movz x0, #0x8000, lsl #48  // __
.L162:
	str x0, [x29, #24]  // 実引数
	mov x0, #0  // 実引数(字面)
	bl newline
	ldr x9, [x29, #24]
	movz x13, #0x8000, lsl #48  // __
	str x0, [x29, #32]  // 実引数
	cmp x9, x13
	b.eq .L163  // 引数が __ なら呼び全体が __
	mov x0, x9
	ldr x1, [x29, #32]
	bl seq2
	b .L164
.L163:
	movz x0, #0x8000, lsl #48  // __
.L164:
	ldp x29, x30, [sp], #48  // フレームを戻す
	ret

pr:
	stp x29, x30, [sp, #-32]!  // フレーム 32 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 x
	str x0, [x29, #24]  // 実引数
	ldp x29, x30, [sp], #32  // フレームを戻す
	b println_int  // 兄弟への末尾呼び出し
	ldp x29, x30, [sp], #32  // フレームを戻す
	ret

t:
	stp x29, x30, [sp, #-48]!  // フレーム 48 バイト
	mov x29, sp
	adrp x0, .Lstr1  // リストの像(.rodata)
	add x0, x0, :lo12:.Lstr1
	mov x1, #4  // 長さ
	mov x2, #0  // 実引数(字面)
	bl db_open
	movz x13, #0x8000, lsl #48  // __
	cmp x0, x13
	b.eq .L167  // 引数が __ なら呼び全体が __
	bl t1
	b .L168
.L167:
	movz x0, #0x8000, lsl #48  // __
.L168:
	ldp x29, x30, [sp], #48  // フレームを戻す
	ret

t1:
	stp x29, x30, [sp, #-128]!  // フレーム 112 バイト
	mov x29, sp
	str x19, [x29, #112]  // 呼ぶ側のために保存(x19〜x28 は呼び出し先が保つ約束)
	mov x19, x0  // 仮引数 h
	adrp x0, .Lstr2  // リストの像(.rodata)
	add x0, x0, :lo12:.Lstr2
	mov x1, #57  // 長さ
	str x0, [x29, #32]  // 実引数(ptr)
	str x1, [x29, #40]  // 実引数(len)
	ldr x1, [x29, #32]
	ldr x2, [x29, #40]
	mov x0, x19
	bl db_exec
	movz x13, #0x8000, lsl #48  // __
	cmp x0, x13
	b.eq .L170  // 引数が __ なら呼び全体が __
	bl pr
	b .L171
.L170:
	movz x0, #0x8000, lsl #48  // __
.L171:
	str x0, [x29, #24]  // 実引数
	adrp x0, .Lstr3  // リストの像(.rodata)
	add x0, x0, :lo12:.Lstr3
	mov x1, #58  // 長さ
	str x0, [x29, #40]  // 実引数(ptr)
	str x1, [x29, #48]  // 実引数(len)
	ldr x1, [x29, #40]
	ldr x2, [x29, #48]
	mov x0, x19
	bl db_exec
	movz x13, #0x8000, lsl #48  // __
	cmp x0, x13
	b.eq .L172  // 引数が __ なら呼び全体が __
	bl pr
	b .L173
.L172:
	movz x0, #0x8000, lsl #48  // __
.L173:
	str x0, [x29, #32]  // 実引数
	adrp x0, .Lstr4  // リストの像(.rodata)
	add x0, x0, :lo12:.Lstr4
	mov x1, #28  // 長さ
	str x0, [x29, #48]  // 実引数(ptr)
	str x1, [x29, #56]  // 実引数(len)
	ldr x1, [x29, #48]
	ldr x2, [x29, #56]
	mov x0, x19
	bl db_exec
	movz x13, #0x8000, lsl #48  // __
	cmp x0, x13
	b.eq .L174  // 引数が __ なら呼び全体が __
	bl pr
	b .L175
.L174:
	movz x0, #0x8000, lsl #48  // __
.L175:
	str x0, [x29, #40]  // 実引数
	adrp x0, .Lstr5  // リストの像(.rodata)
	add x0, x0, :lo12:.Lstr5
	mov x1, #7  // 長さ
	mov x2, #0  // 実引数(字面)
	bl db_open
	movz x13, #0x8000, lsl #48  // __
	cmp x0, x13
	b.eq .L176  // 引数が __ なら呼び全体が __
	bl pr
	b .L177
.L176:
	movz x0, #0x8000, lsl #48  // __
.L177:
	str x0, [x29, #48]  // 実引数
	adrp x0, .Lstr6  // リストの像(.rodata)
	add x0, x0, :lo12:.Lstr6
	mov x1, #27  // 長さ
	str x0, [x29, #64]  // 実引数(ptr)
	str x1, [x29, #72]  // 実引数(len)
	ldr x1, [x29, #64]
	ldr x2, [x29, #72]
	mov x0, x19
	bl db_exec
	movz x13, #0x8000, lsl #48  // __
	cmp x0, x13
	b.eq .L178  // 引数が __ なら呼び全体が __
	bl pr
	b .L179
.L178:
	movz x0, #0x8000, lsl #48  // __
.L179:
	str x0, [x29, #56]  // 実引数
	adrp x0, .Lstr7  // リストの像(.rodata)
	add x0, x0, :lo12:.Lstr7
	mov x1, #18  // 長さ
	str x0, [x29, #72]  // 実引数(ptr)
	str x1, [x29, #80]  // 実引数(len)
	ldr x1, [x29, #72]
	ldr x2, [x29, #80]
	mov x0, x19
	bl db_exec
	movz x13, #0x8000, lsl #48  // __
	cmp x0, x13
	b.eq .L180  // 引数が __ なら呼び全体が __
	bl pr
	b .L181
.L180:
	movz x0, #0x8000, lsl #48  // __
.L181:
	str x0, [x29, #64]  // 実引数
	adrp x0, .Lstr8  // リストの像(.rodata)
	add x0, x0, :lo12:.Lstr8
	mov x1, #41  // 長さ
	str x0, [x29, #88]  // 実引数(ptr)
	str x1, [x29, #96]  // 実引数(len)
	ldr x1, [x29, #88]
	ldr x2, [x29, #96]
	mov x0, x19
	bl db_prep
	movz x13, #0x8000, lsl #48  // __
	mov x9, x0
	cmp x0, x13
	b.eq .L182  // 引数が __ なら呼び全体が __
	mov x0, x19
	mov x1, x9
	bl t2
	b .L183
.L182:
	movz x0, #0x8000, lsl #48  // __
.L183:
	ldr x9, [x29, #24]
	movz x13, #0x8000, lsl #48  // __
	cmp x9, x13
	b.eq .L184  // 引数が __ なら呼び全体が __
	ldr x9, [x29, #32]
	cmp x9, x13
	b.eq .L184  // 引数が __ なら呼び全体が __
	ldr x9, [x29, #40]
	cmp x9, x13
	b.eq .L184  // 引数が __ なら呼び全体が __
	ldr x9, [x29, #48]
	cmp x9, x13
	b.eq .L184  // 引数が __ なら呼び全体が __
	ldr x9, [x29, #56]
	cmp x9, x13
	b.eq .L184  // 引数が __ なら呼び全体が __
	ldr x9, [x29, #64]
	cmp x9, x13
	b.eq .L184  // 引数が __ なら呼び全体が __
	mov x9, x0
	cmp x0, x13
	b.eq .L184  // 引数が __ なら呼び全体が __
	ldr x0, [x29, #24]
	ldr x1, [x29, #32]
	ldr x2, [x29, #40]
	ldr x3, [x29, #48]
	ldr x4, [x29, #56]
	ldr x5, [x29, #64]
	mov x6, x9
	mov x7, #0  // 実引数(字面)
	sub sp, sp, #16  // スタックで渡す実引数 1 語の置き場(呼びの直前に取り、呼びのあとで戻す)
	mov x9, #0  // 実引数(字面)
	str x9, [sp, #0]
	bl seq9
	add sp, sp, #16
	b .L185
.L184:
	movz x0, #0x8000, lsl #48  // __
.L185:
	ldr x19, [x29, #112]  // 保存したレジスタを戻す
	ldp x29, x30, [sp], #128  // フレームを戻す
	ret

t2:
	stp x29, x30, [sp, #-112]!  // フレーム 112 バイト
	mov x29, sp
	str x0, [x29, #16]  // 仮引数 h
	str x1, [x29, #24]  // 仮引数 s
	mov x0, x1  // s
	bl db_step
	movz x13, #0x8000, lsl #48  // __
	cmp x0, x13
	b.eq .L187  // 引数が __ なら呼び全体が __
	bl pr
	b .L188
.L187:
	movz x0, #0x8000, lsl #48  // __
.L188:
	str x0, [x29, #32]  // 実引数
	ldr x0, [x29, #24]  // s
	bl db_print_row
	str x0, [x29, #40]  // 実引数
	ldr x0, [x29, #24]  // s
	bl db_step
	movz x13, #0x8000, lsl #48  // __
	cmp x0, x13
	b.eq .L189  // 引数が __ なら呼び全体が __
	bl pr
	b .L190
.L189:
	movz x0, #0x8000, lsl #48  // __
.L190:
	str x0, [x29, #48]  // 実引数
	ldr x0, [x29, #24]  // s
	bl db_print_row
	str x0, [x29, #56]  // 実引数
	ldr x0, [x29, #24]  // s
	bl db_step
	movz x13, #0x8000, lsl #48  // __
	cmp x0, x13
	b.eq .L191  // 引数が __ なら呼び全体が __
	bl pr
	b .L192
.L191:
	movz x0, #0x8000, lsl #48  // __
.L192:
	str x0, [x29, #64]  // 実引数
	ldr x0, [x29, #16]  // h
	bl db_rowid
	movz x13, #0x8000, lsl #48  // __
	cmp x0, x13
	b.eq .L193  // 引数が __ なら呼び全体が __
	bl pr
	b .L194
.L193:
	movz x0, #0x8000, lsl #48  // __
.L194:
	str x0, [x29, #72]  // 実引数
	ldr x0, [x29, #16]  // h
	bl db_changes
	movz x13, #0x8000, lsl #48  // __
	cmp x0, x13
	b.eq .L195  // 引数が __ なら呼び全体が __
	bl pr
	b .L196
.L195:
	movz x0, #0x8000, lsl #48  // __
.L196:
	str x0, [x29, #80]  // 実引数
	ldr x0, [x29, #16]  // h
	bl db_close
	ldr x9, [x29, #32]
	movz x13, #0x8000, lsl #48  // __
	cmp x9, x13
	b.eq .L197  // 引数が __ なら呼び全体が __
	ldr x9, [x29, #40]
	cmp x9, x13
	b.eq .L197  // 引数が __ なら呼び全体が __
	ldr x9, [x29, #48]
	cmp x9, x13
	b.eq .L197  // 引数が __ なら呼び全体が __
	ldr x9, [x29, #56]
	cmp x9, x13
	b.eq .L197  // 引数が __ なら呼び全体が __
	ldr x9, [x29, #64]
	cmp x9, x13
	b.eq .L197  // 引数が __ なら呼び全体が __
	ldr x9, [x29, #72]
	cmp x9, x13
	b.eq .L197  // 引数が __ なら呼び全体が __
	ldr x9, [x29, #80]
	cmp x9, x13
	b.eq .L197  // 引数が __ なら呼び全体が __
	mov x9, x0
	cmp x0, x13
	b.eq .L197  // 引数が __ なら呼び全体が __
	ldr x0, [x29, #32]
	ldr x1, [x29, #40]
	ldr x2, [x29, #48]
	ldr x3, [x29, #56]
	ldr x4, [x29, #64]
	ldr x5, [x29, #72]
	ldr x6, [x29, #80]
	mov x7, x9
	sub sp, sp, #16  // スタックで渡す実引数 1 語の置き場(呼びの直前に取り、呼びのあとで戻す)
	mov x9, #0  // 実引数(字面)
	str x9, [sp, #0]
	bl seq9
	add sp, sp, #16
	b .L198
.L197:
	movz x0, #0x8000, lsl #48  // __
.L198:
	ldp x29, x30, [sp], #112  // フレームを戻す
	ret

	.global _.main
_.main:
	stp x29, x30, [sp, #-32]!  // フレーム 32 バイト
	mov x29, sp
	mov x0, #0  // 実引数(字面)
	bl t
	ldp x29, x30, [sp], #32  // フレームを戻す
	ret

.Ltrap:
	mov x16, #1  // Int の溢れなど(原因の印)
.Ltrap_halt:
	wfi  // Int の溢れ(罠)。integer_overflow.md §1
	b .Ltrap_halt

	.global _start
_start:
	bl _sign_dev_map
	bl _.main
	bl _sign_print_int
	mov x0, #0
	mov x8, #93  // exit
	svc #0

// x0 を 10 進で標準出力へ(負なら先頭に -)、あとに改行
_sign_print_int:
	movz x13, #0x8000, lsl #48  // __
	cmp x0, x13
	b.ne 3f
	sub sp, sp, #16
	mov w10, #95  // '_'
	strb w10, [sp]
	strb w10, [sp, #1]
	mov w10, #10
	strb w10, [sp, #2]
	mov x0, #1
	mov x1, sp
	mov x2, #3
	mov x8, #64  // write
	svc #0
	add sp, sp, #16
	ret
3:
	sub sp, sp, #48
	add x9, sp, #47
	mov w10, #10
	strb w10, [x9]  // 改行
	mov x11, x0
	cmp x0, #0
	cneg x0, x0, lt  // 絶対値(INT64_MIN は値でないので溢れない)
	mov x12, #10
1:
	udiv x13, x0, x12
	msub x14, x13, x12, x0
	add x14, x14, #48
	sub x9, x9, #1
	strb w14, [x9]
	mov x0, x13
	cbnz x0, 1b
	tbz x11, #63, 2f
	mov w10, #45  // '-'
	sub x9, x9, #1
	strb w10, [x9]
2:
	add x2, sp, #48
	sub x2, x2, x9  // 長さ
	mov x1, x9
	mov x0, #1
	mov x8, #64  // write
	svc #0
	add sp, sp, #48
	ret

// ===== 実機の装置の中継 (--real-dev) =====

// 低い番地の作業メモリ: [0x10000, 0x9000000) を匿名メモリで確保する(プログラムが `0x7C0000` のような絶対番地を作業場に使うため)。
// ELF は --image-base=0x10000000 などでこの外に置く。確保できなければ理由を標準エラーに出して exit(1)。
_sign_dev_map:
	ldr x9, [sp]
	add x10, sp, #16
	add x10, x10, x9, lsl #3
	adrp x11, _sign_envp
	add x11, x11, :lo12:_sign_envp
	str x10, [x11]
	mov x0, #0x10000
	movz x1, #0x8ff, lsl #16
	mov x2, #3
	movz x3, #0x4022
	movk x3, #0x10, lsl #16
	mov x4, #-1
	mov x5, #0
	mov x8, #222
	svc #0
	mov x10, #0x10000
	cmp x0, x10
	b.ne 1f
	ret
1:
	mov x0, #2
	adrp x1, _sign_dev_mapmsg
	add x1, x1, :lo12:_sign_dev_mapmsg
	mov x2, #130
	mov x8, #64
	svc #0
	mov x0, #1
	mov x8, #93
	svc #0

// x11 = 影の先頭, x10 = 先頭からの位置, x0 = 値, x1 = 幅
_sign_dev_sh_st:
	add x12, x11, x10
	cmp x1, #4
	b.ne 1f
	str w0, [x12]
	ret
1:
	str x0, [x12]
	ret

_sign_dev_sh_ld:
	add x12, x11, x10
	cmp x1, #4
	b.ne 1f
	ldr w0, [x12]
	ret
1:
	ldr x0, [x12]
	ret

// x0 = 語の列(4 バイト刻み), x1 = バイト列, x2 = 個数 : 各語の下位 1 バイトを詰める
_sign_dev_pack:
	cbz x2, 2f
1:
	ldr w3, [x0]
	strb w3, [x1]
	add x0, x0, #4
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 1b
2:
	ret

// x0 = バイト列, x1 = 語の列(4 バイト刻み), x2 = 個数 : 1 バイトずつ 1 語に広げる
_sign_dev_unpack:
	cbz x2, 2f
1:
	ldrb w3, [x0]
	str w3, [x1]
	add x0, x0, #1
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 1b
2:
	ret

// I2C: x0 = 命令番号(1 WRITE / 2 READ / 3 WRITE_READ / 4 PROBE)。影の ADDR BUF LEN RDLEN BUS を読む。結果 = 長さか -errno
_sign_dev_i2c:
	stp x29, x30, [sp, #-160]!
	mov x29, sp
	str x0, [sp, #24]
	adrp x11, _sign_dreg
	add x11, x11, :lo12:_sign_dreg
	ldr w1, [x11, #0]
	str x1, [sp, #32]
	ldr w1, [x11, #4]
	str x1, [sp, #40]
	ldr w1, [x11, #8]
	str x1, [sp, #48]
	ldr w1, [x11, #12]
	str x1, [sp, #56]
	ldr w1, [x11, #16]
	str x1, [sp, #64]
	cmp x0, #1
	b.lo .Ldi_inval
	cmp x0, #4
	b.hi .Ldi_inval
	ldr x1, [sp, #32]
	cmp x1, #127
	b.hi .Ldi_inval
	mov x2, #4096
	ldr x1, [sp, #48]
	cmp x1, x2
	b.hi .Ldi_inval
	cmp x0, #3
	b.ne 1f
	ldr x1, [sp, #56]
	cmp x1, x2
	b.hi .Ldi_inval
1:
	cmp x0, #1
	b.ne 2f
	ldr x1, [sp, #48]
	cbz x1, .Ldi_zero
2:
	ldr x1, [sp, #64]
	cmp x1, #99
	b.hi .Ldi_nodev
// パス "/dev/i2c-N"
	movz x1, #0x642f
	movk x1, #0x7665, lsl #16
	movk x1, #0x692f, lsl #32
	movk x1, #0x6332, lsl #48
	str x1, [sp, #72]
	mov w5, #0x2d
	strb w5, [sp, #80]
	ldr x1, [sp, #64]
	mov x2, #10
	udiv x3, x1, x2
	msub x4, x3, x2, x1
	cbz x3, 3f
	add w5, w3, #48
	strb w5, [sp, #81]
	add w5, w4, #48
	strb w5, [sp, #82]
	strb wzr, [sp, #83]
	b 4f
3:
	add w5, w4, #48
	strb w5, [sp, #81]
	strb wzr, [sp, #82]
4:
	mov x0, #-100
	add x1, sp, #72
	mov x2, #2
	mov x3, #0
	mov x8, #56
	svc #0
	cmp x0, #0
	b.lt .Ldi_ret
	str x0, [sp, #16]
	ldr x1, [sp, #24]
	cmp x1, #3
	b.eq .Ldi_rdwr
	ldr x0, [sp, #16]
	mov x1, #1795
	ldr x2, [sp, #32]
	mov x8, #29
	svc #0
	cmp x0, #0
	b.lt .Ldi_close
	ldr x1, [sp, #24]
	cmp x1, #1
	b.eq .Ldi_wr
	cmp x1, #2
	b.eq .Ldi_rd
// 4 PROBE: 1 バイト読めれば 0。読めなければ理由を問わず -6(応答しない)
	ldr x0, [sp, #16]
	adrp x1, _sign_drd
	add x1, x1, :lo12:_sign_drd
	mov x2, #1
	mov x8, #63
	svc #0
	cmp x0, #0
	b.ge 1f
	mov x0, #-6
	b .Ldi_close
1:
	mov x0, #0
	b .Ldi_close
.Ldi_wr:
	ldr x0, [sp, #40]
	adrp x1, _sign_dwr
	add x1, x1, :lo12:_sign_dwr
	ldr x2, [sp, #48]
	bl _sign_dev_pack
	ldr x0, [sp, #16]
	adrp x1, _sign_dwr
	add x1, x1, :lo12:_sign_dwr
	ldr x2, [sp, #48]
	mov x8, #64
	svc #0
	cmp x0, #0
	b.lt .Ldi_close
	ldr x1, [sp, #48]
	cmp x0, x1
	b.eq .Ldi_close
	mov x0, #-5
	b .Ldi_close
.Ldi_rd:
	ldr x0, [sp, #16]
	adrp x1, _sign_drd
	add x1, x1, :lo12:_sign_drd
	ldr x2, [sp, #48]
	mov x8, #63
	svc #0
	cmp x0, #0
	b.lt .Ldi_close
	ldr x1, [sp, #48]
	cmp x0, x1
	b.eq 1f
	mov x0, #-5
	b .Ldi_close
1:
	adrp x0, _sign_drd
	add x0, x0, :lo12:_sign_drd
	ldr x1, [sp, #40]
	ldr x2, [sp, #48]
	bl _sign_dev_unpack
	ldr x0, [sp, #48]
	b .Ldi_close
// 3 WRITE_READ: I2C_RDWR で 2 つのメッセージ(間に STOP を入れない)。LEN = 0 なら読みだけ、RDLEN = 0 なら書きだけ
.Ldi_rdwr:
	ldr x1, [sp, #48]
	ldr x2, [sp, #56]
	orr x3, x1, x2
	cbz x3, .Ldi_zero_close
	ldr x0, [sp, #40]
	adrp x1, _sign_dwr
	add x1, x1, :lo12:_sign_dwr
	ldr x2, [sp, #48]
	bl _sign_dev_pack
	ldr x3, [sp, #32]
	strh w3, [sp, #96]
	strh wzr, [sp, #98]
	ldr x4, [sp, #48]
	strh w4, [sp, #100]
	strh wzr, [sp, #102]
	adrp x5, _sign_dwr
	add x5, x5, :lo12:_sign_dwr
	str x5, [sp, #104]
	strh w3, [sp, #112]
	mov w6, #1
	strh w6, [sp, #114]
	ldr x4, [sp, #56]
	strh w4, [sp, #116]
	strh wzr, [sp, #118]
	adrp x5, _sign_drd
	add x5, x5, :lo12:_sign_drd
	str x5, [sp, #120]
	add x6, sp, #96
	mov x7, #2
	ldr x4, [sp, #48]
	cbnz x4, 1f
	add x6, sp, #112
	mov x7, #1
	b 2f
1:
	ldr x4, [sp, #56]
	cbnz x4, 2f
	mov x7, #1
2:
	str x6, [sp, #128]
	str x7, [sp, #136]
	ldr x0, [sp, #16]
	mov x1, #1799
	add x2, sp, #128
	mov x8, #29
	svc #0
	cmp x0, #0
	b.lt .Ldi_close
	ldr x2, [sp, #56]
	cbz x2, 3f
	adrp x0, _sign_drd
	add x0, x0, :lo12:_sign_drd
	ldr x1, [sp, #40]
	bl _sign_dev_unpack
3:
	ldr x0, [sp, #56]
	b .Ldi_close
.Ldi_zero_close:
	mov x0, #0
.Ldi_close:
	str x0, [sp, #24]
	ldr x0, [sp, #16]
	mov x8, #57
	svc #0
	ldr x0, [sp, #24]
.Ldi_ret:
	ldp x29, x30, [sp], #160
	ret
.Ldi_inval:
	mov x0, #-22
	b .Ldi_ret
.Ldi_nodev:
	mov x0, #-19
	b .Ldi_ret
.Ldi_zero:
	mov x0, #0
	b .Ldi_ret

// SPI の影の既定: SPEED 1 MHz(MODE・CS・BUS は 0)。最初の 1 回だけ
_sign_dev_spi_init:
	adrp x12, _sign_dinit2
	add x12, x12, :lo12:_sign_dinit2
	ldr x13, [x12]
	cbnz x13, 1f
	mov x13, #1
	str x13, [x12]
	adrp x11, _sign_dreg
	add x11, x11, :lo12:_sign_dreg
	movz x14, #0x4240
	movk x14, #0xf, lsl #16
	str x14, [x11, #0x2008]
1:
	ret

// SPI: x0 = 命令番号(1 TRANSFER)。影の BUF LEN SPEED MODE CS BUS を読む。結果 = 長さか -errno
_sign_dev_spi:
	stp x29, x30, [sp, #-160]!
	mov x29, sp
	str x0, [sp, #24]
	adrp x11, _sign_dreg
	add x11, x11, :lo12:_sign_dreg
	add x11, x11, #0x2000
	ldr w1, [x11, #0]
	str x1, [sp, #32]
	ldr w1, [x11, #4]
	str x1, [sp, #40]
	ldr w1, [x11, #8]
	str x1, [sp, #48]
	ldr w1, [x11, #12]
	str x1, [sp, #56]
	ldr w1, [x11, #16]
	str x1, [sp, #64]
	ldr w1, [x11, #28]
	str x1, [sp, #72]
	cmp x0, #1
	b.ne .Lsp_inval
	mov x2, #4096
	ldr x1, [sp, #40]
	cmp x1, x2
	b.hi .Lsp_inval
	cbz x1, .Lsp_zero
	ldr x1, [sp, #72]
	cmp x1, #9
	b.hi .Lsp_nodev
// パス "/dev/spidevB.C"
	movz x1, #0x642f
	movk x1, #0x7665, lsl #16
	movk x1, #0x732f, lsl #32
	movk x1, #0x6970, lsl #48
	str x1, [sp, #80]
	mov w5, #0x64
	strb w5, [sp, #88]
	mov w5, #0x65
	strb w5, [sp, #89]
	mov w5, #0x76
	strb w5, [sp, #90]
	ldr x1, [sp, #72]
	add w5, w1, #48
	strb w5, [sp, #91]
	mov w5, #0x2e
	strb w5, [sp, #92]
	ldr x1, [sp, #64]
	add w5, w1, #48
	strb w5, [sp, #93]
	strb wzr, [sp, #94]
	mov x0, #-100
	add x1, sp, #80
	mov x2, #2
	mov x3, #0
	mov x8, #56
	svc #0
	cmp x0, #0
	b.lt .Lsp_ret
	str x0, [sp, #16]
// モード(CPOL・CPHA)
	ldr x1, [sp, #56]
	strb w1, [sp, #96]
	ldr x0, [sp, #16]
	movz x1, #0x6b01
	movk x1, #0x4001, lsl #16
	add x2, sp, #96
	mov x8, #29
	svc #0
	cmp x0, #0
	b.lt .Lsp_close
	ldr x0, [sp, #32]
	adrp x1, _sign_dwr
	add x1, x1, :lo12:_sign_dwr
	ldr x2, [sp, #40]
	bl _sign_dev_pack
// struct spi_ioc_transfer(32 バイト): tx_buf rx_buf len speed_hz delay_usecs bits_per_word …
	adrp x5, _sign_dwr
	add x5, x5, :lo12:_sign_dwr
	str x5, [sp, #104]
	adrp x5, _sign_drd
	add x5, x5, :lo12:_sign_drd
	str x5, [sp, #112]
	ldr x1, [sp, #40]
	str w1, [sp, #120]
	ldr x1, [sp, #48]
	str w1, [sp, #124]
	str xzr, [sp, #128]
	mov w5, #8
	strb w5, [sp, #129]
	ldr x0, [sp, #16]
	movz x1, #0x6b00
	movk x1, #0x4020, lsl #16
	add x2, sp, #104
	mov x8, #29
	svc #0
	cmp x0, #0
	b.lt .Lsp_close
	ldr x1, [sp, #40]
	cmp x0, x1
	b.eq 1f
	mov x0, #-5
	b .Lsp_close
1:
	adrp x0, _sign_drd
	add x0, x0, :lo12:_sign_drd
	ldr x1, [sp, #32]
	ldr x2, [sp, #40]
	bl _sign_dev_unpack
	ldr x0, [sp, #40]
.Lsp_close:
	str x0, [sp, #24]
	ldr x0, [sp, #16]
	mov x8, #57
	svc #0
	ldr x0, [sp, #24]
.Lsp_ret:
	ldp x29, x30, [sp], #160
	ret
.Lsp_inval:
	mov x0, #-22
	b .Lsp_ret
.Lsp_nodev:
	mov x0, #-19
	b .Lsp_ret
.Lsp_zero:
	mov x0, #0
	b .Lsp_ret

// GPIO の行の要求: x0 = ピン, x1 = フラグ(INPUT 4 / OUTPUT 8 / +PULL_UP 0x100 / +PULL_DOWN 0x200)。結果 0 か負
_sign_dev_gp_req:
	stp x29, x30, [sp, #-48]!
	mov x29, sp
	stp x0, x1, [sp, #16]
	adrp x2, _sign_gfd
	add x2, x2, :lo12:_sign_gfd
	ldr x3, [sp, #16]
	lsl x3, x3, #3
	add x2, x2, x3
	str x2, [sp, #32]
	ldr x0, [x2]
	cbz x0, 1f
	sub x0, x0, #1
	mov x8, #57
	svc #0
	ldr x2, [sp, #32]
	str xzr, [x2]
1:
	mov x0, #-100
	adrp x1, _sign_dev_gchip
	add x1, x1, :lo12:_sign_dev_gchip
	mov x2, #2
	mov x3, #0
	mov x8, #56
	svc #0
	cmp x0, #0
	b.lt .Ldg_ret
	str x0, [sp, #40]
	adrp x4, _sign_greq
	add x4, x4, :lo12:_sign_greq
	mov x5, #74
	mov x6, x4
2:
	str xzr, [x6]
	add x6, x6, #8
	sub x5, x5, #1
	cbnz x5, 2b
	ldr x1, [sp, #16]
	str w1, [x4]
	mov x6, #0x6973
	movk x6, #0x6e67, lsl #16
	str w6, [x4, #256]
	ldr x1, [sp, #24]
	str x1, [x4, #288]
	mov x6, #1
	str w6, [x4, #560]
	ldr x0, [sp, #40]
	movz x1, #0xb407
	movk x1, #0xc250, lsl #16
	mov x2, x4
	mov x8, #29
	svc #0
	str x0, [sp, #24]
	ldr x0, [sp, #40]
	mov x8, #57
	svc #0
	ldr x0, [sp, #24]
	cmp x0, #0
	b.lt .Ldg_ret
	adrp x4, _sign_greq
	add x4, x4, :lo12:_sign_greq
	ldr w5, [x4, #588]
	add x5, x5, #1
	ldr x2, [sp, #32]
	str x5, [x2]
	mov x0, #0
.Ldg_ret:
	ldp x29, x30, [sp], #48
	ret

// GPIO: x0 = 操作(0 向きを設定 / 1 値を書く / 2 値を読む), x1 = ピン, x2 = 引数(0: フラグ, 1: 値)
_sign_dev_gp:
	stp x29, x30, [sp, #-80]!
	mov x29, sp
	stp x0, x1, [sp, #16]
	str x2, [sp, #32]
	adrp x3, _sign_gst
	add x3, x3, :lo12:_sign_gst
	add x3, x3, x1
	str x3, [sp, #40]
	cbnz x0, 1f
	mov x0, x1
	mov x1, x2
	bl _sign_dev_gp_req
	cmp x0, #0
	b.lt .Ldp_end
	ldr x3, [sp, #40]
	ldr x2, [sp, #32]
	mov w4, #1
	tbz x2, #3, 5f
	mov w4, #2
5:
	strb w4, [x3]
	b .Ldp_end
1:
	ldr x3, [sp, #40]
	ldrb w4, [x3]
	cmp x0, #1
	b.ne .Ldp_read
	cmp w4, #2
	b.eq .Ldp_setv
	ldr x0, [sp, #24]
	mov x1, #8
	bl _sign_dev_gp_req
	cmp x0, #0
	b.lt .Ldp_end
	ldr x3, [sp, #40]
	mov w4, #2
	strb w4, [x3]
.Ldp_setv:
	ldr x2, [sp, #32]
	mov x4, #0
	cbz x2, 6f
	mov x4, #1
6:
	str x4, [sp, #48]
	mov x5, #1
	str x5, [sp, #56]
	adrp x6, _sign_gfd
	add x6, x6, :lo12:_sign_gfd
	ldr x7, [sp, #24]
	lsl x7, x7, #3
	ldr x0, [x6, x7]
	sub x0, x0, #1
	movz x1, #0xb40f
	movk x1, #0xc010, lsl #16
	add x2, sp, #48
	mov x8, #29
	svc #0
	b .Ldp_end
.Ldp_read:
	cbnz w4, 7f
	ldr x0, [sp, #24]
	mov x1, #4
	bl _sign_dev_gp_req
	cmp x0, #0
	b.lt .Ldp_end
	ldr x3, [sp, #40]
	mov w4, #1
	strb w4, [x3]
7:
	str xzr, [sp, #48]
	mov x5, #1
	str x5, [sp, #56]
	adrp x6, _sign_gfd
	add x6, x6, :lo12:_sign_gfd
	ldr x7, [sp, #24]
	lsl x7, x7, #3
	ldr x0, [x6, x7]
	sub x0, x0, #1
	movz x1, #0xb40e
	movk x1, #0xc010, lsl #16
	add x2, sp, #48
	mov x8, #29
	svc #0
	cmp x0, #0
	b.lt .Ldp_end
	ldr x0, [sp, #48]
	and x0, x0, #1
.Ldp_end:
	ldp x29, x30, [sp], #80
	ret

// x0 の下位 1 バイト(utf32 で幅 4 のときは符号位置 → UTF-8)を標準出力へ
_sign_dev_putc:
	sub sp, sp, #16
	strb w0, [sp]
	mov x0, #1
	mov x1, sp
	mov x2, #1
	mov x8, #64
	svc #0
	add sp, sp, #16
	ret


// 時計: 最初に触れた時からのミリ秒(最初の呼びで基準を決める)→ x0
_sign_dev_tnow:
	stp x29, x30, [sp, #-48]!
	mov x29, sp
	mov x0, #1
	add x1, sp, #16
	mov x8, #113
	svc #0
	ldr x2, [sp, #16]
	ldr x3, [sp, #24]
	mov x4, #1000
	mul x2, x2, x4
	mov x5, #1000
	mul x5, x5, x4
	udiv x3, x3, x5
	add x2, x2, x3
	adrp x6, _sign_dt0
	add x6, x6, :lo12:_sign_dt0
	ldr x7, [x6]
	cbnz x7, 1f
	add x7, x2, #1
	str x7, [x6]
1:
	sub x0, x2, x7
	add x0, x0, #1
	ldp x29, x30, [sp], #48
	ret

// 装置の番地への書き込み: x9 = 番地, x0 = 値, x1 = 幅。x9 は保つ
_sign_dev_st:
	stp x29, x30, [sp, #-48]!
	mov x29, sp
	stp x9, x1, [sp, #16]
	str x0, [sp, #32]
	lsr x10, x9, #20
	cmp x10, #0x96
	b.eq .Lds_i2c
	cmp x10, #0x95
	b.eq .Lds_gpio
	cmp x10, #0x92
	b.eq .Lds_timer
	cmp x10, #0x97
	b.eq .Lds_spi
	cmp x10, #0x99
	b.eq .Lds_net
	cmp x10, #0x94
	b.eq .Lds_sys
	cmp x10, #0x93
	b.eq .Lds_in
	cmp x10, #0x98
	b.eq .Lds_snd
	cmp x10, #0x91
	b.eq .Lds_gfx
	cmp x10, #0x9A
	b.eq .Lds_db
	cmp x10, #0x90
	b.ne .Lds_end
	mov x10, #0x9000000
	cmp x9, x10
	b.ne .Lds_end
	cmp x1, #4
	b.ne 1f
	bl _sign_dev_putc
	b .Lds_end
1:
	and x0, x0, #0xFF
	cmp x0, #0x80
	b.lo 2f
	sub sp, sp, #16
	strb w0, [sp]
	mov x0, #1
	mov x1, sp
	mov x2, #1
	mov x8, #64
	svc #0
	add sp, sp, #16
	b .Lds_end
2:
	bl _sign_dev_putc
	b .Lds_end
.Lds_timer:
	and x10, x9, #0xFFF
	cmp x10, #4
	b.eq .Lds_t_sleep
	cmp x10, #8
	b.eq .Lds_t_id
	cmp x10, #0xC
	b.eq .Lds_t_after
	cmp x10, #0x10
	b.eq .Lds_t_every
	cmp x10, #0x14
	b.eq .Lds_t_cancel
	b .Lds_end
.Lds_t_sleep:
	cmp x0, #0
	b.lt .Lds_end
	bl _sign_dev_tnow
	ldr x0, [sp, #32]
	mov x1, #1000
	udiv x2, x0, x1
	msub x3, x2, x1, x0
	mov x4, #1000
	mul x3, x3, x4
	mul x3, x3, x4
	str x2, [sp, #32]
	str x3, [sp, #40]
	add x0, sp, #32
	mov x1, #0
	mov x8, #101
	svc #0
	b .Lds_end
// アラーム(AFTER・EVERY・CANCEL・ID)。表は 16 個: 番号・時刻・周期(0 = 1 回)・使用中
.Lds_t_id:
	adrp x11, _sign_dalm
	add x11, x11, :lo12:_sign_dalm
	str x0, [x11]
	b .Lds_end
.Lds_t_after:
	cmp x0, #0
	b.lt .Lds_end
	mov x2, #0
	b .Lds_t_set
.Lds_t_every:
	cmp x0, #1
	b.lt .Lds_end
	mov x2, x0
	b .Lds_t_set
.Lds_t_set:
	str x2, [sp, #40]
	bl _sign_dev_tnow
	ldr x3, [sp, #32]
	add x3, x0, x3
	ldr x4, [sp, #40]
	adrp x11, _sign_dalm
	add x11, x11, :lo12:_sign_dalm
	ldr x5, [x11]
	add x6, x11, #8
	mov x7, #16
	mov x14, #0
1:
	ldr x12, [x6, #24]
	cbz x12, 2f
	ldr x13, [x6]
	cmp x13, x5
	b.eq 4f
	b 3f
2:
	cbnz x14, 3f
	mov x14, x6
3:
	add x6, x6, #32
	sub x7, x7, #1
	cbnz x7, 1b
	cbz x14, .Lds_end
	mov x6, x14
4:
	str x5, [x6]
	str x3, [x6, #8]
	str x4, [x6, #16]
	mov x12, #1
	str x12, [x6, #24]
	b .Lds_end
.Lds_t_cancel:
	adrp x11, _sign_dalm
	add x11, x11, :lo12:_sign_dalm
	add x6, x11, #8
	mov x7, #16
1:
	ldr x12, [x6, #24]
	cbz x12, 2f
	ldr x13, [x6]
	cmp x13, x0
	b.ne 2f
	str xzr, [x6, #24]
2:
	add x6, x6, #32
	sub x7, x7, #1
	cbnz x7, 1b
	b .Lds_end
.Lds_i2c:
	adrp x11, _sign_dreg
	add x11, x11, :lo12:_sign_dreg
	adrp x12, _sign_dinit
	add x12, x12, :lo12:_sign_dinit
	ldr x13, [x12]
	cbnz x13, 1f
	mov x13, #1
	str x13, [x12]
	str x13, [x11, #16]
1:
	and x10, x9, #0xFFF
	cmp x10, #0x20
	b.hs .Lds_end
	ldr x0, [sp, #32]
	ldr x1, [sp, #24]
	bl _sign_dev_sh_st
	cmp x10, #0x14
	b.ne .Lds_end
	ldr x0, [sp, #32]
	bl _sign_dev_i2c
	adrp x11, _sign_dreg
	add x11, x11, :lo12:_sign_dreg
	str x0, [x11, #0x18]
	b .Lds_end
.Lds_spi:
	bl _sign_dev_spi_init
	adrp x11, _sign_dreg
	add x11, x11, :lo12:_sign_dreg
	add x11, x11, #0x2000
	and x10, x9, #0xFFF
	cmp x10, #0x20
	b.hs .Lds_end
	ldr x0, [sp, #32]
	ldr x1, [sp, #24]
	cmp x10, #8
	b.ne 2f
	cmp x0, #1
	b.lt .Lds_end
	movz x14, #0x5940
	movk x14, #0x773, lsl #16
	cmp x0, x14
	b.gt .Lds_end
	b 5f
2:
	cmp x10, #0xC
	b.ne 3f
	cmp x0, #0
	b.lt .Lds_end
	cmp x0, #3
	b.gt .Lds_end
	b 5f
3:
	cmp x10, #0x10
	b.ne 4f
	cmp x0, #0
	b.lt .Lds_end
	cmp x0, #1
	b.gt .Lds_end
	b 5f
4:
	cmp x10, #0x14
	b.eq 6f
	cmp x10, #0x18
	b.eq .Lds_end
5:
	bl _sign_dev_sh_st
	b .Lds_end
6:
	ldr x0, [sp, #32]
	bl _sign_dev_spi
	adrp x11, _sign_dreg
	add x11, x11, :lo12:_sign_dreg
	add x11, x11, #0x2000
	str x0, [x11, #0x18]
	b .Lds_end
.Lds_gpio:
	adrp x11, _sign_dreg
	add x11, x11, :lo12:_sign_dreg
	add x11, x11, #0x1000
	and x10, x9, #0xFFF
	cmp x10, #0x400
	b.hs .Lds_end
	ldr x0, [sp, #32]
	ldr x1, [sp, #24]
	bl _sign_dev_sh_st
	lsr x12, x10, #8
	and x13, x10, #0xFF
	lsr x13, x13, #2
	cbz x12, 1f
	cmp x12, #1
	b.ne .Lds_end
	ldr x2, [sp, #32]
	mov x3, #0x104
	cmp x2, #2
	b.eq 3f
	mov x3, #0x204
	cmp x2, #3
	b.eq 3f
	mov x3, #4
	cmp x2, #0
	b.eq 3f
	mov x3, #8
	cmp x2, #1
	b.ne .Lds_end
3:
	mov x0, #0
	mov x1, x13
	mov x2, x3
	bl _sign_dev_gp
	b .Lds_end
1:
	ldr x2, [sp, #32]
	cmp x2, #0
	b.eq 2f
	mov x2, #1
2:
	mov x0, #1
	mov x1, x13
	bl _sign_dev_gp
	b .Lds_end
.Lds_net:
	adrp x11, _sign_dreg
	add x11, x11, :lo12:_sign_dreg
	add x11, x11, #0x3000
	and x10, x9, #0xFFF
	cmp x10, #0x28
	b.hs .Lds_end
	cmp x10, #0x24
	b.eq .Lds_end
	ldr x0, [sp, #32]
	ldr x1, [sp, #24]
	bl _sign_dev_sh_st
	cmp x10, #0x20
	b.ne .Lds_end
	ldr w0, [x11]
	bl _sign_dev_net
	adrp x11, _sign_dreg
	add x11, x11, :lo12:_sign_dreg
	add x11, x11, #0x3000
	str x0, [x11, #0x24]
	b .Lds_end
.Lds_db:
	adrp x11, _sign_dbreg
	add x11, x11, :lo12:_sign_dbreg
	and x10, x9, #0xFFF
	cmp x10, #0x28
	b.hs .Lds_end
	cmp x10, #0x24
	b.eq .Lds_end
	and x13, x10, #3
	cbnz x13, .Lds_end
	lsl x12, x10, #1
	add x12, x11, x12
	ldr x0, [sp, #32]
	ldr x1, [sp, #24]
	cmp x1, #4
	b.ne 1f
	and x0, x0, #0xFFFFFFFF
1:
	str x0, [x12]
	cmp x10, #0x20
	b.ne .Lds_end
	mov x0, x11
	bl sign_db_call
	adrp x11, _sign_dbreg
	add x11, x11, :lo12:_sign_dbreg
	str x0, [x11, #0x48]
	b .Lds_end
.Lds_sys:
	adrp x11, _sign_dreg
	add x11, x11, :lo12:_sign_dreg
	add x11, x11, #0x4000
	and x10, x9, #0xFFF
	cmp x10, #0x1C
	b.hs .Lds_end
	cmp x10, #0x18
	b.eq .Lds_end
	ldr x0, [sp, #32]
	ldr x1, [sp, #24]
	bl _sign_dev_sh_st
	cmp x10, #0x14
	b.ne .Lds_end
	ldr w0, [x11]
	bl _sign_dev_sys
	adrp x11, _sign_dreg
	add x11, x11, :lo12:_sign_dreg
	add x11, x11, #0x4000
	str x0, [x11, #0x18]
	b .Lds_end
.Lds_gfx:
	ldr x9, [sp, #16]
	movz x10, #0xFFFF
	movk x10, #0xF, lsl #16
	and x0, x9, x10
	ldr x1, [sp, #32]
	ldr x2, [sp, #24]
	cmp x2, #4
	b.ne 1f
	and x1, x1, #0xFFFFFFFF
1:
	bl _sign_dev_gst
	b .Lds_end
.Ldl_gfx:
	ldr x0, [sp, #16]
	movz x10, #0xFFFF
	movk x10, #0xF, lsl #16
	and x0, x0, x10
	bl _sign_dev_gld
	b .Ldl_end
.Lds_snd:
	ldr x9, [sp, #16]
	movz x10, #0xFFFF
	movk x10, #0xF, lsl #16
	and x0, x9, x10
	ldr x1, [sp, #32]
	ldr x2, [sp, #24]
	cmp x2, #4
	b.ne 1f
	and x1, x1, #0xFFFFFFFF
1:
	bl _sign_dev_snd_st
	b .Lds_end
.Ldl_snd:
	ldr x0, [sp, #16]
	movz x10, #0xFFFF
	movk x10, #0xF, lsl #16
	and x0, x0, x10
	bl _sign_dev_snd_ld
	ldr x1, [sp, #24]
	cmp x1, #4
	b.ne .Ldl_end
	and x0, x0, #0xFFFFFFFF
	b .Ldl_end
.Lds_in:
	bl _sign_dev_ipoll
	ldr x9, [sp, #16]
	movz x10, #0xFFFF
	movk x10, #0xF, lsl #16
	and x10, x9, x10
	cmp x10, #0x14
	b.ne .Lds_end
	bl _sign_dev_ipop
	b .Lds_end
.Lds_end:
	ldp x9, x1, [sp, #16]
	ldp x29, x30, [sp], #48
	ret

// 装置の番地の読み: x0 = 番地, x1 = 幅 → x0
_sign_dev_ld:
	stp x29, x30, [sp, #-48]!
	mov x29, sp
	stp x0, x1, [sp, #16]
	lsr x10, x0, #20
	cmp x10, #0x96
	b.eq .Ldl_i2c
	cmp x10, #0x95
	b.eq .Ldl_gpio
	cmp x10, #0x92
	b.eq .Ldl_timer
	cmp x10, #0x97
	b.eq .Ldl_spi
	cmp x10, #0x99
	b.eq .Ldl_net
	cmp x10, #0x94
	b.eq .Ldl_sys
	cmp x10, #0x93
	b.eq .Ldl_in
	cmp x10, #0x98
	b.eq .Ldl_snd
	cmp x10, #0x91
	b.eq .Ldl_gfx
	cmp x10, #0x9A
	b.eq .Ldl_db
	cmp x10, #0x90
	b.eq .Ldl_uart
.Ldl_zero:
	mov x0, #0
.Ldl_end:
	ldp x29, x30, [sp], #48
	ret
.Ldl_i2c:
	adrp x11, _sign_dreg
	add x11, x11, :lo12:_sign_dreg
	and x10, x0, #0xFFF
	cmp x10, #0x20
	b.hs .Ldl_zero
	bl _sign_dev_sh_ld
	b .Ldl_end
.Ldl_db:
	adrp x11, _sign_dbreg
	add x11, x11, :lo12:_sign_dbreg
	and x10, x0, #0xFFF
	cmp x10, #0x28
	b.hs .Ldl_zero
	and x13, x10, #3
	cbnz x13, .Ldl_zero
	lsl x12, x10, #1
	add x12, x11, x12
	ldr x0, [x12]
	ldr x1, [sp, #24]
	cmp x1, #4
	b.ne .Ldl_end
	and x0, x0, #0xFFFFFFFF
	b .Ldl_end
.Ldl_in:
	bl _sign_dev_ipoll
	ldr x0, [sp, #16]
	movz x10, #0xFFFF
	movk x10, #0xF, lsl #16
	and x0, x0, x10
	bl _sign_dev_iget
	b .Ldl_end
.Ldl_sys:
	adrp x11, _sign_dreg
	add x11, x11, :lo12:_sign_dreg
	add x11, x11, #0x4000
	and x10, x0, #0xFFF
	cmp x10, #0x1C
	b.hs .Ldl_zero
	bl _sign_dev_sh_ld
	b .Ldl_end
.Ldl_net:
	adrp x11, _sign_dreg
	add x11, x11, :lo12:_sign_dreg
	add x11, x11, #0x3000
	and x10, x0, #0xFFF
	cmp x10, #0x28
	b.hs .Ldl_zero
	bl _sign_dev_sh_ld
	b .Ldl_end
.Ldl_spi:
	str x0, [sp, #32]
	bl _sign_dev_spi_init
	ldr x0, [sp, #32]
	adrp x11, _sign_dreg
	add x11, x11, :lo12:_sign_dreg
	add x11, x11, #0x2000
	and x10, x0, #0xFFF
	cmp x10, #0x20
	b.hs .Ldl_zero
	bl _sign_dev_sh_ld
	b .Ldl_end
.Ldl_gpio:
	and x10, x0, #0xFFF
	cmp x10, #0x400
	b.hs .Ldl_zero
	cmp x10, #0x100
	b.hs 1f
	lsr x1, x10, #2
	mov x0, #2
	mov x2, #0
	bl _sign_dev_gp
	b .Ldl_end
1:
	adrp x11, _sign_dreg
	add x11, x11, :lo12:_sign_dreg
	add x11, x11, #0x1000
	ldr x1, [sp, #24]
	bl _sign_dev_sh_ld
	b .Ldl_end
.Ldl_timer:
	and x10, x0, #0xFFF
	cbnz x10, 1f
	bl _sign_dev_tnow
	b .Ldl_end
1:
	cmp x10, #8
	b.ne 2f
	adrp x11, _sign_dalm
	add x11, x11, :lo12:_sign_dalm
	ldr x0, [x11]
	b .Ldl_end
// 0x18 DUE(この実装の足し)… 時刻が来たアラームのうち一番早いものの番号を取り出す(1 回きりは消え、くり返しは次へ進む)。無ければ -1
2:
	cmp x10, #0x18
	b.ne .Ldl_zero
	bl _sign_dev_tnow
	mov x4, x0
	adrp x11, _sign_dalm
	add x11, x11, :lo12:_sign_dalm
	add x6, x11, #8
	mov x7, #16
	mov x5, #0
1:
	ldr x12, [x6, #24]
	cbz x12, 3f
	ldr x13, [x6, #8]
	cmp x13, x4
	b.gt 3f
	cbz x5, 2f
	ldr x14, [x5, #8]
	cmp x13, x14
	b.ge 3f
2:
	mov x5, x6
3:
	add x6, x6, #32
	sub x7, x7, #1
	cbnz x7, 1b
	cbnz x5, 4f
	mov x0, #-1
	b .Ldl_end
4:
	ldr x0, [x5]
	ldr x12, [x5, #16]
	cbnz x12, 5f
	str xzr, [x5, #24]
	b .Ldl_end
5:
	ldr x13, [x5, #8]
6:
	add x13, x13, x12
	cmp x13, x4
	b.le 6b
	str x13, [x5, #8]
	b .Ldl_end
.Ldl_uart:
	mov x10, #0x9000000
	cmp x0, x10
	b.ne .Ldl_zero
	mov x0, #0
	add x1, sp, #32
	mov x2, #1
	mov x8, #63
	svc #0
	cmp x0, #1
	b.ne 1f
	ldrb w0, [sp, #32]
	b .Ldl_end
1:
	movz x0, #0x8000, lsl #48
	b .Ldl_end

// ===== ネットワーク (0x99…) =====

_sign_dev_nu:
	sub sp, sp, #16
	add x2, sp, #16
	mov x3, #10
1:
	udiv x4, x0, x3
	msub x5, x4, x3, x0
	add x5, x5, #48
	sub x2, x2, #1
	strb w5, [x2]
	mov x0, x4
	cbnz x0, 1b
	add x6, sp, #16
2:
	ldrb w5, [x2]
	strb w5, [x1]
	add x2, x2, #1
	add x1, x1, #1
	cmp x2, x6
	b.ne 2b
	add sp, sp, #16
	ret

_sign_dev_nip:
	stp x29, x30, [sp, #-32]!
	mov x29, sp
	str x0, [sp, #16]
	mov x13, #0
1:
	ldr x0, [sp, #16]
	lsl x2, x13, #3
	lsr x0, x0, x2
	and x0, x0, #0xFF
	bl _sign_dev_nu
	add x13, x13, #1
	cmp x13, #4
	b.eq 2f
	mov x2, #46
	strb w2, [x1]
	add x1, x1, #1
	b 1b
2:
	ldp x29, x30, [sp], #32
	ret

_sign_dev_nbe:
	and x0, x0, #0xFFFF
	lsr x1, x0, #8
	and x2, x0, #0xFF
	lsl x2, x2, #8
	orr x0, x1, x2
	ret

_sign_dev_nhost:
	stp x29, x30, [sp, #-32]!
	mov x29, sp
	sub x2, x1, #1
	cmp x2, #255
	b.lo 1f
	mov x0, #-22
	b .Lnh_ret
1:
	str x1, [sp, #16]
	mov x2, x1
	adrp x1, _sign_nhs
	add x1, x1, :lo12:_sign_nhs
	bl _sign_dev_pack
	ldr x1, [sp, #16]
	adrp x2, _sign_nhs
	add x2, x2, :lo12:_sign_nhs
	add x3, x2, x1
	cmp x1, #9
	b.ne .Lnh_parse
	adrp x6, _sign_nlh
	add x6, x6, :lo12:_sign_nlh
	mov x7, #0
2:
	add x13, x2, x7
	ldrb w10, [x13]
	add x13, x6, x7
	ldrb w11, [x13]
	cmp x10, x11
	b.ne .Lnh_parse
	add x7, x7, #1
	cmp x7, #9
	b.ne 2b
	movz x0, #0x7f
	movk x0, #0x100, lsl #16
	b .Lnh_ret
.Lnh_parse:
	adrp x2, _sign_nhs
	add x2, x2, :lo12:_sign_nhs
	ldr x1, [sp, #16]
	add x3, x2, x1
	bl _sign_dev_nparse
	cmp x0, #0
	b.ge .Lnh_ret
	ldr x1, [sp, #16]
	bl _sign_dev_ndns
.Lnh_ret:
	ldp x29, x30, [sp], #32
	ret

_sign_dev_nparse:
	mov x4, #0
	mov x5, #0
.Lnh_oct:
	cmp x2, x3
	b.hs .Lnh_bad
	mov x6, #0
	mov x7, #0
.Lnh_dig:
	cmp x2, x3
	b.hs .Lnh_end
	ldrb w10, [x2]
	sub x11, x10, #48
	cmp x11, #10
	b.hs .Lnh_end
	mov x12, #10
	mul x6, x6, x12
	add x6, x6, x11
	add x7, x7, #1
	cmp x6, #255
	b.hi .Lnh_bad
	add x2, x2, #1
	b .Lnh_dig
.Lnh_end:
	cbz x7, .Lnh_bad
	lsl x12, x5, #3
	lsl x6, x6, x12
	orr x4, x4, x6
	add x5, x5, #1
	cmp x5, #4
	b.eq .Lnh_last
	cmp x2, x3
	b.hs .Lnh_bad
	ldrb w10, [x2]
	cmp x10, #46
	b.ne .Lnh_bad
	add x2, x2, #1
	b .Lnh_oct
.Lnh_last:
	cmp x2, x3
	b.ne .Lnh_bad
	mov x0, x4
	ret
.Lnh_bad:
	mov x0, #-2
	ret

// 名前 → ip(DNS): x1 = 長さ(名前は _sign_nhs)→ x0 = ip か -2。/etc/resolv.conf の最初の nameserver(IPv4)に UDP で A を聞く(2 回、各 2 秒)。/etc/hosts は読まない
_sign_dev_ndns:
	stp x29, x30, [sp, #-96]!
	mov x29, sp
	str x1, [sp, #24]
	mov x1, #-1
	str x1, [sp, #16]
	mov x0, #-100
	adrp x1, _sign_dns_path
	add x1, x1, :lo12:_sign_dns_path
	mov x2, #0
	mov x3, #0
	mov x8, #56
	svc #0
	movz x1, #0x7f
	movk x1, #0x100, lsl #16
	str x1, [sp, #32]
	cmp x0, #0
	b.lt .Ldns_build
	str x0, [sp, #40]
	adrp x1, _sign_dnsc
	add x1, x1, :lo12:_sign_dnsc
	mov x2, #2000
	mov x8, #63
	svc #0
	str x0, [sp, #48]
	ldr x0, [sp, #40]
	mov x8, #57
	svc #0
	ldr x4, [sp, #48]
	cmp x4, #0
	b.le .Ldns_build
	adrp x2, _sign_dnsc
	add x2, x2, :lo12:_sign_dnsc
	add x3, x2, x4
	strb wzr, [x3]
.Ldns_line:
	cmp x2, x3
	b.hs .Ldns_build
	adrp x6, _sign_dns_kw
	add x6, x6, :lo12:_sign_dns_kw
	mov x7, #0
1:
	add x13, x2, x7
	ldrb w10, [x13]
	add x13, x6, x7
	ldrb w11, [x13]
	cmp x10, x11
	b.ne .Ldns_next
	add x7, x7, #1
	cmp x7, #10
	b.ne 1b
	add x2, x2, #10
2:
	cmp x2, x3
	b.hs .Ldns_build
	ldrb w10, [x2]
	cmp x10, #32
	b.eq 3f
	cmp x10, #9
	b.ne 4f
3:
	add x2, x2, #1
	b 2b
4:
	mov x4, x2
5:
	cmp x4, x3
	b.hs 6f
	ldrb w10, [x4]
	cmp x10, #33
	b.lo 6f
	add x4, x4, #1
	b 5b
6:
	stp x3, x4, [sp, #56]
	mov x3, x4
	bl _sign_dev_nparse
	ldp x3, x4, [sp, #56]
	cmp x0, #0
	b.lt 7f
	str x0, [sp, #32]
	b .Ldns_build
7:
	mov x2, x4
.Ldns_next:
	cmp x2, x3
	b.hs .Ldns_build
	ldrb w10, [x2]
	add x2, x2, #1
	cmp x10, #10
	b.ne .Ldns_next
	b .Ldns_line
.Ldns_build:
	adrp x5, _sign_dnsq
	add x5, x5, :lo12:_sign_dnsq
	adrp x6, _sign_dns_hdr
	add x6, x6, :lo12:_sign_dns_hdr
	mov x7, #0
1:
	add x13, x6, x7
	ldrb w10, [x13]
	add x13, x5, x7
	strb w10, [x13]
	add x7, x7, #1
	cmp x7, #12
	b.ne 1b
	add x5, x5, #12
	adrp x3, _sign_nhs
	add x3, x3, :lo12:_sign_nhs
	ldr x4, [sp, #24]
	add x4, x3, x4
.Ldns_lab:
	mov x6, x3
7:
	cmp x3, x4
	b.hs 8f
	ldrb w10, [x3]
	cmp x10, #46
	b.eq 8f
	add x3, x3, #1
	b 7b
8:
	sub x7, x3, x6
	cbz x7, .Ldns_bad
	cmp x7, #63
	b.hi .Ldns_bad
	strb w7, [x5]
	add x5, x5, #1
9:
	cbz x7, 10f
	ldrb w10, [x6]
	strb w10, [x5]
	add x6, x6, #1
	add x5, x5, #1
	sub x7, x7, #1
	b 9b
10:
	cmp x3, x4
	b.hs 11f
	add x3, x3, #1
	cmp x3, x4
	b.hs 11f
	b .Ldns_lab
11:
	strb wzr, [x5]
	mov x10, #0
	strb w10, [x5, #1]
	mov x10, #1
	strb w10, [x5, #2]
	mov x10, #0
	strb w10, [x5, #3]
	mov x10, #1
	strb w10, [x5, #4]
	add x5, x5, #5
	adrp x2, _sign_dnsq
	add x2, x2, :lo12:_sign_dnsq
	sub x5, x5, x2
	str x5, [sp, #48]
	mov x0, #2
	mov x1, #2
	mov x2, #0
	mov x8, #198
	svc #0
	cmp x0, #0
	b.lt .Ldns_bad
	str x0, [sp, #16]
	ldr x0, [sp, #32]
	mov x1, #53
	add x2, sp, #64
	bl _sign_dev_nsa
	mov x1, #2
	str x1, [sp, #40]
.Ldns_try:
	ldr x0, [sp, #16]
	adrp x1, _sign_dnsq
	add x1, x1, :lo12:_sign_dnsq
	ldr x2, [sp, #48]
	mov x3, #0
	add x4, sp, #64
	mov x5, #16
	mov x8, #206
	svc #0
	cmp x0, #0
	b.lt .Ldns_fail
	ldr x0, [sp, #16]
	mov x1, #2000
	bl _sign_dev_nwait
	cmp x0, #0
	b.ne .Ldns_retry
	ldr x0, [sp, #16]
	adrp x1, _sign_dnsr
	add x1, x1, :lo12:_sign_dnsr
	mov x2, #512
	mov x3, #0x40
	mov x4, #0
	mov x5, #0
	mov x8, #207
	svc #0
	cmp x0, #12
	b.lt .Ldns_retry
	str x0, [sp, #48]
	adrp x2, _sign_dnsr
	add x2, x2, :lo12:_sign_dnsr
	ldrb w10, [x2]
	cmp x10, #0x5a
	b.ne .Ldns_retry
	ldrb w10, [x2, #1]
	cmp x10, #0x1d
	b.ne .Ldns_retry
	ldrb w10, [x2, #2]
	and x11, x10, #0x80
	cbz x11, .Ldns_retry
	ldrb w10, [x2, #3]
	and x10, x10, #0xF
	cbnz x10, .Ldns_fail
	ldrb w9, [x2, #6]
	ldrb w10, [x2, #7]
	lsl x9, x9, #8
	orr x9, x9, x10
	cmp x9, #64
	b.ls 1f
	mov x9, #64
1:
	ldr x4, [sp, #48]
	add x4, x2, x4
	add x3, x2, #12
	bl _sign_dev_dskip
	cmp x0, #0
	b.lt .Ldns_fail
	add x3, x3, #4
.Ldns_ans:
	cbz x9, .Ldns_fail
	bl _sign_dev_dskip
	cmp x0, #0
	b.lt .Ldns_fail
	add x12, x3, #10
	cmp x12, x4
	b.hi .Ldns_fail
	ldrb w10, [x3]
	ldrb w11, [x3, #1]
	lsl x10, x10, #8
	orr x10, x10, x11
	ldrb w13, [x3, #8]
	ldrb w14, [x3, #9]
	lsl x13, x13, #8
	orr x13, x13, x14
	add x3, x3, #10
	add x14, x3, x13
	cmp x14, x4
	b.hi .Ldns_fail
	cmp x10, #1
	b.ne 2f
	cmp x13, #4
	b.ne 2f
	ldr w0, [x3]
	str x0, [sp, #56]
	ldr x0, [sp, #16]
	mov x8, #57
	svc #0
	ldr x0, [sp, #56]
	b .Ldns_ret
2:
	mov x3, x14
	sub x9, x9, #1
	b .Ldns_ans
.Ldns_retry:
	ldr x1, [sp, #40]
	sub x1, x1, #1
	str x1, [sp, #40]
	cbnz x1, .Ldns_try
.Ldns_fail:
	ldr x0, [sp, #16]
	mov x8, #57
	svc #0
.Ldns_bad:
	mov x0, #-2
.Ldns_ret:
	ldp x29, x30, [sp], #96
	ret

// 名前を飛ばす(ラベル列か圧縮ポインタ): x3 = 位置, x4 = 終わり → x3 が進む, x0 = 0 か -1
_sign_dev_dskip:
1:
	cmp x3, x4
	b.hs 4f
	ldrb w10, [x3]
	cbnz x10, 2f
	add x3, x3, #1
	mov x0, #0
	ret
2:
	and x11, x10, #0xC0
	cmp x11, #0xC0
	b.ne 3f
	add x3, x3, #2
	mov x0, #0
	ret
3:
	add x3, x3, x10
	add x3, x3, #1
	b 1b
4:
	mov x0, #-1
	ret

// x0 = fd, x1 = 種類 → x0 = ハンドル(1〜32)か -24(いっぱい。fd は閉じる)
_sign_dev_nnew:
	adrp x2, _sign_nh
	add x2, x2, :lo12:_sign_nh
	mov x3, #0
	mov x6, #24
1:
	mul x7, x3, x6
	add x5, x2, x7
	ldr x4, [x5]
	cbz x4, 2f
	add x3, x3, #1
	cmp x3, #32
	b.ne 1b
	mov x8, #57
	svc #0
	mov x0, #-24
	ret
2:
	add x4, x0, #1
	str x4, [x5]
	str x1, [x5, #8]
	mov x6, #5000
	str x6, [x5, #16]
	add x0, x3, #1
	ret

// x0 = ハンドル → x0 = fd か -9, x5 = 表の項
_sign_dev_nget:
	sub x1, x0, #1
	cmp x1, #32
	b.hs 1f
	adrp x2, _sign_nh
	add x2, x2, :lo12:_sign_nh
	mov x6, #24
	mul x7, x1, x6
	add x5, x2, x7
	ldr x4, [x5]
	cbz x4, 1f
	sub x0, x4, #1
	ret
1:
	mov x0, #-9
	ret

_sign_dev_nwait:
	stp x29, x30, [sp, #-48]!
	mov x29, sp
	str w0, [sp, #16]
	mov x2, #1
	strh w2, [sp, #20]
	mov x2, #0
	strh w2, [sp, #22]
	mov x3, #1000
	udiv x4, x1, x3
	msub x5, x4, x3, x1
	mov x6, #1000
	mul x5, x5, x6
	mul x5, x5, x6
	str x4, [sp, #24]
	str x5, [sp, #32]
	add x0, sp, #16
	mov x1, #1
	add x2, sp, #24
	mov x3, #0
	mov x4, #8
	mov x8, #73
	svc #0
	cmp x0, #0
	b.gt 2f
	b.eq 1f
	b 3f
1:
	mov x0, #-11
	b 3f
2:
	mov x0, #0
3:
	ldp x29, x30, [sp], #48
	ret

_sign_dev_nsa:
	stp x29, x30, [sp, #-32]!
	mov x29, sp
	stp x0, x2, [sp, #16]
	mov x0, x1
	bl _sign_dev_nbe
	ldp x1, x2, [sp, #16]
	mov x3, #2
	strh w3, [x2]
	strh w0, [x2, #2]
	str w1, [x2, #4]
	str xzr, [x2, #8]
	ldp x29, x30, [sp], #32
	ret

// x0 = 番号。結果 = x0
_sign_dev_net:
	stp x29, x30, [sp, #-160]!
	mov x29, sp
	str x0, [sp, #16]
	adrp x11, _sign_dreg
	add x11, x11, :lo12:_sign_dreg
	add x11, x11, #0x3000
	ldr w1, [x11, #4]
	str x1, [sp, #24]
	ldr w1, [x11, #8]
	str x1, [sp, #32]
	ldr w1, [x11, #12]
	str x1, [sp, #40]
	ldr w1, [x11, #16]
	str x1, [sp, #48]
	ldr w1, [x11, #20]
	str x1, [sp, #56]
	ldr w1, [x11, #24]
	str x1, [sp, #64]
	cmp x0, #1
	b.eq .Lnet_conn
	cmp x0, #2
	b.eq .Lnet_send
	cmp x0, #3
	b.eq .Lnet_recv
	cmp x0, #4
	b.eq .Lnet_close
	cmp x0, #5
	b.eq .Lnet_listen
	cmp x0, #6
	b.eq .Lnet_accept
	cmp x0, #7
	b.eq .Lnet_udp
	cmp x0, #8
	b.eq .Lnet_sendto
	cmp x0, #9
	b.eq .Lnet_recvfrom
	cmp x0, #10
	b.eq .Lnet_settmo
	cmp x0, #11
	b.eq .Lnet_resolve
	cmp x0, #12
	b.eq .Lnet_port
	cmp x0, #13
	b.eq .Lnet_tls
	mov x0, #-38
	b .Lnet_ret
.Lnet_einval:
	mov x0, #-22
.Lnet_ret:
	ldp x29, x30, [sp], #160
	ret

.Lnet_failclose:
	str x0, [sp, #104]
	ldr x0, [sp, #72]
	mov x8, #57
	svc #0
	ldr x0, [sp, #104]
	b .Lnet_ret
.Lnet_conn:
	ldr x0, [sp, #24]
	ldr x1, [sp, #32]
	bl _sign_dev_nhost
	cmp x0, #0
	b.lt .Lnet_ret
	str x0, [sp, #80]
	ldr x1, [sp, #40]
	sub x2, x1, #1
	mov x3, #65535
	cmp x2, x3
	b.hs .Lnet_einval
	mov x0, #2
	mov x1, #1
	mov x2, #0
	mov x8, #198
	svc #0
	cmp x0, #0
	b.lt .Lnet_ret
	str x0, [sp, #72]
	mov x1, #10
	str x1, [sp, #112]
	str xzr, [sp, #120]
	mov x1, #1
	mov x2, #21
	add x3, sp, #112
	mov x4, #16
	mov x8, #208
	svc #0
	ldr x0, [sp, #80]
	ldr x1, [sp, #40]
	add x2, sp, #112
	bl _sign_dev_nsa
	ldr x0, [sp, #72]
	add x1, sp, #112
	mov x2, #16
	mov x8, #203
	svc #0
	cmp x0, #0
	b.ge 1f
	mov x2, #-115
	cmp x0, x2
	b.ne .Lnet_failclose
	mov x0, #-110
	b .Lnet_failclose
1:
	ldr x0, [sp, #72]
	mov x1, #1
	bl _sign_dev_nnew
	b .Lnet_ret
.Lnet_send:
	ldr x0, [sp, #24]
	bl _sign_dev_nget
	cmp x0, #0
	b.lt .Lnet_ret
	str x0, [sp, #72]
	str x5, [sp, #136]
	ldr x2, [sp, #40]
	mov x3, #65536
	cmp x2, x3
	b.hi .Lnet_einval
	cmp x2, #0
	b.lt .Lnet_einval
	str x2, [sp, #96]
	ldr x0, [sp, #32]
	adrp x1, _sign_nbuf
	add x1, x1, :lo12:_sign_nbuf
	str x1, [sp, #88]
	bl _sign_dev_pack
1:
	ldr x2, [sp, #96]
	cbz x2, 2f
	ldr x0, [sp, #72]
	ldr x1, [sp, #88]
	mov x3, #0x4000
	mov x4, #0
	mov x5, #0
	mov x8, #206
	svc #0
	cmp x0, #0
	b.le .Lnet_sendend
	ldr x1, [sp, #88]
	add x1, x1, x0
	str x1, [sp, #88]
	ldr x2, [sp, #96]
	sub x2, x2, x0
	str x2, [sp, #96]
	b 1b
2:
	ldr x0, [sp, #40]
	b .Lnet_ret
.Lnet_sendend:
	cmp x0, #0
	b.lt .Lnet_ret
	mov x0, #-5
	b .Lnet_ret
.Lnet_recv:
	ldr x0, [sp, #24]
	bl _sign_dev_nget
	cmp x0, #0
	b.lt .Lnet_ret
	str x0, [sp, #72]
	str x5, [sp, #136]
	ldr x2, [sp, #40]
	mov x3, #65536
	cmp x2, x3
	b.hi .Lnet_einval
	cmp x2, #0
	b.lt .Lnet_einval
	ldr x5, [sp, #136]
	ldr x1, [x5, #16]
	ldr x0, [sp, #72]
	bl _sign_dev_nwait
	cmp x0, #0
	b.lt .Lnet_ret
	ldr x0, [sp, #72]
	adrp x1, _sign_nbuf
	add x1, x1, :lo12:_sign_nbuf
	ldr x2, [sp, #40]
	mov x3, #0x40
	mov x4, #0
	mov x5, #0
	mov x8, #207
	svc #0
	cmp x0, #0
	b.le .Lnet_ret
	str x0, [sp, #104]
	mov x2, x0
	adrp x0, _sign_nbuf
	add x0, x0, :lo12:_sign_nbuf
	ldr x1, [sp, #32]
	bl _sign_dev_unpack
	ldr x0, [sp, #104]
	b .Lnet_ret
.Lnet_close:
	ldr x0, [sp, #24]
	bl _sign_dev_nget
	cmp x0, #0
	b.lt .Lnet_ret
	str x0, [sp, #72]
	str x5, [sp, #136]
	mov x8, #57
	svc #0
	ldr x5, [sp, #136]
	str xzr, [x5]
	mov x0, #0
	b .Lnet_ret
.Lnet_listen:
	ldr x1, [sp, #24]
	mov x3, #65535
	cmp x1, x3
	b.hi .Lnet_einval
	cmp x1, #0
	b.lt .Lnet_einval
	mov x0, #2
	mov x1, #1
	mov x2, #0
	mov x8, #198
	svc #0
	cmp x0, #0
	b.lt .Lnet_ret
	str x0, [sp, #72]
	mov x1, #1
	str x1, [sp, #112]
	mov x1, #1
	mov x2, #2
	add x3, sp, #112
	mov x4, #4
	mov x8, #208
	svc #0
	mov x0, #0
	ldr x1, [sp, #24]
	add x2, sp, #112
	bl _sign_dev_nsa
	ldr x0, [sp, #72]
	add x1, sp, #112
	mov x2, #16
	mov x8, #200
	svc #0
	cmp x0, #0
	b.lt .Lnet_failclose
	ldr x1, [sp, #32]
	cmp x1, #0
	b.gt 1f
	mov x1, #5
1:
	cmp x1, #128
	b.ls 2f
	mov x1, #128
2:
	ldr x0, [sp, #72]
	mov x8, #201
	svc #0
	cmp x0, #0
	b.lt .Lnet_failclose
	ldr x0, [sp, #72]
	mov x1, #2
	bl _sign_dev_nnew
	b .Lnet_ret
.Lnet_accept:
	ldr x0, [sp, #24]
	bl _sign_dev_nget
	cmp x0, #0
	b.lt .Lnet_ret
	str x0, [sp, #72]
	str x5, [sp, #136]
	ldr x5, [sp, #136]
	ldr x4, [x5, #8]
	cmp x4, #2
	b.ne .Lnet_einval
	ldr x1, [x5, #16]
	ldr x0, [sp, #72]
	bl _sign_dev_nwait
	cmp x0, #0
	b.lt .Lnet_ret
	ldr x0, [sp, #72]
	mov x1, #0
	mov x2, #0
	mov x8, #202
	svc #0
	cmp x0, #0
	b.lt .Lnet_ret
	mov x1, #1
	bl _sign_dev_nnew
	b .Lnet_ret
.Lnet_udp:
	ldr x1, [sp, #24]
	mov x3, #65535
	cmp x1, x3
	b.hi .Lnet_einval
	cmp x1, #0
	b.lt .Lnet_einval
	mov x0, #2
	mov x1, #2
	mov x2, #0
	mov x8, #198
	svc #0
	cmp x0, #0
	b.lt .Lnet_ret
	str x0, [sp, #72]
	mov x0, #0
	ldr x1, [sp, #24]
	add x2, sp, #112
	bl _sign_dev_nsa
	ldr x0, [sp, #72]
	add x1, sp, #112
	mov x2, #16
	mov x8, #200
	svc #0
	cmp x0, #0
	b.lt .Lnet_failclose
	ldr x0, [sp, #72]
	mov x1, #3
	bl _sign_dev_nnew
	b .Lnet_ret
.Lnet_sendto:
	ldr x0, [sp, #24]
	bl _sign_dev_nget
	cmp x0, #0
	b.lt .Lnet_ret
	str x0, [sp, #72]
	str x5, [sp, #136]
	ldr x0, [sp, #32]
	ldr x1, [sp, #40]
	bl _sign_dev_nhost
	cmp x0, #0
	b.lt .Lnet_ret
	str x0, [sp, #80]
	ldr x1, [sp, #48]
	sub x2, x1, #1
	mov x3, #65535
	cmp x2, x3
	b.hs .Lnet_einval
	ldr x2, [sp, #64]
	mov x3, #65536
	cmp x2, x3
	b.hi .Lnet_einval
	cmp x2, #0
	b.lt .Lnet_einval
	ldr x0, [sp, #56]
	adrp x1, _sign_nbuf
	add x1, x1, :lo12:_sign_nbuf
	ldr x2, [sp, #64]
	bl _sign_dev_pack
	ldr x0, [sp, #80]
	ldr x1, [sp, #48]
	add x2, sp, #112
	bl _sign_dev_nsa
	ldr x0, [sp, #72]
	adrp x1, _sign_nbuf
	add x1, x1, :lo12:_sign_nbuf
	ldr x2, [sp, #64]
	mov x3, #0x4000
	add x4, sp, #112
	mov x5, #16
	mov x8, #206
	svc #0
	b .Lnet_ret
.Lnet_recvfrom:
	ldr x0, [sp, #24]
	bl _sign_dev_nget
	cmp x0, #0
	b.lt .Lnet_ret
	str x0, [sp, #72]
	str x5, [sp, #136]
	ldr x2, [sp, #40]
	mov x3, #65536
	cmp x2, x3
	b.hi .Lnet_einval
	cmp x2, #0
	b.lt .Lnet_einval
	ldr x5, [sp, #136]
	ldr x1, [x5, #16]
	ldr x0, [sp, #72]
	bl _sign_dev_nwait
	cmp x0, #0
	b.lt .Lnet_ret
	mov x1, #16
	str x1, [sp, #128]
	ldr x0, [sp, #72]
	adrp x1, _sign_nbuf
	add x1, x1, :lo12:_sign_nbuf
	ldr x2, [sp, #40]
	mov x3, #0x40
	add x4, sp, #112
	add x5, sp, #128
	mov x8, #207
	svc #0
	cmp x0, #0
	b.lt .Lnet_ret
	str x0, [sp, #104]
	mov x2, x0
	adrp x0, _sign_nbuf
	add x0, x0, :lo12:_sign_nbuf
	ldr x1, [sp, #32]
	bl _sign_dev_unpack
	ldr w0, [sp, #116]
	adrp x1, _sign_nhs
	add x1, x1, :lo12:_sign_nhs
	bl _sign_dev_nip
	mov x2, #58
	strb w2, [x1]
	add x1, x1, #1
	str x1, [sp, #88]
	ldrh w0, [sp, #114]
	bl _sign_dev_nbe
	ldr x1, [sp, #88]
	bl _sign_dev_nu
	strb wzr, [x1]
	add x1, x1, #1
	adrp x0, _sign_nhs
	add x0, x0, :lo12:_sign_nhs
	sub x2, x1, x0
	ldr x1, [sp, #48]
	bl _sign_dev_unpack
	ldr x0, [sp, #104]
	b .Lnet_ret
.Lnet_settmo:
	ldr x0, [sp, #24]
	bl _sign_dev_nget
	cmp x0, #0
	b.lt .Lnet_ret
	str x0, [sp, #72]
	str x5, [sp, #136]
	ldr x1, [sp, #32]
	cmp x1, #0
	b.lt .Lnet_einval
	ldr x5, [sp, #136]
	str x1, [x5, #16]
	mov x0, #0
	b .Lnet_ret
.Lnet_resolve:
	ldr x0, [sp, #24]
	ldr x1, [sp, #32]
	bl _sign_dev_nhost
	cmp x0, #0
	b.lt .Lnet_ret
	adrp x1, _sign_nhs
	add x1, x1, :lo12:_sign_nhs
	bl _sign_dev_nip
	strb wzr, [x1]
	adrp x0, _sign_nhs
	add x0, x0, :lo12:_sign_nhs
	sub x2, x1, x0
	str x2, [sp, #104]
	add x2, x2, #1
	ldr x1, [sp, #40]
	bl _sign_dev_unpack
	ldr x0, [sp, #104]
	b .Lnet_ret
.Lnet_port:
	ldr x0, [sp, #24]
	bl _sign_dev_nget
	cmp x0, #0
	b.lt .Lnet_ret
	str x0, [sp, #72]
	str x5, [sp, #136]
	mov x1, #16
	str x1, [sp, #128]
	ldr x0, [sp, #72]
	add x1, sp, #112
	add x2, sp, #128
	mov x8, #204
	svc #0
	cmp x0, #0
	b.lt .Lnet_ret
	ldrh w0, [sp, #114]
	bl _sign_dev_nbe
	b .Lnet_ret
.Lnet_tls:
	ldr x0, [sp, #24]
	bl _sign_dev_nget
	cmp x0, #0
	b.lt .Lnet_ret
	str x0, [sp, #72]
	str x5, [sp, #136]
	mov x0, #-38
	b .Lnet_ret

// ===== sys (0x94…) =====

_sign_dev_spath:
	stp x29, x30, [sp, #-32]!
	mov x29, sp
	str x1, [sp, #16]
	mov x2, x1
	adrp x1, _sign_sbuf
	add x1, x1, :lo12:_sign_sbuf
	bl _sign_dev_pack
	ldr x1, [sp, #16]
	adrp x2, _sign_sbuf
	add x2, x2, :lo12:_sign_sbuf
	add x3, x2, x1
1:
	cmp x2, x3
	b.hs 2f
	ldrb w4, [x2]
	cbz x4, 3f
	add x2, x2, #1
	b 1b
2:
	strb wzr, [x3]
	mov x0, #0
	b 4f
3:
	mov x0, #-22
4:
	ldp x29, x30, [sp], #32
	ret

_sign_dev_sfd:
	sub x1, x0, #3
	cmp x1, #16
	b.hs 1f
	adrp x2, _sign_sfd
	add x2, x2, :lo12:_sign_sfd
	lsl x3, x1, #3
	add x5, x2, x3
	ldr x4, [x5]
	cbz x4, 1f
	sub x0, x4, #1
	ret
1:
	mov x0, #-9
	ret

_sign_dev_sfree:
	adrp x2, _sign_sfd
	add x2, x2, :lo12:_sign_sfd
	mov x1, #0
1:
	lsl x3, x1, #3
	add x5, x2, x3
	ldr x4, [x5]
	cbz x4, 2f
	add x1, x1, #1
	cmp x1, #16
	b.ne 1b
	mov x0, #-24
	ret
2:
	mov x0, x1
	ret

_sign_dev_open2:
	stp x29, x30, [sp, #-64]!
	mov x29, sp
	mov x1, #0
	mov x2, #0
	cmp x0, #0
	b.eq 1f
	mov x1, #0x241
	mov x2, #0x1A4
	cmp x0, #1
	b.eq 1f
	mov x1, #0x441
1:
	str x1, [sp, #16]
	str x2, [sp, #24]
	mov x3, #8
	str x3, [sp, #32]
	mov x0, #-100
	adrp x1, _sign_sbuf
	add x1, x1, :lo12:_sign_sbuf
	add x2, sp, #16
	mov x3, #24
	mov x8, #437
	svc #0
	mov x2, #-18
	cmp x0, x2
	b.ne 2f
	mov x0, #-13
2:
	ldp x29, x30, [sp], #64
	ret

_sign_dev_sys:
	stp x29, x30, [sp, #-96]!
	mov x29, sp
	str x0, [sp, #16]
	adrp x11, _sign_dreg
	add x11, x11, :lo12:_sign_dreg
	add x11, x11, #0x4000
	ldr w1, [x11, #4]
	str x1, [sp, #24]
	ldr w1, [x11, #8]
	str x1, [sp, #32]
	ldr w1, [x11, #12]
	str x1, [sp, #40]
	cmp x0, #1
	b.eq .Lsys_read
	cmp x0, #2
	b.eq .Lsys_write
	cmp x0, #3
	b.eq .Lsys_open
	cmp x0, #4
	b.eq .Lsys_close
	cmp x0, #5
	b.eq .Lsys_times
	cmp x0, #6
	b.eq .Lsys_timems
	cmp x0, #7
	b.eq .Lsys_size
	mov x0, #-38
	b .Lsys_ret
.Lsys_einval:
	mov x0, #-22
.Lsys_ret:
	ldp x29, x30, [sp], #96
	ret

.Lsys_times:
	mov x0, #0
	add x1, sp, #64
	mov x8, #113
	svc #0
	ldr x0, [sp, #64]
	b .Lsys_ret
.Lsys_timems:
	mov x0, #0
	add x1, sp, #64
	mov x8, #113
	svc #0
	ldr x0, [sp, #64]
	mov x1, #1000
	mul x0, x0, x1
	ldr x2, [sp, #72]
	mov x3, #1000
	mul x3, x3, x1
	udiv x2, x2, x3
	add x0, x0, x2
	b .Lsys_ret
.Lsys_read:
	ldr x2, [sp, #40]
	movz x3, #0x10, lsl #16
	cmp x2, x3
	b.hi .Lsys_einval
	ldr x0, [sp, #24]
	cbz x0, 1f
	cmp x0, #3
	b.hs 2f
	mov x0, #-9
	b .Lsys_ret
2:
	bl _sign_dev_sfd
	cmp x0, #0
	b.lt .Lsys_ret
1:
	adrp x1, _sign_sbuf
	add x1, x1, :lo12:_sign_sbuf
	ldr x2, [sp, #40]
	mov x8, #63
	svc #0
	cmp x0, #0
	b.le .Lsys_ret
	str x0, [sp, #56]
	mov x2, x0
	adrp x0, _sign_sbuf
	add x0, x0, :lo12:_sign_sbuf
	ldr x1, [sp, #32]
	bl _sign_dev_unpack
	ldr x0, [sp, #56]
	b .Lsys_ret
.Lsys_write:
	ldr x2, [sp, #40]
	movz x3, #0x10, lsl #16
	cmp x2, x3
	b.hi .Lsys_einval
	ldr x0, [sp, #24]
	cbnz x0, 1f
	mov x0, #-9
	b .Lsys_ret
1:
	cmp x0, #3
	b.hs 2f
	str x0, [sp, #48]
	b 3f
2:
	bl _sign_dev_sfd
	cmp x0, #0
	b.lt .Lsys_ret
	str x0, [sp, #48]
3:
	ldr x0, [sp, #32]
	adrp x1, _sign_sbuf
	add x1, x1, :lo12:_sign_sbuf
	ldr x2, [sp, #40]
	bl _sign_dev_pack
	ldr x3, [sp, #40]
	str x3, [sp, #56]
	adrp x4, _sign_sbuf
	add x4, x4, :lo12:_sign_sbuf
	str x4, [sp, #64]
4:
	ldr x2, [sp, #56]
	cbz x2, 5f
	ldr x0, [sp, #48]
	ldr x1, [sp, #64]
	mov x8, #64
	svc #0
	cmp x0, #0
	b.le .Lsys_wend
	ldr x1, [sp, #64]
	add x1, x1, x0
	str x1, [sp, #64]
	ldr x2, [sp, #56]
	sub x2, x2, x0
	str x2, [sp, #56]
	b 4b
5:
	ldr x0, [sp, #40]
	b .Lsys_ret
.Lsys_wend:
	cmp x0, #0
	b.lt .Lsys_ret
	mov x0, #-5
	b .Lsys_ret
.Lsys_open:
	ldr x2, [sp, #40]
	cmp x2, #2
	b.hi .Lsys_einval
	bl _sign_dev_sfree
	cmp x0, #0
	b.lt .Lsys_ret
	str x0, [sp, #56]
	str x5, [sp, #48]
	ldr x1, [sp, #32]
	sub x2, x1, #1
	cmp x2, #1024
	b.hs .Lsys_einval
	ldr x0, [sp, #24]
	bl _sign_dev_spath
	cmp x0, #0
	b.lt .Lsys_ret
	ldr x0, [sp, #40]
	bl _sign_dev_open2
	cmp x0, #0
	b.lt .Lsys_ret
	add x0, x0, #1
	ldr x5, [sp, #48]
	str x0, [x5]
	ldr x0, [sp, #56]
	add x0, x0, #3
	b .Lsys_ret
.Lsys_close:
	ldr x0, [sp, #24]
	bl _sign_dev_sfd
	cmp x0, #0
	b.lt .Lsys_ret
	str x5, [sp, #48]
	mov x8, #57
	svc #0
	ldr x5, [sp, #48]
	str xzr, [x5]
	mov x0, #0
	b .Lsys_ret
.Lsys_size:
	ldr x1, [sp, #32]
	sub x2, x1, #1
	cmp x2, #1024
	b.hs .Lsys_einval
	ldr x0, [sp, #24]
	bl _sign_dev_spath
	cmp x0, #0
	b.lt .Lsys_ret
	mov x0, #0
	bl _sign_dev_open2
	cmp x0, #0
	b.lt .Lsys_ret
	str x0, [sp, #48]
	mov x1, #0
	mov x2, #2
	mov x8, #62
	svc #0
	str x0, [sp, #56]
	ldr x0, [sp, #48]
	mov x8, #57
	svc #0
	ldr x0, [sp, #56]
	b .Lsys_ret

// ===== 入力 (0x93…) =====

_sign_dev_ipush:
	adrp x4, _sign_in
	add x4, x4, :lo12:_sign_in
	ldr x5, [x4, #144]
	ldr x6, [x4, #152]
	cmp x6, #256
	b.lo 1f
	add x5, x5, #1
	and x5, x5, #255
	str x5, [x4, #144]
	sub x6, x6, #1
1:
	add x7, x5, x6
	and x7, x7, #255
	add x8, x4, #1024
	add x8, x8, x7, lsl #4
	str w0, [x8]
	str w1, [x8, #4]
	str w2, [x8, #8]
	str w3, [x8, #12]
	add x6, x6, #1
	str x6, [x4, #152]
	ret

_sign_dev_ipop:
	adrp x4, _sign_in
	add x4, x4, :lo12:_sign_in
	ldr x6, [x4, #152]
	cbz x6, 1f
	ldr x5, [x4, #144]
	add x5, x5, #1
	and x5, x5, #255
	str x5, [x4, #144]
	sub x6, x6, #1
	str x6, [x4, #152]
1:
	ret

_sign_dev_iget:
	adrp x15, _sign_in
	add x15, x15, :lo12:_sign_in
	cmp x0, #0x500
	b.hs 9f
	cmp x0, #0x100
	b.lo 1f
	sub x0, x0, #0x100
	lsr x0, x0, #2
	add x1, x15, #640
	ldrb w0, [x1, x0]
	ret
1:
	ldr x2, [x15, #152]
	cmp x0, #0
	b.ne 2f
	mov x0, x2
	ret
2:
	cmp x0, #0x20
	b.ne 3f
	ldr x0, [x15, #160]
	ret
3:
	cmp x0, #0x24
	b.ne 4f
	ldr x0, [x15, #168]
	ret
4:
	cmp x0, #0x28
	b.ne 5f
	ldr x0, [x15, #176]
	ret
5:
	cbz x2, 9f
	ldr x3, [x15, #144]
	add x4, x15, #1024
	add x4, x4, x3, lsl #4
	cmp x0, #4
	b.ne 6f
	ldr w0, [x4]
	ret
6:
	cmp x0, #8
	b.ne 7f
	ldr w0, [x4, #4]
	ret
7:
	cmp x0, #0xC
	b.ne 8f
	ldr w0, [x4, #8]
	ret
8:
	cmp x0, #0x10
	b.ne 9f
	ldr w0, [x4, #12]
	ret
9:
	mov x0, #0
	ret

_sign_dev_ipoll:
	stp x29, x30, [sp, #-64]!
	mov x29, sp
	adrp x15, _sign_in
	add x15, x15, :lo12:_sign_in
	ldr x0, [x15]
	cbnz x0, 20f
	mov x0, #1
	str x0, [x15]
	movz x5, #0x642f
	movk x5, #0x7665, lsl #16
	movk x5, #0x692f, lsl #32
	movk x5, #0x706e, lsl #48
	movz x6, #0x7475
	movk x6, #0x652f, lsl #16
	movk x6, #0x6576, lsl #32
	movk x6, #0x746e, lsl #48
	mov x14, #0
10:
	mov x1, #10
	udiv x2, x14, x1
	msub x3, x2, x1, x14
	add x4, sp, #16
	str x5, [x4]
	str x6, [x4, #8]
	cbz x2, 11f
	add x2, x2, #48
	strb w2, [x4, #16]
	add x3, x3, #48
	strb w3, [x4, #17]
	strb wzr, [x4, #18]
	b 12f
11:
	add x3, x3, #48
	strb w3, [x4, #16]
	strb wzr, [x4, #17]
12:
	mov x0, #-100
	mov x1, x4
	mov x2, #0x800
	movk x2, #8, lsl #16
	mov x3, #0
	mov x8, #56
	svc #0
	cmp x0, #0
	b.lt 13f
	ldr x1, [x15, #8]
	cmp x1, #16
	b.hs 14f
	add x2, x15, #16
	lsl x3, x1, #3
	add x2, x2, x3
	str x0, [x2]
	add x1, x1, #1
	str x1, [x15, #8]
	b 13f
14:
	mov x8, #57
	svc #0
13:
	add x14, x14, #1
	cmp x14, #32
	b.ne 10b
20:
	mov x14, #0
	mov x11, #0
21:
	ldr x1, [x15, #8]
	cmp x14, x1
	b.hs 90f
	add x2, x15, #16
	lsl x3, x14, #3
	add x2, x2, x3
	ldr x13, [x2]
	cmp x13, #0
	b.lt 29f
22:
	mov x0, x13
	add x1, x15, #256
	mov x2, #384
	mov x8, #63
	svc #0
	cmp x0, #24
	b.ge 23f
	mov x4, #-19
	cmp x0, x4
	b.ne 29f
	mov x0, x13
	mov x8, #57
	svc #0
	add x2, x15, #16
	lsl x3, x14, #3
	add x2, x2, x3
	mov x4, #-1
	str x4, [x2]
	b 29f
23:
	mov x12, x0
	add x9, x15, #256
24:
	ldrh w4, [x9, #16]
	ldrh w5, [x9, #18]
	ldr w6, [x9, #20]
	lsl x6, x6, #32
	asr x6, x6, #32
	cmp x4, #1
	b.eq 30f
	cmp x4, #2
	b.eq 40f
	cbnz x4, 28f
	cbnz x5, 28f
	cbz x11, 28f
	mov x11, #0
	mov x0, #3
	mov x1, #0
	ldr x2, [x15, #160]
	ldr x3, [x15, #168]
	bl _sign_dev_ipush
	b 28f
30:
	cmp x6, #2
	b.eq 28f
	sub x7, x5, #0x110
	cmp x7, #3
	b.lo 35f
	cmp x5, #256
	b.hs 28f
	adrp x7, _sign_inmap
	add x7, x7, :lo12:_sign_inmap
	ldrb w7, [x7, x5]
	cbz x7, 28f
	add x8, x15, #640
	cmp x6, #0
	b.eq 31f
	mov x4, #1
	strb w4, [x8, x7]
	mov x0, #1
	mov x1, x7
	mov x2, #0
	mov x3, #0
	bl _sign_dev_ipush
	b 28f
31:
	strb wzr, [x8, x7]
	mov x0, #2
	mov x1, x7
	mov x2, #0
	mov x3, #0
	bl _sign_dev_ipush
	b 28f
35:
	mov x0, #1
	mov x1, #3
	cmp x7, #0
	csel x0, x0, x1, eq
	mov x1, #2
	cmp x7, #2
	csel x0, x1, x0, eq
	sub x1, x0, #1
	mov x2, #1
	lsl x2, x2, x1
	ldr x3, [x15, #176]
	cmp x6, #0
	b.eq 36f
	orr x3, x3, x2
	mov x4, #4
	b 37f
36:
	and x5, x3, x2
	sub x3, x3, x5
	mov x4, #5
37:
	str x3, [x15, #176]
	mov x1, x0
	mov x0, x4
	ldr x2, [x15, #160]
	ldr x3, [x15, #168]
	bl _sign_dev_ipush
	b 28f
40:
	cmp x5, #0
	b.ne 41f
	ldr x7, [x15, #160]
	add x7, x7, x6
	cmp x7, #0
	csel x7, xzr, x7, lt
	mov x8, #1919
	cmp x7, x8
	csel x7, x8, x7, gt
	str x7, [x15, #160]
	mov x11, #1
	b 28f
41:
	cmp x5, #1
	b.ne 28f
	ldr x7, [x15, #168]
	add x7, x7, x6
	cmp x7, #0
	csel x7, xzr, x7, lt
	mov x8, #1079
	cmp x7, x8
	csel x7, x8, x7, gt
	str x7, [x15, #168]
	mov x11, #1
	b 28f
28:
	add x9, x9, #24
	sub x12, x12, #24
	cmp x12, #24
	b.hs 24b
	b 22b
29:
	add x14, x14, #1
	b 21b
90:
	ldp x29, x30, [sp], #64
	ret

// ===== 描画 (0x91…) 論理画面 64 x 32 =====

_sign_dev_ginit:
	adrp x15, _sign_gfx
	add x15, x15, :lo12:_sign_gfx
	ldr x2, [x15]
	cbnz x2, 1f
	mov x2, #1
	str x2, [x15]
	mov x2, #0xFFFF
	movk x2, #0xFF, lsl #16
	str x2, [x15, #8]
	mov x2, #-1
	str x2, [x15, #72]
1:
	ret

_sign_dev_gput:
	mov x3, #64
	cmp x0, x3
	b.hs 1f
	mov x4, #32
	cmp x1, x4
	b.hs 1f
	mul x4, x1, x3
	add x4, x4, x0
	lsl x4, x4, #2
	adrp x5, _sign_gpix
	add x5, x5, :lo12:_sign_gpix
	str w2, [x5, x4]
	ret
1:
	adrp x6, _sign_gfx
	add x6, x6, :lo12:_sign_gfx
	mov x7, #1
	str x7, [x6, #48]
	ret

_sign_dev_gst:
	stp x29, x30, [sp, #-32]!
	mov x29, sp
	str x0, [sp, #16]
	str x1, [sp, #24]
	bl _sign_dev_ginit
	ldr x0, [sp, #16]
	ldr x1, [sp, #24]
	cmp x0, #0x1000
	b.lo 2f
	sub x2, x0, #0x1000
	lsr x2, x2, #2
	mov x3, #2048
	cmp x2, x3
	b.hs 9f
	and x1, x1, #0xFFFFFF
	lsl x2, x2, #2
	adrp x3, _sign_gpix
	add x3, x3, :lo12:_sign_gpix
	str w1, [x3, x2]
	b 9f
2:
	cmp x0, #0x14
	b.ne 3f
	mov x0, x1
	bl _sign_dev_gcmd
	b 9f
3:
	cmp x0, #8
	b.ne 4f
	mov x3, #8
	b 5f
4:
	cmp x0, #12
	b.ne 4f
	mov x3, #16
	b 5f
4:
	cmp x0, #16
	b.ne 4f
	mov x3, #24
	b 5f
4:
	cmp x0, #24
	b.ne 4f
	mov x3, #32
	b 5f
4:
	cmp x0, #28
	b.ne 4f
	mov x3, #40
	b 5f
4:
	cmp x0, #40
	b.ne 4f
	mov x3, #64
	b 5f
4:
	cmp x0, #44
	b.ne 4f
	mov x3, #72
	b 5f
4:
	cmp x0, #48
	b.ne 4f
	mov x3, #80
	b 5f
4:
	cmp x0, #52
	b.ne 4f
	mov x3, #88
	b 5f
4:
	b 9f
5:
	cmp x3, #8
	b.ne 6f
	and x1, x1, #0xFFFFFF
6:
	str x1, [x15, x3]
9:
	ldp x29, x30, [sp], #32
	ret

_sign_dev_gld:
	stp x29, x30, [sp, #-32]!
	mov x29, sp
	str x0, [sp, #16]
	bl _sign_dev_ginit
	ldr x0, [sp, #16]
	cmp x0, #0x1000
	b.lo 2f
	sub x2, x0, #0x1000
	lsr x2, x2, #2
	mov x3, #2048
	cmp x2, x3
	b.hs 8f
	lsl x2, x2, #2
	adrp x3, _sign_gpix
	add x3, x3, :lo12:_sign_gpix
	ldr w0, [x3, x2]
	b 9f
2:
	cmp x0, #0
	b.ne 3f
	mov x0, #64
	b 9f
3:
	cmp x0, #4
	b.ne 4f
	mov x0, #32
	b 9f
4:
	cmp x0, #8
	b.ne 5f
	ldr x0, [x15, #8]
	b 9f
5:
	cmp x0, #12
	b.ne 5f
	ldr x0, [x15, #16]
	b 9f
5:
	cmp x0, #16
	b.ne 5f
	ldr x0, [x15, #24]
	b 9f
5:
	cmp x0, #24
	b.ne 5f
	ldr x0, [x15, #32]
	b 9f
5:
	cmp x0, #28
	b.ne 5f
	ldr x0, [x15, #40]
	b 9f
5:
	cmp x0, #32
	b.ne 5f
	ldr x0, [x15, #48]
	b 9f
5:
	cmp x0, #36
	b.ne 5f
	ldr x0, [x15, #56]
	b 9f
5:
	cmp x0, #40
	b.ne 5f
	ldr x0, [x15, #64]
	b 9f
5:
	cmp x0, #44
	b.ne 5f
	ldr x0, [x15, #72]
	b 9f
5:
	cmp x0, #48
	b.ne 5f
	ldr x0, [x15, #80]
	b 9f
5:
	cmp x0, #52
	b.ne 5f
	ldr x0, [x15, #88]
	b 9f
5:
8:
	mov x0, #0
9:
	ldp x29, x30, [sp], #32
	ret

_sign_dev_gcmd:
	stp x29, x30, [sp, #-80]!
	mov x29, sp
	stp x16, x17, [sp, #64]
	adrp x15, _sign_gfx
	add x15, x15, :lo12:_sign_gfx
	str xzr, [x15, #48]
	ldr x10, [x15, #16]
	ldr x11, [x15, #24]
	ldr x12, [x15, #8]
	ldr x13, [x15, #32]
	ldr x14, [x15, #40]
	cmp x0, #1
	b.eq .Lg_plot
	cmp x0, #2
	b.eq .Lg_clear
	cmp x0, #3
	b.eq .Lg_present
	cmp x0, #4
	b.eq .Lg_line
	cmp x0, #5
	b.eq .Lg_rect
	cmp x0, #6
	b.eq .Lg_blit
	mov x0, #2
	str x0, [x15, #48]
.Lg_ret:
	ldp x16, x17, [sp, #64]
	ldp x29, x30, [sp], #80
	ret
.Lg_plot:
	mov x0, x10
	mov x1, x11
	mov x2, x12
	bl _sign_dev_gput
	b .Lg_ret
.Lg_clear:
	mov x1, #2048
	adrp x2, _sign_gpix
	add x2, x2, :lo12:_sign_gpix
1:
	sub x1, x1, #1
	lsl x3, x1, #2
	str w12, [x2, x3]
	cbnz x1, 1b
	b .Lg_ret
.Lg_present:
	ldr x0, [x15, #56]
	add x0, x0, #1
	str x0, [x15, #56]
	bl _sign_dev_gpresent
	b .Lg_ret
.Lg_line:
	sub x3, x13, x10
	neg x3, x3
	sub x4, x13, x10
	cmp x4, #0
	csel x3, x4, x3, gt
	str x3, [sp, #16]
	sub x3, x14, x11
	neg x3, x3
	sub x4, x14, x11
	cmp x4, #0
	csel x3, x4, x3, gt
	neg x3, x3
	str x3, [sp, #24]
	mov x3, #1
	mov x4, #-1
	cmp x10, x13
	csel x5, x3, x4, lt
	str x5, [sp, #32]
	cmp x11, x14
	csel x5, x3, x4, lt
	str x5, [sp, #40]
	ldr x3, [sp, #16]
	ldr x4, [sp, #24]
	add x3, x3, x4
	str x3, [sp, #48]
1:
	mov x0, x10
	mov x1, x11
	mov x2, x12
	bl _sign_dev_gput
	cmp x10, x13
	b.ne 2f
	cmp x11, x14
	b.eq .Lg_ret
2:
	ldr x3, [sp, #48]
	lsl x3, x3, #1
	ldr x4, [sp, #24]
	ldr x5, [sp, #16]
	ldr x6, [sp, #48]
	cmp x3, x4
	b.lt 3f
	add x6, x6, x4
	ldr x7, [sp, #32]
	add x10, x10, x7
3:
	cmp x3, x5
	b.gt 4f
	add x6, x6, x5
	ldr x7, [sp, #40]
	add x11, x11, x7
4:
	str x6, [sp, #48]
	b 1b
.Lg_rect:
	cmp x13, #0
	b.le .Lg_ret
	cmp x14, #0
	b.le .Lg_ret
	cmp x10, #0
	csel x2, x10, xzr, gt
	add x3, x10, x13
	mov x4, #64
	cmp x3, x4
	csel x3, x3, x4, lt
	cmp x11, #0
	csel x5, x11, xzr, gt
	add x6, x11, x14
	mov x7, #32
	cmp x6, x7
	csel x6, x6, x7, lt
	add x8, x10, x13
	cmp x2, x10
	b.ne 1f
	cmp x3, x8
	b.ne 1f
	add x8, x11, x14
	cmp x5, x11
	b.ne 1f
	cmp x6, x8
	b.eq 2f
1:
	mov x8, #1
	str x8, [x15, #48]
2:
	cmp x2, x3
	b.ge .Lg_ret
	cmp x5, x6
	b.ge .Lg_ret
	adrp x9, _sign_gpix
	add x9, x9, :lo12:_sign_gpix
3:
	mov x7, #64
	mul x7, x5, x7
	mov x8, x2
4:
	add x0, x7, x8
	lsl x0, x0, #2
	str w12, [x9, x0]
	add x8, x8, #1
	cmp x8, x3
	b.lt 4b
	add x5, x5, #1
	cmp x5, x6
	b.lt 3b
	b .Lg_ret
.Lg_blit:
	cmp x13, #0
	b.le 8f
	cmp x14, #0
	b.le 8f
	mul x2, x13, x14
	mov x3, #0x10000
	cmp x2, x3
	b.hi 8f
	ldr x3, [x15, #80]
	cmp x3, #0
	mov x4, #1
	csel x3, x4, x3, eq
	str x3, [sp, #16]
	cmp x3, #1
	b.lt 8f
	cmp x3, #64
	b.gt 8f
	ldr x3, [x15, #64]
	mov x4, #0x10000
	cmp x3, x4
	b.lt 8f
	lsl x2, x2, #2
	add x2, x2, x3
	mov x4, #0x9000000
	cmp x2, x4
	b.hi 8f
	mov x16, #0
1:
	cmp x16, x14
	b.ge .Lg_ret
	mov x17, #0
2:
	cmp x17, x13
	b.ge 7f
	ldr x2, [x15, #88]
	sub x3, x14, #1
	sub x3, x3, x16
	and x4, x2, #2
	cmp x4, #0
	csel x4, x3, x16, ne
	sub x5, x13, #1
	sub x5, x5, x17
	and x6, x2, #1
	cmp x6, #0
	csel x5, x5, x17, ne
	mul x4, x4, x13
	add x4, x4, x5
	lsl x4, x4, #2
	ldr x7, [x15, #64]
	add x7, x7, x4
	ldr w6, [x7]
	cbz x6, 6f
	ldr x3, [x15, #72]
	cmp x6, x3
	b.eq 6f
	and x4, x2, #4
	cbz x4, 3f
	mov x6, x12
3:
	and x6, x6, #0xFFFFFF
	ldr x3, [sp, #16]
	mul x4, x17, x3
	add x4, x4, x10
	mul x5, x16, x3
	add x5, x5, x11
	mov x7, #0
4:
	cmp x7, x3
	b.ge 6f
	mov x2, #0
5:
	cmp x2, x3
	b.ge 9f
	add x0, x4, x2
	add x1, x5, x7
	mov x8, #64
	cmp x0, x8
	b.hs 10f
	mov x8, #32
	cmp x1, x8
	b.hs 10f
	mov x8, #64
	mul x8, x1, x8
	add x8, x8, x0
	lsl x8, x8, #2
	adrp x9, _sign_gpix
	add x9, x9, :lo12:_sign_gpix
	str w6, [x9, x8]
	b 11f
10:
	mov x8, #1
	str x8, [x15, #48]
11:
	add x2, x2, #1
	b 5b
9:
	add x7, x7, #1
	b 4b
6:
	add x17, x17, #1
	b 2b
7:
	add x16, x16, #1
	b 1b
8:
	mov x0, #1
	str x0, [x15, #48]
	b .Lg_ret

_sign_dev_gpresent:
	stp x29, x30, [sp, #-272]!
	mov x29, sp
	adrp x15, _sign_gfx
	add x15, x15, :lo12:_sign_gfx
	ldr x0, [x15, #200]
	cmp x0, #1
	b.eq .Lgp_draw
	cmp x0, #2
	b.eq .Lgp_ret
	mov x0, #-100
	adrp x1, _sign_gfx_path
	add x1, x1, :lo12:_sign_gfx_path
	mov x2, #2
	movk x2, #8, lsl #16
	mov x3, #0
	mov x8, #56
	svc #0
	cmp x0, #0
	b.lt .Lgp_fail
	str x0, [x15, #96]
	mov x1, #0x4600
	add x2, sp, #16
	mov x8, #29
	svc #0
	cmp x0, #0
	b.lt .Lgp_fail
	ldr x0, [x15, #96]
	mov x1, #0x4602
	add x2, sp, #176
	mov x8, #29
	svc #0
	cmp x0, #0
	b.lt .Lgp_fail
	ldr w3, [sp, #40]
	cmp x3, #32
	b.eq 1f
	cmp x3, #16
	b.ne .Lgp_fail
1:
	str x3, [x15, #136]
	ldr w1, [sp, #16]
	str x1, [x15, #112]
	ldr w1, [sp, #20]
	str x1, [x15, #120]
	ldr w1, [sp, #224]
	str x1, [x15, #128]
	ldr w1, [sp, #200]
	str x1, [x15, #192]
	ldr w1, [sp, #48]
	str x1, [x15, #144]
	ldr w1, [sp, #52]
	str x1, [x15, #152]
	ldr w1, [sp, #60]
	str x1, [x15, #160]
	ldr w1, [sp, #64]
	str x1, [x15, #168]
	ldr w1, [sp, #72]
	str x1, [x15, #176]
	ldr w1, [sp, #76]
	str x1, [x15, #184]
	ldr w1, [sp, #84]
	str x1, [x15, #208]
	ldr w1, [sp, #88]
	str x1, [x15, #216]
	mov x0, #0
	ldr x1, [x15, #192]
	mov x2, #3
	mov x3, #1
	ldr x4, [x15, #96]
	mov x5, #0
	mov x8, #222
	svc #0
	mov x1, #-4096
	cmp x0, x1
	b.hi .Lgp_fail
	str x0, [x15, #104]
	ldr x1, [x15, #192]
	lsr x1, x1, #3
	mov x2, x0
2:
	cbz x1, 3f
	str xzr, [x2]
	add x2, x2, #8
	sub x1, x1, #1
	b 2b
3:
	mov x0, #1
	str x0, [x15, #200]
	b .Lgp_draw
.Lgp_fail:
	mov x0, #2
	str x0, [x15, #200]
	mov x0, #2
	adrp x1, _sign_gfx_err
	add x1, x1, :lo12:_sign_gfx_err
	mov x2, #200
	mov x8, #64
	svc #0
.Lgp_ret:
	ldp x29, x30, [sp], #272
	ret
.Lgp_draw:
	ldr x1, [x15, #112]
	mov x2, #64
	udiv x11, x1, x2
	ldr x1, [x15, #120]
	mov x2, #32
	udiv x3, x1, x2
	cmp x3, x11
	csel x11, x3, x11, lo
	cmp x11, #1
	mov x3, #1
	csel x11, x3, x11, lo
	ldr x1, [x15, #112]
	mov x2, #64
	mul x2, x2, x11
	sub x1, x1, x2
	cmp x1, #0
	csel x1, x1, xzr, gt
	lsr x9, x1, #1
	ldr x1, [x15, #120]
	mov x2, #32
	mul x2, x2, x11
	sub x1, x1, x2
	cmp x1, #0
	csel x1, x1, xzr, gt
	lsr x1, x1, #1
	str x1, [sp, #264]
	ldr x10, [x15, #136]
	lsr x10, x10, #3
	ldr x16, [x15, #128]
	ldr x17, [x15, #104]
	mov x14, #0
5:
	mov x13, #0
6:
	mov x0, #64
	mul x0, x14, x0
	add x0, x0, x13
	lsl x0, x0, #2
	adrp x1, _sign_gpix
	add x1, x1, :lo12:_sign_gpix
	ldr w0, [x1, x0]
	mov x12, #0
	lsr x1, x0, #16
	and x1, x1, #255
	ldr x2, [x15, #152]
	mov x3, #8
	sub x3, x3, x2
	lsr x1, x1, x3
	ldr x2, [x15, #144]
	lsl x1, x1, x2
	orr x12, x12, x1
	lsr x1, x0, #8
	and x1, x1, #255
	ldr x2, [x15, #168]
	mov x3, #8
	sub x3, x3, x2
	lsr x1, x1, x3
	ldr x2, [x15, #160]
	lsl x1, x1, x2
	orr x12, x12, x1
	lsr x1, x0, #0
	and x1, x1, #255
	ldr x2, [x15, #184]
	mov x3, #8
	sub x3, x3, x2
	lsr x1, x1, x3
	ldr x2, [x15, #176]
	lsl x1, x1, x2
	orr x12, x12, x1
	ldr x2, [x15, #216]
	cmp x2, #8
	b.ne 7f
	mov x1, #255
	ldr x2, [x15, #208]
	lsl x1, x1, x2
	orr x12, x12, x1
7:
	mov x7, #0
8:
	cmp x7, x11
	b.ge 14f
	ldr x1, [sp, #264]
	mul x2, x14, x11
	add x1, x1, x2
	add x1, x1, x7
	ldr x2, [x15, #120]
	cmp x1, x2
	b.hs 14f
	mul x1, x1, x16
	add x1, x1, x17
	mul x2, x13, x11
	add x2, x2, x9
	mov x3, #0
9:
	cmp x3, x11
	b.ge 13f
	add x4, x2, x3
	ldr x5, [x15, #112]
	cmp x4, x5
	b.hs 12f
	mul x4, x4, x10
	add x4, x4, x1
	cmp x10, #4
	b.ne 10f
	str w12, [x4]
	b 12f
10:
	strh w12, [x4]
12:
	add x3, x3, #1
	b 9b
13:
	add x7, x7, #1
	b 8b
14:
	add x13, x13, #1
	mov x0, #64
	cmp x13, x0
	b.lt 6b
	add x14, x14, #1
	mov x0, #32
	cmp x14, x0
	b.lt 5b
	b .Lgp_ret

// ===== 音 (0x98…) =====

_sign_dev_snd_init:
	adrp x15, _sign_snd
	add x15, x15, :lo12:_sign_snd
	ldr x2, [x15, #56]
	cbnz x2, 1f
	mov x2, #1
	str x2, [x15, #56]
	mov x2, #440
	str x2, [x15, #16]
	mov x2, #200
	str x2, [x15, #24]
	mov x2, #100
	str x2, [x15, #32]
1:
	ret

_sign_dev_snd_stop:
	stp x29, x30, [sp, #-48]!
	mov x29, sp
	adrp x15, _sign_snd
	add x15, x15, :lo12:_sign_snd
	ldr x0, [x15, #48]
	cbz x0, 1f
	str xzr, [x15, #48]
	str x0, [sp, #16]
	mov x1, #15
	mov x8, #129
	svc #0
	ldr x0, [sp, #16]
	add x1, sp, #24
	mov x2, #0
	mov x3, #0
	mov x8, #260
	svc #0
1:
	ldp x29, x30, [sp], #48
	ret

_sign_dev_snd_busy:
	stp x29, x30, [sp, #-48]!
	mov x29, sp
	adrp x15, _sign_snd
	add x15, x15, :lo12:_sign_snd
	ldr x0, [x15, #48]
	cbz x0, 2f
	add x1, sp, #16
	mov x2, #1
	mov x3, #0
	mov x8, #260
	svc #0
	cbz x0, 3f
	str xzr, [x15, #48]
2:
	mov x0, #0
	b 4f
3:
	mov x0, #1
4:
	ldp x29, x30, [sp], #48
	ret

_sign_dev_snd_start:
	stp x29, x30, [sp, #-64]!
	mov x29, sp
	str x0, [sp, #16]
	mov x0, #-100
	adrp x1, _sign_snd_path
	add x1, x1, :lo12:_sign_snd_path
	mov x2, #1
	mov x3, #0
	mov x8, #48
	svc #0
	cmp x0, #0
	b.ge 1f
	mov x0, #-19
	b 9f
1:
	bl _sign_dev_snd_stop
	mov x0, #17
	mov x1, #0
	mov x2, #0
	mov x3, #0
	mov x4, #0
	mov x8, #220
	svc #0
	cmp x0, #0
	b.lt 8f
	b.eq 5f
	adrp x15, _sign_snd
	add x15, x15, :lo12:_sign_snd
	str x0, [x15, #48]
	mov x0, #0
	b 9f
8:
	mov x0, #-5
	b 9f
5:
	mov x0, #1
	mov x1, #15
	mov x8, #167
	svc #0
	ldr x0, [sp, #16]
	mov x1, #0
	mov x2, #0
	mov x8, #24
	svc #0
	adrp x1, _sign_snd_a0
	add x1, x1, :lo12:_sign_snd_a0
	str x1, [sp, #24]
	adrp x1, _sign_snd_a1
	add x1, x1, :lo12:_sign_snd_a1
	str x1, [sp, #32]
	str xzr, [sp, #40]
	adrp x0, _sign_snd_path
	add x0, x0, :lo12:_sign_snd_path
	add x1, sp, #24
	adrp x2, _sign_envp
	add x2, x2, :lo12:_sign_envp
	ldr x2, [x2]
	mov x8, #221
	svc #0
	mov x0, #127
	mov x8, #94
	svc #0
9:
	ldp x29, x30, [sp], #64
	ret

_sign_dev_snd_go:
	stp x29, x30, [sp, #-64]!
	mov x29, sp
	adrp x15, _sign_snd
	add x15, x15, :lo12:_sign_snd
	cmp x0, #3
	b.ne 1f
	bl _sign_dev_snd_stop
	mov x0, #0
	b .Lsg_ret
1:
	cmp x0, #1
	b.eq .Lsg_play
	cmp x0, #2
	b.eq .Lsg_tone
.Lsg_einval:
	mov x0, #-22
.Lsg_ret:
	ldp x29, x30, [sp], #64
	ret
.Lsg_play:
	ldr x1, [x15, #8]
	sub x2, x1, #1
	cmp x2, #1024
	b.hs .Lsg_einval
	ldr x0, [x15]
	bl _sign_dev_spath
	cmp x0, #0
	b.lt .Lsg_ret
	mov x0, #0
	bl _sign_dev_open2
	cmp x0, #0
	b.lt .Lsg_ret
	str x0, [sp, #16]
	adrp x1, _sign_sbuf
	add x1, x1, :lo12:_sign_sbuf
	mov x2, #12
	mov x8, #63
	svc #0
	cmp x0, #12
	b.ge 2f
	mov x1, #-21
	cmp x0, x1
	b.ne 3f
	mov x0, #-2
	b 5f
3:
	mov x0, #-22
	b 5f
2:
	adrp x1, _sign_sbuf
	add x1, x1, :lo12:_sign_sbuf
	ldr w2, [x1]
	mov w3, #0x4952
	movk w3, #0x4646, lsl #16
	cmp w2, w3
	b.ne 4f
	ldr w2, [x1, #8]
	mov w3, #0x4157
	movk w3, #0x4556, lsl #16
	cmp w2, w3
	b.ne 4f
	ldr x0, [sp, #16]
	mov x1, #0
	mov x2, #2
	mov x8, #62
	svc #0
	mov x1, #0x4000000
	cmp x0, x1
	b.hi 4f
	ldr x0, [sp, #16]
	mov x1, #0
	mov x2, #0
	mov x8, #62
	svc #0
	ldr x0, [sp, #16]
	bl _sign_dev_snd_start
	b 5f
4:
	mov x0, #-22
5:
	str x0, [sp, #24]
	ldr x0, [sp, #16]
	mov x8, #57
	svc #0
	ldr x0, [sp, #24]
	b .Lsg_ret
.Lsg_tone:
	ldr x1, [x15, #16]
	sub x1, x1, #20
	mov x2, #19980
	cmp x1, x2
	b.hi .Lsg_einval
	ldr x1, [x15, #24]
	sub x1, x1, #1
	mov x2, #9999
	cmp x1, x2
	b.hi .Lsg_einval
	ldr x1, [x15, #32]
	cmp x1, #100
	b.hi .Lsg_einval
	mov x0, #0
	adrp x0, _sign_snd_a1
	add x0, x0, :lo12:_sign_snd_a1
	mov x1, #1
	mov x8, #279
	svc #0
	cmp x0, #0
	b.ge 1f
	mov x0, #-5
	b .Lsg_ret
1:
	str x0, [sp, #16]
	adrp x15, _sign_snd
	add x15, x15, :lo12:_sign_snd
	ldr x2, [x15, #24]
	mov x1, #22050
	mul x3, x1, x2
	mov x1, #1000
	udiv x3, x3, x1
	ldr x2, [x15, #32]
	mov x1, #32767
	mul x6, x1, x2
	mov x1, #100
	udiv x6, x6, x1
	mov x1, #8
	mul x6, x6, x1
	mov x1, #10
	udiv x6, x6, x1
	ldr x2, [x15, #16]
	lsl x5, x2, #32
	mov x1, #22050
	udiv x5, x5, x1
	lsl x13, x3, #1
	str x13, [sp, #32]
	adrp x9, _sign_sbuf
	add x9, x9, :lo12:_sign_sbuf
	mov x1, #0
	adrp x7, _sign_snd_hdr
	add x7, x7, :lo12:_sign_snd_hdr
1:
	ldrb w2, [x7, x1]
	strb w2, [x9, x1]
	add x1, x1, #1
	cmp x1, #44
	b.ne 1b
	add x2, x13, #36
	str w2, [x9, #4]
	str w13, [x9, #40]
	add x9, x9, #44
	adrp x7, _sign_snd_tbl
	add x7, x7, :lo12:_sign_snd_tbl
	mov x2, #0
	mov x4, #0
2:
	cmp x2, x3
	b.ge 3f
	sub x10, x3, #1
	sub x10, x10, x2
	cmp x2, x10
	csel x10, x2, x10, lt
	mov x11, #110
	cmp x10, x11
	csel x10, x10, x11, lt
	mov x11, #0x200000
	add x11, x11, x4
	lsr x11, x11, #22
	and x11, x11, #1023
	lsl x11, x11, #2
	ldr w12, [x7, x11]
	lsl x12, x12, #32
	asr x12, x12, #32
	mul x12, x12, x6
	mul x12, x12, x10
	movz x11, #0xff92
	movk x11, #0x36, lsl #16
	sdiv x12, x12, x11
	lsl x14, x2, #1
	strh w12, [x9, x14]
	add x4, x4, x5
	and x4, x4, #0xFFFFFFFF
	add x2, x2, #1
	b 2b
3:
	ldr x13, [sp, #32]
	add x13, x13, #44
	adrp x9, _sign_sbuf
	add x9, x9, :lo12:_sign_sbuf
	mov x14, #0
4:
	cmp x14, x13
	b.ge 5f
	ldr x0, [sp, #16]
	add x1, x9, x14
	sub x2, x13, x14
	mov x8, #64
	svc #0
	cmp x0, #0
	b.le 6f
	add x14, x14, x0
	b 4b
5:
	ldr x0, [sp, #16]
	mov x1, #0
	mov x2, #0
	mov x8, #62
	svc #0
	ldr x0, [sp, #16]
	bl _sign_dev_snd_start
	b 7f
6:
	mov x0, #-5
7:
	str x0, [sp, #24]
	ldr x0, [sp, #16]
	mov x8, #57
	svc #0
	ldr x0, [sp, #24]
	b .Lsg_ret

_sign_dev_snd_st:
	stp x29, x30, [sp, #-32]!
	mov x29, sp
	str x0, [sp, #16]
	str x1, [sp, #24]
	bl _sign_dev_snd_init
	ldr x0, [sp, #16]
	ldr x1, [sp, #24]
	cmp x0, #0x14
	b.ne 1f
	mov x0, x1
	bl _sign_dev_snd_go
	adrp x15, _sign_snd
	add x15, x15, :lo12:_sign_snd
	str x0, [x15, #40]
	b 9f
1:
	cmp x0, #0x10
	b.hi 9f
	and x2, x0, #3
	cbnz x2, 9f
	lsl x0, x0, #1
	str x1, [x15, x0]
9:
	ldp x29, x30, [sp], #32
	ret

_sign_dev_snd_ld:
	stp x29, x30, [sp, #-32]!
	mov x29, sp
	str x0, [sp, #16]
	bl _sign_dev_snd_init
	ldr x0, [sp, #16]
	cmp x0, #0x18
	b.ne 1f
	ldr x0, [x15, #40]
	b 9f
1:
	cmp x0, #0x1C
	b.ne 2f
	bl _sign_dev_snd_busy
	b 9f
2:
	cmp x0, #0x10
	b.hi 8f
	and x2, x0, #3
	cbnz x2, 8f
	lsl x0, x0, #1
	ldr x0, [x15, x0]
	b 9f
8:
	mov x0, #0
9:
	ldp x29, x30, [sp], #32
	ret

	.section .rodata
.Lstr0:
	.byte 9
.Lstr1:
	.byte 112, 46, 100, 98
.Lstr2:
	.byte 99, 114, 101, 97, 116, 101, 32, 116, 97, 98, 108, 101, 32, 119, 40, 105, 100, 32, 105, 110, 116, 101, 103, 101, 114, 32, 112, 114, 105, 109, 97, 114, 121, 32, 107, 101, 121, 44, 32, 115, 32, 116, 101, 120, 116, 44, 32, 110, 32, 105, 110, 116, 101, 103, 101, 114, 41
.Lstr3:
	.byte 105, 110, 115, 101, 114, 116, 32, 105, 110, 116, 111, 32, 119, 40, 115, 44, 110, 41, 32, 118, 97, 108, 117, 101, 115, 32, 40, 39, 97, 98, 99, 39, 44, 32, 52, 50, 57, 52, 57, 54, 55, 50, 57, 53, 41, 44, 32, 40, 39, 120, 121, 122, 39, 44, 32, 45, 53, 41
.Lstr4:
	.byte 105, 110, 115, 101, 114, 116, 32, 105, 110, 116, 111, 32, 119, 40, 105, 100, 41, 32, 118, 97, 108, 117, 101, 115, 32, 40, 49, 41
.Lstr5:
	.byte 46, 46, 47, 120, 46, 100, 98
.Lstr6:
	.byte 97, 116, 116, 97, 99, 104, 32, 100, 97, 116, 97, 98, 97, 115, 101, 32, 39, 121, 46, 100, 98, 39, 32, 97, 115, 32, 121
.Lstr7:
	.byte 115, 101, 108, 101, 99, 116, 32, 49, 59, 32, 115, 101, 108, 101, 99, 116, 32, 50
.Lstr8:
	.byte 115, 101, 108, 101, 99, 116, 32, 115, 44, 32, 110, 44, 32, 48, 46, 49, 44, 32, 49, 101, 49, 54, 32, 102, 114, 111, 109, 32, 119, 32, 111, 114, 100, 101, 114, 32, 98, 121, 32, 105, 100
	.section .rodata
_sign_dev_gchip:
	.byte 47, 100, 101, 118, 47, 103, 112, 105, 111, 99, 104, 105, 112, 48, 0
_sign_dev_mapmsg:
	.byte 115, 105, 103, 110, 58, 32, 99, 97, 110, 110, 111, 116, 32, 109, 97, 112, 32, 119, 111, 114, 107, 32, 109, 101, 109, 111, 114, 121, 32, 97, 116, 32, 48, 120, 49, 48, 48, 48, 48, 45, 48, 120, 57, 48, 48, 48, 48, 48, 48, 32, 40, 108, 105, 110, 107, 32, 119, 105, 116, 104, 32, 45, 45, 105, 109, 97, 103, 101, 45, 98, 97, 115, 101, 32, 97, 98, 111, 118, 101, 32, 105, 116, 59, 32, 99, 104, 101, 99, 107, 32, 118, 109, 46, 111, 118, 101, 114, 99, 111, 109, 109, 105, 116, 95, 109, 101, 109, 111, 114, 121, 32, 97, 110, 100, 32, 109, 109, 97, 112, 95, 109, 105, 110, 95, 97, 100, 100, 114, 41, 10
_sign_nlh:
	.byte 108, 111, 99, 97, 108, 104, 111, 115, 116
_sign_dns_path:
	.byte 47, 101, 116, 99, 47, 114, 101, 115, 111, 108, 118, 46, 99, 111, 110, 102, 0
_sign_dns_kw:
	.byte 110, 97, 109, 101, 115, 101, 114, 118, 101, 114
_sign_dns_hdr:
	.byte 90, 29, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0
	.section .rodata
_sign_inmap:
	.byte 0, 27, 49, 50, 51, 52, 53, 54, 55, 56, 57, 48, 45, 61, 8, 9, 113, 119, 101, 114, 116, 121, 117, 105, 111, 112, 91, 93, 13, 0, 97, 115, 100, 102, 103, 104, 106, 107, 108, 59, 39, 96, 0, 92, 122, 120, 99, 118, 98, 110, 109, 44, 46, 47, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 0, 28, 29, 0, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
	.section .rodata
_sign_snd_path:
	.byte 47, 117, 115, 114, 47, 98, 105, 110, 47, 97, 112, 108, 97, 121, 0
_sign_snd_a0:
	.byte 97, 112, 108, 97, 121, 0
_sign_snd_a1:
	.byte 45, 113, 0
_sign_snd_hdr:
	.byte 82, 73, 70, 70, 0, 0, 0, 0, 87, 65, 86, 69, 102, 109, 116, 32, 16, 0, 0, 0, 1, 0, 1, 0, 34, 86, 0, 0, 68, 172, 0, 0, 2, 0, 16, 0, 100, 97, 116, 97, 0, 0, 0, 0
	.balign 4
_sign_snd_tbl:
	.word 0, 201, 402, 603, 804, 1005, 1206, 1407, 1608, 1809, 2009, 2210, 2410, 2611, 2811, 3012
	.word 3212, 3412, 3612, 3811, 4011, 4210, 4410, 4609, 4808, 5007, 5205, 5404, 5602, 5800, 5998, 6195
	.word 6393, 6590, 6786, 6983, 7179, 7375, 7571, 7767, 7962, 8157, 8351, 8545, 8739, 8933, 9126, 9319
	.word 9512, 9704, 9896, 10087, 10278, 10469, 10659, 10849, 11039, 11228, 11417, 11605, 11793, 11980, 12167, 12353
	.word 12539, 12725, 12910, 13094, 13279, 13462, 13645, 13828, 14010, 14191, 14372, 14553, 14732, 14912, 15090, 15269
	.word 15446, 15623, 15800, 15976, 16151, 16325, 16499, 16673, 16846, 17018, 17189, 17360, 17530, 17700, 17869, 18037
	.word 18204, 18371, 18537, 18703, 18868, 19032, 19195, 19357, 19519, 19680, 19841, 20000, 20159, 20317, 20475, 20631
	.word 20787, 20942, 21096, 21250, 21403, 21554, 21705, 21856, 22005, 22154, 22301, 22448, 22594, 22739, 22884, 23027
	.word 23170, 23311, 23452, 23592, 23731, 23870, 24007, 24143, 24279, 24413, 24547, 24680, 24811, 24942, 25072, 25201
	.word 25329, 25456, 25582, 25708, 25832, 25955, 26077, 26198, 26319, 26438, 26556, 26674, 26790, 26905, 27019, 27133
	.word 27245, 27356, 27466, 27575, 27683, 27790, 27896, 28001, 28105, 28208, 28310, 28411, 28510, 28609, 28706, 28803
	.word 28898, 28992, 29085, 29177, 29268, 29358, 29447, 29534, 29621, 29706, 29791, 29874, 29956, 30037, 30117, 30195
	.word 30273, 30349, 30424, 30498, 30571, 30643, 30714, 30783, 30852, 30919, 30985, 31050, 31113, 31176, 31237, 31297
	.word 31356, 31414, 31470, 31526, 31580, 31633, 31685, 31736, 31785, 31833, 31880, 31926, 31971, 32014, 32057, 32098
	.word 32137, 32176, 32213, 32250, 32285, 32318, 32351, 32382, 32412, 32441, 32469, 32495, 32521, 32545, 32567, 32589
	.word 32609, 32628, 32646, 32663, 32678, 32692, 32705, 32717, 32728, 32737, 32745, 32752, 32757, 32761, 32765, 32766
	.word 32767, 32766, 32765, 32761, 32757, 32752, 32745, 32737, 32728, 32717, 32705, 32692, 32678, 32663, 32646, 32628
	.word 32609, 32589, 32567, 32545, 32521, 32495, 32469, 32441, 32412, 32382, 32351, 32318, 32285, 32250, 32213, 32176
	.word 32137, 32098, 32057, 32014, 31971, 31926, 31880, 31833, 31785, 31736, 31685, 31633, 31580, 31526, 31470, 31414
	.word 31356, 31297, 31237, 31176, 31113, 31050, 30985, 30919, 30852, 30783, 30714, 30643, 30571, 30498, 30424, 30349
	.word 30273, 30195, 30117, 30037, 29956, 29874, 29791, 29706, 29621, 29534, 29447, 29358, 29268, 29177, 29085, 28992
	.word 28898, 28803, 28706, 28609, 28510, 28411, 28310, 28208, 28105, 28001, 27896, 27790, 27683, 27575, 27466, 27356
	.word 27245, 27133, 27019, 26905, 26790, 26674, 26556, 26438, 26319, 26198, 26077, 25955, 25832, 25708, 25582, 25456
	.word 25329, 25201, 25072, 24942, 24811, 24680, 24547, 24413, 24279, 24143, 24007, 23870, 23731, 23592, 23452, 23311
	.word 23170, 23027, 22884, 22739, 22594, 22448, 22301, 22154, 22005, 21856, 21705, 21554, 21403, 21250, 21096, 20942
	.word 20787, 20631, 20475, 20317, 20159, 20000, 19841, 19680, 19519, 19357, 19195, 19032, 18868, 18703, 18537, 18371
	.word 18204, 18037, 17869, 17700, 17530, 17360, 17189, 17018, 16846, 16673, 16499, 16325, 16151, 15976, 15800, 15623
	.word 15446, 15269, 15090, 14912, 14732, 14553, 14372, 14191, 14010, 13828, 13645, 13462, 13279, 13094, 12910, 12725
	.word 12539, 12353, 12167, 11980, 11793, 11605, 11417, 11228, 11039, 10849, 10659, 10469, 10278, 10087, 9896, 9704
	.word 9512, 9319, 9126, 8933, 8739, 8545, 8351, 8157, 7962, 7767, 7571, 7375, 7179, 6983, 6786, 6590
	.word 6393, 6195, 5998, 5800, 5602, 5404, 5205, 5007, 4808, 4609, 4410, 4210, 4011, 3811, 3612, 3412
	.word 3212, 3012, 2811, 2611, 2410, 2210, 2009, 1809, 1608, 1407, 1206, 1005, 804, 603, 402, 201
	.word 0, 4294967095, 4294966894, 4294966693, 4294966492, 4294966291, 4294966090, 4294965889, 4294965688, 4294965487, 4294965287, 4294965086, 4294964886, 4294964685, 4294964485, 4294964284
	.word 4294964084, 4294963884, 4294963684, 4294963485, 4294963285, 4294963086, 4294962886, 4294962687, 4294962488, 4294962289, 4294962091, 4294961892, 4294961694, 4294961496, 4294961298, 4294961101
	.word 4294960903, 4294960706, 4294960510, 4294960313, 4294960117, 4294959921, 4294959725, 4294959529, 4294959334, 4294959139, 4294958945, 4294958751, 4294958557, 4294958363, 4294958170, 4294957977
	.word 4294957784, 4294957592, 4294957400, 4294957209, 4294957018, 4294956827, 4294956637, 4294956447, 4294956257, 4294956068, 4294955879, 4294955691, 4294955503, 4294955316, 4294955129, 4294954943
	.word 4294954757, 4294954571, 4294954386, 4294954202, 4294954017, 4294953834, 4294953651, 4294953468, 4294953286, 4294953105, 4294952924, 4294952743, 4294952564, 4294952384, 4294952206, 4294952027
	.word 4294951850, 4294951673, 4294951496, 4294951320, 4294951145, 4294950971, 4294950797, 4294950623, 4294950450, 4294950278, 4294950107, 4294949936, 4294949766, 4294949596, 4294949427, 4294949259
	.word 4294949092, 4294948925, 4294948759, 4294948593, 4294948428, 4294948264, 4294948101, 4294947939, 4294947777, 4294947616, 4294947455, 4294947296, 4294947137, 4294946979, 4294946821, 4294946665
	.word 4294946509, 4294946354, 4294946200, 4294946046, 4294945893, 4294945742, 4294945591, 4294945440, 4294945291, 4294945142, 4294944995, 4294944848, 4294944702, 4294944557, 4294944412, 4294944269
	.word 4294944126, 4294943985, 4294943844, 4294943704, 4294943565, 4294943426, 4294943289, 4294943153, 4294943017, 4294942883, 4294942749, 4294942616, 4294942485, 4294942354, 4294942224, 4294942095
	.word 4294941967, 4294941840, 4294941714, 4294941588, 4294941464, 4294941341, 4294941219, 4294941098, 4294940977, 4294940858, 4294940740, 4294940622, 4294940506, 4294940391, 4294940277, 4294940163
	.word 4294940051, 4294939940, 4294939830, 4294939721, 4294939613, 4294939506, 4294939400, 4294939295, 4294939191, 4294939088, 4294938986, 4294938885, 4294938786, 4294938687, 4294938590, 4294938493
	.word 4294938398, 4294938304, 4294938211, 4294938119, 4294938028, 4294937938, 4294937849, 4294937762, 4294937675, 4294937590, 4294937505, 4294937422, 4294937340, 4294937259, 4294937179, 4294937101
	.word 4294937023, 4294936947, 4294936872, 4294936798, 4294936725, 4294936653, 4294936582, 4294936513, 4294936444, 4294936377, 4294936311, 4294936246, 4294936183, 4294936120, 4294936059, 4294935999
	.word 4294935940, 4294935882, 4294935826, 4294935770, 4294935716, 4294935663, 4294935611, 4294935560, 4294935511, 4294935463, 4294935416, 4294935370, 4294935325, 4294935282, 4294935239, 4294935198
	.word 4294935159, 4294935120, 4294935083, 4294935046, 4294935011, 4294934978, 4294934945, 4294934914, 4294934884, 4294934855, 4294934827, 4294934801, 4294934775, 4294934751, 4294934729, 4294934707
	.word 4294934687, 4294934668, 4294934650, 4294934633, 4294934618, 4294934604, 4294934591, 4294934579, 4294934568, 4294934559, 4294934551, 4294934544, 4294934539, 4294934535, 4294934531, 4294934530
	.word 4294934529, 4294934530, 4294934531, 4294934535, 4294934539, 4294934544, 4294934551, 4294934559, 4294934568, 4294934579, 4294934591, 4294934604, 4294934618, 4294934633, 4294934650, 4294934668
	.word 4294934687, 4294934707, 4294934729, 4294934751, 4294934775, 4294934801, 4294934827, 4294934855, 4294934884, 4294934914, 4294934945, 4294934978, 4294935011, 4294935046, 4294935083, 4294935120
	.word 4294935159, 4294935198, 4294935239, 4294935282, 4294935325, 4294935370, 4294935416, 4294935463, 4294935511, 4294935560, 4294935611, 4294935663, 4294935716, 4294935770, 4294935826, 4294935882
	.word 4294935940, 4294935999, 4294936059, 4294936120, 4294936183, 4294936246, 4294936311, 4294936377, 4294936444, 4294936513, 4294936582, 4294936653, 4294936725, 4294936798, 4294936872, 4294936947
	.word 4294937023, 4294937101, 4294937179, 4294937259, 4294937340, 4294937422, 4294937505, 4294937590, 4294937675, 4294937762, 4294937849, 4294937938, 4294938028, 4294938119, 4294938211, 4294938304
	.word 4294938398, 4294938493, 4294938590, 4294938687, 4294938786, 4294938885, 4294938986, 4294939088, 4294939191, 4294939295, 4294939400, 4294939506, 4294939613, 4294939721, 4294939830, 4294939940
	.word 4294940051, 4294940163, 4294940277, 4294940391, 4294940506, 4294940622, 4294940740, 4294940858, 4294940977, 4294941098, 4294941219, 4294941341, 4294941464, 4294941588, 4294941714, 4294941840
	.word 4294941967, 4294942095, 4294942224, 4294942354, 4294942485, 4294942616, 4294942749, 4294942883, 4294943017, 4294943153, 4294943289, 4294943426, 4294943565, 4294943704, 4294943844, 4294943985
	.word 4294944126, 4294944269, 4294944412, 4294944557, 4294944702, 4294944848, 4294944995, 4294945142, 4294945291, 4294945440, 4294945591, 4294945742, 4294945893, 4294946046, 4294946200, 4294946354
	.word 4294946509, 4294946665, 4294946821, 4294946979, 4294947137, 4294947296, 4294947455, 4294947616, 4294947777, 4294947939, 4294948101, 4294948264, 4294948428, 4294948593, 4294948759, 4294948925
	.word 4294949092, 4294949259, 4294949427, 4294949596, 4294949766, 4294949936, 4294950107, 4294950278, 4294950450, 4294950623, 4294950797, 4294950971, 4294951145, 4294951320, 4294951496, 4294951673
	.word 4294951850, 4294952027, 4294952206, 4294952384, 4294952564, 4294952743, 4294952924, 4294953105, 4294953286, 4294953468, 4294953651, 4294953834, 4294954017, 4294954202, 4294954386, 4294954571
	.word 4294954757, 4294954943, 4294955129, 4294955316, 4294955503, 4294955691, 4294955879, 4294956068, 4294956257, 4294956447, 4294956637, 4294956827, 4294957018, 4294957209, 4294957400, 4294957592
	.word 4294957784, 4294957977, 4294958170, 4294958363, 4294958557, 4294958751, 4294958945, 4294959139, 4294959334, 4294959529, 4294959725, 4294959921, 4294960117, 4294960313, 4294960510, 4294960706
	.word 4294960903, 4294961101, 4294961298, 4294961496, 4294961694, 4294961892, 4294962091, 4294962289, 4294962488, 4294962687, 4294962886, 4294963086, 4294963285, 4294963485, 4294963684, 4294963884
	.word 4294964084, 4294964284, 4294964485, 4294964685, 4294964886, 4294965086, 4294965287, 4294965487, 4294965688, 4294965889, 4294966090, 4294966291, 4294966492, 4294966693, 4294966894, 4294967095
	.section .rodata
_sign_gfx_path:
	.byte 47, 100, 101, 118, 47, 102, 98, 48, 0
_sign_gfx_err:
	.byte 227, 130, 168, 227, 131, 169, 227, 131, 188, 58, 32, 47, 100, 101, 118, 47, 102, 98, 48, 32, 227, 129, 140, 228, 189, 191, 227, 129, 136, 227, 129, 190, 227, 129, 155, 227, 130, 147, 40, 233, 150, 139, 227, 129, 145, 227, 129, 170, 227, 129, 132, 227, 131, 187, 50, 52, 32, 227, 131, 147, 227, 131, 131, 227, 131, 136, 227, 129, 170, 227, 129, 169, 230, 156, 170, 229, 175, 190, 229, 191, 156, 227, 129, 174, 229, 189, 162, 229, 188, 143, 227, 131, 187, 230, 168, 169, 233, 153, 144, 227, 129, 175, 32, 118, 105, 100, 101, 111, 32, 227, 130, 176, 227, 131, 171, 227, 131, 188, 227, 131, 151, 41, 227, 128, 130, 231, 148, 187, 233, 157, 162, 227, 129, 184, 227, 129, 174, 229, 135, 186, 229, 138, 155, 227, 129, 175, 232, 161, 140, 227, 129, 132, 227, 129, 190, 227, 129, 155, 227, 130, 147, 40, 230, 143, 143, 231, 148, 187, 227, 129, 174, 232, 170, 173, 227, 129, 191, 230, 155, 184, 227, 129, 141, 227, 129, 175, 227, 129, 167, 227, 129, 141, 227, 129, 190, 227, 129, 153, 41, 10

	.section .bss
	.balign 8
_sign_dreg:
	.skip 20480
_sign_dwr:
	.skip 4096
_sign_drd:
	.skip 4096
_sign_gfd:
	.skip 512
_sign_gst:
	.skip 64
_sign_greq:
	.skip 592
_sign_dinit:
	.skip 8
_sign_dinit2:
	.skip 8
_sign_dalm:
	.skip 544
_sign_dt0:
	.skip 8
_sign_nbuf:
	.skip 65536
_sign_nhs:
	.skip 512
_sign_nh:
	.skip 768
_sign_dnsq:
	.skip 600
_sign_dnsr:
	.skip 600
_sign_dnsc:
	.skip 2048
_sign_sbuf:
	.skip 1048584
_sign_sfd:
	.skip 128
	.balign 8
_sign_in:
	.skip 5120
	.balign 8
_sign_snd:
	.skip 64
_sign_envp:
	.skip 8
	.balign 8
_sign_gfx:
	.skip 256
_sign_gpix:
	.skip 8192
_sign_dbreg:
	.skip 128


	.section .note.GNU-stack,"",@progbits
