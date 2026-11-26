// Int の List の NEON 化を測る手書きの AArch64(Linux, 静的)。
// 溢れは `!_` = INT64_MIN(x13 に持つ)。スカラー版は溢れを adds + csel で niche にする(`!_ + x = x` の伝わりの比べは省いた = スカラーに有利な見積もり)。
// NEON 版は 2 レーンずつ計算し、溢れを粘着ビットで検出し、1 つでも溢れたら全部をスカラー版でやり直す(実装ならブロックごと)。
// MODE 0 = 溢れなしのデータで時間を測る / MODE 1 = 溢れ・niche ちょうど・境の値を含むデータで、NEON 版がスカラー版と同じ答えか確かめる。
	.equ N, 1048576
	.equ REPS, 200
	.text
	.global _start

// ---------- データの用意 ----------
init:
	adrp x1, arr
	add x1, x1, :lo12:arr
	mov x9, #0
	mov x11, #2001
	mov x14, #7919
1:	mul x10, x9, x14
	udiv x12, x10, x11
	msub x10, x12, x11, x10
	sub x10, x10, #1000
.if MODE == 1
	// 溢れのある値を点々と置く
	and x15, x9, #0xFFF
	cmp x15, #5
	b.ne 2f
	movz x10, #0x7FFF, lsl #48
	movk x10, #0xFFFF, lsl #32
	movk x10, #0xFFFF, lsl #16
	movk x10, #0xFFFF           // INT64_MAX(x + x が溢れる)
2:	cmp x15, #77
	b.ne 3f
	movz x10, #0xC000, lsl #48  // -2^62(x + x = INT64_MIN ちょうど = niche)
3:	cmp x15, #900
	b.ne 4f
	movz x10, #0x8000, lsl #48
	add x10, x10, #1            // -INT64_MAX(x + x が溢れる)
4:
.endif
	str x10, [x1, x9, lsl #3]
	add x9, x9, #1
	movz x12, #0x10, lsl #16    // N = 0x100000
	cmp x9, x12
	b.lo 1b
	ret

// ---------- スカラー: out[i] = (x + x) + 1(各段で溢れたら niche) ----------
scalar_map:
	adrp x1, arr
	add x1, x1, :lo12:arr
	adrp x2, out
	add x2, x2, :lo12:out
	movz x13, #0x8000, lsl #48
	movz x3, #0x10, lsl #16
1:	ldr x4, [x1], #8
	adds x5, x4, x4
	csel x5, x13, x5, vs
	adds x6, x5, #1
	csel x6, x13, x6, vs
	str x6, [x2], #8
	subs x3, x3, #1
	b.ne 1b
	ret

// ---------- NEON: 2 レーン × 2 本ずつ。溢れの検出は粘着ビット ----------
neon_map:
	stp x29, x30, [sp, #-16]!
	adrp x1, arr
	add x1, x1, :lo12:arr
	adrp x2, out
	add x2, x2, :lo12:out
	movz x13, #0x8000, lsl #48
	dup v5.2d, x13
	mov x7, #1
	dup v6.2d, x7
	movi v7.16b, #0
	movz x3, #0x4, lsl #16       // N / 4 = 0x40000
1:	ldp q0, q1, [x1], #32
	add v2.2d, v0.2d, v0.2d
	add v3.2d, v1.2d, v1.2d
	eor v16.16b, v2.16b, v0.16b  // x + x が溢れたら符号が変わる
	eor v17.16b, v3.16b, v1.16b
	orr v7.16b, v7.16b, v16.16b
	orr v7.16b, v7.16b, v17.16b
	cmeq v18.2d, v2.2d, v5.2d    // 途中の値が niche なら `!_ + 1 = 1` の規則が要る → やり直し
	cmeq v19.2d, v3.2d, v5.2d
	orr v7.16b, v7.16b, v18.16b
	orr v7.16b, v7.16b, v19.16b
	add v4.2d, v2.2d, v6.2d
	add v20.2d, v3.2d, v6.2d
	bic v16.16b, v4.16b, v2.16b  // + 1 の溢れ: 結果が負で元が 0 以上
	bic v17.16b, v20.16b, v3.16b
	orr v7.16b, v7.16b, v16.16b
	orr v7.16b, v7.16b, v17.16b
	stp q4, q20, [x2], #32
	subs x3, x3, #1
	b.ne 1b
	umov x8, v7.d[0]
	umov x9, v7.d[1]
	orr x8, x8, x9
	tbz x8, #63, 2f
	bl scalar_map                // 溢れがあった: 全部をスカラー版でやり直す
2:	ldp x29, x30, [sp], #16
	ret

// ---------- スカラー: 畳み sum(arr)(溢れたら niche。x0 = 答え) ----------
scalar_fold:
	adrp x1, arr
	add x1, x1, :lo12:arr
	movz x13, #0x8000, lsl #48
	mov x4, #0
	movz x3, #0x10, lsl #16
1:	ldr x5, [x1], #8
	adds x6, x4, x5
	csel x4, x13, x6, vs
	subs x3, x3, #1
	b.ne 1b
	mov x0, x4
	ret

// ---------- NEON: 4 本の部分和(2 レーン × 2 本 × 2)。溢れは粘着ビット。部分和の最後の足し算も adds で見る ----------
neon_fold:
	stp x29, x30, [sp, #-16]!
	adrp x1, arr
	add x1, x1, :lo12:arr
	movi v0.16b, #0
	movi v1.16b, #0
	movi v7.16b, #0
	movz x3, #0x4, lsl #16
1:	ldp q2, q3, [x1], #32
	add v4.2d, v0.2d, v2.2d
	add v20.2d, v1.2d, v3.2d
	eor v16.16b, v4.16b, v0.16b
	eor v17.16b, v4.16b, v2.16b
	and v16.16b, v16.16b, v17.16b
	eor v18.16b, v20.16b, v1.16b
	eor v19.16b, v20.16b, v3.16b
	and v18.16b, v18.16b, v19.16b
	orr v7.16b, v7.16b, v16.16b
	orr v7.16b, v7.16b, v18.16b
	mov v0.16b, v4.16b
	mov v1.16b, v20.16b
	subs x3, x3, #1
	b.ne 1b
	umov x8, v7.d[0]
	umov x9, v7.d[1]
	orr x8, x8, x9
	tbnz x8, #63, 3f
	umov x4, v0.d[0]
	umov x5, v0.d[1]
	umov x6, v1.d[0]
	umov x7, v1.d[1]
	adds x4, x4, x5
	b.vs 3f
	adds x6, x6, x7
	b.vs 3f
	adds x0, x4, x6
	b.vs 3f
	movz x13, #0x8000, lsl #48
	cmp x0, x13
	b.eq 3f
	b 2f
3:	bl scalar_fold                // 溢れ(か部分和の途中の溢れ): スカラー版でやり直す
2:	ldp x29, x30, [sp], #16
	ret

// ---------- 時計・印字 ----------
now_ns:                          // x0 = CLOCK_MONOTONIC のナノ秒
	sub sp, sp, #16
	mov x0, #1
	mov x1, sp
	mov x8, #113
	svc #0
	ldp x2, x3, [sp]
	add sp, sp, #16
	movz x4, #0xCA00
	movk x4, #0x3B9A, lsl #16
	madd x0, x2, x4, x3
	ret

// x0 = 符号つき整数 → 標準出力へ 10 進(改行なし)
put_int:
	sub sp, sp, #48
	mov x9, x0
	add x10, sp, #40
	mov x11, #0                  // 負か
	cmp x9, #0
	b.ge 1f
	mov x11, #1
	neg x9, x9                   // INT64_MIN は 2^63 の符号なしとして読む(下の udiv は符号なし)
1:	mov x12, #10
2:	udiv x13, x9, x12
	msub x14, x13, x12, x9
	add x14, x14, #48
	sub x10, x10, #1
	strb w14, [x10]
	mov x9, x13
	cbnz x9, 2b
	cbz x11, 3f
	sub x10, x10, #1
	mov w14, #45
	strb w14, [x10]
3:	add x2, sp, #40
	sub x2, x2, x10
	mov x1, x10
	mov x0, #1
	mov x8, #64
	svc #0
	add sp, sp, #48
	ret
put_ch:                          // w0 = 文字
	sub sp, sp, #16
	strb w0, [sp]
	mov x0, #1
	mov x1, sp
	mov x2, #1
	mov x8, #64
	svc #0
	add sp, sp, #16
	ret
put_str:                         // x0 = 先頭、x1 = 長さ
	mov x2, x1
	mov x1, x0
	mov x0, #1
	mov x8, #64
	svc #0
	ret

// 出力の和(確かめ用の指紋。niche はそのまま足す)
out_sum:
	adrp x1, out
	add x1, x1, :lo12:out
	mov x0, #0
	movz x3, #0x10, lsl #16
1:	ldr x4, [x1], #8
	add x0, x0, x4
	subs x3, x3, #1
	b.ne 1b
	ret

// 1 つの核を REPS 回走らせて ms と答えを出す。x19 = 核、x20 = 名前の先頭、x21 = 名前の長さ、x22 = 1 なら畳み(x0 が答え)
run_kernel:
	stp x29, x30, [sp, #-16]!
	stp x23, x24, [sp, #-16]!
	bl now_ns
	mov x23, x0
	mov x24, #REPS
1:	blr x19
	subs x24, x24, #1
	b.ne 1b
	mov x25, x0                  // 畳みの答え
	bl now_ns
	sub x23, x0, x23
	mov x0, x20
	mov x1, x21
	bl put_str
	mov w0, #32
	bl put_ch
	movz x9, #0x4240
	movk x9, #0xF, lsl #16
	udiv x0, x23, x9
	bl put_int
	mov w0, #32
	bl put_ch
	cbz x22, 2f
	mov x0, x25
	b 3f
2:	bl out_sum
3:	bl put_int
	mov w0, #10
	bl put_ch
	ldp x23, x24, [sp], #16
	ldp x29, x30, [sp], #16
	ret

_start:
	bl init
	adrp x19, scalar_map
	add x19, x19, :lo12:scalar_map
	adrp x20, n1
	add x20, x20, :lo12:n1
	mov x21, #10
	mov x22, #0
	bl run_kernel
	adrp x19, neon_map
	add x19, x19, :lo12:neon_map
	adrp x20, n2
	add x20, x20, :lo12:n2
	mov x21, #8
	mov x22, #0
	bl run_kernel
	adrp x19, scalar_fold
	add x19, x19, :lo12:scalar_fold
	adrp x20, n3
	add x20, x20, :lo12:n3
	mov x21, #11
	mov x22, #1
	bl run_kernel
	adrp x19, neon_fold
	add x19, x19, :lo12:neon_fold
	adrp x20, n4
	add x20, x20, :lo12:n4
	mov x21, #9
	mov x22, #1
	bl run_kernel
	mov x0, #0
	mov x8, #94
	svc #0

	.section .rodata
n1:	.ascii "scalar_map"
n2:	.ascii "neon_map"
n3:	.ascii "scalar_fold"
n4:	.ascii "neon_fold"
	.section .bss
	.balign 16
arr:	.skip 8388608
out:	.skip 8388608
