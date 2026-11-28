/-
  作業領域(器)の模型(`pre_alloca` の中身)。`SirZAsm.lean` の機械 `St`・`I2` は変えず、`HSt` が `St` を包んで
  語単位のメモリ `h`(番地 / 8 が添字)・`sp`・桁上がりの旗 `c` を足す。命令 `I3` は `I2` に、メモリ・`sp` を触る命令
  (`lsl`/`lsr`/`add #n`/`sub sp`/`add xd, sp, #n`/`ldr xd,[xa,xi,lsl #3]`/`str`/`cmp`(符号なし)/`b.hs`)を足したもの。
  Mathlib なし。先に `lean -o SirZAsm.olean SirZAsm.lean` を作り、`LEAN_PATH=<olean のある場所> lean SirZHeap.lean` で検査する。

  * `copyLoop_ok`: 語の写しのループ(`pre_grow` の `l1: cmp x14,x1; b.hs l2; ldr; str; add; b l1`)。元と先が重ならず、番地が 8 の倍数・桁あふれなしなら、
    終わると先の `[i, len)` が元と同じ、ほかのメモリは変わらない(個数 `len - i` についての帰納法)。
  * `growEntry_ok`: `pre_grow`(リストの累積、食う器は 1 つ)の入口の全体。作業領域の語数 `n = ||acc|| + d × ||食う器||` から
    `sp` を `((8n+15)/16)×16 + 16` バイト下げ、先頭の 8 バイト前に `n` を置き、累積を写し、仮引数の枠を作業領域へ向ける。
    元の領域(`sp` より上)・ほかの枠・`lr`・フレームは変わらない。
  * 範囲: リスト(8 バイトの語)の累積 1 つ・食う器 1 つの形。文字列(1/4 バイト幅)・輪(食う器の和)・複数の累積、
    回るたびの末尾呼び出しの書き足し(append)、`gen_copy_result`(作業領域から置き場へ写す)は次。
-/
import SirZAsm
open SirZAsm
namespace SirZH

/-! 作業領域(器)の模型: `SirZAsm` の機械 `St`・`I2` に、語単位のメモリ `h`(番地 / 8 が添字)・`sp`・桁上がりの旗 `c` を足す。
`SirZAsm` の側は変えず、`HSt` が `St` を包む。メモリを触らない命令(`base`)は `St` の側だけを進める。 -/

structure HSt where
  s : St
  h : Nat → W                          -- 語のメモリ(添字 = 番地 / 8)
  sp : W
  c : Bool                             -- 桁上がり(`cmp` の C。`b.hs` が読む)

/-- メモリを触る命令を足した命令の集合 -/
inductive I3
  | base (i : I2)
  | lslI (d a k : Nat)                 -- lsl xd, xa, #k
  | lsrI (d a k : Nat)                 -- lsr xd, xa, #k
  | addI (d a : Nat) (n : Nat)         -- add xd, xa, #n
  | subSp (a : Nat)                    -- sub sp, sp, xa
  | spAdd (d : Nat) (n : Nat)          -- add xd, sp, #n
  | ldrX (d a i : Nat)                 -- ldr xd, [xa, xi, lsl #3]
  | strX (d a i : Nat)                 -- str xd, [xa, xi, lsl #3]
  | strN (d a : Nat) (n : Nat)         -- str xd, [xa, #-n]
  | cmpU (a b : Nat)                   -- cmp xa, xb(符号なしの比べ: C = (xa ≥ xb))
  | bhs (t : Nat)                      -- b.hs(C なら今の命令から t 先へ。前向き)

/-- 番地 `a + 8 i` の語の添字 -/
def widx (a i : W) : Nat := (a + (i <<< 3)).toNat / 8

def step3 (i : I3) (x : HSt) : HSt :=
  let s := x.s
  match i with
  | .base j => { x with s := step2 j s }
  | .lslI d a k => { x with s := { (s.set d (s.r a <<< k)) with pc := s.pc + 1 } }
  | .lsrI d a k => { x with s := { (s.set d (s.r a >>> k)) with pc := s.pc + 1 } }
  | .addI d a n => { x with s := { (s.set d (s.r a + BitVec.ofNat 64 n)) with pc := s.pc + 1 } }
  | .subSp a => { x with sp := x.sp - s.r a, s := { s with pc := s.pc + 1 } }
  | .spAdd d n => { x with s := { (s.set d (x.sp + BitVec.ofNat 64 n)) with pc := s.pc + 1 } }
  | .ldrX d a i => { x with s := { (s.set d (x.h (widx (s.r a) (s.r i)))) with pc := s.pc + 1 } }
  | .strX d a i => { x with h := fun k => if k = widx (s.r a) (s.r i) then s.r d else x.h k, s := { s with pc := s.pc + 1 } }
  | .strN d a n => { x with h := fun k => if k = (s.r a - BitVec.ofNat 64 n).toNat / 8 then s.r d else x.h k, s := { s with pc := s.pc + 1 } }
  | .cmpU a b => { x with c := decide ((s.r b).toNat ≤ (s.r a).toNat), s := { s with pc := s.pc + 1 } }
  | .bhs t => if x.c then { x with s := { s with pc := s.pc + t } } else { x with s := { s with pc := s.pc + 1 } }

inductive Steps3 (p : Array I3) : HSt → HSt → Prop
  | refl (x) : Steps3 p x x
  | step (x x2) (h : x.s.pc < p.size) : Steps3 p (step3 p[x.s.pc] x) x2 → Steps3 p x x2

theorem Steps3.go' {p : Array I3} {x x2 : HSt} (i : I3) (k : Nat) (hk : x.s.pc = k) (h : p[k]? = some i)
    (h2 : Steps3 p (step3 i x) x2) : Steps3 p x x2 := by
  have hlt : k < p.size := by
    cases Nat.lt_or_ge k p.size with
    | inl hl => exact hl
    | inr hl => simp [Array.getElem?_eq_none hl] at h
  refine Steps3.step x x2 (by omega) ?_
  have : p[x.s.pc] = i := by
    subst hk; simpa [Array.getElem?_eq_getElem hlt] using h
  rw [this]; exact h2

theorem Steps3.trans {p : Array I3} {a b c : HSt} (h1 : Steps3 p a b) (h2 : Steps3 p b c) : Steps3 p a c := by
  induction h1 with
  | refl s => exact h2
  | step s s2 h _ ih => exact Steps3.step s c h (ih h2)

/-! ### 器の写し(`pre_grow` の語ごとの写しのループ)

`x0` = 元の先頭、`x1` = 個数、`x12` = 作業領域の先頭、`x14` = 数えた個数。
```
l1: cmp x14, x1 ; b.hs l2 ; ldr x3,[x0,x14,lsl #3] ; str x3,[x12,x14,lsl #3] ; add x14,x14,#1 ; b l1
l2:
``` -/

def copyLoop : Array I3 :=
  #[I3.cmpU 14 1, I3.bhs 5, I3.ldrX 3 0 14, I3.strX 3 12 14, I3.addI 14 14 1, I3.base (I2.bk 5)]


theorem copyLoop_size : copyLoop.size = 6 := rfl

theorem widx_eq (a i : W) (n : Nat) (ha : a.toNat % 8 = 0) (hi : i.toNat = n) (hb : a.toNat + 8 * n < 2 ^ 64) :
    widx a i = a.toNat / 8 + n := by
  unfold widx
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, hi, Nat.shiftLeft_eq]
  have h1 : n * 2 ^ 3 % 2 ^ 64 = n * 8 := Nat.mod_eq_of_lt (by omega)
  rw [h1, Nat.mod_eq_of_lt (by omega)]
  omega

/-- 語の写しのループ: 元の `src`(個数 `len`)の `i` 番目から後ろを、`dst` の同じ位置へ写す。
番地は 8 の倍数・桁あふれなし・元と先は重ならない、の仮定の下で、終わると `x14 = len`、`dst` の `[i, len)` が元と同じ、他のメモリは変わらない。 -/
theorem copyLoop_ok (P : Array I3) (b : Nat) (hP : ∀ k x, copyLoop[k]? = some x → P[b + k]? = some x)
    (src dst : W) (len : Nat) (hsa : src.toNat % 8 = 0) (hda : dst.toNat % 8 = 0)
    (hs : src.toNat + 8 * len < 2 ^ 64) (hd : dst.toNat + 8 * len < 2 ^ 64)
    (hdis : dst.toNat / 8 + len ≤ src.toNat / 8 ∨ src.toNat / 8 + len ≤ dst.toNat / 8) :
    ∀ (m : Nat) (x : HSt), len - (x.s.r 14).toNat = m → x.s.pc = b → (x.s.r 14).toNat ≤ len →
      x.s.r 0 = src → x.s.r 1 = BitVec.ofNat 64 len → x.s.r 12 = dst →
      ∃ y, Steps3 P x y ∧ y.s.pc = b + 6 ∧ (y.s.r 14).toNat = len ∧
        (∀ j, (x.s.r 14).toNat ≤ j → j < len → y.h (dst.toNat / 8 + j) = x.h (src.toNat / 8 + j)) ∧
        (∀ k, (∀ j, (x.s.r 14).toNat ≤ j → j < len → k ≠ dst.toNat / 8 + j) → y.h k = x.h k) ∧
        y.sp = x.sp ∧ y.s.m = x.s.m ∧ y.s.lr = x.s.lr ∧ y.s.stk = x.s.stk ∧ y.s.r 0 = src ∧ y.s.r 1 = BitVec.ofNat 64 len ∧
        y.s.r 12 = dst := by
  intro m
  induction m with
  | zero =>
      intro x hm hpc hle h0 h1 h12
      have hi : (x.s.r 14).toNat = len := by omega
      have hl64 : len < 2 ^ 64 := by omega
      have hlt1 : (x.s.r 1).toNat = len := by rw [h1]; simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl64]
      have g1 : Steps3 P x (step3 (I3.cmpU 14 1) x) :=
        Steps3.go' (I3.cmpU 14 1) b hpc (by simpa using hP 0 _ (by simp [copyLoop])) (Steps3.refl _)
      obtain ⟨x1, hx1⟩ : ∃ x1, x1 = step3 (I3.cmpU 14 1) x := ⟨_, rfl⟩
      have c1 : x1.c = true := by simp [hx1, step3, hlt1, hi]
      have p1 : x1.s.pc = b + 1 := by simp [hx1, step3, hpc]
      have s1 : x1.s.r = x.s.r := by simp [hx1, step3]
      rw [← hx1] at g1
      obtain ⟨x2, hx2⟩ : ∃ x2, x2 = step3 (I3.bhs 5) x1 := ⟨_, rfl⟩
      have g2 : Steps3 P x1 x2 := by
        rw [hx2]; exact Steps3.go' (I3.bhs 5) (b + 1) p1 (by simpa using hP 1 _ (by simp [copyLoop])) (Steps3.refl _)
      have hx1h : x1.h = x.h := by simp [hx1, step3]
      have hx2e : x2 = { x1 with s := { x1.s with pc := x1.s.pc + 5 } } := by rw [hx2]; simp [step3, c1]
      have e1m : x1.s.m = x.s.m := by simp [hx1, step3]
      have e1l : x1.s.lr = x.s.lr := by simp [hx1, step3]
      have e1k : x1.s.stk = x.s.stk := by simp [hx1, step3]
      have e1s : x1.sp = x.sp := by simp [hx1, step3]
      refine ⟨x2, g1.trans g2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hx2e, p1]
      · simp [hx2e, s1, hi]
      · intro j hj1 hj2; omega
      · intro k _; simp [hx2e, hx1h]
      · simp [hx2e, e1s]
      · simp [hx2e, e1m]
      · simp [hx2e, e1l]
      · simp [hx2e, e1k]
      · simp [hx2e, s1, h0]
      · simp [hx2e, s1, h1]
      · simp [hx2e, s1, h12]
  | succ m ih =>
      intro x hm hpc hle h0 h1 h12
      have hl64 : len < 2 ^ 64 := by omega
      have hlt1 : (x.s.r 1).toNat = len := by rw [h1]; simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl64]
      have hilt : (x.s.r 14).toNat < len := by omega
      have g1 : Steps3 P x (step3 (I3.cmpU 14 1) x) :=
        Steps3.go' (I3.cmpU 14 1) b hpc (by simpa using hP 0 _ (by simp [copyLoop])) (Steps3.refl _)
      obtain ⟨x1, hx1⟩ : ∃ x1, x1 = step3 (I3.cmpU 14 1) x := ⟨_, rfl⟩
      have c1 : x1.c = false := by simp [hx1, step3, hlt1]; omega
      have p1 : x1.s.pc = b + 1 := by simp [hx1, step3, hpc]
      have f1r : x1.s.r = x.s.r := by simp [hx1, step3]
      have f1h : x1.h = x.h := by simp [hx1, step3]
      have f1sp : x1.sp = x.sp := by simp [hx1, step3]
      have f1m : x1.s.m = x.s.m := by simp [hx1, step3]
      have f1l : x1.s.lr = x.s.lr := by simp [hx1, step3]
      have f1k : x1.s.stk = x.s.stk := by simp [hx1, step3]
      rw [← hx1] at g1
      obtain ⟨x2, hx2⟩ : ∃ x2, x2 = step3 (I3.bhs 5) x1 := ⟨_, rfl⟩
      have g2 : Steps3 P x1 x2 := by
        rw [hx2]; exact Steps3.go' (I3.bhs 5) (b + 1) p1 (by simpa using hP 1 _ (by simp [copyLoop])) (Steps3.refl _)
      have hx2e : x2 = { x1 with s := { x1.s with pc := x1.s.pc + 1 } } := by rw [hx2]; simp [step3, c1]
      have p2 : x2.s.pc = b + 2 := by simp [hx2e, p1]
      have f2r : x2.s.r = x.s.r := by simp [hx2e, f1r]
      have f2h : x2.h = x.h := by simp [hx2e, f1h]
      have f2sp : x2.sp = x.sp := by simp [hx2e, f1sp]
      have f2m : x2.s.m = x.s.m := by simp [hx2e, f1m]
      have f2l : x2.s.lr = x.s.lr := by simp [hx2e, f1l]
      have f2k : x2.s.stk = x.s.stk := by simp [hx2e, f1k]
      obtain ⟨x3, hx3⟩ : ∃ x3, x3 = step3 (I3.ldrX 3 0 14) x2 := ⟨_, rfl⟩
      have g3 : Steps3 P x2 x3 := by
        rw [hx3]; exact Steps3.go' (I3.ldrX 3 0 14) (b + 2) p2 (by simpa using hP 2 _ (by simp [copyLoop])) (Steps3.refl _)
      have hw : widx (x.s.r 0) (x.s.r 14) = (x.s.r 0).toNat / 8 + (x.s.r 14).toNat :=
        widx_eq (x.s.r 0) (x.s.r 14) (x.s.r 14).toNat (by rw [h0]; exact hsa) rfl (by rw [h0]; omega)
      have hw' : widx (x.s.r 0) (x.s.r 14) = src.toNat / 8 + (x.s.r 14).toNat := by rw [hw, h0]
      have p3 : x3.s.pc = b + 3 := by simp [hx3, step3, p2]
      have f3h : x3.h = x.h := by simp [hx3, step3, f2h]
      have f3sp : x3.sp = x.sp := by simp [hx3, step3, f2sp]
      have f3m : x3.s.m = x.s.m := by simp [hx3, step3, f2m]
      have f3l : x3.s.lr = x.s.lr := by simp [hx3, step3, f2l]
      have f3k : x3.s.stk = x.s.stk := by simp [hx3, step3, f2k]
      have r3 : x3.s.r 3 = x.h (src.toNat / 8 + (x.s.r 14).toNat) := by
        simp [hx3, step3, St.set, f2r, hw', f2h]
      have s3 : ∀ i, i ≠ 3 → x3.s.r i = x.s.r i := by
        intro i hi; simp [hx3, step3, St.set, f2r, hi]
      obtain ⟨x4, hx4⟩ : ∃ x4, x4 = step3 (I3.strX 3 12 14) x3 := ⟨_, rfl⟩
      have g4 : Steps3 P x3 x4 := by
        rw [hx4]; exact Steps3.go' (I3.strX 3 12 14) (b + 3) p3 (by simpa using hP 3 _ (by simp [copyLoop])) (Steps3.refl _)
      have hw2 : widx (x3.s.r 12) (x3.s.r 14) = dst.toNat / 8 + (x.s.r 14).toNat := by
        rw [s3 12 (by omega), s3 14 (by omega), h12]
        have := widx_eq dst (x.s.r 14) (x.s.r 14).toNat hda rfl (by omega)
        exact this
      have f4h : ∀ k, x4.h k = if k = dst.toNat / 8 + (x.s.r 14).toNat then x.h (src.toNat / 8 + (x.s.r 14).toNat) else x.h k := by
        intro k; simp [hx4, step3, hw2, r3, f3h]
      have p4 : x4.s.pc = b + 4 := by simp [hx4, step3, p3]
      have f4r : x4.s.r = x3.s.r := by simp [hx4, step3]
      have f4sp : x4.sp = x.sp := by simp [hx4, step3, f3sp]
      have f4m : x4.s.m = x.s.m := by simp [hx4, step3, f3m]
      have f4l : x4.s.lr = x.s.lr := by simp [hx4, step3, f3l]
      have f4k : x4.s.stk = x.s.stk := by simp [hx4, step3, f3k]
      obtain ⟨x5, hx5⟩ : ∃ x5, x5 = step3 (I3.addI 14 14 1) x4 := ⟨_, rfl⟩
      have g5 : Steps3 P x4 x5 := by
        rw [hx5]; exact Steps3.go' (I3.addI 14 14 1) (b + 4) p4 (by simpa using hP 4 _ (by simp [copyLoop])) (Steps3.refl _)
      have p5 : x5.s.pc = b + 5 := by simp [hx5, step3, p4]
      have f5h : x5.h = x4.h := by simp [hx5, step3]
      have f5sp : x5.sp = x.sp := by simp [hx5, step3, f4sp]
      have f5m : x5.s.m = x.s.m := by simp [hx5, step3, f4m]
      have f5l : x5.s.lr = x.s.lr := by simp [hx5, step3, f4l]
      have f5k : x5.s.stk = x.s.stk := by simp [hx5, step3, f4k]
      have r5 : ∀ i, i ≠ 3 → i ≠ 14 → x5.s.r i = x.s.r i := by
        intro i hi3 hi
        simp [hx5, step3, St.set, f4r, hi]
        exact s3 i hi3
      have r14 : (x5.s.r 14).toNat = (x.s.r 14).toNat + 1 := by
        have e14 : x5.s.r 14 = x.s.r 14 + BitVec.ofNat 64 1 := by
          simp [hx5, step3, St.set, f4r, s3 14 (by omega)]
        rw [e14, BitVec.toNat_add]; simp
        omega
      obtain ⟨x6, hx6⟩ : ∃ x6, x6 = step3 (I3.base (I2.bk 5)) x5 := ⟨_, rfl⟩
      have g6 : Steps3 P x5 x6 := by
        rw [hx6]; exact Steps3.go' (I3.base (I2.bk 5)) (b + 5) p5 (by simpa using hP 5 _ (by simp [copyLoop])) (Steps3.refl _)
      have p6 : x6.s.pc = b := by simp [hx6, step3, step2, p5]
      have f6r : x6.s.r = x5.s.r := by simp [hx6, step3, step2]
      have f6h : x6.h = x5.h := by simp [hx6, step3]
      have f6sp : x6.sp = x.sp := by simp [hx6, step3, f5sp]
      have f6m : x6.s.m = x.s.m := by simp [hx6, step3, step2, f5m]
      have f6l : x6.s.lr = x.s.lr := by simp [hx6, step3, step2, f5l]
      have f6k : x6.s.stk = x.s.stk := by simp [hx6, step3, step2, f5k]
      have hm' : len - (x6.s.r 14).toNat = m := by rw [f6r, r14]; omega
      have hr0 : x6.s.r 0 = src := by rw [f6r, r5 0 (by omega) (by omega), h0]
      have hr1 : x6.s.r 1 = BitVec.ofNat 64 len := by rw [f6r, r5 1 (by omega) (by omega), h1]
      have hr12 : x6.s.r 12 = dst := by rw [f6r, r5 12 (by omega) (by omega), h12]
      obtain ⟨y, hy, ypc, y14, yh1, yh2, ysp, ym, ylr, ystk, y0, y1, y12⟩ :=
        ih x6 hm' p6 (by rw [f6r, r14]; omega) hr0 hr1 hr12
      have hx6h : ∀ k, x6.h k = if k = dst.toNat / 8 + (x.s.r 14).toNat then x.h (src.toNat / 8 + (x.s.r 14).toNat) else x.h k := by
        intro k; rw [f6h, f5h]; exact f4h k
      refine ⟨y, g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans hy))))), ypc, y14, ?_, ?_, by rw [ysp, f6sp], by rw [ym, f6m],
        by rw [ylr, f6l], by rw [ystk, f6k], y0, y1, y12⟩
      · intro j hj1 hj2
        by_cases hji : j = (x.s.r 14).toNat
        · subst hji
          rw [yh2 (dst.toNat / 8 + (x.s.r 14).toNat) (by intro j' hj' _; rw [f6r, r14] at hj'; omega), hx6h]
          simp
        · rw [yh1 j (by rw [f6r, r14]; omega) hj2, hx6h]
          have : src.toNat / 8 + j ≠ dst.toNat / 8 + (x.s.r 14).toNat := by omega
          simp [this]
      · intro k hk
        rw [yh2 k (by intro j hj1 hj2; exact hk j (by rw [f6r, r14] at hj1; omega) hj2), hx6h]
        have : k ≠ dst.toNat / 8 + (x.s.r 14).toNat := hk _ (Nat.le_refl _) hilt
        simp [this]


/-- 分岐のない命令の並びを順に走る -/
def runL (l : List I3) (x : HSt) : HSt := l.foldl (fun y i => step3 i y) x

def nobr : I3 → Prop
  | .bhs _ => False
  | .base (I2.base (I.b _)) => False
  | .base (I2.base (I.bc _ _)) => False
  | .base .enter => False
  | .base .leave => False
  | .base (.bl _) => False
  | .base .ret => False
  | .base (.bk _) => False
  | .base (.jmp _) => False
  | _ => True

theorem step3_pc (i : I3) (hi : nobr i) (x : HSt) : (step3 i x).s.pc = x.s.pc + 1 := by
  cases i with
  | base j =>
      cases j with
      | base i0 => cases i0 <;> simp [nobr] at hi <;> simp [step3, step2, step, St.set, St.flagsSub]
      | alloca => simp [step3, step2]
      | _ => simp [nobr] at hi
  | bhs t => simp [nobr] at hi
  | _ => simp [step3, St.set]

theorem runL_ok (P : Array I3) (b : Nat) :
    ∀ (l : List I3) (x : HSt) (j : Nat), x.s.pc = b + j → (∀ i ∈ l, nobr i) →
      (∀ k (hk : k < l.length), P[b + j + k]? = some l[k]) →
      Steps3 P x (runL l x) ∧ (runL l x).s.pc = b + j + l.length := by
  intro l
  induction l with
  | nil => intro x j hx _ _; exact ⟨Steps3.refl _, by simpa [runL] using hx⟩
  | cons i l ih =>
      intro x j hx hnb hP
      have hi : nobr i := hnb i (by simp)
      have hp : (step3 i x).s.pc = b + (j + 1) := by rw [step3_pc i hi, hx]; omega
      have g1 : Steps3 P x (step3 i x) :=
        Steps3.go' i (b + j) hx (by have := hP 0 (by simp); exact this) (Steps3.refl _)
      obtain ⟨g2, p2⟩ := ih (step3 i x) (j + 1) hp (fun i' hi' => hnb i' (by simp [hi']))
        (fun k hk => by
          have := hP (k + 1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 k] using this)
      refine ⟨?_, ?_⟩
      · simp only [runL, List.foldl_cons] at g2 ⊢; exact g1.trans g2
      · simp only [runL, List.foldl_cons] at p2 ⊢; rw [p2]; simp; omega


theorem bytes_w (nW : W) (nN : Nat) (h : nW.toNat = nN) (hlt : nN < 2 ^ 50) :
    (((((nW <<< 3) + BitVec.ofNat 64 15) >>> 4) <<< 4) + BitVec.ofNat 64 16).toNat = ((8 * nN + 15) / 16) * 16 + 16 := by
  have e1 : (nW <<< 3).toNat = 8 * nN := by
    rw [BitVec.toNat_shiftLeft, h, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have e2 : ((nW <<< 3) + BitVec.ofNat 64 15).toNat = 8 * nN + 15 := by
    rw [BitVec.toNat_add, e1]; simp; omega
  have e3 : (((nW <<< 3) + BitVec.ofNat 64 15) >>> 4).toNat = (8 * nN + 15) / 16 := by
    rw [BitVec.toNat_ushiftRight, e2, Nat.shiftRight_eq_div_pow]
  have e4 : ((((nW <<< 3) + BitVec.ofNat 64 15) >>> 4) <<< 4).toNat = ((8 * nN + 15) / 16) * 16 := by
    rw [BitVec.toNat_shiftLeft, e3, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add, e4]; simp; omega


/-- `pre_grow`(リストの累積。食う器は 1 つ)の入口: 作業領域を取り、累積を写して、仮引数をそこへ向ける。
`cp`/`cl` = 累積の先頭・長さの枠、`el` = 食う器の長さの枠、`d` = 1 回で伸びる個数 -/
def growPre (cp cl el d : Nat) : List I3 :=
  [I3.base (I2.base (I.ldr 9 cl)), I3.base (I2.base (I.ldr 10 el)), I3.base (I2.base (I.movi 11 d)),
   I3.base (I2.base (I.mul 10 10 11)), I3.base (I2.base (I.adds 9 9 10)), I3.base (I2.base (I.mov 10 9)),
   I3.lslI 9 9 3, I3.addI 9 9 15, I3.lsrI 9 9 4, I3.lslI 9 9 4, I3.addI 9 9 16, I3.subSp 9, I3.spAdd 12 16,
   I3.strN 10 12 8, I3.base (I2.base (I.ldr 0 cp)), I3.base (I2.base (I.ldr 1 cl)), I3.base (I2.base (I.movi 14 0))]

def growCode (cp cl el d : Nat) : Array I3 :=
  (growPre cp cl el d).toArray ++ copyLoop ++ #[I3.base (I2.base (I.str 12 cp))]

theorem growPre_len (cp cl el d : Nat) : (growPre cp cl el d).length = 17 := rfl

theorem growPre_nobr (cp cl el d : Nat) : ∀ i ∈ growPre cp cl el d, nobr i := by
  intro i hi
  simp [growPre] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [nobr]

theorem growA_size (cp cl el d : Nat) : (growPre cp cl el d).toArray.size = 17 := by
  simp [growPre_len]

theorem growCode_pre (cp cl el d : Nat) (k : Nat) (hk : k < 17) :
    (growCode cp cl el d)[k]? = (growPre cp cl el d)[k]? := by
  have hA := growA_size cp cl el d
  unfold growCode
  rw [Array.getElem?_append_left (by simp [hA, copyLoop_size]; omega), Array.getElem?_append_left (by omega)]
  simp

theorem growCode_loop (cp cl el d : Nat) (k : Nat) (x : I3) (h : copyLoop[k]? = some x) :
    (growCode cp cl el d)[17 + k]? = some x := by
  have hA := growA_size cp cl el d
  have hk : k < 6 := by
    cases Nat.lt_or_ge k 6 with
    | inl h' => exact h'
    | inr h' => rw [Array.getElem?_eq_none (by rw [copyLoop_size]; exact h')] at h; cases h
  unfold growCode
  rw [Array.getElem?_append_left (by simp [hA, copyLoop_size]; omega), Array.getElem?_append_right (by omega)]
  rw [hA, show 17 + k - 17 = k by omega]; exact h

theorem growCode_last (cp cl el d : Nat) : (growCode cp cl el d)[23]? = some (I3.base (I2.base (I.str 12 cp))) := by
  have hA := growA_size cp cl el d
  unfold growCode
  rw [Array.getElem?_append_right (by simp [hA, copyLoop_size])]
  simp [hA, copyLoop_size]


theorem growEntry_ok (P : Array I3) (b : Nat) (cp cl el d : Nat)
    (hP : ∀ k x, (growCode cp cl el d)[k]? = some x → P[b + k]? = some x)
    (x : HSt) (hpc : x.s.pc = b)
    (hn : (x.s.m cl).toNat + d * (x.s.m el).toNat < 2 ^ 50) (hd : d < 2 ^ 50)
    (hsa : (x.s.m cp).toNat % 8 = 0) (hsrc : x.sp.toNat ≤ (x.s.m cp).toNat)
    (hs : (x.s.m cp).toNat + 8 * (x.s.m cl).toNat < 2 ^ 64)
    (hsp : x.sp.toNat % 16 = 0) (hroom : 8 * ((x.s.m cl).toNat + d * (x.s.m el).toNat) + 32 ≤ x.sp.toNat) :
    ∃ y, Steps3 P x y ∧ y.s.pc = b + 24 ∧
      y.sp.toNat = x.sp.toNat - (((8 * ((x.s.m cl).toNat + d * (x.s.m el).toNat) + 15) / 16) * 16 + 16) ∧
      (y.s.m cp).toNat = y.sp.toNat + 16 ∧ (∀ i, i ≠ cp → y.s.m i = x.s.m i) ∧
      y.h ((y.sp.toNat + 16) / 8 - 1) = BitVec.ofNat 64 ((x.s.m cl).toNat + d * (x.s.m el).toNat) ∧
      (∀ j, j < (x.s.m cl).toNat → y.h ((y.sp.toNat + 16) / 8 + j) = x.h ((x.s.m cp).toNat / 8 + j)) ∧
      (∀ k, x.sp.toNat / 8 ≤ k → y.h k = x.h k) ∧ y.s.lr = x.s.lr ∧ y.s.stk = x.s.stk := by
  obtain ⟨nN, hnN⟩ : ∃ nN, nN = (x.s.m cl).toNat + d * (x.s.m el).toNat := ⟨_, rfl⟩
  rw [← hnN] at hn hroom ⊢
  obtain ⟨x17, hx17⟩ : ∃ x17, x17 = runL (growPre cp cl el d) x := ⟨_, rfl⟩
  obtain ⟨g1, p1⟩ := runL_ok P b (growPre cp cl el d) x 0 (by simpa using hpc) (growPre_nobr cp cl el d)
    (fun k hk => by
      have hk' : k < 17 := by simpa [growPre_len] using hk
      have := hP k ((growPre cp cl el d)[k]) (by rw [growCode_pre cp cl el d k hk']; exact List.getElem?_eq_getElem hk)
      exact this)
  rw [← hx17] at g1 p1
  simp [growPre_len] at p1
  have fr12 : x17.s.r 12 = x.sp - (((((x.s.m cl + x.s.m el * BitVec.ofInt 64 d) <<< 3) + BitVec.ofNat 64 15) >>> 4 <<< 4) + BitVec.ofNat 64 16) + BitVec.ofNat 64 16 := by
    rw [hx17]; rfl
  have fr0 : x17.s.r 0 = x.s.m cp := by rw [hx17]; rfl
  have fr1 : x17.s.r 1 = x.s.m cl := by rw [hx17]; rfl
  have fr14 : x17.s.r 14 = 0 := by rw [hx17]; rfl
  have fsp : x17.sp = x.sp - (((((x.s.m cl + x.s.m el * BitVec.ofInt 64 d) <<< 3) + BitVec.ofNat 64 15) >>> 4 <<< 4) + BitVec.ofNat 64 16) := by
    rw [hx17]; rfl
  have fm : x17.s.m = x.s.m := by rw [hx17]; rfl
  have fl : x17.s.lr = x.s.lr := by rw [hx17]; rfl
  have fk : x17.s.stk = x.s.stk := by rw [hx17]; rfl
  have fh : x17.h = fun k => if k = (x17.s.r 12 - BitVec.ofNat 64 8).toNat / 8 then (x.s.m cl + x.s.m el * BitVec.ofInt 64 d) else x.h k := by
    rw [hx17]; rfl
  have hEl : (x.s.m el * BitVec.ofInt 64 d).toNat = d * (x.s.m el).toNat := by
    have : BitVec.ofInt 64 (d : Int) = BitVec.ofNat 64 d := BitVec.ofInt_natCast ..
    have hd64 : d % 2 ^ 64 = d := Nat.mod_eq_of_lt (by omega)
    have hlt : d * (x.s.m el).toNat < 2 ^ 64 := by omega
    rw [this, BitVec.toNat_mul, BitVec.toNat_ofNat, hd64, Nat.mul_comm]
    exact Nat.mod_eq_of_lt hlt
  have hnW : (x.s.m cl + x.s.m el * BitVec.ofInt 64 d).toNat = nN := by
    rw [BitVec.toNat_add, hEl, hnN]; exact Nat.mod_eq_of_lt (by omega)
  have hB := bytes_w (x.s.m cl + x.s.m el * BitVec.ofInt 64 d) nN hnW hn
  obtain ⟨Bw, hBw⟩ : ∃ Bw : W, Bw = ((((x.s.m cl + x.s.m el * BitVec.ofInt 64 d) <<< 3) + BitVec.ofNat 64 15) >>> 4 <<< 4) + BitVec.ofNat 64 16 := ⟨_, rfl⟩
  rw [← hBw] at fsp fr12 hB
  have hBn : Bw.toNat = (8 * nN + 15) / 16 * 16 + 16 := hB
  have hspN : x17.sp.toNat = x.sp.toNat - Bw.toNat := by
    rw [fsp, BitVec.toNat_sub]; omega
  have hdst : (x17.s.r 12).toNat = x.sp.toNat - Bw.toNat + 16 := by
    rw [fr12, BitVec.toNat_add, BitVec.toNat_sub]
    simp
    omega
  have hlen : (x.s.m cl).toNat ≤ nN := by omega
  have hsrcW : x.s.m cp = x.s.m cp := rfl
  obtain ⟨y, gy, ypc, y14, yh1, yh2, ysp, ym, ylr, ystk, y0, y1, y12⟩ :=
    copyLoop_ok P (b + 17) (fun k x' hk => by
        have := hP (17 + k) x' (growCode_loop cp cl el d k x' hk)
        rw [← Nat.add_assoc] at this; exact this)
      (x.s.m cp) (x17.s.r 12) (x.s.m cl).toNat hsa (by rw [hdst]; omega) hs (by rw [hdst]; omega)
      (Or.inl (by rw [hdst]; omega)) _ x17 rfl (by rw [p1]) (by rw [fr14]; simp) fr0
      (by rw [fr1]; simp) rfl
  have g2 : Steps3 P y (step3 (I3.base (I2.base (I.str 12 cp))) y) :=
    Steps3.go' _ (b + 23) (by rw [ypc]) (by have := hP 23 _ (growCode_last cp cl el d); exact this) (Steps3.refl _)
  obtain ⟨Y, hY⟩ : ∃ Y, Y = step3 (I3.base (I2.base (I.str 12 cp))) y := ⟨_, rfl⟩
  rw [← hY] at g2
  have Yh : Y.h = y.h := by rw [hY]; rfl
  have Ysp : Y.sp = y.sp := by rw [hY]; rfl
  have Ym : ∀ i, Y.s.m i = if i = cp then y.s.r 12 else y.s.m i := by intro i; rw [hY]; rfl
  have Ylr : Y.s.lr = y.s.lr := by rw [hY]; rfl
  have Ystk : Y.s.stk = y.s.stk := by rw [hY]; rfl
  have Ypc : Y.s.pc = b + 24 := by rw [hY]; simp [step3, step2, step, ypc]
  have hd12 : (y.s.r 12).toNat = x.sp.toNat - Bw.toNat + 16 := by rw [y12, hdst]
  have hysp : y.sp.toNat = x.sp.toNat - Bw.toNat := by rw [ysp, hspN]
  have hnWw : x.s.m cl + x.s.m el * BitVec.ofInt 64 d = BitVec.ofNat 64 nN := by
    apply BitVec.eq_of_toNat_eq; rw [hnW]; simp; omega
  have hd8 : (x17.s.r 12 - BitVec.ofNat 64 8).toNat = x.sp.toNat - Bw.toNat + 8 := by
    rw [BitVec.toNat_sub, hdst]; simp; omega
  have hx17h : ∀ k, x17.h k = if k = (x.sp.toNat - Bw.toNat + 8) / 8 then BitVec.ofNat 64 nN else x.h k := by
    intro k; rw [fh]; simp only [hd8, hnWw]
  refine ⟨Y, g1.trans (gy.trans g2), Ypc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Ysp, hysp, hBn]
  · rw [Ym, if_pos rfl, Ysp, hd12, hysp]
  · intro i hi; rw [Ym, if_neg hi, ym, fm]
  · rw [Yh, Ysp, hysp]
    have hk : (x.sp.toNat - Bw.toNat + 16) / 8 - 1 = (x.sp.toNat - Bw.toNat + 8) / 8 := by omega
    rw [hk, yh2 _ (by intro j hj1 hj2; omega), hx17h]; simp
  · intro j hj
    rw [Yh, Ysp, hysp]
    have := yh1 j (by rw [fr14]; simp) hj
    rw [hdst] at this
    rw [this, hx17h]
    have hne : (x.s.m cp).toNat / 8 + j ≠ (x.sp.toNat - Bw.toNat + 8) / 8 := by omega
    rw [if_neg hne]
  · intro k hk
    rw [Yh, yh2 k (by intro j hj1 hj2; rw [hdst]; omega), hx17h]
    have hne : k ≠ (x.sp.toNat - Bw.toNat + 8) / 8 := by omega
    rw [if_neg hne]
  · rw [Ylr, ylr, fl]
  · rw [Ystk, ystk, fk]

#print axioms copyLoop_ok
#print axioms growEntry_ok

end SirZH
