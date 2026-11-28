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
  * `fcodeH_ok_at`(`fcodeA` との接続): 入口の `alloca` を `growCode`(24 命令)に置き換えた関数 `fcodeH`(I3 の列: `enter`・仮引数の `str`・
    `growCode`・`b 本体`・`.rec` の入口・本体 `B`・`leave`・`ret`)の契約。本体 `B` は `I2` の機械の証明(`SirZAsm` の `*_ok`)をそのまま使う
    (`lift2`: `growCode` の領域を `jmp 自分` で埋めた `I2` の写し `Q`(`shadowQ`)での実行を `Steps3` へ持ち上げる)。結果・枠・`lr`・フレームは
    `fcodeA_ok_at` と同じで、`sp` が `((8n+15)/16)×16+16` 下がる。`leave` のあとの `mov sp, x29` はこの模型の外。
  * `append_ok`・`append_inv`・`append_rounds`(ループの中の append、`commit_grow`): I3 に `ldr xd,[xa,#-n]`・`str xd,[xa,#n]`・`add xd,xa,xb`・
    `cmp`(`b.hi` 用)・`b.hi` を足し、累積(リスト)の末尾へ `k` 個の要素を書く 1 回ぶん(`t1 = ptr`・`t2 = len + k` の setup、
    入る個数の検査、末尾へ書き、仮引数 `ps`・`pl` の更新)を証明した。入らなければ溢れの行き先へ(`h`・`sp`・`lr`・フレームは元のまま)、
    入れば語 `ptr/8 + len + i` に要素が書かれ `len` が `len + k` に(`AccInv`)。`append_rounds` は、各回の要素の評価(`refill`)を挟んだ `r` 回で、
    器の内容が `L ++ (各回の要素)` になることを帰納法で示す。
  * 文字列と輪(`copyLoopS_ok`・`growTailS_ok`・`growTailL_ok`・`sumPre_ok`・`ringEntryL_ok`・`ringEntryS_ok`): `HSt` にバイト単位の領域 `hb` を足し、
    `ldrS`/`strS`(ascii 1 バイト・utf32 4 バイト)を入れた。文字列の写しのループ(`pre_grow` の `ldrb/strb`・`ldr w/str w, lsl #2`)は、
    元と先が重ならなければ先の `[0, 長さ×幅)` バイトが元と同じ(幅 `w = 2^sh ≤ 4`)。作業領域を取る後ろ半分は `x9 = n`(要素数)から
    `((n·w+15)/16)×16+16` バイトを取り、輪では `n = ||acc|| + d × Σ(食う器の長さ)` を `x9` に足し上げる前半(`sumPre_ok`)をつける
    (食う器が 1 つなら `growPre` の前半と同じ)。リストの輪 `ringEntryL_ok`、文字列の輪 `ringEntryS_ok`。
  * 範囲: 累積 1 つ。文字列の `commit_grow`(U+0000 を飛ばす append)、複数の累積、`ringcall`(`.rec` を通る関数をまたいだ累積)、
    `gen_copy_result`(作業領域から置き場へ写す)は次。
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
  hb : Nat → BitVec 8                  -- 文字列の領域(バイト単位。添字 = 番地)。リストの語のメモリ `h` とは別の領域として扱う

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
  | ldrN (d a : Nat) (n : Nat)         -- ldr xd, [xa, #-n]
  | strP (d a : Nat) (n : Nat)         -- str xd, [xa, #n]
  | addR (d a b : Nat)                 -- add xd, xa, xb
  | cmpH (a b : Nat)                   -- cmp xa, xb(続く `b.hi` が読む: 旗は「xa > xb(符号なし)」)
  | bhi (t : Nat)                      -- b.hi(旗なら今の命令から t 先へ。前向き)
  | ldrS (sh d a i : Nat)              -- ascii(sh=0): ldrb wd,[xa,xi] / utf32(sh=2): ldr wd,[xa,xi,lsl #2]
  | strS (sh d a i : Nat)              -- ascii: strb wd,[xa,xi] / utf32: str wd,[xa,xi,lsl #2]
  | strC (sh d a : Nat)                -- ascii: strb wd,[xa] / utf32: str wd,[xa]
  | addL (d a b sh : Nat)              -- add xd, xa, xb, lsl #sh
  | cbzI (a t : Nat)                   -- cbz xa, 今の命令から t 先(前向き)

/-- 番地 `a + 8 i` の語の添字 -/
def widx (a i : W) : Nat := (a + (i <<< 3)).toNat / 8

/-- `p` から `w` バイトを小さい位から読んだ数(リトルエンディアン) -/
def rdb (hb : Nat → BitVec 8) (p : Nat) : Nat → Nat
  | 0 => 0
  | w + 1 => (hb p).toNat + 256 * rdb hb (p + 1) w

/-- `p` から `w` バイトに `v` の下位バイトを書く -/
def wrb (hb : Nat → BitVec 8) (p w v : Nat) : Nat → BitVec 8 :=
  fun k => if p ≤ k ∧ k < p + w then BitVec.ofNat 8 (v / 256 ^ (k - p)) else hb k

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
  | .ldrN d a n => { x with s := { (s.set d (x.h ((s.r a - BitVec.ofNat 64 n).toNat / 8))) with pc := s.pc + 1 } }
  | .strP d a n => { x with h := fun k => if k = (s.r a + BitVec.ofNat 64 n).toNat / 8 then s.r d else x.h k, s := { s with pc := s.pc + 1 } }
  | .addR d a b => { x with s := { (s.set d (s.r a + s.r b)) with pc := s.pc + 1 } }
  | .cmpH a b => { x with c := decide ((s.r b).toNat < (s.r a).toNat), s := { s with pc := s.pc + 1 } }
  | .bhi t => if x.c then { x with s := { s with pc := s.pc + t } } else { x with s := { s with pc := s.pc + 1 } }
  | .ldrS sh d a i => { x with s := { (s.set d (BitVec.ofNat 64 (rdb x.hb (s.r a + (s.r i <<< sh)).toNat (2 ^ sh)))) with pc := s.pc + 1 } }
  | .strS sh d a i => { x with hb := wrb x.hb (s.r a + (s.r i <<< sh)).toNat (2 ^ sh) (s.r d).toNat, s := { s with pc := s.pc + 1 } }
  | .strC sh d a => { x with hb := wrb x.hb (s.r a).toNat (2 ^ sh) (s.r d).toNat, s := { s with pc := s.pc + 1 } }
  | .addL d a b sh => { x with s := { (s.set d (s.r a + (s.r b <<< sh))) with pc := s.pc + 1 } }
  | .cbzI a t => if s.r a = 0 then { x with s := { s with pc := s.pc + t } } else { x with s := { s with pc := s.pc + 1 } }
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
  | .bhi _ => False
  | .cbzI _ _ => False
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
  | bhi t => simp [nobr] at hi
  | cbzI a t => simp [nobr] at hi
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


/-! ### `fcodeA` との接続: 作業領域を取る関数の全体(I3)

`fcodeA` では `alloca` が見える状態を変えなかった。ここでは、入口の `alloca` を `growCode`(24 命令)に置き換えた
関数 `fcodeH` を I3 の列として組み、`growEntry_ok` と、本体 `B`(`I2` の列。`SirZAsm` の証明がそのまま使える)をつなぐ。
本体は `I2` の機械で動くので、I3 の列 `P` の `I2.base` でない位置(`growCode` の領域)には `jmp 自分` を置いた `I2` の写し `Q` を使い、
`lift2` で `Steps2 Q` の実行を `Steps3 P` の実行へ持ち上げる(`jmp 自分` は動けないので、領域の外で終わる実行はそこを通らない)。 -/

/-- 領域 `[g0, g1)` は I3 の命令(`jmp 自分` で埋めた写し)、それ以外は `I2.base` -/
theorem stuck2 (Q : Array I2) (g0 g1 : Nat) (hfill : ∀ k, g0 ≤ k → k < g1 → Q[k]? = some (I2.jmp k)) :
    ∀ (s s' : St), Steps2 Q s s' → g0 ≤ s.pc → s.pc < g1 → g0 ≤ s'.pc ∧ s'.pc < g1 := by
  intro s s' h
  induction h with
  | refl s => intro h1 h2; exact ⟨h1, h2⟩
  | step s s2 hlt hrest ih =>
      intro h1 h2
      have hk := hfill s.pc h1 h2
      have hq : Q[s.pc] = I2.jmp s.pc := by
        simpa [Array.getElem?_eq_getElem hlt] using hk
      rw [hq] at ih
      exact ih (by simp [step2]; omega) (by simp [step2]; omega)

theorem lift2 (P : Array I3) (Q : Array I2) (g0 g1 : Nat)
    (hfill : ∀ k, g0 ≤ k → k < g1 → Q[k]? = some (I2.jmp k))
    (hQ : ∀ k x, Q[k]? = some x → (g0 ≤ k ∧ k < g1) ∨ P[k]? = some (I3.base x)) :
    ∀ (s s' : St), Steps2 Q s s' → (s'.pc < g0 ∨ g1 ≤ s'.pc) → ∀ (h : Nat → W) (sp : W) (c : Bool) (hb : Nat → BitVec 8),
      Steps3 P ⟨s, h, sp, c, hb⟩ ⟨s', h, sp, c, hb⟩ := by
  intro s s' hs
  induction hs with
  | refl s => intro _ h sp c hb; exact Steps3.refl _
  | step s s2 hlt hrest ih =>
      intro hend h sp c hb
      have hout : s.pc < g0 ∨ g1 ≤ s.pc := by
        by_cases hin : g0 ≤ s.pc ∧ s.pc < g1
        · exfalso
          have hq : Q[s.pc] = I2.jmp s.pc := by
            simpa [Array.getElem?_eq_getElem hlt] using hfill s.pc hin.1 hin.2
          rw [hq] at hrest
          have := stuck2 Q g0 g1 hfill _ _ hrest (by simp [step2]; omega) (by simp [step2]; omega)
          omega
        · omega
      have hP := hQ s.pc Q[s.pc] (by simp [Array.getElem?_eq_getElem hlt])
      have hP' : P[s.pc]? = some (I3.base Q[s.pc]) := by
        rcases hP with hP | hP
        · omega
        · exact hP
      refine Steps3.go' (I3.base Q[s.pc]) s.pc rfl hP' ?_
      exact ih hend h sp c hb

/-- `pstore`: 仮引数をレジスタから枠へ(I3 の列の `I2.base (I.str k k)` の並び) -/
theorem pstore3_ok (P : Array I3) (b : Nat) :
    ∀ (n : Nat), (∀ i, i < n → P[b + i]? = some (I3.base (I2.base (I.str i i)))) →
    ∀ (x : HSt), x.s.pc = b →
      ∃ y : HSt, Steps3 P x y ∧ y.s.pc = b + n ∧ y.h = x.h ∧ y.sp = x.sp ∧ y.s.r = x.s.r ∧
        (∀ k, k < n → y.s.m k = x.s.r k) ∧ (∀ j, n ≤ j → y.s.m j = x.s.m j) ∧
        y.s.lr = x.s.lr ∧ y.s.stk = x.s.stk := by
  intro n
  induction n with
  | zero => intro _ x hx; exact ⟨x, Steps3.refl _, by simp [hx], rfl, rfl, rfl, by simp, by simp, rfl, rfl⟩
  | succ n ih =>
      intro hP x hx
      obtain ⟨y, hy, p1, h1, sp1, r1, m1, o1, l1, k1⟩ := ih (fun i hi => hP i (by omega)) x hx
      have g : Steps3 P y (step3 (I3.base (I2.base (I.str n n))) y) :=
        Steps3.go' _ (b + n) (by rw [p1]) (hP n (by omega)) (Steps3.refl _)
      refine ⟨_, hy.trans g, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [step3, step2, step, p1]; omega
      · simp [step3, step2, step, h1]
      · simp [step3, step2, step, sp1]
      · simp [step3, step2, step, r1]
      · intro k hk
        by_cases hkn : k = n
        · subst hkn; simp [step3, step2, step, r1]
        · simp [step3, step2, step, hkn]; rw [m1 k (by omega)]
      · intro j hj
        have : j ≠ n := by omega
        simp [step3, step2, step, this]; exact o1 j (by omega)
      · simp [step3, step2, step, l1]
      · simp [step3, step2, step, k1]

theorem arr_left {α : Type} (A B : Array α) (k : Nat) (h : k < A.size) : (A ++ B)[k]? = A[k]? :=
  Array.getElem?_append_left h

theorem arr_right {α : Type} (A B : Array α) (k : Nat) : (A ++ B)[A.size + k]? = B[k]? := by
  rw [Array.getElem?_append_right (by omega)]; simp

def fcodeHE (n : Nat) : Array I3 := (#[I2.enter] ++ (pstore n).map I2.base).map I3.base

def fcodeHT (n : Nat) (B : Array I2) : Array I3 := (recEntry n ++ B ++ #[I2.leave, I2.ret]).map I3.base

theorem fcodeHE_size (n : Nat) : (fcodeHE n).size = 1 + n := by
  simp [fcodeHE, pstore_size] <;> omega

theorem fcodeHT_size (n : Nat) (B : Array I2) : (fcodeHT n B).size = (1 + n) + B.size + 2 := by
  simp [fcodeHT, recEntry_size] <;> omega

/-- 作業領域を取る関数(`pre_alloca`、I3): `enter`・仮引数の `str`・`growCode`・`b 本体`・`.rec` の入口・本体 `B`・`leave`・`ret`。
`a` は先頭の絶対位置。本体は位置 `a + 2n + 27`。 -/
def fcodeH (a n cp cl el d : Nat) (B : Array I2) : Array I3 :=
  fcodeHE n ++ growCode cp cl el d ++ #[I3.base (I2.jmp (a + 2 * n + 27))] ++ fcodeHT n B

theorem growCode_size24 (cp cl el d : Nat) : (growCode cp cl el d).size = 24 := by
  simp [growCode, copyLoop_size, growPre_len]

theorem fcodeH_E (a n cp cl el d : Nat) (B : Array I2) (k : Nat) (h : k < 1 + n) :
    (fcodeH a n cp cl el d B)[k]? = (fcodeHE n)[k]? := by
  have hs := growCode_size24 cp cl el d
  unfold fcodeH
  rw [arr_left _ _ _ (by simp [hs, fcodeHE_size]; omega), arr_left _ _ _ (by simp [hs, fcodeHE_size]; omega),
    arr_left _ _ _ (by simp [fcodeHE_size]; omega)]

theorem fcodeH_enter (a n cp cl el d : Nat) (B : Array I2) :
    (fcodeH a n cp cl el d B)[0]? = some (I3.base I2.enter) := by
  rw [fcodeH_E a n cp cl el d B 0 (by omega)]
  simp [fcodeHE, Array.getElem?_append]

theorem fcodeH_pstore (a n cp cl el d : Nat) (B : Array I2) (i : Nat) (hi : i < n) :
    (fcodeH a n cp cl el d B)[1 + i]? = some (I3.base (I2.base (I.str i i))) := by
  have hp : ∀ n, ∀ i (hi : i < n), (pstore n)[i]? = some (I.str i i) := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ n ih =>
        intro i hi
        simp only [pstore, Array.getElem?_append, pstore_size]
        by_cases h : i < n
        · simp [h, ih i h]
        · have : i = n := by omega
          subst this; simp
  rw [fcodeH_E a n cp cl el d B (1 + i) (by omega)]
  have h1 : (fcodeHE n)[1 + i]? = ((pstore n).map I2.base)[i]?.map I3.base := by
    simp [fcodeHE, Array.getElem?_append, Array.getElem?_map]
  rw [h1]
  simp [Array.getElem?_map, hp n i hi]

theorem fcodeH_grow (a n cp cl el d : Nat) (B : Array I2) (k : Nat) (x : I3) (h : (growCode cp cl el d)[k]? = some x) :
    (fcodeH a n cp cl el d B)[1 + n + k]? = some x := by
  have hs := growCode_size24 cp cl el d
  have hk : k < 24 := by
    cases Nat.lt_or_ge k 24 with
    | inl h' => exact h'
    | inr h' => rw [Array.getElem?_eq_none (by rw [hs]; exact h')] at h; cases h
  unfold fcodeH
  rw [arr_left _ _ _ (by simp [hs, fcodeHE_size]; omega), arr_left _ _ _ (by simp [hs, fcodeHE_size]; omega)]
  have := arr_right (fcodeHE n) (growCode cp cl el d) k
  rw [fcodeHE_size] at this
  rw [this]; exact h

theorem fcodeH_jmp (a n cp cl el d : Nat) (B : Array I2) :
    (fcodeH a n cp cl el d B)[1 + n + 24]? = some (I3.base (I2.jmp (a + 2 * n + 27))) := by
  have hs := growCode_size24 cp cl el d
  unfold fcodeH
  rw [arr_left _ _ _ (by simp [hs, fcodeHE_size] <;> omega)]
  have := arr_right (fcodeHE n ++ growCode cp cl el d) #[I3.base (I2.jmp (a + 2 * n + 27))] 0
  rw [Array.size_append, hs, fcodeHE_size, Nat.add_zero] at this
  rw [this]; simp

theorem fcodeH_T (a n cp cl el d : Nat) (B : Array I2) (k : Nat) :
    (fcodeH a n cp cl el d B)[1 + n + 24 + 1 + k]? = (fcodeHT n B)[k]? := by
  have hs := growCode_size24 cp cl el d
  unfold fcodeH
  have := arr_right (fcodeHE n ++ growCode cp cl el d ++ #[I3.base (I2.jmp (a + 2 * n + 27))]) (fcodeHT n B) k
  rw [Array.size_append, Array.size_append, hs, fcodeHE_size] at this
  simp only [Array.size_singleton] at this
  exact this

theorem fcodeHT_body (n : Nat) (B : Array I2) (k : Nat) (hk : k < B.size) :
    (fcodeHT n B)[(1 + n) + k]? = some (I3.base B[k]) := by
  have hr := recEntry_size n
  simp only [fcodeHT, Array.getElem?_map]
  have : (recEntry n ++ B ++ #[I2.leave, I2.ret])[(1 + n) + k]? = some B[k] := by
    rw [arr_left _ _ _ (by simp [hr]; omega)]
    have := arr_right (recEntry n) B k
    rw [hr] at this; rw [this]; simp [hk]
  rw [this]; rfl

theorem fcodeHT_leave (n : Nat) (B : Array I2) : (fcodeHT n B)[(1 + n) + B.size]? = some (I3.base I2.leave) := by
  have hr := recEntry_size n
  simp only [fcodeHT, Array.getElem?_map]
  have := arr_right (recEntry n ++ B) #[I2.leave, I2.ret] 0
  rw [Array.size_append, hr, Nat.add_zero] at this
  rw [this]; rfl

theorem fcodeHT_ret (n : Nat) (B : Array I2) : (fcodeHT n B)[(1 + n) + B.size + 1]? = some (I3.base I2.ret) := by
  have hr := recEntry_size n
  simp only [fcodeHT, Array.getElem?_map]
  have := arr_right (recEntry n ++ B) #[I2.leave, I2.ret] 1
  rw [Array.size_append, hr] at this
  rw [this]; rfl

/-- 作業領域を取る関数(`fcodeH`)の入口の契約。`fcodeA_ok_at` と同じ形(結果・枠・`lr`・フレームが元のまま)に、器の確保
(`sp` が `((8n+15)/16)×16+16` 下がる)を足したもの。本体 `B` は `I2` の機械で動く(`Q` はその写し。`growCode` の領域は `jmp 自分`)。
枠の `cp` の番は、作業領域を指すので、本体の前提から除く。`leave` のあとの `mov sp, x29`(`sp` を戻す)はこの模型の外で、
`Z.sp` は確保したままの値。 -/
theorem fcodeH_ok_at (a n cp cl el d : Nat) (B : Array I2) (P : Array I3) (Q : Array I2)
    (hG : ∀ (k : Nat) (x : I3), (fcodeH a n cp cl el d B)[k]? = some x → P[a + k]? = some x)
    (hfill : ∀ k, a + 1 + n ≤ k → k < a + 1 + n + 24 → Q[k]? = some (I2.jmp k))
    (hQP : ∀ (k : Nat) (x : I2), Q[k]? = some x → (a + 1 + n ≤ k ∧ k < a + 1 + n + 24) ∨ P[k]? = some (I3.base x))
    (hPQ : ∀ (k : Nat) (x : I2), P[k]? = some (I3.base x) → (k < a + 1 + n ∨ a + 1 + n + 24 ≤ k) → Q[k]? = some x)
    (hcl : cl < n) (hel : el < n) (hcp : cp < n)
    (R : Nat → Option Int) (res : Option Int)
    (hbody : ∀ s : St, s.pc = a + 2 * n + 27 → (∀ k < n, k ≠ cp → s.m k = encode (R k)) →
      (∃ p : Nat, p < 2 ^ 62 ∧ s.m cp = encode (some (p : Int))) →
      (∀ (k : Nat) (x : I2), B[k]? = some x → Q[a + 2 * n + 27 + k]? = some x) →
      ∃ s', Steps2 Q s s' ∧ s'.pc = a + 2 * n + 27 + B.size ∧ s'.r 0 = encode res ∧ s'.stk = s.stk)
    (x : HSt) (hs : x.s.pc = a) (hr : ∀ k < n, k ≠ cp → x.s.r k = encode (R k))
    (hn : (x.s.r cl).toNat + d * (x.s.r el).toNat < 2 ^ 50) (hd : d < 2 ^ 50)
    (hsa : (x.s.r cp).toNat % 8 = 0) (hsrc : x.sp.toNat ≤ (x.s.r cp).toNat)
    (hs64 : (x.s.r cp).toNat + 8 * (x.s.r cl).toNat < 2 ^ 64)
    (hsp : x.sp.toNat % 16 = 0) (hroom : 8 * ((x.s.r cl).toNat + d * (x.s.r el).toNat) + 32 ≤ x.sp.toNat)
    (hsp62 : x.sp.toNat + 16 < 2 ^ 62) :
    ∃ Z : HSt, Steps3 P x Z ∧ Z.s.pc = x.s.lr ∧ Z.s.r 0 = encode res ∧ Z.s.m = x.s.m ∧ Z.s.lr = x.s.lr ∧
      Z.s.stk = x.s.stk ∧
      Z.sp.toNat = x.sp.toNat - (((8 * ((x.s.r cl).toNat + d * (x.s.r el).toNat) + 15) / 16) * 16 + 16) := by
  -- enter
  obtain ⟨x1, hx1⟩ : ∃ x1, x1 = step3 (I3.base I2.enter) x := ⟨_, rfl⟩
  have g1 : Steps3 P x x1 := by
    rw [hx1]; exact Steps3.go' _ a hs (by simpa using hG 0 _ (fcodeH_enter a n cp cl el d B)) (Steps3.refl _)
  have x1pc : x1.s.pc = a + 1 := by simp [hx1, step3, step2, hs]
  have x1r : x1.s.r = x.s.r := by simp [hx1, step3, step2]
  have x1h : x1.h = x.h := by simp [hx1, step3]
  have x1sp : x1.sp = x.sp := by simp [hx1, step3]
  have x1k : x1.s.stk = (x.s.m, x.s.lr) :: x.s.stk := by simp [hx1, step3, step2]
  have x1l : x1.s.lr = x.s.lr := by simp [hx1, step3, step2]
  -- 仮引数の str
  obtain ⟨y1, g2, y1pc, y1h, y1sp, y1r, y1m, _, y1l, y1k⟩ := pstore3_ok P (a + 1) n (fun i hi => by
      have := hG (1 + i) _ (fcodeH_pstore a n cp cl el d B i hi)
      simpa [Nat.add_assoc] using this) x1 x1pc
  have mcl : y1.s.m cl = x.s.r cl := by rw [y1m cl hcl, x1r]
  have mel : y1.s.m el = x.s.r el := by rw [y1m el hel, x1r]
  have mcp : y1.s.m cp = x.s.r cp := by rw [y1m cp hcp, x1r]
  -- growCode
  obtain ⟨y, g3, ypc, ysp, ymcp, ymo, _, _, _, yl, yk⟩ := growEntry_ok P (a + 1 + n) cp cl el d
    (fun k x' hk => by
      have := hG (1 + n + k) x' (fcodeH_grow a n cp cl el d B k x' hk)
      simpa [Nat.add_assoc] using this)
    y1 (by rw [y1pc]) (by rw [mcl, mel]; exact hn) hd (by rw [mcp]; exact hsa) (by rw [mcp, y1sp, x1sp]; exact hsrc)
    (by rw [mcp, mcl]; exact hs64) (by rw [y1sp, x1sp]; exact hsp) (by rw [mcl, mel, y1sp, x1sp]; exact hroom)
  rw [mcl, mel, y1sp, x1sp] at ysp
  -- jmp 本体へ
  obtain ⟨y2, hy2⟩ : ∃ y2, y2 = step3 (I3.base (I2.jmp (a + 2 * n + 27))) y := ⟨_, rfl⟩
  have g4 : Steps3 P y y2 := by
    rw [hy2]
    exact Steps3.go' _ (a + (1 + n + 24)) (by rw [ypc]; omega) (hG (1 + n + 24) _ (fcodeH_jmp a n cp cl el d B)) (Steps3.refl _)
  have y2pc : y2.s.pc = a + 2 * n + 27 := by simp [hy2, step3, step2]
  have y2m : y2.s.m = y.s.m := by simp [hy2, step3, step2]
  have y2k : y2.s.stk = y.s.stk := by simp [hy2, step3, step2]
  have y2sp : y2.sp = y.sp := by simp [hy2, step3]
  have y2l : y2.s.lr = y.s.lr := by simp [hy2, step3, step2]
  -- 本体
  obtain ⟨s', hbs, bpc, br0, bk⟩ := hbody y2.s y2pc (by
      intro k hk hkc
      rw [y2m, ymo k hkc, y1m k hk, x1r]; exact hr k hk hkc)
    ⟨(y.s.m cp).toNat, by rw [ymcp]; omega, by
      rw [y2m]
      show y.s.m cp = BitVec.ofInt 64 (((y.s.m cp).toNat : Nat) : Int)
      rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
    (fun k x' hk => by
      have hlt : k < B.size := by
        cases Nat.lt_or_ge k B.size with
        | inl h => exact h
        | inr h => simp [Array.getElem?_eq_none h] at hk
      have h1 := hG (1 + n + 24 + 1 + ((1 + n) + k)) _ (by
        rw [fcodeH_T a n cp cl el d B]
        exact fcodeHT_body n B k hlt)
      have h2 : B[k] = x' := by simpa [Array.getElem?_eq_getElem hlt] using hk
      subst h2
      have e : a + (1 + n + 24 + 1 + ((1 + n) + k)) = a + 2 * n + 27 + k := by omega
      rw [e] at h1
      exact hPQ _ _ h1 (by omega))
  have g5 := lift2 P Q (a + 1 + n) (a + 1 + n + 24) hfill hQP y2.s s' hbs (by omega) y2.h y2.sp y2.c y2.hb
  -- leave
  have spk : s'.stk = (x.s.m, x.s.lr) :: x.s.stk := by rw [bk, y2k, yk, y1k, x1k]
  obtain ⟨u, hu⟩ : ∃ u : HSt, u = ⟨s', y2.h, y2.sp, y2.c, y2.hb⟩ := ⟨_, rfl⟩
  obtain ⟨u2, hu2⟩ : ∃ u2, u2 = step3 (I3.base I2.leave) u := ⟨_, rfl⟩
  have g6 : Steps3 P u u2 := by
    rw [hu2]
    exact Steps3.go' _ (a + (1 + n + 24 + 1 + ((1 + n) + B.size))) (by rw [hu]; simp [bpc]; omega) (hG (1 + n + 24 + 1 + ((1 + n) + B.size)) _ (by
      rw [fcodeH_T a n cp cl el d B]; exact fcodeHT_leave n B)) (Steps3.refl _)
  have u2s : u2.s = { s' with pc := s'.pc + 1, m := x.s.m, lr := x.s.lr, stk := x.s.stk } := by
    simp [hu2, hu, step3, step2, spk]
  have u2pc : u2.s.pc = a + (1 + n + 24 + 1 + ((1 + n) + B.size + 1)) := by
    rw [u2s]; simp [bpc]; omega
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = step3 (I3.base I2.ret) u2 := ⟨_, rfl⟩
  have g7 : Steps3 P u2 Z := by
    rw [hZ]
    exact Steps3.go' _ _ u2pc (hG (1 + n + 24 + 1 + ((1 + n) + B.size + 1)) _ (by
      rw [fcodeH_T a n cp cl el d B]; exact fcodeHT_ret n B)) (Steps3.refl _)
  refine ⟨Z, g1.trans (g2.trans (g3.trans (g4.trans ((by rw [← hu] at g5; exact g5 : Steps3 P y2 u).trans (g6.trans g7))))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hZ, step3, step2, u2s]
  · simp [hZ, step3, step2, u2s, br0]
  · simp [hZ, step3, step2, u2s]
  · simp [hZ, step3, step2, u2s]
  · simp [hZ, step3, step2, u2s]
  · simp [hZ, step3, hu2, hu, y2sp]; omega

/-- 累積の枠 `cp` を作業領域の位置(Int として見える値 `p`)に差し替えた環境 -/
def updCp (ρ : Nat → Option Int) (cp p : Nat) : Nat → Option Int := fun j => if j = cp then some (p : Int) else ρ j

/-- **`fcodeH` の本体として自分への末尾呼びのループ(`loopCode`)を載せる**(`selftailA_fn_ok` の作業領域版)。
累積の枠 `cp` は作業領域の位置が入っていて、ループの Int の式は読まない(読んでも結果は変わらない)ので、
`updCp` で枠 `cp` に `p`(`< 2^62`)を置いた環境で、止まる条件 `LDom` と結果 `LΦ` が `p` によらない(`hD`・`hres`)ことを仮定する。
`loop_ok` を `Q`(`growCode` の領域を `jmp 自分` で埋めた `I2` の写し)の上で使い、`fcodeH_ok_at` へ渡す。 -/
theorem selftailH_fn_ok (nov : AOp → E → E → Bool) (Φ : Nat → List (Option Int) → Option Int) (Dom : Nat → List (Option Int) → Prop)
    (hΦ : ∀ f vs, (∀ v ∈ vs, InR v) → InR (Φ f vs))
    (hnov1 : ∀ o l r, nov o l r = true → ∀ ρ a b, sem ρ l = some a → sem ρ r = some b → ∃ z, arithInt o a b = some z)
    (hnov : ∀ o l r, nov o l r = true → ∀ ρ a b, sem2 Φ ρ l = some a → sem2 Φ ρ r = some b → ∃ z, arithInt o a b = some z)
    (tgt ar : Nat → Nat) (Q : Array I2)
    (hcall : ∀ f (vs : List (Option Int)) (s : St), s.pc = tgt f → vs.length = ar f → (∀ v ∈ vs, ∃ z, v = some z) → (∀ v ∈ vs, InR v) →
      (∀ k (h : k < vs.length), s.r k = encode vs[k]) → Dom f vs →
      ∃ s', Steps2 Q s s' ∧ s'.pc = s.lr ∧ s'.r 0 = encode (Φ f vs) ∧ s'.m = s.m ∧ s'.lr = s.lr ∧ s'.stk = s.stk)
    (c : Cn) (v : E) (as : List E)
    (hc : c.lits) (hcv : c.maxVar ≤ as.length)
    (hv : v.lits2 ∧ v.arOk ar ∧ v.maxVar ≤ as.length) (has : ∀ x ∈ as, x.lits2 ∧ x.arOk ar ∧ x.maxVar ≤ as.length)
    (a cp cl el d : Nat) (P : Array I3)
    (hG : ∀ (k : Nat) (x : I3), (fcodeH a as.length cp cl el d (loopCode nov tgt c v as (a + 2 * as.length + 27)))[k]? = some x → P[a + k]? = some x)
    (hfill : ∀ k, a + 1 + as.length ≤ k → k < a + 1 + as.length + 24 → Q[k]? = some (I2.jmp k))
    (hQP : ∀ (k : Nat) (x : I2), Q[k]? = some x → (a + 1 + as.length ≤ k ∧ k < a + 1 + as.length + 24) ∨ P[k]? = some (I3.base x))
    (hPQ : ∀ (k : Nat) (x : I2), P[k]? = some (I3.base x) → (k < a + 1 + as.length ∨ a + 1 + as.length + 24 ≤ k) → Q[k]? = some x)
    (hcl : cl < as.length) (hel : el < as.length) (hcp : cp < as.length)
    (k : Nat) (vs : List (Option Int)) (hlen : vs.length = as.length) (hall : ∀ w ∈ vs, ∃ z, w = some z) (hin : ∀ w ∈ vs, InR w)
    (res0 : Option Int)
    (hD : ∀ p : Nat, p < 2 ^ 62 → LDom Φ Dom c v as k (updCp (envOf vs) cp p))
    (hres : ∀ p : Nat, p < 2 ^ 62 → LΦ Φ c v as k (updCp (envOf vs) cp p) = res0)
    (x : HSt) (hs : x.s.pc = a) (hr : ∀ j (h : j < vs.length), j ≠ cp → x.s.r j = encode vs[j])
    (hn : (x.s.r cl).toNat + d * (x.s.r el).toNat < 2 ^ 50) (hd : d < 2 ^ 50)
    (hsa : (x.s.r cp).toNat % 8 = 0) (hsrc : x.sp.toNat ≤ (x.s.r cp).toNat)
    (hs64 : (x.s.r cp).toNat + 8 * (x.s.r cl).toNat < 2 ^ 64)
    (hsp : x.sp.toNat % 16 = 0) (hroom : 8 * ((x.s.r cl).toNat + d * (x.s.r el).toNat) + 32 ≤ x.sp.toNat)
    (hsp62 : x.sp.toNat + 16 < 2 ^ 62) :
    ∃ Z : HSt, Steps3 P x Z ∧ Z.s.pc = x.s.lr ∧ Z.s.r 0 = encode res0 ∧ Z.s.m = x.s.m ∧ Z.s.lr = x.s.lr ∧
      Z.s.stk = x.s.stk ∧
      Z.sp.toNat = x.sp.toNat - (((8 * ((x.s.r cl).toNat + d * (x.s.r el).toNat) + 15) / 16) * 16 + 16) := by
  refine fcodeH_ok_at a as.length cp cl el d _ P Q hG hfill hQP hPQ hcl hel hcp (envOf vs) res0 ?_ x hs ?_ hn hd hsa hsrc hs64 hsp hroom hsp62
  · intro s' hs' hm ⟨p, hp, hcp'⟩ hGB
    have hM : (p : Int) ≤ M := by unfold M; have : (2 : Int) ^ 62 ≤ 2 ^ 63 - 1 := by decide
                                  have h2 : (p : Int) < 2 ^ 62 := by exact_mod_cast hp
                                  omega
    obtain ⟨u, hu, pu, ru, ku⟩ := loop_ok nov Φ Dom hΦ hnov1 hnov tgt ar Q hcall c v as hc hcv hv has (a + 2 * as.length + 27) hGB
      k (updCp (envOf vs) cp p)
      (fun j => by
        unfold updCp; by_cases hj : j = cp
        · simp [hj]; intro z hz; cases hz; unfold InR at *; constructor <;> omega
        · simp [hj]; exact envOf_inR_gen vs hin j)
      (fun j => by
        unfold updCp; by_cases hj : j = cp
        · exact ⟨p, by simp [hj]⟩
        · simp [hj]; exact envOf_some vs j)
      s' (hD p hp) hs'
      (fun j hj => by
        unfold updCp; by_cases hjc : j = cp
        · subst hjc; simpa using hcp'
        · simp [hjc]; exact hm j hj hjc)
    exact ⟨u, hu, pu, by rw [ru, hres p hp], ku⟩
  · intro j hj hjc
    have hj' : j < vs.length := by omega
    obtain ⟨z, hz⟩ := hall vs[j] (List.getElem_mem hj')
    have : envOf vs j = vs[j] := by simp [envOf, List.getElem?_eq_getElem hj', hz]
    rw [this]; exact hr j hj' hjc

/-- `P` の `I2` の写し: 領域 `[g0, g1)` は `jmp 自分`、ほかは `I2.base` を外した命令(`I3` の命令が領域の外にあれば `jmp 自分`) -/
def shadowQ (P : Array I3) (g0 g1 : Nat) : Array I2 :=
  P.mapIdx (fun k i => if g0 ≤ k ∧ k < g1 then I2.jmp k else match i with | .base j => j | _ => I2.jmp k)

theorem shadowQ_get (P : Array I3) (g0 g1 k : Nat) :
    (shadowQ P g0 g1)[k]? = (P[k]?).map (fun i => if g0 ≤ k ∧ k < g1 then I2.jmp k else match i with | .base j => j | _ => I2.jmp k) := by
  simp [shadowQ, Array.getElem?_mapIdx]

/-- 領域の外が `I2.base` だけの `I3` の列 `P` の写しは、`fcodeH_ok_at` の `Q` の条件を満たす -/
theorem shadowQ_spec (P : Array I3) (g0 g1 : Nat) (hlen : g1 ≤ P.size)
    (hnb : ∀ (k : Nat) (i : I3), P[k]? = some i → ¬ (g0 ≤ k ∧ k < g1) → ∃ j, i = I3.base j) :
    (∀ k, g0 ≤ k → k < g1 → (shadowQ P g0 g1)[k]? = some (I2.jmp k)) ∧
    (∀ (k : Nat) (x : I2), (shadowQ P g0 g1)[k]? = some x → (g0 ≤ k ∧ k < g1) ∨ P[k]? = some (I3.base x)) ∧
    (∀ (k : Nat) (x : I2), P[k]? = some (I3.base x) → (k < g0 ∨ g1 ≤ k) → (shadowQ P g0 g1)[k]? = some x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k h1 h2
    rw [shadowQ_get, Array.getElem?_eq_getElem (by omega)]
    simp [h1, h2]
  · intro k x hx
    rw [shadowQ_get] at hx
    by_cases hin : g0 ≤ k ∧ k < g1
    · exact Or.inl hin
    · right
      cases hP : P[k]? with
      | none => simp [hP] at hx
      | some i =>
          obtain ⟨j, rfl⟩ := hnb k i hP hin
          simp [hP, hin] at hx
          rw [← hx]
  · intro k x hx hout
    rw [shadowQ_get, hx]
    have : ¬ (g0 ≤ k ∧ k < g1) := by omega
    simp [this]

/-! ### ループの中の append(`commit_grow`)

`sign_asm.py` の自分への末尾呼びで、累積(リスト。語の並び)の末尾へ `k` 個の要素を足す部分: 実引数の評価(要素を枠の `te+i` へ)のあと、
`t1 = ptr`・`t2 = len + k`(setup)、入る個数の検査(`ldr x10,[x9,#-8]; cmp x11,x10; b.hi 溢れ`)、末尾へ書く(`commit`)、
仮引数 `ps`(ptr)・`ps+1`(len)の更新(moves)。枠の番号は `ps`・`pl`・`t1`・`t2`・`te+i`。 -/

def bb (i : I) : I3 := I3.base (I2.base i)

def appSetup (ps pl k t1 t2 : Nat) : List I3 :=
  [bb (I.ldr 0 ps), bb (I.ldr 1 pl), I3.addI 1 1 k, bb (I.str 0 t1), bb (I.str 1 t2)]

def appGuard (ps pl k : Nat) : List I3 :=
  [bb (I.ldr 9 ps), I3.ldrN 10 9 8, bb (I.ldr 11 pl), I3.addI 11 11 k, I3.cmpH 11 10]

def appPre (ps pl : Nat) : List I3 :=
  [bb (I.ldr 10 ps), bb (I.ldr 11 pl), I3.lslI 11 11 3, I3.addR 10 10 11]

def commitL (te : Nat) : Nat → List I3
  | 0 => []
  | k + 1 => commitL te k ++ [bb (I.ldr 9 (te + k)), I3.strP 9 10 (8 * k)]

def appMoves (ps pl t1 t2 : Nat) : List I3 :=
  [bb (I.ldr 9 t1), bb (I.str 9 ps), bb (I.ldr 9 t2), bb (I.str 9 pl)]

theorem commitL_length (te k : Nat) : (commitL te k).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [commitL, ih]; omega

theorem commitL_nobr (te k : Nat) : ∀ i ∈ commitL te k, nobr i := by
  induction k with
  | zero => simp [commitL]
  | succ k ih =>
      intro i hi
      simp [commitL] at hi
      rcases hi with hi | rfl | rfl
      · exact ih i hi
      · simp [bb, nobr]
      · simp [nobr]

theorem runL_append (l1 l2 : List I3) (x : HSt) : runL (l1 ++ l2) x = runL l2 (runL l1 x) := by
  simp [runL, List.foldl_append]

/-- 書く部分: 末尾 `E`(語の番地。8 の倍数)から `k` 語へ、枠の `te+i` を書く -/
theorem commitL_facts (te : Nat) :
    ∀ (k : Nat) (x : HSt) (E : W), x.s.r 10 = E → E.toNat % 8 = 0 → E.toNat + 8 * k < 2 ^ 64 →
      (runL (commitL te k) x).s.pc = x.s.pc + 2 * k ∧ (runL (commitL te k) x).s.r 10 = E ∧
      (runL (commitL te k) x).s.m = x.s.m ∧ (runL (commitL te k) x).s.lr = x.s.lr ∧
      (runL (commitL te k) x).s.stk = x.s.stk ∧ (runL (commitL te k) x).sp = x.sp ∧ (runL (commitL te k) x).c = x.c ∧
      (∀ w, (runL (commitL te k) x).h w =
        if E.toNat / 8 ≤ w ∧ w < E.toNat / 8 + k then x.s.m (te + (w - E.toNat / 8)) else x.h w) := by
  intro k
  induction k with
  | zero =>
      intro x E h10 _ _
      simp [commitL, runL]
      exact ⟨h10, fun w a b => by omega⟩
  | succ k ih =>
      intro x E h10 hE hlt
      obtain ⟨p1, r1, m1, l1, k1, sp1, c1, hh1⟩ := ih x E h10 hE (by omega)
      obtain ⟨y, hy⟩ : ∃ y, y = runL (commitL te k) x := ⟨_, rfl⟩
      rw [← hy] at p1 r1 m1 l1 k1 sp1 c1 hh1
      have hrun : runL (commitL te (k + 1)) x = step3 (I3.strP 9 10 (8 * k)) (step3 (bb (I.ldr 9 (te + k))) y) := by
        rw [commitL, runL_append, ← hy]; simp [runL]
      rw [hrun]
      have e1 : (E + BitVec.ofNat 64 (8 * k)).toNat = E.toNat + 8 * k := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega : 8 * k < 2 ^ 64)]
        exact Nat.mod_eq_of_lt (by omega)
      refine ⟨by simp [step3, bb, step2, step, St.set, p1]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [step3, bb, step2, step, St.set, r1]
      · simp [step3, bb, step2, step, St.set, m1]
      · simp [step3, bb, step2, step, St.set, l1]
      · simp [step3, bb, step2, step, St.set, k1]
      · simp [step3, bb, step2, step, St.set, sp1]
      · simp [step3, bb, step2, step, St.set, c1]
      · intro w
        obtain ⟨u1, hu1⟩ : ∃ u1, u1 = step3 (bb (I.ldr 9 (te + k))) y := ⟨_, rfl⟩
        rw [← hu1] at hrun ⊢
        have hr : u1.s.r 10 = E := by rw [hu1]; simp [step3, bb, step2, step, St.set, r1]
        have hr9 : u1.s.r 9 = x.s.m (te + k) := by rw [hu1]; simp [step3, bb, step2, step, St.set, m1]
        have hh : u1.h = y.h := by rw [hu1]; rfl
        have hfin : (step3 (I3.strP 9 10 (8 * k)) u1).h w =
            if w = (u1.s.r 10 + BitVec.ofNat 64 (8 * k)).toNat / 8 then u1.s.r 9 else u1.h w := rfl
        rw [hfin, hr, hr9, e1, hh, hh1 w]
        by_cases hw : w = (E.toNat + 8 * k) / 8
        · have hk8 : (E.toNat + 8 * k) / 8 = E.toNat / 8 + k := by omega
          have h1 : E.toNat / 8 ≤ w := by omega
          have h2 : w < E.toNat / 8 + (k + 1) := by omega
          rw [if_pos hw, if_pos ⟨h1, h2⟩]
          have : w - E.toNat / 8 = k := by omega
          rw [this]
        · rw [if_neg hw]
          by_cases hin : E.toNat / 8 ≤ w ∧ w < E.toNat / 8 + k
          · rw [if_pos hin, if_pos (by omega)]
          · rw [if_neg hin, if_neg (by omega)]

theorem appSetup_facts (ps pl k t1 t2 : Nat) (x : HSt) :
    (runL (appSetup ps pl k t1 t2) x).s.pc = x.s.pc + 5 ∧
    (runL (appSetup ps pl k t1 t2) x).s.m = (fun j => if j = t2 then x.s.m pl + BitVec.ofNat 64 k
        else if j = t1 then x.s.m ps else x.s.m j) ∧
    (runL (appSetup ps pl k t1 t2) x).h = x.h ∧ (runL (appSetup ps pl k t1 t2) x).sp = x.sp ∧
    (runL (appSetup ps pl k t1 t2) x).c = x.c ∧ (runL (appSetup ps pl k t1 t2) x).s.lr = x.s.lr ∧
    (runL (appSetup ps pl k t1 t2) x).s.stk = x.s.stk := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [appSetup, runL, step3, bb, step2, step, St.set]

theorem appGuard_facts (ps pl k : Nat) (x : HSt) (h8 : 8 ≤ (x.s.m ps).toNat) (h64 : (x.s.m ps).toNat < 2 ^ 64) :
    (runL (appGuard ps pl k) x).s.pc = x.s.pc + 5 ∧
    (runL (appGuard ps pl k) x).s.r 10 = x.h (((x.s.m ps).toNat - 8) / 8) ∧
    (runL (appGuard ps pl k) x).s.r 11 = x.s.m pl + BitVec.ofNat 64 k ∧
    (runL (appGuard ps pl k) x).c = decide ((x.h (((x.s.m ps).toNat - 8) / 8)).toNat < (x.s.m pl + BitVec.ofNat 64 k).toNat) ∧
    (runL (appGuard ps pl k) x).s.m = x.s.m ∧ (runL (appGuard ps pl k) x).h = x.h ∧ (runL (appGuard ps pl k) x).sp = x.sp ∧
    (runL (appGuard ps pl k) x).s.lr = x.s.lr ∧ (runL (appGuard ps pl k) x).s.stk = x.s.stk := by
  have hsub : (x.s.m ps - BitVec.ofNat 64 8).toNat = (x.s.m ps).toNat - 8 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hmod : (18446744073709551608 + (x.s.m ps).toNat) % 18446744073709551616 = (x.s.m ps).toNat - 8 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [appGuard, runL, step3, bb, step2, step, St.set, hmod]

theorem appPre_facts (ps pl : Nat) (x : HSt) :
    (runL (appPre ps pl) x).s.pc = x.s.pc + 4 ∧
    (runL (appPre ps pl) x).s.r 10 = x.s.m ps + (x.s.m pl <<< 3) ∧
    (runL (appPre ps pl) x).s.m = x.s.m ∧ (runL (appPre ps pl) x).h = x.h ∧ (runL (appPre ps pl) x).sp = x.sp ∧
    (runL (appPre ps pl) x).c = x.c ∧ (runL (appPre ps pl) x).s.lr = x.s.lr ∧ (runL (appPre ps pl) x).s.stk = x.s.stk := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [appPre, runL, step3, bb, step2, step, St.set]

theorem appMoves_facts (ps pl t1 t2 : Nat) (x : HSt) (h1 : t1 ≠ ps) (h2 : t2 ≠ pl) (h3 : ps ≠ pl) (h4 : t1 ≠ pl) (h5 : t2 ≠ ps) :
    (runL (appMoves ps pl t1 t2) x).s.pc = x.s.pc + 4 ∧
    (runL (appMoves ps pl t1 t2) x).s.m = (fun j => if j = pl then x.s.m t2 else if j = ps then x.s.m t1 else x.s.m j) ∧
    (runL (appMoves ps pl t1 t2) x).h = x.h ∧ (runL (appMoves ps pl t1 t2) x).sp = x.sp ∧
    (runL (appMoves ps pl t1 t2) x).s.lr = x.s.lr ∧ (runL (appMoves ps pl t1 t2) x).s.stk = x.s.stk := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [appMoves, runL, step3, bb, step2, step, St.set]
  funext j
  by_cases hp : j = pl <;> by_cases hq : j = ps <;> simp [hp, hq, h1, h2, h3, h4, h5]

/-- ループの 1 回の累積の append 全体: setup・検査・`b.hi 溢れ`・末尾の計算・書き・仮引数の更新 -/
def appendCode (ps pl k t1 t2 te o : Nat) : List I3 :=
  appSetup ps pl k t1 t2 ++ (appGuard ps pl k ++ ([I3.bhi o] ++ (appPre ps pl ++ (commitL te k ++ appMoves ps pl t1 t2))))

theorem appendCode_length (ps pl k t1 t2 te o : Nat) : (appendCode ps pl k t1 t2 te o).length = 19 + 2 * k := by
  simp [appendCode, appSetup, appGuard, appPre, appMoves, commitL_length]; omega

theorem seg_of {L : List I3} {P : Array I3} {b : Nat} (hP : ∀ i (hi : i < L.length), P[b + i]? = some L[i])
    (A S Z : List I3) (hL : L = A ++ (S ++ Z)) : ∀ i (hi : i < S.length), P[b + A.length + i]? = some S[i] := by
  intro i hi
  subst hL
  have := hP (A.length + i) (by simp; omega)
  rw [← Nat.add_assoc] at this
  rw [this]
  simp [List.getElem_append_right, hi]

theorem append_nobr : (∀ i ∈ appSetup ps pl k t1 t2, nobr i) ∧ (∀ i ∈ appGuard ps pl k, nobr i) ∧
    (∀ i ∈ appPre ps pl, nobr i) ∧ (∀ i ∈ appMoves ps pl t1 t2, nobr i) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro i hi
  · simp [appSetup] at hi; rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [bb, nobr]
  · simp [appGuard] at hi; rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [bb, nobr]
  · simp [appPre] at hi; rcases hi with rfl | rfl | rfl | rfl <;> simp [bb, nobr]
  · simp [appMoves] at hi; rcases hi with rfl | rfl | rfl | rfl <;> simp [bb, nobr]

/-- ループの中の append(`commit_grow`)の契約。累積の器 `ptr`(枠 `ps`)・長さ `len`(枠 `pl`)・入る個数 `x.h (ptr/8 - 1)`、足す `k` 個の要素は
枠の `te+i`。入らなければ(`cap < len + k`)`bhi` で溢れの行き先(`b + 10 + o`)へ、`h`・`sp`・`lr`・フレームは元のまま。入れば、語 `ptr/8 + len + i`
に要素が書かれ(ほかの語は元のまま)、仮引数の `ps`(ptr)は元のまま、`pl`(len)は `len + k` になる。 -/
theorem append_ok (P : Array I3) (b ps pl k t1 t2 te o : Nat)
    (hP : ∀ i (hi : i < (appendCode ps pl k t1 t2 te o).length), P[b + i]? = some (appendCode ps pl k t1 t2 te o)[i])
    (x : HSt) (hpc : x.s.pc = b)
    (h1 : t1 ≠ ps) (h2 : t2 ≠ pl) (h3 : ps ≠ pl) (h4 : t1 ≠ pl) (h5 : t2 ≠ ps) (h12 : t1 ≠ t2)
    (hte : ∀ i, i < k → te + i ≠ t1 ∧ te + i ≠ t2)
    (hal : (x.s.m ps).toNat % 8 = 0) (h8 : 8 ≤ (x.s.m ps).toNat)
    (hlen : (x.s.m pl).toNat + k < 2 ^ 50) (hptr : (x.s.m ps).toNat + 8 * ((x.s.m pl).toNat + k) < 2 ^ 64) :
    ∃ y : HSt, Steps3 P x y ∧ y.sp = x.sp ∧ y.s.lr = x.s.lr ∧ y.s.stk = x.s.stk ∧
      (((x.h (((x.s.m ps).toNat - 8) / 8)).toNat < (x.s.m pl).toNat + k ∧ y.s.pc = b + 10 + o ∧ y.h = x.h) ∨
       ((x.s.m pl).toNat + k ≤ (x.h (((x.s.m ps).toNat - 8) / 8)).toNat ∧ y.s.pc = b + 19 + 2 * k ∧
        (∀ w, y.h w = if (x.s.m ps).toNat / 8 + (x.s.m pl).toNat ≤ w ∧ w < (x.s.m ps).toNat / 8 + (x.s.m pl).toNat + k
          then x.s.m (te + (w - ((x.s.m ps).toNat / 8 + (x.s.m pl).toNat))) else x.h w) ∧
        y.s.m ps = x.s.m ps ∧ y.s.m pl = x.s.m pl + BitVec.ofNat 64 k)) := by
  have hC := appendCode_length ps pl k t1 t2 te o
  obtain ⟨hnS, hnG, hnP, hnM⟩ := (append_nobr (ps := ps) (pl := pl) (k := k) (t1 := t1) (t2 := t2))
  have hSegS := seg_of hP [] (appSetup ps pl k t1 t2)
    (appGuard ps pl k ++ ([I3.bhi o] ++ (appPre ps pl ++ (commitL te k ++ appMoves ps pl t1 t2)))) (by simp [appendCode])
  have hSegG := seg_of hP (appSetup ps pl k t1 t2) (appGuard ps pl k)
    ([I3.bhi o] ++ (appPre ps pl ++ (commitL te k ++ appMoves ps pl t1 t2))) (by simp [appendCode])
  have hSegB := seg_of hP (appSetup ps pl k t1 t2 ++ appGuard ps pl k) [I3.bhi o]
    (appPre ps pl ++ (commitL te k ++ appMoves ps pl t1 t2)) (by simp [appendCode])
  have hSegP := seg_of hP (appSetup ps pl k t1 t2 ++ appGuard ps pl k ++ [I3.bhi o]) (appPre ps pl)
    (commitL te k ++ appMoves ps pl t1 t2) (by simp [appendCode])
  have hSegC := seg_of hP (appSetup ps pl k t1 t2 ++ appGuard ps pl k ++ [I3.bhi o] ++ appPre ps pl) (commitL te k)
    (appMoves ps pl t1 t2) (by simp [appendCode])
  have hSegM := seg_of hP (appSetup ps pl k t1 t2 ++ appGuard ps pl k ++ [I3.bhi o] ++ appPre ps pl ++ commitL te k)
    (appMoves ps pl t1 t2) [] (by simp [appendCode])
  have lS : (appSetup ps pl k t1 t2).length = 5 := rfl
  have lG : (appGuard ps pl k).length = 5 := rfl
  have lP : (appPre ps pl).length = 4 := rfl
  have lM : (appMoves ps pl t1 t2).length = 4 := rfl
  have lC := commitL_length te k
  -- setup
  obtain ⟨gS, pS⟩ := runL_ok P b (appSetup ps pl k t1 t2) x 0 (by simpa using hpc) hnS (fun i hi => by
    have := hSegS i hi; simpa using this)
  obtain ⟨y1, hy1⟩ : ∃ y1, y1 = runL (appSetup ps pl k t1 t2) x := ⟨_, rfl⟩
  rw [← hy1] at gS pS
  simp only [lS, Nat.add_zero, Nat.zero_add] at pS
  obtain ⟨s1p, s1m, s1h, s1sp, s1c, s1l, s1k⟩ := appSetup_facts ps pl k t1 t2 x
  rw [← hy1] at s1p s1m s1h s1sp s1c s1l s1k
  have m1ps : y1.s.m ps = x.s.m ps := by rw [s1m]; simp [h5.symm, h1.symm]
  have m1pl : y1.s.m pl = x.s.m pl := by rw [s1m]; simp [h2.symm, h4.symm]
  have h64 : (x.s.m ps).toNat < 2 ^ 64 := (x.s.m ps).isLt
  -- 検査
  obtain ⟨gG, pG⟩ := runL_ok P b (appGuard ps pl k) y1 5 (by rw [s1p]; omega) hnG (fun i hi => by
    have := hSegG i hi; simp only [lS] at this
    rw [show b + 5 + i = b + 5 + i from rfl]; exact this)
  obtain ⟨y2, hy2⟩ : ∃ y2, y2 = runL (appGuard ps pl k) y1 := ⟨_, rfl⟩
  rw [← hy2] at gG pG
  rw [lG] at pG
  obtain ⟨s2p, s2r10, s2r11, s2c, s2m, s2h, s2sp, s2l, s2k⟩ := appGuard_facts ps pl k y1 (by rw [m1ps]; exact h8) (by rw [m1ps]; exact h64)
  rw [← hy2] at s2p s2r10 s2r11 s2c s2m s2h s2sp s2l s2k
  rw [m1ps, s1h] at s2r10 s2c
  rw [m1pl] at s2r11 s2c
  have hkW : (x.s.m pl + BitVec.ofNat 64 k).toNat = (x.s.m pl).toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hkW] at s2c
  -- b.hi
  obtain ⟨y3, hy3⟩ : ∃ y3, y3 = step3 (I3.bhi o) y2 := ⟨_, rfl⟩
  have g3 : Steps3 P y2 y3 := by
    rw [hy3]
    exact Steps3.go' _ (b + 10) (by rw [pG]) (by
      have := hSegB 0 (by simp)
      simp only [List.length_append, lS, lG] at this
      simpa [Nat.add_assoc] using this) (Steps3.refl _)
  have y3sp : y3.sp = x.sp := by rw [hy3]; cases hcc : y2.c <;> simp [step3, hcc, s2sp, s1sp]
  have y3l : y3.s.lr = x.s.lr := by rw [hy3]; cases hcc : y2.c <;> simp [step3, hcc, s2l, s1l]
  have y3k : y3.s.stk = x.s.stk := by rw [hy3]; cases hcc : y2.c <;> simp [step3, hcc, s2k, s1k]
  by_cases hov : (x.h (((x.s.m ps).toNat - 8) / 8)).toNat < (x.s.m pl).toNat + k
  · have hc : y2.c = true := by rw [s2c]; simp [hov]
    refine ⟨y3, gS.trans (gG.trans g3), y3sp, y3l, y3k, Or.inl ⟨hov, ?_, ?_⟩⟩
    · rw [hy3]; simp [step3, hc, pG]
    · rw [hy3]; simp [step3, hc, s2h, s1h]
  · have hc : y2.c = false := by rw [s2c]; simp; omega
    have y3pc : y3.s.pc = b + 11 := by rw [hy3]; simp [step3, hc, pG]
    have y3m : y3.s.m = y1.s.m := by rw [hy3]; simp [step3, hc, s2m]
    have y3h : y3.h = x.h := by rw [hy3]; simp [step3, hc, s2h, s1h]
    -- 末尾の計算
    obtain ⟨gP, pP⟩ := runL_ok P b (appPre ps pl) y3 11 (by rw [y3pc]) hnP (fun i hi => by
      have := hSegP i hi; simp only [List.length_append, List.length_singleton, lS, lG] at this
      rw [show b + 11 + i = b + (5 + 5 + 1) + i by omega]; exact this)
    obtain ⟨y4, hy4⟩ : ∃ y4, y4 = runL (appPre ps pl) y3 := ⟨_, rfl⟩
    rw [← hy4] at gP pP
    rw [lP] at pP
    obtain ⟨s4p, s4r10, s4m, s4h, s4sp, s4c, s4l, s4k⟩ := appPre_facts ps pl y3
    rw [← hy4] at s4p s4r10 s4m s4h s4sp s4c s4l s4k
    rw [y3m, m1ps, m1pl] at s4r10
    have hshl : (x.s.m pl <<< 3).toNat = (x.s.m pl).toNat * 8 := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      exact Nat.mod_eq_of_lt (by omega)
    have hE : (y4.s.r 10).toNat = (x.s.m ps).toNat + 8 * (x.s.m pl).toNat := by
      rw [s4r10, BitVec.toNat_add, hshl]
      exact (Nat.mod_eq_of_lt (by omega)).trans (by omega)
    -- 書く
    obtain ⟨gC, pC⟩ := runL_ok P b (commitL te k) y4 15 (by rw [s4p, y3pc]) (commitL_nobr te k) (fun i hi => by
      have := hSegC i hi; simp only [List.length_append, List.length_singleton, lS, lG, lP] at this
      rw [show b + 15 + i = b + (5 + 5 + 1 + 4) + i by omega]; exact this)
    obtain ⟨cp, cr, cm, cl, ck, csp, cc, chh⟩ := commitL_facts te k y4 (y4.s.r 10) rfl (by omega) (by omega)
    obtain ⟨y5, hy5⟩ : ∃ y5, y5 = runL (commitL te k) y4 := ⟨_, rfl⟩
    rw [← hy5] at gC pC cp cr cm cl ck csp cc chh
    rw [lC] at pC
    -- 仮引数の更新
    obtain ⟨gM, pM⟩ := runL_ok P b (appMoves ps pl t1 t2) y5 (15 + 2 * k) (by rw [cp, s4p, y3pc]; omega) hnM (fun i hi => by
      have := hSegM i hi; simp only [List.length_append, List.length_singleton, lS, lG, lP, lC] at this
      rw [show b + (15 + 2 * k) + i = b + (5 + 5 + 1 + 4 + 2 * k) + i by omega]; exact this)
    obtain ⟨y6, hy6⟩ : ∃ y6, y6 = runL (appMoves ps pl t1 t2) y5 := ⟨_, rfl⟩
    rw [← hy6] at gM pM
    rw [lM] at pM
    obtain ⟨s6p, s6m, s6h, s6sp, s6l, s6k⟩ := appMoves_facts ps pl t1 t2 y5 h1 h2 h3 h4 h5
    rw [← hy6] at s6p s6m s6h s6sp s6l s6k
    have y5m : y5.s.m = y1.s.m := by rw [cm, s4m, y3m]
    refine ⟨y6, gS.trans (gG.trans (g3.trans (gP.trans (gC.trans gM)))), ?_, ?_, ?_, Or.inr ⟨by omega, ?_, ?_, ?_, ?_⟩⟩
    · rw [s6sp, csp, s4sp, y3sp]
    · rw [s6l, cl, s4l, y3l]
    · rw [s6k, ck, s4k, y3k]
    · rw [s6p, cp, s4p, y3pc]; omega
    · intro w
      rw [s6h, chh w, hE, s4h, y3h]
      have e8 : ((x.s.m ps).toNat + 8 * (x.s.m pl).toNat) / 8 = (x.s.m ps).toNat / 8 + (x.s.m pl).toNat := by omega
      rw [e8]
      by_cases hw : (x.s.m ps).toNat / 8 + (x.s.m pl).toNat ≤ w ∧ w < (x.s.m ps).toNat / 8 + (x.s.m pl).toNat + k
      · rw [if_pos hw, if_pos hw]
        have hi : w - ((x.s.m ps).toNat / 8 + (x.s.m pl).toNat) < k := by omega
        obtain ⟨ha, hb⟩ := hte _ hi
        rw [s4m, y3m, s1m]; simp [ha, hb]
      · rw [if_neg hw, if_neg hw]
    · rw [s6m, y5m, s1m]
      simp [h3, h12]
    · rw [s6m, y5m, s1m]
      simp

/-- 累積(語の並び `L`)の不変条件: 器の先頭 `ptr`(枠 `ps`、8 の倍数)の語 `ptr/8 + i` が `L[i]`、長さの枠 `pl` が `L.length` -/
def AccInv (x : HSt) (ps pl : Nat) (L : List W) : Prop :=
  (x.s.m ps).toNat % 8 = 0 ∧ 8 ≤ (x.s.m ps).toNat ∧ (x.s.m pl).toNat = L.length ∧
    ∀ i (hi : i < L.length), x.h ((x.s.m ps).toNat / 8 + i) = L[i]

/-- 1 回の append が不変条件を保つ: 入る(`len + k ≤ cap`)なら、器の内容は `L ++ vs`、入る個数の語・`ptr` はそのまま -/
theorem append_inv (P : Array I3) (b ps pl k t1 t2 te o : Nat)
    (hP : ∀ i (hi : i < (appendCode ps pl k t1 t2 te o).length), P[b + i]? = some (appendCode ps pl k t1 t2 te o)[i])
    (x : HSt) (hpc : x.s.pc = b)
    (h1 : t1 ≠ ps) (h2 : t2 ≠ pl) (h3 : ps ≠ pl) (h4 : t1 ≠ pl) (h5 : t2 ≠ ps) (h12 : t1 ≠ t2)
    (hte : ∀ i, i < k → te + i ≠ t1 ∧ te + i ≠ t2)
    (L vs : List W) (hvs : vs.length = k) (hel : ∀ i (hi : i < vs.length), x.s.m (te + i) = vs[i])
    (hacc : AccInv x ps pl L)
    (hlen : L.length + k < 2 ^ 50) (hptr : (x.s.m ps).toNat + 8 * (L.length + k) < 2 ^ 64)
    (hcap : L.length + k ≤ (x.h ((x.s.m ps).toNat / 8 - 1)).toNat) :
    ∃ y : HSt, Steps3 P x y ∧ y.s.pc = b + 19 + 2 * k ∧ AccInv y ps pl (L ++ vs) ∧
      y.s.m ps = x.s.m ps ∧ y.h ((x.s.m ps).toNat / 8 - 1) = x.h ((x.s.m ps).toNat / 8 - 1) ∧
      y.sp = x.sp ∧ y.s.lr = x.s.lr ∧ y.s.stk = x.s.stk := by
  obtain ⟨hal, h8, hlenL, hcont⟩ := hacc
  have hc8 : ((x.s.m ps).toNat - 8) / 8 = (x.s.m ps).toNat / 8 - 1 := by omega
  obtain ⟨y, g, ysp, yl, yk, hcase⟩ := append_ok P b ps pl k t1 t2 te o hP x hpc h1 h2 h3 h4 h5 h12 hte hal h8
    (by omega) (by omega)
  rcases hcase with ⟨hov, _, _⟩ | ⟨_, ypc, yh, ymps, ympl⟩
  · exfalso; rw [hc8] at hov; omega
  · have hkW : (x.s.m pl + BitVec.ofNat 64 k).toNat = (x.s.m pl).toNat + k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)]
      exact Nat.mod_eq_of_lt (by omega)
    refine ⟨y, g, ypc, ⟨?_, ?_, ?_, ?_⟩, ymps, ?_, ysp, yl, yk⟩
    · rw [ymps]; exact hal
    · rw [ymps]; exact h8
    · rw [ympl, hkW]; simp [hlenL, hvs]
    · intro i hi
      rw [ymps, yh]
      by_cases hiL : i < L.length
      · have hw : ¬ ((x.s.m ps).toNat / 8 + (x.s.m pl).toNat ≤ (x.s.m ps).toNat / 8 + i ∧
            (x.s.m ps).toNat / 8 + i < (x.s.m ps).toNat / 8 + (x.s.m pl).toNat + k) := by omega
        rw [if_neg hw, hcont i hiL]
        simp [List.getElem_append_left, hiL]
      · have hv : i - L.length < vs.length := by simp at hi; omega
        have hw : ((x.s.m ps).toNat / 8 + (x.s.m pl).toNat ≤ (x.s.m ps).toNat / 8 + i ∧
            (x.s.m ps).toNat / 8 + i < (x.s.m ps).toNat / 8 + (x.s.m pl).toNat + k) := by simp at hi; omega
        rw [if_pos hw]
        have e : (x.s.m ps).toNat / 8 + i - ((x.s.m ps).toNat / 8 + (x.s.m pl).toNat) = i - L.length := by omega
        rw [e, hel _ hv]
        rw [List.getElem_append_right (Nat.not_lt.mp hiL)]
    · rw [yh]
      have : ¬ ((x.s.m ps).toNat / 8 + (x.s.m pl).toNat ≤ (x.s.m ps).toNat / 8 - 1 ∧
          (x.s.m ps).toNat / 8 - 1 < (x.s.m ps).toNat / 8 + (x.s.m pl).toNat + k) := by omega
      rw [if_neg this]

/-- 追加される要素の並び(第 `j0` 回から `r` 回ぶん) -/
def accs (vs : Nat → List W) : Nat → Nat → List W
  | _, 0 => []
  | j0, r + 1 => vs j0 ++ accs vs (j0 + 1) r

/-- `r` 回のループ: 各回で append のコードを走り(`Steps3 P`)、次の回の要素の評価(`refill`。要素の枠 `te+i` を書き換えるだけ。
実引数の評価・条件・`b entry` は `SirZAsm` の `loop_ok` の側で示してあり、ここでは仮定)を挟む -/
def iterR (P : Array I3) (refill : Nat → HSt → HSt) : Nat → Nat → HSt → HSt → Prop
  | 0, _, x, w => w = x
  | r + 1, j, x, w => ∃ z, Steps3 P x z ∧ iterR P refill r (j + 1) (refill (j + 1) z) w

/-- ループの中の append: `r` 回のあと、器の内容は `L ++ (各回の要素)`。入る個数・桁あふれの余地があれば、どの回も入る -/
theorem append_rounds (P : Array I3) (b ps pl k t1 t2 te o : Nat)
    (hP : ∀ i (hi : i < (appendCode ps pl k t1 t2 te o).length), P[b + i]? = some (appendCode ps pl k t1 t2 te o)[i])
    (h1 : t1 ≠ ps) (h2 : t2 ≠ pl) (h3 : ps ≠ pl) (h4 : t1 ≠ pl) (h5 : t2 ≠ ps) (h12 : t1 ≠ t2)
    (hte : ∀ i, i < k → te + i ≠ t1 ∧ te + i ≠ t2)
    (vs : Nat → List W) (hvs : ∀ j, (vs j).length = k) (refill : Nat → HSt → HSt)
    (hrefill : ∀ j (z : HSt), z.s.pc = b + 19 + 2 * k →
      (refill j z).s.pc = b ∧ (refill j z).h = z.h ∧ (refill j z).sp = z.sp ∧ (refill j z).s.lr = z.s.lr ∧
      (refill j z).s.stk = z.s.stk ∧ (refill j z).s.m ps = z.s.m ps ∧ (refill j z).s.m pl = z.s.m pl ∧
      ∀ i (hi : i < (vs j).length), (refill j z).s.m (te + i) = (vs j)[i]) :
    ∀ (r j0 : Nat) (x : HSt) (L : List W), x.s.pc = b → AccInv x ps pl L →
      (∀ i (hi : i < (vs j0).length), x.s.m (te + i) = (vs j0)[i]) →
      L.length + r * k < 2 ^ 50 → (x.s.m ps).toNat + 8 * (L.length + r * k) < 2 ^ 64 →
      L.length + r * k ≤ (x.h ((x.s.m ps).toNat / 8 - 1)).toNat →
      ∃ w, iterR P refill r j0 x w ∧ w.s.pc = b ∧ AccInv w ps pl (L ++ accs vs j0 r) := by
  intro r
  induction r with
  | zero =>
      intro j0 x L hpc hacc _ _ _ _
      exact ⟨x, rfl, hpc, by simpa [accs] using hacc⟩
  | succ r ih =>
      intro j0 x L hpc hacc hel hl hp hc
      have hkk : (r + 1) * k = r * k + k := by rw [Nat.succ_mul]
      obtain ⟨y, g, ypc, yacc, ymps, ycap, ysp, yl, yk⟩ := append_inv P b ps pl k t1 t2 te o hP x hpc h1 h2 h3 h4 h5 h12 hte
        L (vs j0) (hvs j0) hel hacc (by rw [hkk] at hl; omega) (by rw [hkk] at hp; omega) (by rw [hkk] at hc; omega)
      obtain ⟨rpc, rh, rsp, rl, rk, rps, rpl, rel⟩ := hrefill (j0 + 1) y (by rw [ypc])
      obtain ⟨hal', h8', hlen', hcont'⟩ := yacc
      have hacc' : AccInv (refill (j0 + 1) y) ps pl (L ++ vs j0) := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [rps, ymps]; exact hacc.1
        · rw [rps, ymps]; exact hacc.2.1
        · rw [rpl]; exact hlen'
        · intro i hi; rw [rps, rh]; exact hcont' i hi
      have hlen2 : (L ++ vs j0).length = L.length + k := by simp [hvs]
      obtain ⟨w, hw, wpc, wacc⟩ := ih (j0 + 1) (refill (j0 + 1) y) (L ++ vs j0) rpc hacc' rel
        (by rw [hlen2]; rw [hkk] at hl; omega) (by rw [hlen2, rps, ymps]; rw [hkk] at hp; omega)
        (by
          rw [hlen2, rps, rh, ymps, ycap]
          rw [hkk] at hc; omega)
      refine ⟨w, ⟨y, g, hw⟩, wpc, ?_⟩
      simpa [accs, List.append_assoc] using wacc

/-! ### 文字列と輪

文字列の領域はバイト単位の `hb`(`ldrS`/`strS`。ascii は `ldrb/strb`、utf32 は `ldr w/str w, lsl #2`。リトルエンディアン)、リストの語は `h`。
別の領域として扱う。 -/

theorem rdb_lt (hb : Nat → BitVec 8) : ∀ (w p : Nat), rdb hb p w < 256 ^ w := by
  intro w
  induction w with
  | zero => intro p; simp [rdb]
  | succ w ih =>
      intro p
      have h1 := ih (p + 1)
      have h2 := (hb p).isLt
      have h3 : 256 ^ (w + 1) = 256 ^ w * 256 := Nat.pow_succ ..
      simp only [rdb]
      omega

theorem rdb_byte (hb : Nat → BitVec 8) : ∀ (w p j : Nat), j < w → rdb hb p w / 256 ^ j % 256 = (hb (p + j)).toNat := by
  intro w
  induction w with
  | zero => intro p j hj; omega
  | succ w ih =>
      intro p j hj
      have h2 := (hb p).isLt
      cases j with
      | zero => simp only [rdb]; simp; omega
      | succ j =>
          have e : 256 ^ (j + 1) = 256 * 256 ^ j := by rw [Nat.pow_succ]; omega
          have e2 : (hb p).toNat + 256 * rdb hb (p + 1) w = (hb p).toNat + 256 * rdb hb (p + 1) w := rfl
          have e3 : ((hb p).toNat + 256 * rdb hb (p + 1) w) / 256 = rdb hb (p + 1) w := by omega
          simp only [rdb]
          rw [e, ← Nat.div_div_eq_div_mul, e3]
          have := ih (p + 1) j (by omega)
          rw [this]
          congr 2; omega

/-- 読んだ数をそのまま書き戻すと、元と同じバイトが並ぶ -/
theorem wrb_rdb (hb : Nat → BitVec 8) (s d w : Nat) (j : Nat) (hj : j < w) :
    wrb hb d w (rdb hb s w) (d + j) = hb (s + j) := by
  unfold wrb
  rw [if_pos (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  have : d + j - d = j := by omega
  rw [this]
  have := rdb_byte hb w s j hj
  simpa using this

theorem addr_nat (a i : W) (sh n : Nat) (hi : i.toNat = n) (hb : a.toNat + n * 2 ^ sh < 2 ^ 64) :
    (a + (i <<< sh)).toNat = a.toNat + n * 2 ^ sh := by
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, hi, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]


/-! ### 文字列の写し(`pre_grow` の文字列のループ): ascii は `ldrb/strb`(sh = 0)、utf32 は `ldr w/str w, lsl #2`(sh = 2) -/

def copyLoopS (sh : Nat) : Array I3 :=
  #[I3.cmpU 14 1, I3.bhs 5, I3.ldrS sh 3 0 14, I3.strS sh 3 12 14, I3.addI 14 14 1, I3.base (I2.bk 5)]

theorem copyLoopS_size (sh : Nat) : (copyLoopS sh).size = 6 := rfl

theorem copyLoopS_ok (P : Array I3) (b : Nat) (sh w : Nat) (hw : 2 ^ sh = w) (hw0 : 0 < w)
    (hP : ∀ k x, (copyLoopS sh)[k]? = some x → P[b + k]? = some x)
    (src dst : W) (len : Nat)
    (hs : src.toNat + len * w < 2 ^ 64) (hd : dst.toNat + len * w < 2 ^ 64)
    (hdis : dst.toNat + len * w ≤ src.toNat ∨ src.toNat + len * w ≤ dst.toNat) (hrd : w ≤ 4) :
    ∀ (m : Nat) (x : HSt), len - (x.s.r 14).toNat = m → x.s.pc = b → (x.s.r 14).toNat ≤ len →
      x.s.r 0 = src → x.s.r 1 = BitVec.ofNat 64 len → x.s.r 12 = dst →
      ∃ y, Steps3 P x y ∧ y.s.pc = b + 6 ∧ (y.s.r 14).toNat = len ∧
        (∀ j, (x.s.r 14).toNat * w ≤ j → j < len * w → y.hb (dst.toNat + j) = x.hb (src.toNat + j)) ∧
        (∀ k, (∀ j, (x.s.r 14).toNat * w ≤ j → j < len * w → k ≠ dst.toNat + j) → y.hb k = x.hb k) ∧
        y.h = x.h ∧ y.sp = x.sp ∧ y.s.m = x.s.m ∧ y.s.lr = x.s.lr ∧ y.s.stk = x.s.stk ∧ y.s.r 0 = src ∧ y.s.r 1 = BitVec.ofNat 64 len ∧
        y.s.r 12 = dst := by
  intro m
  induction m with
  | zero =>
      intro x hm hpc hle h0 h1 h12
      have hi : (x.s.r 14).toNat = len := by omega
      have hl64 : len < 2 ^ 64 := by
        have : len ≤ len * w := Nat.le_mul_of_pos_right len hw0
        omega
      have hlt1 : (x.s.r 1).toNat = len := by rw [h1]; simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl64]
      have g1 : Steps3 P x (step3 (I3.cmpU 14 1) x) :=
        Steps3.go' (I3.cmpU 14 1) b hpc (by simpa using hP 0 _ (by simp [copyLoopS])) (Steps3.refl _)
      obtain ⟨x1, hx1⟩ : ∃ x1, x1 = step3 (I3.cmpU 14 1) x := ⟨_, rfl⟩
      have c1 : x1.c = true := by simp [hx1, step3, hlt1, hi]
      have p1 : x1.s.pc = b + 1 := by simp [hx1, step3, hpc]
      have s1 : x1.s.r = x.s.r := by simp [hx1, step3]
      rw [← hx1] at g1
      obtain ⟨x2, hx2⟩ : ∃ x2, x2 = step3 (I3.bhs 5) x1 := ⟨_, rfl⟩
      have g2 : Steps3 P x1 x2 := by
        rw [hx2]; exact Steps3.go' (I3.bhs 5) (b + 1) p1 (by simpa using hP 1 _ (by simp [copyLoopS])) (Steps3.refl _)
      have hx1h : x1.h = x.h := by simp [hx1, step3]
      have hx1b : x1.hb = x.hb := by simp [hx1, step3]
      have hx2e : x2 = { x1 with s := { x1.s with pc := x1.s.pc + 5 } } := by rw [hx2]; simp [step3, c1]
      have e1m : x1.s.m = x.s.m := by simp [hx1, step3]
      have e1l : x1.s.lr = x.s.lr := by simp [hx1, step3]
      have e1k : x1.s.stk = x.s.stk := by simp [hx1, step3]
      have e1s : x1.sp = x.sp := by simp [hx1, step3]
      refine ⟨x2, g1.trans g2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hx2e, p1]
      · simp [hx2e, s1, hi]
      · intro j hj1 hj2; rw [hi] at hj1; omega
      · intro k _; simp [hx2e, hx1b]
      · simp [hx2e, hx1h]
      · simp [hx2e, e1s]
      · simp [hx2e, e1m]
      · simp [hx2e, e1l]
      · simp [hx2e, e1k]
      · simp [hx2e, s1, h0]
      · simp [hx2e, s1, h1]
      · simp [hx2e, s1, h12]
  | succ m ih =>
      intro x hm hpc hle h0 h1 h12
      have hl64 : len < 2 ^ 64 := by
        have : len ≤ len * w := Nat.le_mul_of_pos_right len hw0
        omega
      have hlt1 : (x.s.r 1).toNat = len := by rw [h1]; simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl64]
      have hilt : (x.s.r 14).toNat < len := by omega
      obtain ⟨i, hi⟩ : ∃ i, i = (x.s.r 14).toNat := ⟨_, rfl⟩
      have hiw : (i + 1) * w = i * w + w := by rw [Nat.add_mul]; simp
      have hlw : (i + 1) * w ≤ len * w := Nat.mul_le_mul_right w (by omega : i + 1 ≤ len)
      have g1 : Steps3 P x (step3 (I3.cmpU 14 1) x) :=
        Steps3.go' (I3.cmpU 14 1) b hpc (by simpa using hP 0 _ (by simp [copyLoopS])) (Steps3.refl _)
      obtain ⟨x1, hx1⟩ : ∃ x1, x1 = step3 (I3.cmpU 14 1) x := ⟨_, rfl⟩
      have c1 : x1.c = false := by simp [hx1, step3, hlt1]; omega
      have p1 : x1.s.pc = b + 1 := by simp [hx1, step3, hpc]
      have f1r : x1.s.r = x.s.r := by simp [hx1, step3]
      have f1h : x1.h = x.h := by simp [hx1, step3]
      have f1b : x1.hb = x.hb := by simp [hx1, step3]
      have f1sp : x1.sp = x.sp := by simp [hx1, step3]
      have f1m : x1.s.m = x.s.m := by simp [hx1, step3]
      have f1l : x1.s.lr = x.s.lr := by simp [hx1, step3]
      have f1k : x1.s.stk = x.s.stk := by simp [hx1, step3]
      rw [← hx1] at g1
      obtain ⟨x2, hx2⟩ : ∃ x2, x2 = step3 (I3.bhs 5) x1 := ⟨_, rfl⟩
      have g2 : Steps3 P x1 x2 := by
        rw [hx2]; exact Steps3.go' (I3.bhs 5) (b + 1) p1 (by simpa using hP 1 _ (by simp [copyLoopS])) (Steps3.refl _)
      have hx2e : x2 = { x1 with s := { x1.s with pc := x1.s.pc + 1 } } := by rw [hx2]; simp [step3, c1]
      have p2 : x2.s.pc = b + 2 := by simp [hx2e, p1]
      have f2r : x2.s.r = x.s.r := by simp [hx2e, f1r]
      have f2h : x2.h = x.h := by simp [hx2e, f1h]
      have f2b : x2.hb = x.hb := by simp [hx2e, f1b]
      have f2sp : x2.sp = x.sp := by simp [hx2e, f1sp]
      have f2m : x2.s.m = x.s.m := by simp [hx2e, f1m]
      have f2l : x2.s.lr = x.s.lr := by simp [hx2e, f1l]
      have f2k : x2.s.stk = x.s.stk := by simp [hx2e, f1k]
      obtain ⟨x3, hx3⟩ : ∃ x3, x3 = step3 (I3.ldrS sh 3 0 14) x2 := ⟨_, rfl⟩
      have g3 : Steps3 P x2 x3 := by
        rw [hx3]; exact Steps3.go' (I3.ldrS sh 3 0 14) (b + 2) p2 (by simpa using hP 2 _ (by simp [copyLoopS])) (Steps3.refl _)
      have hiw' : i * w ≤ len * w := Nat.mul_le_mul_right w (by omega)
      have hadr : (x.s.r 0 + (x.s.r 14 <<< sh)).toNat = src.toNat + i * w := by
        have := addr_nat (x.s.r 0) (x.s.r 14) sh i hi.symm (by rw [h0, hw]; omega)
        rw [this, h0, hw]
      have p3 : x3.s.pc = b + 3 := by simp [hx3, step3, p2]
      have f3h : x3.h = x.h := by simp [hx3, step3, f2h]
      have f3b : x3.hb = x.hb := by simp [hx3, step3, f2b]
      have f3sp : x3.sp = x.sp := by simp [hx3, step3, f2sp]
      have f3m : x3.s.m = x.s.m := by simp [hx3, step3, f2m]
      have f3l : x3.s.lr = x.s.lr := by simp [hx3, step3, f2l]
      have f3k : x3.s.stk = x.s.stk := by simp [hx3, step3, f2k]
      have r3 : x3.s.r 3 = BitVec.ofNat 64 (rdb x.hb (src.toNat + i * w) w) := by
        have e : x3.s.r 3 = BitVec.ofNat 64 (rdb x2.hb (x2.s.r 0 + (x2.s.r 14 <<< sh)).toNat (2 ^ sh)) := by
          rw [hx3]; rfl
        rw [e, f2r, f2b, hadr, hw]
      have s3 : ∀ j, j ≠ 3 → x3.s.r j = x.s.r j := by
        intro j hj; simp [hx3, step3, St.set, f2r, hj]
      have hr3n : (x3.s.r 3).toNat = rdb x.hb (src.toNat + i * w) w := by
        rw [r3, BitVec.toNat_ofNat]
        apply Nat.mod_eq_of_lt
        have := rdb_lt x.hb w (src.toNat + i * w)
        have h256 : 256 ^ w ≤ 256 ^ 4 := Nat.pow_le_pow_right (by omega) hrd
        have : (256 : Nat) ^ 4 < 2 ^ 64 := by decide
        omega
      obtain ⟨x4, hx4⟩ : ∃ x4, x4 = step3 (I3.strS sh 3 12 14) x3 := ⟨_, rfl⟩
      have g4 : Steps3 P x3 x4 := by
        rw [hx4]; exact Steps3.go' (I3.strS sh 3 12 14) (b + 3) p3 (by simpa using hP 3 _ (by simp [copyLoopS])) (Steps3.refl _)
      have hadr2 : (x3.s.r 12 + (x3.s.r 14 <<< sh)).toNat = dst.toNat + i * w := by
        rw [s3 12 (by omega), s3 14 (by omega), h12]
        have := addr_nat dst (x.s.r 14) sh i hi.symm (by rw [hw]; omega)
        rw [this, hw]
      have f4b : ∀ k, x4.hb k = wrb x.hb (dst.toNat + i * w) w (rdb x.hb (src.toNat + i * w) w) k := by
        intro k; simp only [hx4, step3, hadr2, hw, f3b, hr3n]
      have p4 : x4.s.pc = b + 4 := by simp [hx4, step3, p3]
      have f4r : x4.s.r = x3.s.r := by simp [hx4, step3]
      have f4h : x4.h = x.h := by simp [hx4, step3, f3h]
      have f4sp : x4.sp = x.sp := by simp [hx4, step3, f3sp]
      have f4m : x4.s.m = x.s.m := by simp [hx4, step3, f3m]
      have f4l : x4.s.lr = x.s.lr := by simp [hx4, step3, f3l]
      have f4k : x4.s.stk = x.s.stk := by simp [hx4, step3, f3k]
      obtain ⟨x5, hx5⟩ : ∃ x5, x5 = step3 (I3.addI 14 14 1) x4 := ⟨_, rfl⟩
      have g5 : Steps3 P x4 x5 := by
        rw [hx5]; exact Steps3.go' (I3.addI 14 14 1) (b + 4) p4 (by simpa using hP 4 _ (by simp [copyLoopS])) (Steps3.refl _)
      have p5 : x5.s.pc = b + 5 := by simp [hx5, step3, p4]
      have f5h : x5.h = x.h := by simp [hx5, step3, f4h]
      have f5b : x5.hb = x4.hb := by simp [hx5, step3]
      have f5sp : x5.sp = x.sp := by simp [hx5, step3, f4sp]
      have f5m : x5.s.m = x.s.m := by simp [hx5, step3, f4m]
      have f5l : x5.s.lr = x.s.lr := by simp [hx5, step3, f4l]
      have f5k : x5.s.stk = x.s.stk := by simp [hx5, step3, f4k]
      have r5 : ∀ j, j ≠ 3 → j ≠ 14 → x5.s.r j = x.s.r j := by
        intro j hi3 hj
        simp [hx5, step3, St.set, f4r, hj]
        exact s3 j hi3
      have r14 : (x5.s.r 14).toNat = i + 1 := by
        have e14 : x5.s.r 14 = x.s.r 14 + BitVec.ofNat 64 1 := by
          simp [hx5, step3, St.set, f4r, s3 14 (by omega)]
        rw [e14, BitVec.toNat_add]; simp
        omega
      obtain ⟨x6, hx6⟩ : ∃ x6, x6 = step3 (I3.base (I2.bk 5)) x5 := ⟨_, rfl⟩
      have g6 : Steps3 P x5 x6 := by
        rw [hx6]; exact Steps3.go' (I3.base (I2.bk 5)) (b + 5) p5 (by simpa using hP 5 _ (by simp [copyLoopS])) (Steps3.refl _)
      have p6 : x6.s.pc = b := by simp [hx6, step3, step2, p5]
      have f6r : x6.s.r = x5.s.r := by simp [hx6, step3, step2]
      have f6h : x6.h = x.h := by simp [hx6, step3, f5h]
      have f6b : x6.hb = x5.hb := by simp [hx6, step3]
      have f6sp : x6.sp = x.sp := by simp [hx6, step3, f5sp]
      have f6m : x6.s.m = x.s.m := by simp [hx6, step3, step2, f5m]
      have f6l : x6.s.lr = x.s.lr := by simp [hx6, step3, step2, f5l]
      have f6k : x6.s.stk = x.s.stk := by simp [hx6, step3, step2, f5k]
      have hm' : len - (x6.s.r 14).toNat = m := by rw [f6r, r14]; omega
      have hr0 : x6.s.r 0 = src := by rw [f6r, r5 0 (by omega) (by omega), h0]
      have hr1 : x6.s.r 1 = BitVec.ofNat 64 len := by rw [f6r, r5 1 (by omega) (by omega), h1]
      have hr12 : x6.s.r 12 = dst := by rw [f6r, r5 12 (by omega) (by omega), h12]
      obtain ⟨y, hy, ypc, y14, yh1, yh2, yhh, ysp, ym, ylr, ystk, y0, y1, y12⟩ :=
        ih x6 hm' p6 (by rw [f6r, r14]; omega) hr0 hr1 hr12
      have hx6b : ∀ k, x6.hb k = wrb x.hb (dst.toNat + i * w) w (rdb x.hb (src.toNat + i * w) w) k := by
        intro k; rw [f6b, f5b]; exact f4b k
      have r14x : (x6.s.r 14).toNat = i + 1 := by rw [f6r, r14]
      rw [r14x] at yh1 yh2
      refine ⟨y, g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans hy))))), ypc, y14, ?_, ?_, by rw [yhh, f6h], by rw [ysp, f6sp], by rw [ym, f6m],
        by rw [ylr, f6l], by rw [ystk, f6k], y0, y1, y12⟩
      · intro j hj1 hj2
        rw [← hi] at hj1
        by_cases hji : j < i * w + w
        · rw [yh2 (dst.toNat + j) (by intro j' hj' _; omega), hx6b]
          have hj' : j - i * w < w := by omega
          have := wrb_rdb x.hb (src.toNat + i * w) (dst.toNat + i * w) w (j - i * w) hj'
          have e1 : dst.toNat + i * w + (j - i * w) = dst.toNat + j := by omega
          have e2 : src.toNat + i * w + (j - i * w) = src.toNat + j := by omega
          rw [e1, e2] at this; exact this
        · rw [yh1 j (by omega) hj2, hx6b]
          unfold wrb
          rw [if_neg]
          intro hc
          omega
      · intro k hk
        rw [yh2 k (by intro j hj1 hj2; exact hk j (by rw [← hi]; omega) hj2), hx6b]
        unfold wrb
        rw [if_neg]
        intro hc
        have := hk (k - dst.toNat) (by rw [← hi]; omega) (by omega)
        omega


theorem bytes_gen (nW : W) (nN sh : Nat) (h : nW.toNat = nN) (hlt : nN * 2 ^ sh < 2 ^ 50) :
    (((((nW <<< sh) + BitVec.ofNat 64 15) >>> 4) <<< 4) + BitVec.ofNat 64 16).toNat = ((nN * 2 ^ sh + 15) / 16) * 16 + 16 := by
  have e1 : (nW <<< sh).toNat = nN * 2 ^ sh := by
    rw [BitVec.toNat_shiftLeft, h, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega)]
  have e2 : ((nW <<< sh) + BitVec.ofNat 64 15).toNat = nN * 2 ^ sh + 15 := by
    rw [BitVec.toNat_add, e1]; simp; omega
  have e3 : (((nW <<< sh) + BitVec.ofNat 64 15) >>> 4).toNat = (nN * 2 ^ sh + 15) / 16 := by
    rw [BitVec.toNat_ushiftRight, e2, Nat.shiftRight_eq_div_pow]
  have e4 : ((((nW <<< sh) + BitVec.ofNat 64 15) >>> 4) <<< 4).toNat = ((nN * 2 ^ sh + 15) / 16) * 16 := by
    rw [BitVec.toNat_shiftLeft, e3, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add, e4]; simp; omega

/-- 作業領域を取る入口の後ろ半分: 文字数 `n` が `x9` に入っているところから(`mov x10,x9` から)。
`n` 文字ぶんを `sh`(ascii 0・utf32 2)のバイト幅で数え、16 に切り上げ + 16 バイトを `sp` から取り、先頭の 8 バイト前に `n` を置く。 -/
def growTail (cp cl sh : Nat) : List I3 :=
  [I3.base (I2.base (I.mov 10 9)),
   I3.lslI 9 9 sh, I3.addI 9 9 15, I3.lsrI 9 9 4, I3.lslI 9 9 4, I3.addI 9 9 16, I3.subSp 9, I3.spAdd 12 16,
   I3.strN 10 12 8, I3.base (I2.base (I.ldr 0 cp)), I3.base (I2.base (I.ldr 1 cl)), I3.base (I2.base (I.movi 14 0))]

def growCodeS (cp cl sh : Nat) : Array I3 :=
  (growTail cp cl sh).toArray ++ copyLoopS sh ++ #[I3.base (I2.base (I.str 12 cp))]

theorem growTail_len (cp cl sh : Nat) : (growTail cp cl sh).length = 12 := rfl

theorem growTail_nobr (cp cl sh : Nat) : ∀ i ∈ growTail cp cl sh, nobr i := by
  intro i hi
  simp [growTail] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [nobr]

theorem growCodeS_pre (cp cl sh : Nat) (k : Nat) (hk : k < 12) :
    (growCodeS cp cl sh)[k]? = (growTail cp cl sh)[k]? := by
  have hA : (growTail cp cl sh).toArray.size = 12 := by simp [growTail_len]
  unfold growCodeS
  rw [Array.getElem?_append_left (by simp [hA, copyLoopS_size]; omega), Array.getElem?_append_left (by omega)]
  simp

theorem growCodeS_loop (cp cl sh : Nat) (k : Nat) (x : I3) (h : (copyLoopS sh)[k]? = some x) :
    (growCodeS cp cl sh)[12 + k]? = some x := by
  have hA : (growTail cp cl sh).toArray.size = 12 := by simp [growTail_len]
  have hk : k < 6 := by
    cases Nat.lt_or_ge k 6 with
    | inl h' => exact h'
    | inr h' => rw [Array.getElem?_eq_none (by rw [copyLoopS_size]; exact h')] at h; cases h
  unfold growCodeS
  rw [Array.getElem?_append_left (by simp [hA, copyLoopS_size]; omega), Array.getElem?_append_right (by omega)]
  rw [hA, show 12 + k - 12 = k by omega]; exact h

theorem growCodeS_last (cp cl sh : Nat) : (growCodeS cp cl sh)[18]? = some (I3.base (I2.base (I.str 12 cp))) := by
  have hA : (growTail cp cl sh).toArray.size = 12 := by simp [growTail_len]
  unfold growCodeS
  rw [Array.getElem?_append_right (by simp [hA, copyLoopS_size])]
  simp [hA, copyLoopS_size]


/-- 文字列の入口の後ろ半分(`pre_grow` の文字列の枝): `x9 = n`(文字数)から作業領域を取り、累積を文字ごとに写し、仮引数を作業領域へ向ける。
`w = 2^sh`(ascii 1・utf32 4)バイト幅。領域は `sp` から `((n·w+15)/16)×16 + 16` バイト下で、先頭の 8 バイト前(語のメモリ `h`)に `n` が入る。
元の文字列(`sp` 以上)・`sp` 以上のバイト・ほかの枠・`lr`・フレームは変わらない。 -/
theorem growTailS_ok (P : Array I3) (b : Nat) (cp cl sh w nN : Nat) (hw : 2 ^ sh = w) (hw0 : 0 < w) (hrd : w ≤ 4)
    (hP : ∀ k x, (growCodeS cp cl sh)[k]? = some x → P[b + k]? = some x)
    (x : HSt) (hpc : x.s.pc = b) (hR9 : x.s.r 9 = BitVec.ofNat 64 nN)
    (hn : nN * w < 2 ^ 50) (hlen : (x.s.m cl).toNat ≤ nN)
    (hsrc : x.sp.toNat ≤ (x.s.m cp).toNat)
    (hs : (x.s.m cp).toNat + (x.s.m cl).toNat * w < 2 ^ 64)
    (hsp : x.sp.toNat % 16 = 0) (hroom : nN * w + 32 ≤ x.sp.toNat) :
    ∃ y, Steps3 P x y ∧ y.s.pc = b + 18 + 1 ∧
      y.sp.toNat = x.sp.toNat - (((nN * w + 15) / 16) * 16 + 16) ∧
      (y.s.m cp).toNat = y.sp.toNat + 16 ∧ (∀ i, i ≠ cp → y.s.m i = x.s.m i) ∧
      y.h ((y.sp.toNat + 16) / 8 - 1) = BitVec.ofNat 64 nN ∧
      (∀ j, j < (x.s.m cl).toNat * w → y.hb (y.sp.toNat + 16 + j) = x.hb ((x.s.m cp).toNat + j)) ∧
      (∀ k, x.sp.toNat ≤ k → y.hb k = x.hb k) ∧
      (∀ k, x.sp.toNat / 8 ≤ k → y.h k = x.h k) ∧ y.s.lr = x.s.lr ∧ y.s.stk = x.s.stk := by
  have hnlt : nN < 2 ^ 50 := by
    have : nN ≤ nN * w := Nat.le_mul_of_pos_right nN hw0
    omega
  have hclw : (x.s.m cl).toNat * w ≤ nN * w := Nat.mul_le_mul_right w hlen
  obtain ⟨x12, hx12⟩ : ∃ x12, x12 = runL (growTail cp cl sh) x := ⟨_, rfl⟩
  obtain ⟨g1, p1⟩ := runL_ok P b (growTail cp cl sh) x 0 (by simpa using hpc) (growTail_nobr cp cl sh)
    (fun k hk => by
      have hk' : k < 12 := by simpa [growTail_len] using hk
      have := hP k ((growTail cp cl sh)[k]) (by rw [growCodeS_pre cp cl sh k hk']; exact List.getElem?_eq_getElem hk)
      exact this)
  rw [← hx12] at g1 p1
  simp [growTail_len] at p1
  have fr12 : x12.s.r 12 = x.sp - ((((x.s.r 9 <<< sh) + BitVec.ofNat 64 15) >>> 4 <<< 4) + BitVec.ofNat 64 16) + BitVec.ofNat 64 16 := by
    rw [hx12]; rfl
  have fr0 : x12.s.r 0 = x.s.m cp := by rw [hx12]; rfl
  have fr1 : x12.s.r 1 = x.s.m cl := by rw [hx12]; rfl
  have fr14 : x12.s.r 14 = 0 := by rw [hx12]; rfl
  have fsp : x12.sp = x.sp - ((((x.s.r 9 <<< sh) + BitVec.ofNat 64 15) >>> 4 <<< 4) + BitVec.ofNat 64 16) := by
    rw [hx12]; rfl
  have fm : x12.s.m = x.s.m := by rw [hx12]; rfl
  have fl : x12.s.lr = x.s.lr := by rw [hx12]; rfl
  have fk : x12.s.stk = x.s.stk := by rw [hx12]; rfl
  have fb : x12.hb = x.hb := by rw [hx12]; rfl
  have fh : x12.h = fun k => if k = (x12.s.r 12 - BitVec.ofNat 64 8).toNat / 8 then x.s.r 9 else x.h k := by
    rw [hx12]; rfl
  have hnW : (x.s.r 9).toNat = nN := by rw [hR9, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hB := bytes_gen (x.s.r 9) nN sh hnW (by rw [hw]; omega)
  obtain ⟨Bw, hBw⟩ : ∃ Bw : W, Bw = ((((x.s.r 9 <<< sh) + BitVec.ofNat 64 15) >>> 4 <<< 4) + BitVec.ofNat 64 16) := ⟨_, rfl⟩
  rw [← hBw] at fsp fr12 hB
  have hBn : Bw.toNat = (nN * w + 15) / 16 * 16 + 16 := by rw [hB, hw]
  have hspN : x12.sp.toNat = x.sp.toNat - Bw.toNat := by
    rw [fsp, BitVec.toNat_sub]; omega
  have hdst : (x12.s.r 12).toNat = x.sp.toNat - Bw.toNat + 16 := by
    rw [fr12, BitVec.toNat_add, BitVec.toNat_sub]
    simp
    omega
  obtain ⟨y, gy, ypc, y14, yb1, yb2, yhh, ysp, ym, ylr, ystk, y0, y1, y12⟩ :=
    copyLoopS_ok P (b + 12) sh w hw hw0
      (fun k x' hk => by
        have := hP (12 + k) x' (growCodeS_loop cp cl sh k x' hk)
        rw [← Nat.add_assoc] at this; exact this)
      (x.s.m cp) (x12.s.r 12) (x.s.m cl).toNat hs (by rw [hdst]; omega)
      (Or.inl (by rw [hdst]; omega)) hrd _ x12 rfl (by rw [p1]) (by rw [fr14]; simp) fr0
      (by rw [fr1]; simp) rfl
  have g2 : Steps3 P y (step3 (I3.base (I2.base (I.str 12 cp))) y) :=
    Steps3.go' _ (b + 18) (by rw [ypc]) (by have := hP 18 _ (growCodeS_last cp cl sh); exact this) (Steps3.refl _)
  obtain ⟨Y, hY⟩ : ∃ Y, Y = step3 (I3.base (I2.base (I.str 12 cp))) y := ⟨_, rfl⟩
  rw [← hY] at g2
  have Yh : Y.h = y.h := by rw [hY]; rfl
  have Yb : Y.hb = y.hb := by rw [hY]; rfl
  have Ysp : Y.sp = y.sp := by rw [hY]; rfl
  have Ym : ∀ i, Y.s.m i = if i = cp then y.s.r 12 else y.s.m i := by intro i; rw [hY]; rfl
  have Ylr : Y.s.lr = y.s.lr := by rw [hY]; rfl
  have Ystk : Y.s.stk = y.s.stk := by rw [hY]; rfl
  have Ypc : Y.s.pc = b + 18 + 1 := by rw [hY]; simp [step3, step2, step, ypc]
  have hd12 : (y.s.r 12).toNat = x.sp.toNat - Bw.toNat + 16 := by rw [y12, hdst]
  have hysp : y.sp.toNat = x.sp.toNat - Bw.toNat := by rw [ysp, hspN]
  have hd8 : (x12.s.r 12 - BitVec.ofNat 64 8).toNat = x.sp.toNat - Bw.toNat + 8 := by
    rw [BitVec.toNat_sub, hdst]; simp; omega
  have hx12h : ∀ k, x12.h k = if k = (x.sp.toNat - Bw.toNat + 8) / 8 then BitVec.ofNat 64 nN else x.h k := by
    intro k; rw [fh]; simp only [hd8, hR9]
  refine ⟨Y, g1.trans (gy.trans g2), Ypc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Ysp, hysp, hBn]
  · rw [Ym, if_pos rfl, Ysp, hd12, hysp]
  · intro i hi; rw [Ym, if_neg hi, ym, fm]
  · rw [Yh, Ysp, hysp, yhh]
    have hk : (x.sp.toNat - Bw.toNat + 16) / 8 - 1 = (x.sp.toNat - Bw.toNat + 8) / 8 := by omega
    rw [hk, hx12h]; simp
  · intro j hj
    rw [Yb, Ysp, hysp]
    have := yb1 j (by rw [fr14]; simp) hj
    rw [hdst] at this
    rw [this, fb]
  · intro k hk
    rw [Yb, yb2 k (by intro j hj1 hj2; rw [hdst]; omega), fb]
  · intro k hk
    rw [Yh, yhh, hx12h]
    have hne : k ≠ (x.sp.toNat - Bw.toNat + 8) / 8 := by omega
    rw [if_neg hne]
  · rw [Ylr, ylr, fl]
  · rw [Ystk, ystk, fk]


def growCodeL (cp cl : Nat) : Array I3 :=
  (growTail cp cl 3).toArray ++ copyLoop ++ #[I3.base (I2.base (I.str 12 cp))]

theorem growCodeL_pre (cp cl : Nat) (k : Nat) (hk : k < 12) :
    (growCodeL cp cl)[k]? = (growTail cp cl 3)[k]? := by
  have hA : (growTail cp cl 3).toArray.size = 12 := by simp [growTail_len]
  unfold growCodeL
  rw [Array.getElem?_append_left (by simp [hA, copyLoop_size]; omega), Array.getElem?_append_left (by omega)]
  simp

theorem growCodeL_loop (cp cl : Nat) (k : Nat) (x : I3) (h : copyLoop[k]? = some x) :
    (growCodeL cp cl)[12 + k]? = some x := by
  have hA : (growTail cp cl 3).toArray.size = 12 := by simp [growTail_len]
  have hk : k < 6 := by
    cases Nat.lt_or_ge k 6 with
    | inl h' => exact h'
    | inr h' => rw [Array.getElem?_eq_none (by rw [copyLoop_size]; exact h')] at h; cases h
  unfold growCodeL
  rw [Array.getElem?_append_left (by simp [hA, copyLoop_size]; omega), Array.getElem?_append_right (by omega)]
  rw [hA, show 12 + k - 12 = k by omega]; exact h

theorem growCodeL_last (cp cl : Nat) : (growCodeL cp cl)[18]? = some (I3.base (I2.base (I.str 12 cp))) := by
  have hA : (growTail cp cl 3).toArray.size = 12 := by simp [growTail_len]
  unfold growCodeL
  rw [Array.getElem?_append_right (by simp [hA, copyLoop_size])]
  simp [hA, copyLoop_size]

/-- リストの入口の後ろ半分(`x9 = n`(要素数)から)。`growEntry_ok` の後ろ半分と同じ結論 -/
theorem growTailL_ok (P : Array I3) (b : Nat) (cp cl nN : Nat)
    (hP : ∀ k x, (growCodeL cp cl)[k]? = some x → P[b + k]? = some x)
    (x : HSt) (hpc : x.s.pc = b) (hR9 : x.s.r 9 = BitVec.ofNat 64 nN)
    (hn : nN < 2 ^ 50) (hlen : (x.s.m cl).toNat ≤ nN)
    (hsa : (x.s.m cp).toNat % 8 = 0) (hsrc : x.sp.toNat ≤ (x.s.m cp).toNat)
    (hs : (x.s.m cp).toNat + 8 * (x.s.m cl).toNat < 2 ^ 64)
    (hsp : x.sp.toNat % 16 = 0) (hroom : 8 * nN + 32 ≤ x.sp.toNat) :
    ∃ y, Steps3 P x y ∧ y.s.pc = b + 19 ∧
      y.sp.toNat = x.sp.toNat - (((8 * nN + 15) / 16) * 16 + 16) ∧
      (y.s.m cp).toNat = y.sp.toNat + 16 ∧ (∀ i, i ≠ cp → y.s.m i = x.s.m i) ∧
      y.h ((y.sp.toNat + 16) / 8 - 1) = BitVec.ofNat 64 nN ∧
      (∀ j, j < (x.s.m cl).toNat → y.h ((y.sp.toNat + 16) / 8 + j) = x.h ((x.s.m cp).toNat / 8 + j)) ∧
      (∀ k, x.sp.toNat / 8 ≤ k → y.h k = x.h k) ∧ y.s.lr = x.s.lr ∧ y.s.stk = x.s.stk := by
  obtain ⟨x12, hx12⟩ : ∃ x12, x12 = runL (growTail cp cl 3) x := ⟨_, rfl⟩
  obtain ⟨g1, p1⟩ := runL_ok P b (growTail cp cl 3) x 0 (by simpa using hpc) (growTail_nobr cp cl 3)
    (fun k hk => by
      have hk' : k < 12 := by simpa [growTail_len] using hk
      have := hP k ((growTail cp cl 3)[k]) (by rw [growCodeL_pre cp cl k hk']; exact List.getElem?_eq_getElem hk)
      exact this)
  rw [← hx12] at g1 p1
  simp [growTail_len] at p1
  have fr12 : x12.s.r 12 = x.sp - ((((x.s.r 9 <<< 3) + BitVec.ofNat 64 15) >>> 4 <<< 4) + BitVec.ofNat 64 16) + BitVec.ofNat 64 16 := by
    rw [hx12]; rfl
  have fr0 : x12.s.r 0 = x.s.m cp := by rw [hx12]; rfl
  have fr1 : x12.s.r 1 = x.s.m cl := by rw [hx12]; rfl
  have fr14 : x12.s.r 14 = 0 := by rw [hx12]; rfl
  have fsp : x12.sp = x.sp - ((((x.s.r 9 <<< 3) + BitVec.ofNat 64 15) >>> 4 <<< 4) + BitVec.ofNat 64 16) := by
    rw [hx12]; rfl
  have fm : x12.s.m = x.s.m := by rw [hx12]; rfl
  have fl : x12.s.lr = x.s.lr := by rw [hx12]; rfl
  have fk : x12.s.stk = x.s.stk := by rw [hx12]; rfl
  have fh : x12.h = fun k => if k = (x12.s.r 12 - BitVec.ofNat 64 8).toNat / 8 then x.s.r 9 else x.h k := by
    rw [hx12]; rfl
  have hnW : (x.s.r 9).toNat = nN := by rw [hR9, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hB := bytes_w (x.s.r 9) nN hnW hn
  obtain ⟨Bw, hBw⟩ : ∃ Bw : W, Bw = ((((x.s.r 9 <<< 3) + BitVec.ofNat 64 15) >>> 4 <<< 4) + BitVec.ofNat 64 16) := ⟨_, rfl⟩
  rw [← hBw] at fsp fr12 hB
  have hBn : Bw.toNat = (8 * nN + 15) / 16 * 16 + 16 := hB
  have hspN : x12.sp.toNat = x.sp.toNat - Bw.toNat := by
    rw [fsp, BitVec.toNat_sub]; omega
  have hdst : (x12.s.r 12).toNat = x.sp.toNat - Bw.toNat + 16 := by
    rw [fr12, BitVec.toNat_add, BitVec.toNat_sub]
    simp
    omega
  obtain ⟨y, gy, ypc, y14, yh1, yh2, ysp, ym, ylr, ystk, y0, y1, y12⟩ :=
    copyLoop_ok P (b + 12) (fun k x' hk => by
        have := hP (12 + k) x' (growCodeL_loop cp cl k x' hk)
        rw [← Nat.add_assoc] at this; exact this)
      (x.s.m cp) (x12.s.r 12) (x.s.m cl).toNat hsa (by rw [hdst]; omega) hs (by rw [hdst]; omega)
      (Or.inl (by rw [hdst]; omega)) _ x12 rfl (by rw [p1]) (by rw [fr14]; simp) fr0
      (by rw [fr1]; simp) rfl
  have g2 : Steps3 P y (step3 (I3.base (I2.base (I.str 12 cp))) y) :=
    Steps3.go' _ (b + 18) (by rw [ypc]) (by have := hP 18 _ (growCodeL_last cp cl); exact this) (Steps3.refl _)
  obtain ⟨Y, hY⟩ : ∃ Y, Y = step3 (I3.base (I2.base (I.str 12 cp))) y := ⟨_, rfl⟩
  rw [← hY] at g2
  have Yh : Y.h = y.h := by rw [hY]; rfl
  have Ysp : Y.sp = y.sp := by rw [hY]; rfl
  have Ym : ∀ i, Y.s.m i = if i = cp then y.s.r 12 else y.s.m i := by intro i; rw [hY]; rfl
  have Ylr : Y.s.lr = y.s.lr := by rw [hY]; rfl
  have Ystk : Y.s.stk = y.s.stk := by rw [hY]; rfl
  have Ypc : Y.s.pc = b + 19 := by rw [hY]; simp [step3, step2, step, ypc]
  have hd12 : (y.s.r 12).toNat = x.sp.toNat - Bw.toNat + 16 := by rw [y12, hdst]
  have hysp : y.sp.toNat = x.sp.toNat - Bw.toNat := by rw [ysp, hspN]
  have hd8 : (x12.s.r 12 - BitVec.ofNat 64 8).toNat = x.sp.toNat - Bw.toNat + 8 := by
    rw [BitVec.toNat_sub, hdst]; simp; omega
  have hx12h : ∀ k, x12.h k = if k = (x.sp.toNat - Bw.toNat + 8) / 8 then BitVec.ofNat 64 nN else x.h k := by
    intro k; rw [fh]; simp only [hd8, hR9]
  refine ⟨Y, g1.trans (gy.trans g2), Ypc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Ysp, hysp, hBn]
  · rw [Ym, if_pos rfl, Ysp, hd12, hysp]
  · intro i hi; rw [Ym, if_neg hi, ym, fm]
  · rw [Yh, Ysp, hysp]
    have hk : (x.sp.toNat - Bw.toNat + 16) / 8 - 1 = (x.sp.toNat - Bw.toNat + 8) / 8 := by omega
    rw [hk, yh2 _ (by intro j hj1 hj2; omega), hx12h]; simp
  · intro j hj
    rw [Yh, Ysp, hysp]
    have := yh1 j (by rw [fr14]; simp) hj
    rw [hdst] at this
    rw [this, hx12h]
    have hne : (x.s.m cp).toNat / 8 + j ≠ (x.sp.toNat - Bw.toNat + 8) / 8 := by omega
    rw [if_neg hne]
  · intro k hk
    rw [Yh, yh2 k (by intro j hj1 hj2; rw [hdst]; omega), hx12h]
    have hne : k ≠ (x.sp.toNat - Bw.toNat + 8) / 8 := by omega
    rw [if_neg hne]
  · rw [Ylr, ylr, fl]
  · rw [Ystk, ystk, fk]


/-! ### 輪: 食う器が複数の入口(`pre_grow_one` の `isinstance(e, tuple)` の枝)

作業領域の要素数 `n = ||acc|| + d × (食う器の長さの和)`。`x9 = ||acc||` から食う器ごとに `x10 = 長さ; x11 = d; x10 *= x11; x9 += x10` と足していき、
そのあとは食う器 1 つのときと同じ後ろ半分(`growTail`)。食う器が 1 つなら `growPre` の前半 5 命令と同じ。 -/

def eatI (e d : Nat) : List I3 :=
  [bb (I.ldr 10 e), bb (I.movi 11 d), bb (I.mul 10 10 11), bb (I.adds 9 9 10)]

def sumPre (cl d : Nat) (els : List Nat) : List I3 :=
  bb (I.ldr 9 cl) :: els.flatMap (fun e => eatI e d)

def ringW (m : Nat → W) (d : Nat) : List Nat → W → W
  | [], a => a
  | e :: es, a => ringW m d es (a + m e * BitVec.ofInt 64 d)

theorem eatI_nobr (e d : Nat) : ∀ i ∈ eatI e d, nobr i := by
  intro i hi
  simp [eatI] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> simp [nobr, bb]

theorem sumPre_nobr (cl d : Nat) (els : List Nat) : ∀ i ∈ sumPre cl d els, nobr i := by
  intro i hi
  simp only [sumPre, List.mem_cons, List.mem_flatMap] at hi
  rcases hi with rfl | ⟨e, _, hi⟩
  · simp [nobr, bb]
  · exact eatI_nobr e d i hi

theorem sumPre_len (cl d : Nat) (els : List Nat) : (sumPre cl d els).length = 1 + 4 * els.length := by
  simp only [sumPre, List.length_cons, List.length_flatMap]
  have : ∀ (l : List Nat), (l.map (fun e => (eatI e d).length)).sum = 4 * l.length := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp [eatI] at *; omega
  rw [this]; omega

theorem eat_run (e d : Nat) (y : HSt) :
    (runL (eatI e d) y).s.r 9 = y.s.r 9 + y.s.m e * BitVec.ofInt 64 d ∧ (runL (eatI e d) y).s.m = y.s.m ∧
    (runL (eatI e d) y).sp = y.sp ∧ (runL (eatI e d) y).h = y.h ∧ (runL (eatI e d) y).hb = y.hb ∧
    (runL (eatI e d) y).s.lr = y.s.lr ∧ (runL (eatI e d) y).s.stk = y.s.stk ∧
    (runL (eatI e d) y).s.pc = y.s.pc + 4 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ring_run (d : Nat) : ∀ (els : List Nat) (y : HSt),
    (runL (els.flatMap (fun e => eatI e d)) y).s.r 9 = ringW y.s.m d els (y.s.r 9) ∧
    (runL (els.flatMap (fun e => eatI e d)) y).s.m = y.s.m ∧ (runL (els.flatMap (fun e => eatI e d)) y).sp = y.sp ∧
    (runL (els.flatMap (fun e => eatI e d)) y).h = y.h ∧ (runL (els.flatMap (fun e => eatI e d)) y).hb = y.hb ∧
    (runL (els.flatMap (fun e => eatI e d)) y).s.lr = y.s.lr ∧ (runL (els.flatMap (fun e => eatI e d)) y).s.stk = y.s.stk := by
  intro els
  induction els with
  | nil => intro y; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons e es ih =>
      intro y
      have hrun : runL ((e :: es).flatMap (fun e => eatI e d)) y = runL (es.flatMap (fun e => eatI e d)) (runL (eatI e d) y) := by
        rw [List.flatMap_cons, runL_append]
      rw [hrun]
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := eat_run e d y
      obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := ih (runL (eatI e d) y)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [b1, a2, a1]; rfl
      · rw [b2, a2]
      · rw [b3, a3]
      · rw [b4, a4]
      · rw [b5, a5]
      · rw [b6, a6]
      · rw [b7, a7]

theorem ringW_nat (m : Nat → W) (d : Nat) (hd : d < 2 ^ 50) :
    ∀ (els : List Nat) (a : W), a.toNat + d * (els.map (fun e => (m e).toNat)).sum < 2 ^ 50 →
      (ringW m d els a).toNat = a.toNat + d * (els.map (fun e => (m e).toNat)).sum := by
  intro els
  induction els with
  | nil => intro a _; simp [ringW]
  | cons e es ih =>
      intro a h
      simp only [List.map_cons, List.sum_cons, Nat.mul_add] at h ⊢
      have hEl : (m e * BitVec.ofInt 64 d).toNat = d * (m e).toNat := by
        have : BitVec.ofInt 64 (d : Int) = BitVec.ofNat 64 d := BitVec.ofInt_natCast ..
        have hd64 : d % 2 ^ 64 = d := Nat.mod_eq_of_lt (by omega)
        have hlt : d * (m e).toNat < 2 ^ 64 := by omega
        rw [this, BitVec.toNat_mul, BitVec.toNat_ofNat, hd64, Nat.mul_comm]
        exact Nat.mod_eq_of_lt hlt
      have hs : (a + m e * BitVec.ofInt 64 d).toNat = a.toNat + d * (m e).toNat := by
        rw [BitVec.toNat_add, hEl]; exact Nat.mod_eq_of_lt (by omega)
      simp only [ringW]
      rw [ih _ (by rw [hs]; omega), hs]
      omega


def ringCodeL (cp cl d : Nat) (els : List Nat) : Array I3 := (sumPre cl d els).toArray ++ growCodeL cp cl
def ringCodeS (cp cl d : Nat) (els : List Nat) (sh : Nat) : Array I3 := (sumPre cl d els).toArray ++ growCodeS cp cl sh

theorem ring_pre {α : Type} (A B : Array α) (k : Nat) (hk : k < A.size) : (A ++ B)[k]? = A[k]? := arr_left A B k hk

/-- 前半(食う器の長さの和を `x9` へ): 終わると `x9 = ||acc|| + d × Σ(食う器の長さ)`、メモリ・`sp`・`lr`・フレームは変わらない -/
theorem sumPre_ok (P : Array I3) (b : Nat) (cl d : Nat) (els : List Nat)
    (hP : ∀ k (hk : k < (sumPre cl d els).length), P[b + k]? = some (sumPre cl d els)[k])
    (x : HSt) (hpc : x.s.pc = b) (hd : d < 2 ^ 50)
    (hT : (x.s.m cl).toNat + d * (els.map (fun e => (x.s.m e).toNat)).sum < 2 ^ 50) :
    ∃ z, Steps3 P x z ∧ z.s.pc = b + (1 + 4 * els.length) ∧
      z.s.r 9 = BitVec.ofNat 64 ((x.s.m cl).toNat + d * (els.map (fun e => (x.s.m e).toNat)).sum) ∧
      z.s.m = x.s.m ∧ z.sp = x.sp ∧ z.h = x.h ∧ z.hb = x.hb ∧ z.s.lr = x.s.lr ∧ z.s.stk = x.s.stk := by
  obtain ⟨g, p⟩ := runL_ok P b (sumPre cl d els) x 0 (by simpa using hpc) (sumPre_nobr cl d els) (by simpa using hP)
  rw [sumPre_len] at p
  obtain ⟨x0, hx0⟩ : ∃ x0, x0 = step3 (bb (I.ldr 9 cl)) x := ⟨_, rfl⟩
  have hrun : runL (sumPre cl d els) x = runL (els.flatMap (fun e => eatI e d)) x0 := by
    rw [hx0]; rfl
  have e9 : x0.s.r 9 = x.s.m cl := by rw [hx0]; rfl
  have em : x0.s.m = x.s.m := by rw [hx0]; rfl
  have esp : x0.sp = x.sp := by rw [hx0]; rfl
  have eh : x0.h = x.h := by rw [hx0]; rfl
  have eb : x0.hb = x.hb := by rw [hx0]; rfl
  have el : x0.s.lr = x.s.lr := by rw [hx0]; rfl
  have ek : x0.s.stk = x.s.stk := by rw [hx0]; rfl
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := ring_run d els x0
  rw [← hrun] at r1 r2 r3 r4 r5 r6 r7
  refine ⟨runL (sumPre cl d els) x, g, by simpa using p, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r1, e9, em]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact ringW_nat x.s.m d hd els (x.s.m cl) hT
  · rw [r2, em]
  · rw [r3, esp]
  · rw [r4, eh]
  · rw [r5, eb]
  · rw [r6, el]
  · rw [r7, ek]


theorem ringCodeL_sum (cp cl d : Nat) (els : List Nat) (k : Nat) (hk : k < (sumPre cl d els).length) :
    (ringCodeL cp cl d els)[k]? = some (sumPre cl d els)[k] := by
  unfold ringCodeL
  rw [arr_left _ _ _ (by simpa using hk)]; simp [List.getElem?_eq_getElem hk]

theorem ringCodeL_grow (cp cl d : Nat) (els : List Nat) (k : Nat) :
    (ringCodeL cp cl d els)[(1 + 4 * els.length) + k]? = (growCodeL cp cl)[k]? := by
  unfold ringCodeL
  have : (sumPre cl d els).toArray.size = 1 + 4 * els.length := by simp [sumPre_len]
  rw [← this]; exact arr_right _ _ _

theorem ringCodeS_sum (cp cl d : Nat) (els : List Nat) (sh k : Nat) (hk : k < (sumPre cl d els).length) :
    (ringCodeS cp cl d els sh)[k]? = some (sumPre cl d els)[k] := by
  unfold ringCodeS
  rw [arr_left _ _ _ (by simpa using hk)]; simp [List.getElem?_eq_getElem hk]

theorem ringCodeS_grow (cp cl d : Nat) (els : List Nat) (sh k : Nat) :
    (ringCodeS cp cl d els sh)[(1 + 4 * els.length) + k]? = (growCodeS cp cl sh)[k]? := by
  unfold ringCodeS
  have : (sumPre cl d els).toArray.size = 1 + 4 * els.length := by simp [sumPre_len]
  rw [← this]; exact arr_right _ _ _

/-- 輪(リスト): 食う器が `els`(長さの枠の並び)の入口の全体。作業領域の要素数 `T = ||acc|| + d × Σ(食う器の長さ)` -/
theorem ringEntryL_ok (P : Array I3) (b : Nat) (cp cl d : Nat) (els : List Nat)
    (hP : ∀ k x, (ringCodeL cp cl d els)[k]? = some x → P[b + k]? = some x)
    (x : HSt) (hpc : x.s.pc = b) (hd : d < 2 ^ 50)
    (hn : (x.s.m cl).toNat + d * (els.map (fun e => (x.s.m e).toNat)).sum < 2 ^ 50)
    (hsa : (x.s.m cp).toNat % 8 = 0) (hsrc : x.sp.toNat ≤ (x.s.m cp).toNat)
    (hs : (x.s.m cp).toNat + 8 * (x.s.m cl).toNat < 2 ^ 64)
    (hsp : x.sp.toNat % 16 = 0)
    (hroom : 8 * ((x.s.m cl).toNat + d * (els.map (fun e => (x.s.m e).toNat)).sum) + 32 ≤ x.sp.toNat) :
    ∃ y, Steps3 P x y ∧ y.s.pc = b + (1 + 4 * els.length) + 19 ∧
      y.sp.toNat = x.sp.toNat - (((8 * ((x.s.m cl).toNat + d * (els.map (fun e => (x.s.m e).toNat)).sum) + 15) / 16) * 16 + 16) ∧
      (y.s.m cp).toNat = y.sp.toNat + 16 ∧ (∀ i, i ≠ cp → y.s.m i = x.s.m i) ∧
      y.h ((y.sp.toNat + 16) / 8 - 1) = BitVec.ofNat 64 ((x.s.m cl).toNat + d * (els.map (fun e => (x.s.m e).toNat)).sum) ∧
      (∀ j, j < (x.s.m cl).toNat → y.h ((y.sp.toNat + 16) / 8 + j) = x.h ((x.s.m cp).toNat / 8 + j)) ∧
      (∀ k, x.sp.toNat / 8 ≤ k → y.h k = x.h k) ∧ y.s.lr = x.s.lr ∧ y.s.stk = x.s.stk := by
  obtain ⟨z, gz, zpc, z9, zm, zsp, zh, zhb, zl, zk⟩ := sumPre_ok P b cl d els
    (fun k hk => hP k _ (ringCodeL_sum cp cl d els k hk)) x hpc hd hn
  obtain ⟨y, gy, ypc, ysp, ym, yo, yhead, ycopy, yabove, ylr, ystk⟩ := growTailL_ok P (b + (1 + 4 * els.length)) cp cl
    ((x.s.m cl).toNat + d * (els.map (fun e => (x.s.m e).toNat)).sum)
    (fun k x' hk => by
      have := hP ((1 + 4 * els.length) + k) x' (by rw [ringCodeL_grow]; exact hk)
      rw [← Nat.add_assoc] at this; exact this)
    z zpc z9 hn (by rw [zm]; omega) (by rw [zm]; exact hsa) (by rw [zsp, zm]; exact hsrc) (by rw [zm]; exact hs)
    (by rw [zsp]; exact hsp) (by rw [zsp]; exact hroom)
  refine ⟨y, gz.trans gy, ypc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ysp, zsp]
  · exact ym
  · intro i hi; rw [yo i hi, zm]
  · exact yhead
  · intro j hj
    rw [ycopy j (by rw [zm]; exact hj), zm, zh]
  · intro k hk
    rw [yabove k (by rw [zsp]; exact hk), zh]
  · rw [ylr, zl]
  · rw [ystk, zk]


/-- 輪(文字列): 食う器が `els` の入口の全体。`sh`(ascii 0・utf32 2)のバイト幅 `w = 2^sh`、文字数 `T = ||acc|| + d × Σ(食う器の長さ)` -/
theorem ringEntryS_ok (P : Array I3) (b : Nat) (cp cl d : Nat) (els : List Nat) (sh w : Nat) (hw : 2 ^ sh = w) (hw0 : 0 < w) (hrd : w ≤ 4)
    (hP : ∀ k x, (ringCodeS cp cl d els sh)[k]? = some x → P[b + k]? = some x)
    (x : HSt) (hpc : x.s.pc = b) (hd : d < 2 ^ 50)
    (hn : (x.s.m cl).toNat + d * (els.map (fun e => (x.s.m e).toNat)).sum < 2 ^ 50)
    (hnw : ((x.s.m cl).toNat + d * (els.map (fun e => (x.s.m e).toNat)).sum) * w < 2 ^ 50)
    (hsrc : x.sp.toNat ≤ (x.s.m cp).toNat)
    (hs : (x.s.m cp).toNat + (x.s.m cl).toNat * w < 2 ^ 64)
    (hsp : x.sp.toNat % 16 = 0)
    (hroom : ((x.s.m cl).toNat + d * (els.map (fun e => (x.s.m e).toNat)).sum) * w + 32 ≤ x.sp.toNat)
    (hlen : (x.s.m cl).toNat ≤ (x.s.m cl).toNat + d * (els.map (fun e => (x.s.m e).toNat)).sum) :
    ∃ y, Steps3 P x y ∧ y.s.pc = b + (1 + 4 * els.length) + 18 + 1 ∧
      y.sp.toNat = x.sp.toNat - (((((x.s.m cl).toNat + d * (els.map (fun e => (x.s.m e).toNat)).sum) * w + 15) / 16) * 16 + 16) ∧
      (y.s.m cp).toNat = y.sp.toNat + 16 ∧ (∀ i, i ≠ cp → y.s.m i = x.s.m i) ∧
      y.h ((y.sp.toNat + 16) / 8 - 1) = BitVec.ofNat 64 ((x.s.m cl).toNat + d * (els.map (fun e => (x.s.m e).toNat)).sum) ∧
      (∀ j, j < (x.s.m cl).toNat * w → y.hb (y.sp.toNat + 16 + j) = x.hb ((x.s.m cp).toNat + j)) ∧
      (∀ k, x.sp.toNat ≤ k → y.hb k = x.hb k) ∧
      (∀ k, x.sp.toNat / 8 ≤ k → y.h k = x.h k) ∧ y.s.lr = x.s.lr ∧ y.s.stk = x.s.stk := by
  obtain ⟨z, gz, zpc, z9, zm, zsp, zh, zhb, zl, zk⟩ := sumPre_ok P b cl d els
    (fun k hk => hP k _ (ringCodeS_sum cp cl d els sh k hk)) x hpc hd hn
  obtain ⟨y, gy, ypc, ysp, ym, yo, yhead, ycopy, yabove, yh, ylr, ystk⟩ := growTailS_ok P (b + (1 + 4 * els.length)) cp cl sh w
    ((x.s.m cl).toNat + d * (els.map (fun e => (x.s.m e).toNat)).sum) hw hw0 hrd
    (fun k x' hk => by
      have := hP ((1 + 4 * els.length) + k) x' (by rw [ringCodeS_grow]; exact hk)
      rw [← Nat.add_assoc] at this; exact this)
    z zpc z9 hnw (by rw [zm]; exact hlen) (by rw [zsp, zm]; exact hsrc) (by rw [zm]; exact hs)
    (by rw [zsp]; exact hsp) (by rw [zsp]; exact hroom)
  refine ⟨y, gz.trans gy, ypc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ysp, zsp]
  · exact ym
  · intro i hi; rw [yo i hi, zm]
  · exact yhead
  · intro j hj
    rw [ycopy j (by rw [zm]; exact hj), zm, zhb]
  · intro k hk
    rw [yabove k (by rw [zsp]; exact hk), zhb]
  · intro k hk
    rw [yh k (by rw [zsp]; exact hk), zh]
  · rw [ylr, zl]
  · rw [ystk, zk]

/-! ### 文字列の `commit_grow`(U+0000 を飛ばして末尾へ書く)

`strC`(`strb/str w, [x9]`)・`addL`(`add xd, xa, xb, lsl #sh`)・`cbzI`(`cbz`)を足した I3 での写し。 -/

theorem rdb_congr (h1 h2 : Nat → BitVec 8) : ∀ (w p : Nat), (∀ j, j < w → h1 (p + j) = h2 (p + j)) → rdb h1 p w = rdb h2 p w := by
  intro w
  induction w with
  | zero => intro p _; rfl
  | succ w ih =>
      intro p h
      simp only [rdb]
      have a := h 0 (by omega)
      have b := ih (p + 1) (fun j hj => by have := h (j + 1) (by omega); rw [show p + 1 + j = p + (j + 1) by omega]; exact this)
      simp only [Nat.add_zero] at a
      rw [a, b]

theorem rdb_wrb (hb : Nat → BitVec 8) : ∀ (w q v : Nat), v < 256 ^ w → rdb (wrb hb q w v) q w = v := by
  intro w
  induction w generalizing hb with
  | zero => intro q v hv; simp at hv; simp [rdb]; omega
  | succ w ih =>
      intro q v hv
      have h3 : 256 ^ (w + 1) = 256 ^ w * 256 := Nat.pow_succ ..
      simp only [rdb]
      have e0 : (wrb hb q (w + 1) v q).toNat = v % 256 := by
        unfold wrb; rw [if_pos (by omega)]; simp [BitVec.toNat_ofNat]
      have e1 : rdb (wrb hb q (w + 1) v) (q + 1) w = rdb (wrb hb (q + 1) w (v / 256)) (q + 1) w := by
        apply rdb_congr
        intro j hj
        unfold wrb
        rw [if_pos (by omega), if_pos (by omega)]
        have e5 : q + 1 + j - q = j + 1 := by omega
        have e6 : q + 1 + j - (q + 1) = j := by omega
        have e7 : v / 256 ^ (j + 1) = v / 256 / 256 ^ j := by
          rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
        rw [e5, e6, e7]
      rw [e0, e1, ih hb (q + 1) (v / 256) (by omega)]
      omega


def blockS (sh cur d : Nat) : List I3 :=
  [bb (I.ldr 0 d), I3.cbzI 0 5, bb (I.ldr 9 cur), I3.strC sh 0 9, I3.addI 9 9 (2 ^ sh), bb (I.str 9 cur)]

def blockT (sh cur : Nat) : List I3 :=
  [bb (I.ldr 9 cur), I3.strC sh 0 9, I3.addI 9 9 (2 ^ sh), bb (I.str 9 cur)]

theorem blockT_nobr (sh cur : Nat) : ∀ i ∈ blockT sh cur, nobr i := by
  intro i hi
  simp [blockT] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> simp [nobr, bb]

/-- 文字 1 つの書き(`ldr x0,[d]; cbz x0,sk; ldr x9,[cur]; strb/str w0,[x9]; add x9,x9,#CW; str x9,[cur]; sk:`):
0 なら何もせず、0 でなければ `cur` の位置へ書いて `cur` を `w` 進める -/
theorem blk_ok (P : Array I3) (b sh w cur d : Nat) (hw : 2 ^ sh = w)
    (hP : ∀ k (hk : k < 6), P[b + k]? = some (blockS sh cur d)[k])
    (x : HSt) (hpc : x.s.pc = b) (hdc : d ≠ cur) (hq : (x.s.m cur).toNat + w < 2 ^ 64) :
    ∃ y, Steps3 P x y ∧ y.s.pc = b + 6 ∧ y.h = x.h ∧ y.sp = x.sp ∧ y.s.lr = x.s.lr ∧ y.s.stk = x.s.stk ∧
      (∀ i, i ≠ cur → y.s.m i = x.s.m i) ∧
      ((x.s.m d).toNat = 0 → y.hb = x.hb ∧ y.s.m cur = x.s.m cur) ∧
      ((x.s.m d).toNat ≠ 0 → y.hb = wrb x.hb (x.s.m cur).toNat w (x.s.m d).toNat ∧ (y.s.m cur).toNat = (x.s.m cur).toNat + w) := by
  obtain ⟨x1, hx1⟩ : ∃ x1, x1 = step3 (bb (I.ldr 0 d)) x := ⟨_, rfl⟩
  have g1 : Steps3 P x x1 := by
    rw [hx1]; exact Steps3.go' _ b hpc (by have := hP 0 (by omega); simpa [blockS] using this) (Steps3.refl _)
  have p1 : x1.s.pc = b + 1 := by rw [hx1]; simp [step3, step2, step, bb, hpc]
  have r0 : x1.s.r 0 = x.s.m d := by rw [hx1]; rfl
  have f1m : x1.s.m = x.s.m := by rw [hx1]; rfl
  have f1h : x1.h = x.h := by rw [hx1]; rfl
  have f1b : x1.hb = x.hb := by rw [hx1]; rfl
  have f1s : x1.sp = x.sp := by rw [hx1]; rfl
  have f1l : x1.s.lr = x.s.lr := by rw [hx1]; rfl
  have f1k : x1.s.stk = x.s.stk := by rw [hx1]; rfl
  obtain ⟨x2, hx2⟩ : ∃ x2, x2 = step3 (I3.cbzI 0 5) x1 := ⟨_, rfl⟩
  have g2 : Steps3 P x1 x2 := by
    rw [hx2]; exact Steps3.go' _ (b + 1) p1 (by have := hP 1 (by omega); simpa [blockS] using this) (Steps3.refl _)
  by_cases hz : (x.s.m d).toNat = 0
  · have hz' : x.s.m d = 0 := BitVec.eq_of_toNat_eq (by simpa using hz)
    have e2 : x2 = { x1 with s := { x1.s with pc := x1.s.pc + 5 } } := by rw [hx2]; simp [step3, r0, hz']
    refine ⟨x2, g1.trans g2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e2]; simp [p1]
    · rw [e2]; simp [f1h]
    · rw [e2]; simp [f1s]
    · rw [e2]; simp [f1l]
    · rw [e2]; simp [f1k]
    · intro i _; rw [e2]; simp [f1m]
    · intro _; refine ⟨?_, ?_⟩
      · rw [e2]; simp [f1b]
      · rw [e2]; simp [f1m]
    · intro h; exact absurd hz h
  · have hnz : x.s.m d ≠ 0 := fun h => hz (by rw [h]; rfl)
    have e2 : x2 = { x1 with s := { x1.s with pc := x1.s.pc + 1 } } := by rw [hx2]; simp [step3, r0]; exact hnz
    have p2 : x2.s.pc = b + 2 := by rw [e2]; simp [p1]
    obtain ⟨g3, p3⟩ := runL_ok P b (blockT sh cur) x2 2 (by simpa using p2) (blockT_nobr sh cur)
      (fun k hk => by
        have hk' : k < 4 := by simpa [blockT] using hk
        have := hP (2 + k) (by omega)
        have e : b + 2 + k = b + (2 + k) := by omega
        rw [e, this]
        have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
        rcases this with rfl | rfl | rfl | rfl <;> rfl)
    obtain ⟨y, hy⟩ : ∃ y, y = runL (blockT sh cur) x2 := ⟨_, rfl⟩
    rw [← hy] at g3 p3
    have ym : ∀ i, y.s.m i = if i = cur then x.s.m cur + BitVec.ofNat 64 w else x.s.m i := by
      intro i; rw [hy, e2]
      have : (runL (blockT sh cur) { x1 with s := { x1.s with pc := x1.s.pc + 1 } }).s.m i
          = if i = cur then x1.s.m cur + BitVec.ofNat 64 (2 ^ sh) else x1.s.m i := rfl
      rw [this, f1m, hw]
    have yb : y.hb = wrb x.hb (x.s.m cur).toNat w (x.s.m d).toNat := by
      rw [hy, e2]
      have : (runL (blockT sh cur) { x1 with s := { x1.s with pc := x1.s.pc + 1 } }).hb
          = wrb x1.hb (x1.s.m cur).toNat (2 ^ sh) (x1.s.r 0).toNat := rfl
      rw [this, f1b, f1m, hw, r0]
    refine ⟨y, g1.trans (g2.trans g3), by simp [blockT] at p3; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hy, e2]; exact f1h
    · rw [hy, e2]; exact f1s
    · rw [hy, e2]; exact f1l
    · rw [hy, e2]; exact f1k
    · intro i hi; rw [ym, if_neg hi]
    · intro h; exact absurd h hz
    · intro _
      refine ⟨yb, ?_⟩
      rw [ym, if_pos rfl, BitVec.toNat_add]
      simp
      omega


def charsS (sh cur : Nat) (ds : List Nat) : List I3 := ds.flatMap (blockS sh cur)

def csOf (m : Nat → W) (ds : List Nat) : List Nat := (ds.map fun d => (m d).toNat).filter (· ≠ 0)

theorem csOf_cons (m : Nat → W) (d : Nat) (ds : List Nat) :
    csOf m (d :: ds) = (if (m d).toNat = 0 then [] else [(m d).toNat]) ++ csOf m ds := by
  unfold csOf
  simp only [List.map_cons, List.filter_cons]
  by_cases h : (m d).toNat = 0 <;> simp [h]

theorem csOf_congr (m1 m2 : Nat → W) (ds : List Nat) (h : ∀ d ∈ ds, m1 d = m2 d) : csOf m1 ds = csOf m2 ds := by
  have : ds.map (fun d => (m1 d).toNat) = ds.map (fun d => (m2 d).toNat) :=
    List.map_congr_left (fun d hd => by rw [h d hd])
  unfold csOf
  rw [this]

theorem csOf_len (m : Nat → W) (ds : List Nat) : (csOf m ds).length ≤ ds.length := by
  unfold csOf
  have := List.length_filter_le (fun x => decide (x ≠ 0)) (ds.map fun d => (m d).toNat)
  simpa using this

theorem chars_ok (P : Array I3) (sh w cur : Nat) (hw : 2 ^ sh = w) :
    ∀ (ds : List Nat) (b : Nat) (x : HSt),
      (∀ k z, (charsS sh cur ds)[k]? = some z → P[b + k]? = some z) →
      x.s.pc = b → (∀ d ∈ ds, d ≠ cur) →
      (x.s.m cur).toNat + (ds.length + 1) * w < 2 ^ 64 →
      (∀ d ∈ ds, (x.s.m d).toNat < 256 ^ w) →
      ∃ y, Steps3 P x y ∧ y.s.pc = b + 6 * ds.length ∧
        (y.s.m cur).toNat = (x.s.m cur).toNat + (csOf x.s.m ds).length * w ∧
        (∀ i (hi : i < (csOf x.s.m ds).length), rdb y.hb ((x.s.m cur).toNat + i * w) w = (csOf x.s.m ds)[i]) ∧
        (∀ pos, (pos < (x.s.m cur).toNat ∨ (x.s.m cur).toNat + (csOf x.s.m ds).length * w ≤ pos) → y.hb pos = x.hb pos) ∧
        (∀ i, i ≠ cur → y.s.m i = x.s.m i) ∧ y.h = x.h ∧ y.sp = x.sp ∧ y.s.lr = x.s.lr ∧ y.s.stk = x.s.stk := by
  intro ds
  induction ds with
  | nil =>
      intro b x _ hpc _ _ _
      refine ⟨x, Steps3.refl _, by simp [hpc], by simp [csOf], ?_, ?_, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
      · intro i hi; simp [csOf] at hi
      · intro _ _; rfl
  | cons d ds ih =>
      intro b x hP hpc hdc hq hv
      have hdc1 : d ≠ cur := hdc d (by simp)
      have hlen : (d :: ds).length = ds.length + 1 := rfl
      have hq0 : (x.s.m cur).toNat + w < 2 ^ 64 := by
        have : w ≤ (ds.length + 1 + 1) * w := by
          rw [Nat.succ_mul]; omega
        rw [hlen] at hq; omega
      obtain ⟨y, gy, ypc, yh, ysp, ylr, ystk, ym, hz, hnz⟩ := blk_ok P b sh w cur d hw
        (fun k hk => by
          apply hP k
          unfold charsS
          rw [List.flatMap_cons, List.getElem?_append_left (by simp [blockS]; omega)]
          exact List.getElem?_eq_getElem (by simp [blockS]; omega))
        x hpc hdc1 hq0
      have hrest : ∀ d' ∈ ds, y.s.m d' = x.s.m d' := fun d' hd' => ym d' (hdc d' (by simp [hd']))
      have hcs : csOf y.s.m ds = csOf x.s.m ds := csOf_congr _ _ _ hrest
      have hPs : ∀ k z, (charsS sh cur ds)[k]? = some z → P[(b + 6) + k]? = some z := by
        intro k z hk
        have := hP (6 + k) z (by
          unfold charsS at hk ⊢
          rw [List.flatMap_cons, List.getElem?_append_right (by simp [blockS])]
          simpa [blockS] using hk)
        rw [← Nat.add_assoc] at this; exact this
      have hq1 : (y.s.m cur).toNat + (ds.length + 1) * w < 2 ^ 64 := by
        have e : (ds.length + 1 + 1) * w = (ds.length + 1) * w + w := Nat.succ_mul _ _
        rw [hlen] at hq
        by_cases h0 : (x.s.m d).toNat = 0
        · rw [(hz h0).2]; omega
        · rw [(hnz h0).2]; omega
      obtain ⟨u, gu, upc, ucur, urd, uoth, uym, uh, usp, ulr, ustk⟩ := ih (b + 6) y hPs ypc (fun d' hd' => hdc d' (by simp [hd']))
        hq1 (fun d' hd' => by rw [hrest d' hd']; exact hv d' (by simp [hd']))
      rw [hcs] at ucur urd uoth
      refine ⟨u, gy.trans gu, by rw [upc, hlen]; omega, ?_, ?_, ?_, ?_, by rw [uh, yh], by rw [usp, ysp], by rw [ulr, ylr], by rw [ustk, ystk]⟩
      · by_cases h0 : (x.s.m d).toNat = 0
        · rw [ucur, (hz h0).2, csOf_cons, if_pos h0]; simp
        · rw [ucur, (hnz h0).2, csOf_cons, if_neg h0]; simp [Nat.succ_mul]; omega
      · intro i hi
        by_cases h0 : (x.s.m d).toNat = 0
        · have hc : csOf x.s.m (d :: ds) = csOf x.s.m ds := by rw [csOf_cons, if_pos h0]; simp
          simp only [hc] at hi ⊢
          have := urd i hi
          rw [(hz h0).2] at this; exact this
        · have hc : csOf x.s.m (d :: ds) = (x.s.m d).toNat :: csOf x.s.m ds := by rw [csOf_cons, if_neg h0]; simp
          simp only [hc]
          cases i with
          | zero =>
              simp
              have hb0 : ∀ j, j < w → u.hb ((x.s.m cur).toNat + j) = y.hb ((x.s.m cur).toNat + j) := by
                intro j hj
                have := uoth ((x.s.m cur).toNat + j) (Or.inl (by rw [(hnz h0).2]; omega))
                exact this
              have hv0 := hv d (by simp)
              rw [rdb_congr u.hb y.hb w _ hb0, (hnz h0).1]
              exact rdb_wrb x.hb w _ _ hv0
          | succ i =>
              simp only [List.getElem_cons_succ]
              have := urd i (by simp [hc] at hi; omega)
              rw [(hnz h0).2] at this
              rw [← this]; congr 1
              rw [Nat.succ_mul]; omega
      · intro pos hpos
        by_cases h0 : (x.s.m d).toNat = 0
        · have hc : csOf x.s.m (d :: ds) = csOf x.s.m ds := by rw [csOf_cons, if_pos h0]; simp
          rw [hc] at hpos
          have := uoth pos (by rw [(hz h0).2]; exact hpos)
          rw [this, (hz h0).1]
        · have hc : csOf x.s.m (d :: ds) = (x.s.m d).toNat :: csOf x.s.m ds := by rw [csOf_cons, if_neg h0]; simp
          rw [hc] at hpos
          simp only [List.length_cons, Nat.succ_mul] at hpos
          have := uoth pos (by rw [(hnz h0).2]; omega)
          rw [this, (hnz h0).1]
          unfold wrb
          rw [if_neg (by omega)]
      · intro i hi
        rw [uym i hi, ym i hi]


def commitPro (sh t1 t2 cur : Nat) : List I3 :=
  [bb (I.ldr 10 t1), bb (I.ldr 11 t2), I3.addL 10 10 11 sh, bb (I.str 10 cur)]

def commitEpi (sh t1 t2 cur : Nat) : List I3 :=
  [bb (I.ldr 9 cur), bb (I.ldr 10 t1), bb (I.subs 9 9 10), I3.lsrI 9 9 sh, bb (I.str 9 t2)]

/-- 文字列の `commit_grow`: 末尾の位置 `cur` を決め、文字(U+0000 は飛ばす)を順に書き、長さ `t2` を決める -/
def commitS (sh t1 t2 cur : Nat) (ds : List Nat) : List I3 :=
  commitPro sh t1 t2 cur ++ charsS sh cur ds ++ commitEpi sh t1 t2 cur

theorem commitPro_nobr (sh t1 t2 cur : Nat) : ∀ i ∈ commitPro sh t1 t2 cur, nobr i := by
  intro i hi
  simp [commitPro] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> simp [nobr, bb]

theorem commitEpi_nobr (sh t1 t2 cur : Nat) : ∀ i ∈ commitEpi sh t1 t2 cur, nobr i := by
  intro i hi
  simp [commitEpi] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [nobr, bb]

theorem charsS_len (sh cur : Nat) (ds : List Nat) : (charsS sh cur ds).length = 6 * ds.length := by
  unfold charsS
  induction ds with
  | nil => simp
  | cons d ds ih => simp [List.flatMap_cons, blockS] at *; omega

theorem commitS_ok (P : Array I3) (b sh w t1 t2 cur : Nat) (ds : List Nat) (hw : 2 ^ sh = w) (hw0 : 0 < w)
    (hP : ∀ k z, (commitS sh t1 t2 cur ds)[k]? = some z → P[b + k]? = some z)
    (x : HSt) (hpc : x.s.pc = b) (hc1 : cur ≠ t1) (hc2 : cur ≠ t2) (hdc : ∀ d ∈ ds, d ≠ cur)
    (hq : (x.s.m t1).toNat + ((x.s.m t2).toNat + ds.length + 1) * w < 2 ^ 64)
    (hv : ∀ d ∈ ds, (x.s.m d).toNat < 256 ^ w) :
    ∃ y, Steps3 P x y ∧ y.s.pc = b + 9 + 6 * ds.length ∧
      (y.s.m t2).toNat = (x.s.m t2).toNat + (csOf x.s.m ds).length ∧
      (∀ i (hi : i < (csOf x.s.m ds).length),
        rdb y.hb ((x.s.m t1).toNat + ((x.s.m t2).toNat + i) * w) w = (csOf x.s.m ds)[i]) ∧
      (∀ pos, (pos < (x.s.m t1).toNat + (x.s.m t2).toNat * w ∨
        (x.s.m t1).toNat + ((x.s.m t2).toNat + (csOf x.s.m ds).length) * w ≤ pos) → y.hb pos = x.hb pos) ∧
      (∀ i, i ≠ cur → i ≠ t2 → y.s.m i = x.s.m i) ∧ y.h = x.h ∧ y.sp = x.sp ∧ y.s.lr = x.s.lr ∧ y.s.stk = x.s.stk := by
  have hcl := csOf_len x.s.m ds
  have hL : (x.s.m t2).toNat * w ≤ ((x.s.m t2).toNat + ds.length + 1) * w := Nat.mul_le_mul_right w (by omega)
  have hd : ((x.s.m t2).toNat + ds.length + 1) * w = (x.s.m t2).toNat * w + (ds.length + 1) * w := by
    rw [Nat.add_assoc, Nat.add_mul]
  have hlenc := charsS_len sh cur ds
  -- 前半
  obtain ⟨g1, p1⟩ := runL_ok P b (commitPro sh t1 t2 cur) x 0 (by simpa using hpc) (commitPro_nobr sh t1 t2 cur)
    (fun k hk => by
      have hk' : k < 4 := by simpa [commitPro] using hk
      have := hP k ((commitPro sh t1 t2 cur)[k]) (by
        unfold commitS
        rw [List.append_assoc, List.getElem?_append_left (by simp [commitPro]; omega)]
        exact List.getElem?_eq_getElem hk)
      rw [Nat.add_zero]; exact this)
  obtain ⟨z, hz⟩ : ∃ z, z = runL (commitPro sh t1 t2 cur) x := ⟨_, rfl⟩
  rw [← hz] at g1 p1
  simp [commitPro] at p1
  have hadr : (x.s.m t1 + (x.s.m t2 <<< sh)).toNat = (x.s.m t1).toNat + (x.s.m t2).toNat * w := by
    have := addr_nat (x.s.m t1) (x.s.m t2) sh (x.s.m t2).toNat rfl (by rw [hw]; omega)
    rw [this, hw]
  have zm : ∀ i, z.s.m i = if i = cur then x.s.m t1 + (x.s.m t2 <<< sh) else x.s.m i := by
    intro i; rw [hz]; rfl
  have zh : z.h = x.h := by rw [hz]; rfl
  have zb : z.hb = x.hb := by rw [hz]; rfl
  have zs : z.sp = x.sp := by rw [hz]; rfl
  have zl : z.s.lr = x.s.lr := by rw [hz]; rfl
  have zk : z.s.stk = x.s.stk := by rw [hz]; rfl
  have zcur : (z.s.m cur).toNat = (x.s.m t1).toNat + (x.s.m t2).toNat * w := by rw [zm, if_pos rfl, hadr]
  have zd : ∀ d ∈ ds, z.s.m d = x.s.m d := fun d hd => by rw [zm, if_neg (hdc d hd)]
  have hcs : csOf z.s.m ds = csOf x.s.m ds := csOf_congr _ _ _ zd
  -- 文字
  obtain ⟨u, gu, upc, ucur, urd, uoth, uym, uh, usp, ulr, ustk⟩ := chars_ok P sh w cur hw ds (b + 4) z
    (fun k y hk => by
      have hkl := (List.getElem?_eq_some_iff.mp hk).1
      have := hP (4 + k) y (by
        unfold commitS
        rw [List.getElem?_append_left (by simp [commitPro, hlenc] at hkl ⊢; omega),
          List.getElem?_append_right (by simp [commitPro])]
        simpa [commitPro] using hk)
      rw [← Nat.add_assoc] at this; exact this)
    (by simpa using p1) hdc (by rw [zcur]; omega) (fun d hd => by rw [zd d hd]; exact hv d hd)
  rw [hcs] at ucur urd uoth
  rw [zcur] at ucur urd uoth
  -- 後半
  obtain ⟨g3, p3⟩ := runL_ok P b (commitEpi sh t1 t2 cur) u (4 + 6 * ds.length) (by
      have : b + (4 + 6 * ds.length) = b + 4 + 6 * ds.length := by omega
      rw [this]; exact upc) (commitEpi_nobr sh t1 t2 cur)
    (fun k hk => by
      have hk' : k < 5 := by simpa [commitEpi] using hk
      have hL : (commitPro sh t1 t2 cur ++ charsS sh cur ds).length = 4 + 6 * ds.length := by
        simp [commitPro, hlenc]; omega
      have := hP (4 + 6 * ds.length + k) ((commitEpi sh t1 t2 cur)[k]) (by
        unfold commitS
        rw [List.getElem?_append_right (by omega), hL, show 4 + 6 * ds.length + k - (4 + 6 * ds.length) = k by omega]
        exact List.getElem?_eq_getElem hk)
      rw [Nat.add_assoc]; exact this)
  obtain ⟨y, hy⟩ : ∃ y, y = runL (commitEpi sh t1 t2 cur) u := ⟨_, rfl⟩
  rw [← hy] at g3 p3
  have ym : ∀ i, y.s.m i = if i = t2 then (u.s.m cur - u.s.m t1) >>> sh else u.s.m i := by
    intro i; rw [hy]; rfl
  have u1 : u.s.m t1 = x.s.m t1 := by rw [uym t1 (Ne.symm hc1), zm, if_neg (Ne.symm hc1)]
  have hge : (x.s.m t1).toNat ≤ (u.s.m cur).toNat := by rw [ucur]; omega
  have hsub : (u.s.m cur - u.s.m t1).toNat = (u.s.m cur).toNat - (x.s.m t1).toNat := by
    rw [BitVec.toNat_sub, u1]
    have := (x.s.m t1).isLt
    omega
  have hfin : (y.s.m t2).toNat = (x.s.m t2).toNat + (csOf x.s.m ds).length := by
    rw [ym, if_pos rfl, BitVec.toNat_ushiftRight, hsub, ucur, Nat.shiftRight_eq_div_pow, hw]
    have : (x.s.m t1).toNat + (x.s.m t2).toNat * w + (csOf x.s.m ds).length * w - (x.s.m t1).toNat
        = ((x.s.m t2).toNat + (csOf x.s.m ds).length) * w := by rw [Nat.add_mul]; omega
    rw [this]
    exact Nat.mul_div_cancel _ hw0
  refine ⟨y, g1.trans (gu.trans g3), by simp [commitEpi] at p3; omega, hfin, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have := urd i hi
    have e : (x.s.m t1).toNat + ((x.s.m t2).toNat + i) * w = (x.s.m t1).toNat + (x.s.m t2).toNat * w + i * w := by
      rw [Nat.add_mul]; omega
    rw [e]
    have hyb : y.hb = u.hb := by rw [hy]; rfl
    rw [hyb]; exact this
  · intro pos hpos
    have hyb : y.hb = u.hb := by rw [hy]; rfl
    rw [hyb, uoth pos (by rw [Nat.add_mul] at hpos; omega), zb]
  · intro i hi1 hi2
    rw [ym, if_neg hi2, uym i hi1, zm, if_neg hi1]
  · rw [hy]; show u.h = x.h; rw [uh, zh]
  · rw [hy]; show u.sp = x.sp; rw [usp, zs]
  · rw [hy]; show u.s.lr = x.s.lr; rw [ulr, zl]
  · rw [hy]; show u.s.stk = x.s.stk; rw [ustk, zk]

#print axioms copyLoop_ok
#print axioms growEntry_ok
#print axioms lift2
#print axioms pstore3_ok
#print axioms fcodeH_ok_at
#print axioms commitL_facts
#print axioms append_ok
#print axioms append_inv
#print axioms append_rounds
#print axioms copyLoopS_ok
#print axioms growTailS_ok
#print axioms growTailL_ok
#print axioms sumPre_ok
#print axioms ringEntryL_ok
#print axioms ringEntryS_ok
#print axioms rdb_wrb
#print axioms blk_ok
#print axioms chars_ok
#print axioms commitS_ok
#print axioms selftailH_fn_ok

end SirZH
