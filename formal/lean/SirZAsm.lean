/-
  SIR-Z → AArch64(段階 (c) の核)。`sign_asm.py` が出す整数の `+ - * / %` の命令列(`bin_tail`)が、
  64 ビットのすべての入力で、SIR-Z の意味(`clamp` と `!_` の単位)と一致する。
  Mathlib なし。`lean SirZAsm.lean` だけで検査できる。

  * 値の表し方(value_representation.md): `!_` は `INT64_MIN`(niche)。値は 2 の補数の 64 ビット。
  * 範囲: Int の値域は `[-M, M]`、`M = 2^63 - 1`。溢れ・`INT64_MIN` に着く結果は `!_`(設計者の答え 2026-11-25)。
-/

namespace SirZAsm

def M : Int := 2 ^ 63 - 1
def clamp (z : Int) : Option Int := if -M ≤ z ∧ z ≤ M then some z else none

inductive AOp | add | sub | mul | div | mod
  deriving DecidableEq, Repr

def arithInt : AOp → Int → Int → Option Int
  | .add, a, b => clamp (a + b)
  | .sub, a, b => clamp (a - b)
  | .mul, a, b => clamp (a * b)
  | .div, a, b => if b = 0 then none else clamp (a.tdiv b)
  | .mod, a, b => if b = 0 then none else clamp (a - a.tdiv b * b)

/-- `!_` は算術の単位元(operator_table.md の爆発律) -/
def arith (o : AOp) : Option Int → Option Int → Option Int
  | some a, some b => arithInt o a b
  | some a, none   => some a
  | none,   some b => some b
  | none,   none   => none

/-! ## 値の表し方 -/

abbrev W := BitVec 64
def NICHE : W := BitVec.intMin 64

def decode (x : W) : Option Int := if x = NICHE then none else some x.toInt
def encode : Option Int → W
  | none => NICHE
  | some z => BitVec.ofInt 64 z

theorem toInt_niche : NICHE.toInt = -(2 ^ 63) := by
  simp [NICHE, BitVec.toInt_intMin]

theorem toInt_bounds (x : W) : -(2 ^ 63 : Int) ≤ x.toInt ∧ x.toInt < 2 ^ 63 := by
  have h1 := BitVec.le_toInt x
  have h2 := BitVec.toInt_lt (x := x)
  simp at h1 h2
  omega

theorem ne_niche_iff (x : W) : x ≠ NICHE ↔ x.toInt ≠ -(2 ^ 63) := by
  constructor
  · intro h e; apply h; apply BitVec.eq_of_toInt_eq; rw [e, toInt_niche]
  · intro h e; apply h; rw [e, toInt_niche]

/-- `ofInt` の `toInt` -/
theorem toInt_ofInt' (z : Int) (h : -(2 ^ 63 : Int) ≤ z ∧ z < 2 ^ 63) : (BitVec.ofInt 64 z).toInt = z := by
  rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]

/-- 結果の語 `v` の符号つきの値が `z`(64 ビットに収まる)なら、`v` は `clamp z` の表し方 -/
theorem result_ok (v : W) (z : Int) (hv : v.toInt = z) (hz : -(2 ^ 63 : Int) ≤ z ∧ z < 2 ^ 63) :
    v = encode (clamp z) := by
  unfold clamp
  by_cases h : -M ≤ z ∧ z ≤ M
  · simp only [h, and_self, ite_true, encode]
    apply BitVec.eq_of_toInt_eq
    rw [hv, toInt_ofInt' z hz]
  · simp only [h, ite_false, encode]
    have : z = -(2 ^ 63) := by unfold M at h; omega
    apply BitVec.eq_of_toInt_eq
    rw [hv, this, toInt_niche]

/-- 溢れた結果は `clamp` で `none` -/
theorem clamp_out (z : Int) (h : z < -(2 ^ 63) ∨ z ≥ 2 ^ 63) : clamp z = none := by
  unfold clamp M; simp; omega

/-! ## 核: 入力は両方とも `!_` ではない -/

theorem add_core (x y : W) :
    (if x.saddOverflow y then NICHE else x + y) = encode (clamp (x.toInt + y.toInt)) := by
  by_cases h : x.saddOverflow y = true
  · simp only [h, ite_true]
    have : x.toInt + y.toInt ≥ 2 ^ 63 ∨ x.toInt + y.toInt < -(2 ^ 63) := by
      simp [BitVec.saddOverflow] at h; omega
    rw [clamp_out _ (by omega)]; rfl
  · have h' : ¬ x.saddOverflow y = true := h
    simp only [h, Bool.false_eq_true, ite_false]
    have h2 := BitVec.toInt_add_of_not_saddOverflow h'
    have : -(2 ^ 63 : Int) ≤ x.toInt + y.toInt ∧ x.toInt + y.toInt < 2 ^ 63 := by
      simp [BitVec.saddOverflow] at h; omega
    exact result_ok _ _ h2 this

theorem sub_core (x y : W) :
    (if x.ssubOverflow y then NICHE else x - y) = encode (clamp (x.toInt - y.toInt)) := by
  by_cases h : x.ssubOverflow y = true
  · simp only [h, ite_true]
    have : x.toInt - y.toInt ≥ 2 ^ 63 ∨ x.toInt - y.toInt < -(2 ^ 63) := by
      simp [BitVec.ssubOverflow] at h; omega
    rw [clamp_out _ (by omega)]; rfl
  · have h' : ¬ x.ssubOverflow y = true := h
    simp only [h, Bool.false_eq_true, ite_false]
    have h2 := BitVec.toInt_sub_of_not_ssubOverflow h'
    have : -(2 ^ 63 : Int) ≤ x.toInt - y.toInt ∧ x.toInt - y.toInt < 2 ^ 63 := by
      simp [BitVec.ssubOverflow] at h; omega
    exact result_ok _ _ h2 this

/-- SDIV(simp が中身を展開しないように、別の名前にしておく) -/
def sdivW (a b : W) : W := a.sdiv b

/-- SMULH: 128 ビットの符号つきの積の上の 64 ビット(ARM ARM: `result<127:64>`) -/
def smulh (x y : W) : W := BitVec.ofInt 64 ((x.toInt * y.toInt) / 2 ^ 64)

theorem prod_bound (x y : W) : (x.toInt * y.toInt) ≤ 2 ^ 126 ∧ -(2 ^ 126 : Int) ≤ x.toInt * y.toInt := by
  have hx := toInt_bounds x
  have hy := toInt_bounds y
  have h1 : (x.toInt * y.toInt).natAbs = x.toInt.natAbs * y.toInt.natAbs := Int.natAbs_mul _ _
  have h2 : x.toInt.natAbs ≤ 2 ^ 63 := by omega
  have h3 : y.toInt.natAbs ≤ 2 ^ 63 := by omega
  have h4 : x.toInt.natAbs * y.toInt.natAbs ≤ 2 ^ 63 * 2 ^ 63 := Nat.mul_le_mul h2 h3
  omega

/-- `cmp x12, x11, asr #63` が等しい ⇔ 積が 64 ビットの符号つきに収まる -/
theorem mul_core (x y : W) :
    (if smulh x y = (x * y).sshiftRight 63 then x * y else NICHE) = encode (clamp (x.toInt * y.toInt)) := by
  have hb := prod_bound x y
  generalize hP : x.toInt * y.toInt = P at hb
  have hlo : (x * y).toInt = P.bmod (2 ^ 64) := by rw [BitVec.toInt_mul, hP]
  have hsh : ((x * y).sshiftRight 63).toInt = (x * y).toInt >>> 63 := by
    rw [BitVec.toInt_sshiftRight]
  have hhi : (smulh x y).toInt = (P / 2 ^ 64).bmod (2 ^ 64) := by
    unfold smulh; rw [hP, BitVec.toInt_ofInt]
  have hlb := toInt_bounds (x * y)
  rw [Int.shiftRight_eq_div_pow] at hsh
  by_cases hc : smulh x y = (x * y).sshiftRight 63
  · simp only [hc, ite_true]
    have e := congrArg BitVec.toInt hc
    rw [hhi, hsh, hlo] at e
    have hr : -(2 ^ 63 : Int) ≤ P ∧ P < 2 ^ 63 := by
      simp only [Int.bmod_def] at e hlo ⊢; omega
    have : (x * y).toInt = P := by rw [hlo]; exact Int.bmod_eq_of_le (by omega) (by omega)
    exact result_ok _ _ this hr
  · simp only [hc, Bool.false_eq_true, ite_false]
    have : P < -(2 ^ 63) ∨ P ≥ 2 ^ 63 := by
      refine Classical.byContradiction fun hn => ?_
      apply hc
      apply BitVec.eq_of_toInt_eq
      rw [hhi, hsh, hlo]
      simp only [Int.bmod_def]; omega
    rw [clamp_out _ (by omega)]; rfl

/-- 商は被除数を超えない。被除数が `INT64_MIN` でなければ、値域の中。 -/
theorem tdiv_in_range (a b : Int) (ha : -(2 ^ 63 : Int) < a ∧ a < 2 ^ 63) : clamp (a.tdiv b) = some (a.tdiv b) := by
  have h := Int.natAbs_tdiv_le_natAbs a b
  have : -(2 ^ 63 - 1 : Int) ≤ a.tdiv b ∧ a.tdiv b ≤ 2 ^ 63 - 1 := by omega
  unfold clamp M
  have h3 : -(2 ^ 63 - 1 : Int) ≤ a.tdiv b ∧ a.tdiv b ≤ 2 ^ 63 - 1 := this
  simp only [h3, and_self, ite_true]

/-- `/`: `cmp x10, #0; b.ne ok; (niche); b done; ok: sdiv x0, x9, x10` -/
theorem div_core (x y : W) (hx : x ≠ NICHE) :
    (if y = 0 then NICHE else x.sdiv y) = encode (if y.toInt = 0 then none else clamp (x.toInt.tdiv y.toInt)) := by
  have hb := toInt_bounds x
  have hxn := (ne_niche_iff x).1 hx
  by_cases h : y = 0
  · subst h; simp [encode]
  · have hy : y.toInt ≠ 0 := fun e => h (by apply BitVec.eq_of_toInt_eq; rw [e]; simp)
    simp only [h, ite_false, hy]
    have hq := tdiv_in_range x.toInt y.toInt (by omega)
    have h2 : (x.sdiv y).toInt = x.toInt.tdiv y.toInt := by
      rw [BitVec.toInt_sdiv]
      have := Int.natAbs_tdiv_le_natAbs x.toInt y.toInt
      exact Int.bmod_eq_of_le (by omega) (by omega)
    exact result_ok _ _ h2 (by have := Int.natAbs_tdiv_le_natAbs x.toInt y.toInt; omega)

/-- `%`: `sdiv x11, x9, x10; msub x0, x11, x10, x9`(`x0 = x9 - x11 * x10`) -/
theorem mod_core (x y : W) (hx : x ≠ NICHE) :
    (if y = 0 then NICHE else x - x.sdiv y * y) =
      encode (if y.toInt = 0 then none else clamp (x.toInt - x.toInt.tdiv y.toInt * y.toInt)) := by
  have hb := toInt_bounds x
  have hxn := (ne_niche_iff x).1 hx
  by_cases h : y = 0
  · subst h; simp [encode]
  · have hy : y.toInt ≠ 0 := fun e => h (by apply BitVec.eq_of_toInt_eq; rw [e]; simp)
    simp only [h, ite_false, hy]
    have hq : (x.sdiv y).toInt = x.toInt.tdiv y.toInt := by
      rw [BitVec.toInt_sdiv]
      have := Int.natAbs_tdiv_le_natAbs x.toInt y.toInt
      exact Int.bmod_eq_of_le (by omega) (by omega)
    -- |q| * |b| ≤ |a|
    have hqb : (x.toInt.tdiv y.toInt * y.toInt).natAbs ≤ x.toInt.natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_tdiv]
      exact Nat.div_mul_le_self _ _
    have hprod : (x.sdiv y * y).toInt = x.toInt.tdiv y.toInt * y.toInt := by
      rw [BitVec.toInt_mul, hq]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    have htm : x.toInt - x.toInt.tdiv y.toInt * y.toInt = x.toInt.tmod y.toInt := by
      rw [Int.tmod_def]; rw [Int.mul_comm y.toInt]
    have hab : (x.toInt.tmod y.toInt).natAbs ≤ x.toInt.natAbs := by
      rw [Int.natAbs_tmod]; exact Nat.mod_le _ _
    have hv : (x - x.sdiv y * y).toInt = x.toInt - x.toInt.tdiv y.toInt * y.toInt := by
      rw [BitVec.toInt_sub, hprod, htm]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    exact result_ok _ _ hv (by rw [htm]; omega)

/-! ## 機械(AArch64 の部分集合) -/

inductive Cond | ne | eq | vs | lt | ge | gt | le
  deriving DecidableEq

inductive I
  | movz (d : Nat)                     -- movz xd, #0x8000, lsl #48(`!_` の印)
  | mov (d s : Nat)
  | cmpR (a b : Nat)
  | cmpI (a n : Nat)                   -- cmp xa, #n
  | cmpAsr (a b sh : Nat)              -- cmp xa, xb, asr #sh
  | adds (d a b : Nat)
  | subs (d a b : Nat)
  | mul (d a b : Nat)
  | smulh (d a b : Nat)
  | sdiv (d a b : Nat)
  | msub (d a b c : Nat)               -- xd = xc - xa * xb
  | csel (d a b : Nat) (c : Cond)      -- xd = c ? xa : xb
  | bc (c : Cond) (t : Nat)            -- 相対(今の命令から t 先。前向きだけ)
  | b (t : Nat)
  | movi (d : Nat) (n : Int)           -- mov xd, #n(リテラル)
  | str (a k : Nat)                    -- str xa, [x29, #16+8k]
  | ldr (d k : Nat)                    -- ldr xd, [x29, #16+8k]
  | neg (d a : Nat)                    -- neg xd, xa(= 0 - xa。旗は変えない)

structure St where
  r : Nat → W
  m : Nat → W                          -- フレームの枠(x29 からの位置 k)
  z : Bool
  n : Bool
  v : Bool
  pc : Nat

def St.set (s : St) (d : Nat) (x : W) : St := { s with r := fun i => if i = d then x else s.r i }

def Cond.holds (c : Cond) (s : St) : Bool :=
  match c with
  | .ne => !s.z
  | .eq => s.z
  | .vs => s.v
  | .lt => s.n != s.v
  | .ge => s.n == s.v
  | .gt => !s.z && (s.n == s.v)
  | .le => s.z || (s.n != s.v)

/-- 即値(simp が具体的な 64 ビットの値を展開しないよう、別の名前にしておく) -/
@[irreducible] def immW (n : Nat) : W := BitVec.ofNat 64 n

theorem immW_zero : immW 0 = (0 : W) := by unfold immW; rfl

/-- 比べの V 旗。分岐が見るのは Z だけなので、simp が具体的な値で展開しないよう、別の名前にしておく -/
@[irreducible] def cmpV (a b : W) : Bool := a.ssubOverflow b

/-- 減算の旗(cmp・subs): Z は差が 0、V は符号つきの溢れ -/
def St.flagsSub (s : St) (a b : W) : St := { s with z := decide (a = b), n := (a - b).msb, v := cmpV a b }

def step (i : I) (s : St) : St :=
  let s' := { s with pc := s.pc + 1 }
  match i with
  | .movz d => s'.set d NICHE
  | .mov d a => s'.set d (s.r a)
  | .cmpR a b => s'.flagsSub (s.r a) (s.r b)
  | .cmpI a n => s'.flagsSub (s.r a) (immW n)
  | .cmpAsr a b sh => s'.flagsSub (s.r a) ((s.r b).sshiftRight sh)
  | .adds d a b => { (s'.set d (s.r a + s.r b)) with z := decide (s.r a + s.r b = 0), n := (s.r a + s.r b).msb, v := (s.r a).saddOverflow (s.r b) }
  | .subs d a b => { (s'.set d (s.r a - s.r b)) with z := decide (s.r a - s.r b = 0), n := (s.r a - s.r b).msb, v := (s.r a).ssubOverflow (s.r b) }
  | .mul d a b => s'.set d (s.r a * s.r b)
  | .smulh d a b => s'.set d (smulh (s.r a) (s.r b))
  | .sdiv d a b => s'.set d (sdivW (s.r a) (s.r b))
  | .msub d a b c => s'.set d (s.r c - s.r a * s.r b)
  | .csel d a b c => s'.set d (if c.holds s then s.r a else s.r b)
  | .bc c t => if c.holds s then { s with pc := s.pc + t } else s'
  | .b t => { s with pc := s.pc + t }
  | .movi d n => s'.set d (BitVec.ofInt 64 n)
  | .str a k => { s' with m := fun i => if i = k then s.r a else s.m i }
  | .ldr d k => s'.set d (s.m k)
  | .neg d a => s'.set d (0 - s.r a)

/-- 燃料つきの実行。`pc` が終わりに着いたら止まる -/
def run (p : Array I) : Nat → St → St
  | 0, s => s
  | n + 1, s => if h : s.pc < p.size then run p n (step p[s.pc] s) else s

def init (x y : W) : St := { r := fun i => if i = 9 then x else if i = 10 then y else 0, m := fun _ => 0, z := false, n := false, v := false, pc := 0 }

/-- 符号つきの `<` は、`cmp` の旗の N と V が違うこと -/
theorem flag_lt (a b : BitVec 64) : ((a - b).msb != a.ssubOverflow b) = decide (a.toInt < b.toInt) := by
  have h1 := BitVec.le_toInt a
  have h2 := BitVec.toInt_lt (x := a)
  have h3 := BitVec.le_toInt b
  have h4 := BitVec.toInt_lt (x := b)
  simp only [BitVec.msb_eq_toInt, BitVec.toInt_sub, BitVec.ssubOverflow]
  simp at h1 h2 h3 h4
  generalize a.toInt = A at *
  generalize b.toInt = B at *
  have e0 : -9223372036854775808 ≤ A - B → A - B < 9223372036854775808 → (A - B).bmod 18446744073709551616 = A - B := fun h h' =>
    Int.bmod_eq_of_le (by omega) (by omega)
  have e1 : A - B ≥ 9223372036854775808 → (A - B).bmod 18446744073709551616 = A - B - 18446744073709551616 := by
    intro h; simp only [Int.bmod]; split <;> omega
  have e2 : A - B < -9223372036854775808 → (A - B).bmod 18446744073709551616 = A - B + 18446744073709551616 := by
    intro h; simp only [Int.bmod]; split <;> omega
  have p : (2 : Int) ^ (64 - 1) = 9223372036854775808 := by decide
  have p2 : (2 : Int) ^ 64 = 18446744073709551616 := by decide
  simp only [p, p2]
  rw [← Bool.decide_or]
  by_cases c1 : A - B ≥ 9223372036854775808
  · rw [e1 c1]
    by_cases hR : A < B <;> by_cases hX : A - B - 18446744073709551616 < 0 <;> simp [hR, hX] <;> omega
  · by_cases c2 : A - B < -9223372036854775808
    · rw [e2 c2]
      by_cases hR : A < B <;> by_cases hX : A - B + 18446744073709551616 < 0 <;> simp [hR, hX] <;> omega
    · rw [e0 (by omega) (by omega)]
      by_cases hR : A < B <;> by_cases hX : A - B < 0 <;> simp [hR, hX] <;> omega


theorem hold_lt (s : St) (a b : W) : Cond.lt.holds (s.flagsSub a b) = decide (a.toInt < b.toInt) := by
  simp only [Cond.holds, St.flagsSub, cmpV]; exact flag_lt a b

theorem hold_ge (s : St) (a b : W) : Cond.ge.holds (s.flagsSub a b) = decide (b.toInt ≤ a.toInt) := by
  have h := flag_lt a b
  simp only [Cond.holds, St.flagsSub, cmpV]
  cases hm : (a - b).msb <;> cases ho : a.ssubOverflow b <;> simp [hm, ho] at h ⊢ <;> omega

theorem hold_gt (s : St) (a b : W) : Cond.gt.holds (s.flagsSub a b) = decide (b.toInt < a.toInt) := by
  have h := flag_lt a b
  have hab : (a = b) ↔ a.toInt = b.toInt := ⟨fun e => by rw [e], fun e => BitVec.eq_of_toInt_eq e⟩
  simp only [Cond.holds, St.flagsSub, cmpV]
  cases hm : (a - b).msb <;> cases ho : a.ssubOverflow b <;> by_cases he : a = b <;> simp [hm, ho, he] at h hab ⊢ <;> omega

theorem hold_le (s : St) (a b : W) : Cond.le.holds (s.flagsSub a b) = decide (a.toInt ≤ b.toInt) := by
  have h := flag_lt a b
  have hab : (a = b) ↔ a.toInt = b.toInt := ⟨fun e => by rw [e], fun e => BitVec.eq_of_toInt_eq e⟩
  simp only [Cond.holds, St.flagsSub, cmpV]
  cases hm : (a - b).msb <;> cases ho : a.ssubOverflow b <;> by_cases he : a = b <;> simp [hm, ho, he] at h hab ⊢ <;> omega

theorem hold_eq (s : St) (a b : W) : Cond.eq.holds (s.flagsSub a b) = decide (a.toInt = b.toInt) := by
  have hab : (a = b) ↔ a.toInt = b.toInt := ⟨fun e => by rw [e], fun e => BitVec.eq_of_toInt_eq e⟩
  simp only [Cond.holds, St.flagsSub]
  by_cases he : a = b <;> simp [he] at hab ⊢ <;> omega

theorem hold_ne (s : St) (a b : W) : Cond.ne.holds (s.flagsSub a b) = decide (a.toInt ≠ b.toInt) := by
  have hab : (a = b) ↔ a.toInt = b.toInt := ⟨fun e => by rw [e], fun e => BitVec.eq_of_toInt_eq e⟩
  simp only [Cond.holds, St.flagsSub]
  by_cases he : a = b <;> simp [he] at hab ⊢ <;> omega

-- BEGIN GENERATED
def tpl_add : Array I := #[
  (I.movz 13),
  (I.cmpR 9 13),
  (I.bc Cond.ne 3),
  (I.mov 0 10),
  (I.b 8),
  (I.cmpR 10 13),
  (I.bc Cond.ne 3),
  (I.mov 0 9),
  (I.b 4),
  (I.movz 13),
  (I.adds 9 9 10),
  (I.csel 0 13 9 Cond.vs)]

def tpl_sub : Array I := #[
  (I.movz 13),
  (I.cmpR 9 13),
  (I.bc Cond.ne 3),
  (I.mov 0 10),
  (I.b 8),
  (I.cmpR 10 13),
  (I.bc Cond.ne 3),
  (I.mov 0 9),
  (I.b 4),
  (I.movz 13),
  (I.subs 9 9 10),
  (I.csel 0 13 9 Cond.vs)]

def tpl_mul : Array I := #[
  (I.movz 13),
  (I.cmpR 9 13),
  (I.bc Cond.ne 3),
  (I.mov 0 10),
  (I.b 10),
  (I.cmpR 10 13),
  (I.bc Cond.ne 3),
  (I.mov 0 9),
  (I.b 6),
  (I.movz 13),
  (I.mul 11 9 10),
  (I.smulh 12 9 10),
  (I.cmpAsr 12 11 63),
  (I.csel 0 13 11 Cond.ne)]

def tpl_div : Array I := #[
  (I.movz 13),
  (I.cmpR 9 13),
  (I.bc Cond.ne 3),
  (I.mov 0 10),
  (I.b 10),
  (I.cmpR 10 13),
  (I.bc Cond.ne 3),
  (I.mov 0 9),
  (I.b 6),
  (I.cmpI 10 0),
  (I.bc Cond.ne 3),
  (I.movz 0),
  (I.b 2),
  (I.sdiv 0 9 10)]

def tpl_mod : Array I := #[
  (I.movz 13),
  (I.cmpR 9 13),
  (I.bc Cond.ne 3),
  (I.mov 0 10),
  (I.b 11),
  (I.cmpR 10 13),
  (I.bc Cond.ne 3),
  (I.mov 0 9),
  (I.b 7),
  (I.cmpI 10 0),
  (I.bc Cond.ne 3),
  (I.movz 0),
  (I.b 3),
  (I.sdiv 11 9 10),
  (I.msub 0 11 10 9)]

def tplN_add : Array I := #[
  (I.movz 13),
  (I.adds 9 9 10),
  (I.csel 0 13 9 Cond.vs)]

def tplN_sub : Array I := #[
  (I.movz 13),
  (I.subs 9 9 10),
  (I.csel 0 13 9 Cond.vs)]

def tplN_mul : Array I := #[
  (I.movz 13),
  (I.mul 11 9 10),
  (I.smulh 12 9 10),
  (I.cmpAsr 12 11 63),
  (I.csel 0 13 11 Cond.ne)]

def tplN_div : Array I := #[
  (I.cmpI 10 0),
  (I.bc Cond.ne 3),
  (I.movz 0),
  (I.b 2),
  (I.sdiv 0 9 10)]

def tplN_mod : Array I := #[
  (I.cmpI 10 0),
  (I.bc Cond.ne 3),
  (I.movz 0),
  (I.b 3),
  (I.sdiv 11 9 10),
  (I.msub 0 11 10 9)]

def tplL_add : Array I := #[
  (I.movz 13),
  (I.cmpR 9 13),
  (I.bc Cond.ne 3),
  (I.mov 0 10),
  (I.b 4),
  (I.movz 13),
  (I.adds 9 9 10),
  (I.csel 0 13 9 Cond.vs)]

def tplL_sub : Array I := #[
  (I.movz 13),
  (I.cmpR 9 13),
  (I.bc Cond.ne 3),
  (I.mov 0 10),
  (I.b 4),
  (I.movz 13),
  (I.subs 9 9 10),
  (I.csel 0 13 9 Cond.vs)]

def tplL_mul : Array I := #[
  (I.movz 13),
  (I.cmpR 9 13),
  (I.bc Cond.ne 3),
  (I.mov 0 10),
  (I.b 6),
  (I.movz 13),
  (I.mul 11 9 10),
  (I.smulh 12 9 10),
  (I.cmpAsr 12 11 63),
  (I.csel 0 13 11 Cond.ne)]

def tplL_div : Array I := #[
  (I.movz 13),
  (I.cmpR 9 13),
  (I.bc Cond.ne 3),
  (I.mov 0 10),
  (I.b 6),
  (I.cmpI 10 0),
  (I.bc Cond.ne 3),
  (I.movz 0),
  (I.b 2),
  (I.sdiv 0 9 10)]

def tplL_mod : Array I := #[
  (I.movz 13),
  (I.cmpR 9 13),
  (I.bc Cond.ne 3),
  (I.mov 0 10),
  (I.b 7),
  (I.cmpI 10 0),
  (I.bc Cond.ne 3),
  (I.movz 0),
  (I.b 3),
  (I.sdiv 11 9 10),
  (I.msub 0 11 10 9)]

def tplR_add : Array I := #[
  (I.movz 13),
  (I.cmpR 10 13),
  (I.bc Cond.ne 3),
  (I.mov 0 9),
  (I.b 4),
  (I.movz 13),
  (I.adds 9 9 10),
  (I.csel 0 13 9 Cond.vs)]

def tplR_sub : Array I := #[
  (I.movz 13),
  (I.cmpR 10 13),
  (I.bc Cond.ne 3),
  (I.mov 0 9),
  (I.b 4),
  (I.movz 13),
  (I.subs 9 9 10),
  (I.csel 0 13 9 Cond.vs)]

def tplR_mul : Array I := #[
  (I.movz 13),
  (I.cmpR 10 13),
  (I.bc Cond.ne 3),
  (I.mov 0 9),
  (I.b 6),
  (I.movz 13),
  (I.mul 11 9 10),
  (I.smulh 12 9 10),
  (I.cmpAsr 12 11 63),
  (I.csel 0 13 11 Cond.ne)]

def tplR_div : Array I := #[
  (I.movz 13),
  (I.cmpR 10 13),
  (I.bc Cond.ne 3),
  (I.mov 0 9),
  (I.b 6),
  (I.cmpI 10 0),
  (I.bc Cond.ne 3),
  (I.movz 0),
  (I.b 2),
  (I.sdiv 0 9 10)]

def tplR_mod : Array I := #[
  (I.movz 13),
  (I.cmpR 10 13),
  (I.bc Cond.ne 3),
  (I.mov 0 9),
  (I.b 7),
  (I.cmpI 10 0),
  (I.bc Cond.ne 3),
  (I.movz 0),
  (I.b 3),
  (I.sdiv 11 9 10),
  (I.msub 0 11 10 9)]

def tplZN_div : Array I := #[
  (I.sdiv 0 9 10)]

def tplZN_mod : Array I := #[
  (I.sdiv 11 9 10),
  (I.msub 0 11 10 9)]

def tplZL_div : Array I := #[
  (I.movz 13),
  (I.cmpR 9 13),
  (I.bc Cond.ne 3),
  (I.mov 0 10),
  (I.b 2),
  (I.sdiv 0 9 10)]

def tplZL_mod : Array I := #[
  (I.movz 13),
  (I.cmpR 9 13),
  (I.bc Cond.ne 3),
  (I.mov 0 10),
  (I.b 3),
  (I.sdiv 11 9 10),
  (I.msub 0 11 10 9)]

-- END GENERATED

theorem decode_ne (x : W) (h : x ≠ NICHE) : decode x = some x.toInt := by simp [decode, h]

theorem encode_decode (y : W) : encode (decode y) = y := by
  by_cases h : y = NICHE
  · subst h; simp [decode, encode]
  · simp only [decode, h, ite_false, encode]
    apply BitVec.eq_of_toInt_eq
    rw [toInt_ofInt' _ (toInt_bounds y)]

theorem arith_none_left (o : AOp) (d : Option Int) : arith o none d = d := by cases d <;> rfl
theorem arith_none_right (o : AOp) (d : Option Int) : arith o d none = d := by cases d <;> rfl

theorem tpl_add_ok (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) :
    (run tpl_add 30 s).r 0 = encode (arith .add (decode x) (decode y)) ∧ (run tpl_add 30 s).pc = tpl_add.size := by
  by_cases hx : x = NICHE
  · subst hx
    have : decode NICHE = none := by simp [decode]
    simp [run, tpl_add, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, this, arith_none_left, encode_decode]
  · by_cases hy : y = NICHE
    · subst hy
      have : decode NICHE = none := by simp [decode]
      simp [run, tpl_add, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, this, arith_none_right, encode_decode, hx]
    · have hdx := decode_ne x hx
      have hdy := decode_ne y hy
      simp [run, tpl_add, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hdx, hdy, arith, arithInt]
      exact add_core x y


theorem tpl_sub_ok (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) :
    (run tpl_sub 30 s).r 0 = encode (arith .sub (decode x) (decode y)) ∧ (run tpl_sub 30 s).pc = tpl_sub.size := by
  by_cases hx : x = NICHE
  · subst hx
    have : decode NICHE = none := by simp [decode]
    simp [run, tpl_sub, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, this, arith_none_left, encode_decode]
  · by_cases hy : y = NICHE
    · subst hy
      have : decode NICHE = none := by simp [decode]
      simp [run, tpl_sub, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, this, arith_none_right, encode_decode, hx]
    · have hdx := decode_ne x hx
      have hdy := decode_ne y hy
      simp [run, tpl_sub, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hdx, hdy, arith, arithInt]
      exact sub_core x y

theorem tpl_mul_ok (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) :
    (run tpl_mul 30 s).r 0 = encode (arith .mul (decode x) (decode y)) ∧ (run tpl_mul 30 s).pc = tpl_mul.size := by
  by_cases hx : x = NICHE
  · subst hx
    have : decode NICHE = none := by simp [decode]
    simp [run, tpl_mul, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, this, arith_none_left, encode_decode]
  · by_cases hy : y = NICHE
    · subst hy
      have : decode NICHE = none := by simp [decode]
      simp [run, tpl_mul, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, this, arith_none_right, encode_decode, hx]
    · have hdx := decode_ne x hx
      have hdy := decode_ne y hy
      simp [run, tpl_mul, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hdx, hdy, arith, arithInt]
      exact mul_core x y

theorem tpl_div_ok (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) :
    (run tpl_div 30 s).r 0 = encode (arith .div (decode x) (decode y)) ∧ (run tpl_div 30 s).pc = tpl_div.size := by
  by_cases hx : x = NICHE
  · subst hx
    have : decode NICHE = none := by simp [decode]
    simp [run, tpl_div, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, this, arith_none_left, encode_decode]
  · by_cases hy : y = NICHE
    · subst hy
      have : decode NICHE = none := by simp [decode]
      simp [run, tpl_div, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, this, arith_none_right, encode_decode, hx]
    · have hdx := decode_ne x hx
      have hdy := decode_ne y hy
      by_cases hy0 : y = 0
      · have hz : decide (y = immW 0) = true := by rw [immW_zero]; exact decide_eq_true hy0
        have h0 : (0 : W).toInt = 0 := by decide
        have hyt : y.toInt = 0 := by rw [hy0]; exact h0
        have hdy0 : decode y = some 0 := by rw [hdy, hyt]
        simp [run, tpl_div, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hz]
        rw [hdx, hdy0]; simp [arith, arithInt, encode]
      · have hz : decide (y = immW 0) = false := by rw [immW_zero]; exact decide_eq_false hy0
        have hyz : y.toInt ≠ 0 := fun e => hy0 (by apply BitVec.eq_of_toInt_eq; rw [e]; simp)
        simp [run, tpl_div, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hdx, hdy, arith, arithInt, hz, hyz]
        have h := div_core x y hx
        simp only [hy0, hyz, ite_false, if_false] at h
        exact h

theorem tpl_mod_ok (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) :
    (run tpl_mod 30 s).r 0 = encode (arith .mod (decode x) (decode y)) ∧ (run tpl_mod 30 s).pc = tpl_mod.size := by
  by_cases hx : x = NICHE
  · subst hx
    have : decode NICHE = none := by simp [decode]
    simp [run, tpl_mod, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, this, arith_none_left, encode_decode]
  · by_cases hy : y = NICHE
    · subst hy
      have : decode NICHE = none := by simp [decode]
      simp [run, tpl_mod, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, this, arith_none_right, encode_decode, hx]
    · have hdx := decode_ne x hx
      have hdy := decode_ne y hy
      by_cases hy0 : y = 0
      · have hz : decide (y = immW 0) = true := by rw [immW_zero]; exact decide_eq_true hy0
        have h0 : (0 : W).toInt = 0 := by decide
        have hyt : y.toInt = 0 := by rw [hy0]; exact h0
        have hdy0 : decode y = some 0 := by rw [hdy, hyt]
        simp [run, tpl_mod, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hz]
        rw [hdx, hdy0]; simp [arith, arithInt, encode]
      · have hz : decide (y = immW 0) = false := by rw [immW_zero]; exact decide_eq_false hy0
        have hyz : y.toInt ≠ 0 := fun e => hy0 (by apply BitVec.eq_of_toInt_eq; rw [e]; simp)
        simp [run, tpl_mod, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hdx, hdy, arith, arithInt, hz, hyz]
        have h := mod_core x y hx
        simp only [hy0, hyz, ite_false, if_false] at h
        exact h

/-- 5 つの演算の命令列 -/
def tpl : AOp → Array I
  | .add => tpl_add | .sub => tpl_sub | .mul => tpl_mul | .div => tpl_div | .mod => tpl_mod

/-- 段階 (c)(整数の核): `sign_asm.py` の `bin_tail` の命令列は、`x9`・`x10` が 64 ビットのどんな語でも(`!_` の印を含めて)、
    最後に `x0` に `arith o (decode x9) (decode x10)` の表し方を置き、終わりまで走る。 -/
theorem tpl_ok (o : AOp) (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) :
    (run (tpl o) 30 s).r 0 = encode (arith o (decode x) (decode y)) ∧ (run (tpl o) 30 s).pc = (tpl o).size := by
  cases o
  · exact tpl_add_ok s hs x y h9 h10
  · exact tpl_sub_ok s hs x y h9 h10
  · exact tpl_mul_ok s hs x y h9 h10
  · exact tpl_div_ok s hs x y h9 h10
  · exact tpl_mod_ok s hs x y h9 h10

/-! ### `!_` にならないと分かっている所の短い形(N: 両方、L: 左だけ `!_` になりうる、R: 右だけ) -/

theorem tplN_add_ok (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) (hx : x ≠ NICHE) (hy : y ≠ NICHE) :
    (run tplN_add 30 s).r 0 = encode (arith .add (decode x) (decode y)) ∧ (run tplN_add 30 s).pc = tplN_add.size := by
  have hdx := decode_ne x hx
  have hdy := decode_ne y hy
  simp [run, tplN_add, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hdx, hdy, arith, arithInt]
  exact add_core x y

theorem tplN_sub_ok (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) (hx : x ≠ NICHE) (hy : y ≠ NICHE) :
    (run tplN_sub 30 s).r 0 = encode (arith .sub (decode x) (decode y)) ∧ (run tplN_sub 30 s).pc = tplN_sub.size := by
  have hdx := decode_ne x hx
  have hdy := decode_ne y hy
  simp [run, tplN_sub, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hdx, hdy, arith, arithInt]
  exact sub_core x y

theorem tplN_mul_ok (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) (hx : x ≠ NICHE) (hy : y ≠ NICHE) :
    (run tplN_mul 30 s).r 0 = encode (arith .mul (decode x) (decode y)) ∧ (run tplN_mul 30 s).pc = tplN_mul.size := by
  have hdx := decode_ne x hx
  have hdy := decode_ne y hy
  simp [run, tplN_mul, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hdx, hdy, arith, arithInt]
  exact mul_core x y

theorem tplN_div_ok (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) (hx : x ≠ NICHE) (hy : y ≠ NICHE) :
    (run tplN_div 30 s).r 0 = encode (arith .div (decode x) (decode y)) ∧ (run tplN_div 30 s).pc = tplN_div.size := by
  have hdx := decode_ne x hx
  have hdy := decode_ne y hy
  by_cases hy0 : y = 0
  · have hz : decide (y = immW 0) = true := by rw [immW_zero]; exact decide_eq_true hy0
    have h0 : (0 : W).toInt = 0 := by decide
    have hyt : y.toInt = 0 := by rw [hy0]; exact h0
    have hdy0 : decode y = some 0 := by rw [hdy, hyt]
    simp [run, tplN_div, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hz]
    rw [hdx, hdy0]; simp [arith, arithInt, encode]
  · have hz : decide (y = immW 0) = false := by rw [immW_zero]; exact decide_eq_false hy0
    have hyz : y.toInt ≠ 0 := fun e => hy0 (by apply BitVec.eq_of_toInt_eq; rw [e]; simp)
    simp [run, tplN_div, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hdx, hdy, arith, arithInt, hz, hyz]
    have h := div_core x y hx
    simp only [hy0, hyz, ite_false, if_false] at h
    exact h

theorem tplN_mod_ok (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) (hx : x ≠ NICHE) (hy : y ≠ NICHE) :
    (run tplN_mod 30 s).r 0 = encode (arith .mod (decode x) (decode y)) ∧ (run tplN_mod 30 s).pc = tplN_mod.size := by
  have hdx := decode_ne x hx
  have hdy := decode_ne y hy
  by_cases hy0 : y = 0
  · have hz : decide (y = immW 0) = true := by rw [immW_zero]; exact decide_eq_true hy0
    have h0 : (0 : W).toInt = 0 := by decide
    have hyt : y.toInt = 0 := by rw [hy0]; exact h0
    have hdy0 : decode y = some 0 := by rw [hdy, hyt]
    simp [run, tplN_mod, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hz]
    rw [hdx, hdy0]; simp [arith, arithInt, encode]
  · have hz : decide (y = immW 0) = false := by rw [immW_zero]; exact decide_eq_false hy0
    have hyz : y.toInt ≠ 0 := fun e => hy0 (by apply BitVec.eq_of_toInt_eq; rw [e]; simp)
    simp [run, tplN_mod, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hdx, hdy, arith, arithInt, hz, hyz]
    have h := mod_core x y hx
    simp only [hy0, hyz, ite_false, if_false] at h
    exact h

theorem tplL_add_ok (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) (hy : y ≠ NICHE) :
    (run tplL_add 30 s).r 0 = encode (arith .add (decode x) (decode y)) ∧ (run tplL_add 30 s).pc = tplL_add.size := by
  by_cases hx : x = NICHE
  · subst hx
    have : decode NICHE = none := by simp [decode]
    simp [run, tplL_add, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, this, arith_none_left, encode_decode]
  · have hdx := decode_ne x hx
    have hdy := decode_ne y hy
    simp [run, tplL_add, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hdx, hdy, arith, arithInt]
    exact add_core x y

theorem tplL_sub_ok (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) (hy : y ≠ NICHE) :
    (run tplL_sub 30 s).r 0 = encode (arith .sub (decode x) (decode y)) ∧ (run tplL_sub 30 s).pc = tplL_sub.size := by
  by_cases hx : x = NICHE
  · subst hx
    have : decode NICHE = none := by simp [decode]
    simp [run, tplL_sub, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, this, arith_none_left, encode_decode]
  · have hdx := decode_ne x hx
    have hdy := decode_ne y hy
    simp [run, tplL_sub, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hdx, hdy, arith, arithInt]
    exact sub_core x y

theorem tplL_mul_ok (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) (hy : y ≠ NICHE) :
    (run tplL_mul 30 s).r 0 = encode (arith .mul (decode x) (decode y)) ∧ (run tplL_mul 30 s).pc = tplL_mul.size := by
  by_cases hx : x = NICHE
  · subst hx
    have : decode NICHE = none := by simp [decode]
    simp [run, tplL_mul, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, this, arith_none_left, encode_decode]
  · have hdx := decode_ne x hx
    have hdy := decode_ne y hy
    simp [run, tplL_mul, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hdx, hdy, arith, arithInt]
    exact mul_core x y

theorem tplL_div_ok (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) (hy : y ≠ NICHE) :
    (run tplL_div 30 s).r 0 = encode (arith .div (decode x) (decode y)) ∧ (run tplL_div 30 s).pc = tplL_div.size := by
  by_cases hx : x = NICHE
  · subst hx
    have : decode NICHE = none := by simp [decode]
    simp [run, tplL_div, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, this, arith_none_left, encode_decode]
  · have hdx := decode_ne x hx
    have hdy := decode_ne y hy
    by_cases hy0 : y = 0
    · have hz : decide (y = immW 0) = true := by rw [immW_zero]; exact decide_eq_true hy0
      have h0 : (0 : W).toInt = 0 := by decide
      have hyt : y.toInt = 0 := by rw [hy0]; exact h0
      have hdy0 : decode y = some 0 := by rw [hdy, hyt]
      simp [run, tplL_div, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hz]
      rw [hdx, hdy0]; simp [arith, arithInt, encode]
    · have hz : decide (y = immW 0) = false := by rw [immW_zero]; exact decide_eq_false hy0
      have hyz : y.toInt ≠ 0 := fun e => hy0 (by apply BitVec.eq_of_toInt_eq; rw [e]; simp)
      simp [run, tplL_div, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hdx, hdy, arith, arithInt, hz, hyz]
      have h := div_core x y hx
      simp only [hy0, hyz, ite_false, if_false] at h
      exact h

theorem tplL_mod_ok (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) (hy : y ≠ NICHE) :
    (run tplL_mod 30 s).r 0 = encode (arith .mod (decode x) (decode y)) ∧ (run tplL_mod 30 s).pc = tplL_mod.size := by
  by_cases hx : x = NICHE
  · subst hx
    have : decode NICHE = none := by simp [decode]
    simp [run, tplL_mod, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, this, arith_none_left, encode_decode]
  · have hdx := decode_ne x hx
    have hdy := decode_ne y hy
    by_cases hy0 : y = 0
    · have hz : decide (y = immW 0) = true := by rw [immW_zero]; exact decide_eq_true hy0
      have h0 : (0 : W).toInt = 0 := by decide
      have hyt : y.toInt = 0 := by rw [hy0]; exact h0
      have hdy0 : decode y = some 0 := by rw [hdy, hyt]
      simp [run, tplL_mod, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hz]
      rw [hdx, hdy0]; simp [arith, arithInt, encode]
    · have hz : decide (y = immW 0) = false := by rw [immW_zero]; exact decide_eq_false hy0
      have hyz : y.toInt ≠ 0 := fun e => hy0 (by apply BitVec.eq_of_toInt_eq; rw [e]; simp)
      simp [run, tplL_mod, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hdx, hdy, arith, arithInt, hz, hyz]
      have h := mod_core x y hx
      simp only [hy0, hyz, ite_false, if_false] at h
      exact h

theorem tplR_add_ok (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) (hx : x ≠ NICHE) :
    (run tplR_add 30 s).r 0 = encode (arith .add (decode x) (decode y)) ∧ (run tplR_add 30 s).pc = tplR_add.size := by
  by_cases hy : y = NICHE
  · subst hy
    have : decode NICHE = none := by simp [decode]
    simp [run, tplR_add, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, this, arith_none_right, encode_decode, hx]
  · have hdx := decode_ne x hx
    have hdy := decode_ne y hy
    simp [run, tplR_add, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hdx, hdy, arith, arithInt]
    exact add_core x y

theorem tplR_sub_ok (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) (hx : x ≠ NICHE) :
    (run tplR_sub 30 s).r 0 = encode (arith .sub (decode x) (decode y)) ∧ (run tplR_sub 30 s).pc = tplR_sub.size := by
  by_cases hy : y = NICHE
  · subst hy
    have : decode NICHE = none := by simp [decode]
    simp [run, tplR_sub, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, this, arith_none_right, encode_decode, hx]
  · have hdx := decode_ne x hx
    have hdy := decode_ne y hy
    simp [run, tplR_sub, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hdx, hdy, arith, arithInt]
    exact sub_core x y

theorem tplR_mul_ok (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) (hx : x ≠ NICHE) :
    (run tplR_mul 30 s).r 0 = encode (arith .mul (decode x) (decode y)) ∧ (run tplR_mul 30 s).pc = tplR_mul.size := by
  by_cases hy : y = NICHE
  · subst hy
    have : decode NICHE = none := by simp [decode]
    simp [run, tplR_mul, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, this, arith_none_right, encode_decode, hx]
  · have hdx := decode_ne x hx
    have hdy := decode_ne y hy
    simp [run, tplR_mul, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hdx, hdy, arith, arithInt]
    exact mul_core x y

theorem tplR_div_ok (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) (hx : x ≠ NICHE) :
    (run tplR_div 30 s).r 0 = encode (arith .div (decode x) (decode y)) ∧ (run tplR_div 30 s).pc = tplR_div.size := by
  by_cases hy : y = NICHE
  · subst hy
    have : decode NICHE = none := by simp [decode]
    simp [run, tplR_div, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, this, arith_none_right, encode_decode, hx]
  · have hdx := decode_ne x hx
    have hdy := decode_ne y hy
    by_cases hy0 : y = 0
    · have hz : decide (y = immW 0) = true := by rw [immW_zero]; exact decide_eq_true hy0
      have h0 : (0 : W).toInt = 0 := by decide
      have hyt : y.toInt = 0 := by rw [hy0]; exact h0
      have hdy0 : decode y = some 0 := by rw [hdy, hyt]
      simp [run, tplR_div, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hz]
      rw [hdx, hdy0]; simp [arith, arithInt, encode]
    · have hz : decide (y = immW 0) = false := by rw [immW_zero]; exact decide_eq_false hy0
      have hyz : y.toInt ≠ 0 := fun e => hy0 (by apply BitVec.eq_of_toInt_eq; rw [e]; simp)
      simp [run, tplR_div, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hdx, hdy, arith, arithInt, hz, hyz]
      have h := div_core x y hx
      simp only [hy0, hyz, ite_false, if_false] at h
      exact h

theorem tplR_mod_ok (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) (hx : x ≠ NICHE) :
    (run tplR_mod 30 s).r 0 = encode (arith .mod (decode x) (decode y)) ∧ (run tplR_mod 30 s).pc = tplR_mod.size := by
  by_cases hy : y = NICHE
  · subst hy
    have : decode NICHE = none := by simp [decode]
    simp [run, tplR_mod, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, this, arith_none_right, encode_decode, hx]
  · have hdx := decode_ne x hx
    have hdy := decode_ne y hy
    by_cases hy0 : y = 0
    · have hz : decide (y = immW 0) = true := by rw [immW_zero]; exact decide_eq_true hy0
      have h0 : (0 : W).toInt = 0 := by decide
      have hyt : y.toInt = 0 := by rw [hy0]; exact h0
      have hdy0 : decode y = some 0 := by rw [hdy, hyt]
      simp [run, tplR_mod, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hz]
      rw [hdx, hdy0]; simp [arith, arithInt, encode]
    · have hz : decide (y = immW 0) = false := by rw [immW_zero]; exact decide_eq_false hy0
      have hyz : y.toInt ≠ 0 := fun e => hy0 (by apply BitVec.eq_of_toInt_eq; rw [e]; simp)
      simp [run, tplR_mod, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hdx, hdy, arith, arithInt, hz, hyz]
      have h := mod_core x y hx
      simp only [hy0, hyz, ite_false, if_false] at h
      exact h


/-! ### 右が 0 でない字面: 0 割りの検査を省いた形 -/

theorem tplZN_div_ok (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) (hy : y ≠ NICHE) (hy0 : y ≠ 0) (hx : x ≠ NICHE) :
    (run tplZN_div 30 s).r 0 = encode (arith .div (decode x) (decode y)) ∧ (run tplZN_div 30 s).pc = tplZN_div.size := by
  have hdx := decode_ne x hx
  have hdy := decode_ne y hy
  have hz : decide (y = immW 0) = false := by rw [immW_zero]; exact decide_eq_false hy0
  have hyz : y.toInt ≠ 0 := fun e => hy0 (by apply BitVec.eq_of_toInt_eq; rw [e]; simp)
  simp [run, tplZN_div, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hdx, hdy, arith, arithInt, hz, hyz]
  have h := div_core x y hx
  simp only [hy0, hyz, ite_false, if_false] at h
  exact h

theorem tplZN_mod_ok (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) (hy : y ≠ NICHE) (hy0 : y ≠ 0) (hx : x ≠ NICHE) :
    (run tplZN_mod 30 s).r 0 = encode (arith .mod (decode x) (decode y)) ∧ (run tplZN_mod 30 s).pc = tplZN_mod.size := by
  have hdx := decode_ne x hx
  have hdy := decode_ne y hy
  have hz : decide (y = immW 0) = false := by rw [immW_zero]; exact decide_eq_false hy0
  have hyz : y.toInt ≠ 0 := fun e => hy0 (by apply BitVec.eq_of_toInt_eq; rw [e]; simp)
  simp [run, tplZN_mod, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hdx, hdy, arith, arithInt, hz, hyz]
  have h := mod_core x y hx
  simp only [hy0, hyz, ite_false, if_false] at h
  exact h

theorem tplZL_div_ok (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) (hy : y ≠ NICHE) (hy0 : y ≠ 0) :
    (run tplZL_div 30 s).r 0 = encode (arith .div (decode x) (decode y)) ∧ (run tplZL_div 30 s).pc = tplZL_div.size := by
  by_cases hx : x = NICHE
  · subst hx
    have : decode NICHE = none := by simp [decode]
    simp [run, tplZL_div, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, this, arith_none_left, encode_decode]
  · have hdx := decode_ne x hx
    have hdy := decode_ne y hy
    have hz : decide (y = immW 0) = false := by rw [immW_zero]; exact decide_eq_false hy0
    have hyz : y.toInt ≠ 0 := fun e => hy0 (by apply BitVec.eq_of_toInt_eq; rw [e]; simp)
    simp [run, tplZL_div, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hdx, hdy, arith, arithInt, hz, hyz]
    have h := div_core x y hx
    simp only [hy0, hyz, ite_false, if_false] at h
    exact h

theorem tplZL_mod_ok (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) (hy : y ≠ NICHE) (hy0 : y ≠ 0) :
    (run tplZL_mod 30 s).r 0 = encode (arith .mod (decode x) (decode y)) ∧ (run tplZL_mod 30 s).pc = tplZL_mod.size := by
  by_cases hx : x = NICHE
  · subst hx
    have : decode NICHE = none := by simp [decode]
    simp [run, tplZL_mod, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, this, arith_none_left, encode_decode]
  · have hdx := decode_ne x hx
    have hdy := decode_ne y hy
    have hz : decide (y = immW 0) = false := by rw [immW_zero]; exact decide_eq_false hy0
    have hyz : y.toInt ≠ 0 := fun e => hy0 (by apply BitVec.eq_of_toInt_eq; rw [e]; simp)
    simp [run, tplZL_mod, step, St.set, St.flagsSub, hs, h9, h10, Cond.holds, hx, hy, hdx, hdy, arith, arithInt, hz, hyz]
    have h := mod_core x y hx
    simp only [hy0, hyz, ite_false, if_false] at h
    exact h


/-! ### 命令列をつなげる -/

/-- 1 歩ずつ進んだ道(`pc` が列の中にある間だけ進める) -/
inductive Steps (p : Array I) : St → St → Prop
  | refl (s) : Steps p s s
  | step (s s2) (h : s.pc < p.size) : Steps p (step p[s.pc] s) s2 → Steps p s s2

theorem run_steps (p : Array I) : ∀ (n : Nat) (s : St), Steps p s (run p n s)
  | 0, s => Steps.refl s
  | n + 1, s => by
      by_cases h : s.pc < p.size
      · have : run p (n + 1) s = run p n (step p[s.pc] s) := by simp [run, h]
        rw [this]; exact Steps.step s _ h (run_steps p n _)
      · have : run p (n + 1) s = s := by simp [run, h]
        rw [this]; exact Steps.refl s

theorem Steps.trans {p : Array I} {a b c : St} (h1 : Steps p a b) (h2 : Steps p b c) : Steps p a c := by
  induction h1 with
  | refl s => exact h2
  | step s s2 h _ ih => exact Steps.step s c h (ih h2)

/-- 前に別の列があっても、同じ命令を同じ位置で実行する -/
theorem Steps.left {p : Array I} (q : Array I) {a b : St} (h : Steps p a b) : Steps (p ++ q) a b := by
  induction h with
  | refl s => exact Steps.refl s
  | step s s2 h _ ih =>
      refine Steps.step s s2 (by simp; omega) ?_
      have : (p ++ q)[s.pc]'(by simp; omega) = p[s.pc] := Array.getElem_append_left h
      simpa [this] using ih

theorem holds_pc (c : Cond) (s : St) (x : Nat) : c.holds { s with pc := x } = c.holds s := by cases c <;> rfl

theorem step_shift (i : I) (s : St) (k : Nat) :
    step i { s with pc := s.pc + k } = { step i s with pc := (step i s).pc + k } := by
  cases i <;> simp only [step, St.set, St.flagsSub, holds_pc] <;> (try split) <;> (try simp) <;> (try omega)

/-- 後ろに置いた列は、`pc` を長さぶんずらして実行する -/
theorem Steps.shift (p : Array I) {q : Array I} {a b : St} (h : Steps q a b) :
    Steps (p ++ q) { a with pc := a.pc + p.size } { b with pc := b.pc + p.size } := by
  induction h with
  | refl s => exact Steps.refl _
  | step s s2 h _ ih =>
      refine Steps.step _ _ (by simp; omega) ?_
      have e : (p ++ q)[s.pc + p.size]'(by simp; omega) = q[s.pc] := by
        rw [Array.getElem_append_right (by omega)]; simp
      simp only [e]
      rw [step_shift]
      simpa using ih

/-- つなげる: `p` が終わりまで走り、その後 `q` が終わりまで走るなら、`p ++ q` が終わりまで走る -/
theorem Steps.append {p q : Array I} {a b c : St} (h1 : Steps p a b) (hb : b.pc = p.size)
    (h2 : Steps q { b with pc := 0 } c) :
    Steps (p ++ q) a { c with pc := c.pc + p.size } := by
  have h1' := h1.left q
  have h2' := h2.shift p
  simp only [Nat.zero_add] at h2'
  have : ({ b with pc := p.size } : St) = b := by cases b; simp at hb ⊢; exact hb.symm
  rw [this] at h2'
  exact h1'.trans h2'

/-! ### 式木から命令列へ(整数の `+ - * / %`、字面、変数) -/

inductive CmpOp | lt | le | gt | ge | eq
  deriving DecidableEq

def CmpOp.holds : CmpOp → Int → Int → Bool
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)
  | .gt, a, b => decide (a > b)
  | .ge, a, b => decide (a ≥ b)
  | .eq, a, b => decide (a = b)

/-- 比べ(実装 V6 の読み): 両方が値で成り立てば左の値、そうでなければ `!_` -/
def cmpSem (c : CmpOp) : Option Int → Option Int → Option Int
  | some a, some b => if c.holds a b then some a else none
  | _, _ => none

inductive E
  | lit (n : Int)
  | var (k : Nat)
  | op (o : AOp) (l r : E)
  | neg (e : E)
  | cmp (c : CmpOp) (l r : E)

/-- 意味(`!_` を含む)。変数の値は環境 `ρ` -/
def sem (ρ : Nat → Option Int) : E → Option Int
  | .lit n => clamp n
  | .var k => ρ k
  | .op o l r => arith o (sem ρ l) (sem ρ r)
  | .neg e => (sem ρ e).map (fun a => -a)
  | .cmp c l r => cmpSem c (sem ρ l) (sem ρ r)

def E.lits : E → Prop
  | .lit n => -M ≤ n ∧ n ≤ M
  | .var _ => True
  | .op _ l r => l.lits ∧ r.lits
  | .neg e => e.lits
  | .cmp _ l r => l.lits ∧ r.lits

def E.maxVar : E → Nat
  | .lit _ => 0
  | .var k => k + 1
  | .op _ l r => max l.maxVar r.maxVar
  | .neg e => e.maxVar
  | .cmp _ l r => max l.maxVar r.maxVar

def InR (v : Option Int) : Prop := ∀ z, v = some z → -M ≤ z ∧ z ≤ M

theorem InR_clamp (z : Int) : InR (clamp z) := by
  intro w h; unfold clamp at h; split at h <;> simp_all

theorem InR_arithInt (o : AOp) (a b : Int) : InR (arithInt o a b) := by
  cases o <;> simp only [arithInt] <;> (try split) <;> first | exact InR_clamp _ | (intro z h; cases h)

theorem InR_arith (o : AOp) (a b : Option Int) (ha : InR a) (hb : InR b) : InR (arith o a b) := by
  cases a <;> cases b <;> simp only [arith]
  · intro z h; cases h
  · exact hb
  · exact ha
  · exact InR_arithInt o _ _

theorem InR_neg (v : Option Int) (h : InR v) : InR (v.map (fun a => -a)) := by
  cases v with
  | none => intro z hz; cases hz
  | some a =>
      intro z hz
      have := h a rfl
      simp only [Option.map_some, Option.some.injEq] at hz
      subst hz; unfold M at *; omega

theorem InR_cmp (c : CmpOp) (u v : Option Int) (hu : InR u) : InR (cmpSem c u v) := by
  cases u <;> cases v <;> simp only [cmpSem]
  · intro z h; cases h
  · intro z h; cases h
  · intro z h; cases h
  · split
    · exact hu
    · intro z h; cases h

theorem decode_encode (v : Option Int) (h : InR v) : decode (encode v) = v := by
  cases v with
  | none => simp [encode, decode]
  | some z =>
      obtain ⟨h1, h2⟩ := h z rfl
      have hb : -(2 ^ 63 : Int) ≤ z ∧ z < 2 ^ 63 := by unfold M at h1 h2; omega
      have e : (BitVec.ofInt 64 z).toInt = z := toInt_ofInt' z hb
      have hne : BitVec.ofInt 64 z ≠ NICHE := by
        rw [ne_niche_iff, e]; unfold M at h1; omega
      simp [encode, decode, hne, e]

def I.isStr : I → Bool
  | .str _ _ => true
  | _ => false

theorem step_m (i : I) (s : St) (h : i.isStr = false) : (step i s).m = s.m := by
  cases i <;> simp [I.isStr] at h <;> simp [step, St.set, St.flagsSub] <;> split <;> rfl

theorem Steps.m_eq {p : Array I} {a b : St} (hp : ∀ i ∈ p, i.isStr = false) (h : Steps p a b) : b.m = a.m := by
  induction h with
  | refl s => rfl
  | step s s2 h _ ih =>
      rw [ih, step_m _ _ (hp _ (Array.getElem_mem h))]

theorem tpl_nostr (o : AOp) : ∀ i ∈ tpl o, i.isStr = false := by
  cases o <;> decide

theorem single (i : I) (s : St) (hs : s.pc = 0) : Steps #[i] s (step i s) :=
  Steps.step s _ (by simp [hs]) (by
    have : (#[i] : Array I)[s.pc]'(by simp [hs]) = i := by simp [hs]
    simp only [this]; exact Steps.refl _)

/-- `append` の結果の状態を、`pc` が `(p ++ q).size` の形で言う -/
theorem Steps.append' {p q : Array I} {a b c : St} (h1 : Steps p a b) (hb : b.pc = p.size)
    (h2 : Steps q { b with pc := 0 } c) (hc : c.pc = q.size) :
    Steps (p ++ q) a { c with pc := (p ++ q).size } := by
  have := Steps.append h1 hb h2
  simpa [hc, Nat.add_comm] using this

/-! ### `maybe`(`!_` になりうるか)の健全性と、省略形を使う `compile` -/

def tplN : AOp → Array I
  | .add => tplN_add | .sub => tplN_sub | .mul => tplN_mul | .div => tplN_div | .mod => tplN_mod
def tplL : AOp → Array I
  | .add => tplL_add | .sub => tplL_sub | .mul => tplL_mul | .div => tplL_div | .mod => tplL_mod
def tplR : AOp → Array I
  | .add => tplR_add | .sub => tplR_sub | .mul => tplR_mul | .div => tplR_div | .mod => tplR_mod

/-- 左・右が `!_` になりうるか(`ml`・`mr`)で形を選ぶ。 -/
def tplV (o : AOp) : Bool → Bool → Array I
  | true, true => tpl o
  | false, false => tplN o
  | true, false => tplL o
  | false, true => tplR o

theorem tplV_ok (o : AOp) (ml mr : Bool) (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y)
    (hx : ml = false → x ≠ NICHE) (hy : mr = false → y ≠ NICHE) :
    (run (tplV o ml mr) 30 s).r 0 = encode (arith o (decode x) (decode y)) ∧
      (run (tplV o ml mr) 30 s).pc = (tplV o ml mr).size := by
  cases ml <;> cases mr <;> cases o <;> simp only [tplV, tplN, tplL, tplR]
  all_goals first
    | exact tplN_add_ok s hs x y h9 h10 (hx rfl) (hy rfl) | exact tplN_sub_ok s hs x y h9 h10 (hx rfl) (hy rfl)
    | exact tplN_mul_ok s hs x y h9 h10 (hx rfl) (hy rfl) | exact tplN_div_ok s hs x y h9 h10 (hx rfl) (hy rfl)
    | exact tplN_mod_ok s hs x y h9 h10 (hx rfl) (hy rfl)
    | exact tplL_add_ok s hs x y h9 h10 (hy rfl) | exact tplL_sub_ok s hs x y h9 h10 (hy rfl)
    | exact tplL_mul_ok s hs x y h9 h10 (hy rfl) | exact tplL_div_ok s hs x y h9 h10 (hy rfl)
    | exact tplL_mod_ok s hs x y h9 h10 (hy rfl)
    | exact tplR_add_ok s hs x y h9 h10 (hx rfl) | exact tplR_sub_ok s hs x y h9 h10 (hx rfl)
    | exact tplR_mul_ok s hs x y h9 h10 (hx rfl) | exact tplR_div_ok s hs x y h9 h10 (hx rfl)
    | exact tplR_mod_ok s hs x y h9 h10 (hx rfl)
    | exact tpl_ok _ s hs x y h9 h10

theorem tplV_nostr (o : AOp) (ml mr : Bool) : ∀ i ∈ tplV o ml mr, i.isStr = false := by
  cases ml <;> cases mr <;> cases o <;> decide

/-- 整数の `+ - *` の溢れが無いと言える(値域の解析。`sign_asm.py` の `no_overflow`)ことを、抽象の述語 `nov` で受ける -/
def nzlit : E → Bool
  | .lit n => decide (n ≠ 0)
  | .neg (.lit n) => decide (n ≠ 0)
  | _ => false

/-- `sign_asm.py` の `maybe`(仮引数は `!_` にならない) -/
def mb (nov : AOp → E → E → Bool) : E → Bool
  | .lit _ => false
  | .var _ => false
  | .neg e => mb nov e
  | .cmp _ _ _ => true
  | .op o l r =>
      match o with
      | .add | .sub | .mul => !nov o l r || (mb nov l && mb nov r)
      | .div | .mod => (mb nov l && mb nov r) || !nzlit r

theorem sem_inR (ρ : Nat → Option Int) (hρ : ∀ k, InR (ρ k)) : ∀ e : E, e.lits → InR (sem ρ e)
  | .lit n, _ => InR_clamp n
  | .var k, _ => hρ k
  | .op o l r, h => InR_arith o _ _ (sem_inR ρ hρ l h.1) (sem_inR ρ hρ r h.2)
  | .neg e, h => InR_neg _ (sem_inR ρ hρ e h)
  | .cmp c l r, h => InR_cmp c _ _ (sem_inR ρ hρ l h.1)

theorem arithInt_nz (o : AOp) (a n : Int) (ha : InR (some a)) (hn : n ≠ 0) (ho : o = .div ∨ o = .mod) :
    ∃ z, arithInt o a n = some z := by
  obtain ⟨h1, h2⟩ := ha a rfl
  have hb : -(2 ^ 63 : Int) < a ∧ a < 2 ^ 63 := by unfold M at h1 h2; omega
  rcases ho with rfl | rfl
  · simp only [arithInt, hn, ite_false]
    exact ⟨_, tdiv_in_range a n hb⟩
  · simp only [arithInt, hn, ite_false]
    have hq : (a.tdiv n * n).natAbs ≤ a.natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_tdiv]; exact Nat.div_mul_le_self _ _
    have htm : a - a.tdiv n * n = a.tmod n := by rw [Int.tmod_def]; rw [Int.mul_comm n]
    have hab : (a.tmod n).natAbs ≤ a.natAbs := by rw [Int.natAbs_tmod]; exact Nat.mod_le _ _
    refine ⟨a - a.tdiv n * n, ?_⟩
    unfold clamp M
    rw [htm] at *
    unfold M at h1 h2
    have : -(2 ^ 63 - 1 : Int) ≤ a.tmod n ∧ a.tmod n ≤ 2 ^ 63 - 1 := by omega
    simpa [clamp, M] using this

theorem nz_sem (ρ : Nat → Option Int) (r : E) (hr : r.lits) (hf : nzlit r = true) :
    ∃ n, sem ρ r = some n ∧ n ≠ 0 ∧ -M ≤ n ∧ n ≤ M := by
  cases r with
  | lit n =>
      have hn : n ≠ 0 := by simpa [nzlit] using hf
      have h2 : -M ≤ n ∧ n ≤ M := hr
      exact ⟨n, by simp [sem, clamp, h2], hn, h2⟩
  | var _ => simp [nzlit] at hf
  | op _ _ _ => simp [nzlit] at hf
  | cmp _ _ _ => simp [nzlit] at hf
  | neg e =>
      cases e with
      | lit n =>
          have hn : n ≠ 0 := by simpa [nzlit] using hf
          have h2 : -M ≤ n ∧ n ≤ M := hr
          exact ⟨-n, by simp [sem, clamp, h2], by omega, by unfold M at *; omega, by unfold M at *; omega⟩
      | var _ => simp [nzlit] at hf
      | op _ _ _ => simp [nzlit] at hf
      | cmp _ _ _ => simp [nzlit] at hf
      | neg _ => simp [nzlit] at hf

/-- `mb` が偽なら、`!_` ではない(変数は `!_` ではないとき) -/
theorem mb_sound (nov : AOp → E → E → Bool)
    (hnov : ∀ o l r, nov o l r = true → ∀ ρ a b, sem ρ l = some a → sem ρ r = some b → ∃ z, arithInt o a b = some z)
    (ρ : Nat → Option Int) (hρ : ∀ k, InR (ρ k)) (hv : ∀ k, ∃ z, ρ k = some z) :
    ∀ e : E, e.lits → mb nov e = false → ∃ z, sem ρ e = some z
  | .lit n, h, _ => by
      have h' : -M ≤ n ∧ n ≤ M := h
      exact ⟨n, by simp [sem, clamp, h']⟩
  | .var k, _, _ => hv k
  | .neg e, h, hm => by
      obtain ⟨z, hz⟩ := mb_sound nov hnov ρ hρ hv e h (by simpa [mb] using hm)
      exact ⟨-z, by simp [sem, hz]⟩
  | .op o l r, h, hm => by
      have hl' := h.1
      have hr' := h.2
      by_cases hd : o = .div ∨ o = .mod
      · have hm' : (mb nov l && mb nov r || !nzlit r) = false := by rcases hd with rfl | rfl <;> simpa [mb] using hm
        simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at hm'
        obtain ⟨_, hnz⟩ := hm'
        obtain ⟨n, hn', hn, _⟩ := nz_sem ρ r hr' hnz
        cases hsl : sem ρ l with
        | none => exact ⟨n, by show arith o (sem ρ l) (sem ρ r) = some n; rw [hsl, hn']; rfl⟩
        | some a =>
            obtain ⟨z, hz⟩ := arithInt_nz o a n (hsl ▸ sem_inR ρ hρ l hl') hn hd
            exact ⟨z, by show arith o (sem ρ l) (sem ρ r) = some z; rw [hsl, hn']; simpa [arith] using hz⟩
      · have hm' : (!nov o l r || (mb nov l && mb nov r)) = false := by
          cases o <;> first | simpa [mb] using hm | (exfalso; exact hd (by simp))
        simp only [Bool.or_eq_false_iff, Bool.not_eq_false', Bool.not_not] at hm'
        obtain ⟨hn, hlr⟩ := hm'
        have hk := hnov o l r hn ρ
        by_cases hml : mb nov l = false
        · obtain ⟨a, ha⟩ := mb_sound nov hnov ρ hρ hv l hl' hml
          cases hsr : sem ρ r with
          | none => exact ⟨a, by simp [sem, ha, hsr, arith]⟩
          | some b => obtain ⟨z, hz⟩ := hk a b ha hsr; exact ⟨z, by simp [sem, ha, hsr, arith, hz]⟩
        · have hmr : mb nov r = false := by simpa [hml] using hlr
          obtain ⟨b, hb⟩ := mb_sound nov hnov ρ hρ hv r hr' hmr
          cases hsl : sem ρ l with
          | none => exact ⟨b, by simp [sem, hb, hsl, arith]⟩
          | some a => obtain ⟨z, hz⟩ := hk a b hsl hb; exact ⟨z, by simp [sem, hb, hsl, arith, hz]⟩

theorem encode_ne_niche (z : Int) (h : InR (some z)) : encode (some z) ≠ NICHE := by
  obtain ⟨h1, h2⟩ := h z rfl
  have hb : -(2 ^ 63 : Int) ≤ z ∧ z < 2 ^ 63 := by unfold M at h1 h2; omega
  rw [ne_niche_iff]; simp only [encode]; rw [toInt_ofInt' z hb]; unfold M at h1; omega

def tplZ (o : AOp) : Bool → Array I
  | false => match o with | .mod => tplZN_mod | _ => tplZN_div
  | true => match o with | .mod => tplZL_mod | _ => tplZL_div

/-- 右が 0 でない字面(`nz`)の `/` `%` は 0 割りの検査を省く形、それ以外は `tplV` -/
def tplW (o : AOp) (ml mr nz : Bool) : Array I :=
  if nz = true ∧ (o = .div ∨ o = .mod) ∧ mr = false then tplZ o ml else tplV o ml mr

theorem tplW_ok (o : AOp) (ml mr nz : Bool) (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y)
    (hx : ml = false → x ≠ NICHE) (hy : mr = false → y ≠ NICHE) (hnz : nz = true → y ≠ 0) :
    (run (tplW o ml mr nz) 30 s).r 0 = encode (arith o (decode x) (decode y)) ∧
      (run (tplW o ml mr nz) 30 s).pc = (tplW o ml mr nz).size := by
  unfold tplW
  by_cases hc : nz = true ∧ (o = .div ∨ o = .mod) ∧ mr = false
  · rw [if_pos hc]
    obtain ⟨hn, ho, hm⟩ := hc
    have hy' := hy hm
    have hy0 := hnz hn
    cases ml <;> rcases ho with rfl | rfl <;> simp only [tplZ]
    · exact tplZN_div_ok s hs x y h9 h10 hy' hy0 (hx rfl)
    · exact tplZN_mod_ok s hs x y h9 h10 hy' hy0 (hx rfl)
    · exact tplZL_div_ok s hs x y h9 h10 hy' hy0
    · exact tplZL_mod_ok s hs x y h9 h10 hy' hy0
  · rw [if_neg hc]; exact tplV_ok o ml mr s hs x y h9 h10 hx hy

theorem tplW_nostr (o : AOp) (ml mr nz : Bool) : ∀ i ∈ tplW o ml mr nz, i.isStr = false := by
  unfold tplW
  split
  · cases ml <;> cases o <;> decide
  · exact tplV_nostr o ml mr

theorem nz_enc (ρ : Nat → Option Int) (r : E) (hr : r.lits) (hf : nzlit r = true) : encode (sem ρ r) ≠ 0 := by
  obtain ⟨n, hn', hn, h1, h2⟩ := nz_sem ρ r hr hf
  have hb : -(2 ^ 63 : Int) ≤ n ∧ n < 2 ^ 63 := by unfold M at h1 h2; omega
  intro e
  rw [hn'] at e
  simp only [encode] at e
  have := toInt_ofInt' n hb
  rw [e] at this
  simp at this; omega

/-! ### 符号反転 -/

theorem neg_enc (a : Int) (h : InR (some a)) : 0 - encode (some a) = encode (some (-a)) := by
  obtain ⟨h1, h2⟩ := h a rfl
  have hb : -(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63 := by unfold M at h1 h2; omega
  have hb' : -(2 ^ 63 : Int) ≤ -a ∧ -a < 2 ^ 63 := by unfold M at h1 h2; omega
  simp only [encode]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sub, toInt_ofInt' _ hb']
  have : (0 : W).toInt = 0 := by decide
  rw [this, show ((BitVec.ofInt 64 a).toInt) = a from toInt_ofInt' a hb]
  have h3 : (0 : Int) - a = -a := by omega
  rw [h3]
  exact Int.bmod_eq_of_le (by unfold M at h1 h2; omega) (by unfold M at h1 h2; omega)

theorem neg_enc' (a : Int) (h : InR (some a)) : -encode (some a) = encode (some (-a)) := by
  simpa using neg_enc a h

/-- `-e` の尾: `e` が `!_` になりうるなら、印を見て飛ばす(`b.eq`) -/
def negTail (m : Bool) : Array I :=
  if m then #[I.movz 13, I.cmpR 0 13, I.bc Cond.eq 2, I.neg 0 0] else #[I.neg 0 0]

theorem negTail_ok (m : Bool) (s : St) (hs : s.pc = 0) (v : Option Int) (hv : InR v) (h0 : s.r 0 = encode v)
    (hm : m = false → ∃ a, v = some a) :
    (run (negTail m) 10 s).r 0 = encode (v.map (fun a => -a)) ∧ (run (negTail m) 10 s).pc = (negTail m).size ∧
      (run (negTail m) 10 s).m = s.m := by
  cases m
  · obtain ⟨a, rfl⟩ := hm rfl
    have := neg_enc' a hv
    simp [run, negTail, step, St.set, hs, h0, this]
  · cases v with
    | none => simp [run, negTail, step, St.set, St.flagsSub, hs, h0, Cond.holds, encode]
    | some a =>
        have hne := encode_ne_niche a hv
        have := neg_enc' a hv
        simp [run, negTail, step, St.set, St.flagsSub, hs, h0, Cond.holds, hne, this]

theorem negTail_nostr (m : Bool) : ∀ i ∈ negTail m, i.isStr = false := by
  cases m <;> decide

def simpleR : E → Bool
  | .lit _ => true
  | .var _ => true
  | .neg (.lit _) => true
  | .neg _ => false
  | .op _ _ _ => false
  | .cmp _ _ _ => false

/-- 字面・変数を、レジスタ `d` に置く命令(`sign_asm.py` の `load`) -/
def rldD (d : Nat) : E → I
  | .lit n => I.movi d n
  | .var k => I.ldr d k
  | .neg (.lit n) => I.movi d (-n)
  | .neg _ => I.movi d 0
  | .op _ _ _ => I.movi d 0
  | .cmp _ _ _ => I.movi d 0

def rld (e : E) : I := rldD 10 e

/-! ### 比べ -/

def invCond : CmpOp → Cond
  | .lt => .ge | .le => .gt | .gt => .le | .ge => .lt | .eq => .ne

/-- 比べの尾(`sign_asm.py` の `gen_cmp` の値の形): `x9`・`x10` に項を置いた後、`!_` の印を見て外れへ、`cmp` で外れへ、
    成り立てば `vi`(左の値を `x0` へ)、外れは `!_` -/
def cmpTail (c : CmpOp) (ml mr : Bool) (vi : I) : Array I :=
  let n0 := if ml || mr then 1 else 0
  let gl := if ml then 2 else 0
  let gr := if mr then 2 else 0
  let T := n0 + gl + gr + 5
  (if ml || mr then #[I.movz 13] else #[])
    ++ (if ml then #[I.cmpR 9 13, I.bc Cond.eq (T - 1 - (n0 + 1))] else #[])
    ++ (if mr then #[I.cmpR 10 13, I.bc Cond.eq (T - 1 - (n0 + gl + 1))] else #[])
    ++ #[I.cmpR 9 10, I.bc (invCond c) (T - 1 - (n0 + gl + gr + 1)), vi, I.b 2, I.movz 0]

theorem enc_toInt (x : W) (hx : x ≠ NICHE) : encode (some x.toInt) = x := by
  simp only [encode]
  exact BitVec.ofInt_toInt

theorem inv_holds (c : CmpOp) (s : St) (a b : W) :
    (invCond c).holds (s.flagsSub a b) = !(c.holds a.toInt b.toInt) := by
  cases c <;> simp only [invCond, CmpOp.holds, hold_lt, hold_ge, hold_gt, hold_le, hold_ne] <;>
    (rw [Bool.eq_iff_iff]; simp)

@[simp] theorem fs_z (s : St) (a b : W) : (s.flagsSub a b).z = decide (a = b) := rfl
@[simp] theorem fs_pc (s : St) (a b : W) : (s.flagsSub a b).pc = s.pc := rfl
@[simp] theorem fs_r (s : St) (a b : W) : (s.flagsSub a b).r = s.r := rfl
@[simp] theorem fs_m (s : St) (a b : W) : (s.flagsSub a b).m = s.m := rfl
@[simp] theorem set_pc (s : St) (d : Nat) (x : W) : (s.set d x).pc = s.pc := rfl
@[simp] theorem set_m (s : St) (d : Nat) (x : W) : (s.set d x).m = s.m := rfl

theorem Steps.go {p : Array I} {s s2 : St} (i : I) (h : s.pc < p.size) (hi : p[s.pc] = i)
    (h2 : Steps p (SirZAsm.step i s) s2) : Steps p s s2 := Steps.step s s2 h (by rw [hi]; exact h2)

theorem L_fail (p : Array I) (k : Nat) (hk : k < p.size) (hp : p[k] = I.movz 0) (s : St) (hs : s.pc = k) :
    ∃ s', Steps p s s' ∧ s'.pc = k + 1 ∧ s'.r 0 = NICHE ∧ s'.m = s.m := by
  refine ⟨step (I.movz 0) s, ?_, ?_, ?_, ?_⟩
  · exact Steps.go _ (by omega) (by simp only [hs]; exact hp) (Steps.refl _)
  · simp [step, St.set, hs]
  · simp [step, St.set]
  · simp [step, St.set]

theorem L_guard (p : Array I) (k : Nat) (a t : Nat) (hk : k + 1 < p.size) (h1 : p[k] = I.cmpR a 13)
    (h2 : p[k+1] = I.bc Cond.eq t) (s : St) (hs : s.pc = k) (x : W) (ha : s.r a = x) (h13 : s.r 13 = NICHE) :
    ∃ s', Steps p s s' ∧ s'.m = s.m ∧ s'.r = s.r ∧ (x = NICHE → s'.pc = k + 1 + t) ∧ (x ≠ NICHE → s'.pc = k + 2) := by
  obtain ⟨s1, hs1⟩ : ∃ s1, s1 = step (I.cmpR a 13) s := ⟨_, rfl⟩
  have e1 : s1.z = decide (x = NICHE) := by simp [hs1, step, St.flagsSub, ha, h13]
  have e2 : s1.pc = k + 1 := by simp [hs1, step, St.flagsSub, hs]
  have e3 : s1.r = s.r := by simp [hs1, step, St.flagsSub]
  have e4 : s1.m = s.m := by simp [hs1, step, St.flagsSub]
  have ebt : s1.z = true → step (I.bc Cond.eq t) s1 = { s1 with pc := s1.pc + t } := by
    intro h; simp [step, Cond.holds, h]
  have ebf : s1.z = false → step (I.bc Cond.eq t) s1 = { s1 with pc := s1.pc + 1 } := by
    intro h; simp [step, Cond.holds, h]
  have hp2 : p[s1.pc]'(by omega) = I.bc Cond.eq t := by
    have : s1.pc = k + 1 := e2
    simp only [this]; exact h2
  refine ⟨step (I.bc Cond.eq t) s1, ?_, ?_, ?_, ?_, ?_⟩
  · exact Steps.go _ (by omega) (by subst hs; exact h1) (by rw [← hs1]; exact Steps.go _ (by omega) hp2 (Steps.refl _))
  · by_cases hx : x = NICHE
    · rw [ebt (by simp [e1, hx])]; simp [e4]
    · rw [ebf (by simp [e1, hx])]; simp [e4]
  · by_cases hx : x = NICHE
    · rw [ebt (by simp [e1, hx])]; simp [e3]
    · rw [ebf (by simp [e1, hx])]; simp [e3]
  · intro hx
    rw [ebt (by simp [e1, hx])]; simp [e2]
  · intro hx
    rw [ebf (by simp [e1, hx])]; simp [e2]

theorem L_core (p : Array I) (k : Nat) (c : CmpOp) (vi : I) (hk : k + 4 < p.size)
    (h0 : p[k] = I.cmpR 9 10) (h1 : p[k+1] = I.bc (invCond c) 3) (h2 : p[k+2] = vi)
    (h3 : p[k+3] = I.b 2) (h4 : p[k+4] = I.movz 0)
    (s : St) (hs : s.pc = k) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) (hx : x ≠ NICHE) (hy : y ≠ NICHE)
    (hvi : ∀ st : St, st.m = s.m → step vi st = ({ st with pc := st.pc + 1 } : St).set 0 x) :
    ∃ s', Steps p s s' ∧ s'.pc = k + 5 ∧ s'.r 0 = encode (cmpSem c (some x.toInt) (some y.toInt)) ∧ s'.m = s.m := by
  obtain ⟨s1, hs1⟩ : ∃ s1, s1 = step (I.cmpR 9 10) s := ⟨_, rfl⟩
  have e1 : s1 = ({ s with pc := s.pc + 1 } : St).flagsSub x y := by simp [hs1, step, h9, h10]
  have e2 : s1.pc = k + 1 := by simp [e1, hs]
  have e3 : s1.m = s.m := by simp [e1]
  have e4 : (invCond c).holds s1 = !(c.holds x.toInt y.toInt) := by rw [e1]; exact inv_holds c _ x y
  have hp1 : p[s1.pc]'(by omega) = I.bc (invCond c) 3 := by
    have : s1.pc = k + 1 := e2
    simp only [this]; exact h1
  by_cases hc : c.holds x.toInt y.toInt = true
  · -- 成り立つ: 分岐せず vi, b 2
    have eb : step (I.bc (invCond c) 3) s1 = { s1 with pc := s1.pc + 1 } := by
      simp [step, e4, hc]
    obtain ⟨s2, hs2⟩ : ∃ s2, s2 = { s1 with pc := s1.pc + 1 } := ⟨_, rfl⟩
    have f2 : s2.pc = k + 2 := by simp [hs2, e2]
    have hp2 : p[s2.pc]'(by omega) = vi := by
      have : s2.pc = k + 2 := f2
      simp only [this]; exact h2
    have f3 := hvi s2 (by simp [hs2, e3])
    obtain ⟨s3, hs3⟩ : ∃ s3, s3 = step vi s2 := ⟨_, rfl⟩
    have g3 : s3.pc = k + 3 := by simp [hs3, f3, f2]
    have hp3 : p[s3.pc]'(by omega) = I.b 2 := by
      have : s3.pc = k + 3 := g3
      simp only [this]; exact h3
    refine ⟨step (I.b 2) s3, ?_, ?_, ?_, ?_⟩
    · refine Steps.go _ (by omega) (by subst hs; exact h0) ?_
      rw [← hs1]
      refine Steps.go _ (by omega) hp1 ?_
      rw [eb, ← hs2]
      refine Steps.go _ (by omega) hp2 ?_
      rw [← hs3]
      exact Steps.go _ (by omega) hp3 (Steps.refl _)
    · simp [step, g3]
    · have : s3.r 0 = x := by rw [hs3, f3]; simp [St.set]
      simp [step, this, cmpSem, hc, enc_toInt x hx]
    · have : s3.m = s.m := by rw [hs3, f3]; simp [St.set, hs2, e3]
      simp [step, this]
  · -- 外れ: 分岐して `movz 0`
    have hc' : c.holds x.toInt y.toInt = false := by simpa using hc
    have eb : step (I.bc (invCond c) 3) s1 = { s1 with pc := s1.pc + 3 } := by
      simp [step, e4, hc']
    have f2 : ({ s1 with pc := s1.pc + 3 } : St).pc = k + 4 := by simp [e2]
    obtain ⟨s4, hs4, hp, hr, hm⟩ := L_fail p (k + 4) (by omega) h4 { s1 with pc := s1.pc + 3 } f2
    refine ⟨s4, ?_, ?_, ?_, ?_⟩
    · refine Steps.go _ (by omega) (by subst hs; exact h0) ?_
      rw [← hs1]
      refine Steps.go _ (by omega) hp1 ?_
      rw [eb]; exact hs4
    · omega
    · simp [hr, cmpSem, hc', encode]
    · simp [hm, e3]

theorem L_movz13 (p : Array I) (h : 0 < p.size) (hp : p[0] = I.movz 13) (s : St) (hs : s.pc = 0) :
    ∃ s', Steps p s s' ∧ s'.pc = 1 ∧ s'.r 13 = NICHE ∧ (∀ i, i ≠ 13 → s'.r i = s.r i) ∧ s'.m = s.m := by
  refine ⟨step (I.movz 13) s, Steps.go _ (by omega) (by simp only [hs]; exact hp) (Steps.refl _), ?_, ?_, ?_, ?_⟩
  · simp [step, St.set, hs]
  · simp [step, St.set]
  · intro i hi; simp [step, St.set, hi]
  · simp [step, St.set]

theorem decode_nich : decode NICHE = none := by simp [decode]

theorem cmpTail_ok (c : CmpOp) (ml mr : Bool) (vi : I) (s : St) (hs : s.pc = 0) (x y : W)
    (h9 : s.r 9 = x) (h10 : s.r 10 = y) (hx : ml = false → x ≠ NICHE) (hy : mr = false → y ≠ NICHE)
    (hvi : ∀ st : St, st.m = s.m → step vi st = ({ st with pc := st.pc + 1 } : St).set 0 x) :
    ∃ s', Steps (cmpTail c ml mr vi) s s' ∧ s'.pc = (cmpTail c ml mr vi).size ∧
      s'.r 0 = encode (cmpSem c (decode x) (decode y)) ∧ s'.m = s.m := by
  cases ml <;> cases mr
  · -- 旗なし
    have E : cmpTail c false false vi = #[I.cmpR 9 10, I.bc (invCond c) 3, vi, I.b 2, I.movz 0] := rfl
    obtain ⟨s', h1, h2, h3, h4⟩ := L_core (cmpTail c false false vi) 0 c vi (by simp [E]) (by simp [E]) (by simp [E])
      (by simp [E]) (by simp [E]) (by simp [E]) s hs x y h9 h10 (hx rfl) (hy rfl) hvi
    exact ⟨s', h1, by simpa [E] using h2, by rw [h3, decode_ne _ (hx rfl), decode_ne _ (hy rfl)], h4⟩
  · -- 右だけ
    have E : cmpTail c false true vi = #[I.movz 13, I.cmpR 10 13, I.bc Cond.eq 5, I.cmpR 9 10, I.bc (invCond c) 3, vi, I.b 2, I.movz 0] := rfl
    obtain ⟨s1, h1, p1, r1, o1, m1⟩ := L_movz13 (cmpTail c false true vi) (by simp [E]) (by simp [E]) s hs
    obtain ⟨s2, h2, m2, r2, g1, g2⟩ := L_guard (cmpTail c false true vi) 1 10 5 (by simp [E]) (by simp [E]) (by simp [E])
      s1 p1 y (by rw [o1 10 (by omega), h10]) r1
    by_cases hy0 : y = NICHE
    · have pc2 := g1 hy0
      obtain ⟨s3, h3, p3, r3, m3⟩ := L_fail (cmpTail c false true vi) 7 (by simp [E]) (by simp [E]) s2 (by omega)
      refine ⟨s3, h1.trans (h2.trans h3), by simp [E, p3], ?_, by rw [m3, m2, m1]⟩
      rw [r3, hy0, decode_nich]; simp [cmpSem, encode]
    · have pc2 := g2 hy0
      have e9 : s2.r 9 = x := by rw [r2, o1 9 (by omega), h9]
      have e10 : s2.r 10 = y := by rw [r2, o1 10 (by omega), h10]
      obtain ⟨s3, h3, p3, r3, m3⟩ := L_core (cmpTail c false true vi) 3 c vi (by simp [E]) (by simp [E]) (by simp [E])
        (by simp [E]) (by simp [E]) (by simp [E]) s2 (by omega) x y e9 e10 (hx rfl) hy0 (by
          intro st hst; apply hvi; rw [hst, m2, m1])
      refine ⟨s3, h1.trans (h2.trans h3), by simp [E, p3], ?_, by rw [m3, m2, m1]⟩
      rw [r3, decode_ne _ (hx rfl), decode_ne _ hy0]
  · -- 左だけ
    have E : cmpTail c true false vi = #[I.movz 13, I.cmpR 9 13, I.bc Cond.eq 5, I.cmpR 9 10, I.bc (invCond c) 3, vi, I.b 2, I.movz 0] := rfl
    obtain ⟨s1, h1, p1, r1, o1, m1⟩ := L_movz13 (cmpTail c true false vi) (by simp [E]) (by simp [E]) s hs
    obtain ⟨s2, h2, m2, r2, g1, g2⟩ := L_guard (cmpTail c true false vi) 1 9 5 (by simp [E]) (by simp [E]) (by simp [E])
      s1 p1 x (by rw [o1 9 (by omega), h9]) r1
    by_cases hx0 : x = NICHE
    · have pc2 := g1 hx0
      obtain ⟨s3, h3, p3, r3, m3⟩ := L_fail (cmpTail c true false vi) 7 (by simp [E]) (by simp [E]) s2 (by omega)
      refine ⟨s3, h1.trans (h2.trans h3), by simp [E, p3], ?_, by rw [m3, m2, m1]⟩
      rw [r3, hx0, decode_nich]; simp [cmpSem, encode]
    · have pc2 := g2 hx0
      have e9 : s2.r 9 = x := by rw [r2, o1 9 (by omega), h9]
      have e10 : s2.r 10 = y := by rw [r2, o1 10 (by omega), h10]
      obtain ⟨s3, h3, p3, r3, m3⟩ := L_core (cmpTail c true false vi) 3 c vi (by simp [E]) (by simp [E]) (by simp [E])
        (by simp [E]) (by simp [E]) (by simp [E]) s2 (by omega) x y e9 e10 hx0 (hy rfl) (by
          intro st hst; apply hvi; rw [hst, m2, m1])
      refine ⟨s3, h1.trans (h2.trans h3), by simp [E, p3], ?_, by rw [m3, m2, m1]⟩
      rw [r3, decode_ne _ hx0, decode_ne _ (hy rfl)]
  · -- 両方
    have E : cmpTail c true true vi = #[I.movz 13, I.cmpR 9 13, I.bc Cond.eq 7, I.cmpR 10 13, I.bc Cond.eq 5, I.cmpR 9 10, I.bc (invCond c) 3, vi, I.b 2, I.movz 0] := rfl
    obtain ⟨s1, h1, p1, r1, o1, m1⟩ := L_movz13 (cmpTail c true true vi) (by simp [E]) (by simp [E]) s hs
    obtain ⟨s2, h2, m2, r2, g1, g2⟩ := L_guard (cmpTail c true true vi) 1 9 7 (by simp [E]) (by simp [E]) (by simp [E])
      s1 p1 x (by rw [o1 9 (by omega), h9]) r1
    by_cases hx0 : x = NICHE
    · have pc2 := g1 hx0
      obtain ⟨s3, h3, p3, r3, m3⟩ := L_fail (cmpTail c true true vi) 9 (by simp [E]) (by simp [E]) s2 (by omega)
      refine ⟨s3, h1.trans (h2.trans h3), by simp [E, p3], ?_, by rw [m3, m2, m1]⟩
      rw [r3, hx0, decode_nich]; simp [cmpSem, encode]
    · have pc2 := g2 hx0
      have r13 : s2.r 13 = NICHE := by rw [r2]; exact r1
      obtain ⟨s4, h4, m4, r4, g3, g4⟩ := L_guard (cmpTail c true true vi) 3 10 5 (by simp [E]) (by simp [E]) (by simp [E])
        s2 (by omega) y (by rw [r2, o1 10 (by omega), h10]) r13
      by_cases hy0 : y = NICHE
      · have pc4 := g3 hy0
        obtain ⟨s5, h5, p5, r5, m5⟩ := L_fail (cmpTail c true true vi) 9 (by simp [E]) (by simp [E]) s4 (by omega)
        refine ⟨s5, h1.trans (h2.trans (h4.trans h5)), by simp [E, p5], ?_, by rw [m5, m4, m2, m1]⟩
        rw [r5, hy0, decode_nich]; simp [cmpSem, encode]
      · have pc4 := g4 hy0
        have e9 : s4.r 9 = x := by rw [r4, r2, o1 9 (by omega), h9]
        have e10 : s4.r 10 = y := by rw [r4, r2, o1 10 (by omega), h10]
        obtain ⟨s5, h5, p5, r5, m5⟩ := L_core (cmpTail c true true vi) 5 c vi (by simp [E]) (by simp [E]) (by simp [E])
          (by simp [E]) (by simp [E]) (by simp [E]) s4 (by omega) x y e9 e10 hx0 hy0 (by
            intro st hst; apply hvi; rw [hst, m4, m2, m1])
        refine ⟨s5, h1.trans (h2.trans (h4.trans h5)), by simp [E, p5], ?_, by rw [m5, m4, m2, m1]⟩
        rw [r5, decode_ne _ hx0, decode_ne _ hy0]

/-- 項を取り出す命令: 字面・変数ならその場で `dst` へ、さもなくば枠 `slot` から -/
def ldOp (e : E) (dst slot : Nat) : I := if simpleR e = true then rldD dst e else I.ldr dst slot

/-- 項の用意: 字面・変数でなければ、式を計算して枠 `slot` に預ける -/
def opB (simple : Bool) (code : Array I) (slot : Nat) : Array I :=
  if simple = true then #[] else code ++ #[I.str 0 slot]

/-- `sign_asm.py` に近づけた骨組み: 右が字面・変数なら枠に預けず、左を `x9`、右を `x10` に置く -/
def compileS (nov : AOp → E → E → Bool) (base : Nat) : Nat → E → Array I
  | _, .lit n => #[I.movi 0 n]
  | _, .var k => #[I.ldr 0 k]
  | _, .neg (.lit n) => #[I.movi 0 (-n)]
  | d, .neg e => compileS nov base d e ++ negTail (mb nov e)
  | d, .cmp c l r =>
      let d1 := if simpleR l = true then d else d + 1
      opB (simpleR l) (compileS nov base d l) (base + d)
        ++ opB (simpleR r) (compileS nov base d1 r) (base + d1)
        ++ #[ldOp l 9 (base + d), ldOp r 10 (base + d1)]
        ++ cmpTail c (mb nov l) (mb nov r) (ldOp l 0 (base + d))
  | d, .op o l r =>
      if simpleR r = true then
        compileS nov base d l ++ #[I.mov 9 0] ++ #[rld r] ++ tplW o (mb nov l) (mb nov r) (nzlit r)
      else
        compileS nov base d l ++ #[I.str 0 (base + d)] ++ compileS nov base (d + 1) r
          ++ #[I.mov 10 0, I.ldr 9 (base + d)] ++ tplW o (mb nov l) (mb nov r) (nzlit r)

theorem rldD_ok (ρ : Nat → Option Int) (base : Nat) (d : Nat) (r : E) (hsr : simpleR r = true) (hlr : r.lits) (hv : r.maxVar ≤ base)
    (t : St) (hm : ∀ k < base, t.m k = encode (ρ k)) :
    (step (rldD d r) t).r d = encode (sem ρ r) ∧ (step (rldD d r) t).pc = t.pc + 1 ∧
      (∀ i, i ≠ d → (step (rldD d r) t).r i = t.r i) ∧ (step (rldD d r) t).m = t.m := by
  cases r with
  | lit n =>
      have h2 : -M ≤ n ∧ n ≤ M := hlr
      have hc : clamp n = some n := by simp [clamp, h2]
      simp [rldD, step, St.set, sem, hc, encode]
      intro i hi; simp [hi]
  | var k =>
      have hk : k < base := by simp [E.maxVar] at hv; omega
      simp [rldD, step, St.set, sem, hm k hk]
      intro i hi; simp [hi]
  | op _ _ _ => simp [simpleR] at hsr
  | cmp _ _ _ => simp [simpleR] at hsr
  | neg e =>
      cases e with
      | lit n =>
          have h2 : -M ≤ n ∧ n ≤ M := hlr
          have hc : clamp n = some n := by simp [clamp, h2]
          simp [rldD, step, St.set, sem, hc, encode]
          intro i hi; simp [hi]
      | var _ => simp [simpleR] at hsr
      | op _ _ _ => simp [simpleR] at hsr
      | cmp _ _ _ => simp [simpleR] at hsr
      | neg _ => simp [simpleR] at hsr


theorem rld_ok (ρ : Nat → Option Int) (base : Nat) (r : E) (hsr : simpleR r = true) (hlr : r.lits) (hv : r.maxVar ≤ base)
    (t : St) (hm : ∀ k < base, t.m k = encode (ρ k)) :
    (step (rld r) t).r 10 = encode (sem ρ r) ∧ (step (rld r) t).pc = t.pc + 1 ∧
      (∀ i, i ≠ 10 → (step (rld r) t).r i = t.r i) ∧ (step (rld r) t).m = t.m :=
  rldD_ok ρ base 10 r hsr hlr hv t hm

theorem ldOp_eq (ρ : Nat → Option Int) (base : Nat) (e : E) (dst slot : Nat) (hl : e.lits) (hv : e.maxVar ≤ base)
    (t : St) (hm : ∀ k < base, t.m k = encode (ρ k)) (hs : simpleR e = false → t.m slot = encode (sem ρ e)) :
    step (ldOp e dst slot) t = ({ t with pc := t.pc + 1 } : St).set dst (encode (sem ρ e)) := by
  by_cases h : simpleR e = true
  · simp only [ldOp, h, if_true]
    cases e with
    | lit n =>
        have h2 : -M ≤ n ∧ n ≤ M := hl
        have hc : clamp n = some n := by simp [clamp, h2]
        simp [rldD, step, sem, hc, encode]
    | var k =>
        have hk : k < base := by simp [E.maxVar] at hv; omega
        simp [rldD, step, sem, hm k hk]
    | op _ _ _ => simp [simpleR] at h
    | cmp _ _ _ => simp [simpleR] at h
    | neg e =>
        cases e with
        | lit n =>
            have h2 : -M ≤ n ∧ n ≤ M := hl
            have hc : clamp n = some n := by simp [clamp, h2]
            simp [rldD, step, sem, hc, encode]
        | var _ => simp [simpleR] at h
        | op _ _ _ => simp [simpleR] at h
        | cmp _ _ _ => simp [simpleR] at h
        | neg _ => simp [simpleR] at h
  · have h' : simpleR e = false := by simpa using h
    simp only [ldOp, h', Bool.false_eq_true, if_false]
    simp [step, hs h']

theorem opB_ok (nov : AOp → E → E → Bool) (ρ : Nat → Option Int) (hρ : ∀ k, InR (ρ k)) (base d : Nat) (e : E)
    (hl : e.lits)
    (ih : ∀ s : St, s.pc = 0 → (∀ k < base, s.m k = encode (ρ k)) →
      ∃ s', Steps (compileS nov base d e) s s' ∧ s'.pc = (compileS nov base d e).size ∧
        s'.r 0 = encode (sem ρ e) ∧ (∀ j < base + d, s'.m j = s.m j) ∧ InR (sem ρ e))
    (s : St) (hs : s.pc = 0) (hm : ∀ k < base, s.m k = encode (ρ k)) :
    ∃ s', Steps (opB (simpleR e) (compileS nov base d e) (base + d)) s s' ∧
      s'.pc = (opB (simpleR e) (compileS nov base d e) (base + d)).size ∧
      (∀ j < base + d, s'.m j = s.m j) ∧ (simpleR e = false → s'.m (base + d) = encode (sem ρ e)) := by
  by_cases h : simpleR e = true
  · refine ⟨s, ?_, ?_, fun _ _ => rfl, fun hh => by simp [h] at hh⟩
    · simp only [opB, h, if_true]; exact Steps.refl s
    · simp [opB, h, hs]
  · have h' : simpleR e = false := by simpa using h
    obtain ⟨s1, h1, p1, r1, m1, i1⟩ := ih s hs hm
    let s2 : St := step (I.str 0 (base + d)) { s1 with pc := 0 }
    have h2 : Steps (compileS nov base d e ++ #[I.str 0 (base + d)]) s
        { s2 with pc := (compileS nov base d e ++ #[I.str 0 (base + d)]).size } :=
      Steps.append' h1 p1 (single _ _ rfl) (by simp [s2, step])
    refine ⟨{ s2 with pc := (compileS nov base d e ++ #[I.str 0 (base + d)]).size }, ?_, ?_, ?_, ?_⟩
    · simp only [opB, h', Bool.false_eq_true, if_false]; exact h2
    · simp [opB, h']
    · intro j hj
      have : j ≠ base + d := by omega
      simp [s2, step, this]; exact m1 j hj
    · intro _; simp [s2, step, r1]

theorem compileS_ok (nov : AOp → E → E → Bool)
    (hnov : ∀ o l r, nov o l r = true → ∀ ρ a b, sem ρ l = some a → sem ρ r = some b → ∃ z, arithInt o a b = some z)
    (ρ : Nat → Option Int) (hρ : ∀ k, InR (ρ k)) (hvs : ∀ k, ∃ z, ρ k = some z) (base : Nat) :
    ∀ (e : E) (d : Nat) (s : St), e.lits → e.maxVar ≤ base → s.pc = 0 →
      (∀ k < base, s.m k = encode (ρ k)) →
      ∃ s', Steps (compileS nov base d e) s s' ∧ s'.pc = (compileS nov base d e).size ∧
        s'.r 0 = encode (sem ρ e) ∧ (∀ j < base + d, s'.m j = s.m j) ∧ InR (sem ρ e) := by
  intro e
  induction e with
  | lit n =>
      intro d s hl _ hs _
      have hl' : -M ≤ n ∧ n ≤ M := hl
      refine ⟨step (I.movi 0 n) s, single _ s hs, ?_, ?_, ?_, InR_clamp n⟩
      · simp [step, St.set, hs, compileS]
      · have hc : clamp n = some n := by simp [clamp, hl']
        simp [step, St.set, sem, hc, encode]
      · intro j _; simp [step, St.set]
  | var k =>
      intro d s _ hv hs hm
      refine ⟨step (I.ldr 0 k) s, single _ s hs, ?_, ?_, ?_, hρ k⟩
      · simp [step, St.set, hs, compileS]
      · simp [step, St.set, sem, hm k (by simp [E.maxVar] at hv; omega)]
      · intro j _; simp [step, St.set]
  | neg e ih =>
      intro d s hl hv hs hm
      by_cases hlit : ∃ n, e = .lit n
      · obtain ⟨n, rfl⟩ := hlit
        have hl' : -M ≤ n ∧ n ≤ M := hl
        have hc : clamp n = some n := by simp [clamp, hl']
        refine ⟨step (I.movi 0 (-n)) s, ?_, ?_, ?_, ?_, sem_inR ρ hρ _ hl⟩
        · simpa [compileS] using single (I.movi 0 (-n)) s hs
        · simp [step, St.set, hs, compileS]
        · simp [step, St.set, sem, hc, encode]
        · intro j _; simp [step, St.set]
      · have hG : compileS nov base d (.neg e) = compileS nov base d e ++ negTail (mb nov e) := by
          cases e <;> simp_all [compileS]
        obtain ⟨s1, h1, p1, r1, m1, i1⟩ := ih d s hl hv hs hm
        have hT := negTail_ok (mb nov e) { s1 with pc := 0 } rfl (sem ρ e) i1 r1
          (fun hf => mb_sound nov hnov ρ hρ hvs e hl hf)
        have h5 : Steps (negTail (mb nov e)) { s1 with pc := 0 } (run (negTail (mb nov e)) 10 { s1 with pc := 0 }) :=
          run_steps _ _ _
        refine ⟨{ run (negTail (mb nov e)) 10 { s1 with pc := 0 } with pc := (compileS nov base d (.neg e)).size }, ?_, rfl, ?_, ?_, InR_neg _ i1⟩
        · rw [hG]; exact Steps.append' h1 p1 h5 hT.2.1
        · simp only []; rw [hT.1]; rfl
        · intro j hj; simp only []; rw [hT.2.2]; exact m1 j hj
  | cmp c l r ihl ihr =>
      intro d s hl hv hs hm
      obtain ⟨hll, hlr⟩ := hl
      have hv1 : l.maxVar ≤ base := by simp only [E.maxVar] at hv; omega
      have hv2 : r.maxVar ≤ base := by simp only [E.maxVar] at hv; omega
      have hl_in : InR (sem ρ l) := sem_inR ρ hρ l hll
      have hr_in : InR (sem ρ r) := sem_inR ρ hρ r hlr
      -- 左の用意
      obtain ⟨sA, hA, pA, mA, eA⟩ := opB_ok nov ρ hρ base d l hll (fun t ht hmt => ihl d t hll hv1 ht hmt) s hs hm
      -- 右の用意
      obtain ⟨sB, hB, pB, mB, eB⟩ := opB_ok nov ρ hρ base (if simpleR l = true then d else d + 1) r hlr
        (fun t ht hmt => ihr _ t hlr hv2 ht hmt) { sA with pc := 0 } rfl (by
          intro k hk; show sA.m k = _; rw [mA k (by omega)]; exact hm k hk)
      have hAB := Steps.append' hA pA hB pB
      let tB : St := { sB with pc := (opB (simpleR l) (compileS nov base d l) (base + d)
        ++ opB (simpleR r) (compileS nov base (if simpleR l = true then d else d + 1) r)
          (base + (if simpleR l = true then d else d + 1))).size }
      -- 枠の中身
      have hmB : ∀ k < base, tB.m k = encode (ρ k) := by
        intro k hk
        show sB.m k = _
        rw [mB k (by split <;> omega)]; show sA.m k = _; rw [mA k (by omega)]; exact hm k hk
      have hslotL : simpleR l = false → tB.m (base + d) = encode (sem ρ l) := by
        intro hf
        show sB.m (base + d) = _
        have hd1 : (if simpleR l = true then d else d + 1) = d + 1 := by simp [hf]
        rw [mB (base + d) (by rw [hd1]; omega)]
        exact eA hf
      have hslotR : simpleR r = false → tB.m (base + (if simpleR l = true then d else d + 1)) = encode (sem ρ r) := by
        intro hf; exact eB hf
      -- 二つの取り出し
      have eq9 := ldOp_eq ρ base l 9 (base + d) hll hv1 { tB with pc := 0 } hmB hslotL
      let u1 : St := step (ldOp l 9 (base + d)) { tB with pc := 0 }
      have hu1 : u1 = ({ { tB with pc := 0 } with pc := 0 + 1 } : St).set 9 (encode (sem ρ l)) := eq9
      have hmu1 : ∀ k < base, u1.m k = encode (ρ k) := by
        intro k hk; rw [hu1]; simpa using hmB k hk
      have hslotR1 : simpleR r = false → ({ u1 with pc := 0 } : St).m (base + (if simpleR l = true then d else d + 1)) = encode (sem ρ r) := by
        intro hf; rw [hu1]; simpa using hslotR hf
      have eq10 := ldOp_eq ρ base r 10 (base + (if simpleR l = true then d else d + 1)) hlr hv2 { u1 with pc := 0 }
        (by intro k hk; exact hmu1 k hk) hslotR1
      let u2 : St := step (ldOp r 10 (base + (if simpleR l = true then d else d + 1))) { u1 with pc := 0 }
      have hu2 : u2 = ({ { u1 with pc := 0 } with pc := 0 + 1 } : St).set 10 (encode (sem ρ r)) := eq10
      have h4 : Steps #[ldOp l 9 (base + d), ldOp r 10 (base + (if simpleR l = true then d else d + 1))]
          { tB with pc := 0 } { u2 with pc := 2 } := by
        have := Steps.append' (single (ldOp l 9 (base + d)) { tB with pc := 0 } rfl) (by show u1.pc = 1; rw [hu1]; rfl)
          (single (ldOp r 10 (base + (if simpleR l = true then d else d + 1))) { u1 with pc := 0 } rfl) (by show u2.pc = 1; rw [hu2]; rfl)
        simpa using this
      have hABC := Steps.append' hAB (by simp [tB]) h4 (by simp [hu2])
      -- 比べの尾
      let s5 : St := { u2 with pc := 0 }
      have h9' : s5.r 9 = encode (sem ρ l) := by simp [s5, hu2, hu1, St.set]
      have h10' : s5.r 10 = encode (sem ρ r) := by simp [s5, hu2, St.set]
      have hmu2 : s5.m = tB.m := by simp [s5, hu2, hu1, St.set]
      have hvi : ∀ st : St, st.m = s5.m →
          step (ldOp l 0 (base + d)) st = ({ st with pc := st.pc + 1 } : St).set 0 (encode (sem ρ l)) := by
        intro st hst
        apply ldOp_eq ρ base l 0 (base + d) hll hv1 st
        · intro k hk; rw [hst, hmu2]; exact hmB k hk
        · intro hf; rw [hst, hmu2]; exact hslotL hf
      obtain ⟨sD, hD, pD, rD, mD⟩ := cmpTail_ok c (mb nov l) (mb nov r) (ldOp l 0 (base + d)) s5 rfl
        (encode (sem ρ l)) (encode (sem ρ r)) h9' h10'
        (fun hf => by
          obtain ⟨z, hz⟩ := mb_sound nov hnov ρ hρ hvs l hll hf
          rw [hz]; exact encode_ne_niche z (hz ▸ hl_in))
        (fun hf => by
          obtain ⟨z, hz⟩ := mb_sound nov hnov ρ hρ hvs r hlr hf
          rw [hz]; exact encode_ne_niche z (hz ▸ hr_in))
        hvi
      refine ⟨{ sD with pc := (compileS nov base d (.cmp c l r)).size }, ?_, rfl, ?_, ?_, InR_cmp c _ _ hl_in⟩
      · have := Steps.append' hABC (by simp [hu2]) hD pD
        simpa [compileS, Array.append_assoc] using this
      · show sD.r 0 = _
        rw [rD, decode_encode _ hl_in, decode_encode _ hr_in]; rfl
      · intro j hj
        show sD.m j = s.m j
        have hd1 : base + d ≤ base + (if simpleR l = true then d else d + 1) := by split <;> omega
        rw [mD, hmu2]
        show sB.m j = _
        rw [mB j (by omega)]; show sA.m j = _; exact mA j hj
  | op o l r ihl ihr =>
      intro d s hl hv hs hm
      obtain ⟨hll, hlr⟩ := hl
      by_cases hsr : simpleR r = true
      · have hv1 : l.maxVar ≤ base := by simp only [E.maxVar] at hv; omega
        have hv2 : r.maxVar ≤ base := by simp only [E.maxVar] at hv; omega
        obtain ⟨s1, h1, p1, r1, m1, i1⟩ := ihl d s hll hv1 hs hm
        let s2 : St := step (I.mov 9 0) { s1 with pc := 0 }
        have h2 : Steps (compileS nov base d l ++ #[I.mov 9 0]) s
            { s2 with pc := (compileS nov base d l ++ #[I.mov 9 0]).size } :=
          Steps.append' h1 p1 (single _ _ rfl) (by simp [s2, step, St.set])
        let t2 : St := { s2 with pc := (compileS nov base d l ++ #[I.mov 9 0]).size }
        let s3 : St := step (rld r) { t2 with pc := 0 }
        have hR := rld_ok ρ base r hsr hlr hv2 { t2 with pc := 0 } (by
          intro k hk
          have : t2.m k = s.m k := by simp [t2, s2, step, St.set]; exact m1 k (by omega)
          exact this.trans (hm k hk))
        have hpc3 : s3.pc = 1 := by simpa using hR.2.1
        have h3 : Steps (compileS nov base d l ++ #[I.mov 9 0] ++ #[rld r]) s
            { s3 with pc := (compileS nov base d l ++ #[I.mov 9 0] ++ #[rld r]).size } :=
          Steps.append' h2 (by simp [t2]) (single _ _ rfl) hpc3
        have hr_in : InR (sem ρ r) := sem_inR ρ hρ r hlr
        have hl_in : InR (sem ρ l) := i1
        have hs9 : s3.r 9 = encode (sem ρ l) := by
          rw [show s3.r 9 = _ from hR.2.2.1 9 (by omega)]
          simp [t2, s2, step, St.set, r1]
        have hs10 : s3.r 10 = encode (sem ρ r) := hR.1
        have hs3m : ∀ j, j < base + d → s3.m j = s.m j := by
          intro j hj
          rw [show s3.m = _ from hR.2.2.2]
          simp [t2, s2, step, St.set]; exact m1 j hj
        let s5 : St := { s3 with pc := 0 }
        have h9' : s5.r 9 = encode (sem ρ l) := hs9
        have h10' : s5.r 10 = encode (sem ρ r) := hs10
        have hT := tplW_ok o (mb nov l) (mb nov r) (nzlit r) s5 rfl (s5.r 9) (s5.r 10) rfl rfl
          (fun hf => by
            obtain ⟨z, hz⟩ := mb_sound nov hnov ρ hρ hvs l hll hf
            rw [h9', hz]; exact encode_ne_niche z (hz ▸ hl_in))
          (fun hf => by
            obtain ⟨z, hz⟩ := mb_sound nov hnov ρ hρ hvs r hlr hf
            rw [h10', hz]; exact encode_ne_niche z (hz ▸ hr_in))
          (fun hf => by rw [h10']; exact nz_enc ρ r hlr hf)
        have h5 : Steps (tplW o (mb nov l) (mb nov r) (nzlit r)) s5 (run (tplW o (mb nov l) (mb nov r) (nzlit r)) 30 s5) := run_steps _ _ _
        have hmm : (run (tplW o (mb nov l) (mb nov r) (nzlit r)) 30 s5).m = s5.m := Steps.m_eq (tplW_nostr o _ _ _) h5
        refine ⟨{ run (tplW o (mb nov l) (mb nov r) (nzlit r)) 30 s5 with pc := (compileS nov base d (.op o l r)).size }, ?_, rfl, ?_, ?_, InR_arith o _ _ hl_in hr_in⟩
        · have := Steps.append' h3 (by simp [hpc3]) h5 hT.2
          simpa [compileS, hsr, Array.append_assoc] using this
        · simp only []
          rw [hT.1, h9', h10', decode_encode _ hl_in, decode_encode _ hr_in]; rfl
        · intro j hj
          simp only []
          rw [hmm]
          exact hs3m j (by omega)
      · have hsr' : simpleR r = false := by simpa using hsr
        have hv1 : l.maxVar ≤ base := by simp only [E.maxVar] at hv; omega
        have hv2 : r.maxVar ≤ base := by simp only [E.maxVar] at hv; omega
        obtain ⟨s1, h1, p1, r1, m1, i1⟩ := ihl d s hll hv1 hs hm
        let s2 : St := step (I.str 0 (base + d)) { s1 with pc := 0 }
        have h2 : Steps (compileS nov base d l ++ #[I.str 0 (base + d)]) s
            { s2 with pc := (compileS nov base d l ++ #[I.str 0 (base + d)]).size } :=
          Steps.append' h1 p1 (single _ _ rfl) (by simp [s2, step])
        let t2 : St := { s2 with pc := (compileS nov base d l ++ #[I.str 0 (base + d)]).size }
        have t2m : ∀ j, t2.m j = if j = base + d then s1.r 0 else s1.m j := by
          intro j; simp [t2, s2, step]
        obtain ⟨s3, h3, p3, r3, m3, i3⟩ := ihr (d + 1) { t2 with pc := 0 } hlr hv2 rfl (by
          intro k hk
          have : k ≠ base + d := by omega
          show t2.m k = _
          rw [t2m, if_neg this, m1 k (by omega)]; exact hm k hk)
        have h23 := Steps.append' h2 (by simp [t2]) h3 p3
        let t3 : St := { s3 with pc := (compileS nov base d l ++ #[I.str 0 (base + d)] ++ compileS nov base (d + 1) r).size }
        let u : St := step (I.mov 10 0) { t3 with pc := 0 }
        let s4 : St := step (I.ldr 9 (base + d)) { u with pc := 0 }
        have h4 : Steps #[I.mov 10 0, I.ldr 9 (base + d)] { t3 with pc := 0 } { s4 with pc := 2 } := by
          have := Steps.append' (single (I.mov 10 0) { t3 with pc := 0 } rfl) (by simp [step, St.set])
            (single (I.ldr 9 (base + d)) { u with pc := 0 } rfl) (by simp [s4, step, St.set])
          simpa using this
        have hm9 : s4.r 9 = encode (sem ρ l) := by
          have a1 : s3.m (base + d) = t2.m (base + d) := m3 (base + d) (by omega)
          simp only [s4, u, step, St.set, t3]
          simp [a1, t2m, r1]
        have hm10 : s4.r 10 = encode (sem ρ r) := by
          simp [s4, u, step, St.set, t3, r3]
        have h234 := Steps.append' h23 (by simp [t3]) h4 (by simp [s4, step, St.set])
        have hl_in : InR (sem ρ l) := i1
        have hr_in : InR (sem ρ r) := i3
        let s5 : St := { s4 with pc := 0 }
        have h9' : s5.r 9 = encode (sem ρ l) := hm9
        have h10' : s5.r 10 = encode (sem ρ r) := hm10
        have hT := tplW_ok o (mb nov l) (mb nov r) (nzlit r) s5 rfl (s5.r 9) (s5.r 10) rfl rfl
          (fun hf => by
            obtain ⟨z, hz⟩ := mb_sound nov hnov ρ hρ hvs l hll hf
            rw [h9', hz]; exact encode_ne_niche z (hz ▸ hl_in))
          (fun hf => by
            obtain ⟨z, hz⟩ := mb_sound nov hnov ρ hρ hvs r hlr hf
            rw [h10', hz]; exact encode_ne_niche z (hz ▸ hr_in))
          (fun hf => by rw [h10']; exact nz_enc ρ r hlr hf)
        have h5 : Steps (tplW o (mb nov l) (mb nov r) (nzlit r)) s5 (run (tplW o (mb nov l) (mb nov r) (nzlit r)) 30 s5) := run_steps _ _ _
        have hmm : (run (tplW o (mb nov l) (mb nov r) (nzlit r)) 30 s5).m = s5.m := Steps.m_eq (tplW_nostr o _ _ _) h5
        refine ⟨{ run (tplW o (mb nov l) (mb nov r) (nzlit r)) 30 s5 with pc := (compileS nov base d (.op o l r)).size }, ?_, rfl, ?_, ?_, InR_arith o _ _ hl_in hr_in⟩
        · have := Steps.append' h234 (by simp [s4, step, St.set]) h5 hT.2
          simpa [compileS, hsr', Array.append_assoc] using this
        · simp only []
          rw [hT.1, h9', h10', decode_encode _ hl_in, decode_encode _ hr_in]; rfl
        · intro j hj
          simp only []
          rw [hmm]
          have a1 : s3.m j = t2.m j := m3 j (by omega)
          simp only [s5, s4, u, step, St.set, t3, a1, t2m]
          have : j ≠ base + d := by omega
          rw [if_neg this]; exact m1 j (by omega)

/-! ### 値域の解析 `no_overflow`(`sign_asm.py` の `const_int` + `no_overflow`)の写し -/

/-- 定数の整数の式の値(字面・`+ - *` の定数。`sign_asm.py` の `const_int`)。範囲の外は定数としない -/
def cst : E → Option Int
  | .lit n => clamp n
  | .var _ => none
  | .cmp _ _ _ => none
  | .neg e => (cst e).map (fun a => -a)
  | .op o l r =>
      match o with
      | .add | .sub | .mul =>
          match cst l, cst r with
          | some a, some b => arithInt o a b
          | _, _ => none
      | _ => none

/-- `l op r` は溢れず、結果が `INT64_MIN` にもならないと静的に言えるか(両辺が定数のとき、その値で) -/
def novR (o : AOp) (l r : E) : Bool :=
  match cst l, cst r with
  | some a, some b => (arithInt o a b).isSome
  | _, _ => false

theorem cst_sound (ρ : Nat → Option Int) : ∀ (e : E) (v : Int), cst e = some v → sem ρ e = some v
  | .lit n, v, h => by simpa [cst, sem] using h
  | .var _, v, h => by simp [cst] at h
  | .cmp _ _ _, v, h => by simp [cst] at h
  | .neg e, v, h => by
      simp only [cst] at h
      cases hc : cst e with
      | none => simp [hc] at h
      | some a =>
          simp only [hc, Option.map_some, Option.some.injEq] at h
          have := cst_sound ρ e a hc
          simp [sem, this, h]
  | .op o l r, v, h => by
      cases o <;> simp only [cst] at h
      all_goals first
        | (simp at h; done)
        | (cases hl : cst l with
            | none => simp [hl] at h
            | some a =>
                cases hr : cst r with
                | none => simp [hl, hr] at h
                | some b =>
                    simp only [hl, hr] at h
                    have e1 := cst_sound ρ l a hl
                    have e2 := cst_sound ρ r b hr
                    simp [sem, e1, e2, arith, h])

/-- 値域の解析の健全性: `novR` が真なら、両辺が値のとき演算は溢れない -/
theorem novR_sound : ∀ o l r, novR o l r = true → ∀ ρ a b, sem ρ l = some a → sem ρ r = some b →
    ∃ z, arithInt o a b = some z := by
  intro o l r h ρ a b ha hb
  unfold novR at h
  cases hl : cst l with
  | none => simp [hl] at h
  | some a' =>
      cases hr : cst r with
      | none => simp [hl, hr] at h
      | some b' =>
          simp only [hl, hr] at h
          have e1 := cst_sound ρ l a' hl
          have e2 := cst_sound ρ r b' hr
          rw [ha] at e1; rw [hb] at e2
          cases e1; cases e2
          cases hz : arithInt o a b with
          | none => simp [hz] at h
          | some z => exact ⟨z, rfl⟩

/-- 実際の値域の解析 `novR` を使った `compileS` の保存(仮定は、変数が `!_` でない整数であることだけ) -/
theorem compileS_ok_real (ρ : Nat → Option Int) (hρ : ∀ k, InR (ρ k)) (hvs : ∀ k, ∃ z, ρ k = some z) (base : Nat) :
    ∀ (e : E) (d : Nat) (s : St), e.lits → e.maxVar ≤ base → s.pc = 0 →
      (∀ k < base, s.m k = encode (ρ k)) →
      ∃ s', Steps (compileS novR base d e) s s' ∧ s'.pc = (compileS novR base d e).size ∧
        s'.r 0 = encode (sem ρ e) ∧ (∀ j < base + d, s'.m j = s.m j) ∧ InR (sem ρ e) :=
  compileS_ok novR novR_sound ρ hρ hvs base

/-- 条件の尾: 値の形から `vi`・`b`・`movz 0` を除き、外れは `fo`(尾の先頭から数えた飛び先)へ飛ぶ -/
def condTail (c : CmpOp) (ml mr : Bool) (fo : Nat) : Array I :=
  let n0 := if ml || mr then 1 else 0
  let gl := if ml then 2 else 0
  let gr := if mr then 2 else 0
  (if ml || mr then #[I.movz 13] else #[])
    ++ (if ml then #[I.cmpR 9 13, I.bc Cond.eq (fo - (n0 + 1))] else #[])
    ++ (if mr then #[I.cmpR 10 13, I.bc Cond.eq (fo - (n0 + gl + 1))] else #[])
    ++ #[I.cmpR 9 10, I.bc (invCond c) (fo - (n0 + gl + gr + 1))]

theorem L_brk (p : Array I) (k : Nat) (c : CmpOp) (t : Nat) (hk : k + 1 < p.size)
    (h0 : p[k] = I.cmpR 9 10) (h1 : p[k+1] = I.bc (invCond c) t)
    (s : St) (hs : s.pc = k) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y) :
    ∃ s', Steps p s s' ∧ s'.m = s.m ∧ (c.holds x.toInt y.toInt = true → s'.pc = k + 2) ∧
      (c.holds x.toInt y.toInt = false → s'.pc = k + 1 + t) := by
  obtain ⟨s1, hs1⟩ : ∃ s1, s1 = step (I.cmpR 9 10) s := ⟨_, rfl⟩
  have e1 : s1 = ({ s with pc := s.pc + 1 } : St).flagsSub x y := by simp [hs1, step, h9, h10]
  have e2 : s1.pc = k + 1 := by simp [e1, hs]
  have e3 : s1.m = s.m := by simp [e1]
  have e4 : (invCond c).holds s1 = !(c.holds x.toInt y.toInt) := by rw [e1]; exact inv_holds c _ x y
  have hp1 : p[s1.pc]'(by omega) = I.bc (invCond c) t := by
    have : s1.pc = k + 1 := e2
    simp only [this]; exact h1
  have ebt : (invCond c).holds s1 = true → step (I.bc (invCond c) t) s1 = { s1 with pc := s1.pc + t } := by
    intro h; simp [step, h]
  have ebf : (invCond c).holds s1 = false → step (I.bc (invCond c) t) s1 = { s1 with pc := s1.pc + 1 } := by
    intro h; simp [step, h]
  refine ⟨step (I.bc (invCond c) t) s1, ?_, ?_, ?_, ?_⟩
  · exact Steps.go _ (by omega) (by simp only [hs]; exact h0)
      (by rw [← hs1]; exact Steps.go _ (by omega) hp1 (Steps.refl _))
  · by_cases h : (invCond c).holds s1 = true
    · rw [ebt h]; simp [e3]
    · rw [ebf (by simpa using h)]; simp [e3]
  · intro hc; rw [ebf (by rw [e4, hc]; rfl)]; simp [e2]
  · intro hc; rw [ebt (by rw [e4, hc]; rfl)]; simp [e2]

theorem isSome_cmpSem (c : CmpOp) (a b : Int) : (cmpSem c (some a) (some b)).isSome = c.holds a b := by
  simp only [cmpSem]; split <;> simp_all

theorem condTail_ok (c : CmpOp) (ml mr : Bool) (fo : Nat) (hfo : (condTail c ml mr fo).size ≤ fo)
    (s : St) (hs : s.pc = 0) (x y : W) (h9 : s.r 9 = x) (h10 : s.r 10 = y)
    (hx : ml = false → x ≠ NICHE) (hy : mr = false → y ≠ NICHE) :
    ∃ s', Steps (condTail c ml mr fo) s s' ∧
      ((cmpSem c (decode x) (decode y)).isSome = true → s'.pc = (condTail c ml mr fo).size) ∧
      ((cmpSem c (decode x) (decode y)).isSome = false → s'.pc = fo) ∧ s'.m = s.m := by
  cases ml <;> cases mr
  · have E : condTail c false false fo = #[I.cmpR 9 10, I.bc (invCond c) (fo - 1)] := rfl
    obtain ⟨s', h1, m1, t1, t2⟩ := L_brk (condTail c false false fo) 0 c (fo - 1) (by simp [E]) (by simp [E]) (by simp [E])
      s hs x y h9 h10
    have dx := decode_ne x (hx rfl); have dy := decode_ne y (hy rfl)
    refine ⟨s', h1, ?_, ?_, m1⟩
    · intro h; rw [dx, dy, isSome_cmpSem] at h; have := t1 h; simpa [E] using this
    · intro h; rw [dx, dy, isSome_cmpSem] at h; have := t2 h; simp [E] at hfo; omega
  · have E : condTail c false true fo = #[I.movz 13, I.cmpR 10 13, I.bc Cond.eq (fo - 2), I.cmpR 9 10, I.bc (invCond c) (fo - 4)] := rfl
    have hsz : (condTail c false true fo).size = 5 := by rw [E]; rfl
    have hf5 : 5 ≤ fo := by omega
    obtain ⟨s1, h1, p1, r1, o1, m1⟩ := L_movz13 (condTail c false true fo) (by simp [E]) (by simp [E]) s hs
    obtain ⟨s2, h2, m2, r2, g1, g2⟩ := L_guard (condTail c false true fo) 1 10 (fo - 2) (by simp [E]) (by simp [E]) (by simp [E])
      s1 p1 y (by rw [o1 10 (by omega), h10]) r1
    by_cases hy0 : y = NICHE
    · have pc2 := g1 hy0
      refine ⟨s2, h1.trans h2, ?_, ?_, by rw [m2, m1]⟩
      · intro h; rw [hy0, decode_nich] at h; simp [cmpSem] at h
      · intro _; omega
    · have pc2 := g2 hy0
      have e9 : s2.r 9 = x := by rw [r2, o1 9 (by omega), h9]
      have e10 : s2.r 10 = y := by rw [r2, o1 10 (by omega), h10]
      obtain ⟨s3, h3, m3, t1, t2⟩ := L_brk (condTail c false true fo) 3 c (fo - 4) (by simp [E]) (by simp [E]) (by simp [E])
        s2 (by omega) x y e9 e10
      have dx := decode_ne x (hx rfl); have dy := decode_ne y hy0
      refine ⟨s3, h1.trans (h2.trans h3), ?_, ?_, by rw [m3, m2, m1]⟩
      · intro h; rw [dx, dy, isSome_cmpSem] at h; have := t1 h; omega
      · intro h; rw [dx, dy, isSome_cmpSem] at h; have := t2 h; omega
  · have E : condTail c true false fo = #[I.movz 13, I.cmpR 9 13, I.bc Cond.eq (fo - 2), I.cmpR 9 10, I.bc (invCond c) (fo - 4)] := rfl
    have hsz : (condTail c true false fo).size = 5 := by rw [E]; rfl
    have hf5 : 5 ≤ fo := by omega
    obtain ⟨s1, h1, p1, r1, o1, m1⟩ := L_movz13 (condTail c true false fo) (by simp [E]) (by simp [E]) s hs
    obtain ⟨s2, h2, m2, r2, g1, g2⟩ := L_guard (condTail c true false fo) 1 9 (fo - 2) (by simp [E]) (by simp [E]) (by simp [E])
      s1 p1 x (by rw [o1 9 (by omega), h9]) r1
    by_cases hx0 : x = NICHE
    · have pc2 := g1 hx0
      refine ⟨s2, h1.trans h2, ?_, ?_, by rw [m2, m1]⟩
      · intro h; rw [hx0, decode_nich] at h; simp [cmpSem] at h
      · intro _; omega
    · have pc2 := g2 hx0
      have e9 : s2.r 9 = x := by rw [r2, o1 9 (by omega), h9]
      have e10 : s2.r 10 = y := by rw [r2, o1 10 (by omega), h10]
      obtain ⟨s3, h3, m3, t1, t2⟩ := L_brk (condTail c true false fo) 3 c (fo - 4) (by simp [E]) (by simp [E]) (by simp [E])
        s2 (by omega) x y e9 e10
      have dx := decode_ne x hx0; have dy := decode_ne y (hy rfl)
      refine ⟨s3, h1.trans (h2.trans h3), ?_, ?_, by rw [m3, m2, m1]⟩
      · intro h; rw [dx, dy, isSome_cmpSem] at h; have := t1 h; omega
      · intro h; rw [dx, dy, isSome_cmpSem] at h; have := t2 h; omega
  · have E : condTail c true true fo = #[I.movz 13, I.cmpR 9 13, I.bc Cond.eq (fo - 2), I.cmpR 10 13, I.bc Cond.eq (fo - 4), I.cmpR 9 10, I.bc (invCond c) (fo - 6)] := rfl
    have hsz : (condTail c true true fo).size = 7 := by rw [E]; rfl
    have hf5 : 7 ≤ fo := by omega
    obtain ⟨s1, h1, p1, r1, o1, m1⟩ := L_movz13 (condTail c true true fo) (by simp [E]) (by simp [E]) s hs
    obtain ⟨s2, h2, m2, r2, g1, g2⟩ := L_guard (condTail c true true fo) 1 9 (fo - 2) (by simp [E]) (by simp [E]) (by simp [E])
      s1 p1 x (by rw [o1 9 (by omega), h9]) r1
    by_cases hx0 : x = NICHE
    · have pc2 := g1 hx0
      refine ⟨s2, h1.trans h2, ?_, ?_, by rw [m2, m1]⟩
      · intro h; rw [hx0, decode_nich] at h; simp [cmpSem] at h
      · intro _; omega
    · have pc2 := g2 hx0
      have r13 : s2.r 13 = NICHE := by rw [r2]; exact r1
      obtain ⟨s4, h4, m4, r4, g3, g4⟩ := L_guard (condTail c true true fo) 3 10 (fo - 4) (by simp [E]) (by simp [E]) (by simp [E])
        s2 (by omega) y (by rw [r2, o1 10 (by omega), h10]) r13
      by_cases hy0 : y = NICHE
      · have pc4 := g3 hy0
        refine ⟨s4, h1.trans (h2.trans h4), ?_, ?_, by rw [m4, m2, m1]⟩
        · intro h; rw [hy0, decode_nich] at h; simp [cmpSem] at h
        · intro _; omega
      · have pc4 := g4 hy0
        have e9 : s4.r 9 = x := by rw [r4, r2, o1 9 (by omega), h9]
        have e10 : s4.r 10 = y := by rw [r4, r2, o1 10 (by omega), h10]
        obtain ⟨s5, h5, m5, t1, t2⟩ := L_brk (condTail c true true fo) 5 c (fo - 6) (by simp [E]) (by simp [E]) (by simp [E])
          s4 (by omega) x y e9 e10
        have dx := decode_ne x hx0; have dy := decode_ne y hy0
        refine ⟨s5, h1.trans (h2.trans (h4.trans h5)), ?_, ?_, by rw [m5, m4, m2, m1]⟩
        · intro h; rw [dx, dy, isSome_cmpSem] at h; have := t1 h; omega
        · intro h; rw [dx, dy, isSome_cmpSem] at h; have := t2 h; omega


/-! ### 条件(`false_label`)-/

def cmpPre (nov : AOp → E → E → Bool) (base d : Nat) (l r : E) : Array I :=
  opB (simpleR l) (compileS nov base d l) (base + d)
    ++ opB (simpleR r) (compileS nov base (if simpleR l = true then d else d + 1) r)
      (base + (if simpleR l = true then d else d + 1))
    ++ #[ldOp l 9 (base + d), ldOp r 10 (base + (if simpleR l = true then d else d + 1))]

theorem compileS_cmp (nov : AOp → E → E → Bool) (base d : Nat) (c : CmpOp) (l r : E) :
    compileS nov base d (.cmp c l r) = cmpPre nov base d l r ++ cmpTail c (mb nov l) (mb nov r) (ldOp l 0 (base + d)) := by
  simp [compileS, cmpPre]

theorem cmpPre_ok (nov : AOp → E → E → Bool)
    (hnov : ∀ o l r, nov o l r = true → ∀ ρ a b, sem ρ l = some a → sem ρ r = some b → ∃ z, arithInt o a b = some z)
    (ρ : Nat → Option Int) (hρ : ∀ k, InR (ρ k)) (hvs : ∀ k, ∃ z, ρ k = some z) (base : Nat) (c : CmpOp) (l r : E)
    (ihl : ∀ (d : Nat) (s : St), l.lits → l.maxVar ≤ base → s.pc = 0 → (∀ k < base, s.m k = encode (ρ k)) →
      ∃ s', Steps (compileS nov base d l) s s' ∧ s'.pc = (compileS nov base d l).size ∧
        s'.r 0 = encode (sem ρ l) ∧ (∀ j < base + d, s'.m j = s.m j) ∧ InR (sem ρ l))
    (ihr : ∀ (d : Nat) (s : St), r.lits → r.maxVar ≤ base → s.pc = 0 → (∀ k < base, s.m k = encode (ρ k)) →
      ∃ s', Steps (compileS nov base d r) s s' ∧ s'.pc = (compileS nov base d r).size ∧
        s'.r 0 = encode (sem ρ r) ∧ (∀ j < base + d, s'.m j = s.m j) ∧ InR (sem ρ r))
    (d : Nat) (s : St) (hl : (E.cmp c l r).lits) (hv : (E.cmp c l r).maxVar ≤ base) (hs : s.pc = 0)
    (hm : ∀ k < base, s.m k = encode (ρ k)) :
    ∃ u : St, Steps (cmpPre nov base d l r) s u ∧ u.pc = (cmpPre nov base d l r).size ∧
      u.r 9 = encode (sem ρ l) ∧ u.r 10 = encode (sem ρ r) ∧ (∀ k < base, u.m k = encode (ρ k)) ∧
      (∀ j < base + d, u.m j = s.m j) ∧ (simpleR l = false → u.m (base + d) = encode (sem ρ l)) := by
    obtain ⟨hll, hlr⟩ := hl
    have hv1 : l.maxVar ≤ base := by simp only [E.maxVar] at hv; omega
    have hv2 : r.maxVar ≤ base := by simp only [E.maxVar] at hv; omega
    have hl_in : InR (sem ρ l) := sem_inR ρ hρ l hll
    have hr_in : InR (sem ρ r) := sem_inR ρ hρ r hlr
    -- 左の用意
    obtain ⟨sA, hA, pA, mA, eA⟩ := opB_ok nov ρ hρ base d l hll (fun t ht hmt => ihl d t hll hv1 ht hmt) s hs hm
    -- 右の用意
    obtain ⟨sB, hB, pB, mB, eB⟩ := opB_ok nov ρ hρ base (if simpleR l = true then d else d + 1) r hlr
      (fun t ht hmt => ihr _ t hlr hv2 ht hmt) { sA with pc := 0 } rfl (by
        intro k hk; show sA.m k = _; rw [mA k (by omega)]; exact hm k hk)
    have hAB := Steps.append' hA pA hB pB
    let tB : St := { sB with pc := (opB (simpleR l) (compileS nov base d l) (base + d)
      ++ opB (simpleR r) (compileS nov base (if simpleR l = true then d else d + 1) r)
        (base + (if simpleR l = true then d else d + 1))).size }
    -- 枠の中身
    have hmB : ∀ k < base, tB.m k = encode (ρ k) := by
      intro k hk
      show sB.m k = _
      rw [mB k (by split <;> omega)]; show sA.m k = _; rw [mA k (by omega)]; exact hm k hk
    have hslotL : simpleR l = false → tB.m (base + d) = encode (sem ρ l) := by
      intro hf
      show sB.m (base + d) = _
      have hd1 : (if simpleR l = true then d else d + 1) = d + 1 := by simp [hf]
      rw [mB (base + d) (by rw [hd1]; omega)]
      exact eA hf
    have hslotR : simpleR r = false → tB.m (base + (if simpleR l = true then d else d + 1)) = encode (sem ρ r) := by
      intro hf; exact eB hf
    -- 二つの取り出し
    have eq9 := ldOp_eq ρ base l 9 (base + d) hll hv1 { tB with pc := 0 } hmB hslotL
    let u1 : St := step (ldOp l 9 (base + d)) { tB with pc := 0 }
    have hu1 : u1 = ({ { tB with pc := 0 } with pc := 0 + 1 } : St).set 9 (encode (sem ρ l)) := eq9
    have hmu1 : ∀ k < base, u1.m k = encode (ρ k) := by
      intro k hk; rw [hu1]; simpa using hmB k hk
    have hslotR1 : simpleR r = false → ({ u1 with pc := 0 } : St).m (base + (if simpleR l = true then d else d + 1)) = encode (sem ρ r) := by
      intro hf; rw [hu1]; simpa using hslotR hf
    have eq10 := ldOp_eq ρ base r 10 (base + (if simpleR l = true then d else d + 1)) hlr hv2 { u1 with pc := 0 }
      (by intro k hk; exact hmu1 k hk) hslotR1
    let u2 : St := step (ldOp r 10 (base + (if simpleR l = true then d else d + 1))) { u1 with pc := 0 }
    have hu2 : u2 = ({ { u1 with pc := 0 } with pc := 0 + 1 } : St).set 10 (encode (sem ρ r)) := eq10
    have h4 : Steps #[ldOp l 9 (base + d), ldOp r 10 (base + (if simpleR l = true then d else d + 1))]
        { tB with pc := 0 } { u2 with pc := 2 } := by
      have := Steps.append' (single (ldOp l 9 (base + d)) { tB with pc := 0 } rfl) (by show u1.pc = 1; rw [hu1]; rfl)
        (single (ldOp r 10 (base + (if simpleR l = true then d else d + 1))) { u1 with pc := 0 } rfl) (by show u2.pc = 1; rw [hu2]; rfl)
      simpa using this
    have hABC := Steps.append' hAB (by simp [tB]) h4 (by simp [hu2])
    refine ⟨{ u2 with pc := (cmpPre nov base d l r).size }, hABC, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hu2, hu1, St.set]
    · simp [hu2, St.set]
    · intro k hk; show u2.m k = _; simp [hu2, hu1, St.set]; exact hmB k hk
    · intro j hj
      show u2.m j = _
      simp [hu2, hu1, St.set]
      show sB.m j = _
      rw [mB j (by split <;> omega)]; show sA.m j = _; exact mA j hj
    · intro hf; show u2.m (base + d) = _; simp [hu2, hu1, St.set]; exact hslotL hf

/-- 条件の式の木: 値の式、`a & b`(両方が成り立つ)、`a | b`(どちらかが成り立つ)。成り立つ = `!_` でない -/
inductive Cn
  | val (e : E)
  | and (a b : Cn)
  | or (a b : Cn)

def ctruth (ρ : Nat → Option Int) : Cn → Bool
  | .val e => (sem ρ e).isSome
  | .and a b => ctruth ρ a && ctruth ρ b
  | .or a b => ctruth ρ a || ctruth ρ b

def Cn.lits : Cn → Prop
  | .val e => e.lits
  | .and a b => a.lits ∧ b.lits
  | .or a b => a.lits ∧ b.lits

def Cn.maxVar : Cn → Nat
  | .val e => e.maxVar
  | .and a b => max a.maxVar b.maxVar
  | .or a b => max a.maxVar b.maxVar

/-- `sign_asm.py` の `gen_cond`: 成り立たなければ(コードの頭から数えて)`fo` へ飛び、成り立てば下へ流れる -/
def compileC (nov : AOp → E → E → Bool) (base : Nat) : Nat → Nat → Cn → Array I
  | d, fo, .val (.cmp c l r) =>
      cmpPre nov base d l r ++ condTail c (mb nov l) (mb nov r) (fo - (cmpPre nov base d l r).size)
  | d, fo, .val e =>
      if mb nov e = true then
        compileS nov base d e ++ #[I.movz 13, I.cmpR 0 13, I.bc Cond.eq (fo - ((compileS nov base d e).size + 2))]
      else compileS nov base d e
  | d, fo, .and a b =>
      compileC nov base d fo a ++ compileC nov base d (fo - (compileC nov base d fo a).size) b
  | d, fo, .or a b =>
      compileC nov base d ((compileC nov base d 0 a).size + 1) a
        ++ #[I.b ((compileC nov base d (fo - ((compileC nov base d ((compileC nov base d 0 a).size + 1) a).size + 1)) b).size + 1)]
        ++ compileC nov base d (fo - ((compileC nov base d ((compileC nov base d 0 a).size + 1) a).size + 1)) b

theorem condTail_size (c : CmpOp) (ml mr : Bool) (fo fo' : Nat) :
    (condTail c ml mr fo).size = (condTail c ml mr fo').size := by
  cases ml <;> cases mr <;> simp [condTail]

theorem compileC_size (nov : AOp → E → E → Bool) (base : Nat) :
    ∀ (cn : Cn) (d fo fo' : Nat), (compileC nov base d fo cn).size = (compileC nov base d fo' cn).size
  | .val e, d, fo, fo' => by
      cases e with
      | cmp c l r =>
          simp only [compileC, Array.size_append]
          rw [condTail_size c _ _ (fo - _) (fo' - _)]
      | lit n => simp only [compileC]; split <;> simp
      | var k => simp only [compileC]; split <;> simp
      | op o l r => simp only [compileC]; split <;> simp
      | neg e => simp only [compileC]; split <;> simp
  | .and a b, d, fo, fo' => by
      have h1 := compileC_size nov base a d fo fo'
      have h2 := compileC_size nov base b d (fo - (compileC nov base d fo' a).size) (fo' - (compileC nov base d fo' a).size)
      simp only [compileC, Array.size_append]
      rw [h1, h2]
  | .or a b, d, fo, fo' => by
      have h2 := compileC_size nov base b d (fo - ((compileC nov base d ((compileC nov base d 0 a).size + 1) a).size + 1))
        (fo' - ((compileC nov base d ((compileC nov base d 0 a).size + 1) a).size + 1))
      simp only [compileC, Array.size_append, Array.size_singleton]
      rw [h2]

theorem compileC_val (nov : AOp → E → E → Bool) (base d fo : Nat) (e : E) (hnc : ∀ c l r, e ≠ E.cmp c l r) :
    compileC nov base d fo (.val e) =
      if mb nov e = true then
        compileS nov base d e ++ #[I.movz 13, I.cmpR 0 13, I.bc Cond.eq (fo - ((compileS nov base d e).size + 2))]
      else compileS nov base d e := by
  cases e with
  | cmp c l r => exact absurd rfl (hnc c l r)
  | lit n => simp [compileC]
  | var k => simp [compileC]
  | op o l r => simp [compileC]
  | neg e => simp [compileC]

theorem compileC_ok (nov : AOp → E → E → Bool)
    (hnov : ∀ o l r, nov o l r = true → ∀ ρ a b, sem ρ l = some a → sem ρ r = some b → ∃ z, arithInt o a b = some z)
    (ρ : Nat → Option Int) (hρ : ∀ k, InR (ρ k)) (hvs : ∀ k, ∃ z, ρ k = some z) (base : Nat) :
    ∀ (cn : Cn) (d fo : Nat) (s : St), cn.lits → cn.maxVar ≤ base → s.pc = 0 →
      (∀ k < base, s.m k = encode (ρ k)) → (compileC nov base d fo cn).size ≤ fo →
      ∃ s', Steps (compileC nov base d fo cn) s s' ∧
        (ctruth ρ cn = true → s'.pc = (compileC nov base d fo cn).size) ∧
        (ctruth ρ cn = false → s'.pc = fo) ∧ (∀ j < base + d, s'.m j = s.m j) := by
  intro cn
  induction cn with
  | val e =>
      intro d fo s hl hv hs hm hfo
      by_cases hc : ∃ c l r, e = E.cmp c l r
      · obtain ⟨c, l, r, rfl⟩ := hc
        obtain ⟨hll, hlr⟩ := hl
        have hv1 : l.maxVar ≤ base := by simp only [Cn.maxVar, E.maxVar] at hv; omega
        have hv2 : r.maxVar ≤ base := by simp only [Cn.maxVar, E.maxVar] at hv; omega
        have hl_in : InR (sem ρ l) := sem_inR ρ hρ l hll
        have hr_in : InR (sem ρ r) := sem_inR ρ hρ r hlr
        obtain ⟨u, hu, pu, r9, r10, mk, mj, _⟩ := cmpPre_ok nov hnov ρ hρ hvs base c l r
          (fun d s h1 h2 h3 h4 => compileS_ok nov hnov ρ hρ hvs base l d s h1 h2 h3 h4)
          (fun d s h1 h2 h3 h4 => compileS_ok nov hnov ρ hρ hvs base r d s h1 h2 h3 h4)
          d s ⟨hll, hlr⟩ (by simpa [Cn.maxVar] using hv) hs hm
        have hfo' : (condTail c (mb nov l) (mb nov r) (fo - (cmpPre nov base d l r).size)).size
            ≤ fo - (cmpPre nov base d l r).size := by
          simp only [compileC, Array.size_append] at hfo; omega
        obtain ⟨sT, hT, t1, t2, mT⟩ := condTail_ok c (mb nov l) (mb nov r) (fo - (cmpPre nov base d l r).size) hfo'
          { u with pc := 0 } rfl (encode (sem ρ l)) (encode (sem ρ r)) r9 r10
          (fun hf => by
            obtain ⟨z, hz⟩ := mb_sound nov hnov ρ hρ hvs l hll hf
            rw [hz]; exact encode_ne_niche z (hz ▸ hl_in))
          (fun hf => by
            obtain ⟨z, hz⟩ := mb_sound nov hnov ρ hρ hvs r hlr hf
            rw [hz]; exact encode_ne_niche z (hz ▸ hr_in))
        have hA := Steps.append hu pu hT
        have hsz : (compileC nov base d fo (.val (E.cmp c l r))).size
            = (cmpPre nov base d l r).size + (condTail c (mb nov l) (mb nov r) (fo - (cmpPre nov base d l r).size)).size := by
          simp [compileC]
        have hct : ctruth ρ (.val (E.cmp c l r)) = (cmpSem c (decode (encode (sem ρ l))) (decode (encode (sem ρ r)))).isSome := by
          rw [decode_encode _ hl_in, decode_encode _ hr_in]; rfl
        refine ⟨{ sT with pc := sT.pc + (cmpPre nov base d l r).size }, ?_, ?_, ?_, ?_⟩
        · simpa [compileC] using hA
        · intro h; rw [hct] at h; have := t1 h; simp only []; omega
        · intro h; rw [hct] at h; have := t2 h; simp only []; omega
        · intro j hj; show sT.m j = s.m j; rw [mT]; exact mj j hj
      · have hnc : ∀ c l r, e ≠ E.cmp c l r := fun c l r h => hc ⟨c, l, r, h⟩
        rw [compileC_val nov base d fo e hnc] at hfo ⊢
        obtain ⟨s1, h1, p1, r1, m1, i1⟩ := compileS_ok nov hnov ρ hρ hvs base e d s hl hv hs hm
        by_cases hmb : mb nov e = true
        · simp only [hmb, if_true] at hfo ⊢
          have hsz : (compileS nov base d e ++ #[I.movz 13, I.cmpR 0 13, I.bc Cond.eq (fo - ((compileS nov base d e).size + 2))]).size
              = (compileS nov base d e).size + 3 := by simp
          obtain ⟨s2, h2, p2, q2, o2, m2⟩ := L_movz13 #[I.movz 13, I.cmpR 0 13, I.bc Cond.eq (fo - ((compileS nov base d e).size + 2))] (by simp) (by simp) { s1 with pc := 0 } rfl
          obtain ⟨s3, h3, m3, r3, g1, g2⟩ := L_guard #[I.movz 13, I.cmpR 0 13, I.bc Cond.eq (fo - ((compileS nov base d e).size + 2))] 1 0 (fo - ((compileS nov base d e).size + 2)) (by simp) (by simp) (by simp)
            s2 p2 (encode (sem ρ e)) (by rw [o2 0 (by omega)]; exact r1) q2
          have hA := Steps.append h1 p1 (h2.trans h3)
          refine ⟨{ s3 with pc := s3.pc + (compileS nov base d e).size }, hA, ?_, ?_, ?_⟩
          · intro ht
            have hne : encode (sem ρ e) ≠ NICHE := by
              cases hse : sem ρ e with
              | none => simp [ctruth, hse] at ht
              | some z => exact encode_ne_niche z (hse ▸ i1)
            have := g2 hne; simp only []; omega
          · intro hf
            have hn : sem ρ e = none := by simpa [ctruth] using hf
            have := g1 (by rw [hn]; rfl); simp only []; omega
          · intro j hj; show s3.m j = s.m j; rw [m3, m2]; exact m1 j hj
        · have hmb' : mb nov e = false := by simpa using hmb
          simp only [hmb', Bool.false_eq_true, if_false] at hfo ⊢
          obtain ⟨z, hz⟩ := mb_sound nov hnov ρ hρ hvs e hl hmb'
          refine ⟨s1, h1, fun _ => p1, fun hf => by simp [ctruth, hz] at hf, m1⟩
  | and a b iha ihb =>
      intro d fo s hl hv hs hm hfo
      obtain ⟨hla, hlb⟩ := hl
      have hva : a.maxVar ≤ base := by simp only [Cn.maxVar] at hv; omega
      have hvb : b.maxVar ≤ base := by simp only [Cn.maxVar] at hv; omega
      have hsz : (compileC nov base d fo (.and a b)).size
          = (compileC nov base d fo a).size + (compileC nov base d (fo - (compileC nov base d fo a).size) b).size := by
        simp [compileC]
      obtain ⟨sA, hA, tA, fA, mA⟩ := iha d fo s hla hva hs hm (by omega)
      by_cases hta : ctruth ρ a = true
      · have pA := tA hta
        obtain ⟨sB, hB, tB, fB, mB⟩ := ihb d (fo - (compileC nov base d fo a).size) { sA with pc := 0 } hlb hvb rfl
          (by intro k hk; show sA.m k = _; rw [mA k (by omega)]; exact hm k hk) (by omega)
        have hAB := Steps.append hA pA hB
        refine ⟨{ sB with pc := sB.pc + (compileC nov base d fo a).size }, by simpa [compileC] using hAB, ?_, ?_, ?_⟩
        · intro h
          have hb : ctruth ρ b = true := by simpa [ctruth, hta] using h
          have := tB hb; simp only []; omega
        · intro h
          have hb : ctruth ρ b = false := by simpa [ctruth, hta] using h
          have := fB hb; simp only []; omega
        · intro j hj; show sB.m j = s.m j; rw [mB j hj]; show sA.m j = _; exact mA j hj
      · have hta' : ctruth ρ a = false := by simpa using hta
        have pA := fA hta'
        refine ⟨sA, by simpa [compileC] using hA.left (compileC nov base d (fo - (compileC nov base d fo a).size) b), ?_, ?_, mA⟩
        · intro h; simp [ctruth, hta'] at h
        · intro _; exact pA
  | or a b iha ihb =>
      intro d fo s hl hv hs hm hfo
      obtain ⟨hla, hlb⟩ := hl
      have hva : a.maxVar ≤ base := by simp only [Cn.maxVar] at hv; omega
      have hvb : b.maxVar ≤ base := by simp only [Cn.maxVar] at hv; omega
      obtain ⟨la, hla_def⟩ : ∃ la, la = (compileC nov base d 0 a).size + 1 := ⟨_, rfl⟩
      obtain ⟨fb, hfb⟩ : ∃ fb, fb = fo - ((compileC nov base d la a).size + 1) := ⟨_, rfl⟩
      have hdef : compileC nov base d fo (.or a b) =
          (compileC nov base d la a ++ #[I.b ((compileC nov base d fb b).size + 1)]) ++ compileC nov base d fb b := by
        simp only [compileC]; rw [← hla_def, ← hfb]
      have hSA : (compileC nov base d la a).size + 1 = la := by
        have := compileC_size nov base a d la 0
        omega
      rw [hdef] at hfo ⊢
      simp only [Array.size_append, Array.size_singleton] at hfo
      obtain ⟨sA, hA, tA, fA, mA⟩ := iha d la s hla hva hs hm (by omega)
      by_cases hta : ctruth ρ a = true
      · have pA := tA hta
        let s2 : St := step (I.b ((compileC nov base d fb b).size + 1)) { sA with pc := 0 }
        have h2 : Steps (compileC nov base d la a ++ #[I.b ((compileC nov base d fb b).size + 1)]) s
            { s2 with pc := s2.pc + (compileC nov base d la a).size } :=
          Steps.append hA pA (single _ _ rfl)
        have hpc2 : s2.pc = (compileC nov base d fb b).size + 1 := by simp [s2, step]
        refine ⟨{ s2 with pc := s2.pc + (compileC nov base d la a).size }, h2.left _, ?_, ?_, ?_⟩
        · intro _; show s2.pc + (compileC nov base d la a).size = _; simp only [Array.size_append, Array.size_singleton]; omega
        · intro h; simp [ctruth, hta] at h
        · intro j hj; show s2.m j = s.m j; simp [s2, step]; exact mA j hj
      · have hta' : ctruth ρ a = false := by simpa using hta
        have pA := fA hta'
        have h1 : Steps (compileC nov base d la a ++ #[I.b ((compileC nov base d fb b).size + 1)]) s sA := hA.left _
        obtain ⟨sB, hB, tB, fB, mB⟩ := ihb d fb { sA with pc := 0 } hlb hvb rfl
          (by intro k hk; show sA.m k = _; rw [mA k (by omega)]; exact hm k hk) (by omega)
        have hAB := Steps.append h1 (by simp; omega) hB
        refine ⟨{ sB with pc := sB.pc + (compileC nov base d la a ++ #[I.b ((compileC nov base d fb b).size + 1)]).size }, hAB, ?_, ?_, ?_⟩
        · intro h
          have hb : ctruth ρ b = true := by simpa [ctruth, hta'] using h
          have := tB hb; simp only [Array.size_append, Array.size_singleton] at this ⊢; omega
        · intro h
          have hb : ctruth ρ b = false := by simpa [ctruth, hta'] using h
          have := fB hb; simp only [Array.size_append, Array.size_singleton] at this ⊢; omega
        · intro j hj; show sB.m j = s.m j; rw [mB j hj]; show sA.m j = _; exact mA j hj

end SirZAsm

#print axioms SirZAsm.compileS_ok
#print axioms SirZAsm.compileS_ok_real
#print axioms SirZAsm.compileC_ok
