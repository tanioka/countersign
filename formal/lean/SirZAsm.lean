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

inductive Cond | ne | eq | vs
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

structure St where
  r : Nat → W
  m : Nat → W                          -- フレームの枠(x29 からの位置 k)
  z : Bool
  v : Bool
  pc : Nat

def St.set (s : St) (d : Nat) (x : W) : St := { s with r := fun i => if i = d then x else s.r i }

def Cond.holds (c : Cond) (s : St) : Bool :=
  match c with
  | .ne => !s.z
  | .eq => s.z
  | .vs => s.v

/-- 即値(simp が具体的な 64 ビットの値を展開しないよう、別の名前にしておく) -/
@[irreducible] def immW (n : Nat) : W := BitVec.ofNat 64 n

theorem immW_zero : immW 0 = (0 : W) := by unfold immW; rfl

/-- 比べの V 旗。分岐が見るのは Z だけなので、simp が具体的な値で展開しないよう、別の名前にしておく -/
@[irreducible] def cmpV (a b : W) : Bool := a.ssubOverflow b

/-- 減算の旗(cmp・subs): Z は差が 0、V は符号つきの溢れ -/
def St.flagsSub (s : St) (a b : W) : St := { s with z := decide (a = b), v := cmpV a b }

def step (i : I) (s : St) : St :=
  let s' := { s with pc := s.pc + 1 }
  match i with
  | .movz d => s'.set d NICHE
  | .mov d a => s'.set d (s.r a)
  | .cmpR a b => s'.flagsSub (s.r a) (s.r b)
  | .cmpI a n => s'.flagsSub (s.r a) (immW n)
  | .cmpAsr a b sh => s'.flagsSub (s.r a) ((s.r b).sshiftRight sh)
  | .adds d a b => { (s'.set d (s.r a + s.r b)) with z := decide (s.r a + s.r b = 0), v := (s.r a).saddOverflow (s.r b) }
  | .subs d a b => { (s'.set d (s.r a - s.r b)) with z := decide (s.r a - s.r b = 0), v := (s.r a).ssubOverflow (s.r b) }
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

/-- 燃料つきの実行。`pc` が終わりに着いたら止まる -/
def run (p : Array I) : Nat → St → St
  | 0, s => s
  | n + 1, s => if h : s.pc < p.size then run p n (step p[s.pc] s) else s

def init (x y : W) : St := { r := fun i => if i = 9 then x else if i = 10 then y else 0, m := fun _ => 0, z := false, v := false, pc := 0 }

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

inductive E
  | lit (n : Int)
  | var (k : Nat)
  | op (o : AOp) (l r : E)

/-- 意味(`!_` を含む)。変数の値は環境 `ρ` -/
def sem (ρ : Nat → Option Int) : E → Option Int
  | .lit n => clamp n
  | .var k => ρ k
  | .op o l r => arith o (sem ρ l) (sem ρ r)

def E.lits : E → Prop
  | .lit n => -M ≤ n ∧ n ≤ M
  | .var _ => True
  | .op _ l r => l.lits ∧ r.lits

def E.maxVar : E → Nat
  | .lit _ => 0
  | .var k => k + 1
  | .op _ l r => max l.maxVar r.maxVar

/-- `sign_asm.py` の骨組み: 左を作って枠へ、右を作って `x10`、左を `x9` に戻し、`bin_tail` の列。
    `base + d` 番目の枠が深さ `d` の途中の値。 -/
def compile (base : Nat) : Nat → E → Array I
  | _, .lit n => #[I.movi 0 n]
  | _, .var k => #[I.ldr 0 k]
  | d, .op o l r =>
      compile base d l ++ #[I.str 0 (base + d)] ++ compile base (d + 1) r
        ++ #[I.mov 10 0, I.ldr 9 (base + d)] ++ tpl o

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

/-- 段階 (c)(式の木): `compile` の命令列は、環境が枠に入っていれば、`x0` に式の値の表し方を置いて終わりまで走り、
    変数の枠と、より浅い途中の枠を変えない。 -/
theorem compile_ok (ρ : Nat → Option Int) (hρ : ∀ k, InR (ρ k)) (base : Nat) :
    ∀ (e : E) (d : Nat) (s : St), e.lits → e.maxVar ≤ base → s.pc = 0 →
      (∀ k < base, s.m k = encode (ρ k)) →
      ∃ s', Steps (compile base d e) s s' ∧ s'.pc = (compile base d e).size ∧
        s'.r 0 = encode (sem ρ e) ∧ (∀ j < base + d, s'.m j = s.m j) ∧ InR (sem ρ e) := by
  intro e
  induction e with
  | lit n =>
      intro d s hl _ hs _
      have hl' : -M ≤ n ∧ n ≤ M := hl
      refine ⟨step (I.movi 0 n) s, single _ s hs, ?_, ?_, ?_, InR_clamp n⟩
      · simp [step, St.set, hs, compile]
      · have hc : clamp n = some n := by simp [clamp, hl']
        simp [step, St.set, sem, hc, encode]
      · intro j _; simp [step, St.set]
  | var k =>
      intro d s _ hv hs hm
      refine ⟨step (I.ldr 0 k) s, single _ s hs, ?_, ?_, ?_, hρ k⟩
      · simp [step, St.set, hs, compile]
      · simp [step, St.set, sem, hm k (by simp [E.maxVar] at hv; omega)]
      · intro j _; simp [step, St.set]
  | op o l r ihl ihr =>
      intro d s hl hv hs hm
      obtain ⟨hll, hlr⟩ := hl
      have hv1 : l.maxVar ≤ base := by simp only [E.maxVar] at hv; omega
      have hv2 : r.maxVar ≤ base := by simp only [E.maxVar] at hv; omega
      obtain ⟨s1, h1, p1, r1, m1, i1⟩ := ihl d s hll hv1 hs hm
      let s2 : St := step (I.str 0 (base + d)) { s1 with pc := 0 }
      have h2 : Steps (compile base d l ++ #[I.str 0 (base + d)]) s
          { s2 with pc := (compile base d l ++ #[I.str 0 (base + d)]).size } :=
        Steps.append' h1 p1 (single _ _ rfl) (by simp [s2, step])
      let t2 : St := { s2 with pc := (compile base d l ++ #[I.str 0 (base + d)]).size }
      have t2m : ∀ j, t2.m j = if j = base + d then s1.r 0 else s1.m j := by
        intro j; simp [t2, s2, step]
      obtain ⟨s3, h3, p3, r3, m3, i3⟩ := ihr (d + 1) { t2 with pc := 0 } hlr hv2 rfl (by
        intro k hk
        have : k ≠ base + d := by omega
        show t2.m k = _
        rw [t2m, if_neg this, m1 k (by omega)]; exact hm k hk)
      have h23 := Steps.append' h2 (by simp [t2]) h3 p3
      let t3 : St := { s3 with pc := (compile base d l ++ #[I.str 0 (base + d)] ++ compile base (d + 1) r).size }
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
      have hT := tpl_ok o s5 rfl (s5.r 9) (s5.r 10) rfl rfl
      have h9' : s5.r 9 = encode (sem ρ l) := hm9
      have h10' : s5.r 10 = encode (sem ρ r) := hm10
      have h5 : Steps (tpl o) s5 (run (tpl o) 30 s5) := run_steps _ _ _
      have hmm : (run (tpl o) 30 s5).m = s5.m := Steps.m_eq (tpl_nostr o) h5
      refine ⟨{ run (tpl o) 30 s5 with pc := (compile base d (.op o l r)).size }, ?_, rfl, ?_, ?_, InR_arith o _ _ hl_in hr_in⟩
      · have := Steps.append' h234 (by simp [s4, step, St.set]) h5 hT.2
        simpa [compile, Array.append_assoc] using this
      · simp only []
        rw [hT.1, h9', h10', decode_encode _ hl_in, decode_encode _ hr_in]; rfl
      · intro j hj
        simp only []
        rw [hmm]
        have a1 : s3.m j = t2.m j := m3 j (by omega)
        simp only [s5, s4, u, step, St.set, t3, a1, t2m]
        have : j ≠ base + d := by omega
        rw [if_neg this]; exact m1 j (by omega)

end SirZAsm

#print axioms SirZAsm.compile_ok
