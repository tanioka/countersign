/-
  SIR-Z(SIR_SUBSET.md): SIR が扱う整数の核の、意味の定義と、規則(宣言)と評価器(関数)の一致。
  Mathlib は使わない(`lean SirZ.lean` だけで検査できる)。呼び(`call`)・関数・畳み・リスト・文字列は次の段階。

  読み方:
  * `Ev` は SIR_SUBSET.md §3 の規則をそのまま書いた大きな歩幅の意味(宣言)。
  * `ev` は sign_sir.py の `evaluate` に対応する関数。
  * `ev_iff : ev ρ t = v ↔ Ev ρ t v` が段階 (b)(評価器 = 規則)。
  * 比べが真のときに返す値(`sel`)は、仕様の食い違い(designer_questions 6e P-1)が決まるまで引数にする。
-/

namespace SirZ

/-- 値: `none` は `!_`(unit)。`some z` は整数(値域 `[-M, M]`)。 -/
abbrev V := Option Int

def M : Int := 2 ^ 63 - 1

/-- 域の外の答えは `!_`(strict の観測。SIR_SUBSET.md §1 と P-3) -/
def clamp (z : Int) : V := if -M ≤ z ∧ z ≤ M then some z else none

inductive AOp | add | sub | mul | div | mod
  deriving DecidableEq, Repr
inductive COp | lt | gt | le | ge | eq | ne
  deriving DecidableEq, Repr

/-- 算術の核。`!_` は単位元として消える。割る数が 0 なら `!_`(消えた単位ではなく、答えが域に無い)。 -/
def arithInt : AOp → Int → Int → V
  | .add, a, b => clamp (a + b)
  | .sub, a, b => clamp (a - b)
  | .mul, a, b => clamp (a * b)
  | .div, a, b => if b = 0 then none else clamp (a.tdiv b)
  | .mod, a, b => if b = 0 then none else clamp (a - a.tdiv b * b)

def arith (o : AOp) : V → V → V
  | some a, some b => arithInt o a b
  | some a, none   => some a
  | none,   some b => some b
  | none,   none   => none

def cmpHolds : COp → Int → Int → Bool
  | .lt, a, b => decide (a < b)
  | .gt, a, b => decide (a > b)
  | .le, a, b => decide (a ≤ b)
  | .ge, a, b => decide (a ≥ b)
  | .eq, a, b => decide (a = b)
  | .ne, a, b => decide (a ≠ b)

/-- 項。`rowD v rest`: 既定の行(条件なし)。`rowC c v rest`: 条件 `c`・値 `v`・残りの行 `rest`。 -/
inductive T
  | int (n : Int)
  | void
  | var (i : Nat)
  | op (o : AOp) (a b : T)
  | neg (a : T)
  | abs (a : T)
  | cmp (o : COp) (a b : T)
  | chain3 (o₁ o₂ : COp) (a b c : T)
  | and (a b : T)
  | or (a b : T)
  | rowD (v rest : T)
  | rowC (c v rest : T)

abbrev Env := Nat → V

/-- 比べが真のとき返す値の選び方(`sel o a b`)。実装(V6)は `fun _ a _ => a`、
    仕様の comparison.md §2.1 は「左が 0 か 1 なら右」(P-1)。 -/
abbrev Sel := COp → Int → Int → Int

def selLeft : Sel := fun _ a _ => a
def selSpec : Sel := fun o a b =>
  if (o = .eq ∨ o = .ne) then a else if a = 0 ∨ a = 1 then b else a

/-! ## 評価器 `ev`(sign_sir.py の `evaluate`) -/

def ev (sel : Sel) (ρ : Env) : T → V
  | .int n => clamp n
  | .void => none
  | .var i => ρ i
  | .op o a b => arith o (ev sel ρ a) (ev sel ρ b)
  | .neg a => (ev sel ρ a).bind fun z => clamp (-z)
  | .abs a => (ev sel ρ a).bind fun z => clamp z.natAbs
  | .cmp o a b =>
      match ev sel ρ a, ev sel ρ b with
      | some x, some y => if cmpHolds o x y then some (sel o x y) else none
      | _, _ => none
  | .chain3 o₁ o₂ a b c =>
      match ev sel ρ a with
      | none => none
      | some x =>
        match ev sel ρ b with
        | none => none
        | some y =>
          if cmpHolds o₁ x y then
            match ev sel ρ c with
            | none => none
            | some z => if cmpHolds o₂ y z then some y else none
          else none
  | .and a b => match ev sel ρ a with | none => none | some _ => ev sel ρ b
  | .or a b => match ev sel ρ a with | none => ev sel ρ b | some x => some x
  | .rowD v rest =>
      match ev sel ρ v with
      | some r => some r
      | none => ev sel ρ rest
  | .rowC c v rest =>
      match ev sel ρ c with
      | none => ev sel ρ rest
      | some _ =>
        match ev sel ρ v with
        | some r => some r
        | none => ev sel ρ rest

/-! ## 規則(SIR_SUBSET.md §3) -/

inductive Ev (sel : Sel) (ρ : Env) : T → V → Prop
  | int (n : Int) : Ev sel ρ (.int n) (clamp n)
  | void : Ev sel ρ .void none
  | var (i : Nat) : Ev sel ρ (.var i) (ρ i)
  | op {o a b va vb} : Ev sel ρ a va → Ev sel ρ b vb → Ev sel ρ (.op o a b) (arith o va vb)
  | negN {a} : Ev sel ρ a none → Ev sel ρ (.neg a) none
  | negV {a z} : Ev sel ρ a (some z) → Ev sel ρ (.neg a) (clamp (-z))
  | absN {a} : Ev sel ρ a none → Ev sel ρ (.abs a) none
  | absV {a z} : Ev sel ρ a (some z) → Ev sel ρ (.abs a) (clamp z.natAbs)
  | cmpVoidL {o a b vb} : Ev sel ρ a none → Ev sel ρ b vb → Ev sel ρ (.cmp o a b) none
  | cmpVoidR {o a b x} : Ev sel ρ a (some x) → Ev sel ρ b none → Ev sel ρ (.cmp o a b) none
  | cmpTrue {o a b x y} : Ev sel ρ a (some x) → Ev sel ρ b (some y) → cmpHolds o x y = true →
      Ev sel ρ (.cmp o a b) (some (sel o x y))
  | cmpFalse {o a b x y} : Ev sel ρ a (some x) → Ev sel ρ b (some y) → cmpHolds o x y = false →
      Ev sel ρ (.cmp o a b) none
  -- 連鎖: 左から評価し、`!_`(偽も含む)になったら右は評価しない(comparison.md §4.1)
  | chainA {o₁ o₂ a b c} : Ev sel ρ a none → Ev sel ρ (.chain3 o₁ o₂ a b c) none
  | chainB {o₁ o₂ a b c x} : Ev sel ρ a (some x) → Ev sel ρ b none → Ev sel ρ (.chain3 o₁ o₂ a b c) none
  | chainF1 {o₁ o₂ a b c x y} : Ev sel ρ a (some x) → Ev sel ρ b (some y) → cmpHolds o₁ x y = false →
      Ev sel ρ (.chain3 o₁ o₂ a b c) none
  | chainC {o₁ o₂ a b c x y} : Ev sel ρ a (some x) → Ev sel ρ b (some y) → cmpHolds o₁ x y = true →
      Ev sel ρ c none → Ev sel ρ (.chain3 o₁ o₂ a b c) none
  | chainF2 {o₁ o₂ a b c x y z} : Ev sel ρ a (some x) → Ev sel ρ b (some y) → cmpHolds o₁ x y = true →
      Ev sel ρ c (some z) → cmpHolds o₂ y z = false → Ev sel ρ (.chain3 o₁ o₂ a b c) none
  | chainT {o₁ o₂ a b c x y z} : Ev sel ρ a (some x) → Ev sel ρ b (some y) → cmpHolds o₁ x y = true →
      Ev sel ρ c (some z) → cmpHolds o₂ y z = true → Ev sel ρ (.chain3 o₁ o₂ a b c) (some y)
  | andN {a b} : Ev sel ρ a none → Ev sel ρ (.and a b) none
  | andV {a b x v} : Ev sel ρ a (some x) → Ev sel ρ b v → Ev sel ρ (.and a b) v
  | orV {a b x} : Ev sel ρ a (some x) → Ev sel ρ (.or a b) (some x)
  | orN {a b v} : Ev sel ρ a none → Ev sel ρ b v → Ev sel ρ (.or a b) v
  -- 行: 条件が通り、値が `!_` でなければその値。値が `!_` なら次の行へ落ちる(V10)。
  -- 条件が既定(`none`)か、`!_` でない値を持てば「通る」。通らなければ次の行へ。
  | rowDefHit {v rest r} : Ev sel ρ v (some r) → Ev sel ρ (.rowD v rest) (some r)
  | rowDefFall {v rest w} : Ev sel ρ v none → Ev sel ρ rest w → Ev sel ρ (.rowD v rest) w
  | rowHit {c v rest x r} : Ev sel ρ c (some x) → Ev sel ρ v (some r) → Ev sel ρ (.rowC c v rest) (some r)
  | rowFall {c v rest x w} : Ev sel ρ c (some x) → Ev sel ρ v none → Ev sel ρ rest w →
      Ev sel ρ (.rowC c v rest) w
  | rowSkip {c v rest w} : Ev sel ρ c none → Ev sel ρ rest w → Ev sel ρ (.rowC c v rest) w



/-! ## 評価器は規則を満たす(健全) -/

theorem ev_Ev (sel : Sel) (ρ : Env) : ∀ t : T, Ev sel ρ t (ev sel ρ t) := by
  intro t
  induction t with
  | int n => exact Ev.int n
  | void => exact Ev.void
  | var i => exact Ev.var i
  | op o a b iha ihb => exact Ev.op iha ihb
  | neg a iha =>
    simp only [ev]
    cases h : ev sel ρ a with
    | none => rw [h] at iha; exact Ev.negN iha
    | some z => rw [h] at iha; exact Ev.negV iha
  | abs a iha =>
    simp only [ev]
    cases h : ev sel ρ a with
    | none => rw [h] at iha; exact Ev.absN iha
    | some z => rw [h] at iha; exact Ev.absV iha
  | cmp o a b iha ihb =>
    simp only [ev]
    cases ha : ev sel ρ a with
    | none => rw [ha] at iha; cases hb : ev sel ρ b <;> rw [hb] at ihb <;> exact Ev.cmpVoidL iha ihb
    | some x =>
      rw [ha] at iha
      cases hb : ev sel ρ b with
      | none => rw [hb] at ihb; exact Ev.cmpVoidR iha ihb
      | some y =>
        rw [hb] at ihb
        by_cases hc : cmpHolds o x y = true
        · simp only [hc, ite_true]; exact Ev.cmpTrue iha ihb hc
        · have hc' : cmpHolds o x y = false := by simpa using hc
          simp only [hc', Bool.false_eq_true, ite_false]; exact Ev.cmpFalse iha ihb hc'
  | chain3 o₁ o₂ a b c iha ihb ihc =>
    simp only [ev]
    cases ha : ev sel ρ a with
    | none => rw [ha] at iha; exact Ev.chainA iha
    | some x =>
      rw [ha] at iha
      cases hb : ev sel ρ b with
      | none => rw [hb] at ihb; exact Ev.chainB iha ihb
      | some y =>
        rw [hb] at ihb
        by_cases h1 : cmpHolds o₁ x y = true
        · simp only [h1, ite_true]
          cases hc : ev sel ρ c with
          | none => rw [hc] at ihc; exact Ev.chainC iha ihb h1 ihc
          | some z =>
            rw [hc] at ihc
            by_cases h2 : cmpHolds o₂ y z = true
            · simp only [h2, ite_true]; exact Ev.chainT iha ihb h1 ihc h2
            · have h2' : cmpHolds o₂ y z = false := by simpa using h2
              simp only [h2', Bool.false_eq_true, ite_false]; exact Ev.chainF2 iha ihb h1 ihc h2'
        · have h1' : cmpHolds o₁ x y = false := by simpa using h1
          simp only [h1', Bool.false_eq_true, ite_false]; exact Ev.chainF1 iha ihb h1'
  | and a b iha ihb =>
    simp only [ev]
    cases ha : ev sel ρ a with
    | none => rw [ha] at iha; exact Ev.andN iha
    | some x => rw [ha] at iha; exact Ev.andV iha ihb
  | or a b iha ihb =>
    simp only [ev]
    cases ha : ev sel ρ a with
    | none => rw [ha] at iha; exact Ev.orN iha ihb
    | some x => rw [ha] at iha; exact Ev.orV iha
  | rowD v rest ihv ihr =>
    simp only [ev]
    cases hv : ev sel ρ v with
    | none => rw [hv] at ihv; exact Ev.rowDefFall ihv ihr
    | some r => rw [hv] at ihv; exact Ev.rowDefHit ihv
  | rowC c v rest ihc ihv ihr =>
    simp only [ev]
    cases hc : ev sel ρ c with
    | none => rw [hc] at ihc; exact Ev.rowSkip ihc ihr
    | some x =>
      rw [hc] at ihc
      cases hv : ev sel ρ v with
      | none => rw [hv] at ihv; exact Ev.rowFall ihc ihv ihr
      | some r => rw [hv] at ihv; exact Ev.rowHit ihc ihv

/-! ## 規則を満たす値は評価器の値(完全・一意) -/

theorem Ev_ev (sel : Sel) (ρ : Env) {t : T} {v : V} (h : Ev sel ρ t v) : ev sel ρ t = v := by
  induction h with
  | int n => rfl
  | void => rfl
  | var i => rfl
  | op _ _ iha ihb => simp [ev, iha, ihb]
  | negN _ ih => simp [ev, ih]
  | negV _ ih => simp [ev, ih]
  | absN _ ih => simp [ev, ih]
  | absV _ ih => simp [ev, ih]
  | cmpVoidL _ _ iha ihb => simp [ev, iha, ihb]
  | cmpVoidR _ _ iha ihb => simp [ev, iha, ihb]
  | cmpTrue _ _ hc iha ihb => simp [ev, iha, ihb, hc]
  | cmpFalse _ _ hc iha ihb => simp [ev, iha, ihb, hc]
  | chainA _ ih => simp [ev, ih]
  | chainB _ _ iha ihb => simp [ev, iha, ihb]
  | chainF1 _ _ h1 iha ihb => simp [ev, iha, ihb, h1]
  | chainC _ _ h1 _ iha ihb ihc => simp [ev, iha, ihb, h1, ihc]
  | chainF2 _ _ h1 _ h2 iha ihb ihc => simp [ev, iha, ihb, h1, ihc, h2]
  | chainT _ _ h1 _ h2 iha ihb ihc => simp [ev, iha, ihb, h1, ihc, h2]
  | andN _ ih => simp [ev, ih]
  | andV _ _ iha ihb => simp [ev, iha, ihb]
  | orV _ ih => simp [ev, ih]
  | orN _ _ iha ihb => simp [ev, iha, ihb]
  | rowDefHit _ ih => simp [ev, ih]
  | rowDefFall _ _ ihv ihr => simp [ev, ihv, ihr]
  | rowHit _ _ ihc ihv => simp [ev, ihc, ihv]
  | rowFall _ _ _ ihc ihv ihr => simp [ev, ihc, ihv, ihr]
  | rowSkip _ _ ihc ihr => simp [ev, ihc, ihr]

/-- 段階 (b): 評価器 = 規則 -/
theorem ev_iff (sel : Sel) (ρ : Env) (t : T) (v : V) : ev sel ρ t = v ↔ Ev sel ρ t v :=
  ⟨fun h => h ▸ ev_Ev sel ρ t, Ev_ev sel ρ⟩

/-- 規則は決定的 -/
theorem Ev_det (sel : Sel) (ρ : Env) {t : T} {v w : V} (h : Ev sel ρ t v) (h' : Ev sel ρ t w) : v = w :=
  (Ev_ev sel ρ h).symm.trans (Ev_ev sel ρ h')

/-! ## 性質 -/

/-- V10: 行は `(c & v) | 次の行` と同じ(値が `!_` なら次の行へ落ちる) -/
theorem row_eq_or_and (sel : Sel) (ρ : Env) (c v rest : T) :
    ev sel ρ (.rowC c v rest) = ev sel ρ (.or (.and c v) rest) := by
  simp only [ev]
  cases hc : ev sel ρ c <;> cases hv : ev sel ρ v <;> simp

theorem rowD_eq_or (sel : Sel) (ρ : Env) (v rest : T) :
    ev sel ρ (.rowD v rest) = ev sel ρ (.or v rest) := by
  simp only [ev]
  cases hv : ev sel ρ v <;> simp

/-- `!_` は算術の単位元(両側。unit.md・operator_table.md の爆発律) -/
theorem arith_void_left (o : AOp) (x : V) : arith o none x = x := by cases x <;> rfl
theorem arith_void_right (o : AOp) (x : V) : arith o x none = x := by cases x <;> rfl

/-- 値は常に域の中(または `!_`) -/
theorem clamp_range {z w : Int} (h : clamp z = some w) : -M ≤ w ∧ w ≤ M := by
  unfold clamp at h
  split at h
  · cases h; assumption
  · cases h

/-- 加減乗の答えが域の外になるとき、残る値は無く `!_`(溢れは `!_` に収束。P-3 の strict の読み) -/
theorem arith_add_overflow (a b : Int) (h : ¬(-M ≤ a + b ∧ a + b ≤ M)) :
    arith .add (some a) (some b) = none := by
  simp [arith, arithInt, clamp, h]

/-- 0 で割れば `!_`(`/`・`%`) -/
theorem arith_div_zero (a : Int) : arith .div (some a) (some 0) = none := by simp [arith, arithInt]
theorem arith_mod_zero (a : Int) : arith .mod (some a) (some 0) = none := by simp [arith, arithInt]

/-- 連鎖(範囲)は、最初の項が `!_` なら残りを評価せず `!_`。右の項の評価結果に依らない -/
theorem chain3_short (sel : Sel) (ρ : Env) (o₁ o₂ : COp) (a b c b' c' : T)
    (h : ev sel ρ a = none) :
    ev sel ρ (.chain3 o₁ o₂ a b c) = ev sel ρ (.chain3 o₁ o₂ a b' c') := by
  simp [ev, h]

end SirZ

#print axioms SirZ.ev_iff
#print axioms SirZ.row_eq_or_and
