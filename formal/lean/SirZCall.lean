/-
  SIR-Z + 呼び(SIR_SUBSET.md §3 の `f(e,…)`)。SirZ.lean の続き(段階 (b) の関数・再帰・部分適用)。
  Mathlib なし。`lean SirZCall.lean` だけで検査できる。

  * `Res` は評価の結果: 値 `v`・部分適用 `pf`・実引数の並び `args`(呼びの内部)・`unsup`(SIR-Z の外。Python の `Unsup`)・`fuel`(燃料切れ)。
  * `ev fs sel n ρ t`: 深さ `n` の燃料つき評価器(sign_sir.py の `evaluate`)。
  * `Ev fs ρ t r`: 成功する結果(`v`・`pf`・`args`)だけの規則(大きな歩幅の意味)。
  * `ev_sound`: 評価器が `unsup`・`fuel` 以外を返せば、規則がそれを導く。
  * `Ev_complete`: 規則が導く結果は、十分な燃料で評価器が返す。
  * `Ev_det`: 規則は決定的。
  部分的な正しさ(止まる場合の正しさ)であって、止まることは言わない。
-/

namespace SirZC

abbrev V := Option Int
def M : Int := 2 ^ 63 - 1
def clamp (z : Int) : V := if -M ≤ z ∧ z ≤ M then some z else none

inductive AOp | add | sub | mul | div | mod
  deriving DecidableEq, Repr
inductive COp | lt | gt | le | ge | eq | ne
  deriving DecidableEq, Repr

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

/-- 項。実引数の並びは `anil`・`acons` の鎖(入れ子の帰納型を避けて、`induction` が使えるようにする)。 -/
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
  | anil
  | acons (a rest : T)
  | call (f : Nat) (as : T)

inductive Res
  | v (x : V)
  | pf
  | args (l : List V)
  | unsup
  | fuel
  deriving DecidableEq, Repr

abbrev Env := Nat → V
abbrev Sel := COp → Int → Int → Int
/-- 関数表: 名前 ↦ (口の数, 本体)。本体の `var i` は i 番目の口。 -/
abbrev Fs := Nat → Option (Nat × T)

def selLeft : Sel := fun _ a _ => a

/-- 演算の項に置く: 部分適用は `!_` と同じ(`one`)。並び・unsup・fuel はそのまま伝わる。 -/
def bnd (r : Res) (k : V → Res) : Res :=
  match r with
  | .v x => k x
  | .pf => k none
  | .fuel => .fuel
  | _ => .unsup

def dePF : Res → Res
  | .pf => .v none
  | r => r

/-- 結果の組み合わせ(評価器の部品。単調性の証明のために切り出す) -/
def andR (A : Res) (B : Unit → Res) : Res :=
  match A with
  | .v none => .v none
  | .v (some _) => B ()
  | .fuel => .fuel
  | _ => .unsup

def orR (A : Res) (B : Unit → Res) : Res :=
  match A with
  | .v (some x) => .v (some x)
  | .v none => B ()
  | .fuel => .fuel
  | _ => .unsup

def rowR (A : Res) (Rest : Unit → Res) : Res :=
  match A with
  | .v (some r) => .v (some r)
  | .v none => Rest ()
  | .pf => Rest ()
  | .fuel => .fuel
  | _ => .unsup

def consR (A : Res) (R : Unit → Res) : Res :=
  match A with
  | .v x =>
    match R () with
    | .args l => .args (x :: l)
    | .fuel => .fuel
    | _ => .unsup
  | .fuel => .fuel
  | _ => .unsup

def callR (fs : Fs) (f : Nat) (A : Res) (run : List V → T → Res) : Res :=
  match A with
  | .args l =>
    match fs f with
    | none => .unsup
    | some (k, body) =>
      if l.length ≠ k then .unsup
      else if l.any Option.isNone then .pf
      else dePF (run l body)
  | .fuel => .fuel
  | _ => .unsup

def ev (fs : Fs) (sel : Sel) : Nat → Env → T → Res
  | 0, _, _ => .fuel
  | n + 1, ρ, t =>
    match t with
    | .int k => .v (clamp k)
    | .void => .v none
    | .var i => .v (ρ i)
    | .op o a b => bnd (ev fs sel n ρ a) fun x => bnd (ev fs sel n ρ b) fun y => .v (arith o x y)
    | .neg a => bnd (ev fs sel n ρ a) fun x => .v (x.bind fun z => clamp (-z))
    | .abs a => bnd (ev fs sel n ρ a) fun x => .v (x.bind fun z => clamp z.natAbs)
    | .cmp o a b =>
        bnd (ev fs sel n ρ a) fun x => bnd (ev fs sel n ρ b) fun y =>
          match x, y with
          | some x', some y' => if cmpHolds o x' y' then .v (some (sel o x' y')) else .v none
          | _, _ => .v none
    | .chain3 o₁ o₂ a b c =>
        bnd (ev fs sel n ρ a) fun x =>
          match x with
          | none => .v none
          | some x' =>
            bnd (ev fs sel n ρ b) fun y =>
              match y with
              | none => .v none
              | some y' =>
                if cmpHolds o₁ x' y' then
                  bnd (ev fs sel n ρ c) fun z =>
                    match z with
                    | none => .v none
                    | some z' => if cmpHolds o₂ y' z' then .v (some y') else .v none
                else .v none
    | .and a b => andR (ev fs sel n ρ a) fun _ => ev fs sel n ρ b
    | .or a b => orR (ev fs sel n ρ a) fun _ => ev fs sel n ρ b
    | .rowD v rest => rowR (ev fs sel n ρ v) fun _ => ev fs sel n ρ rest
    | .rowC c v rest =>
        bnd (ev fs sel n ρ c) fun x =>
          match x with
          | none => ev fs sel n ρ rest
          | some _ => rowR (ev fs sel n ρ v) fun _ => ev fs sel n ρ rest
    | .anil => .args []
    | .acons a r => consR (ev fs sel n ρ a) fun _ => ev fs sel n ρ r
    | .call f as => callR fs f (ev fs sel n ρ as) fun l body => ev fs sel n (fun i => l.getD i none) body

/-- 規則側の「演算の項」: 値はそのまま、部分適用は `!_`、並びは項にならない -/
def co : Res → Option V
  | .v x => some x
  | .pf => some none
  | _ => none

inductive Ev (fs : Fs) (sel : Sel) : Env → T → Res → Prop
  | int {ρ} (k : Int) : Ev fs sel ρ (.int k) (.v (clamp k))
  | void {ρ} : Ev fs sel ρ .void (.v none)
  | var {ρ} (i : Nat) : Ev fs sel ρ (.var i) (.v (ρ i))
  | op {ρ o a b ra rb x y} : Ev fs sel ρ a ra → co ra = some x → Ev fs sel ρ b rb → co rb = some y →
      Ev fs sel ρ (.op o a b) (.v (arith o x y))
  | neg {ρ a ra x} : Ev fs sel ρ a ra → co ra = some x →
      Ev fs sel ρ (.neg a) (.v (x.bind fun z => clamp (-z)))
  | abs {ρ a ra x} : Ev fs sel ρ a ra → co ra = some x →
      Ev fs sel ρ (.abs a) (.v (x.bind fun z => clamp z.natAbs))
  | cmpV {ρ o a b ra rb x y} : Ev fs sel ρ a ra → co ra = some x → Ev fs sel ρ b rb → co rb = some y →
      Ev fs sel ρ (.cmp o a b)
        (match x, y with
          | some x', some y' => if cmpHolds o x' y' then .v (some (sel o x' y')) else .v none
          | _, _ => .v none)
  | chainA {ρ o₁ o₂ a b c ra} : Ev fs sel ρ a ra → co ra = some none → Ev fs sel ρ (.chain3 o₁ o₂ a b c) (.v none)
  | chainB {ρ o₁ o₂ a b c ra rb x} : Ev fs sel ρ a ra → co ra = some (some x) →
      Ev fs sel ρ b rb → co rb = some none → Ev fs sel ρ (.chain3 o₁ o₂ a b c) (.v none)
  | chainC {ρ o₁ o₂ a b c ra rb x y} : Ev fs sel ρ a ra → co ra = some (some x) →
      Ev fs sel ρ b rb → co rb = some (some y) → cmpHolds o₁ x y = false →
      Ev fs sel ρ (.chain3 o₁ o₂ a b c) (.v none)
  | chainD {ρ o₁ o₂ a b c ra rb rc x y z} : Ev fs sel ρ a ra → co ra = some (some x) →
      Ev fs sel ρ b rb → co rb = some (some y) → cmpHolds o₁ x y = true →
      Ev fs sel ρ c rc → co rc = some z →
      Ev fs sel ρ (.chain3 o₁ o₂ a b c)
        (match z with
          | none => .v none
          | some z' => if cmpHolds o₂ y z' then .v (some y) else .v none)
  | andN {ρ a b} : Ev fs sel ρ a (.v none) → Ev fs sel ρ (.and a b) (.v none)
  | andV {ρ a b x r} : Ev fs sel ρ a (.v (some x)) → Ev fs sel ρ b r → Ev fs sel ρ (.and a b) r
  | orV {ρ a b x} : Ev fs sel ρ a (.v (some x)) → Ev fs sel ρ (.or a b) (.v (some x))
  | orN {ρ a b r} : Ev fs sel ρ a (.v none) → Ev fs sel ρ b r → Ev fs sel ρ (.or a b) r
  | rowDHit {ρ v rest r} : Ev fs sel ρ v (.v (some r)) → Ev fs sel ρ (.rowD v rest) (.v (some r))
  | rowDFallV {ρ v rest r} : Ev fs sel ρ v (.v none) → Ev fs sel ρ rest r → Ev fs sel ρ (.rowD v rest) r
  | rowDFallP {ρ v rest r} : Ev fs sel ρ v .pf → Ev fs sel ρ rest r → Ev fs sel ρ (.rowD v rest) r
  | rowCSkip {ρ c v rest rc r} : Ev fs sel ρ c rc → co rc = some none → Ev fs sel ρ rest r →
      Ev fs sel ρ (.rowC c v rest) r
  | rowCHit {ρ c v rest rc x r} : Ev fs sel ρ c rc → co rc = some (some x) →
      Ev fs sel ρ v (.v (some r)) → Ev fs sel ρ (.rowC c v rest) (.v (some r))
  | rowCFallV {ρ c v rest rc x r} : Ev fs sel ρ c rc → co rc = some (some x) →
      Ev fs sel ρ v (.v none) → Ev fs sel ρ rest r → Ev fs sel ρ (.rowC c v rest) r
  | rowCFallP {ρ c v rest rc x r} : Ev fs sel ρ c rc → co rc = some (some x) →
      Ev fs sel ρ v .pf → Ev fs sel ρ rest r → Ev fs sel ρ (.rowC c v rest) r
  | anil {ρ} : Ev fs sel ρ .anil (.args [])
  | acons {ρ a r x l} : Ev fs sel ρ a (.v x) → Ev fs sel ρ r (.args l) → Ev fs sel ρ (.acons a r) (.args (x :: l))
  | callPF {ρ f as l k body} : Ev fs sel ρ as (.args l) → fs f = some (k, body) → l.length = k →
      l.any Option.isNone = true → Ev fs sel ρ (.call f as) .pf
  | callRun {ρ f as l k body rb} : Ev fs sel ρ as (.args l) → fs f = some (k, body) → l.length = k →
      l.any Option.isNone = false → Ev fs sel (fun i => l.getD i none) body rb →
      Ev fs sel ρ (.call f as) (dePF rb)

/-! ## 補題 -/

theorem co_ok {r : Res} {x : V} (h : co r = some x) : r ≠ .unsup ∧ r ≠ .fuel := by
  cases r <;> simp [co] at h ⊢

theorem bnd_inv {r : Res} {k : V → Res} {s : Res} (h : bnd r k = s) (hu : s ≠ .unsup) (hf : s ≠ .fuel) :
    ∃ x, co r = some x ∧ k x = s := by
  cases r with
  | v x => exact ⟨x, rfl, h⟩
  | pf => exact ⟨none, rfl, h⟩
  | args l => simp [bnd] at h; exact absurd h.symm hu
  | unsup => simp [bnd] at h; exact absurd h.symm hu
  | fuel => simp [bnd] at h; exact absurd h.symm hf

/-! ## 評価器は規則を満たす(健全) -/

theorem ev_sound (fs : Fs) (sel : Sel) : ∀ (n : Nat) (ρ : Env) (t : T) (r : Res),
    ev fs sel n ρ t = r → r ≠ .unsup → r ≠ .fuel → Ev fs sel ρ t r := by
  intro n
  induction n with
  | zero => intro ρ t r h _ hf; simp [ev] at h; exact absurd h.symm hf
  | succ n ih =>
    intro ρ t r h hu hf
    have IH : ∀ ρ' t' ra, ev fs sel n ρ' t' = ra → ra ≠ .unsup → ra ≠ .fuel → Ev fs sel ρ' t' ra := ih
    cases t with
    | int k => simp only [ev, andR, orR, rowR, consR, callR] at h; subst h; exact Ev.int k
    | void => simp only [ev, andR, orR, rowR, consR, callR] at h; subst h; exact Ev.void
    | var i => simp only [ev, andR, orR, rowR, consR, callR] at h; subst h; exact Ev.var i
    | op o a b =>
      simp only [ev, andR, orR, rowR, consR, callR] at h
      obtain ⟨x, hx, h1⟩ := bnd_inv h hu hf
      obtain ⟨y, hy, h2⟩ := bnd_inv h1 hu hf
      subst h2
      exact Ev.op (IH _ _ _ rfl (co_ok hx).1 (co_ok hx).2) hx (IH _ _ _ rfl (co_ok hy).1 (co_ok hy).2) hy
    | neg a =>
      simp only [ev, andR, orR, rowR, consR, callR] at h
      obtain ⟨x, hx, h1⟩ := bnd_inv h hu hf
      subst h1
      exact Ev.neg (IH _ _ _ rfl (co_ok hx).1 (co_ok hx).2) hx
    | abs a =>
      simp only [ev, andR, orR, rowR, consR, callR] at h
      obtain ⟨x, hx, h1⟩ := bnd_inv h hu hf
      subst h1
      exact Ev.abs (IH _ _ _ rfl (co_ok hx).1 (co_ok hx).2) hx
    | cmp o a b =>
      simp only [ev, andR, orR, rowR, consR, callR] at h
      obtain ⟨x, hx, h1⟩ := bnd_inv h hu hf
      obtain ⟨y, hy, h2⟩ := bnd_inv h1 hu hf
      subst h2
      exact Ev.cmpV (IH _ _ _ rfl (co_ok hx).1 (co_ok hx).2) hx (IH _ _ _ rfl (co_ok hy).1 (co_ok hy).2) hy
    | chain3 o₁ o₂ a b c =>
      simp only [ev, andR, orR, rowR, consR, callR] at h
      obtain ⟨x, hx, h1⟩ := bnd_inv h hu hf
      have Ha := IH _ _ _ rfl (co_ok hx).1 (co_ok hx).2
      cases x with
      | none => simp at h1; subst h1; exact Ev.chainA Ha hx
      | some x' =>
        simp only at h1
        obtain ⟨y, hy, h2⟩ := bnd_inv h1 hu hf
        have Hb := IH _ _ _ rfl (co_ok hy).1 (co_ok hy).2
        cases y with
        | none => simp at h2; subst h2; exact Ev.chainB Ha hx Hb hy
        | some y' =>
          simp only at h2
          by_cases hc : cmpHolds o₁ x' y' = true
          · simp only [hc, ite_true] at h2
            obtain ⟨z, hz, h3⟩ := bnd_inv h2 hu hf
            have Hc := IH _ _ _ rfl (co_ok hz).1 (co_ok hz).2
            subst h3
            exact Ev.chainD Ha hx Hb hy hc Hc hz
          · have hc' : cmpHolds o₁ x' y' = false := by simpa using hc
            rw [hc'] at h2; simp at h2; subst h2
            exact Ev.chainC Ha hx Hb hy hc'
    | and a b =>
      simp only [ev, andR, orR, rowR, consR, callR] at h
      rcases hr : ev fs sel n ρ a with (_ | x) | _ | l | _ | _ <;> rw [hr] at h <;> try simp only at h
      · subst h; exact Ev.andN (IH _ _ _ hr (by simp) (by simp))
      · exact Ev.andV (IH _ _ _ hr (by simp) (by simp)) (IH _ _ _ h hu hf)
      all_goals (subst h; first | exact absurd rfl hu | exact absurd rfl hf)
    | or a b =>
      simp only [ev, andR, orR, rowR, consR, callR] at h
      rcases hr : ev fs sel n ρ a with (_ | x) | _ | l | _ | _ <;> rw [hr] at h <;> try simp only at h
      · exact Ev.orN (IH _ _ _ hr (by simp) (by simp)) (IH _ _ _ h hu hf)
      · subst h; exact Ev.orV (IH _ _ _ hr (by simp) (by simp))
      all_goals (subst h; first | exact absurd rfl hu | exact absurd rfl hf)
    | rowD v rest =>
      simp only [ev, andR, orR, rowR, consR, callR] at h
      rcases hr : ev fs sel n ρ v with (_ | x) | _ | l | _ | _ <;> rw [hr] at h <;> try simp only at h
      · exact Ev.rowDFallV (IH _ _ _ hr (by simp) (by simp)) (IH _ _ _ h hu hf)
      · subst h; exact Ev.rowDHit (IH _ _ _ hr (by simp) (by simp))
      · exact Ev.rowDFallP (IH _ _ _ hr (by simp) (by simp)) (IH _ _ _ h hu hf)
      all_goals (subst h; first | exact absurd rfl hu | exact absurd rfl hf)
    | rowC c v rest =>
      simp only [ev, andR, orR, rowR, consR, callR] at h
      obtain ⟨x, hx, h1⟩ := bnd_inv h hu hf
      have Hc := IH _ _ _ rfl (co_ok hx).1 (co_ok hx).2
      cases x with
      | none => simp only at h1; exact Ev.rowCSkip Hc hx (IH _ _ _ h1 hu hf)
      | some x' =>
        simp only at h1
        rcases hr : ev fs sel n ρ v with (_ | y) | _ | l | _ | _ <;> rw [hr] at h1 <;> try simp only at h1
        · exact Ev.rowCFallV Hc hx (IH _ _ _ hr (by simp) (by simp)) (IH _ _ _ h1 hu hf)
        · subst h1; exact Ev.rowCHit Hc hx (IH _ _ _ hr (by simp) (by simp))
        · exact Ev.rowCFallP Hc hx (IH _ _ _ hr (by simp) (by simp)) (IH _ _ _ h1 hu hf)
        all_goals (subst h1; first | exact absurd rfl hu | exact absurd rfl hf)
    | anil => simp only [ev, andR, orR, rowR, consR, callR] at h; subst h; exact Ev.anil
    | acons a rest =>
      simp only [ev, andR, orR, rowR, consR, callR] at h
      rcases hr : ev fs sel n ρ a with x | _ | l | _ | _ <;> rw [hr] at h <;> try simp only at h
      · rcases hs : ev fs sel n ρ rest with y | _ | l' | _ | _ <;> rw [hs] at h <;> try simp only at h
        all_goals first
          | (subst h; first | exact absurd rfl hu | exact absurd rfl hf)
          | skip
        subst h
        exact Ev.acons (IH _ _ _ hr (by simp) (by simp)) (IH _ _ _ hs (by simp) (by simp))
      all_goals (subst h; first | exact absurd rfl hu | exact absurd rfl hf)
    | call f as =>
      simp only [ev, andR, orR, rowR, consR, callR] at h
      rcases hr : ev fs sel n ρ as with y | _ | l | _ | _ <;> rw [hr] at h <;> try simp only at h
      · subst h; exact absurd rfl hu
      · subst h; exact absurd rfl hu
      · have Ha := IH _ _ _ hr (by simp) (by simp)
        rcases hf' : fs f with _ | ⟨k, body⟩ <;> rw [hf'] at h <;> dsimp only at h
        · subst h; exact absurd rfl hu
        · by_cases hk : l.length ≠ k
          · rw [if_pos hk] at h; subst h; exact absurd rfl hu
          · have hk' : l.length = k := by simpa using hk
            simp only [hk, ite_false] at h
            by_cases hn : l.any Option.isNone = true
            · simp only [hn, ite_true] at h; subst h; exact Ev.callPF Ha hf' hk' hn
            · have hn' : l.any Option.isNone = false := by
                cases hh : l.any Option.isNone
                · rfl
                · exact absurd hh hn
              simp only [hn, ite_false] at h
              subst h
              have hb : ev fs sel n (fun i => l.getD i none) body ≠ .unsup ∧ ev fs sel n (fun i => l.getD i none) body ≠ .fuel := by
                constructor <;> intro e <;> rw [e] at hu hf <;> simp [dePF] at hu hf
              exact Ev.callRun Ha hf' hk' hn' (IH _ _ _ rfl hb.1 hb.2)
      all_goals (subst h; first | exact absurd rfl hu | exact absurd rfl hf)

/-! ## 燃料の単調性: 燃料切れでなければ、燃料を増やしても同じ -/

/-- `A` は燃料切れか、`A'` と同じ -/
abbrev Refines (A A' : Res) : Prop := A = .fuel ∨ A = A'

theorem bnd_mono {A A' : Res} {k k' : V → Res} (hA : Refines A A') (hk : ∀ x, Refines (k x) (k' x)) :
    Refines (bnd A k) (bnd A' k') := by
  rcases hA with h | h
  · subst h; left; rfl
  · subst h
    cases A with
    | v x => exact hk x
    | pf => exact hk none
    | args l => right; rfl
    | unsup => right; rfl
    | fuel => left; rfl

theorem andR_mono {A A' : Res} {B B' : Unit → Res} (hA : Refines A A') (hB : Refines (B ()) (B' ())) :
    Refines (andR A B) (andR A' B') := by
  rcases hA with h | h
  · subst h; left; rfl
  · subst h
    cases A with
    | v x => cases x with
      | none => right; rfl
      | some _ => exact hB
    | pf => right; rfl
    | args l => right; rfl
    | unsup => right; rfl
    | fuel => left; rfl

theorem orR_mono {A A' : Res} {B B' : Unit → Res} (hA : Refines A A') (hB : Refines (B ()) (B' ())) :
    Refines (orR A B) (orR A' B') := by
  rcases hA with h | h
  · subst h; left; rfl
  · subst h
    cases A with
    | v x => cases x with
      | none => exact hB
      | some _ => right; rfl
    | pf => right; rfl
    | args l => right; rfl
    | unsup => right; rfl
    | fuel => left; rfl

theorem rowR_mono {A A' : Res} {B B' : Unit → Res} (hA : Refines A A') (hB : Refines (B ()) (B' ())) :
    Refines (rowR A B) (rowR A' B') := by
  rcases hA with h | h
  · subst h; left; rfl
  · subst h
    cases A with
    | v x => cases x with
      | none => exact hB
      | some _ => right; rfl
    | pf => exact hB
    | args l => right; rfl
    | unsup => right; rfl
    | fuel => left; rfl

theorem consR_mono {A A' : Res} {B B' : Unit → Res} (hA : Refines A A') (hB : Refines (B ()) (B' ())) :
    Refines (consR A B) (consR A' B') := by
  rcases hA with h | h
  · subst h; left; rfl
  · subst h
    cases A with
    | v x =>
      rcases hB with h2 | h2
      · left; simp only [consR]; rw [h2]
      · right; simp only [consR]; rw [h2]
    | pf => right; rfl
    | args l => right; rfl
    | unsup => right; rfl
    | fuel => left; rfl

theorem callR_mono {fs : Fs} {f : Nat} {A A' : Res} {run run' : List V → T → Res}
    (hA : Refines A A') (hr : ∀ l b, Refines (run l b) (run' l b)) :
    Refines (callR fs f A run) (callR fs f A' run') := by
  rcases hA with h | h
  · subst h; left; rfl
  · subst h
    cases A with
    | v x => right; rfl
    | pf => right; rfl
    | args l =>
      cases hfs : fs f with
      | none => right; simp [callR, hfs]
      | some p =>
        obtain ⟨k, body⟩ := p
        by_cases h1 : l.length ≠ k
        · right; simp [callR, hfs, h1]
        · by_cases h2 : l.any Option.isNone = true
          · right; simp [callR, hfs, h1, h2]
          · simp only [callR, hfs, h1, h2, ite_false, if_false]
            rcases hr l body with h3 | h3
            · left; rw [h3]; rfl
            · right; rw [h3]
    | unsup => right; rfl
    | fuel => left; rfl

theorem ev_mono (fs : Fs) (sel : Sel) : ∀ (n m : Nat), n ≤ m → ∀ (ρ : Env) (t : T),
    Refines (ev fs sel n ρ t) (ev fs sel m ρ t) := by
  intro n
  induction n with
  | zero => intro m _ ρ t; left; simp [ev]
  | succ n ih =>
    intro m hnm ρ t
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have h' : n ≤ m' := by omega
    have IH := ih m' h'
    cases t with
    | int k => right; simp [ev]
    | void => right; simp [ev]
    | var i => right; simp [ev]
    | op o a b => simp only [ev]; exact bnd_mono (IH _ _) fun x => bnd_mono (IH _ _) fun y => Or.inr rfl
    | neg a => simp only [ev]; exact bnd_mono (IH _ _) fun x => Or.inr rfl
    | abs a => simp only [ev]; exact bnd_mono (IH _ _) fun x => Or.inr rfl
    | cmp o a b => simp only [ev]; exact bnd_mono (IH _ _) fun x => bnd_mono (IH _ _) fun y => Or.inr rfl
    | chain3 o₁ o₂ a b c =>
      simp only [ev]
      refine bnd_mono (IH _ _) fun x => ?_
      cases x with
      | none => exact Or.inr rfl
      | some x' =>
        refine bnd_mono (IH _ _) fun y => ?_
        cases y with
        | none => exact Or.inr rfl
        | some y' =>
          by_cases hc : cmpHolds o₁ x' y' = true
          · simp only [hc, ite_true]
            exact bnd_mono (IH _ _) fun z => by cases z <;> exact Or.inr rfl
          · simp only [hc]; exact Or.inr rfl
    | and a b => simp only [ev]; exact andR_mono (IH _ _) (IH _ _)
    | or a b => simp only [ev]; exact orR_mono (IH _ _) (IH _ _)
    | rowD v rest => simp only [ev]; exact rowR_mono (IH _ _) (IH _ _)
    | rowC c v rest =>
      simp only [ev]
      refine bnd_mono (IH _ _) fun x => ?_
      cases x with
      | none => exact IH _ _
      | some _ => exact rowR_mono (IH _ _) (IH _ _)
    | anil => right; simp [ev]
    | acons a r => simp only [ev]; exact consR_mono (IH _ _) (IH _ _)
    | call f as => simp only [ev]; exact callR_mono (IH _ _) fun l b => IH _ _

theorem ev_at_ge (fs : Fs) (sel : Sel) {n m : Nat} (hnm : n ≤ m) {ρ : Env} {t : T} {r : Res}
    (h : ev fs sel n ρ t = r) (hf : r ≠ .fuel) : ev fs sel m ρ t = r := by
  rcases ev_mono fs sel n m hnm ρ t with e | e
  · exact absurd (h.symm.trans e) hf
  · rw [← e]; exact h

/-! ## 規則を満たす結果は、十分な燃料で評価器が返す(完全) -/

theorem bnd_co {r : Res} {x : V} {k : V → Res} (h : co r = some x) : bnd r k = k x := by
  cases r <;> simp [co, bnd] at h ⊢ <;> subst h <;> rfl

theorem Ev_nf {fs : Fs} {sel : Sel} {ρ : Env} {t : T} {r : Res} (h : Ev fs sel ρ t r) :
    r ≠ .fuel ∧ r ≠ .unsup := by
  induction h with
  | callRun _ _ _ _ _ _ ih => cases rb : ‹Res› <;> simp_all [dePF]
  | cmpV => constructor <;> (split <;> (try split) <;> simp)
  | chainD => constructor <;> (split <;> (try split) <;> simp)
  | _ => first | (constructor <;> simp; done) | assumption

theorem Ev_complete (fs : Fs) (sel : Sel) {ρ : Env} {t : T} {r : Res} (h : Ev fs sel ρ t r) :
    ∃ n, ev fs sel n ρ t = r := by
  induction h with
  | int k => exact ⟨1, by simp [ev]⟩
  | void => exact ⟨1, by simp [ev]⟩
  | var i => exact ⟨1, by simp [ev]⟩
  | anil => exact ⟨1, by simp [ev]⟩
  | op _ hx _ hy iha ihb =>
    obtain ⟨n1, h1⟩ := iha; obtain ⟨n2, h2⟩ := ihb
    refine ⟨max n1 n2 + 1, ?_⟩
    have e1 := ev_at_ge fs sel (n := n1) (m := max n1 n2) (by omega) h1 (co_ok hx).2
    have e2 := ev_at_ge fs sel (n := n2) (m := max n1 n2) (by omega) h2 (co_ok hy).2
    simp only [ev]; rw [e1, e2, bnd_co hx, bnd_co hy]
  | neg _ hx iha =>
    obtain ⟨n1, h1⟩ := iha
    refine ⟨n1 + 1, ?_⟩
    simp only [ev]; rw [h1, bnd_co hx]
  | abs _ hx iha =>
    obtain ⟨n1, h1⟩ := iha
    refine ⟨n1 + 1, ?_⟩
    simp only [ev]; rw [h1, bnd_co hx]
  | cmpV _ hx _ hy iha ihb =>
    obtain ⟨n1, h1⟩ := iha; obtain ⟨n2, h2⟩ := ihb
    refine ⟨max n1 n2 + 1, ?_⟩
    have e1 := ev_at_ge fs sel (n := n1) (m := max n1 n2) (by omega) h1 (co_ok hx).2
    have e2 := ev_at_ge fs sel (n := n2) (m := max n1 n2) (by omega) h2 (co_ok hy).2
    simp only [ev]; rw [e1, e2, bnd_co hx, bnd_co hy]
  | chainA _ hx iha =>
    obtain ⟨n1, h1⟩ := iha
    refine ⟨n1 + 1, ?_⟩
    simp only [ev]; rw [h1, bnd_co hx]
  | chainB _ hx _ hy iha ihb =>
    obtain ⟨n1, h1⟩ := iha; obtain ⟨n2, h2⟩ := ihb
    refine ⟨max n1 n2 + 1, ?_⟩
    have e1 := ev_at_ge fs sel (n := n1) (m := max n1 n2) (by omega) h1 (co_ok hx).2
    have e2 := ev_at_ge fs sel (n := n2) (m := max n1 n2) (by omega) h2 (co_ok hy).2
    simp only [ev]; rw [e1, bnd_co hx]; simp only []; rw [e2, bnd_co hy]
  | chainC _ hx _ hy hc iha ihb =>
    obtain ⟨n1, h1⟩ := iha; obtain ⟨n2, h2⟩ := ihb
    refine ⟨max n1 n2 + 1, ?_⟩
    have e1 := ev_at_ge fs sel (n := n1) (m := max n1 n2) (by omega) h1 (co_ok hx).2
    have e2 := ev_at_ge fs sel (n := n2) (m := max n1 n2) (by omega) h2 (co_ok hy).2
    simp only [ev]; rw [e1, bnd_co hx]; simp only []; rw [e2, bnd_co hy]; simp [hc]
  | chainD _ hx _ hy hc _ hz iha ihb ihc =>
    obtain ⟨n1, h1⟩ := iha; obtain ⟨n2, h2⟩ := ihb; obtain ⟨n3, h3⟩ := ihc
    refine ⟨max n1 (max n2 n3) + 1, ?_⟩
    have e1 := ev_at_ge fs sel (n := n1) (m := max n1 (max n2 n3)) (by omega) h1 (co_ok hx).2
    have e2 := ev_at_ge fs sel (n := n2) (m := max n1 (max n2 n3)) (by omega) h2 (co_ok hy).2
    have e3 := ev_at_ge fs sel (n := n3) (m := max n1 (max n2 n3)) (by omega) h3 (co_ok hz).2
    simp only [ev]; rw [e1, bnd_co hx]; simp only []; rw [e2, bnd_co hy]; simp only [hc, ite_true]; rw [e3, bnd_co hz]
  | andN _ iha =>
    obtain ⟨n1, h1⟩ := iha
    refine ⟨n1 + 1, ?_⟩
    simp only [ev]; rw [h1]; rfl
  | andV _ _ iha ihb =>
    rename_i ρ a b x r ha hb
    obtain ⟨n1, h1⟩ := iha; obtain ⟨n2, h2⟩ := ihb
    refine ⟨max n1 n2 + 1, ?_⟩
    have e1 := ev_at_ge fs sel (n := n1) (m := max n1 n2) (by omega) h1 (by simp)
    have e2 := ev_at_ge fs sel (n := n2) (m := max n1 n2) (by omega) h2 (Ev_nf hb).1
    simp only [ev, andR]; rw [e1, e2]
  | orV _ iha =>
    obtain ⟨n1, h1⟩ := iha
    refine ⟨n1 + 1, ?_⟩
    simp only [ev]; rw [h1]; rfl
  | orN _ _ iha ihb =>
    rename_i ρ a b r ha hb
    obtain ⟨n1, h1⟩ := iha; obtain ⟨n2, h2⟩ := ihb
    refine ⟨max n1 n2 + 1, ?_⟩
    have e1 := ev_at_ge fs sel (n := n1) (m := max n1 n2) (by omega) h1 (by simp)
    have e2 := ev_at_ge fs sel (n := n2) (m := max n1 n2) (by omega) h2 (Ev_nf hb).1
    simp only [ev, orR]; rw [e1, e2]
  | rowDHit _ iha =>
    obtain ⟨n1, h1⟩ := iha
    refine ⟨n1 + 1, ?_⟩
    simp only [ev]; rw [h1]; rfl
  | rowDFallV _ _ iha ihb =>
    rename_i ρ v rest r hv hr
    obtain ⟨n1, h1⟩ := iha; obtain ⟨n2, h2⟩ := ihb
    refine ⟨max n1 n2 + 1, ?_⟩
    have e1 := ev_at_ge fs sel (n := n1) (m := max n1 n2) (by omega) h1 (by simp)
    have e2 := ev_at_ge fs sel (n := n2) (m := max n1 n2) (by omega) h2 (Ev_nf hr).1
    simp only [ev, rowR]; rw [e1, e2]
  | rowDFallP _ _ iha ihb =>
    rename_i ρ v rest r hv hr
    obtain ⟨n1, h1⟩ := iha; obtain ⟨n2, h2⟩ := ihb
    refine ⟨max n1 n2 + 1, ?_⟩
    have e1 := ev_at_ge fs sel (n := n1) (m := max n1 n2) (by omega) h1 (by simp)
    have e2 := ev_at_ge fs sel (n := n2) (m := max n1 n2) (by omega) h2 (Ev_nf hr).1
    simp only [ev, rowR]; rw [e1, e2]
  | rowCSkip _ hx _ iha ihb =>
    rename_i ρ c v rest rc r hc hr
    obtain ⟨n1, h1⟩ := iha; obtain ⟨n2, h2⟩ := ihb
    refine ⟨max n1 n2 + 1, ?_⟩
    have e1 := ev_at_ge fs sel (n := n1) (m := max n1 n2) (by omega) h1 (co_ok hx).2
    have e2 := ev_at_ge fs sel (n := n2) (m := max n1 n2) (by omega) h2 (Ev_nf hr).1
    simp only [ev]; rw [e1, bnd_co hx]; simp only []; rw [e2]
  | rowCHit _ hx _ iha ihb =>
    rename_i ρ c v rest rc x r hc hr
    obtain ⟨n1, h1⟩ := iha; obtain ⟨n2, h2⟩ := ihb
    refine ⟨max n1 n2 + 1, ?_⟩
    have e1 := ev_at_ge fs sel (n := n1) (m := max n1 n2) (by omega) h1 (co_ok hx).2
    have e2 := ev_at_ge fs sel (n := n2) (m := max n1 n2) (by omega) h2 (by simp)
    simp only [ev]; rw [e1, bnd_co hx]; simp only [rowR]; rw [e2]
  | rowCFallV _ hx _ _ iha ihb ihc =>
    rename_i ρ c v rest rc x r hc hv hr
    obtain ⟨n1, h1⟩ := iha; obtain ⟨n2, h2⟩ := ihb; obtain ⟨n3, h3⟩ := ihc
    refine ⟨max n1 (max n2 n3) + 1, ?_⟩
    have e1 := ev_at_ge fs sel (n := n1) (m := max n1 (max n2 n3)) (by omega) h1 (co_ok hx).2
    have e2 := ev_at_ge fs sel (n := n2) (m := max n1 (max n2 n3)) (by omega) h2 (by simp)
    have e3 := ev_at_ge fs sel (n := n3) (m := max n1 (max n2 n3)) (by omega) h3 (Ev_nf hr).1
    simp only [ev]; rw [e1, bnd_co hx]; simp only [rowR]; rw [e2, e3]
  | rowCFallP _ hx _ _ iha ihb ihc =>
    rename_i ρ c v rest rc x r hc hv hr
    obtain ⟨n1, h1⟩ := iha; obtain ⟨n2, h2⟩ := ihb; obtain ⟨n3, h3⟩ := ihc
    refine ⟨max n1 (max n2 n3) + 1, ?_⟩
    have e1 := ev_at_ge fs sel (n := n1) (m := max n1 (max n2 n3)) (by omega) h1 (co_ok hx).2
    have e2 := ev_at_ge fs sel (n := n2) (m := max n1 (max n2 n3)) (by omega) h2 (by simp)
    have e3 := ev_at_ge fs sel (n := n3) (m := max n1 (max n2 n3)) (by omega) h3 (Ev_nf hr).1
    simp only [ev]; rw [e1, bnd_co hx]; simp only [rowR]; rw [e2, e3]
  | acons _ _ iha ihb =>
    obtain ⟨n1, h1⟩ := iha; obtain ⟨n2, h2⟩ := ihb
    refine ⟨max n1 n2 + 1, ?_⟩
    have e1 := ev_at_ge fs sel (n := n1) (m := max n1 n2) (by omega) h1 (by simp)
    have e2 := ev_at_ge fs sel (n := n2) (m := max n1 n2) (by omega) h2 (by simp)
    simp only [ev, consR]; rw [e1, e2]
  | callPF _ hf hl hn iha =>
    obtain ⟨n1, h1⟩ := iha
    refine ⟨n1 + 1, ?_⟩
    simp only [ev, callR]; rw [h1]; simp [hf, hl, hn]
  | callRun _ hf hl hn _ iha ihb =>
    rename_i ρ f as l k body rb ha hb
    obtain ⟨n1, h1⟩ := iha; obtain ⟨n2, h2⟩ := ihb
    refine ⟨max n1 n2 + 1, ?_⟩
    have e1 := ev_at_ge fs sel (n := n1) (m := max n1 n2) (by omega) h1 (by simp)
    have e2 := ev_at_ge fs sel (n := n2) (m := max n1 n2) (by omega) h2 (Ev_nf hb).1
    simp only [ev, callR]; rw [e1]; dsimp only; rw [hf]; dsimp only
    rw [if_neg (by simp [hl]), if_neg (by simp [hn]), e2]

/-- 規則は決定的(部分的な正しさ: 値があれば一意) -/
theorem Ev_det (fs : Fs) (sel : Sel) {ρ : Env} {t : T} {r r' : Res}
    (h : Ev fs sel ρ t r) (h' : Ev fs sel ρ t r') : r = r' := by
  obtain ⟨n, hn⟩ := Ev_complete fs sel h
  obtain ⟨m, hm⟩ := Ev_complete fs sel h'
  have a := ev_at_ge fs sel (Nat.le_max_left n m) hn (Ev_nf h).1
  have b := ev_at_ge fs sel (Nat.le_max_right n m) hm (Ev_nf h').1
  exact a.symm.trans b

/-- 段階 (b)(呼びを含む): 評価器が燃料切れでも SIR 外でもなければ、結果は規則が導く。逆も言える -/
theorem ev_iff (fs : Fs) (sel : Sel) (ρ : Env) (t : T) (r : Res) :
    (∃ n, ev fs sel n ρ t = r ∧ r ≠ .unsup ∧ r ≠ .fuel) ↔ Ev fs sel ρ t r :=
  ⟨fun ⟨n, h, hu, hf⟩ => ev_sound fs sel n ρ t r h hu hf,
   fun h => by obtain ⟨n, hn⟩ := Ev_complete fs sel h; exact ⟨n, hn, (Ev_nf h).2, (Ev_nf h).1⟩⟩

/-- 部分適用: 実引数が `!_` なら呼びは成り立たず `pf`(口の数ちょうど) -/
theorem call_void_arg_pf (fs : Fs) (sel : Sel) (ρ : Env) (f k : Nat) (body : T) (hf : fs f = some (k, body))
    (as : T) (l : List V) (ha : Ev fs sel ρ as (.args l)) (hl : l.length = k) (hv : none ∈ l) :
    Ev fs sel ρ (.call f as) .pf :=
  Ev.callPF ha hf hl (by simpa using hv)

end SirZC

#print axioms SirZC.ev_iff
#print axioms SirZC.Ev_det
