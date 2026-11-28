/-
  SIR-Z の評価器(SirZCall.lean の規則 `Ev`)と、機械語の側の意味(SirZAsm.lean の `sem2`・燃料つきの関数表 `ΦF`)の橋。
  Mathlib なし。先に `lean -o SirZAsm.olean SirZAsm.lean` と `lean -o SirZCall.olean SirZCall.lean` で olean を作り、
  `LEAN_PATH=<olean のある場所> lean SirZBridge.lean` で検査する。

  * `tr : E → SirZC.T`: SirZAsm の式(呼び `call1`/`call2` を含む)を SirZCall の項に写す(実引数は `acons` の鎖)。
  * `TermG`/`DomG`: `Term`/`DomF` に「呼びの実引数が部分適用(`pf`)にならない」(評価器は並びの中の `pf` を SIR の外とする)を足した止まる条件。`DomG_DomF`: `DomG` ⊆ `DomF`。
  * `limit_sound`: 燃料 `k` 段で止まる(`DomG`)呼びの本体は、規則 `Ev` でも同じ値に評価される。
  * `limit_complete`: 規則 `Ev` が本体を値に評価するなら、ある燃料で止まり同じ値(`Ev` の導出についての帰納法。燃料は部分木ごとに違うので、単調性 `termG_fuel_mono` で max に揃える)。
  * `loop_sound`: 自分への末尾呼びのループ関数(`loopT` = 行 `c : v` + 既定の行 `self(as..)`)の燃料つき反復 `LΦ`(SirZAsm)は、評価器の規則 `Ev` でも同じ値。`tree_sound_fs` は `tree_sound` を任意の関数表に一般化したもの。
  * `limit_iff`: `(∃ k, DomG body k f l ∧ ΦF body k f l = x) ↔ ∃ rb, Ev … (tr (body f)) rb ∧ co rb = some x`(`ΦF` の極限 = 評価器の意味)。
-/
import SirZAsm
import SirZCall
open SirZAsm

namespace SirZB

/-! ### SirZAsm の式 `E` を SirZCall の項 `SirZC.T` に写す -/

def cA : SirZAsm.AOp → SirZC.AOp
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div | .mod => .mod

def cC : SirZAsm.CmpOp → SirZC.COp
  | .lt => .lt | .le => .le | .gt => .gt | .ge => .ge | .eq => .eq

def tr : SirZAsm.E → SirZC.T
  | .lit n => .int n
  | .var k => .var k
  | .op o l r => .op (cA o) (tr l) (tr r)
  | .neg e => .neg (tr e)
  | .cmp c l r => .cmp (cC c) (tr l) (tr r)
  | .call1 f a => .call f (.acons (tr a) .anil)
  | .call2 f a b => .call f (.acons (tr a) (.acons (tr b) .anil))

theorem arith_eq (o : SirZAsm.AOp) (x y : Option Int) :
    SirZC.arith (cA o) x y = SirZAsm.arith o x y := by
  cases o <;> cases x <;> cases y <;> rfl

theorem clamp_eq (z : Int) : SirZC.clamp z = SirZAsm.clamp z := rfl

theorem cmp_eq (c : SirZAsm.CmpOp) (a b : Int) : SirZC.cmpHolds (cC c) a b = c.holds a b := by
  cases c <;> rfl

/-- 呼びの口の `pf` になる形: 実引数のどれかが `!_` -/
def pfOf (Φ : Nat → List (Option Int) → Option Int) (ρ : Nat → Option Int) : E → Prop
  | .call1 _ x => sem2 Φ ρ x = none
  | .call2 _ x y => sem2 Φ ρ x = none ∨ sem2 Φ ρ y = none
  | _ => False

/-- `Term` に「呼びの実引数が部分適用(`pf`)にならない」を足したもの(評価器は並びの中の `pf` を SIR の外とする) -/
def TermG (Φ : Nat → List (Option Int) → Option Int) (Dom : Nat → List (Option Int) → Prop) (ρ : Nat → Option Int) : E → Prop
  | .lit _ => True
  | .var _ => True
  | .op _ l r => TermG Φ Dom ρ l ∧ TermG Φ Dom ρ r
  | .neg e => TermG Φ Dom ρ e
  | .cmp _ l r => TermG Φ Dom ρ l ∧ TermG Φ Dom ρ r
  | .call1 f a => TermG Φ Dom ρ a ∧ ¬ pfOf Φ ρ a ∧ ((∀ v ∈ [sem2 Φ ρ a], ∃ z, v = some z) → Dom f [sem2 Φ ρ a])
  | .call2 f a b => TermG Φ Dom ρ a ∧ TermG Φ Dom ρ b ∧ ¬ pfOf Φ ρ a ∧ ¬ pfOf Φ ρ b ∧
      ((∀ v ∈ [sem2 Φ ρ a, sem2 Φ ρ b], ∃ z, v = some z) → Dom f [sem2 Φ ρ a, sem2 Φ ρ b])

theorem termG_mono (Φ Φ' : Nat → List (Option Int) → Option Int) (Dom Dom' : Nat → List (Option Int) → Prop)
    (H : ∀ f vs, Dom f vs → Dom' f vs ∧ Φ' f vs = Φ f vs) (ρ : Nat → Option Int) :
    ∀ e : E, TermG Φ Dom ρ e → TermG Φ' Dom' ρ e ∧ sem2 Φ' ρ e = sem2 Φ ρ e ∧ (pfOf Φ' ρ e ↔ pfOf Φ ρ e) := by
  intro e
  induction e with
  | lit n => intro _; exact ⟨trivial, rfl, Iff.rfl⟩
  | var k => intro _; exact ⟨trivial, rfl, Iff.rfl⟩
  | neg e ih =>
      intro h; obtain ⟨h1, h2, _⟩ := ih h
      exact ⟨h1, by simp [sem2, h2], Iff.rfl⟩
  | op o l r ihl ihr =>
      intro h; obtain ⟨hl1, hl2, _⟩ := ihl h.1; obtain ⟨hr1, hr2, _⟩ := ihr h.2
      exact ⟨⟨hl1, hr1⟩, by simp [sem2, hl2, hr2], Iff.rfl⟩
  | cmp c l r ihl ihr =>
      intro h; obtain ⟨hl1, hl2, _⟩ := ihl h.1; obtain ⟨hr1, hr2, _⟩ := ihr h.2
      exact ⟨⟨hl1, hr1⟩, by simp [sem2, hl2, hr2], Iff.rfl⟩
  | call1 f a ih =>
      intro h; obtain ⟨ha1, ha2, ha3⟩ := ih h.1
      have hD : (∀ v ∈ [sem2 Φ' ρ a], ∃ z, v = some z) → Dom' f [sem2 Φ' ρ a] := by
        rw [ha2]; intro hs; exact (H _ _ (h.2.2 hs)).1
      refine ⟨⟨ha1, fun hp => h.2.1 (ha3.1 hp), hD⟩, ?_, by simp [pfOf, ha2]⟩
      simp only [sem2, ha2, callSem]
      by_cases hv : [sem2 Φ ρ a].all Option.isSome = true
      · have hs : ∀ v ∈ [sem2 Φ ρ a], ∃ z, v = some z := by
          intro v hv'; simp at hv'; subst hv'; simpa [Option.isSome_iff_exists] using hv
        rw [if_pos hv, if_pos hv]; exact (H _ _ (h.2.2 hs)).2
      · rw [if_neg hv, if_neg hv]
  | call2 f a b iha ihb =>
      intro h; obtain ⟨ha1, ha2, ha3⟩ := iha h.1; obtain ⟨hb1, hb2, hb3⟩ := ihb h.2.1
      have hD : (∀ v ∈ [sem2 Φ' ρ a, sem2 Φ' ρ b], ∃ z, v = some z) → Dom' f [sem2 Φ' ρ a, sem2 Φ' ρ b] := by
        rw [ha2, hb2]; intro hs; exact (H _ _ (h.2.2.2.2 hs)).1
      refine ⟨⟨ha1, hb1, fun hp => h.2.2.1 (ha3.1 hp), fun hp => h.2.2.2.1 (hb3.1 hp), hD⟩, ?_, by simp [pfOf, ha2, hb2]⟩
      simp only [sem2, ha2, hb2, callSem]
      by_cases hv : [sem2 Φ ρ a, sem2 Φ ρ b].all Option.isSome = true
      · have hs : ∀ v ∈ [sem2 Φ ρ a, sem2 Φ ρ b], ∃ z, v = some z := by
          intro v hv'; simp at hv'
          simp [Option.isSome_iff_exists] at hv
          cases hv' with
          | inl h1 => subst h1; exact hv.1
          | inr h1 => subst h1; exact hv.2
        rw [if_pos hv, if_pos hv]; exact (H _ _ (h.2.2.2.2 hs)).2
      · rw [if_neg hv, if_neg hv]

def DomG (body : Nat → E) : Nat → Nat → List (Option Int) → Prop
  | 0, _, _ => False
  | k + 1, f, vs => TermG (ΦF body k) (DomG body k) (envOf vs) (body f)

theorem DomG_step (body : Nat → E) :
    ∀ k f vs, DomG body k f vs → DomG body (k + 1) f vs ∧ ΦF body (k + 1) f vs = ΦF body k f vs := by
  intro k
  induction k with
  | zero => intro f vs h; exact absurd h (by simp [DomG])
  | succ k ih =>
      intro f vs h
      have := termG_mono (ΦF body k) (ΦF body (k + 1)) (DomG body k) (DomG body (k + 1)) ih (envOf vs) (body f) h
      exact ⟨this.1, this.2.1⟩

theorem DomG_mono_le (body : Nat → E) {k k' : Nat} (hk : k ≤ k') (f : Nat) (vs : List (Option Int))
    (h : DomG body k f vs) : DomG body k' f vs ∧ ΦF body k' f vs = ΦF body k f vs := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction n with
  | zero => exact ⟨h, rfl⟩
  | succ n ih =>
      obtain ⟨h1, h2⟩ := ih (Nat.le_add_right k n)
      obtain ⟨h3, h4⟩ := DomG_step body (k + n) f vs h1
      exact ⟨h3, by show ΦF body (k + n + 1) f vs = _; rw [h4, h2]⟩

theorem termG_fuel_mono (body : Nat → E) {k k' : Nat} (hk : k ≤ k') (ρ : Nat → Option Int) (e : E)
    (h : TermG (ΦF body k) (DomG body k) ρ e) :
    TermG (ΦF body k') (DomG body k') ρ e ∧ sem2 (ΦF body k') ρ e = sem2 (ΦF body k) ρ e ∧
      (pfOf (ΦF body k') ρ e ↔ pfOf (ΦF body k) ρ e) :=
  termG_mono _ _ _ _ (fun f vs hd => DomG_mono_le body hk f vs hd) ρ e h

def fsOf (ar : Nat → Nat) (body : Nat → E) : SirZC.Fs := fun f => some (ar f, tr (body f))

theorem co_v {r : SirZC.Res} {x : Option Int} (h : SirZC.co r = some x) (hne : r ≠ .pf) : r = .v x := by
  cases r with
  | v y => simp [SirZC.co] at h; rw [h]
  | pf => exact absurd rfl hne
  | args l => simp [SirZC.co] at h
  | unsup => simp [SirZC.co] at h
  | fuel => simp [SirZC.co] at h

theorem co_dePF (r : SirZC.Res) : SirZC.co (SirZC.dePF r) = SirZC.co r := by
  cases r <;> simp [SirZC.dePF, SirZC.co]

theorem dePF_ne_pf (r : SirZC.Res) : SirZC.dePF r ≠ .pf := by
  cases r <;> simp [SirZC.dePF]

theorem neg_eq (x : Option Int) (hx : InR x) :
    x.bind (fun z => SirZC.clamp (-z)) = x.map (fun a => -a) := by
  cases x with
  | none => rfl
  | some z =>
      have := hx z rfl
      simp [SirZC.clamp, SirZC.M]
      unfold M at this; omega

theorem tree_sound_fs (ar : Nat → Nat) (fs : SirZC.Fs) (bd : Nat → SirZC.T) (hfs : ∀ f, fs f = some (ar f, bd f))
    (Φ : Nat → List (Option Int) → Option Int) (Dom : Nat → List (Option Int) → Prop)
    (hΦ : ∀ f vs, (∀ v ∈ vs, InR v) → InR (Φ f vs))
    (HΦ : ∀ f vs, Dom f vs → vs.length = ar f → (∀ v ∈ vs, ∃ z, v = some z) → (∀ v ∈ vs, InR v) →
      ∃ rb, SirZC.Ev fs SirZC.selLeft (fun i => vs.getD i none) (bd f) rb ∧ SirZC.co rb = some (Φ f vs))
    (ρT : SirZC.Env) (ρE : Nat → Option Int) (hρ : ∀ i, InR (ρE i)) :
    ∀ e : E, e.lits2 → e.arOk ar → (∀ i < e.maxVar, ρT i = ρE i) → TermG Φ Dom ρE e →
      ∃ r, SirZC.Ev fs SirZC.selLeft ρT (tr e) r ∧ SirZC.co r = some (sem2 Φ ρE e) ∧ (r = .pf → pfOf Φ ρE e) := by
  intro e
  induction e with
  | lit n =>
      intro _ _ _ _
      exact ⟨_, SirZC.Ev.int n, rfl, fun h => by cases h⟩
  | var k =>
      intro _ _ hv _
      have : ρT k = ρE k := hv k (by simp [E.maxVar])
      exact ⟨_, SirZC.Ev.var k, by simp [SirZC.co, sem2, this], fun h => by cases h⟩
  | neg e ih =>
      intro hl har hv ht
      obtain ⟨ra, hra, hco, hpf⟩ := ih hl har (by simpa [E.maxVar] using hv) ht
      have hin := sem2_inR Φ hΦ ρE hρ e hl
      refine ⟨_, SirZC.Ev.neg hra hco, ?_, fun h => by cases h⟩
      simp [SirZC.co, sem2, neg_eq _ hin]
  | op o l r ihl ihr =>
      intro hl har hv ht
      obtain ⟨ra, hra, hca, _⟩ := ihl hl.1 har.1 (fun i hi => hv i (by simp [E.maxVar]; omega)) ht.1
      obtain ⟨rb, hrb, hcb, _⟩ := ihr hl.2 har.2 (fun i hi => hv i (by simp [E.maxVar]; omega)) ht.2
      refine ⟨_, SirZC.Ev.op hra hca hrb hcb, ?_, fun h => by cases h⟩
      simp [SirZC.co, sem2, arith_eq]
  | cmp c l r ihl ihr =>
      intro hl har hv ht
      obtain ⟨ra, hra, hca, _⟩ := ihl hl.1 har.1 (fun i hi => hv i (by simp [E.maxVar]; omega)) ht.1
      obtain ⟨rb, hrb, hcb, _⟩ := ihr hl.2 har.2 (fun i hi => hv i (by simp [E.maxVar]; omega)) ht.2
      refine ⟨_, SirZC.Ev.cmpV hra hca hrb hcb, ?_, ?_⟩
      · cases hx : sem2 Φ ρE l with
        | none => simp [SirZC.co, sem2, hx, cmpSem]
        | some a =>
          cases hy : sem2 Φ ρE r with
          | none => simp [SirZC.co, sem2, hx, hy, cmpSem]
          | some b =>
            by_cases hh : c.holds a b = true
            · simp [SirZC.co, sem2, hx, hy, cmpSem, cmp_eq, hh, SirZC.selLeft]
            · simp [SirZC.co, sem2, hx, hy, cmpSem, cmp_eq, hh, SirZC.selLeft]
      · intro h
        cases hx : sem2 Φ ρE l with
        | none => simp [hx] at h
        | some a =>
          cases hy : sem2 Φ ρE r with
          | none => simp [hx, hy] at h
          | some b =>
            by_cases hh : c.holds a b = true
            · simp [hx, hy, cmp_eq, hh] at h
            · simp [hx, hy, cmp_eq, hh] at h
  | call1 f a ih =>
      intro hl har hv ht
      obtain ⟨ra, hra, hca, hpa⟩ := ih hl har.2 (by simpa [E.maxVar] using hv) ht.1
      have hra' : ra = .v (sem2 Φ ρE a) := co_v hca (fun h => ht.2.1 (hpa h))
      subst hra'
      have hin := sem2_inR Φ hΦ ρE hρ a hl
      have hargs : SirZC.Ev fs SirZC.selLeft ρT (.acons (tr a) .anil) (.args [sem2 Φ ρE a]) :=
        SirZC.Ev.acons hra SirZC.Ev.anil
      by_cases hall : ∃ z, sem2 Φ ρE a = some z
      · obtain ⟨z, hz⟩ := hall
        have hall' : ∀ v ∈ [sem2 Φ ρE a], ∃ z, v = some z := by
          intro v hv'; simp at hv'; subst hv'; exact ⟨z, hz⟩
        obtain ⟨rb, hrb, hcb⟩ := HΦ f [sem2 Φ ρE a] (ht.2.2 hall') (by simp [har.1]) hall'
          (by intro v hv'; simp at hv'; subst hv'; exact hin)
        refine ⟨_, SirZC.Ev.callRun hargs (hfs f) (by simp [har.1]) (by simp [hz]) hrb, ?_, fun h => absurd h (dePF_ne_pf _)⟩
        rw [co_dePF, hcb]
        simp [sem2, callSem, hz]
      · have hn : sem2 Φ ρE a = none := by
          cases h : sem2 Φ ρE a with
          | none => rfl
          | some z => exact absurd ⟨z, h⟩ hall
        refine ⟨_, SirZC.Ev.callPF hargs (hfs f) (by simp [har.1]) (by simp [hn]), ?_, fun _ => hn⟩
        simp [SirZC.co, sem2, callSem, hn]
  | call2 f a b iha ihb =>
      intro hl har hv ht
      obtain ⟨ra, hra, hca, hpa⟩ := iha hl.1 har.2.1 (fun i hi => hv i (by simp [E.maxVar]; omega)) ht.1
      obtain ⟨rb, hrb, hcb, hpb⟩ := ihb hl.2 har.2.2 (fun i hi => hv i (by simp [E.maxVar]; omega)) ht.2.1
      have hra' : ra = .v (sem2 Φ ρE a) := co_v hca (fun h => ht.2.2.1 (hpa h))
      have hrb' : rb = .v (sem2 Φ ρE b) := co_v hcb (fun h => ht.2.2.2.1 (hpb h))
      subst hra'; subst hrb'
      have hina := sem2_inR Φ hΦ ρE hρ a hl.1
      have hinb := sem2_inR Φ hΦ ρE hρ b hl.2
      have hargs : SirZC.Ev fs SirZC.selLeft ρT (.acons (tr a) (.acons (tr b) .anil))
          (.args [sem2 Φ ρE a, sem2 Φ ρE b]) :=
        SirZC.Ev.acons hra (SirZC.Ev.acons hrb SirZC.Ev.anil)
      by_cases hall : (∃ z, sem2 Φ ρE a = some z) ∧ (∃ z, sem2 Φ ρE b = some z)
      · obtain ⟨⟨z1, hz1⟩, ⟨z2, hz2⟩⟩ := hall
        have hall' : ∀ v ∈ [sem2 Φ ρE a, sem2 Φ ρE b], ∃ z, v = some z := by
          intro v hv'; simp at hv'
          cases hv' with
          | inl h => subst h; exact ⟨z1, hz1⟩
          | inr h => subst h; exact ⟨z2, hz2⟩
        obtain ⟨rb', hrb', hcb'⟩ := HΦ f [sem2 Φ ρE a, sem2 Φ ρE b] (ht.2.2.2.2 hall') (by simp [har.1]) hall'
          (by intro v hv'; simp at hv'
              cases hv' with
              | inl h => subst h; exact hina
              | inr h => subst h; exact hinb)
        refine ⟨_, SirZC.Ev.callRun hargs (hfs f) (by simp [har.1]) (by simp [hz1, hz2]) hrb', ?_, fun h => absurd h (dePF_ne_pf _)⟩
        rw [co_dePF, hcb']
        simp [sem2, callSem, hz1, hz2]
      · have hn : sem2 Φ ρE a = none ∨ sem2 Φ ρE b = none := by
          cases h1 : sem2 Φ ρE a with
          | none => exact Or.inl rfl
          | some z1 =>
            cases h2 : sem2 Φ ρE b with
            | none => exact Or.inr rfl
            | some z2 => exact absurd ⟨⟨z1, h1⟩, ⟨z2, h2⟩⟩ hall
        refine ⟨_, SirZC.Ev.callPF hargs (hfs f) (by simp [har.1]) (by
          cases hn with
          | inl h => simp [h]
          | inr h => simp [h]), ?_, fun _ => hn⟩
        cases hn with
        | inl h => simp [SirZC.co, sem2, callSem, h]
        | inr h => simp [SirZC.co, sem2, callSem, h]

theorem tree_sound (ar : Nat → Nat) (body : Nat → E)
    (Φ : Nat → List (Option Int) → Option Int) (Dom : Nat → List (Option Int) → Prop)
    (hΦ : ∀ f vs, (∀ v ∈ vs, InR v) → InR (Φ f vs))
    (HΦ : ∀ f vs, Dom f vs → vs.length = ar f → (∀ v ∈ vs, ∃ z, v = some z) → (∀ v ∈ vs, InR v) →
      ∃ rb, SirZC.Ev (fsOf ar body) SirZC.selLeft (fun i => vs.getD i none) (tr (body f)) rb ∧ SirZC.co rb = some (Φ f vs))
    (ρT : SirZC.Env) (ρE : Nat → Option Int) (hρ : ∀ i, InR (ρE i)) :
    ∀ e : E, e.lits2 → e.arOk ar → (∀ i < e.maxVar, ρT i = ρE i) → TermG Φ Dom ρE e →
      ∃ r, SirZC.Ev (fsOf ar body) SirZC.selLeft ρT (tr e) r ∧ SirZC.co r = some (sem2 Φ ρE e) ∧ (r = .pf → pfOf Φ ρE e) :=
  tree_sound_fs ar (fsOf ar body) (fun f => tr (body f)) (fun _ => rfl) Φ Dom hΦ HΦ ρT ρE hρ

theorem getD_envOf (vs : List (Option Int)) (hall : ∀ v ∈ vs, ∃ z, v = some z) (i : Nat) (hi : i < vs.length) :
    vs.getD i none = envOf vs i := by
  obtain ⟨z, hz⟩ := hall vs[i] (List.getElem_mem hi)
  simp [envOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hz]

/-- `ΦF` の側から評価器へ: 燃料 `k` 段で止まる(`DomG`)呼びの本体は、評価器の規則 `Ev` でも同じ値に評価される -/
theorem limit_sound (ar : Nat → Nat) (body : Nat → E)
    (hb : ∀ f, (body f).lits2 ∧ (body f).arOk ar ∧ (body f).maxVar ≤ ar f) :
    ∀ k f (vs : List (Option Int)), DomG body k f vs → vs.length = ar f → (∀ v ∈ vs, ∃ z, v = some z) →
      (∀ v ∈ vs, InR v) →
      ∃ rb, SirZC.Ev (fsOf ar body) SirZC.selLeft (fun i => vs.getD i none) (tr (body f)) rb ∧
        SirZC.co rb = some (ΦF body k f vs) := by
  intro k
  induction k with
  | zero => intro f vs h; exact absurd h (by simp [DomG])
  | succ k ih =>
      intro f vs hD hlen hall hin
      obtain ⟨r, hr, hc, _⟩ := tree_sound ar body (ΦF body k) (DomG body k) (ΦF_inR body (fun f => (hb f).1) k) ih
        (fun i => vs.getD i none) (envOf vs) (envOf_inR_gen vs hin) (body f) (hb f).1 (hb f).2.1
        (fun i hi => getD_envOf vs hall i (by have := (hb f).2.2; omega)) hD
      exact ⟨r, hr, hc⟩

/-- 実引数の並び(`acons` の鎖) -/
def trs : List E → SirZC.T
  | [] => .anil
  | a :: as => .acons (tr a) (trs as)

theorem lift2 (body : Nat → E) (ρ : Nat → Option Int) (e1 e2 : E) (k1 k2 : Nat)
    (h1 : TermG (ΦF body k1) (DomG body k1) ρ e1) (h2 : TermG (ΦF body k2) (DomG body k2) ρ e2) :
    TermG (ΦF body (max k1 k2)) (DomG body (max k1 k2)) ρ e1 ∧ sem2 (ΦF body (max k1 k2)) ρ e1 = sem2 (ΦF body k1) ρ e1 ∧
      (pfOf (ΦF body (max k1 k2)) ρ e1 ↔ pfOf (ΦF body k1) ρ e1) ∧
    TermG (ΦF body (max k1 k2)) (DomG body (max k1 k2)) ρ e2 ∧ sem2 (ΦF body (max k1 k2)) ρ e2 = sem2 (ΦF body k2) ρ e2 ∧
      (pfOf (ΦF body (max k1 k2)) ρ e2 ↔ pfOf (ΦF body k2) ρ e2) := by
  obtain ⟨a1, a2, a3⟩ := termG_fuel_mono body (Nat.le_max_left k1 k2) ρ e1 h1
  obtain ⟨b1, b2, b3⟩ := termG_fuel_mono body (Nat.le_max_right k1 k2) ρ e2 h2
  exact ⟨a1, a2, a3, b1, b2, b3⟩

theorem InR_of_sem2 (body : Nat → E) (hb : ∀ f, (body f).lits2) (k : Nat) (ρ : Nat → Option Int) (hρ : ∀ i, InR (ρ i))
    (e : E) (he : e.lits2) : InR (sem2 (ΦF body k) ρ e) :=
  sem2_inR (ΦF body k) (ΦF_inR body hb k) ρ hρ e he

/-- 評価器の規則 `Ev` の結果と、`ΦF` の燃料つきの意味の対応(木と実引数の並びの両方。`Ev` の導出についての帰納法で証明する) -/
def CompP (body : Nat → E) (ρT : SirZC.Env) (t : SirZC.T) (r : SirZC.Res) : Prop :=
  (∀ (ρE : Nat → Option Int) (e : E), tr e = t → e.lits2 → (∀ i < e.maxVar, ρT i = ρE i) → (∀ i, InR (ρE i)) →
    ∃ k, TermG (ΦF body k) (DomG body k) ρE e ∧ SirZC.co r = some (sem2 (ΦF body k) ρE e) ∧
      (r = .pf → pfOf (ΦF body k) ρE e) ∧ (pfOf (ΦF body k) ρE e → r = .pf)) ∧
  (∀ (ρE : Nat → Option Int) (es : List E), trs es = t → (∀ a ∈ es, a.lits2) →
    (∀ a ∈ es, ∀ i < a.maxVar, ρT i = ρE i) → (∀ i, InR (ρE i)) →
    ∃ k, (∀ a ∈ es, TermG (ΦF body k) (DomG body k) ρE a ∧ ¬ pfOf (ΦF body k) ρE a) ∧
      r = .args (es.map (sem2 (ΦF body k) ρE)))

theorem CompP_vac (body : Nat → E) (ρT : SirZC.Env) (t : SirZC.T) (r : SirZC.Res)
    (hA : ∀ e : E, tr e ≠ t) (hB : ∀ es : List E, trs es ≠ t) : CompP body ρT t r :=
  ⟨fun _ e he => absurd he (hA e), fun _ es he => absurd he (hB es)⟩

theorem tr_ne_void : ∀ e : E, tr e ≠ .void := by intro e; cases e <;> simp [tr]
theorem trs_ne_void : ∀ es : List E, trs es ≠ .void := by intro es; cases es <;> simp [trs]
theorem tr_ne_abs (a : SirZC.T) : ∀ e : E, tr e ≠ .abs a := by intro e; cases e <;> simp [tr]
theorem trs_ne_abs (a : SirZC.T) : ∀ es : List E, trs es ≠ .abs a := by intro es; cases es <;> simp [trs]

macro "vac" : tactic => `(tactic| exact CompP_vac _ _ _ _ (by intro e; cases e <;> simp [tr]) (by intro es; cases es <;> simp [trs]))

theorem complete_aux (ar : Nat → Nat) (body : Nat → E)
    (hb : ∀ f, (body f).lits2 ∧ (body f).arOk ar ∧ (body f).maxVar ≤ ar f)
    {ρT : SirZC.Env} {t : SirZC.T} {r : SirZC.Res} (h : SirZC.Ev (fsOf ar body) SirZC.selLeft ρT t r) :
    CompP body ρT t r := by
  induction h
  case int ρ k0 =>
      constructor
      · intro ρE e he hl hv hI
        cases e <;> simp [tr] at he
        rename_i n; subst he
        exact ⟨0, trivial, rfl, (fun h => by cases h), (fun h => by simp [pfOf] at h)⟩
      · intro ρE es he; cases es <;> simp [trs] at he
  case var ρ i =>
      constructor
      · intro ρE e he hl hv hI
        cases e <;> simp [tr] at he
        rename_i n; subst he
        exact ⟨0, trivial, by simp [SirZC.co, sem2, hv n (by simp [E.maxVar])], (fun h => by cases h),
          (fun h => by simp [pfOf] at h)⟩
      · intro ρE es he; cases es <;> simp [trs] at he
  case void => vac
  case abs => vac
  case chainA => vac
  case chainB => vac
  case chainC => vac
  case chainD => vac
  case andN => vac
  case andV => vac
  case orV => vac
  case orN => vac
  case rowDHit => vac
  case rowDFallV => vac
  case rowDFallP => vac
  case rowCSkip => vac
  case rowCHit => vac
  case rowCFallV => vac
  case rowCFallP => vac
  case anil ρ =>
      constructor
      · intro ρE e he; cases e <;> simp [tr] at he
      · intro ρE es he hl hv hI
        cases es with
        | nil => exact ⟨0, by simp, by simp⟩
        | cons a as => simp [trs] at he
  case op ρ o a b ra rb x y h1 h2 h3 h4 iha ihb =>
      constructor
      · intro ρE e he hl hv hI
        cases e <;> simp [tr] at he
        rename_i o' l r'
        obtain ⟨ho, hla, hrb⟩ := he
        subst ho; subst hla; subst hrb
        obtain ⟨k1, t1, c1, _⟩ := iha.1 ρE l rfl hl.1 (fun i hi => hv i (by simp [E.maxVar]; omega)) hI
        obtain ⟨k2, t2, c2, _⟩ := ihb.1 ρE r' rfl hl.2 (fun i hi => hv i (by simp [E.maxVar]; omega)) hI
        obtain ⟨a1, a2, a3, b1, b2, b3⟩ := lift2 body ρE l r' k1 k2 t1 t2
        have hx : x = sem2 (ΦF body k1) ρE l := by rw [c1] at h2; exact (Option.some.inj h2).symm
        have hy : y = sem2 (ΦF body k2) ρE r' := by rw [c2] at h4; exact (Option.some.inj h4).symm
        refine ⟨max k1 k2, ⟨a1, b1⟩, ?_, (fun h => by cases h), (fun h => by simp [pfOf] at h)⟩
        simp [SirZC.co, sem2, a2, b2, ← hx, ← hy, arith_eq]
      · intro ρE es he; cases es <;> simp [trs] at he
  case neg ρ a ra x h1 h2 iha =>
      constructor
      · intro ρE e he hl hv hI
        cases e <;> simp [tr] at he
        rename_i e'
        subst he
        obtain ⟨k1, t1, c1, _⟩ := iha.1 ρE e' rfl hl (by simpa [E.maxVar] using hv) hI
        have hx : x = sem2 (ΦF body k1) ρE e' := by rw [c1] at h2; exact (Option.some.inj h2).symm
        have hin := InR_of_sem2 body (fun f => (hb f).1) k1 ρE hI e' hl
        refine ⟨k1, t1, ?_, (fun h => by cases h), (fun h => by simp [pfOf] at h)⟩
        simp [SirZC.co, sem2, ← hx]
        rw [← hx] at hin
        exact neg_eq x hin
      · intro ρE es he; cases es <;> simp [trs] at he
  case cmpV ρ o a b ra rb x y h1 h2 h3 h4 iha ihb =>
      constructor
      · intro ρE e he hl hv hI
        cases e <;> simp [tr] at he
        rename_i c l r'
        obtain ⟨ho, hla, hrb⟩ := he
        subst ho; subst hla; subst hrb
        obtain ⟨k1, t1, c1, _⟩ := iha.1 ρE l rfl hl.1 (fun i hi => hv i (by simp [E.maxVar]; omega)) hI
        obtain ⟨k2, t2, c2, _⟩ := ihb.1 ρE r' rfl hl.2 (fun i hi => hv i (by simp [E.maxVar]; omega)) hI
        obtain ⟨a1, a2, a3, b1, b2, b3⟩ := lift2 body ρE l r' k1 k2 t1 t2
        have hx : x = sem2 (ΦF body k1) ρE l := by rw [c1] at h2; exact (Option.some.inj h2).symm
        have hy : y = sem2 (ΦF body k2) ρE r' := by rw [c2] at h4; exact (Option.some.inj h4).symm
        subst hx; subst hy
        refine ⟨max k1 k2, ⟨a1, b1⟩, ?_, ?_, (fun h => by simp [pfOf] at h)⟩
        · rw [sem2, a2, b2]
          cases hx : sem2 (ΦF body k1) ρE l with
          | none => simp [SirZC.co, cmpSem]
          | some p =>
            cases hy : sem2 (ΦF body k2) ρE r' with
            | none => simp [SirZC.co, cmpSem]
            | some q =>
              by_cases hh : c.holds p q = true
              · simp [SirZC.co, cmpSem, cmp_eq, hh, SirZC.selLeft]
              · simp [SirZC.co, cmpSem, cmp_eq, hh, SirZC.selLeft]
        · intro h
          cases hx : sem2 (ΦF body k1) ρE l with
          | none => simp [hx] at h
          | some p =>
            cases hy : sem2 (ΦF body k2) ρE r' with
            | none => simp [hx, hy] at h
            | some q =>
              by_cases hh : c.holds p q = true
              · simp [hx, hy, cmp_eq, hh] at h
              · simp [hx, hy, cmp_eq, hh] at h
      · intro ρE es he; cases es <;> simp [trs] at he
  case acons ρ a r' x l h1 h2 iha ihr =>
      constructor
      · intro ρE e he; cases e <;> simp [tr] at he
      · intro ρE es he hl hv hI
        cases es with
        | nil => simp [trs] at he
        | cons a0 as =>
          simp [trs] at he
          obtain ⟨hA, hR⟩ := he
          subst hA; subst hR
          obtain ⟨k1, t1, c1, pf1, pf1'⟩ := iha.1 ρE a0 rfl (hl a0 (by simp)) (hv a0 (by simp)) hI
          obtain ⟨k2, t2, hr⟩ := ihr.2 ρE as rfl (fun b hb => hl b (by simp [hb])) (fun b hb => hv b (by simp [hb])) hI
          have hx : x = sem2 (ΦF body k1) ρE a0 := by simp [SirZC.co] at c1; exact c1
          have hnp : ¬ pfOf (ΦF body k1) ρE a0 := fun hp => by have := pf1' hp; cases this
          obtain ⟨a1, a2, a3⟩ := termG_fuel_mono body (Nat.le_max_left k1 k2) ρE a0 t1
          refine ⟨max k1 k2, ?_, ?_⟩
          · intro b hb
            simp at hb
            cases hb with
            | inl hb => subst hb; exact ⟨a1, fun hp => hnp (a3.1 hp)⟩
            | inr hb =>
              obtain ⟨b1, b2, b3⟩ := termG_fuel_mono body (Nat.le_max_right k1 k2) ρE b (t2 b hb).1
              exact ⟨b1, fun hp => (t2 b hb).2 (b3.1 hp)⟩
          · have : as.map (sem2 (ΦF body (max k1 k2)) ρE) = as.map (sem2 (ΦF body k2) ρE) := by
              apply List.map_congr_left
              intro b hb
              exact (termG_fuel_mono body (Nat.le_max_right k1 k2) ρE b (t2 b hb).1).2.1
            simp only [List.map_cons, this, a2, ← hx]
            simp at hr
            rw [hr]
  case callPF ρ f as l k bd h1 h2 h3 h4 ih1 =>
      constructor
      · intro ρE e he hl hv hI
        cases e <;> simp [tr] at he
        · rename_i f' a0
          obtain ⟨rfl, rfl⟩ := he
          obtain ⟨k1, tt, hl'⟩ := ih1.2 ρE [a0] (by simp [trs]) (by intro b hb; simp at hb; subst hb; exact hl) (by intro b hb i hi; simp at hb; subst hb; exact hv i (by simp [E.maxVar]; omega)) hI
          have hl'' : l = [sem2 (ΦF body k1) ρE a0] := by simpa using hl'
          subst hl''
          have hn : sem2 (ΦF body k1) ρE a0 = none := by simpa using h4
          refine ⟨k1, ⟨(tt a0 (by simp)).1, (tt a0 (by simp)).2, fun hall => ?_⟩, ?_, fun _ => hn, fun _ => rfl⟩
          · exfalso; have := hall (sem2 (ΦF body k1) ρE a0) (by simp); rw [hn] at this; obtain ⟨z, hz⟩ := this; cases hz
          · simp [SirZC.co, sem2, callSem, hn]
        · rename_i f' a0 b0
          obtain ⟨rfl, rfl⟩ := he
          obtain ⟨k1, tt, hl'⟩ := ih1.2 ρE [a0, b0] (by simp [trs]) (by intro b hb; simp at hb; cases hb with | inl hb => subst hb; exact hl.1 | inr hb => subst hb; exact hl.2) (by
            intro b hb i hi; simp at hb
            cases hb with
            | inl hb => subst hb; exact hv i (by simp [E.maxVar]; omega)
            | inr hb => subst hb; exact hv i (by simp [E.maxVar]; omega)) hI
          have hl'' : l = [sem2 (ΦF body k1) ρE a0, sem2 (ΦF body k1) ρE b0] := by simpa using hl'
          subst hl''
          have hn : sem2 (ΦF body k1) ρE a0 = none ∨ sem2 (ΦF body k1) ρE b0 = none := by simpa using h4
          refine ⟨k1, ⟨(tt a0 (by simp)).1, (tt b0 (by simp)).1, (tt a0 (by simp)).2, (tt b0 (by simp)).2, fun hall => ?_⟩, ?_, fun _ => hn, fun _ => rfl⟩
          · exfalso
            cases hn with
            | inl h => have := hall (sem2 (ΦF body k1) ρE a0) (by simp); rw [h] at this; obtain ⟨z, hz⟩ := this; cases hz
            | inr h => have := hall (sem2 (ΦF body k1) ρE b0) (by simp); rw [h] at this; obtain ⟨z, hz⟩ := this; cases hz
          · cases hn with
            | inl h => simp [SirZC.co, sem2, callSem, h]
            | inr h => simp [SirZC.co, sem2, callSem, h]
      · intro ρE es he; cases es <;> simp [trs] at he
  case callRun ρ f as l k bd rb h1 h2 h3 h4 h5 ih1 ih5 =>
      constructor
      · intro ρE e he hl hv hI
        have hbd : k = ar f ∧ bd = tr (body f) := by
          simp [fsOf] at h2
          exact ⟨h2.1.symm, h2.2.symm⟩
        obtain ⟨hk, hbd⟩ := hbd
        subst hbd
        cases e <;> simp [tr] at he
        · rename_i f' a0
          obtain ⟨rfl, rfl⟩ := he
          obtain ⟨k1, tt, hl'⟩ := ih1.2 ρE [a0] (by simp [trs]) (by intro b hb; simp at hb; subst hb; exact hl)
            (by intro b hb i hi; simp at hb; subst hb; exact hv i (by simp [E.maxVar]; omega)) hI
          have hl'' : l = [sem2 (ΦF body k1) ρE a0] := by simpa using hl'
          subst hl''
          have hin := InR_of_sem2 body (fun f => (hb f).1) k1 ρE hI a0 hl
          obtain ⟨z, hz⟩ : ∃ z, sem2 (ΦF body k1) ρE a0 = some z := by
            cases hh : sem2 (ΦF body k1) ρE a0 with
            | none => simp [hh] at h4
            | some z => exact ⟨z, rfl⟩
          have hall : ∀ v ∈ [sem2 (ΦF body k1) ρE a0], ∃ z, v = some z := by
            intro v hv'; simp at hv'; subst hv'; exact ⟨z, hz⟩
          obtain ⟨k2, t2, c2, _⟩ := ih5.1 (envOf [sem2 (ΦF body k1) ρE a0]) (body f') rfl (hb f').1
            (fun i hi => getD_envOf _ hall i (by have := (hb f').2.2; have h3' := h3; rw [hk] at h3'; omega))
            (envOf_inR_gen _ (by intro v hv'; simp at hv'; subst hv'; exact hin))
          have hD : DomG body (k2 + 1) f' [sem2 (ΦF body k1) ρE a0] := t2
          obtain ⟨d1, d2⟩ := DomG_mono_le body (Nat.le_max_right k1 (k2 + 1)) f' _ hD
          obtain ⟨a1, a2, a3⟩ := termG_fuel_mono body (Nat.le_max_left k1 (k2 + 1)) ρE a0 (tt a0 (by simp)).1
          have hnp := (tt a0 (by simp)).2
          refine ⟨max k1 (k2 + 1), ⟨a1, fun hp => hnp (a3.1 hp), fun _ => ?_⟩, ?_, fun h => absurd h (dePF_ne_pf _), fun hp => ?_⟩
          · rw [a2]; exact d1
          · rw [co_dePF, c2]
            simp [sem2, callSem, a2, hz]
            have := d2
            simpa [ΦF, hz] using this.symm
          · exfalso
            simp [pfOf, a2, hz] at hp
        · rename_i f' a0 b0
          obtain ⟨rfl, rfl⟩ := he
          obtain ⟨k1, tt, hl'⟩ := ih1.2 ρE [a0, b0] (by simp [trs])
            (by intro b hb; simp at hb; cases hb with | inl hb => subst hb; exact hl.1 | inr hb => subst hb; exact hl.2)
            (by
              intro b hb i hi; simp at hb
              cases hb with
              | inl hb => subst hb; exact hv i (by simp [E.maxVar]; omega)
              | inr hb => subst hb; exact hv i (by simp [E.maxVar]; omega)) hI
          have hl'' : l = [sem2 (ΦF body k1) ρE a0, sem2 (ΦF body k1) ρE b0] := by simpa using hl'
          subst hl''
          have hina := InR_of_sem2 body (fun f => (hb f).1) k1 ρE hI a0 hl.1
          have hinb := InR_of_sem2 body (fun f => (hb f).1) k1 ρE hI b0 hl.2
          obtain ⟨z1, hz1⟩ : ∃ z, sem2 (ΦF body k1) ρE a0 = some z := by
            cases hh : sem2 (ΦF body k1) ρE a0 with
            | none => simp [hh] at h4
            | some z => exact ⟨z, rfl⟩
          obtain ⟨z2, hz2⟩ : ∃ z, sem2 (ΦF body k1) ρE b0 = some z := by
            cases hh : sem2 (ΦF body k1) ρE b0 with
            | none => simp [hh] at h4
            | some z => exact ⟨z, rfl⟩
          have hall : ∀ v ∈ [sem2 (ΦF body k1) ρE a0, sem2 (ΦF body k1) ρE b0], ∃ z, v = some z := by
            intro v hv'; simp at hv'
            cases hv' with
            | inl h => subst h; exact ⟨z1, hz1⟩
            | inr h => subst h; exact ⟨z2, hz2⟩
          obtain ⟨k2, t2, c2, _⟩ := ih5.1 (envOf [sem2 (ΦF body k1) ρE a0, sem2 (ΦF body k1) ρE b0]) (body f') rfl (hb f').1
            (fun i hi => getD_envOf _ hall i (by have := (hb f').2.2; have h3' := h3; rw [hk] at h3'; omega))
            (envOf_inR_gen _ (by
              intro v hv'; simp at hv'
              cases hv' with
              | inl h => subst h; exact hina
              | inr h => subst h; exact hinb))
          have hD : DomG body (k2 + 1) f' [sem2 (ΦF body k1) ρE a0, sem2 (ΦF body k1) ρE b0] := t2
          obtain ⟨d1, d2⟩ := DomG_mono_le body (Nat.le_max_right k1 (k2 + 1)) f' _ hD
          obtain ⟨a1, a2, a3⟩ := termG_fuel_mono body (Nat.le_max_left k1 (k2 + 1)) ρE a0 (tt a0 (by simp)).1
          obtain ⟨b1, b2, b3⟩ := termG_fuel_mono body (Nat.le_max_left k1 (k2 + 1)) ρE b0 (tt b0 (by simp)).1
          have hnp := (tt a0 (by simp)).2
          have hnq := (tt b0 (by simp)).2
          refine ⟨max k1 (k2 + 1), ⟨a1, b1, fun hp => hnp (a3.1 hp), fun hp => hnq (b3.1 hp), fun _ => ?_⟩, ?_,
            fun h => absurd h (dePF_ne_pf _), fun hp => ?_⟩
          · rw [a2, b2]; exact d1
          · rw [co_dePF, c2]
            simp [sem2, callSem, a2, b2, hz1, hz2]
            have := d2
            simpa [ΦF, hz1, hz2] using this.symm
          · exfalso
            simp [pfOf, a2, b2, hz1, hz2] at hp
      · intro ρE es he; cases es <;> simp [trs] at he

/-- 評価器の規則 `Ev` から `ΦF` の側へ: 呼びの本体が `Ev` で値に評価されるなら、ある燃料で止まり(`DomG`)、同じ値 -/
theorem limit_complete (ar : Nat → Nat) (body : Nat → E)
    (hb : ∀ f, (body f).lits2 ∧ (body f).arOk ar ∧ (body f).maxVar ≤ ar f)
    (f : Nat) (l : List (Option Int)) (rb : SirZC.Res) (hlen : l.length = ar f)
    (hall : ∀ v ∈ l, ∃ z, v = some z) (hin : ∀ v ∈ l, InR v)
    (h : SirZC.Ev (fsOf ar body) SirZC.selLeft (fun i => l.getD i none) (tr (body f)) rb) :
    ∃ k, DomG body (k + 1) f l ∧ SirZC.co rb = some (ΦF body (k + 1) f l) := by
  obtain ⟨k, t, c, _⟩ := (complete_aux ar body hb h).1 (envOf l) (body f) rfl (hb f).1
    (fun i hi => getD_envOf l hall i (by have := (hb f).2.2; omega)) (envOf_inR_gen l hin)
  exact ⟨k, t, c⟩

/-- `ΦF` の極限と評価器の意味の一致: ある燃料で止まって `x` になることと、評価器の規則 `Ev` が `x` を導くこと -/
theorem limit_iff (ar : Nat → Nat) (body : Nat → E)
    (hb : ∀ f, (body f).lits2 ∧ (body f).arOk ar ∧ (body f).maxVar ≤ ar f)
    (f : Nat) (l : List (Option Int)) (x : Option Int) (hlen : l.length = ar f)
    (hall : ∀ v ∈ l, ∃ z, v = some z) (hin : ∀ v ∈ l, InR v) :
    (∃ k, DomG body k f l ∧ ΦF body k f l = x) ↔
      ∃ rb, SirZC.Ev (fsOf ar body) SirZC.selLeft (fun i => l.getD i none) (tr (body f)) rb ∧ SirZC.co rb = some x := by
  constructor
  · rintro ⟨k, hD, hx⟩
    obtain ⟨rb, hr, hc⟩ := limit_sound ar body hb k f l hD hlen hall hin
    exact ⟨rb, hr, by rw [hc, hx]⟩
  · rintro ⟨rb, hr, hc⟩
    obtain ⟨k, hD, hc'⟩ := limit_complete ar body hb f l rb hlen hall hin hr
    refine ⟨k + 1, hD, ?_⟩
    rw [hc] at hc'; exact (Option.some.inj hc').symm

theorem termG_term (Φ : Nat → List (Option Int) → Option Int) (Dom Dom' : Nat → List (Option Int) → Prop)
    (H : ∀ f vs, Dom f vs → Dom' f vs) (ρ : Nat → Option Int) :
    ∀ e : E, TermG Φ Dom ρ e → Term Φ Dom' ρ e := by
  intro e
  induction e with
  | lit n => intro _; trivial
  | var k => intro _; trivial
  | neg e ih => intro h; exact ih h
  | op o l r ihl ihr => intro h; exact ⟨ihl h.1, ihr h.2⟩
  | cmp c l r ihl ihr => intro h; exact ⟨ihl h.1, ihr h.2⟩
  | call1 f a ih => intro h; exact ⟨ih h.1, fun hs => H _ _ (h.2.2 hs)⟩
  | call2 f a b iha ihb => intro h; exact ⟨iha h.1, ihb h.2.1, fun hs => H _ _ (h.2.2.2.2 hs)⟩

/-- `DomG`(評価器と合う止まる条件)は `DomF`(コード生成の保存に使う止まる条件)を含む -/
theorem DomG_DomF (body : Nat → E) : ∀ k f vs, DomG body k f vs → DomF body k f vs := by
  intro k
  induction k with
  | zero => intro f vs h; exact h
  | succ k ih => intro f vs h; exact termG_term _ _ _ ih _ (body f) h


/-! ### ループ関数(自分への末尾呼び)の `LΦ` と評価器 -/

/-- 条件の式の木の写し -/
def trc : Cn → SirZC.T
  | .val e => tr e
  | .and a b => .and (trc a) (trc b)
  | .or a b => .or (trc a) (trc b)

/-- ループ関数の本体の項: `c : v` の行、既定の行 `self(as..)`、(全部外れたら)`!_` -/
def loopT (self : Nat) (c : Cn) (v : E) (as : List E) : SirZC.T :=
  .rowC (trc c) (tr v) (.rowD (.call self (trs as)) .void)

theorem arOk_of_lits (ar : Nat → Nat) : ∀ e : E, e.lits → e.arOk ar
  | .lit _, _ => trivial
  | .var _, _ => trivial
  | .op _ l r, h => ⟨arOk_of_lits ar l h.1, arOk_of_lits ar r h.2⟩
  | .neg e, h => arOk_of_lits ar e h
  | .cmp _ l r, h => ⟨arOk_of_lits ar l h.1, arOk_of_lits ar r h.2⟩
  | .call1 _ _, h => h.elim
  | .call2 _ _ _, h => h.elim

theorem termG_of_lits (Φ : Nat → List (Option Int) → Option Int) (Dom : Nat → List (Option Int) → Prop) (ρ : Nat → Option Int) :
    ∀ e : E, e.lits → TermG Φ Dom ρ e
  | .lit _, _ => trivial
  | .var _, _ => trivial
  | .op _ l r, h => ⟨termG_of_lits Φ Dom ρ l h.1, termG_of_lits Φ Dom ρ r h.2⟩
  | .neg e, h => termG_of_lits Φ Dom ρ e h
  | .cmp _ l r, h => ⟨termG_of_lits Φ Dom ρ l h.1, termG_of_lits Φ Dom ρ r h.2⟩
  | .call1 _ _, h => h.elim
  | .call2 _ _ _, h => h.elim

theorem sem2_of_lits (Φ : Nat → List (Option Int) → Option Int) (ρ : Nat → Option Int) :
    ∀ e : E, e.lits → sem2 Φ ρ e = sem ρ e
  | .lit _, _ => rfl
  | .var _, _ => rfl
  | .op o l r, h => by simp [sem2, sem, sem2_of_lits Φ ρ l h.1, sem2_of_lits Φ ρ r h.2]
  | .neg e, h => by simp [sem2, sem, sem2_of_lits Φ ρ e h]
  | .cmp c l r, h => by simp [sem2, sem, sem2_of_lits Φ ρ l h.1, sem2_of_lits Φ ρ r h.2]
  | .call1 _ _, h => h.elim
  | .call2 _ _ _, h => h.elim

theorem not_pfOf_lits (Φ : Nat → List (Option Int) → Option Int) (ρ : Nat → Option Int) :
    ∀ e : E, e.lits → ¬ pfOf Φ ρ e
  | .lit _, _ => by simp [pfOf]
  | .var _, _ => by simp [pfOf]
  | .op _ _ _, _ => by simp [pfOf]
  | .neg _, _ => by simp [pfOf]
  | .cmp _ _ _, _ => by simp [pfOf]
  | .call1 _ _, h => h.elim
  | .call2 _ _ _, h => h.elim

/-- 条件の木は評価器で、成り立てば `some _`、成り立たなければ `none`(`pf` にはならない)になる -/
theorem trc_ev (ar : Nat → Nat) (fs : SirZC.Fs) (bd : Nat → SirZC.T) (hfs : ∀ f, fs f = some (ar f, bd f))
    (Φ : Nat → List (Option Int) → Option Int) (Dom : Nat → List (Option Int) → Prop)
    (hΦ : ∀ f vs, (∀ v ∈ vs, InR v) → InR (Φ f vs))
    (HΦ : ∀ f vs, Dom f vs → vs.length = ar f → (∀ v ∈ vs, ∃ z, v = some z) → (∀ v ∈ vs, InR v) →
      ∃ rb, SirZC.Ev fs SirZC.selLeft (fun i => vs.getD i none) (bd f) rb ∧ SirZC.co rb = some (Φ f vs))
    (ρT : SirZC.Env) (ρE : Nat → Option Int) (hρ : ∀ i, InR (ρE i)) :
    ∀ c : Cn, c.lits → (∀ i < c.maxVar, ρT i = ρE i) →
      ∃ r, SirZC.Ev fs SirZC.selLeft ρT (trc c) r ∧ (ctruth ρE c = true → ∃ x, r = .v (some x)) ∧
        (ctruth ρE c = false → r = .v none) := by
  intro c
  induction c with
  | val e =>
      intro hl hv
      obtain ⟨r, hr, hc, hp⟩ := tree_sound_fs ar fs bd hfs Φ Dom hΦ HΦ ρT ρE hρ e (lits_lits2 e hl) (arOk_of_lits ar e hl)
        (by simpa [Cn.maxVar] using hv) (termG_of_lits Φ Dom ρE e hl)
      have hnp : r ≠ .pf := fun h => not_pfOf_lits Φ ρE e hl (hp h)
      have hr' : r = .v (sem2 Φ ρE e) := co_v hc hnp
      refine ⟨r, hr, ?_, ?_⟩
      · intro h
        simp [ctruth, ← sem2_of_lits Φ ρE e hl] at h
        cases hs : sem2 Φ ρE e with
        | none => simp [hs] at h
        | some x => exact ⟨x, by rw [hr', hs]⟩
      · intro h
        simp [ctruth, ← sem2_of_lits Φ ρE e hl] at h
        rw [hr', h]
  | and a b iha ihb =>
      intro hl hv
      obtain ⟨ra, hra, hta, hfa⟩ := iha hl.1 (fun i hi => hv i (by simp [Cn.maxVar]; omega))
      obtain ⟨rb, hrb, htb, hfb⟩ := ihb hl.2 (fun i hi => hv i (by simp [Cn.maxVar]; omega))
      by_cases hca : ctruth ρE a = true
      · obtain ⟨x, hx⟩ := hta hca
        subst hx
        refine ⟨rb, SirZC.Ev.andV hra hrb, ?_, ?_⟩
        · intro h; exact htb (by simpa [ctruth, hca] using h)
        · intro h; exact hfb (by simpa [ctruth, hca] using h)
      · have hca' : ctruth ρE a = false := by simpa using hca
        have := hfa hca'
        subst this
        exact ⟨_, SirZC.Ev.andN hra, fun h => by simp [ctruth, hca'] at h, fun _ => rfl⟩
  | or a b iha ihb =>
      intro hl hv
      obtain ⟨ra, hra, hta, hfa⟩ := iha hl.1 (fun i hi => hv i (by simp [Cn.maxVar]; omega))
      obtain ⟨rb, hrb, htb, hfb⟩ := ihb hl.2 (fun i hi => hv i (by simp [Cn.maxVar]; omega))
      by_cases hca : ctruth ρE a = true
      · obtain ⟨x, hx⟩ := hta hca
        subst hx
        exact ⟨_, SirZC.Ev.orV hra, fun _ => ⟨x, rfl⟩, fun h => by simp [ctruth, hca] at h⟩
      · have hca' : ctruth ρE a = false := by simpa using hca
        have := hfa hca'
        subst this
        refine ⟨rb, SirZC.Ev.orN hra hrb, ?_, ?_⟩
        · intro h; exact htb (by simpa [ctruth, hca'] using h)
        · intro h; exact hfb (by simpa [ctruth, hca'] using h)

/-- 実引数の並びの評価(引数が `pf` にならないとき) -/
theorem args_ev (ar : Nat → Nat) (fs : SirZC.Fs) (bd : Nat → SirZC.T) (hfs : ∀ f, fs f = some (ar f, bd f))
    (Φ : Nat → List (Option Int) → Option Int) (Dom : Nat → List (Option Int) → Prop)
    (hΦ : ∀ f vs, (∀ v ∈ vs, InR v) → InR (Φ f vs))
    (HΦ : ∀ f vs, Dom f vs → vs.length = ar f → (∀ v ∈ vs, ∃ z, v = some z) → (∀ v ∈ vs, InR v) →
      ∃ rb, SirZC.Ev fs SirZC.selLeft (fun i => vs.getD i none) (bd f) rb ∧ SirZC.co rb = some (Φ f vs))
    (ρT : SirZC.Env) (ρE : Nat → Option Int) (hρ : ∀ i, InR (ρE i)) (n : Nat) (hρn : ∀ i < n, ρT i = ρE i) :
    ∀ xs : List E, (∀ x ∈ xs, x.lits2 ∧ x.arOk ar ∧ x.maxVar ≤ n ∧ TermG Φ Dom ρE x ∧ ¬ pfOf Φ ρE x) →
      SirZC.Ev fs SirZC.selLeft ρT (trs xs) (.args (xs.map (sem2 Φ ρE))) := by
  intro xs
  induction xs with
  | nil => intro _; exact SirZC.Ev.anil
  | cons x xs ih =>
      intro h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h x (by simp)
      obtain ⟨r, hr, hc, hp⟩ := tree_sound_fs ar fs bd hfs Φ Dom hΦ HΦ ρT ρE hρ x h1 h2
        (fun i hi => hρn i (by omega)) h4
      have hr' : r = .v (sem2 Φ ρE x) := co_v hc (fun e => h5 (hp e))
      subst hr'
      exact SirZC.Ev.acons hr (ih (fun y hy => h y (by simp [hy])))

/-- `rowD t void`: `t` の結果が値(`some`/`none`)か `pf` なら、行全体は同じ値 -/
theorem rowD_void_ev (fs : SirZC.Fs) (sel : SirZC.Sel) (ρ : SirZC.Env) (t : SirZC.T) (r : SirZC.Res) (w : Option Int)
    (h : SirZC.Ev fs sel ρ t r) (hc : SirZC.co r = some w) :
    ∃ r2, SirZC.Ev fs sel ρ (.rowD t .void) r2 ∧ SirZC.co r2 = some w := by
  cases r with
  | v x =>
      simp [SirZC.co] at hc; subst hc
      cases x with
      | none => exact ⟨_, SirZC.Ev.rowDFallV h SirZC.Ev.void, rfl⟩
      | some y => exact ⟨_, SirZC.Ev.rowDHit h, rfl⟩
  | pf =>
      simp [SirZC.co] at hc; subst hc
      exact ⟨_, SirZC.Ev.rowDFallP h SirZC.Ev.void, rfl⟩
  | args l => simp [SirZC.co] at hc
  | unsup => simp [SirZC.co] at hc
  | fuel => simp [SirZC.co] at hc

/-- `LΦ` が止まる条件(評価器と合わせる版): 条件が成り立つ行の値は `!_` でなく(評価器は `!_` の値で次の行へ落ちる)、
実引数は `pf` にならない -/
def LDomG (Φ : Nat → List (Option Int) → Option Int) (Dom : Nat → List (Option Int) → Prop) (c : Cn) (v : E) (as : List E) :
    Nat → (Nat → Option Int) → Prop
  | 0, _ => False
  | k + 1, ρ => (ctruth ρ c = true → TermG Φ Dom ρ v ∧ sem2 Φ ρ v ≠ none) ∧
      (ctruth ρ c = false → (∀ x ∈ as, TermG Φ Dom ρ x ∧ ¬ pfOf Φ ρ x) ∧
        ((∀ x ∈ as, ∃ z, sem2 Φ ρ x = some z) → LDomG Φ Dom c v as k (envOf (as.map (sem2 Φ ρ)))))

/-- ループ関数の `LΦ` は評価器の規則 `Ev` でも同じ値(燃料 `k` の帰納法) -/
theorem loop_sound (ar : Nat → Nat) (fs : SirZC.Fs) (bd : Nat → SirZC.T) (hfs : ∀ f, fs f = some (ar f, bd f))
    (Φ : Nat → List (Option Int) → Option Int) (Dom : Nat → List (Option Int) → Prop)
    (hΦ : ∀ f vs, (∀ v ∈ vs, InR v) → InR (Φ f vs))
    (HΦ : ∀ f vs, Dom f vs → vs.length = ar f → (∀ v ∈ vs, ∃ z, v = some z) → (∀ v ∈ vs, InR v) →
      ∃ rb, SirZC.Ev fs SirZC.selLeft (fun i => vs.getD i none) (bd f) rb ∧ SirZC.co rb = some (Φ f vs))
    (self : Nat) (c : Cn) (v : E) (as : List E) (hself : bd self = loopT self c v as) (hlen : as.length = ar self)
    (hc : c.lits) (hcv : c.maxVar ≤ as.length)
    (hv : v.lits2 ∧ v.arOk ar ∧ v.maxVar ≤ as.length) (has : ∀ x ∈ as, x.lits2 ∧ x.arOk ar ∧ x.maxVar ≤ as.length) :
    ∀ k (ρE : Nat → Option Int) (ρT : SirZC.Env), (∀ i, InR (ρE i)) → (∀ i < as.length, ρT i = ρE i) →
      LDomG Φ Dom c v as k ρE →
      ∃ r, SirZC.Ev fs SirZC.selLeft ρT (loopT self c v as) r ∧ SirZC.co r = some (LΦ Φ c v as k ρE) := by
  intro k
  induction k with
  | zero => intro ρE ρT _ _ h; exact absurd h (by simp [LDomG])
  | succ k ih =>
      intro ρE ρT hρ hag hD
      obtain ⟨hT, hF⟩ := hD
      obtain ⟨rc, hrc, hct, hcf⟩ := trc_ev ar fs bd hfs Φ Dom hΦ HΦ ρT ρE hρ c hc (fun i hi => hag i (by omega))
      by_cases hctr : ctruth ρE c = true
      · obtain ⟨x, hx⟩ := hct hctr
        subst hx
        obtain ⟨hTv, hne⟩ := hT hctr
        obtain ⟨rv, hrv, hcvv, _⟩ := tree_sound_fs ar fs bd hfs Φ Dom hΦ HΦ ρT ρE hρ v hv.1 hv.2.1
          (fun i hi => hag i (by omega)) hTv
        cases hs : sem2 Φ ρE v with
        | none => exact absurd hs hne
        | some y =>
            have hrv' : rv = .v (some y) := co_v (by rw [hcvv, hs]) (by intro h; subst h; simp [SirZC.co, hs] at hcvv)
            subst hrv'
            refine ⟨_, SirZC.Ev.rowCHit hrc rfl hrv, ?_⟩
            simp [LΦ, hctr, hs, SirZC.co]
      · have hctf : ctruth ρE c = false := by simpa using hctr
        have hrc' := hcf hctf
        subst hrc'
        obtain ⟨hA, hB⟩ := hF hctf
        have hargs := args_ev ar fs bd hfs Φ Dom hΦ HΦ ρT ρE hρ as.length (fun i hi => hag i hi) as
          (fun x hx => ⟨(has x hx).1, (has x hx).2.1, (has x hx).2.2, (hA x hx).1, (hA x hx).2⟩)
        by_cases hall : ∀ x ∈ as, ∃ z, sem2 Φ ρE x = some z
        · have hD' := hB hall
          have hallv : ∀ w ∈ as.map (sem2 Φ ρE), ∃ z, w = some z := by
            intro w hw; simp at hw; obtain ⟨x, hx, rfl⟩ := hw; exact hall x hx
          have hinv : ∀ w ∈ as.map (sem2 Φ ρE), InR w := by
            intro w hw; simp at hw; obtain ⟨x, hx, rfl⟩ := hw
            exact sem2_inR Φ hΦ ρE hρ x (has x hx).1
          have hlen' : (as.map (sem2 Φ ρE)).length = ar self := by simp [hlen]
          obtain ⟨r', hr', hc'⟩ := ih (envOf (as.map (sem2 Φ ρE))) (fun i => (as.map (sem2 Φ ρE)).getD i none)
            (envOf_inR_gen _ hinv)
            (fun i hi => getD_envOf _ hallv i (by simpa using hi)) hD'
          have hbody : SirZC.Ev fs SirZC.selLeft (fun i => (as.map (sem2 Φ ρE)).getD i none) (bd self) r' := by
            rw [hself]; exact hr'
          have hcall := SirZC.Ev.callRun hargs (hfs self) hlen' (by
            simp only [List.any_eq_false]; intro w hw; obtain ⟨z, hz⟩ := hallv w hw; simp [hz]) hbody
          have hcc : SirZC.co (SirZC.dePF r') = some (LΦ Φ c v as k (envOf (as.map (sem2 Φ ρE)))) := by
            rw [co_dePF]; exact hc'
          obtain ⟨r2, hr2, hc2⟩ := rowD_void_ev fs SirZC.selLeft ρT _ _ _ hcall hcc
          refine ⟨r2, SirZC.Ev.rowCSkip hrc rfl hr2, ?_⟩
          rw [hc2]
          have hall' : (as.map (sem2 Φ ρE)).all Option.isSome = true := by
            simp only [List.all_eq_true]; intro w hw; obtain ⟨z, hz⟩ := hallv w hw; simp [hz]
          simp [LΦ, hctr, callSem, hall']
        · have hany : (as.map (sem2 Φ ρE)).any Option.isNone = true := by
            simp only [List.any_eq_true]
            refine Classical.byContradiction fun hh => ?_
            apply hall
            intro x hx
            cases hs : sem2 Φ ρE x with
            | none => exact absurd ⟨none, List.mem_map.2 ⟨x, hx, hs⟩, rfl⟩ hh
            | some z => exact ⟨z, rfl⟩
          have hlen' : (as.map (sem2 Φ ρE)).length = ar self := by simp [hlen]
          have hcall := SirZC.Ev.callPF hargs (hfs self) hlen' hany
          obtain ⟨r2, hr2, hc2⟩ := rowD_void_ev fs SirZC.selLeft ρT _ _ none hcall rfl
          refine ⟨r2, SirZC.Ev.rowCSkip hrc rfl hr2, ?_⟩
          rw [hc2]
          have hnall : (as.map (sem2 Φ ρE)).all Option.isSome = false := by
            cases h : (as.map (sem2 Φ ρE)).all Option.isSome
            · rfl
            · exfalso; apply hall; intro x hx
              have := List.all_eq_true.1 h (sem2 Φ ρE x) (List.mem_map.2 ⟨x, hx, rfl⟩)
              cases hs : sem2 Φ ρE x with
              | none => simp [hs] at this
              | some z => exact ⟨z, rfl⟩
          simp [LΦ, hctr, callSem, hnall]

#print axioms loop_sound

end SirZB

#print axioms SirZB.limit_sound
#print axioms SirZB.limit_complete
#print axioms SirZB.limit_iff
#print axioms SirZB.DomG_DomF
