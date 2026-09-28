import SlidingPuzzle.Hub.RunInner

/-! # The initial ghost state and the plan's rounds

Indexing of the König rounds (`rsN`: set-aside rounds `j < Q'`, plan rounds
`Q' + i`, run in the order `σo`), per-round counting facts, and the invariants
of the initial ghost state `G0`. -/
namespace SlidingPuzzle.Hub

open Finset

variable {k : ℕ}

/-- A round with only loops. -/
def idleRound : Round k := ⟨Equiv.refl _, fun _ => false⟩

/-- The rounds indexed by `ℕ` (idle beyond `Δ0`). -/
def rsN {Δ0 : ℕ} (rs0 : Fin Δ0 → Round k) (j : ℕ) : Round k :=
  if h : j < Δ0 then rs0 ⟨j, h⟩ else idleRound

/-- The plan rounds: the rounds after the first `Q'`. -/
def planRs {Δ0 : ℕ} (rs0 : Fin Δ0 → Round k) (Q' : ℕ) (i : Fin (Δ0 - Q')) : Round k :=
  rs0 ⟨Q' + i, by omega⟩

/-- The plan rounds in execution order. -/
def ordRd {Δ0 : ℕ} (rs0 : Fin Δ0 → Round k) (Q' : ℕ) (σo : Equiv.Perm (Fin (Δ0 - Q')))
    (τ : ℕ) : Round k :=
  if h : τ < Δ0 - Q' then planRs rs0 Q' (σo ⟨τ, h⟩) else idleRound

section index

variable {Δ0 : ℕ} (rs0 : Fin Δ0 → Round k)

theorem sum_rsN (f : Round k → ℕ) :
    ∑ j ∈ range Δ0, f (rsN rs0 j) = ∑ j : Fin Δ0, f (rs0 j) := by
  rw [← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun j _ => ?_
  simp [rsN, j.isLt]

theorem sum_rsN_split (f : Round k → ℕ) {Q' : ℕ} (hQ : Q' ≤ Δ0) :
    ∑ j ∈ range Δ0, f (rsN rs0 j) =
      (∑ j ∈ range Q', f (rsN rs0 j)) + ∑ i ∈ range (Δ0 - Q'), f (rsN rs0 (Q' + i)) := by
  have := Finset.sum_range_add (fun j => f (rsN rs0 j)) Q' (Δ0 - Q')
  rw [Nat.add_sub_cancel' hQ] at this
  exact this

theorem sum_ordRd (f : Round k → ℕ) (Q' : ℕ) (σo : Equiv.Perm (Fin (Δ0 - Q'))) :
    ∑ τ ∈ range (Δ0 - Q'), f (ordRd rs0 Q' σo τ) =
      ∑ i ∈ range (Δ0 - Q'), f (rsN rs0 (Q' + i)) := by
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  have h1 : ∀ i : Fin (Δ0 - Q'), f (ordRd rs0 Q' σo i) = f (planRs rs0 Q' (σo i)) := by
    intro i; simp [ordRd, i.isLt]
  have h2 : ∀ i : Fin (Δ0 - Q'), f (rsN rs0 (Q' + i)) = f (planRs rs0 Q' i) := by
    intro i; simp [rsN, planRs, show Q' + i < Δ0 by omega]
  simp only [h1, h2]
  exact Equiv.sum_comp σo (fun i => f (planRs rs0 Q' i))

end index

section round

theorem ind_self (r : Round k) (S : Sq k) : ind r S S = 0 := by
  unfold ind Round.real; simp only [ite_eq_right_iff, one_ne_zero]; tauto

/-- Each square is real, dummy or idle in a round. -/
theorem trichotomy (r : Round k) (S : Sq k) :
    (if r.real S then 1 else 0) + dummyAt r S + (if r.perm S = S then 1 else 0) = 1 := by
  unfold dummyAt Round.real Round.isDummy
  by_cases h : r.perm S = S
  · simp [h]
  · rcases Bool.eq_false_or_eq_true (r.dummy S) with hd | hd <;> simp [h, hd]

end round

/-! ## The initial ghost state -/

/-- The initial ghost state. -/
def G0 (σ0 : IState k) (sched0 free0 : Sq k → Sq k → ℕ) : GS k where
  σ := σ0
  evs := []
  ins := []
  sched := sched0
  stock := fun _ _ => 0
  free := free0
  out := fun _ _ => 0
  byp := fun _ _ => 0
  served := fun _ => 0
  sent := fun _ => 0
  wt := 0
  dd := fun _ => 0

section init

variable (s : ℕ) (σ0 : IState k) (sched0 free0 : Sq k → Sq k → ℕ)

theorem gh_G0 : gh s (G0 σ0 sched0 free0) = fun _ _ => none := rfl

theorem hubCnt_none (P : Option (Sq k × ℕ) → Prop) [DecidablePred P] (h : Sq k) (hP : ¬ P none) :
    hubCnt s (fun _ _ => none) P h = 0 := by
  unfold hubCnt; simp [hP]

theorem noneCnt_none (h : Sq k) :
    noneCnt s (fun _ _ => none) h = (k - 1) * s := by
  unfold noneCnt hubCnt
  have := rowLen_pair (s := s) h.1 h.2
  simp [this]

theorem G0_linv (hle : ∀ Q y, sched0 Q y + free0 Q y ≤ σ0.cnt Q y)
    (hge : ∀ Q y, y ≠ Q → σ0.cnt Q y ≤ sched0 Q y + free0 Q y)
    (hdf : ∀ Q y, σ0.dcnt Q y ≤ free0 Q y) :
    LInv s σ0 ((∑ Q, ∑ y, free0 Q y) + junkCnt s σ0) (G0 σ0 sched0 free0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, le_refl _, rfl, trivial, hdf⟩
  · intro Q y; have := hle Q y; simp only [G0]; omega
  · intro Q y hy; have := hge Q y hy; simp only [G0]; omega
  · intro h x hx; exact absurd rfl hx
  · intro H q x d hg; simp [gh_G0] at hg
  · intro h; rw [gh_G0, noneCnt_none]; simp [G0]

theorem G0_hinv (free0t : Sq k → ℕ) (hf : ∀ Z, free0t Z = ∑ y, free0 Z y)
    (N : Sq k → Sq k → ℕ) :
    HInv s σ0 free0t N (∑ S, ∑ D, sched0 S D) (G0 σ0 sched0 free0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h x _
    rw [gh_G0, newCnt_eq_hubCnt, hubCnt_none s _ h (by simp)]
    simp [G0]
  · intro h x; simp [G0]
  · intro Z; rw [hf Z]; simp [G0]; split_ifs <;> simp_all
  · simp [G0, IState.totalCost]
  · simp [G0]

end init

end SlidingPuzzle.Hub
