import SlidingPuzzle.Hub.Basic
import SlidingPuzzle.Hub.PlanAux

/-! # The plan: rounds from a regular bipartite multigraph

`T S D` counts the reservoir tiles of `S` with class `D ≠ S`. Padding with
dummy edges (from squares that receive more than they send to squares that
send more than they receive) and loops gives a `Δ0`-regular bipartite
multigraph, which splits into `Δ0` perfect matchings (Hall/König). A round is
one of them: a permutation `perm` of the squares (`S ↦` the square `S` sends
to) with a flag marking dummy edges. -/
namespace SlidingPuzzle.Hub

/-- One perfect matching of the padded multigraph. -/
structure Round (k : ℕ) where
  perm : Equiv.Perm (Sq k)
  dummy : Sq k → Bool

namespace Round
variable {k : ℕ}

/-- `S` sends a real tile in this round (to `perm S`). -/
def real (r : Round k) (S : Sq k) : Prop := r.perm S ≠ S ∧ r.dummy S = false

/-- `S`'s edge is a dummy edge (to `perm S ≠ S`). -/
def isDummy (r : Round k) (S : Sq k) : Prop := r.perm S ≠ S ∧ r.dummy S = true

instance (r : Round k) (S : Sq k) : Decidable (r.real S) := by unfold real; infer_instance
instance (r : Round k) (S : Sq k) : Decidable (r.isDummy S) := by unfold isDummy; infer_instance

end Round

/-- Tiles a square sends. -/
def sends {k : ℕ} (T : Sq k → Sq k → ℕ) (S : Sq k) : ℕ := ∑ D, T S D

/-- Tiles a square receives. -/
def recv {k : ℕ} (T : Sq k → Sq k → ℕ) (D : Sq k) : ℕ := ∑ S, T S D

open Finset in
/-- Decomposition of `T + U` (all row and column sums `Δ`) into `Δ` rounds, the
edges counted by `T` flagged real (`dummy = false`), those of `U` flagged dummy. -/
theorem exists_decomp {k : ℕ} :
    ∀ (Δ : ℕ) (T U : Sq k → Sq k → ℕ), (∀ S, ∑ D, (T S D + U S D) = Δ) →
      (∀ D, ∑ S, (T S D + U S D) = Δ) →
      ∃ rs : Fin Δ → Round k, ∀ S D (b : Bool),
        (univ.filter fun i => (rs i).perm S = D ∧ (rs i).dummy S = b).card =
          if b then U S D else T S D
  | 0, T, U, hr, _ => by
    refine ⟨Fin.elim0, ?_⟩
    intro S D b
    have h := (Finset.sum_eq_zero_iff.1 (hr S)) D (mem_univ _)
    have hT : T S D = 0 := by omega
    have hU : U S D = 0 := by omega
    cases b <;> simp [hT, hU]
  | Δ + 1, T, U, hr, hc => by
    obtain ⟨σ, hσ⟩ := exists_perm_pos (fun S D => T S D + U S D) (Δ + 1) (by omega) hr hc
    let fl : Sq k → Bool := fun S => decide (T S (σ S) = 0)
    let T' : Sq k → Sq k → ℕ := fun S D => T S D - if σ S = D ∧ T S D ≠ 0 then 1 else 0
    let U' : Sq k → Sq k → ℕ := fun S D => U S D - if σ S = D ∧ T S D = 0 then 1 else 0
    have key : ∀ S D, T' S D + U' S D + (if σ S = D then 1 else 0) = T S D + U S D := by
      intro S D
      have := hσ S
      by_cases h : σ S = D
      · subst h
        by_cases h2 : T S (σ S) = 0
        · simp [T', U', h2]; omega
        · simp [T', U', h2]; omega
      · simp [T', U', h]
    have row : ∀ S, ∑ D, (T' S D + U' S D) = Δ := by
      intro S
      have := hr S
      rw [← Finset.sum_congr rfl (fun D (_ : D ∈ univ) => key S D), Finset.sum_add_distrib] at this
      simp at this; omega
    have col : ∀ D, ∑ S, (T' S D + U' S D) = Δ := by
      intro D
      have := hc D
      rw [← Finset.sum_congr rfl (fun S (_ : S ∈ univ) => key S D), Finset.sum_add_distrib] at this
      simp [← Equiv.eq_symm_apply] at this; omega
    obtain ⟨rs', h'⟩ := exists_decomp Δ T' U' row col
    refine ⟨Fin.cons (α := fun _ => Round k) ⟨σ, fl⟩ rs', ?_⟩
    intro S D b
    rw [Fin.card_filter_univ_succ']
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [h' S D b]
    have := hσ S
    by_cases h : σ S = D
    · subst h
      by_cases h2 : T S (σ S) = 0
      · cases b <;> simp [fl, T', U', h2]
        all_goals omega
      · cases b <;> simp [fl, T', U', h2]
        all_goals omega
    · cases b <;> simp [T', U', h]

/-- König decomposition of the padded demand multigraph. -/
theorem exists_rounds {k : ℕ} (T : Sq k → Sq k → ℕ) (hT : ∀ S, T S S = 0) :
    ∃ (Δ0 : ℕ) (rs : Fin Δ0 → Round k),
      (∀ S D, (Finset.univ.filter fun i => (rs i).perm S = D ∧ (rs i).real S).card = T S D) ∧
      (∀ S, (Finset.univ.filter fun i => (rs i).isDummy S).card = recv T S - sends T S) ∧
      (∀ S, (Finset.univ.filter fun i => (rs i).perm S = S).card =
        Δ0 - max (sends T S) (recv T S)) ∧
      (∀ S, max (sends T S) (recv T S) ≤ Δ0) ∧
      (∀ M, (∀ S, sends T S ≤ M ∧ recv T S ≤ M) → Δ0 ≤ M) := by
  classical
  set a : Sq k → ℕ := fun S => recv T S - sends T S with ha
  set b : Sq k → ℕ := fun S => sends T S - recv T S with hb
  have hsr : ∑ S, sends T S = ∑ S, recv T S := by
    unfold sends recv; exact Finset.sum_comm
  have hab : ∑ S, a S = ∑ S, b S := by
    have h1 : ∀ S, a S + sends T S = b S + recv T S := fun S => by simp only [ha, hb]; omega
    have := Finset.sum_congr rfl (fun S (_ : S ∈ Finset.univ) => h1 S)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsr] at this
    omega
  obtain ⟨X, hXr, hXc, hXs⟩ := exists_transport _ a b rfl hab.symm
  have hXd : ∀ S, X S S = 0 := by
    intro S; by_contra h
    obtain ⟨h1, h2⟩ := hXs S S h
    simp only [ha, hb] at h1 h2; omega
  set Δ0 := Finset.univ.sup fun S => max (sends T S) (recv T S) with hΔ0
  have hle : ∀ S, max (sends T S) (recv T S) ≤ Δ0 := fun S =>
    Finset.le_sup (f := fun S => max (sends T S) (recv T S)) (Finset.mem_univ S)
  let L : Sq k → Sq k → ℕ := fun S D => if S = D then Δ0 - max (sends T S) (recv T S) else 0
  have row : ∀ S, ∑ D, (T S D + (X S D + L S D)) = Δ0 := by
    intro S
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hXr]
    have := hle S
    simp only [L, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    change sends T S + (a S + _) = _
    simp only [ha]; omega
  have col : ∀ D, ∑ S, (T S D + (X S D + L S D)) = Δ0 := by
    intro D
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hXc]
    have := hle D
    simp only [L, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    change recv T D + (b D + _) = _
    simp only [hb]; omega
  obtain ⟨rs, hrs⟩ := exists_decomp Δ0 T (fun S D => X S D + L S D) row col
  refine ⟨Δ0, rs, ?_, ?_, ?_, hle, ?_⟩
  · intro S D
    by_cases hSD : S = D
    · subst hSD
      rw [hT S, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ h
      exact h.2.1 h.1
    · have h0 := hrs S D false
      simp only [Bool.false_eq_true, if_false] at h0
      rw [← h0]
      congr 1
      apply Finset.filter_congr
      intro i _
      simp only [Round.real]
      constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, by rw [h1]; exact Ne.symm hSD, h3⟩
  · intro S
    rw [Finset.card_eq_sum_card_fiberwise (f := fun i => (rs i).perm S) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    rw [show recv T S - sends T S = a S from rfl, ← hXr S]
    apply Finset.sum_congr rfl
    intro D _
    rw [Finset.filter_filter]
    by_cases hSD : S = D
    · subst hSD
      rw [hXd S, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ h
      exact h.1.1 h.2
    · have := hrs S D true
      simp only [if_true, L, hSD, if_false, add_zero] at this
      rw [← this]
      congr 1
      apply Finset.filter_congr
      intro i _
      simp only [Round.isDummy]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨by rw [h1]; exact Ne.symm hSD, h2⟩, h1⟩
  · intro S
    have h0 := hrs S S false
    have h1 := hrs S S true
    simp only [hT S, hXd S, L, if_true, zero_add, Bool.false_eq_true, if_false] at h0 h1
    rw [← Finset.card_filter_add_card_filter_not (p := fun i => (rs i).dummy S = true),
      Finset.filter_filter, Finset.filter_filter, ← h1]
    simp only [Bool.not_eq_true] at h0 ⊢
    rw [h0]; simp
  · intro M hM
    exact Finset.sup_le fun S _ => max_le (hM S).1 (hM S).2

end SlidingPuzzle.Hub
