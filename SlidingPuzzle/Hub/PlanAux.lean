import Mathlib

/-! # Combinatorial tools for the plan: Hall for regular matrices, transportation -/
namespace SlidingPuzzle.Hub

open Finset

/-- A nonnegative integer matrix with all row sums `Δ > 0` and all column sums `Δ`
has a permutation in its support (Hall's theorem). -/
theorem exists_perm_pos {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ι → ι → ℕ) (Δ : ℕ)
    (hΔ : 0 < Δ) (hrow : ∀ S, ∑ D, M S D = Δ) (hcol : ∀ D, ∑ S, M S D = Δ) :
    ∃ σ : Equiv.Perm ι, ∀ S, 0 < M S (σ S) := by
  let t : ι → Finset ι := fun S => univ.filter (fun D => 0 < M S D)
  have hall : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card := by
    intro s
    have h1 : ∑ S ∈ s, ∑ D ∈ s.biUnion t, M S D = Δ * s.card := by
      rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro S hS
      rw [← hrow S]
      apply Finset.sum_subset (subset_univ _)
      intro D _ hD
      by_contra h
      exact hD (mem_biUnion.2 ⟨S, hS, by simp [t]; omega⟩)
    have h2 : ∑ S ∈ s, ∑ D ∈ s.biUnion t, M S D ≤ Δ * (s.biUnion t).card := by
      rw [Finset.sum_comm]
      calc _ ≤ ∑ D ∈ s.biUnion t, ∑ S, M S D :=
            sum_le_sum fun D _ => sum_le_sum_of_subset (subset_univ _)
        _ = _ := by simp [hcol, mul_comm]
    exact Nat.le_of_mul_le_mul_left (h1 ▸ h2) hΔ
  obtain ⟨f, hf, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  refine ⟨Equiv.ofBijective f hf.bijective_of_finite, fun S => ?_⟩
  have := hft S
  simpa [t] using this

/-- Transportation: row sums `a`, column sums `b` (equal totals), supported where
`a` and `b` are nonzero. -/
theorem exists_transport {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∀ (n : ℕ) (a b : ι → ℕ), ∑ i, a i = n → ∑ i, b i = n →
      ∃ X : ι → ι → ℕ, (∀ S, ∑ D, X S D = a S) ∧ (∀ D, ∑ S, X S D = b D) ∧
        (∀ S D, X S D ≠ 0 → a S ≠ 0 ∧ b D ≠ 0)
  | 0, a, b, ha, hb => by
    have ha0 : ∀ i, a i = 0 := fun i => (Finset.sum_eq_zero_iff.1 ha) i (mem_univ _)
    have hb0 : ∀ i, b i = 0 := fun i => (Finset.sum_eq_zero_iff.1 hb) i (mem_univ _)
    exact ⟨fun _ _ => 0, by simp [ha0], by simp [hb0], by simp⟩
  | n + 1, a, b, ha, hb => by
    obtain ⟨S, -, hS⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := univ) (f := a) (by omega)
    obtain ⟨D, -, hD⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := univ) (f := b) (by omega)
    let a' : ι → ℕ := fun i => a i - if i = S then 1 else 0
    let b' : ι → ℕ := fun i => b i - if i = D then 1 else 0
    have ha' : ∀ i, a' i + (if i = S then 1 else 0) = a i := by
      intro i; by_cases h : i = S
      · subst h; simp [a']; omega
      · simp [a', h]
    have hb' : ∀ i, b' i + (if i = D then 1 else 0) = b i := by
      intro i; by_cases h : i = D
      · subst h; simp [b']; omega
      · simp [b', h]
    have hsa : ∑ i, a' i = n := by
      have := Finset.sum_congr rfl (fun i (_ : i ∈ univ) => ha' i)
      rw [Finset.sum_add_distrib, ha] at this
      simp at this; omega
    have hsb : ∑ i, b' i = n := by
      have := Finset.sum_congr rfl (fun i (_ : i ∈ univ) => hb' i)
      rw [Finset.sum_add_distrib, hb] at this
      simp at this; omega
    obtain ⟨X, hXr, hXc, hXs⟩ := exists_transport n a' b' hsa hsb
    refine ⟨fun S' D' => X S' D' + if S' = S ∧ D' = D then 1 else 0, ?_, ?_, ?_⟩
    · intro S'
      rw [Finset.sum_add_distrib, hXr, ← ha' S']
      by_cases h : S' = S <;> simp [h]
    · intro D'
      rw [Finset.sum_add_distrib, hXc, ← hb' D']
      by_cases h : D' = D <;> simp [h]
    · intro S' D' h
      by_cases h2 : S' = S ∧ D' = D
      · obtain ⟨rfl, rfl⟩ := h2; exact ⟨hS, hD⟩
      · simp only [h2, if_false, add_zero] at h
        obtain ⟨h3, h4⟩ := hXs S' D' h
        constructor
        · intro h5; apply h3; simp [a', h5]
        · intro h5; apply h4; simp [b', h5]

end SlidingPuzzle.Hub
