import Mathlib

/-! # Maclaurin's inequality

For nonnegative reals `y_1, …, y_N`, the elementary symmetric mean is at most the
power of the arithmetic mean: `e_t(y) ≤ C(N,t) (Σ y / N)^t`.

Proof by induction on `N`: `e_{t+1}(a, y) = e_{t+1}(y) + a e_t(y)`, the induction
hypothesis bounds both by powers of the old mean `μ'`, and the tangent-line
inequality `μ'^(t+1) + (t+1) μ'^t (μ - μ') ≤ μ^(t+1)` (Bernoulli) for the new
mean `μ = μ' + (a - μ')/(N+1)` closes the step. -/
namespace SlidingPuzzle.Hub

/-- Tangent-line inequality for `x ↦ x^(t+1)` on `x ≥ 0`. -/
theorem pow_succ_tangent_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (t : ℕ) :
    x ^ (t + 1) + (t + 1) * x ^ t * (y - x) ≤ y ^ (t + 1) := by
  rcases hx.eq_or_lt with rfl | hx
  · rcases t with _ | t
    · simp
    · simp; positivity
  · have hb := one_add_mul_le_pow (a := y / x - 1) (by
      have : 0 ≤ y / x := div_nonneg hy hx.le
      linarith) (t + 1)
    have hxt : 0 < x ^ (t + 1) := pow_pos hx _
    have h1 : (1 + (y / x - 1)) ^ (t + 1) * x ^ (t + 1) = y ^ (t + 1) := by
      rw [← mul_pow]; congr 1; field_simp; ring
    have h2 : (1 + ((t + 1 : ℕ) : ℝ) * (y / x - 1)) * x ^ (t + 1) =
        x ^ (t + 1) + (t + 1) * x ^ t * (y - x) := by
      push_cast; field_simp; ring
    rw [← h1, ← h2]
    exact mul_le_mul_of_nonneg_right hb hxt.le

theorem esymm_cons_succ (a : ℝ) (s : Multiset ℝ) (t : ℕ) :
    (a ::ₘ s).esymm (t + 1) = s.esymm (t + 1) + a * s.esymm t := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_def, Multiset.prod_cons, Multiset.sum_map_mul_left]

theorem esymm_zero_right (s : Multiset ℝ) : s.esymm 0 = 1 := by
  simp [Multiset.esymm]

/-- The inductive step of Maclaurin's inequality, as an inequality of reals. -/
theorem maclaurin_step {N t : ℕ} {a μ' : ℝ} (ha : 0 ≤ a) (hμ' : 0 ≤ μ')
    {e1 e0 : ℝ} (he1 : e1 ≤ (N.choose (t + 1)) * μ' ^ (t + 1))
    (he0 : e0 ≤ (N.choose t) * μ' ^ t) :
    e1 + a * e0 ≤ ((N + 1).choose (t + 1)) * (μ' + (a - μ') / (N + 1)) ^ (t + 1) := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  have hμ : 0 ≤ μ' + (a - μ') / (N + 1) := by
    have : μ' + (a - μ') / (N + 1) = (N * μ' + a) / (N + 1) := by field_simp; ring
    rw [this]; positivity
  have T := pow_succ_tangent_le hμ' hμ t
  have h1 : ((N : ℝ) + 1) * (N.choose t) = ((N + 1).choose (t + 1)) * (t + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq N t
  have h2 : (((N + 1).choose (t + 1) : ℕ) : ℝ) = (N.choose t) + (N.choose (t + 1)) := by
    exact_mod_cast Nat.choose_succ_succ' N t
  have hc : (0 : ℝ) ≤ ((N + 1).choose (t + 1)) := Nat.cast_nonneg _
  calc e1 + a * e0 ≤ (N.choose (t + 1)) * μ' ^ (t + 1) + a * ((N.choose t) * μ' ^ t) := by
        gcongr
    _ = ((N + 1).choose (t + 1)) *
          (μ' ^ (t + 1) + (t + 1) * μ' ^ t * ((μ' + (a - μ') / (N + 1)) - μ')) := by
        have e : ((N + 1).choose (t + 1) : ℝ) * (t + 1) * ((μ' + (a - μ') / (N + 1)) - μ') =
            (N.choose t) * (a - μ') := by
          rw [← h1]; field_simp; ring
        linear_combination (-(μ' ^ t)) * e - (μ' ^ (t + 1)) * h2
    _ ≤ _ := mul_le_mul_of_nonneg_left T hc

/-- **Maclaurin's inequality** for a multiset of nonnegative reals. -/
theorem maclaurin (m : Multiset ℝ) (hm : ∀ x ∈ m, 0 ≤ x) (t : ℕ) :
    m.esymm t ≤ (m.card.choose t) * (m.sum / m.card) ^ t := by
  induction m using Multiset.induction_on generalizing t with
  | empty =>
    rcases t with _ | t
    · simp [Multiset.esymm]
    · simp [Multiset.esymm, Multiset.powersetCard_eq_empty (t + 1) (s := (0 : Multiset ℝ)) (by simp)]
  | cons a s ih =>
    have ha : 0 ≤ a := hm a (Multiset.mem_cons_self a s)
    have hs : ∀ x ∈ s, 0 ≤ x := fun x hx => hm x (Multiset.mem_cons_of_mem hx)
    rcases t with _ | t
    · simp [esymm_zero_right]
    have hS : 0 ≤ s.sum := Multiset.sum_nonneg hs
    have hμ' : 0 ≤ s.sum / s.card := div_nonneg hS (Nat.cast_nonneg _)
    have key := maclaurin_step (N := s.card) (t := t) ha hμ' (ih hs (t + 1)) (ih hs t)
    have hmean : (a ::ₘ s).sum / ((a ::ₘ s).card : ℝ) =
        s.sum / s.card + (a - s.sum / s.card) / (s.card + 1) := by
      rw [Multiset.sum_cons, Multiset.card_cons]
      rcases Nat.eq_zero_or_pos s.card with h0 | hpos
      · rw [Multiset.card_eq_zero.mp h0]; simp
      · have : (0 : ℝ) < s.card := by exact_mod_cast hpos
        push_cast; field_simp; ring
    rw [esymm_cons_succ, hmean, Multiset.card_cons]
    exact key

/-- Maclaurin's inequality over the `t`-subsets of a finset. -/
theorem maclaurin_finset {ι : Type*} [DecidableEq ι] (s : Finset ι) (y : ι → ℝ)
    (hy : ∀ i ∈ s, 0 ≤ y i) (t : ℕ) :
    ∑ W ∈ s.powersetCard t, ∏ i ∈ W, y i ≤ (s.card.choose t) * ((∑ i ∈ s, y i) / s.card) ^ t := by
  have h := maclaurin (s.val.map y) (by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
    exact hy i hi) t
  rw [Finset.esymm_map_val] at h
  rwa [Multiset.card_map, Finset.card_val, ← Finset.sum_eq_multiset_sum] at h

end SlidingPuzzle.Hub
