import SlidingPuzzle.Hub.RunInit

/-! # Numeric bounds for the run

Junk count and potential of any state. -/
namespace SlidingPuzzle.Hub

open Finset

variable {k : ℕ}

section junk

variable (s : ℕ) (σ : IState k)

theorem junkR_le (H : RowH k) : junkR s σ H ≤ (k - 1) * s :=
  ((card_filter_le _ _).trans (card_range _).le).trans (rowLen_le H)

theorem junkC_le (V : ColH k) : junkC s σ V ≤ (k - 1) * s :=
  ((card_filter_le _ _).trans (card_range _).le).trans
    ((colLen_le V).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _)))

/-- The two halves of a row corridor piece together have `(k-1)s` cells. -/
theorem sum_rowLen : ∑ H : RowH k, rowLen k s H = k * k * ((k - 1) * s) := by
  have hin : ∀ r : Fin k, ∑ y : Fin k × Bool, rowLen k s (r, y) = k * ((k - 1) * s) := by
    intro r
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    rw [show k * ((k - 1) * s) = ∑ _c : Fin k, (k - 1) * s by simp]
    refine sum_congr rfl fun c _ => ?_
    unfold rowLen
    simp only [if_true, Bool.false_eq_true, if_false]
    have := c.isLt
    rw [← add_mul]; congr 1; omega
  rw [Fintype.sum_prod_type, sum_congr rfl fun r _ => hin r]
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- The two halves of a column corridor piece together have `(k-1)(s-k)` cells. -/
theorem sum_colLen : ∑ H : ColH k, colLen k s H = k * k * ((k - 1) * (s - k)) := by
  have hin : ∀ r : Fin k, ∑ y : Fin k × Bool, colLen k s (r, y) = k * ((k - 1) * (s - k)) := by
    intro r
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    rw [show k * ((k - 1) * (s - k)) = ∑ _c : Fin k, (k - 1) * (s - k) by simp]
    refine sum_congr rfl fun c _ => ?_
    unfold colLen
    simp only [if_true, Bool.false_eq_true, if_false]
    have := c.isLt
    rw [← add_mul]; congr 1; omega
  rw [Fintype.sum_prod_type, sum_congr rfl fun r _ => hin r]
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  ring

theorem junkCnt_le : junkCnt s σ ≤ 2 * k ^ 2 * (k * s) := by
  unfold junkCnt
  have h1 : ∑ H, junkR s σ H ≤ ∑ H : RowH k, rowLen k s H :=
    sum_le_sum fun H _ => (card_filter_le _ _).trans (card_range _).le
  have h2 : ∑ V, junkC s σ V ≤ ∑ V : ColH k, colLen k s V :=
    sum_le_sum fun V _ => (card_filter_le _ _).trans (card_range _).le
  rw [sum_rowLen] at h1
  rw [sum_colLen] at h2
  have h3 : (k - 1) * s ≤ k * s := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have h4 : (k - 1) * (s - k) ≤ k * s := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  have h5 := Nat.mul_le_mul_left (k * k) h3
  have h6 := Nat.mul_le_mul_left (k * k) h4
  have e : 2 * k ^ 2 * (k * s) = k * k * (k * s) + k * k * (k * s) := by ring
  omega

theorem potR_le (H : RowH k) : potR s σ H ≤ junkR s σ H * (k * s) := by
  unfold potR junkR
  refine (sum_le_card_nsmul _ _ (k * s) fun q hq => ?_).trans (by simp)
  have hq' := (mem_range.1 (mem_filter.1 hq).1)
  have := rowLen_le (s := s) H
  have : (k - 1) * s ≤ k * s := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  omega

theorem potC_le (V : ColH k) : potC s σ V ≤ junkC s σ V * (k * s) := by
  unfold potC junkC
  refine (sum_le_card_nsmul _ _ (k * s) fun q hq => ?_).trans (by simp)
  have hq' := (mem_range.1 (mem_filter.1 hq).1)
  have := colLen_le (s := s) V
  have : (k - 1) * (s - k) ≤ k * s := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  omega

theorem pot_le : pot s σ ≤ junkCnt s σ * (k * s) := by
  unfold pot junkCnt
  rw [add_mul, sum_mul, sum_mul]
  exact add_le_add (sum_le_sum fun H _ => potR_le s σ H) (sum_le_sum fun V _ => potC_le s σ V)

end junk

end SlidingPuzzle.Hub
