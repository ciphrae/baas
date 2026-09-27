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

theorem junkCnt_le : junkCnt s σ ≤ 4 * k ^ 2 * (k * s) := by
  unfold junkCnt
  have h1 : ∑ H, junkR s σ H ≤ ∑ _H : RowH k, (k - 1) * s := sum_le_sum fun H _ => junkR_le s σ H
  have h2 : ∑ V, junkC s σ V ≤ ∑ _V : ColH k, (k - 1) * s := sum_le_sum fun V _ => junkC_le s σ V
  simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    smul_eq_mul] at h1 h2
  have h3 : (k - 1) * s ≤ k * s := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have h4 : k * (k * 2) * ((k - 1) * s) ≤ k * (k * 2) * (k * s) := Nat.mul_le_mul_left _ h3
  nlinarith

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
