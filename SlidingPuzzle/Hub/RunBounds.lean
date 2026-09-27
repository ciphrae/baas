import SlidingPuzzle.Hub.RunInit

/-! # Numeric bounds for the run

Junk count and potential of any state, and the arithmetic closing the cost
and misplaced-tile budgets. -/
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

section arith

theorem cost_T3 (k s L B : ℕ) (hk : 2 ≤ k) (hks : k ≤ s) (hL : 10 ≤ L)
    (hB : B ≤ k ^ 2 * (7 * (k * s) * L + k ^ 2)) :
    288 * s * (1 + k) * B ≤ 3068 * (k ^ 2 * (k * s) ^ 2 * L) := by
  have h1 : k ^ 2 ≤ k * s := by nlinarith
  have h2 : 10 * (k * s) ≤ k * s * L := by nlinarith
  have h3 := Nat.mul_le_mul_left (k ^ 2) (h1.trans (by omega : k * s ≤ k * s * L))
  have h4 := Nat.mul_le_mul_left (k ^ 2) h2
  have hb : 10 * B ≤ 71 * k ^ 2 * (k * s) * L := by
    have hh := Nat.mul_le_mul_left (k ^ 2) h1
    nlinarith
  have hc : 288 * s * (1 + k) ≤ 432 * (k * s) := by nlinarith
  have hh := Nat.mul_le_mul hc hb
  nlinarith

theorem cost_T4 (k s L W : ℕ) (hk : 2 ≤ k) (hks : k ≤ s) (hL : 10 ≤ L)
    (hW : W ≤ s ^ 2 * (4 * k ^ 2 + 4 * k) + 4 * k * (k ^ 2 * (2 * k * s + 1))) :
    576 * s * W ≤ 3456 * ((k * s) ^ 2 * s) + 692 * (k ^ 2 * (k * s) ^ 2 * L) := by
  have h1 : 576 * s * W ≤ 576 * s * (s ^ 2 * (4 * k ^ 2 + 4 * k) +
      4 * k * (k ^ 2 * (2 * k * s + 1))) := Nat.mul_le_mul_left _ hW
  have h2 : 4 * k ^ 2 + 4 * k ≤ 6 * k ^ 2 := by nlinarith
  have h3 : 2 * k * s + 1 ≤ 3 * k * s := by nlinarith
  have h4 : s ^ 2 * (4 * k ^ 2 + 4 * k) ≤ s ^ 2 * (6 * k ^ 2) := Nat.mul_le_mul_left _ h2
  have h5 : 4 * k * (k ^ 2 * (2 * k * s + 1)) ≤ 4 * k * (k ^ 2 * (3 * k * s)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
  have h6 : 576 * s * (s ^ 2 * (6 * k ^ 2) + 4 * k * (k ^ 2 * (3 * k * s))) =
      3456 * ((k * s) ^ 2 * s) + 6912 * (k ^ 2 * (k * s) ^ 2) := by ring
  have h7 : 10 * (k ^ 2 * (k * s) ^ 2) ≤ k ^ 2 * (k * s) ^ 2 * L := by nlinarith [Nat.mul_le_mul_left (k ^ 2 * (k * s) ^ 2) hL]
  have h8 : 576 * s * (s ^ 2 * (4 * k ^ 2 + 4 * k) + 4 * k * (k ^ 2 * (2 * k * s + 1))) ≤
      576 * s * (s ^ 2 * (6 * k ^ 2) + 4 * k * (k ^ 2 * (3 * k * s))) :=
    Nat.mul_le_mul_left _ (add_le_add h4 h5)
  omega

/-- Keep the local coefficient `576 + 3456` separate from the corridor
coefficient `1 + 6 + 3068 + 692`. -/
theorem cost_arith (k s L P S0 B W : ℕ) (hk : 2 ≤ k) (hks : k ≤ s) (hL : 10 ≤ L)
    (hP : P ≤ 4 * k ^ 2 * (k * s) * (k * s)) (hS : S0 ≤ (k * s) ^ 2)
    (hB : B ≤ k ^ 2 * (7 * (k * s) * L + k ^ 2))
    (hW : W ≤ s ^ 2 * (4 * k ^ 2 + 4 * k) + 4 * k * (k ^ 2 * (2 * k * s + 1))) :
    P + 2 * (288 * s + 30 * k ^ 2) * S0 + 288 * s * (1 + k) * B + 576 * s * W ≤
      4032 * ((k * s) ^ 2 * s) + 3767 * (k ^ 2 * (k * s) ^ 2 * L) := by
  have t3 := cost_T3 k s L B hk hks hL hB
  have t4 := cost_T4 k s L W hk hks hL hW
  have h7 : 10 * (k ^ 2 * (k * s) ^ 2) ≤ k ^ 2 * (k * s) ^ 2 * L := by nlinarith [Nat.mul_le_mul_left (k ^ 2 * (k * s) ^ 2) hL]
  have t1 : P ≤ 1 * (k ^ 2 * (k * s) ^ 2 * L) := by
    have : 4 * k ^ 2 * (k * s) * (k * s) = 4 * (k ^ 2 * (k * s) ^ 2) := by ring
    omega
  have t2 : 2 * (288 * s + 30 * k ^ 2) * S0 ≤ 576 * ((k * s) ^ 2 * s) +
      6 * (k ^ 2 * (k * s) ^ 2 * L) := by
    have := Nat.mul_le_mul_left (2 * (288 * s + 30 * k ^ 2)) hS
    have e : 2 * (288 * s + 30 * k ^ 2) * (k * s) ^ 2 =
        576 * ((k * s) ^ 2 * s) + 60 * (k ^ 2 * (k * s) ^ 2) := by ring
    omega
  omega

/-- The leading coefficient is `21`; `L ≥ 10` absorbs the remainder into `3`. -/
theorem mis_arith (k s L A : ℕ) (hk : 2 ≤ k) (hks : k ≤ s) (hL : 10 ≤ L)
    (h : A ≤ k ^ 2 * (k * s) + k ^ 2 * (7 * (k * s) * L + k ^ 2) +
      k ^ 2 * (2 * (7 * (k * s) * L + 8 * (k * s) + 10)) + 4 * k ^ 2 * (k * s)) :
    A ≤ 24 * k ^ 2 * (k * s) * L := by
  have hn : 4 ≤ k * s := by nlinarith
  have hk2 : k ^ 2 ≤ k * s := by nlinarith
  have h1 : 10 * (k * s) ≤ k * s * L := by nlinarith
  have h2 : k ^ 2 * (k ^ 2) ≤ k ^ 2 * (k * s) := Nat.mul_le_mul_left _ hk2
  have h3 : k ^ 2 * 4 ≤ k ^ 2 * (k * s) := Nat.mul_le_mul_left _ hn
  have h4 : 10 * (k ^ 2 * (k * s)) ≤ k ^ 2 * (k * s * L) := by nlinarith [Nat.mul_le_mul_left (k ^ 2) h1]
  have e : A ≤ 21 * (k ^ 2 * (k * s * L)) + 21 * (k ^ 2 * (k * s)) + k ^ 2 * k ^ 2 +
      20 * (k ^ 2 * 1) := by
    have : k ^ 2 * (k * s) + k ^ 2 * (7 * (k * s) * L + k ^ 2) +
      k ^ 2 * (2 * (7 * (k * s) * L + 8 * (k * s) + 10)) + 4 * k ^ 2 * (k * s) =
        21 * (k ^ 2 * (k * s * L)) + 21 * (k ^ 2 * (k * s)) + k ^ 2 * k ^ 2 +
          20 * (k ^ 2 * 1) := by ring
    omega
  have : 24 * k ^ 2 * (k * s) * L = 24 * (k ^ 2 * (k * s * L)) := by ring
  omega

end arith

end SlidingPuzzle.Hub
