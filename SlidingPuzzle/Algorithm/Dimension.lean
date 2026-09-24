import SlidingPuzzle.Asymptotics

/-! The arithmetic part of rounding a board dimension down to a fourth power.
No puzzle-solving or protected-placement claim is made in this module. -/
namespace SlidingPuzzle

/-- Integer fourth root, expressed using two integer square roots. -/
def fourthRoot (n : ℕ) : ℕ := Nat.sqrt (Nat.sqrt n)

theorem le_fourthRoot_iff (k n : ℕ) : k ≤ fourthRoot n ↔ k ^ 4 ≤ n := by
  unfold fourthRoot
  rw [Nat.le_sqrt', Nat.le_sqrt']
  norm_num [← pow_mul]

theorem fourthRoot_pow_le (n : ℕ) : fourthRoot n ^ 4 ≤ n :=
  (le_fourthRoot_iff _ _).mp le_rfl

theorem lt_fourthRoot_add_one_pow (n : ℕ) : n < (fourthRoot n + 1) ^ 4 := by
  have h := le_fourthRoot_iff (fourthRoot n + 1) n
  omega

theorem two_le_fourthRoot {n : ℕ} (hn : 16 ≤ n) : 2 ≤ fourthRoot n := by
  apply (le_fourthRoot_iff 2 n).mpr
  norm_num
  exact hn

/-- Concrete dimension choice with all validity and gap requirements. -/
theorem exists_fourth_power_dimension {n : ℕ} (hn : 16 ≤ n) :
    ∃ k : ℕ, 2 ≤ k ∧ k ^ 4 ≤ n ∧ n < (k + 1) ^ 4 ∧ n - k ^ 4 ≤ 15 * k ^ 3 := by
  refine ⟨fourthRoot n, two_le_fourthRoot hn, fourthRoot_pow_le n,
    lt_fourthRoot_add_one_pow n, ?_⟩
  apply fourth_power_gap_le (by have := two_le_fourthRoot hn; omega)
  exact lt_fourthRoot_add_one_pow n

/-- Converting an outer-layer move budget to the fourth-power error scale. -/
theorem outer_layer_budget_le {n k : ℕ} (hk : 1 ≤ k) (hn : n < (k + 1) ^ 4) :
    (n - k ^ 4) * n ^ 2 ≤ 3840 * k ^ 11 := by
  have hgap := fourth_power_gap_le hk hn
  have hk1 : k + 1 ≤ 2 * k := by omega
  have hn' : n ≤ 16 * k ^ 4 := by
    have hpow := Nat.pow_le_pow_left hk1 4
    nlinarith
  have hn2 : n ^ 2 ≤ 256 * k ^ 8 := by
    calc n ^ 2 ≤ (16 * k ^ 4) ^ 2 := Nat.pow_le_pow_left hn' 2
         _ = 256 * k ^ 8 := by ring
  calc
    (n - k ^ 4) * n ^ 2 ≤ (15 * k ^ 3) * (256 * k ^ 8) := Nat.mul_le_mul hgap hn2
    _ = 3840 * k ^ 11 := by ring

/-- The discarded width is at most four times the ambient three-quarter power. -/
theorem outer_layer_width_le_rpow {n k : ℕ} (hlo : k^4 ≤ n) (hhi : n < (k+1)^4) :
    (n-k^4 : ℕ) ≤ 4 * Real.rpow (n : ℝ) (3/4 : ℝ) := by
  let x := Real.rpow (n : ℝ) (1/4 : ℝ)
  have hx : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hx4 : x^4 = (n : ℝ) := by
    simpa [x] using Real.rpow_inv_natCast_pow (Nat.cast_nonneg n) (by norm_num : (4 : ℕ) ≠ 0)
  have hxk : x < (k : ℝ)+1 := by
    have hn : (n : ℝ) < ((k : ℝ)+1)^4 := by exact_mod_cast hhi
    by_contra h
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (k : ℝ)+1) (le_of_not_gt h) 4
    linarith
  have hgap : (n : ℝ)-(k : ℝ)^4 ≤ 4*x^3 := by
    have hfactor : 0 ≤ (x-(k : ℝ))^2*(3*x^2+2*x*(k : ℝ)+(k : ℝ)^2) := by positivity
    have hlast := mul_le_mul_of_nonneg_left (le_of_lt hxk) (show 0 ≤ 4*x^3 by positivity)
    nlinarith [hfactor, hlast]
  have hx3 : x^3 = Real.rpow (n : ℝ) (3/4 : ℝ) := by
    convert (Real.rpow_mul_natCast (Nat.cast_nonneg n) (1/4 : ℝ) 3).symm using 1 <;>
      norm_num [x]
  rw [Nat.cast_sub hlo, Nat.cast_pow, ← hx3]
  exact hgap

/-- Convert the discarded width to the ambient eleven-quarter power. -/
theorem outer_layer_budget_le_rpow {n k : ℕ} (hlo : k^4 ≤ n) (hhi : n < (k+1)^4) :
    (n-k^4 : ℕ) * (n : ℝ)^2 ≤ 4 * Real.rpow (n : ℝ) (11/4 : ℝ) := by
  calc
    (n-k^4 : ℕ) * (n : ℝ)^2 ≤
        4*Real.rpow (n : ℝ) (3/4 : ℝ)*(n : ℝ)^2 :=
      mul_le_mul_of_nonneg_right (outer_layer_width_le_rpow hlo hhi) (sq_nonneg _)
    _ = 4*Real.rpow (n : ℝ) (11/4 : ℝ) := by
      rw [mul_assoc]
      congr 1
      convert (Real.rpow_add_of_nonneg (Nat.cast_nonneg n)
        (by norm_num : (0 : ℝ) ≤ 3/4) (by norm_num : (0 : ℝ) ≤ 2)).symm using 1 <;>
        norm_num [Real.rpow_natCast]

end SlidingPuzzle
