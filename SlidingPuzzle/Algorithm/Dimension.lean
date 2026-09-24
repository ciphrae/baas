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

end SlidingPuzzle
