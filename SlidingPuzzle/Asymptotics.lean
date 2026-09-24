import Mathlib

/-! Arithmetic for the general-size reduction and asymptotic assembly.
These results do not assume any unproved sliding-puzzle estimates. -/

open Filter Asymptotics

namespace SlidingPuzzle

/-- The quadratic error is bounded by the final error scale at every positive size. -/
theorem nat_sq_le_rpow_eleven_fourths {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ 2 ≤ Real.rpow (n : ℝ) (11 / 4 : ℝ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simpa using
    (Real.rpow_le_rpow_of_exponent_le hn' (show (2 : ℝ) ≤ 11 / 4 by norm_num))

/-- A quadratic error plus the final error scale is still of the final order. -/
theorem error_isBigO_rpow_eleven_fourths
    (f baseline : ℕ → ℝ) (C K : ℝ) (hC : 0 ≤ C)
    (h : ∀ᶠ n in atTop,
      |f n - baseline n| ≤ C * (n : ℝ) ^ 2 + K * Real.rpow (n : ℝ) (11 / 4 : ℝ)) :
    (fun n => f n - baseline n) =O[atTop]
      (fun n : ℕ => Real.rpow (n : ℝ) (11 / 4 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (C + K)
  filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
  have hp : 0 ≤ Real.rpow (n : ℝ) (11 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp]
  calc
    |f n - baseline n| ≤ C * (n : ℝ) ^ 2 + K * Real.rpow (n : ℝ) (11 / 4 : ℝ) := hn
    _ ≤ C * Real.rpow (n : ℝ) (11 / 4 : ℝ) +
        K * Real.rpow (n : ℝ) (11 / 4 : ℝ) :=
      by linarith [mul_le_mul_of_nonneg_left (nat_sq_le_rpow_eleven_fourths hn1) hC]
    _ = (C + K) * Real.rpow (n : ℝ) (11 / 4 : ℝ) := by ring

/-- The width lost by rounding a dimension down to a fourth power is cubic. -/
theorem fourth_power_gap_le {n k : ℕ} (hk : 1 ≤ k) (hn : n < (k + 1) ^ 4) :
    n - k ^ 4 ≤ 15 * k ^ 3 := by
  have h1 : k ≤ k ^ 2 := by nlinarith
  have h2 : k ^ 2 ≤ k ^ 3 := by nlinarith [Nat.mul_le_mul_left k h1]
  have h3 : 1 ≤ k ^ 3 := by omega
  have hg : (k + 1) ^ 4 ≤ k ^ 4 + 15 * k ^ 3 := by nlinarith
  omega

/-- A fourth-power subproblem has an error bounded by the ambient error scale. -/
theorem pow_eleven_le_rpow_of_fourth_power_le {k n : ℕ} (hkn : k ^ 4 ≤ n) :
    (k : ℝ) ^ 11 ≤ Real.rpow (n : ℝ) (11 / 4 : ℝ) := by
  have hkn' : (k : ℝ) ^ 4 ≤ (n : ℝ) := by exact_mod_cast hkn
  calc
    (k : ℝ) ^ 11 = Real.rpow ((k : ℝ) ^ 4) (11 / 4 : ℝ) := by
      rw [Real.rpow_eq_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg k) 4]
      norm_num [Real.rpow_natCast]
    _ ≤ Real.rpow (n : ℝ) (11 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hkn' (by norm_num)

end SlidingPuzzle
