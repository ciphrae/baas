import Mathlib

/-! # The error scale `n^(8/3) (log n)^(1/3)`

The older error scale, kept for `uniform_approximation_log_explicit`. Its cube
is `n⁸ log n`; the cubic solver's bound is at most `450 hubError n` on the
initial range `4096 ≤ n ≤ 11·2^20` (`cubic_solver_le_hubError`). -/

open Filter Asymptotics

set_option maxRecDepth 4096

namespace SlidingPuzzle.Hub

/-- The error scale `n^(8/3) (log n)^(1/3)`. -/
noncomputable def hubError (n : ℕ) : ℝ :=
  Real.rpow (n : ℝ) (8 / 3 : ℝ) * Real.rpow (Real.log n) (1 / 3 : ℝ)

theorem hubError_nonneg (n : ℕ) : 0 ≤ hubError n := by
  unfold hubError
  have h1 : 0 ≤ Real.rpow (n : ℝ) (8 / 3 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have h2 : 0 ≤ Real.rpow (Real.log n) (1 / 3 : ℝ) :=
    Real.rpow_nonneg (Real.log_natCast_nonneg n) _
  exact mul_nonneg h1 h2

/-- `(x^(a/3))³ = x^a` for `x ≥ 0`. -/
private theorem rpow_div_three_cube {x : ℝ} (hx : 0 ≤ x) (a : ℕ) :
    (Real.rpow x ((a : ℝ) / 3)) ^ 3 = x ^ a := by
  rw [Real.rpow_eq_pow, ← Real.rpow_mul_natCast hx, ← Real.rpow_natCast]
  congr 1
  push_cast
  ring

theorem hubError_cube (n : ℕ) : hubError n ^ 3 = (n : ℝ) ^ 8 * Real.log n := by
  unfold hubError
  rw [mul_pow]
  have h8 := rpow_div_three_cube (Nat.cast_nonneg n) 8
  have h1 := rpow_div_three_cube (Real.log_natCast_nonneg n) 1
  push_cast at h8 h1
  rw [h8, h1, pow_one]

/-- `log n ≥ j log 2` from `2^j ≤ n`. -/
private theorem log_ge_of_pow_le {n j : ℕ} (h : 2 ^ j ≤ n) :
    (j : ℝ) * (6931471803 / 10000000000) ≤ Real.log n := by
  have hh := Real.log_le_log (by positivity) (show (2 : ℝ) ^ j ≤ n by exact_mod_cast h)
  rw [Real.log_pow] at hh
  have := Real.log_two_gt_d9
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

/-- `(c n³)³ ≤ (C hubError n)³` on a range `2^a ≤ n ≤ U`. -/
private theorem cube_range_le' {n a U : ℕ} (ha : 2 ^ a ≤ n) (hb : n ≤ U) {c C P : ℝ}
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hP0 : 0 ≤ P) (hP : P ≤ c * (n : ℝ) ^ 3)
    (hcoef : c ^ 3 * U ≤ C ^ 3 * ((a : ℝ) * (6931471803 / 10000000000))) :
    P ≤ C * hubError n := by
  have hlog := log_ge_of_pow_le ha
  have hbR : (n : ℝ) ≤ U := by exact_mod_cast hb
  have hn8 : (0 : ℝ) ≤ (n : ℝ) ^ 8 := by positivity
  have hcube : P ^ 3 ≤ (C * hubError n) ^ 3 := by
    rw [mul_pow, hubError_cube]
    have hp3 := pow_le_pow_left₀ hP0 hP 3
    have h1 := mul_le_mul_of_nonneg_left hbR (mul_nonneg (pow_nonneg hc 3) hn8)
    have h2 := mul_le_mul_of_nonneg_left hlog (mul_nonneg (pow_nonneg hC 3) hn8)
    have h3 := mul_le_mul_of_nonneg_left hcoef hn8
    calc P ^ 3 ≤ (c * (n : ℝ) ^ 3) ^ 3 := hp3
      _ = c ^ 3 * (n : ℝ) ^ 8 * n := by ring
      _ ≤ c ^ 3 * (n : ℝ) ^ 8 * U := by nlinarith
      _ ≤ C ^ 3 * (n : ℝ) ^ 8 * ((a : ℝ) * (6931471803 / 10000000000)) := by nlinarith
      _ ≤ C ^ 3 * ((n : ℝ) ^ 8 * Real.log n) := by nlinarith
  exact le_of_pow_le_pow_left₀ (by norm_num) (mul_nonneg hC (hubError_nonneg n)) hcube

private theorem cube_range_le {n a b : ℕ} (ha : 2 ^ a ≤ n) (hb : n ≤ 2 ^ b) {c C P : ℝ}
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hP0 : 0 ≤ P) (hP : P ≤ c * (n : ℝ) ^ 3)
    (hcoef : c ^ 3 * 2 ^ b ≤ C ^ 3 * ((a : ℝ) * (6931471803 / 10000000000))) :
    P ≤ C * hubError n :=
  cube_range_le' ha hb hc hC hP0 hP (by exact_mod_cast hcoef)

/-- The cubic solver's exact bound on the finite initial range, in three pieces:
`6n³` below `2^20`, `5.0015 n³` on `[2^20, 2^23]` and `5.0002 n³` on `[2^23, 11·2^20]`. -/
theorem cubic_solver_le_hubError {n : ℕ} (hn : 4096 ≤ n) (hhi : n ≤ 11 * 2 ^ 20) :
    ((5 * n ^ 3 + 1509 * n ^ 2 + 1505 * n + 4796 : ℕ) : ℝ) ≤ 450 * hubError n := by
  have hP0 : (0 : ℝ) ≤ ((5 * n ^ 3 + 1509 * n ^ 2 + 1505 * n + 4796 : ℕ) : ℝ) := Nat.cast_nonneg _
  by_cases h20 : n ≤ 2 ^ 20
  · have hpoly : 5 * n ^ 3 + 1509 * n ^ 2 + 1505 * n + 4796 ≤ 6 * n ^ 3 := by
      have hh := Nat.mul_le_mul_left (n ^ 2) hn
      nlinarith
    exact cube_range_le (a := 12) (b := 20) (by norm_num; omega) h20 (c := 6) (by norm_num)
      (by norm_num) hP0 (by exact_mod_cast hpoly) (by norm_num)
  have hbig : 2 ^ 20 ≤ n := Nat.le_of_lt (Nat.lt_of_not_le h20)
  by_cases h23 : n ≤ 2 ^ 23
  · have hpoly : 10000 * (5 * n ^ 3 + 1509 * n ^ 2 + 1505 * n + 4796) ≤ 50015 * n ^ 3 := by
      have hh := Nat.mul_le_mul_left (n ^ 2) hbig
      nlinarith
    have hpolyR : ((5 * n ^ 3 + 1509 * n ^ 2 + 1505 * n + 4796 : ℕ) : ℝ) ≤
        50015 / 10000 * (n : ℝ) ^ 3 := by
      have : ((10000 * (5 * n ^ 3 + 1509 * n ^ 2 + 1505 * n + 4796) : ℕ) : ℝ) ≤
          ((50015 * n ^ 3 : ℕ) : ℝ) := by exact_mod_cast hpoly
      push_cast at this ⊢
      linarith
    exact cube_range_le (a := 20) (b := 23) hbig h23 (by norm_num) (by norm_num) hP0 hpolyR
      (by norm_num)
  have hbig23 : 2 ^ 23 ≤ n := Nat.le_of_lt (Nat.lt_of_not_le h23)
  have hpoly : 10000 * (5 * n ^ 3 + 1509 * n ^ 2 + 1505 * n + 4796) ≤ 50002 * n ^ 3 := by
    have hh := Nat.mul_le_mul_left (n ^ 2) hbig23
    nlinarith
  have hpolyR : ((5 * n ^ 3 + 1509 * n ^ 2 + 1505 * n + 4796 : ℕ) : ℝ) ≤
      50002 / 10000 * (n : ℝ) ^ 3 := by
    have : ((10000 * (5 * n ^ 3 + 1509 * n ^ 2 + 1505 * n + 4796) : ℕ) : ℝ) ≤
        ((50002 * n ^ 3 : ℕ) : ℝ) := by exact_mod_cast hpoly
    push_cast at this ⊢
    linarith
  exact cube_range_le' (a := 23) (U := 11 * 2 ^ 20) hbig23 hhi (by norm_num) (by norm_num) hP0
    hpolyR (by norm_num)

end SlidingPuzzle.Hub
