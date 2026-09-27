import Mathlib

/-! # The error scale `n^(8/3) (log n)^(1/3)`

Real-analysis facts about `hubError`: its cube is `n⁸ log n`, so a natural
number whose cube is `O(n⁸ (log₂ n + 1))` is `O(hubError n)`; it dominates
`n²`; and it is `O(n^α)` for every `α > 8/3`. -/

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

/-- `log₂ n + 1 ≤ 3 ln n` for `n ≥ 2`. -/
theorem natLog_succ_le_three_log {n : ℕ} (hn : 2 ≤ n) :
    ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ 3 * Real.log n := by
  set j := Nat.log 2 n with hj
  have hj1 : 1 ≤ j := by
    rw [hj]
    exact Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)
  have hpow : 2 ^ j ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hpowR : (2 : ℝ) ^ j ≤ n := by exact_mod_cast hpow
  have hlog : (j : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hpowR
  have hl2 := Real.log_two_gt_d9
  have hj1R : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  push_cast
  nlinarith

/-- Above the algorithm's threshold, `log₂ n + 1 ≤ (8/5) ln n`. -/
theorem natLog_succ_le_eight_fifths_log {n : ℕ} (hn : 4096 ≤ n) :
    ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ (8 / 5 : ℝ) * Real.log n := by
  set j := Nat.log 2 n with hj
  have hj12 : 12 ≤ j := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hpow : (2 : ℝ) ^ j ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  have hlog : (j : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hpow
  have hl2 := Real.log_two_gt_d9
  have hjR : (12 : ℝ) ≤ j := by exact_mod_cast hj12
  push_cast
  nlinarith

/-- Above the algorithm's threshold, `log₂ n + 1 ≤ (156292 / 100000) ln n`. -/
theorem natLog_succ_le_large_log {n : ℕ} (hn : 4096 ≤ n) :
    ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ (156292 / 100000 : ℝ) * Real.log n := by
  set j := Nat.log 2 n with hj
  have hj12 : 12 ≤ j := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hpow : (2 : ℝ) ^ j ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  have hlog : (j : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hpow
  have hl2 := Real.log_two_gt_d9
  have hjR : (12 : ℝ) ≤ j := by exact_mod_cast hj12
  push_cast
  nlinarith

/-- Above the algorithm's threshold, `log₂ n + 1 ≤ (1479688 / 1000000) ln n`. -/
theorem natLog_succ_le_grid_log {n : ℕ} (hn : 2 ^ 39 ≤ n) :
    ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ (1479688 / 1000000 : ℝ) * Real.log n := by
  set j := Nat.log 2 n with hj
  have hj12 : 39 ≤ j := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hpow : (2 : ℝ) ^ j ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  have hlog : (j : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hpow
  have hl2 := Real.log_two_gt_d9
  have hjR : (39 : ℝ) ≤ j := by exact_mod_cast hj12
  push_cast
  nlinarith

/-- A natural number whose cube is at most `D³ n⁸ (log₂ n + 1)` is at most
`(3/2) D hubError n`. -/
theorem le_hubError_of_cube_sharp {n : ℕ} (hn : 2 ≤ n) {X D : ℕ}
    (h : X ^ 3 ≤ D ^ 3 * n ^ 8 * (Nat.log 2 n + 1)) :
    (X : ℝ) ≤ (3 / 2 : ℝ) * D * hubError n := by
  have hR : (X : ℝ) ^ 3 ≤ (D : ℝ) ^ 3 * (n : ℝ) ^ 8 * ((Nat.log 2 n + 1 : ℕ) : ℝ) := by
    exact_mod_cast h
  have hL := natLog_succ_le_three_log hn
  have hA : (0 : ℝ) ≤ (D : ℝ) ^ 3 * (n : ℝ) ^ 8 := by positivity
  have hcube : (X : ℝ) ^ 3 ≤ ((3 / 2 : ℝ) * D * hubError n) ^ 3 := by
    rw [mul_pow, hubError_cube]
    have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    calc (X : ℝ) ^ 3 ≤ (D : ℝ) ^ 3 * (n : ℝ) ^ 8 * ((Nat.log 2 n + 1 : ℕ) : ℝ) := hR
      _ ≤ (D : ℝ) ^ 3 * (n : ℝ) ^ 8 * (3 * Real.log n) := mul_le_mul_of_nonneg_left hL hA
      _ ≤ (D : ℝ) ^ 3 * (n : ℝ) ^ 8 * ((3 / 2 : ℝ) ^ 3 * Real.log n) :=
          mul_le_mul_of_nonneg_left (by nlinarith) hA
      _ = ((3 / 2 : ℝ) * (D : ℝ)) ^ 3 * ((n : ℝ) ^ 8 * Real.log n) := by ring
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (mul_nonneg (by positivity) (hubError_nonneg n)) hcube

/-- A natural number whose cube is at most `D³ n⁸ (log₂ n + 1)` is at most
`(1160502/1000000) D hubError n`. -/
theorem le_hubError_of_cube_large {n : ℕ} (hn : 4096 ≤ n) {X D : ℕ}
    (h : X ^ 3 ≤ D ^ 3 * n ^ 8 * (Nat.log 2 n + 1)) :
    (X : ℝ) ≤ (1160502 / 1000000 : ℝ) * D * hubError n := by
  have hR : (X : ℝ) ^ 3 ≤ (D : ℝ) ^ 3 * (n : ℝ) ^ 8 * ((Nat.log 2 n + 1 : ℕ) : ℝ) := by
    exact_mod_cast h
  have hL := natLog_succ_le_large_log hn
  have hA : (0 : ℝ) ≤ (D : ℝ) ^ 3 * (n : ℝ) ^ 8 := by positivity
  have hcube : (X : ℝ) ^ 3 ≤ ((1160502 / 1000000 : ℝ) * D * hubError n) ^ 3 := by
    rw [mul_pow, hubError_cube]
    have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    calc (X : ℝ) ^ 3 ≤ (D : ℝ) ^ 3 * (n : ℝ) ^ 8 * ((Nat.log 2 n + 1 : ℕ) : ℝ) := hR
      _ ≤ (D : ℝ) ^ 3 * (n : ℝ) ^ 8 * ((156292 / 100000 : ℝ) * Real.log n) := mul_le_mul_of_nonneg_left hL hA
      _ ≤ (D : ℝ) ^ 3 * (n : ℝ) ^ 8 * ((1160502 / 1000000 : ℝ) ^ 3 * Real.log n) :=
          mul_le_mul_of_nonneg_left (by nlinarith) hA
      _ = ((1160502 / 1000000 : ℝ) * (D : ℝ)) ^ 3 * ((n : ℝ) ^ 8 * Real.log n) := by ring
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (mul_nonneg (by positivity) (hubError_nonneg n)) hcube

/-- A natural number whose cube is at most `D³ n⁸ (log₂ n + 1)` is at most
`(1139524/1000000) D hubError n`. -/
theorem le_hubError_of_cube_grid {n : ℕ} (hn : 2 ^ 39 ≤ n) {X D : ℕ}
    (h : X ^ 3 ≤ D ^ 3 * n ^ 8 * (Nat.log 2 n + 1)) :
    (X : ℝ) ≤ (1139524 / 1000000 : ℝ) * D * hubError n := by
  have hR : (X : ℝ) ^ 3 ≤ (D : ℝ) ^ 3 * (n : ℝ) ^ 8 * ((Nat.log 2 n + 1 : ℕ) : ℝ) := by
    exact_mod_cast h
  have hL := natLog_succ_le_grid_log hn
  have hA : (0 : ℝ) ≤ (D : ℝ) ^ 3 * (n : ℝ) ^ 8 := by positivity
  have hcube : (X : ℝ) ^ 3 ≤ ((1139524 / 1000000 : ℝ) * D * hubError n) ^ 3 := by
    rw [mul_pow, hubError_cube]
    have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    calc (X : ℝ) ^ 3 ≤ (D : ℝ) ^ 3 * (n : ℝ) ^ 8 * ((Nat.log 2 n + 1 : ℕ) : ℝ) := hR
      _ ≤ (D : ℝ) ^ 3 * (n : ℝ) ^ 8 * ((1479688 / 1000000 : ℝ) * Real.log n) := mul_le_mul_of_nonneg_left hL hA
      _ ≤ (D : ℝ) ^ 3 * (n : ℝ) ^ 8 * ((1139524 / 1000000 : ℝ) ^ 3 * Real.log n) :=
          mul_le_mul_of_nonneg_left (by nlinarith) hA
      _ = ((1139524 / 1000000 : ℝ) * (D : ℝ)) ^ 3 * ((n : ℝ) ^ 8 * Real.log n) := by ring
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (mul_nonneg (by positivity) (hubError_nonneg n)) hcube

/-- Coarser integral-factor form of `le_hubError_of_cube_sharp`. -/
theorem le_hubError_of_cube {n : ℕ} (hn : 2 ≤ n) {X D : ℕ}
    (h : X ^ 3 ≤ D ^ 3 * n ^ 8 * (Nat.log 2 n + 1)) :
    (X : ℝ) ≤ 2 * D * hubError n := by
  have hsharp := le_hubError_of_cube_sharp hn h
  have hnonneg := mul_nonneg (Nat.cast_nonneg D) (hubError_nonneg n)
  nlinarith

/-- On the finite initial range, the existing cubic solver has a much
smaller coefficient than the hub bound. -/
theorem six_cube_le_hubError {n : ℕ} (hn : 4096 ≤ n) (hhi : n ≤ 2 ^ 39) :
    (6 * n ^ 3 : ℝ) ≤ 24576 * hubError n := by
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hhiR : (n : ℝ) ≤ 2 ^ 39 := by exact_mod_cast hhi
  have hlog : (8 : ℝ) ≤ Real.log n := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2 ^ 12) (show (2 : ℝ) ^ 12 ≤ n by exact_mod_cast hn)
    rw [Real.log_pow] at hh
    have := Real.log_two_gt_d9
    norm_num at hh
    linarith
  have hc : (6 * (n : ℝ) ^ 3) ^ 3 ≤ (24576 * hubError n) ^ 3 := by
    simp only [mul_pow, hubError_cube]
    have h1 := mul_le_mul_of_nonneg_left hhiR (show 0 ≤ (n : ℝ) ^ 8 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (n : ℝ) ^ 8 by positivity)
    nlinarith only [h1, h2]
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (mul_nonneg (by norm_num) (hubError_nonneg n)) hc

/-- `n² ≤ hubError n` once `ln n ≥ 1`. -/
theorem sq_le_hubError {n : ℕ} (hn : 3 ≤ n) : (n : ℝ) ^ 2 ≤ hubError n := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hcube : ((n : ℝ) ^ 2) ^ 3 ≤ hubError n ^ 3 := by
    rw [hubError_cube]
    have h8 : (0 : ℝ) ≤ (n : ℝ) ^ 6 := by positivity
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    calc ((n : ℝ) ^ 2) ^ 3 = (n : ℝ) ^ 6 * 1 * 1 := by ring
      _ ≤ (n : ℝ) ^ 6 * (n : ℝ) ^ 2 * Real.log n := by gcongr
      _ = (n : ℝ) ^ 8 * Real.log n := by ring
  exact le_of_pow_le_pow_left₀ (by norm_num) (hubError_nonneg n) hcube

theorem sq_le_hubError_eventually : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 ≤ hubError n := by
  filter_upwards [eventually_ge_atTop 3] with n hn
  exact sq_le_hubError hn

/-- `hubError = O(n^α)` for every `α > 8/3`. -/
theorem hubError_isBigO_rpow {α : ℝ} (hα : 8 / 3 < α) :
    hubError =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) α) := by
  have hlog : (fun x : ℝ => Real.log x ^ (1 / 3 : ℝ)) =o[atTop]
      (fun x : ℝ => x ^ (α - 8 / 3)) :=
    isLittleO_log_rpow_rpow_atTop _ (by linarith)
  have hlogN := (hlog.comp_tendsto tendsto_natCast_atTop_atTop).isBigO
  have hmain := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ (8 / 3 : ℝ)) atTop).mul hlogN
  refine (hmain.congr_left fun n => ?_).congr' EventuallyEq.rfl ?_
  · simp [hubError, Function.comp]
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Function.comp, Real.rpow_eq_pow]
    rw [← Real.rpow_add hnR]
    congr 1
    ring

end SlidingPuzzle.Hub
