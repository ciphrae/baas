import SlidingPuzzle.Port.Asymp
import SlidingPuzzle.Port.AsympDeep
import SlidingPuzzle.Tree.Stats

/-! # Orbit statistics with error `O(n^(5/2) ln n)`

The statistical reduction (`Hub/AsympStats.lean`) applied to the port bound
`port_approximation_uniform`: the mean optimal solution length is
`(2/3)n³ + O(n^(5/2) ln n)` and God's number is `n³ + O(n^(5/2) ln n)`. -/

open Filter Asymptotics

namespace SlidingPuzzle.Port

open SlidingPuzzle SlidingPuzzle.Hub SlidingPuzzle.Tree

/-- **`OPT(B) ≤ M(B) + 1260 n^(5/2) ln n`** for `n ≥ 2²³`. -/
theorem port_approximation_uniform {n : ℕ} [NeZero n] (hn : 2 ^ 23 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) + 1260 * (n : ℝ) ^ ((5 : ℝ) / 2) * Real.log n := by
  have h := port_optimalLength_le hn B
  have hL := log_ge_of_pow23 hn
  have hs : Real.sqrt (Real.log n) ≤ Real.log n / 3.99 := by
    have h1 : (3.99 : ℝ) ≤ Real.sqrt (Real.log n) := by
      rw [show (3.99 : ℝ) = Real.sqrt (3.99 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by linarith)
    rw [le_div_iff₀ (by norm_num)]
    have e := Real.mul_self_sqrt (show (0 : ℝ) ≤ Real.log n by linarith)
    nlinarith
  have hc : 29 * Real.log n + 4900 * Real.sqrt (Real.log n) ≤ 1260 * Real.log n := by
    have h1 := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 4900)
    have h2 : 4900 * (Real.log n / 3.99) ≤ 1231 * Real.log n := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ (by norm_num)]
      nlinarith
    linarith
  have hP : (0 : ℝ) ≤ (n : ℝ) ^ ((5 : ℝ) / 2) := by positivity
  have := mul_le_mul_of_nonneg_right hc hP
  linarith

/-- The error scale `n^(5/2) ln n`. -/
noncomputable def lnError (n : ℕ) : ℝ := (n : ℝ) ^ ((5 : ℝ) / 2) * Real.log n

theorem sq_le_lnError_eventually : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 ≤ lnError n := by
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlog : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h1 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ ((5 : ℝ) / 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  unfold lnError
  nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ n by positivity) ((5 : ℝ) / 2)]

theorem port_uniform_approximation_with : UniformApproximationWith lnError :=
  ⟨1260, by norm_num, 2 ^ 23, fun n hn hn2 =>
    letI : NeZero n := ⟨by omega⟩
    fun B => by
      have := port_approximation_uniform hn B
      unfold lnError; linarith⟩

/-- The average optimal solution length is `(2/3)n³ + O(n^(5/2) ln n)`. -/
theorem port_average_optimal_length :
    (fun n : ℕ => averageOptimalLength n - (2 / 3 : ℝ) * (n : ℝ) ^ 3) =O[atTop] lnError :=
  average_optimal_length_of_approximation_with sq_le_lnError_eventually
    port_uniform_approximation_with ⟨3, by norm_num, averageManhattan_error_eventually⟩

/-- God's number is `n³ + O(n^(5/2) ln n)`. -/
theorem port_gods_number :
    (fun n : ℕ => godsNumber n - (n : ℝ) ^ 3) =O[atTop] lnError :=
  gods_number_of_approximation_with sq_le_lnError_eventually
    port_uniform_approximation_with ⟨3, by norm_num, maximumManhattan_error_eventually⟩

end SlidingPuzzle.Port
