import SlidingPuzzle.Port.Asymp
import SlidingPuzzle.Port.AsympDeep
import SlidingPuzzle.Port.Uniform
import SlidingPuzzle.Tree.Stats

/-! # Orbit statistics with error `O(n^(5/2) ln n / ln ln n)`

The statistical reduction (`Hub/AsympStats.lean`) applied to the port bounds
`port_approximation_uniform` and `port_loglog_uniform`: the mean optimal solution length
is `(2/3)n³ + O(n^(5/2) ln n / ln ln n)` and God's number is
`n³ + O(n^(5/2) ln n / ln ln n)`. -/

open Filter Asymptotics

namespace SlidingPuzzle.Port

open SlidingPuzzle SlidingPuzzle.Hub SlidingPuzzle.Tree

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
  ⟨940, by norm_num, 2 ^ 23, fun n hn hn2 =>
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

/-! ## Error `O(n^(5/2) ln n / ln ln n)` -/

/-- The error scale `n^(5/2) ln n / ln ln n`. -/
noncomputable def llError (n : ℕ) : ℝ :=
  (n : ℝ) ^ ((5 : ℝ) / 2) * Real.log n / Real.log (Real.log n)

theorem sq_le_llError_eventually : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 ≤ llError n := by
  filter_upwards [eventually_ge_atTop 16] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlog : 2 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    have : (16 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.exp_pos 1]
  have ht0 : 0 < Real.log (Real.log n) := Real.log_pos (by linarith)
  have htL : Real.log (Real.log n) ≤ Real.log n := by
    have := Real.log_le_sub_one_of_pos (show 0 < Real.log n by linarith); linarith
  have h1 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ ((5 : ℝ) / 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hP : 0 ≤ (n : ℝ) ^ ((5 : ℝ) / 2) := by positivity
  unfold llError
  rw [le_div_iff₀ ht0]
  have := mul_le_mul h1 htL ht0.le hP
  linarith

theorem port_loglog_approximation_with : UniformApproximationWith llError :=
  ⟨2700, by norm_num, 2 ^ 23, fun n hn hn2 =>
    letI : NeZero n := ⟨by omega⟩
    fun B => by
      have := port_loglog_uniform hn B
      unfold llError
      have e : 2700 * ((n : ℝ) ^ ((5 : ℝ) / 2) * Real.log n / Real.log (Real.log n)) =
          2700 * (n : ℝ) ^ ((5 : ℝ) / 2) * Real.log n / Real.log (Real.log n) := by ring
      rw [e]; exact this⟩

/-- The average optimal solution length is `(2/3)n³ + O(n^(5/2) ln n / ln ln n)`. -/
theorem port_average_optimal_length_loglog :
    (fun n : ℕ => averageOptimalLength n - (2 / 3 : ℝ) * (n : ℝ) ^ 3) =O[atTop] llError :=
  average_optimal_length_of_approximation_with sq_le_llError_eventually
    port_loglog_approximation_with ⟨3, by norm_num, averageManhattan_error_eventually⟩

/-- God's number is `n³ + O(n^(5/2) ln n / ln ln n)`. -/
theorem port_gods_number_loglog :
    (fun n : ℕ => godsNumber n - (n : ℝ) ^ 3) =O[atTop] llError :=
  gods_number_of_approximation_with sq_le_llError_eventually
    port_loglog_approximation_with ⟨3, by norm_num, maximumManhattan_error_eventually⟩

end SlidingPuzzle.Port
