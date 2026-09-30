import SlidingPuzzle.Port.Asymp
import SlidingPuzzle.Port.AsympDeep
import SlidingPuzzle.Port.LogLog
import SlidingPuzzle.Tree.Stats

/-! # Orbit statistics with error `O(n^(5/2) ln n / ln ln n)`

The statistical reduction (`Hub/AsympStats.lean`) applied to the port bounds
`port_approximation_uniform` and `port_loglog_uniform`: the mean optimal solution length
is `(2/3)n³ + O(n^(5/2) ln n / ln ln n)` and God's number is
`n³ + O(n^(5/2) ln n / ln ln n)`. -/

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
  ⟨3500, by norm_num, 2 ^ 23, fun n hn hn2 =>
    letI : NeZero n := ⟨by omega⟩
    fun B => by
      have := port_loglog_uniform hn B
      unfold llError
      have e : 3500 * ((n : ℝ) ^ ((5 : ℝ) / 2) * Real.log n / Real.log (Real.log n)) =
          3500 * (n : ℝ) ^ ((5 : ℝ) / 2) * Real.log n / Real.log (Real.log n) := by ring
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
