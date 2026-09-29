import SlidingPuzzle.Tree.LamLog
import SlidingPuzzle.Hub.AsympStats
import SlidingPuzzle.Bridge.Statistics

/-! # Orbit statistics with error `O(n^(5/2) (ln n)^(3/2))`

The statistical reduction (`Hub/AsympStats.lean`) applied to `tree_exponent` and to
`tree_lam_approximation_uniform`: the mean optimal solution length is
`(2/3)n³ + O(n^(5/2) (ln n)^(3/2))` and God's number is `n³ + O(n^(5/2) (ln n)^(3/2))`;
in particular both errors are `O(n^(5/2+ε))` for every `ε > 0`. -/

open Filter Asymptotics

namespace SlidingPuzzle.Tree

open SlidingPuzzle SlidingPuzzle.Hub

theorem sq_le_rpow_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (5 / 2 + ε) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hn1 (by push_cast; linarith)

theorem tree_uniform_approximation_with {ε : ℝ} (hε : 0 < ε) :
    UniformApproximationWith (fun n => (n : ℝ) ^ (5 / 2 + ε)) :=
  tree_exponent hε

/-- The average optimal solution length is `(2/3)n³ + O(n^(5/2+ε))` for every `ε > 0`. -/
theorem tree_average_optimal_length {ε : ℝ} (hε : 0 < ε) :
    (fun n : ℕ => averageOptimalLength n - (2 / 3 : ℝ) * (n : ℝ) ^ 3) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (5 / 2 + ε)) :=
  average_optimal_length_of_approximation_with (sq_le_rpow_eventually hε)
    (tree_uniform_approximation_with hε) ⟨3, by norm_num, averageManhattan_error_eventually⟩

/-- God's number is `n³ + O(n^(5/2+ε))` for every `ε > 0`. -/
theorem tree_gods_number {ε : ℝ} (hε : 0 < ε) :
    (fun n : ℕ => godsNumber n - (n : ℝ) ^ 3) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (5 / 2 + ε)) :=
  gods_number_of_approximation_with (sq_le_rpow_eventually hε)
    (tree_uniform_approximation_with hε) ⟨3, by norm_num, maximumManhattan_error_eventually⟩

/-- The error scale `n^(5/2) (ln n)^(3/2)`. -/
noncomputable def logError (n : ℕ) : ℝ := (n : ℝ) ^ ((5 : ℝ) / 2) * Real.log n ^ ((3 : ℝ) / 2)

theorem sq_le_logError_eventually : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 ≤ logError n := by
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
  have h2 : (1 : ℝ) ≤ Real.log n ^ ((3 : ℝ) / 2) := Real.one_le_rpow hlog (by norm_num)
  unfold logError
  nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ n by positivity) ((5 : ℝ) / 2)]

theorem tree_log_uniform_approximation_with : UniformApproximationWith logError :=
  ⟨375, by norm_num, 2 ^ 23, fun n hn hn2 =>
    letI : NeZero n := ⟨by omega⟩
    fun B => by
      have := tree_lam_approximation_uniform hn B
      unfold logError; linarith⟩

/-- The average optimal solution length is `(2/3)n³ + O(n^(5/2) (ln n)^(3/2))`. -/
theorem tree_log_average_optimal_length :
    (fun n : ℕ => averageOptimalLength n - (2 / 3 : ℝ) * (n : ℝ) ^ 3) =O[atTop] logError :=
  average_optimal_length_of_approximation_with sq_le_logError_eventually
    tree_log_uniform_approximation_with ⟨3, by norm_num, averageManhattan_error_eventually⟩

/-- God's number is `n³ + O(n^(5/2) (ln n)^(3/2))`. -/
theorem tree_log_gods_number :
    (fun n : ℕ => godsNumber n - (n : ℝ) ^ 3) =O[atTop] logError :=
  gods_number_of_approximation_with sq_le_logError_eventually
    tree_log_uniform_approximation_with ⟨3, by norm_num, maximumManhattan_error_eventually⟩

end SlidingPuzzle.Tree
