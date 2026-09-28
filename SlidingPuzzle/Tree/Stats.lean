import SlidingPuzzle.Tree.Final
import SlidingPuzzle.Hub.AsympStats
import SlidingPuzzle.Bridge.Statistics

/-! # Orbit statistics with error `O(n^(5/2 + ε))`

The statistical reduction (`Hub/AsympStats.lean`) applied to `tree_exponent`:
for every `ε > 0` the mean optimal solution length is `(2/3)n³ + O(n^(5/2+ε))`
and God's number is `n³ + O(n^(5/2+ε))`. -/

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

end SlidingPuzzle.Tree
