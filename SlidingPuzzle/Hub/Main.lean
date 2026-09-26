import SlidingPuzzle.Hub.AsympBound
import SlidingPuzzle.Hub.AsympError
import SlidingPuzzle.Hub.AsympStats
import SlidingPuzzle.Bridge.Statistics

/-! # A better leading exponent

With `k³ ≈ n / log n` (`k` even) and `s = ⌊n/k⌋`, the hub algorithm on the
`k*s × k*s` residual board costs `O(n³/k + k²n² log n)` inefficient moves, i.e.
`O(n^(8/3) (log n)^(1/3))`; the outer `n - k*s < k` layers are solved by the
Parberry prefix as in `Algorithm/GeneralSize.lean`. Hence the mean optimal
solution length is `(2/3)n³ + O(n^(8/3) (log n)^(1/3))` and God's number is
`n³ + O(n^(8/3) (log n)^(1/3))`, improving Zhong's `O(n^(11/4))`. -/
open Filter Asymptotics

namespace SlidingPuzzle.Hub

/-! The error scale `hubError n = n^(8/3) (log n)^(1/3)` is defined in
`Hub/AsympError.lean`; the natural-number bound of the algorithm is
`optimalLength_le_hub` (`Hub/AsympBound.lean`). -/

/-- The boardwise bound `OPT(B) ≤ M(B) + C n^(8/3) (log n)^(1/3)`. -/
theorem uniform_approximation :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (hn : 2 ≤ n),
      letI : NeZero n := ⟨by omega⟩
      ∀ B : ReachableBoard n,
        (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) + C * hubError n := by
  refine ⟨((8 * hubK * hubD + 4 * hubD : ℕ) : ℝ), by positivity, hubN, ?_⟩
  intro n hn hn2
  let : NeZero n := ⟨by omega⟩
  intro B
  obtain ⟨X, Y, Z, hX, hY, hZ, hopt⟩ := optimalLength_le_hub hn B
  have hn2' : 2 ≤ n := hn2
  have hXR := le_hubError_of_cube hn2' hX
  have hYR := le_hubError_of_cube hn2' hY
  have hZR := le_hubError_of_cube hn2' hZ
  have hoptR : (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      2 * (hubK : ℝ) * ((X : ℝ) + Y) + 2 * Z := by exact_mod_cast hopt
  have hK : (0 : ℝ) ≤ hubK := Nat.cast_nonneg _
  have hXY : 2 * (hubK : ℝ) * ((X : ℝ) + Y) ≤
      2 * (hubK : ℝ) * (2 * hubD * hubError n + 2 * hubD * hubError n) :=
    mul_le_mul_of_nonneg_left (add_le_add hXR hYR) (by positivity)
  push_cast
  nlinarith

/-- The average optimal solution length is `(2/3)n³ + O(n^(8/3) (log n)^(1/3))`. -/
theorem average_optimal_length :
    (fun n : ℕ => averageOptimalLength n - (2 / 3 : ℝ) * (n : ℝ) ^ 3) =O[atTop] hubError := by
  exact average_optimal_length_of_approximation_with sq_le_hubError_eventually
    uniform_approximation ⟨3, by norm_num, averageManhattan_error_eventually⟩

/-- God's number is `n³ + O(n^(8/3) (log n)^(1/3))`. -/
theorem gods_number :
    (fun n : ℕ => godsNumber n - (n : ℝ) ^ 3) =O[atTop] hubError := by
  exact gods_number_of_approximation_with sq_le_hubError_eventually
    uniform_approximation ⟨3, by norm_num, maximumManhattan_error_eventually⟩

/-- Any exponent above `8/3` works; in particular `27/10 < 11/4`. -/
theorem average_optimal_length_rpow {α : ℝ} (hα : 8 / 3 < α) :
    (fun n : ℕ => averageOptimalLength n - (2 / 3 : ℝ) * (n : ℝ) ^ 3)
      =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) α) := by
  exact average_optimal_length.trans (hubError_isBigO_rpow hα)

theorem gods_number_rpow {α : ℝ} (hα : 8 / 3 < α) :
    (fun n : ℕ => godsNumber n - (n : ℝ) ^ 3) =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) α) := by
  exact gods_number.trans (hubError_isBigO_rpow hα)

end SlidingPuzzle.Hub
