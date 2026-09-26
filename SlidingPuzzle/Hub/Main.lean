import SlidingPuzzle.Hub.Transport
import SlidingPuzzle.Bridge.Statistics
import SlidingPuzzle.Algorithm.GeneralSize

/-! # A better leading exponent

With `k³ ≈ n / log n` (`k` even) and `s = ⌊n/k⌋`, the hub algorithm on the
`k*s × k*s` residual board costs `O(n³/k + k²n² log n)` inefficient moves, i.e.
`O(n^(8/3) (log n)^(1/3))`; the outer `n - k*s < k` layers are solved by the
Parberry prefix as in `Algorithm/GeneralSize.lean`. Hence the mean optimal
solution length is `(2/3)n³ + O(n^(8/3) (log n)^(1/3))` and God's number is
`n³ + O(n^(8/3) (log n)^(1/3))`, improving Zhong's `O(n^(11/4))`. -/
open Filter Asymptotics

namespace SlidingPuzzle.Hub

/-- The error scale `n^(8/3) (log n)^(1/3)`. -/
noncomputable def hubError (n : ℕ) : ℝ :=
  Real.rpow (n : ℝ) (8 / 3 : ℝ) * Real.rpow (Real.log n) (1 / 3 : ℝ)

/-- The boardwise bound `OPT(B) ≤ M(B) + C n^(8/3) (log n)^(1/3)`. -/
theorem uniform_approximation :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (hn : 2 ≤ n),
      letI : NeZero n := ⟨by omega⟩
      ∀ B : ReachableBoard n,
        (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) + C * hubError n := by
  sorry

/-- The average optimal solution length is `(2/3)n³ + O(n^(8/3) (log n)^(1/3))`. -/
theorem average_optimal_length :
    (fun n : ℕ => averageOptimalLength n - (2 / 3 : ℝ) * (n : ℝ) ^ 3) =O[atTop] hubError := by
  sorry

/-- God's number is `n³ + O(n^(8/3) (log n)^(1/3))`. -/
theorem gods_number :
    (fun n : ℕ => godsNumber n - (n : ℝ) ^ 3) =O[atTop] hubError := by
  sorry

/-- Any exponent above `8/3` works; in particular `27/10 < 11/4`. -/
theorem average_optimal_length_rpow {α : ℝ} (hα : 8 / 3 < α) :
    (fun n : ℕ => averageOptimalLength n - (2 / 3 : ℝ) * (n : ℝ) ^ 3)
      =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) α) := by
  sorry

theorem gods_number_rpow {α : ℝ} (hα : 8 / 3 < α) :
    (fun n : ℕ => godsNumber n - (n : ℝ) ^ 3) =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) α) := by
  sorry

end SlidingPuzzle.Hub
