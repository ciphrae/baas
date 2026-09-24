import SlidingPuzzle.Proposition9
import SlidingPuzzle.Bridge.Statistics

/-! All orbit-statistical hypotheses in the initial assembly are now discharged.
Only the uniform additive approximation algorithm remains as an assumption. -/
open Filter Asymptotics

namespace SlidingPuzzle

/-- The average conclusion, conditional only on the still-open algorithmic bound. -/
theorem average_optimal_length_of_uniformApproximation (h : UniformApproximation) :
    (fun n : ℕ => averageOptimalLength n - (2 / 3 : ℝ) * (n : ℝ) ^ 3)
      =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) (11 / 4 : ℝ)) :=
  conditional_average_optimal_length h
    ⟨3, by norm_num, averageManhattan_error_eventually⟩

/-- The maximum conclusion, conditional only on the still-open algorithmic bound. -/
theorem gods_number_of_uniformApproximation (h : UniformApproximation) :
    (fun n : ℕ => godsNumber n - (n : ℝ) ^ 3)
      =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) (11 / 4 : ℝ)) :=
  conditional_gods_number h
    ⟨3, by norm_num, maximumManhattan_error_eventually⟩

end SlidingPuzzle
