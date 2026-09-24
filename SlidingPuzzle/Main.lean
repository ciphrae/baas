import SlidingPuzzle.Proposition9Reduction
import SlidingPuzzle.Algorithm.GeneralSize

/-! Proposition 9 for the concrete sliding puzzle, with all algorithmic,
reachability, and statistical hypotheses discharged. -/
open Filter Asymptotics

namespace SlidingPuzzle

/-- The average optimal solution length differs from `(2/3)*n³` by `O(n^(11/4))`. -/
theorem average_optimal_length :
    (fun n : ℕ => averageOptimalLength n - (2 / 3 : ℝ)*(n : ℝ)^3)
      =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) (11 / 4 : ℝ)) :=
  average_optimal_length_of_uniformApproximation Algorithm.uniformApproximation_leading

/-- God's number differs from `n³` by `O(n^(11/4))`. -/
theorem gods_number :
    (fun n : ℕ => godsNumber n - (n : ℝ)^3)
      =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) (11 / 4 : ℝ)) :=
  gods_number_of_uniformApproximation Algorithm.uniformApproximation_leading

/-- Both conclusions of Zhong's Proposition 9, without remaining proof obligations. -/
theorem proposition9 :
    ((fun n : ℕ => averageOptimalLength n - (2 / 3 : ℝ)*(n : ℝ)^3)
      =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) (11 / 4 : ℝ))) ∧
    ((fun n : ℕ => godsNumber n - (n : ℝ)^3)
      =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) (11 / 4 : ℝ))) :=
  ⟨average_optimal_length, gods_number⟩

end SlidingPuzzle
