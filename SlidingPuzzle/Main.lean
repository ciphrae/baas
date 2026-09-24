import SlidingPuzzle.Algorithm.GeneralSize
import SlidingPuzzle.Bridge.Statistics

/-! # Proposition 9

Zhixian Zhong, *Additive Approximation Algorithms for Sliding Puzzle* (2023),
Proposition 9 (§5.2). Over the reachable orbit of the standard target, the mean
optimal solution length is `(2/3)*n³ + O(n^(11/4))` and the maximum (God's
number) is `n³ + O(n^(11/4))`.

The boardwise bound `Algorithm.uniformApproximation` comes from the partition
algorithm; `Algorithm.exists_solution_explicit` states it with explicit
constants. The Manhattan estimates come from `Bridge.Statistics`. -/
open Filter Asymptotics

namespace SlidingPuzzle

/-- The average optimal solution length differs from `(2/3)*n³` by `O(n^(11/4))`. -/
theorem average_optimal_length :
    (fun n : ℕ => averageOptimalLength n - (2 / 3 : ℝ)*(n : ℝ)^3)
      =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) (11 / 4 : ℝ)) :=
  average_optimal_length_of_approximation Algorithm.uniformApproximation
    ⟨3, by norm_num, averageManhattan_error_eventually⟩

/-- God's number differs from `n³` by `O(n^(11/4))`. -/
theorem gods_number :
    (fun n : ℕ => godsNumber n - (n : ℝ)^3)
      =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) (11 / 4 : ℝ)) :=
  gods_number_of_approximation Algorithm.uniformApproximation
    ⟨3, by norm_num, maximumManhattan_error_eventually⟩

/-- Both conclusions of Proposition 9. -/
theorem proposition9 :
    ((fun n : ℕ => averageOptimalLength n - (2 / 3 : ℝ)*(n : ℝ)^3)
      =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) (11 / 4 : ℝ))) ∧
    ((fun n : ℕ => godsNumber n - (n : ℝ)^3)
      =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) (11 / 4 : ℝ))) :=
  ⟨average_optimal_length, gods_number⟩

end SlidingPuzzle
