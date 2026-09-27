import SlidingPuzzle

/-! Axiom audit. Each result below should depend only on `propext`,
`Classical.choice` and `Quot.sound`. Run with `lake env lean Checks/Axioms.lean`. -/

-- Main results: O(n^(8/3) (log n)^(1/3)) by hub transport
#print axioms SlidingPuzzle.Hub.average_optimal_length
#print axioms SlidingPuzzle.Hub.gods_number
#print axioms SlidingPuzzle.Hub.average_optimal_length_rpow
#print axioms SlidingPuzzle.Hub.gods_number_rpow

-- The boardwise bounds
#print axioms SlidingPuzzle.Hub.uniform_approximation
#print axioms SlidingPuzzle.Hub.uniform_approximation_explicit
#print axioms SlidingPuzzle.Hub.hubLargeConstant_rounding
#print axioms SlidingPuzzle.Hub.exists_hub_solution

-- Foundations
#print axioms SlidingPuzzle.Path.length_add_manhattan
#print axioms SlidingPuzzle.manhattan_le_optimalLength
#print axioms SlidingPuzzle.Parberry.exists_solution_cubic
#print axioms SlidingPuzzle.averageManhattan_error_eventually
#print axioms SlidingPuzzle.maximumManhattan_error_eventually
