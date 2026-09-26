import SlidingPuzzle

/-! Axiom audit. Each result below should depend only on `propext`,
`Classical.choice` and `Quot.sound`. Run with `lake env lean Checks/Axioms.lean`. -/

-- Proposition 9
#print axioms SlidingPuzzle.proposition9
#print axioms SlidingPuzzle.average_optimal_length
#print axioms SlidingPuzzle.gods_number

-- The better exponent: O(n^(8/3) (log n)^(1/3)) by hub transport (SlidingPuzzle/Hub)
#print axioms SlidingPuzzle.Hub.uniform_approximation
#print axioms SlidingPuzzle.Hub.average_optimal_length
#print axioms SlidingPuzzle.Hub.gods_number
#print axioms SlidingPuzzle.Hub.average_optimal_length_rpow
#print axioms SlidingPuzzle.Hub.gods_number_rpow
#print axioms SlidingPuzzle.Hub.exists_hub_solution

-- The boardwise bounds
#print axioms SlidingPuzzle.Algorithm.uniformApproximation
#print axioms SlidingPuzzle.Algorithm.exists_solution_two_level
#print axioms SlidingPuzzle.Algorithm.exists_solution_explicit
#print axioms SlidingPuzzle.Algorithm.exists_admissible_solution
#print axioms SlidingPuzzle.Algorithm.exists_admissible_solution_of_solver_ineff

-- The four phases
#print axioms SlidingPuzzle.Algorithm.preparation_phase
#print axioms SlidingPuzzle.Algorithm.transport_phase
#print axioms SlidingPuzzle.Algorithm.arrangement_bound
#print axioms SlidingPuzzle.Algorithm.finish_bound

-- Foundations
#print axioms SlidingPuzzle.Path.length_add_manhattan
#print axioms SlidingPuzzle.manhattan_le_optimalLength
#print axioms SlidingPuzzle.Parberry.exists_solution_cubic
#print axioms SlidingPuzzle.averageManhattan_error_eventually
#print axioms SlidingPuzzle.maximumManhattan_error_eventually
