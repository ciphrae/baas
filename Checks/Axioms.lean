import SlidingPuzzle

/-! Axiom audit. Each result below should depend only on `propext`,
`Classical.choice` and `Quot.sound`. Run with `lake env lean Checks/Axioms.lean`. -/

-- Main results: error n^(5/2) (ln n)^(3/2)
#print axioms SlidingPuzzle.Tree.tree_log_approximation_explicit
#print axioms SlidingPuzzle.Tree.tree_log_average_optimal_length
#print axioms SlidingPuzzle.Tree.tree_log_gods_number

-- Fixed depth: exponent 5/2 + 1/(4h+2), and 5/2 + ε
#print axioms SlidingPuzzle.Tree.tree_uniform_approximation_explicit
#print axioms SlidingPuzzle.Tree.tree_uniform_approximation
#print axioms SlidingPuzzle.Tree.tree_exponent
#print axioms SlidingPuzzle.Tree.tree_average_optimal_length
#print axioms SlidingPuzzle.Tree.tree_gods_number

-- Ingredients
#print axioms SlidingPuzzle.Tree.optimalLength_le_lanes
#print axioms SlidingPuzzle.Tree.treeBound_le_fine
#print axioms SlidingPuzzle.Hub.exists_good_order

-- Foundations
#print axioms SlidingPuzzle.Path.length_add_manhattan
#print axioms SlidingPuzzle.manhattan_le_optimalLength
#print axioms SlidingPuzzle.Parberry.exists_solution_cubic
#print axioms SlidingPuzzle.averageManhattan_error_eventually
#print axioms SlidingPuzzle.maximumManhattan_error_eventually
