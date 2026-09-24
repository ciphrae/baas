import SlidingPuzzle.Manhattan
import SlidingPuzzle.DistanceEstimates
import SlidingPuzzle.Statistics

/-! Unconditional statistical consequences of the proved boardwise bounds. -/
namespace SlidingPuzzle

/-- Manhattan distance lower-bounds the mean solution length at every size. -/
theorem averageManhattan_le_averageOptimalLength (n : ℕ) :
    averageManhattan n ≤ averageOptimalLength n := by
  by_cases hn : 2 ≤ n
  · let : NeZero n := ⟨by omega⟩
    rw [averageManhattan_of_two_le n hn, averageOptimalLength_of_two_le n hn]
    exact finiteMean_mono fun B => by exact_mod_cast manhattan_le_optimalLength B
  · simp [averageManhattan_of_lt_two (by omega : n < 2),
      averageOptimalLength_of_lt_two (by omega : n < 2)]

/-- Manhattan distance lower-bounds God's number at every size. -/
theorem maximumManhattan_le_godsNumber (n : ℕ) : maximumManhattan n ≤ godsNumber n := by
  by_cases hn : 2 ≤ n
  · let : NeZero n := ⟨by omega⟩
    rw [maximumManhattan_of_two_le n hn, godsNumber_of_two_le n hn]
    exact finiteMaximum_mono fun B => by exact_mod_cast manhattan_le_optimalLength B
  · simp [maximumManhattan_of_lt_two (by omega : n < 2),
      godsNumber_of_lt_two (by omega : n < 2)]

/-- The maximum Manhattan distance over the reachable orbit obeys the cubic bound. -/
theorem maximumManhattan_le_cube (n : ℕ) : maximumManhattan n ≤ (n : ℝ) ^ 3 := by
  by_cases hn : 2 ≤ n
  · let : NeZero n := ⟨by omega⟩
    rw [maximumManhattan_of_two_le n hn]
    exact finiteMaximum_le fun B => manhattan_le_cube_real B.val
  · rw [maximumManhattan_of_lt_two (by omega : n < 2)]
    positivity

/-- Only the reachable lower bound remains to prove the maximum distance error. -/
theorem maximumManhattan_abs_error_le {n : ℕ} {E : ℝ}
    (hlo : (n : ℝ) ^ 3 - E ≤ maximumManhattan n) :
    |maximumManhattan n - (n : ℝ) ^ 3| ≤ E := by
  rw [abs_of_nonpos (sub_nonpos.mpr (maximumManhattan_le_cube n))]
  linarith

end SlidingPuzzle
