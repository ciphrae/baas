import SlidingPuzzle.Statistics
import SlidingPuzzle.Manhattan
import SlidingPuzzle.Asymptotics

/-! Conditional assembly of Proposition 9. The approximation algorithm and the
Manhattan statistical estimates remain explicit hypotheses. This file does not
claim an unconditional solution of those mathematical obligations. -/

open Filter Asymptotics

namespace SlidingPuzzle

/-- The algorithmic obligation: a single additive constant and size threshold
work for every reachable board of every sufficiently large valid dimension. -/
def UniformApproximation : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (hn : 2 ≤ n),
    letI : NeZero n := ⟨by omega⟩
    ∀ B : ReachableBoard n,
      (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
        C * Real.rpow (n : ℝ) (11 / 4 : ℝ)

/-- A uniform boardwise approximation bounds both orbit statistics, eventually
using only valid dimensions. The lower bounds use the proved potential bound. -/
theorem uniform_approximation_statistics (happrox : UniformApproximation) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      (averageManhattan n ≤ averageOptimalLength n ∧
        averageOptimalLength n ≤ averageManhattan n +
          C * Real.rpow (n : ℝ) (11 / 4 : ℝ)) ∧
      (maximumManhattan n ≤ godsNumber n ∧
        godsNumber n ≤ maximumManhattan n +
          C * Real.rpow (n : ℝ) (11 / 4 : ℝ)) := by
  obtain ⟨C, hC, N, hN⟩ := happrox
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 2] with n hn hn2
  let : NeZero n := ⟨by omega⟩
  apply statistics_sandwich n hn2
  · intro B
    exact_mod_cast manhattan_le_optimalLength B
  · exact hN n hn hn2

/-- Conditional average statement. Its two inputs are the uniform algorithmic
bound and a quadratic error estimate for the mean Manhattan distance. -/
theorem conditional_average_optimal_length (happrox : UniformApproximation)
    (hmean : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      |averageManhattan n - (2 / 3 : ℝ) * (n : ℝ) ^ 3| ≤ C * (n : ℝ) ^ 2) :
    (fun n : ℕ => averageOptimalLength n - (2 / 3 : ℝ) * (n : ℝ) ^ 3)
      =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) (11 / 4 : ℝ)) := by
  obtain ⟨C, hC, hmean⟩ := hmean
  obtain ⟨K, hK, hstats⟩ := uniform_approximation_statistics happrox
  apply error_isBigO_rpow_eleven_fourths _ _ C K hC
  filter_upwards [hmean, hstats] with n hn hs
  have hp : 0 ≤ K * Real.rpow (n : ℝ) (11 / 4 : ℝ) :=
    mul_nonneg hK (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  obtain ⟨hlo, hhi⟩ := abs_le.mp hn
  apply abs_le.mpr
  constructor <;> linarith [hs.1.1, hs.1.2]

/-- Conditional maximum statement. In particular its Manhattan hypothesis is
about reachable boards, as required by the definition of `maximumManhattan`. -/
theorem conditional_gods_number (happrox : UniformApproximation)
    (hmax : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      |maximumManhattan n - (n : ℝ) ^ 3| ≤ C * (n : ℝ) ^ 2) :
    (fun n : ℕ => godsNumber n - (n : ℝ) ^ 3)
      =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) (11 / 4 : ℝ)) := by
  obtain ⟨C, hC, hmax⟩ := hmax
  obtain ⟨K, hK, hstats⟩ := uniform_approximation_statistics happrox
  apply error_isBigO_rpow_eleven_fourths _ _ C K hC
  filter_upwards [hmax, hstats] with n hn hs
  have hp : 0 ≤ K * Real.rpow (n : ℝ) (11 / 4 : ℝ) :=
    mul_nonneg hK (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  obtain ⟨hlo, hhi⟩ := abs_le.mp hn
  apply abs_le.mpr
  constructor <;> linarith [hs.2.1, hs.2.2]

end SlidingPuzzle
