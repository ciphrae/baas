import SlidingPuzzle.Statistics
import SlidingPuzzle.Manhattan

/-! # Orbit statistics from a boardwise approximation, for any error scale

The statistical reduction of Zhong (2023), Section 5, for an arbitrary error scale:
`f` need only satisfy `n² ≤ f n` eventually. -/

open Filter Asymptotics

namespace SlidingPuzzle.Hub

/-- The boardwise bound `OPT(B) ≤ M(B) + C f(n)` for all large sizes. -/
def UniformApproximationWith (f : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (hn : 2 ≤ n),
    letI : NeZero n := ⟨by omega⟩
    ∀ B : ReachableBoard n,
      (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) + C * f n

theorem uniform_approximation_statistics_with {f : ℕ → ℝ}
    (happrox : UniformApproximationWith f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      (averageManhattan n ≤ averageOptimalLength n ∧
        averageOptimalLength n ≤ averageManhattan n + C * f n) ∧
      (maximumManhattan n ≤ godsNumber n ∧
        godsNumber n ≤ maximumManhattan n + C * f n) := by
  obtain ⟨C, hC, N, hN⟩ := happrox
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 2] with n hn hn2
  let : NeZero n := ⟨by omega⟩
  apply statistics_sandwich n hn2
  · intro B
    exact_mod_cast manhattan_le_optimalLength B
  · exact hN n hn hn2

/-- A quadratic error plus the error scale is of the order of the error scale. -/
theorem error_isBigO_of_sq_le (f : ℕ → ℝ) (hf : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 ≤ f n)
    (g baseline : ℕ → ℝ) (C K : ℝ) (hC : 0 ≤ C)
    (h : ∀ᶠ n in atTop, |g n - baseline n| ≤ C * (n : ℝ) ^ 2 + K * f n) :
    (fun n => g n - baseline n) =O[atTop] f := by
  apply Asymptotics.IsBigO.of_bound (C + K)
  filter_upwards [h, hf] with n hn hfn
  have hp : 0 ≤ f n := le_trans (by positivity) hfn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp]
  nlinarith [mul_le_mul_of_nonneg_left hfn hC]

theorem average_optimal_length_of_approximation_with {f : ℕ → ℝ}
    (hf : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 ≤ f n) (happrox : UniformApproximationWith f)
    (hmean : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      |averageManhattan n - (2 / 3 : ℝ) * (n : ℝ) ^ 3| ≤ C * (n : ℝ) ^ 2) :
    (fun n : ℕ => averageOptimalLength n - (2 / 3 : ℝ) * (n : ℝ) ^ 3) =O[atTop] f := by
  obtain ⟨C, hC, hmean⟩ := hmean
  obtain ⟨K, hK, hstats⟩ := uniform_approximation_statistics_with happrox
  apply error_isBigO_of_sq_le f hf _ _ C K hC
  filter_upwards [hmean, hstats, hf] with n hn hs hfn
  have hp : 0 ≤ K * f n := mul_nonneg hK (le_trans (by positivity) hfn)
  obtain ⟨hlo, hhi⟩ := abs_le.mp hn
  apply abs_le.mpr
  constructor <;> linarith [hs.1.1, hs.1.2]

theorem gods_number_of_approximation_with {f : ℕ → ℝ}
    (hf : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 ≤ f n) (happrox : UniformApproximationWith f)
    (hmax : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      |maximumManhattan n - (n : ℝ) ^ 3| ≤ C * (n : ℝ) ^ 2) :
    (fun n : ℕ => godsNumber n - (n : ℝ) ^ 3) =O[atTop] f := by
  obtain ⟨C, hC, hmax⟩ := hmax
  obtain ⟨K, hK, hstats⟩ := uniform_approximation_statistics_with happrox
  apply error_isBigO_of_sq_le f hf _ _ C K hC
  filter_upwards [hmax, hstats, hf] with n hn hs hfn
  have hp : 0 ≤ K * f n := mul_nonneg hK (le_trans (by positivity) hfn)
  obtain ⟨hlo, hhi⟩ := abs_le.mp hn
  apply abs_le.mpr
  constructor <;> linarith [hs.2.1, hs.2.2]

end SlidingPuzzle.Hub
