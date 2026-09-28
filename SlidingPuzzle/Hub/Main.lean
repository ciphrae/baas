import SlidingPuzzle.Hub.LinError
import SlidingPuzzle.Hub.AsympStats
import SlidingPuzzle.Bridge.Statistics

/-! # Main results: error `O(n^(8/3))`

With `k ≍ n^(1/3)` and `s = ⌊n/k⌋`, the hub algorithm on the `k*s × k*s`
residual board costs `O(n³/k + k²n²)` inefficient moves: the in-flight budget
is linear in `n` (segmented residence, `Hub/InFlightSegment.lean`). The outer
`n - k*s < k` layers are solved by the Parberry prefix (`Parberry/Prefix.lean`).
Hence the mean optimal solution length is `(2/3)n³ + O(n^(8/3))` and God's
number is `n³ + O(n^(8/3))`, improving Zhong's `O(n^(11/4))`.

Explicitly, `OPT(B) ≤ M(B) + 520 n^(8/3)` for every reachable board with
`n ≥ 10⁹` (`uniform_approximation_explicit`). -/
open Filter Asymptotics

set_option maxRecDepth 4096

namespace SlidingPuzzle.Hub

/-- The uniform coefficient of `n^(8/3)`: the hub algorithm from `hubN = linN = 10⁹` on
(`optimalLength_le_linError`). -/
def linConstant : ℕ := 520

theorem linConstant_eq : linConstant = 520 := rfl

/-- **The boardwise bound**: `OPT(B) ≤ M(B) + 520 n^(8/3)` for every `n ≥ 10⁹`. -/
theorem uniform_approximation_explicit {n : ℕ} [NeZero n]
    (hn : hubN ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) + linConstant * linError n := by
  unfold linConstant
  exact_mod_cast optimalLength_le_linError (by unfold linN; unfold hubN at hn; omega) B

/-- The boardwise bound `OPT(B) ≤ M(B) + C n^(8/3)`. -/
theorem uniform_approximation :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (hn : 2 ≤ n),
      letI : NeZero n := ⟨by omega⟩
      ∀ B : ReachableBoard n,
        (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) + C * linError n := by
  refine ⟨(linConstant : ℝ), by positivity, hubN, ?_⟩
  intro n hn hn2
  let : NeZero n := ⟨by omega⟩
  exact fun B => uniform_approximation_explicit hn B

theorem sq_le_linError {n : ℕ} (hn : 1 ≤ n) : (n : ℝ) ^ 2 ≤ linError n := by
  rw [linError_eq]
  have hx0 := cbrtN_nonneg n
  have hx3 := cbrtN_cube n
  have hx1 : 1 ≤ cbrtN n := by
    apply le_of_cube_le hx0; rw [hx3]; norm_num; exact_mod_cast hn
  rw [← hx3]
  have : (cbrtN n ^ 3) ^ 2 = cbrtN n ^ 6 * 1 := by ring
  rw [this]
  have h8 : cbrtN n ^ 8 = cbrtN n ^ 6 * cbrtN n ^ 2 := by ring
  rw [h8]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  nlinarith

theorem sq_le_linError_eventually : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 ≤ linError n := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact sq_le_linError hn

/-- The average optimal solution length is `(2/3)n³ + O(n^(8/3))`. -/
theorem average_optimal_length :
    (fun n : ℕ => averageOptimalLength n - (2 / 3 : ℝ) * (n : ℝ) ^ 3) =O[atTop]
      (fun n : ℕ => Real.rpow (n : ℝ) (8 / 3 : ℝ)) := by
  exact average_optimal_length_of_approximation_with sq_le_linError_eventually
    uniform_approximation ⟨3, by norm_num, averageManhattan_error_eventually⟩

/-- God's number is `n³ + O(n^(8/3))`. -/
theorem gods_number :
    (fun n : ℕ => godsNumber n - (n : ℝ) ^ 3) =O[atTop]
      (fun n : ℕ => Real.rpow (n : ℝ) (8 / 3 : ℝ)) := by
  exact gods_number_of_approximation_with sq_le_linError_eventually
    uniform_approximation ⟨3, by norm_num, maximumManhattan_error_eventually⟩

/-- `n^(8/3) = O(n^α)` for every `α ≥ 8/3`. -/
theorem rpow_isBigO_rpow {α : ℝ} (hα : 8 / 3 ≤ α) :
    (fun n : ℕ => Real.rpow (n : ℝ) (8 / 3 : ℝ)) =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) α) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (0 : ℝ) ≤ Real.rpow (n : ℝ) (8 / 3 : ℝ) := Real.rpow_nonneg (by positivity) _
  have h2 : (0 : ℝ) ≤ Real.rpow (n : ℝ) α := Real.rpow_nonneg (by positivity) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1, abs_of_nonneg h2, one_mul]
  exact Real.rpow_le_rpow_of_exponent_le hnR hα

/-- In particular `8/3 < 11/4`: any exponent `α ≥ 8/3` works. -/
theorem average_optimal_length_rpow {α : ℝ} (hα : 8 / 3 ≤ α) :
    (fun n : ℕ => averageOptimalLength n - (2 / 3 : ℝ) * (n : ℝ) ^ 3)
      =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) α) :=
  average_optimal_length.trans (rpow_isBigO_rpow hα)

theorem gods_number_rpow {α : ℝ} (hα : 8 / 3 ≤ α) :
    (fun n : ℕ => godsNumber n - (n : ℝ) ^ 3) =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) α) :=
  gods_number.trans (rpow_isBigO_rpow hα)

end SlidingPuzzle.Hub
