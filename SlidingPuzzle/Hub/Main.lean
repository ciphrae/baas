import SlidingPuzzle.Hub.AsympBound
import SlidingPuzzle.Hub.AsympError
import SlidingPuzzle.Hub.AsympStats
import SlidingPuzzle.Bridge.Statistics

/-! # A better leading exponent

With `k³ ≈ n / log n` (`k` even) and `s = ⌊n/k⌋`, the hub algorithm on the
`k*s × k*s` residual board costs `O(n³/k + k²n² log n)` inefficient moves, i.e.
`O(n^(8/3) (log n)^(1/3))`; the outer `n - k*s < k` layers are solved by the
Parberry prefix (`Parberry/Prefix.lean`). Hence the mean optimal
solution length is `(2/3)n³ + O(n^(8/3) (log n)^(1/3))` and God's number is
`n³ + O(n^(8/3) (log n)^(1/3))`, improving Zhong's `O(n^(11/4))`. -/
open Filter Asymptotics

set_option maxRecDepth 4096

namespace SlidingPuzzle.Hub

/-! The error scale `hubError n = n^(8/3) (log n)^(1/3)` is defined in
`Hub/AsympError.lean`; the natural-number bound of the algorithm is
`optimalLength_le_hub` (`Hub/AsympBound.lean`). -/

/-- Round up `2·1.139524·((hubXNum/hubXDen) hubScaledKX/1000 +
(hubYNum/hubYDen) hubScaledKY/1000 + 1/1000)`, keeping the three error
coefficients separate. -/
def hubConstant : ℕ := 16656

theorem hubConstant_eq : hubConstant = 16656 := by
  rfl

/-- Integer inequalities certify the ceiling without evaluating a large division. -/
theorem hubConstant_rounding :
    2 * 1139524 * (hubXNum * hubYDen * hubScaledKX + hubYNum * hubXDen * hubScaledKY +
        hubXDen * hubYDen) ≤ 1000000000 * hubXDen * hubYDen * hubConstant ∧
      1000000000 * hubXDen * hubYDen * (hubConstant - 1) <
        2 * 1139524 * (hubXNum * hubYDen * hubScaledKX + hubYNum * hubXDen * hubScaledKY +
          hubXDen * hubYDen) := by
  norm_num [hubConstant, hubScaledKX, hubScaledKY, hubXNum, hubXDen, hubYNum, hubYDen]

/-- The optimized bound holds with `C = 16656` for every `n ≥ 4096`. -/
theorem uniform_approximation_explicit {n : ℕ} [NeZero n]
    (hn : hubN ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) + hubConstant * hubError n := by
  by_cases hlarge : hubLargeN ≤ n
  swap
  · obtain ⟨p,hp⟩ := Parberry.exists_solution_cubic B (by unfold hubN at hn; omega)
    have hopt := optimalLength_le_path_length B p
    have hnat : optimalLength B ≤ 5 * n ^ 3 + 1509 * n ^ 2 + 1505 * n + 4796 := hopt.trans hp
    have hreal : (optimalLength B : ℝ) ≤ ((5 * n ^ 3 + 1509 * n ^ 2 + 1505 * n + 4796 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have herr := cubic_solver_le_hubError (by unfold hubN at hn; omega)
      (show n ≤ 2 ^ 39 by unfold hubLargeN at hlarge; omega)
    have hM : (0 : ℝ) ≤ manhattan B.val := Nat.cast_nonneg _
    have hE := hubError_nonneg n
    norm_num [hubConstant, hubScaledKX, hubScaledKY] at *
    nlinarith
  obtain ⟨X, Y, Z, hX, hY, hZ, hopt⟩ := optimalLength_le_hub_scaled hlarge B
  have hnlarge : 2 ^ 39 ≤ n := hlarge
  have hXR := le_hubError_of_cube_grid hnlarge hX
  have hYR := le_hubError_of_cube_grid hnlarge hY
  have hZR := le_hubError_of_cube_grid hnlarge hZ
  have hoptR : 1000 * (optimalLength B : ℝ) ≤ 1000 * (manhattan B.val : ℝ) +
      2 * (hubScaledKX : ℝ) * X + 2 * (hubScaledKY : ℝ) * Y + 2000 * Z := by exact_mod_cast hopt
  have hx := mul_le_mul_of_nonneg_left hXR
    (show (0 : ℝ) ≤ hubScaledKX by positivity)
  have hy := mul_le_mul_of_nonneg_left hYR
    (show (0 : ℝ) ≤ hubScaledKY by positivity)
  have hE := hubError_nonneg n
  norm_num [hubConstant, hubScaledKX, hubScaledKY, hubXNum, hubXDen, hubYNum, hubYDen] at *
  linarith

/-- The boardwise bound `OPT(B) ≤ M(B) + C n^(8/3) (log n)^(1/3)`. -/
theorem uniform_approximation :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (hn : 2 ≤ n),
      letI : NeZero n := ⟨by omega⟩
      ∀ B : ReachableBoard n,
        (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) + C * hubError n := by
  refine ⟨(hubConstant : ℝ), by positivity, hubN, ?_⟩
  intro n hn hn2
  let : NeZero n := ⟨by omega⟩
  exact fun B => uniform_approximation_explicit hn B

/-- The average optimal solution length is `(2/3)n³ + O(n^(8/3) (log n)^(1/3))`. -/
theorem average_optimal_length :
    (fun n : ℕ => averageOptimalLength n - (2 / 3 : ℝ) * (n : ℝ) ^ 3) =O[atTop] hubError := by
  exact average_optimal_length_of_approximation_with sq_le_hubError_eventually
    uniform_approximation ⟨3, by norm_num, averageManhattan_error_eventually⟩

/-- God's number is `n³ + O(n^(8/3) (log n)^(1/3))`. -/
theorem gods_number :
    (fun n : ℕ => godsNumber n - (n : ℝ) ^ 3) =O[atTop] hubError := by
  exact gods_number_of_approximation_with sq_le_hubError_eventually
    uniform_approximation ⟨3, by norm_num, maximumManhattan_error_eventually⟩

/-- Any exponent above `8/3` works; in particular `27/10 < 11/4`. -/
theorem average_optimal_length_rpow {α : ℝ} (hα : 8 / 3 < α) :
    (fun n : ℕ => averageOptimalLength n - (2 / 3 : ℝ) * (n : ℝ) ^ 3)
      =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) α) := by
  exact average_optimal_length.trans (hubError_isBigO_rpow hα)

theorem gods_number_rpow {α : ℝ} (hα : 8 / 3 < α) :
    (fun n : ℕ => godsNumber n - (n : ℝ) ^ 3) =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) α) := by
  exact gods_number.trans (hubError_isBigO_rpow hα)

end SlidingPuzzle.Hub
