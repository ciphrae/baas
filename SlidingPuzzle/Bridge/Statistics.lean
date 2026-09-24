import SlidingPuzzle.Bridge.Distance
import SlidingPuzzle.Bridge.Words
import SlidingPuzzle.StatisticalBounds
import Zhong.Uniform
import Zhong.Extremal

/-! Statistics of the reachable sliding-puzzle orbit, identified with Zhong's orbit. -/

open Filter

namespace SlidingPuzzle

noncomputable section

variable (n : ℕ) [NeZero n]

private theorem reachable_iff_mem_zhong_orbit (B : Board n) :
    Reachable B ↔ B ∈ Zhong.orbit (Zhong.target n n) := by
  rw [Zhong.orbit]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact reachable_iff_zhong

private theorem sum_reachable_eq_sum_zhong_orbit (f : Board n → ℝ) :
    (∑ B : ReachableBoard n, f B.val) =
      ∑ B ∈ Zhong.orbit (Zhong.target n n), f B := by
  classical
  symm
  exact Finset.sum_subtype _ (fun B => (reachable_iff_mem_zhong_orbit n B).symm) f

private theorem card_reachable_eq_card_zhong_orbit :
    Fintype.card (ReachableBoard n) = (Zhong.orbit (Zhong.target n n)).card := by
  classical
  have h := Finset.sum_subtype (F := inferInstanceAs (Fintype (ReachableBoard n))) (Zhong.orbit (Zhong.target n n))
    (fun B => (reachable_iff_mem_zhong_orbit n B).symm) (fun _ : Board n => (1 : ℕ))
  simpa using h.symm

/-- The uniform real mean on the reachable orbit is Zhong's rational orbit average. -/
theorem orbitAverageManhattan_eq_zhong_avgD :
    orbitAverageManhattan n = (Zhong.avgD (Zhong.target n n) : ℝ) := by
  classical
  unfold orbitAverageManhattan finiteMean Zhong.avgD
  rw [sum_reachable_eq_sum_zhong_orbit n (fun B => (manhattan B : ℝ)),
    card_reachable_eq_card_zhong_orbit n]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro B _
  rw [manhattan_eq_zhong_D]

/-- Explicit bounds for the mean Manhattan distance for every valid size. -/
theorem averageManhattan_bounds (hn : 2 ≤ n) :
    (2 / 3 : ℝ) * (n : ℝ) ^ 3 - (8 / 3 : ℝ) * (n : ℝ) + 2 ≤ averageManhattan n ∧
      averageManhattan n ≤ (2 / 3 : ℝ) * (n : ℝ) ^ 3 - (2 / 3 : ℝ) * (n : ℝ) := by
  rw [averageManhattan_of_two_le n hn, orbitAverageManhattan_eq_zhong_avgD n]
  have h := Zhong.avgD_target_bounds (n := n) (by omega : 1 < n)
  constructor
  · have h' := (Rat.cast_le (K := ℝ)).mpr h.1
    push_cast at h'
    exact h'
  · have h' := (Rat.cast_le (K := ℝ)).mpr h.2
    push_cast at h'
    exact h'

/-- A quadratic error bound for the average Manhattan distance. -/
theorem averageManhattan_error_bound (hn : 2 ≤ n) :
    |averageManhattan n - (2 / 3 : ℝ) * (n : ℝ) ^ 3| ≤ 3 * (n : ℝ) ^ 2 := by
  obtain ⟨hlo, hhi⟩ := averageManhattan_bounds n hn
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (n : ℝ)]

/-- The mean error bound holds eventually, with threshold `2`. -/
theorem averageManhattan_error_eventually :
    ∀ᶠ n : ℕ in atTop,
      |averageManhattan n - (2 / 3 : ℝ) * (n : ℝ) ^ 3| ≤ 3 * (n : ℝ) ^ 2 := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  let : NeZero n := ⟨by omega⟩
  exact averageManhattan_error_bound n hn

/-- The reachable maximum has Zhong's extremal lower bound. -/
theorem maximumManhattan_lower_bound (hn : 3 ≤ n) :
    (n : ℝ) ^ 3 - 3 * (n : ℝ) ^ 2 ≤ maximumManhattan n := by
  obtain ⟨B, hB, hD⟩ := Zhong.exists_orbit_D_ge (n := n) hn
  let C : ReachableBoard n := ⟨B, (reachable_iff_mem_zhong_orbit n B).mpr hB⟩
  rw [maximumManhattan_of_two_le n (by omega : 2 ≤ n)]
  calc
    (n : ℝ) ^ 3 - 3 * (n : ℝ) ^ 2 ≤ (manhattan C.val : ℝ) := by
      rw [manhattan_eq_zhong_D]
      have hD' : (n : ℝ)^3 ≤ (Zhong.D B : ℝ) + 3 * (n : ℝ)^2 := by exact_mod_cast hD
      change (n : ℝ)^3 - 3 * (n : ℝ)^2 ≤ (Zhong.D B : ℝ)
      linarith
    _ ≤ orbitMaximumManhattan n :=
      le_finiteMaximum (fun D : ReachableBoard n => (manhattan D.val : ℝ)) C

/-- A quadratic error bound for the maximum Manhattan distance. -/
theorem maximumManhattan_error_bound (hn : 3 ≤ n) :
    |maximumManhattan n - (n : ℝ) ^ 3| ≤ 3 * (n : ℝ) ^ 2 := by
  apply maximumManhattan_abs_error_le
  exact maximumManhattan_lower_bound n hn

/-- The maximum error bound holds eventually, with threshold `3`. -/
theorem maximumManhattan_error_eventually :
    ∀ᶠ n : ℕ in atTop,
      |maximumManhattan n - (n : ℝ) ^ 3| ≤ 3 * (n : ℝ) ^ 2 := by
  filter_upwards [eventually_ge_atTop 3] with n hn
  let : NeZero n := ⟨by omega⟩
  exact maximumManhattan_error_bound n hn

end

end SlidingPuzzle
