import SlidingPuzzle.Basic

namespace SlidingPuzzle

/-- Sum of distances from the integer midpoint of a row. -/
def midpointDeviation (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, Nat.dist i (n / 2)

theorem midpointDeviation_add_two (n : ℕ) :
    midpointDeviation (n + 2) = midpointDeviation n + n + 1 := by
  have hhalf : (n + 2) / 2 = n / 2 + 1 := by omega
  have hle : n / 2 ≤ n := Nat.div_le_self _ _
  unfold midpointDeviation
  rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ']
  simp only [hhalf, Nat.dist_succ_succ]
  rw [Finset.sum_range_succ]
  simp only [Nat.dist_zero_left, Nat.dist_eq_sub_of_le_right hle]
  omega

/-- Exact finite absolute-deviation formula, uniform across both parities. -/
theorem midpointDeviation_exact (n : ℕ) :
    4 * midpointDeviation n + n % 2 = n * n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [midpointDeviation]
  | one => simp [midpointDeviation]
  | more n ih _ =>
      rw [midpointDeviation_add_two]
      have hmod : (n + 2) % 2 = n % 2 := by omega
      rw [hmod]
      nlinarith

theorem midpointDeviation_le (n : ℕ) : 4 * midpointDeviation n ≤ n * n := by
  have h := midpointDeviation_exact n
  omega

/-- Distance to the coordinatewise integer midpoint. -/
def midpointDistance {n : ℕ} (c : Cell n) : ℕ :=
  Nat.dist c.1.val (n / 2) + Nat.dist c.2.val (n / 2)

theorem gridDistance_le_midpoint {n : ℕ} (a b : Cell n) :
    gridDistance a b ≤ midpointDistance a + midpointDistance b := by
  have h₁ := Nat.dist.triangle_inequality a.1.val (n / 2) b.1.val
  have h₂ := Nat.dist.triangle_inequality a.2.val (n / 2) b.2.val
  rw [Nat.dist_comm (n / 2)] at h₁ h₂
  unfold gridDistance midpointDistance
  omega

theorem sum_midpointDistance (n : ℕ) :
    ∑ c : Cell n, midpointDistance c = 2 * n * midpointDeviation n := by
  simp only [midpointDistance, Fintype.sum_prod_type, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun i => Nat.dist i (n / 2)) n]
  change n * midpointDeviation n + n * midpointDeviation n = _
  ring

theorem sum_position_midpointDistance {n : ℕ} (B : Board n) :
    ∑ t : Tile n, midpointDistance (position B t) = 2 * n * midpointDeviation n := by
  change (∑ t : Tile n, midpointDistance (B.symm t)) = _
  rw [B.symm.sum_comp midpointDistance]
  exact sum_midpointDistance n

/-- The coordinatewise midpoint gives a bound independent of the board permutation. -/
theorem manhattan_le_midpoint {n : ℕ} (B : Board n) :
    manhattan B ≤ 4 * n * midpointDeviation n := by
  calc
    manhattan B ≤ ∑ t : Tile n,
        (midpointDistance (position B t) + midpointDistance (position (target n) t)) := by
      apply Finset.sum_le_sum
      intro t _
      split_ifs
      · exact Nat.zero_le _
      · exact gridDistance_le_midpoint _ _
    _ = 4 * n * midpointDeviation n := by
      rw [Finset.sum_add_distrib, sum_position_midpointDistance,
        sum_position_midpointDistance]
      ring

/-- Every board has Manhattan potential at most the cube of the side length. -/
theorem manhattan_le_cube {n : ℕ} (B : Board n) : manhattan B ≤ n ^ 3 := by
  have h := manhattan_le_midpoint B
  have h' := Nat.mul_le_mul_left n (midpointDeviation_le n)
  nlinarith

theorem manhattan_le_cube_real {n : ℕ} (B : Board n) :
    (manhattan B : ℝ) ≤ (n : ℝ) ^ 3 := by
  exact_mod_cast manhattan_le_cube B

end SlidingPuzzle
