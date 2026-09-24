import SlidingPuzzle.Algorithm.PreparationHorizontal
import SlidingPuzzle.Moves.ColumnSchedule

/-! Preparation step (iii): spread vertical quotas while preserving horizontal
corridors and the explicit representative row. -/
namespace SlidingPuzzle.Partition
noncomputable section

/-- Destination of a compressed column in a vertical data band. -/
def verticalDestination (k i : ℕ) : ℕ := i/k^2*k^3+i%k^2

/-- The data rows in the `a`-th block row, excluding horizontal corridors. -/
def verticalPreparationBand {n : ℕ} (k a : ℕ) (c : Cell n) : Prop :=
  a*k^3+k ≤ c.1.val ∧ c.1.val < (a+1)*k^3

theorem vertical_geometry {k : ℕ} (hk : 2 ≤ k) :
    4 ≤ k^2 ∧ 2*k^2 ≤ k^3 ∧ k+2 ≤ k^3 ∧ k^3 ≤ k^4 := by
  have hsq : 4 ≤ k^2 := by nlinarith
  have hksq : k ≤ k^2 := by nlinarith
  have htwo : 2*k^2 ≤ k^3 := by
    calc
      2*k^2 ≤ k*k^2 := Nat.mul_le_mul_right _ hk
      _ = k^3 := by ring
  have hfour : k^3 ≤ k^4 := by
    calc
      k^3 ≤ k*k^3 := Nat.le_mul_of_pos_left _ (by omega)
      _ = k^4 := by ring
  omega

theorem verticalDestination_strictMono {k : ℕ} (hk : 2 ≤ k) :
    StrictMono (verticalDestination k) := by
  intro i j hij
  have hg := vertical_geometry hk
  have hi := Nat.mod_lt i (by positivity : 0 < k^2)
  have hj := Nat.mod_lt j (by positivity : 0 < k^2)
  have hid := Nat.div_add_mod' i (k^2)
  have hjd := Nat.div_add_mod' j (k^2)
  have hdiv : i/k^2 ≤ j/k^2 := Nat.div_le_div_right hij.le
  by_cases he : i/k^2 = j/k^2
  · unfold verticalDestination
    rw [he] at hid ⊢
    omega
  · have hdiv' : i/k^2+1 ≤ j/k^2 := by omega
    calc
      verticalDestination k i < i/k^2*k^3+k^3 := by unfold verticalDestination; omega
      _ = (i/k^2+1)*k^3 := by ring
      _ ≤ j/k^2*k^3 := Nat.mul_le_mul_right _ hdiv'
      _ ≤ verticalDestination k j := Nat.le_add_right _ _

theorem verticalDestination_bounds {k : ℕ} (hk : 2 ≤ k)
    (i : ℕ) (hi : i < k^3) :
    i ≤ verticalDestination k i ∧ verticalDestination k i < k^4-k^2 ∧
      verticalDestination k i+3 ≤ k^4 := by
  have hg := vertical_geometry hk
  have hid := Nat.div_add_mod' i (k^2)
  have himod := Nat.mod_lt i (by positivity : 0 < k^2)
  have hidiv : i/k^2 < k := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    simpa only [show k*k^2 = k^3 by ring] using hi
  have hmul := Nat.mul_le_mul_left (i/k^2) (show k^2 ≤ k^3 by omega)
  have hblock : i/k^2*k^3+k^3 ≤ k^4 := by
    calc
      i/k^2*k^3+k^3 = (i/k^2+1)*k^3 := by ring
      _ ≤ k*k^3 := Nat.mul_le_mul_right _ hidiv
      _ = k^4 := by ring
  unfold verticalDestination
  omega

theorem verticalPreparationBand_unique {n k a b : ℕ} {c : Cell n}
    (ha : verticalPreparationBand k a c) (hb : verticalPreparationBand k b c) : a = b := by
  have hda : c.1.val/k^3 = a := Nat.div_eq_of_lt_le (by have := ha.1; omega) ha.2
  have hdb : c.1.val/k^3 = b := Nat.div_eq_of_lt_le (by have := hb.1; omega) hb.2
  exact hda.symm.trans hdb

end
end SlidingPuzzle.Partition
