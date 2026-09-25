import SlidingPuzzle.Algorithm.Partition

/-! Preparation step (iii): spread vertical quotas while preserving horizontal
corridors and the explicit representative row. The staged columns `i < k³`
move to the vertical corridor columns `i/k²*s + i%k²`, `s = side n k`. -/
namespace SlidingPuzzle.Partition
noncomputable section

/-- Destination of a compressed column in a vertical data band. -/
def verticalDestination (s k i : ℕ) : ℕ := i/k^2*s+i%k^2

/-- The data rows in the `a`-th block row, excluding horizontal corridors. -/
def verticalPreparationBand {n : ℕ} (k a : ℕ) (c : Cell n) : Prop :=
  a*side n k+2*k ≤ c.1.val ∧ c.1.val < (a+1)*side n k

theorem vertical_geometry {n k : ℕ} (hk : Dims n k) :
    4 ≤ k^2 ∧ 2*k^2 ≤ k^3 ∧ k+2 ≤ side n k ∧ k^3 ≤ n ∧ 2*k^2 ≤ side n k := by
  obtain ⟨hk2, hsq, htwo, hs3, -⟩ := hk.facts
  have := hk.k_add_two_le
  have := hk.cube_le_n
  omega

theorem verticalDestination_strictMono {s k : ℕ} (hk : 2 ≤ k) (hs : k^2 ≤ s) :
    StrictMono (verticalDestination s k) := by
  intro i j hij
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
      verticalDestination s k i < i/k^2*s+s := by unfold verticalDestination; omega
      _ = (i/k^2+1)*s := by ring
      _ ≤ j/k^2*s := Nat.mul_le_mul_right _ hdiv'
      _ ≤ verticalDestination s k j := Nat.le_add_right _ _

theorem verticalDestination_bounds {n k : ℕ} (hk : Dims n k)
    (i : ℕ) (hi : i < k^3) :
    i ≤ verticalDestination (side n k) k i ∧ verticalDestination (side n k) k i < n-k^2 ∧
      verticalDestination (side n k) k i+3 ≤ n := by
  have hg := vertical_geometry hk
  have hk2 := hk.two_le
  have hid := Nat.div_add_mod' i (k^2)
  have himod := Nat.mod_lt i (by positivity : 0 < k^2)
  have hidiv : i/k^2 < k := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    simpa only [show k*k^2 = k^3 by ring] using hi
  have hmul := Nat.mul_le_mul_left (i/k^2) (show k^2 ≤ side n k by omega)
  have hblock : i/k^2*side n k+side n k ≤ n := by
    calc
      i/k^2*side n k+side n k = (i/k^2+1)*side n k := by ring
      _ ≤ k*side n k := Nat.mul_le_mul_right _ hidiv
      _ = n := hk.mul_side
  unfold verticalDestination
  omega

theorem verticalPreparationBand_unique {n k a b : ℕ} {c : Cell n}
    (ha : verticalPreparationBand k a c) (hb : verticalPreparationBand k b c) : a = b := by
  have hda : c.1.val/side n k = a := Nat.div_eq_of_lt_le (by have := ha.1; omega) ha.2
  have hdb : c.1.val/side n k = b := Nat.div_eq_of_lt_le (by have := hb.1; omega) hb.2
  exact hda.symm.trans hdb

end
end SlidingPuzzle.Partition
