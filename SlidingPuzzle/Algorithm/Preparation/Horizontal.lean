import SlidingPuzzle.Algorithm.Preparation.Representatives
import SlidingPuzzle.Moves.RowSchedule

/-! Preparation step (ii): the complete descending horizontal-corridor schedule. -/
namespace SlidingPuzzle.Partition
noncomputable section

/-- Destination row of a horizontal corridor for squares of side `s`, extended
to natural indices. -/
def horizontalDestination (s k i : ℕ) : ℕ := i/k*s+i%k

/-- The destination rows are strictly increasing, even across square boundaries. -/
theorem horizontalDestination_strictMono {s k : ℕ} (hk : 2 ≤ k) (hs : k+3 ≤ s) :
    StrictMono (horizontalDestination s k) := by
  intro i j hij
  have hi := Nat.mod_lt i (by omega : 0 < k)
  have hj := Nat.mod_lt j (by omega : 0 < k)
  have hid := Nat.div_add_mod' i k
  have hjd := Nat.div_add_mod' j k
  have hdiv : i/k ≤ j/k := Nat.div_le_div_right hij.le
  by_cases he : i/k = j/k
  · unfold horizontalDestination
    rw [he] at hid ⊢
    omega
  · have hdiv' : i/k+1 ≤ j/k := by omega
    calc
      horizontalDestination s k i < i/k*s+s := by unfold horizontalDestination; omega
      _ = (i/k+1)*s := by ring
      _ ≤ j/k*s := Nat.mul_le_mul_right _ hdiv'
      _ ≤ horizontalDestination s k j := Nat.le_add_right _ _

private theorem horizontalDestination_bounds {n k : ℕ} (hk : Dims n k)
    (i : ℕ) (hi : i < k*k) :
    i ≤ horizontalDestination (side n k) k i ∧ horizontalDestination (side n k) k i+4 ≤ n := by
  have hk2 := hk.two_le
  have hs := hk.k_add_two_le
  have hs3 := hk.sq_add_le
  have hid := Nat.div_add_mod' i k
  have himod := Nat.mod_lt i (by omega : 0 < k)
  have hidiv : i/k < k := (Nat.div_lt_iff_lt_mul (by omega)).mpr hi
  have hmul := Nat.mul_le_mul_left (i/k) (show k ≤ side n k by omega)
  have hblock : i/k*side n k+side n k ≤ n := by
    calc
      i/k*side n k+side n k = (i/k+1)*side n k := by ring
      _ ≤ k*side n k := Nat.mul_le_mul_right _ hidiv
      _ = n := hk.mul_side
  have hkk : k ≤ k^2 := by nlinarith
  unfold horizontalDestination
  omega

theorem horizontalDestination_group {n k : ℕ} (i : GroupIndex k) :
    horizontalDestination (side n k) k i.val = (groupRow i).val*side n k+(groupCol i).val := rfl

/-- Fill all horizontal corridors from their staged rows. The compressed vertical
quotas and explicit representative row survive, and the blank stays on the last row. -/
theorem exists_horizontal_preparation_path {n k : ℕ} (hk : Dims n k)
    [NeZero n] (B : Board n)
    (hstage : ∀ (i : GroupIndex k) (c : Cell n), c ∈ stagingCells i → B c ∈ targetGroup i)
    (hblank : (blank B).1.val = n-1) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 12*n^2*k^2 ∧ blank C = blank B ∧
      (∀ (i : GroupIndex k) (c : Cell n), horizontal i c → C c ∈ targetGroup i) ∧
      (∀ (j i : GroupIndex k) (c : Cell n), c ∈ stagingC j i → C c = B c) ∧
      (∀ i : GroupIndex k, C (representativeDestination hk i) = B (representativeDestination hk i)) := by
  have hg := preparation_geometry hk
  have hk3 : 4 ≤ k^3 := by have := hk.two_le; omega
  have hwidth : k^3+4 ≤ n := by omega
  obtain ⟨C,p,hp,hb,hrow,hfix⟩ := exists_descending_row_schedule B (k^3) (n-k^3)
    (k*k) (by omega) (by omega) (horizontalDestination (side n k) k)
    (horizontalDestination_strictMono hk.two_le (by have := hk.k_add_two_le; omega))
    (by
      intro i hi
      have hh := horizontalDestination_bounds hk i hi
      rw [hblank]
      omega)
  refine ⟨C,p,?_,hb,?_,?_,?_⟩
  · calc
      p.length ≤ 12*n^2*(k*k) := hp
      _ = 12*n^2*k^2 := by ring
  · intro i c hc
    have hdest : c.1.val = horizontalDestination (side n k) k i.val := by
      rw [horizontalDestination_group]
      exact hc
    by_cases hcol : c.2.val < k^3
    · rw [hfix c (Or.inr (Or.inl hcol))]
      exact hstage i c ((mem_stagingCells i c).mpr
        (Or.inl ((mem_stagingA i c).mpr ⟨hc,hcol⟩)))
    · let j : Fin (n-k^3) := ⟨c.2.val-k^3,by have := c.2.isLt; omega⟩
      have hh := hrow i.val i.isLt j
      have he : (⟨horizontalDestination (side n k) k i.val,by
          have := horizontalDestination_bounds hk i.val i.isLt; omega⟩,
          ⟨k^3+j.val,by have := c.2.isLt; dsimp [j]; omega⟩) = c := by
        apply Prod.ext <;> apply Fin.ext
        · exact hdest.symm
        · dsimp [j]; omega
      rw [he] at hh
      rw [hh]
      apply hstage i
      apply (mem_stagingCells i _).mpr
      right; left
      apply (mem_stagingB i _).mpr
      exact ⟨rfl,by simp only; omega⟩
  · intro j i c hc
    apply hfix
    right; left
    have hh := (mem_stagingC j i c).mp hc
    rw [hh.2.2]
    have hi : i.val < k^2 := by simp [pow_two]
    have hcol := (groupCol j).isLt
    have hmul := Nat.mul_le_mul_right (k^2) hcol
    have he : k*k^2 = k^3 := by ring
    nlinarith
  · intro i
    apply hfix
    left
    intro j hj
    have hh := horizontalDestination_bounds hk j hj
    change horizontalDestination (side n k) k j < n-3
    omega

end
end SlidingPuzzle.Partition
