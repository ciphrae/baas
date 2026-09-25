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
    (i : ℕ) (hi : i < 2*k*k) :
    i ≤ horizontalDestination (side n k) (2*k) i ∧
      horizontalDestination (side n k) (2*k) i+4 ≤ n := by
  have hk2 := hk.two_le
  have hs3 := hk.sq_add_le
  have h2k : 2*k+4 ≤ side n k := by nlinarith
  have hid := Nat.div_add_mod' i (2*k)
  have himod := Nat.mod_lt i (by omega : 0 < 2*k)
  have hidiv : i/(2*k) < k := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by
    rw [Nat.mul_comm] at hi; simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hi)
  have hmul := Nat.mul_le_mul_left (i/(2*k)) (show 2*k ≤ side n k by omega)
  have hblock : i/(2*k)*side n k+side n k ≤ n := by
    calc
      i/(2*k)*side n k+side n k = (i/(2*k)+1)*side n k := by ring
      _ ≤ k*side n k := Nat.mul_le_mul_right _ hidiv
      _ = n := hk.mul_side
  unfold horizontalDestination
  omega

/-- The staged rows are sent to the rows of `H_i`. -/
theorem horizontalDestination_stagedRow {n k : ℕ} (hk : Dims n k) (i : GroupIndex k)
    (low : Bool) :
    horizontalDestination (side n k) (2*k) (stagedRow k i low) = corridorRow (n := n) i low := by
  have hb := (groupCol i).isLt
  have hk2 := hk.two_le
  have hdm : ∀ a o : ℕ, o < 2*k →
      horizontalDestination (side n k) (2*k) (a*(2*k)+o) = a*side n k+o := by
    intro a o ho
    have h2 : 0 < 2*k := by omega
    unfold horizontalDestination
    rw [Nat.add_comm (a*(2*k)) o, Nat.add_mul_div_right _ _ h2, Nat.div_eq_of_lt ho,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ho]
    ring
  unfold stagedRow corridorRow
  cases low <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact hdm _ _ (by omega)
  · rw [Nat.add_assoc, hdm _ _ (by omega), Nat.add_assoc]

/-- Fill all horizontal corridors from their staged rows. The compressed vertical
quotas and explicit representative row survive, and the blank stays on the last row. -/
theorem exists_horizontal_preparation_path {n k : ℕ} (hk : Dims n k)
    [NeZero n] (B : Board n)
    (hstage : ∀ (i : GroupIndex k) (c : Cell n), c ∈ stagingCells i → B c ∈ targetGroup i)
    (hblank : (blank B).1.val = n-1) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 24*n^2*k^2 ∧ blank C = blank B ∧
      (∀ (i : GroupIndex k) (c : Cell n), horizontal i c → C c ∈ targetGroup i) ∧
      (∀ (j i : GroupIndex k) (c : Cell n), c ∈ stagingC j i → C c = B c) ∧
      (∀ i : GroupIndex k, C (representativeDestination hk i) = B (representativeDestination hk i)) := by
  have hg := preparation_geometry hk
  have hk3 : 4 ≤ k^3 := by have := hk.two_le; omega
  have hwidth : k^3+4 ≤ n := by omega
  obtain ⟨C,p,hp,hb,hrow,hfix⟩ := exists_descending_row_schedule B (k^3) (n-k^3)
    (2*k*k) (by omega) (by omega) (horizontalDestination (side n k) (2*k))
    (horizontalDestination_strictMono (by have := hk.two_le; omega)
      (by have := hk.sq_add_le; have := hk.two_le; nlinarith))
    (by
      intro i hi
      have hh := horizontalDestination_bounds hk i hi
      rw [hblank]
      omega)
  refine ⟨C,p,?_,hb,?_,?_,?_⟩
  · calc
      p.length ≤ 12*n^2*(2*k*k) := hp
      _ = 24*n^2*k^2 := by ring
  · intro i c hc
    by_cases hcol : c.2.val < k^3
    · rw [hfix c (Or.inr (Or.inl hcol))]
      exact hstage i c ((mem_stagingCells i c).mpr
        (Or.inl ((mem_stagingA i c).mpr ⟨hc,hcol⟩)))
    · obtain ⟨low, hlow⟩ : ∃ low, c.1.val = corridorRow (n := n) i low := by
        rcases hc with h | h
        · exact ⟨false, h⟩
        · exact ⟨true, h⟩
      have hρ := stagedRow_lt hk.two_le i low
      have hρ' : stagedRow k i low < 2*k*k := by rw [pow_two] at hρ; linarith
      have hdest : c.1.val = horizontalDestination (side n k) (2*k) (stagedRow k i low) := by
        rw [horizontalDestination_stagedRow hk]; exact hlow
      let j : Fin (n-k^3) := ⟨c.2.val-k^3,by have := c.2.isLt; omega⟩
      have hh := hrow (stagedRow k i low) hρ' j
      have he : (⟨horizontalDestination (side n k) (2*k) (stagedRow k i low),by
          have := horizontalDestination_bounds hk _ hρ'; omega⟩,
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
      refine ⟨?_, by simp only; omega⟩
      cases low
      · exact Or.inl rfl
      · exact Or.inr rfl
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
    change horizontalDestination (side n k) (2*k) j < n-3
    omega

end
end SlidingPuzzle.Partition
