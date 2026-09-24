import SlidingPuzzle.Algorithm.PreparationRepresentatives
import SlidingPuzzle.Moves.RowSchedule

/-! Preparation step (ii): the complete descending horizontal-corridor schedule. -/
namespace SlidingPuzzle.Partition
noncomputable section

/-- Destination row of a horizontal corridor, extended to natural indices. -/
def horizontalDestination (k i : ℕ) : ℕ := i/k*k^3+i%k

private theorem cube_room {k : ℕ} (hk : 2 ≤ k) : k+3 ≤ k^3 := by
  have hsq : 4 ≤ k^2 := by nlinarith
  have hksq : k ≤ k^2 := by nlinarith
  have h : 2*k^2 ≤ k^3 := by
    calc
      2*k^2 ≤ k*k^2 := Nat.mul_le_mul_right _ hk
      _ = k^3 := by ring
  omega

/-- The destination rows are strictly increasing, even across square boundaries. -/
theorem horizontalDestination_strictMono {k : ℕ} (hk : 2 ≤ k) :
    StrictMono (horizontalDestination k) := by
  intro i j hij
  have hcube := cube_room hk
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
      horizontalDestination k i < i/k*k^3+k^3 := by unfold horizontalDestination; omega
      _ = (i/k+1)*k^3 := by ring
      _ ≤ j/k*k^3 := Nat.mul_le_mul_right _ hdiv'
      _ ≤ horizontalDestination k j := Nat.le_add_right _ _

private theorem horizontalDestination_bounds {k : ℕ} (hk : 2 ≤ k)
    (i : ℕ) (hi : i < k*k) :
    i ≤ horizontalDestination k i ∧ horizontalDestination k i+4 ≤ k^4 := by
  have hcube := cube_room hk
  have hid := Nat.div_add_mod' i k
  have himod := Nat.mod_lt i (by omega : 0 < k)
  have hidiv : i/k < k := (Nat.div_lt_iff_lt_mul (by omega)).mpr hi
  have hmul := Nat.mul_le_mul_left (i/k) (show k ≤ k^3 by omega)
  have hblock : i/k*k^3+k^3 ≤ k^4 := by
    calc
      i/k*k^3+k^3 = (i/k+1)*k^3 := by ring
      _ ≤ k*k^3 := Nat.mul_le_mul_right _ hidiv
      _ = k^4 := by ring
  unfold horizontalDestination
  omega

theorem horizontalDestination_group {k : ℕ} (i : GroupIndex k) :
    horizontalDestination k i.val = (groupRow i).val*k^3+(groupCol i).val := rfl

/-- Fill all horizontal corridors from their staged rows. The compressed vertical
quotas and explicit representative row survive, and the blank stays on the last row. -/
theorem exists_horizontal_preparation_path {k : ℕ} (hk : 2 ≤ k)
    [NeZero (k^4)] (B : Board (k^4))
    (hstage : ∀ (i : GroupIndex k) (c : Cell (k^4)), c ∈ stagingCells i → B c ∈ targetGroup i)
    (hblank : (blank B).1.val = k^4-1) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ 12*k^10 ∧ blank C = blank B ∧
      (∀ (i : GroupIndex k) (c : Cell (k^4)), horizontal i c → C c ∈ targetGroup i) ∧
      (∀ (j i : GroupIndex k) (c : Cell (k^4)), c ∈ stagingC j i → C c = B c) ∧
      (∀ i : GroupIndex k, C (representativeDestination hk i) = B (representativeDestination hk i)) := by
  have hcube := cube_room hk
  have hk3 : 4 ≤ k^3 := by omega
  have hwidth : k^3+4 ≤ k^4 := by
    have h : 2*k^3 ≤ k^4 := by
      calc
        2*k^3 ≤ k*k^3 := Nat.mul_le_mul_right _ hk
        _ = k^4 := by ring
    omega
  obtain ⟨C,p,hp,hb,hrow,hfix⟩ := exists_descending_row_schedule B (k^3) (k^4-k^3)
    (k*k) (by omega) (by omega) (horizontalDestination k) (horizontalDestination_strictMono hk)
    (by
      intro i hi
      have hh := horizontalDestination_bounds hk i hi
      rw [hblank]
      omega)
  refine ⟨C,p,?_,hb,?_,?_,?_⟩
  · calc
      p.length ≤ 12*(k^4)^2*(k*k) := hp
      _ = 12*k^10 := by ring
  · intro i c hc
    have hdest : c.1.val = horizontalDestination k i.val := by
      rw [horizontalDestination_group]
      exact hc
    by_cases hcol : c.2.val < k^3
    · rw [hfix c (Or.inr (Or.inl hcol))]
      exact hstage i c ((mem_stagingCells i c).mpr
        (Or.inl ((mem_stagingA i c).mpr ⟨hc,hcol⟩)))
    · let j : Fin (k^4-k^3) := ⟨c.2.val-k^3,by have := c.2.isLt; omega⟩
      have hh := hrow i.val i.isLt j
      have he : (⟨horizontalDestination k i.val,by
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
    have hi : i.val < k^2 := by simpa [pow_two] using i.isLt
    have hcol := (groupCol j).isLt
    have hmul := Nat.mul_le_mul_right (k^2) hcol
    have he : k*k^2 = k^3 := by ring
    nlinarith
  · intro i
    apply hfix
    left
    intro j hj
    have hh := horizontalDestination_bounds hk j hj
    change horizontalDestination k j < k^4-3
    omega

/- A legal preparation prefix now stages all vertical quotas, clears every
horizontal corridor, and installs last-reservoir representatives. -/
/-- Horizontal spreading retains the shared prefix budget. -/
theorem exists_horizontal_prepared_path_with_blank_of_bound {P k : ℕ}
    (hprefix : PrefixPathBound P) (hk : 2 ≤ k)
    [NeZero (k^4)] (B : Board (k^4)) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ (P+15)*k^11 ∧ (blank C).1.val = k^4-1 ∧
      (∀ (i : GroupIndex k) (c : Cell (k^4)), horizontal i c → C c ∈ targetGroup i) ∧
      (∀ (j i : GroupIndex k) (c : Cell (k^4)), c ∈ stagingC j i → C c ∈ targetGroup i) ∧
      (∀ i : GroupIndex k, i ≠ lastGroup k hk → C (representativeDestination hk i) ∈ targetGroup i) ∧
      (blank C).2.val = k^4-k^2 := by
  obtain ⟨A,p,hp,hstage,hrep,hbr,hbc⟩ := exists_staging_representative_row_path_with_blank_of_bound hprefix hk B
  obtain ⟨C,q,hq,hb,hH,hCs,hR⟩ := exists_horizontal_preparation_path hk A hstage hbr
  refine ⟨C,p.append q,?_,by rw [hb]; exact hbr,hH,?_,?_,by rw [hb]; exact hbc⟩
  · have hpow : 12*k^10 ≤ 6*k^11 := by
      calc
        12*k^10 = 6*(2*k^10) := by ring
        _ ≤ 6*k^11 := Nat.mul_le_mul_left _ (by
          calc
            2*k^10 ≤ k*k^10 := Nat.mul_le_mul_right _ hk
            _ = k^11 := by ring)
    rw [Path.length_append]
    calc
      p.length + q.length ≤ (P+9)*k^11 + 12*k^10 := Nat.add_le_add hp hq
      _ ≤ (P+9)*k^11 + 6*k^11 := Nat.add_le_add_left hpow _
      _ = (P+15)*k^11 := by ring
  · intro j i c hc
    rw [hCs j i c hc]
    exact hstage i c ((mem_stagingCells i c).mpr (Or.inr (Or.inr ⟨j,hc⟩)))
  · intro i hi
    rw [hR]
    exact hrep i hi

theorem exists_horizontal_prepared_path_with_blank {k : ℕ} (hk : 2 ≤ k)
    [NeZero (k^4)] (B : Board (k^4)) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ 1019*k^11 ∧ (blank C).1.val = k^4-1 ∧
      (∀ (i : GroupIndex k) (c : Cell (k^4)), horizontal i c → C c ∈ targetGroup i) ∧
      (∀ (j i : GroupIndex k) (c : Cell (k^4)), c ∈ stagingC j i → C c ∈ targetGroup i) ∧
      (∀ i : GroupIndex k, i ≠ lastGroup k hk → C (representativeDestination hk i) ∈ targetGroup i) ∧
      (blank C).2.val = k^4-k^2 := by
  exact exists_horizontal_prepared_path_with_blank_of_bound prefixPathBound_current hk B

/-- The horizontal preparation prefix without retaining the blank column. -/
theorem exists_horizontal_prepared_path {k : ℕ} (hk : 2 ≤ k)
    [NeZero (k^4)] (B : Board (k^4)) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ 1019*k^11 ∧ (blank C).1.val = k^4-1 ∧
      (∀ (i : GroupIndex k) (c : Cell (k^4)), horizontal i c → C c ∈ targetGroup i) ∧
      (∀ (j i : GroupIndex k) (c : Cell (k^4)), c ∈ stagingC j i → C c ∈ targetGroup i) ∧
      (∀ i : GroupIndex k, i ≠ lastGroup k hk → C (representativeDestination hk i) ∈ targetGroup i) := by
  obtain ⟨C,p,hp,hb,hH,hV,hR,_⟩ := exists_horizontal_prepared_path_with_blank hk B
  exact ⟨C,p,hp,hb,hH,hV,hR⟩

end
end SlidingPuzzle.Partition
