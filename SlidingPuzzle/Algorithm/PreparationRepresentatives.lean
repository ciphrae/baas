import SlidingPuzzle.Algorithm.StagingPath
import SlidingPuzzle.Algorithm.PhaseStates
import SlidingPuzzle.Moves.BlankAccess
import SlidingPuzzle.Moves.Translation

/-! Stage the corridor quotas and install last-reservoir representatives.

The spare tiles start on row `k²`, to the right of the compressed staging area.
A single row translation deposits them on row `k⁴ - 3` in the last reservoir.
The access path and translation both preserve all original staging cells.
This is a preparation subphase; spreading the staged corridors remains separate.
-/
namespace SlidingPuzzle.Partition
noncomputable section
open Classical

theorem preparation_geometry {k : ℕ} (hk : 2 ≤ k) :
    k^2 + 3 ≤ k^3 ∧ 2*k^2 ≤ k^3 ∧ k^3 + k^2 ≤ k^4 ∧
      k^3 + 4 ≤ k^4 ∧ k + 3 ≤ k^3 := by
  have hsq : 4 ≤ k^2 := by nlinarith
  have htwo : 2*k^2 ≤ k^3 := by
    calc
      2*k^2 ≤ k*k^2 := Nat.mul_le_mul_right _ hk
      _ = k^3 := by ring
  have hfour : 2*k^3 ≤ k^4 := by
    calc
      2*k^3 ≤ k*k^3 := Nat.mul_le_mul_right _ hk
      _ = k^4 := by ring
  have hksq : k ≤ k^2 := by nlinarith
  omega

/-- Source of the spare representative for group `i`, outside the original quotas. -/
def representativeSource {k : ℕ} (hk : 2 ≤ k) (i : GroupIndex k) : Cell (k^4) :=
  (⟨k^2, by have := preparation_geometry hk; omega⟩,
   ⟨k^4-k^2+i.val, by
     have := preparation_geometry hk
     have hi : i.val < k^2 := by simpa [pow_two] using i.isLt
     omega⟩)

private theorem representativeSource_not_staging {k : ℕ} (hk : 2 ≤ k)
    (i j : GroupIndex k) : representativeSource hk i ∉ stagingCells j := by
  intro h
  have hh := stagingCells_compressed hk h
  have := preparation_geometry hk
  change k^2 < k^2 ∨ k^4-k^2+i.val < k^3 at hh
  omega

private theorem representativeSource_injective {k : ℕ} (hk : 2 ≤ k) :
    Function.Injective (representativeSource hk) := by
  intro i j h
  apply Fin.ext
  have := congrArg (fun c : Cell (k^4) => c.2.val) h
  change k^4-k^2+i.val = k^4-k^2+j.val at this
  omega

/-- Add one spare tile to every nonfinal group's compressed quota. -/
def representativeStagingCells {k : ℕ} (hk : 2 ≤ k) (i : GroupIndex k) :
    Finset (Cell (k^4)) :=
  if i = lastGroup k hk then stagingCells i
  else insert (representativeSource hk i) (stagingCells i)

theorem mem_representativeStagingCells {k : ℕ} (hk : 2 ≤ k)
    (i : GroupIndex k) (c : Cell (k^4)) :
    c ∈ representativeStagingCells hk i ↔
      c ∈ stagingCells i ∨ (i ≠ lastGroup k hk ∧ c = representativeSource hk i) := by
  by_cases hi : i = lastGroup k hk <;> simp [representativeStagingCells, hi, or_comm]

theorem representativeStagingCells_disjoint {k : ℕ} (hk : 2 ≤ k) :
    (Set.univ : Set (GroupIndex k)).PairwiseDisjoint (representativeStagingCells hk) := by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro c hi hj
  rw [mem_representativeStagingCells] at hi hj
  rcases hi with hi | ⟨_,rfl⟩
  · rcases hj with hj | ⟨_,rfl⟩
    · exact Finset.disjoint_left.mp (stagingCells_disjoint hk hij) hi hj
    · exact representativeSource_not_staging hk j i hi
  · rcases hj with hj | ⟨_,he⟩
    · exact representativeSource_not_staging hk i j hj
    · exact hij (representativeSource_injective hk he)

theorem representativeStagingCells_capacity {k : ℕ} (hk : 2 ≤ k)
    [NeZero (k^4)] (i : GroupIndex k) :
    (representativeStagingCells hk i).card ≤ (targetGroup (n := k^4) i).card := by
  by_cases hi : i = lastGroup k hk
  · simp only [representativeStagingCells, if_pos hi]
    rw [card_stagingCells hk rfl]
    exact card_targetGroup_ge_corridor_quota hk rfl i
  · simp only [representativeStagingCells, if_neg hi]
    rw [Finset.card_insert_of_notMem (representativeSource_not_staging hk i i),
      card_stagingCells hk rfl]
    exact card_targetGroup_ge_corridor_quota_add_one_of_ne_last hk rfl i hi

/- Simultaneously stage all corridor tiles and one spare per nonfinal group,
with the blank below and to the right of the entire prefix. -/
/-- Representative staging inherits the shared protected-prefix cost. -/
theorem exists_representative_staging_path_of_bound {P k : ℕ}
    (hprefix : PrefixPathBound P) (hk : 2 ≤ k)
    [NeZero (k^4)] (B : Board (k^4)) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ P*k^11 ∧
      (∀ (i : GroupIndex k) (c : Cell (k^4)),
        c ∈ stagingCells i → C c ∈ targetGroup i) ∧
      (∀ i : GroupIndex k, i ≠ lastGroup k hk →
        C (representativeSource hk i) ∈ targetGroup i) ∧
      k^3 ≤ (blank C).1.val ∧ k^3 ≤ (blank C).2.val := by
  have hg := preparation_geometry hk
  obtain ⟨C,p,hp,hC,hb⟩ := exists_prefix_disjoint_group_path_with_blank_of_bound hprefix hk B (k^3)
    (by omega) (representativeStagingCells hk) (representativeStagingCells_disjoint hk)
    (by
      intro i c hc
      rcases (mem_representativeStagingCells hk i c).mp hc with hc | ⟨_,rfl⟩
      · exact stagingCells_prefix hk hc
      · left; change k^2 < k^3; omega)
    (representativeStagingCells_capacity hk)
  refine ⟨C,p,?_,?_,?_,hb⟩
  · calc
      p.length ≤ P*k^3*(k^4)^2 := hp
      _ = P*k^11 := by ring
  · intro i c hc
    exact hC i c ((mem_representativeStagingCells hk i c).mpr (Or.inl hc))
  · intro i hi
    exact hC i _ ((mem_representativeStagingCells hk i _).mpr (Or.inr ⟨hi,rfl⟩))

theorem exists_representative_staging_path {k : ℕ} (hk : 2 ≤ k)
    [NeZero (k^4)] (B : Board (k^4)) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ 1004*k^11 ∧
      (∀ (i : GroupIndex k) (c : Cell (k^4)),
        c ∈ stagingCells i → C c ∈ targetGroup i) ∧
      (∀ i : GroupIndex k, i ≠ lastGroup k hk →
        C (representativeSource hk i) ∈ targetGroup i) ∧
      k^3 ≤ (blank C).1.val ∧ k^3 ≤ (blank C).2.val := by
  exact exists_representative_staging_path_of_bound prefixPathBound_current hk B

/-- The final representative positions, kept explicit for subsequent translations. -/
def representativeDestination {k : ℕ} (hk : 2 ≤ k) (i : GroupIndex k) : Cell (k^4) :=
  (⟨k^4-3, by have := preparation_geometry hk; omega⟩,
   (representativeSource hk i).2)

/-- The translated spare row lies inside the last reservoir. -/
theorem representative_destination_in_last_reservoir {k : ℕ} (hk : 2 ≤ k)
    (i : GroupIndex k) :
    reservoir (lastGroup k hk) (representativeDestination hk i) := by
  have hg := preparation_geometry hk
  have hi : i.val < k^2 := by simpa [pow_two] using i.isLt
  have he : (k-1)*k^3 + k^3 = k^4 := by
    calc
      (k-1)*k^3 + k^3 = (k-1+1)*k^3 := by ring
      _ = k*k^3 := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
      _ = k^4 := by ring
  simp only [reservoir, lastGroup, groupRow, groupCol, Equiv.symm_apply_apply,
    representativeDestination, representativeSource, Nat.add_mul, Nat.one_mul]
  omega

/- Install all required representatives while retaining the original staging
quotas. The complete path has a uniform `O(k¹¹)` all-moves bound. -/
/-- Access and representative translation add nine to the shared cost. -/
theorem exists_staging_representative_row_path_with_blank_of_bound {P k : ℕ}
    (hprefix : PrefixPathBound P) (hk : 2 ≤ k)
    [NeZero (k^4)] (B : Board (k^4)) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ (P+9)*k^11 ∧
      (∀ (i : GroupIndex k) (c : Cell (k^4)),
        c ∈ stagingCells i → C c ∈ targetGroup i) ∧
      (∀ i : GroupIndex k, i ≠ lastGroup k hk →
        C (representativeDestination hk i) ∈ targetGroup i) ∧
      (blank C).1.val = k^4-1 ∧ (blank C).2.val = k^4-k^2 := by
  have hg := preparation_geometry hk
  have hk2 : 1 < k^2 := by nlinarith
  obtain ⟨A,p,hp,hstage,hrep,hbr,hbc⟩ := exists_representative_staging_path_of_bound hprefix hk B
  let access : Cell (k^4) :=
    (⟨k^2+2,by omega⟩,⟨k^4-k^2,by omega⟩)
  obtain ⟨D,q,hblank,hq,hfix⟩ := exists_blank_access_path_preserving A access
  have hqstage (i : GroupIndex k) (c : Cell (k^4)) (hc : c ∈ stagingCells i) :
      D c = A c := by
    apply hfix
    rcases stagingCells_compressed hk hc with hr | hcol
    · left
      change c.1.val < min (blank A).1.val (k^2+2)
      exact lt_min (by omega) (by omega)
    · right; right; left
      change c.2.val < min (blank A).2.val (k^4-k^2)
      exact lt_min (by omega) (by omega)
  have hqrep (i : GroupIndex k) : D (representativeSource hk i) = A (representativeSource hk i) := by
    apply hfix
    left
    change k^2 < min (blank A).1.val (k^2+2)
    exact lt_min (by omega) (by omega)
  obtain ⟨E,s,hs,hrow,hsfix,hsblank⟩ := exists_row_translation_with_blank D (k^2) (k^4-k^2)
    (k^2) (k^4-3-k^2) (by omega) (by omega) hk2 hblank
  have hEstage (i : GroupIndex k) (c : Cell (k^4)) (hc : c ∈ stagingCells i) :
      E c ∈ targetGroup i := by
    rw [hsfix c, hqstage i c hc]
    · exact hstage i c hc
    · rcases stagingCells_compressed hk hc with hr | hcol
      · exact Or.inl hr
      · exact Or.inr (Or.inr (Or.inl (by omega)))
  have hErep (i : GroupIndex k) (hi : i ≠ lastGroup k hk) :
      E (⟨k^4-3,by omega⟩,(representativeSource hk i).2) ∈ targetGroup i := by
    have hil : i.val < k^2 := by simpa [pow_two] using i.isLt
    have hh := hrow ⟨i.val,hil⟩
    have hroweq : k^2 + (k^4-3-k^2) = k^4-3 := by omega
    simp only [hroweq] at hh
    change E (⟨k^4-3,by omega⟩,(representativeSource hk i).2) =
      D (representativeSource hk i) at hh
    rw [hh,hqrep]
    exact hrep i hi
  refine ⟨E,(p.append q).append s,?_,hEstage,hErep,?_⟩
  · have hqbound : q.length ≤ 2*k^4 := by
      apply hq.trans
      unfold gridDistance Nat.dist
      have := (blank A).1.isLt
      have := (blank A).2.isLt
      have := access.1.isLt
      have := access.2.isLt
      omega
    have hsbound : s.length ≤ 7*k^6 := by
      calc
        s.length ≤ (k^4-3-k^2)*(6*k^2+3) := hs
        _ ≤ k^4*(7*k^2) := Nat.mul_le_mul (by omega) (by nlinarith)
        _ = 7*k^6 := by ring
    have h46 : k^4 ≤ k^6 := Nat.pow_le_pow_right (by omega) (by omega)
    have h611 : k^6 ≤ k^11 := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [Path.length_append]
    nlinarith [Nat.mul_le_mul_left 2 h611, Nat.mul_le_mul_left 7 h611]
  · rw [hsblank]
    change k^2+(k^4-3-k^2)+2 = k^4-1 ∧ k^4-k^2 = k^4-k^2
    omega

theorem exists_staging_representative_row_path_with_blank {k : ℕ} (hk : 2 ≤ k)
    [NeZero (k^4)] (B : Board (k^4)) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ 1013*k^11 ∧
      (∀ (i : GroupIndex k) (c : Cell (k^4)),
        c ∈ stagingCells i → C c ∈ targetGroup i) ∧
      (∀ i : GroupIndex k, i ≠ lastGroup k hk →
        C (representativeDestination hk i) ∈ targetGroup i) ∧
      (blank C).1.val = k^4-1 ∧ (blank C).2.val = k^4-k^2 := by
  exact exists_staging_representative_row_path_with_blank_of_bound prefixPathBound_current hk B

/-- Staging and explicit representatives without retaining the blank endpoint. -/
theorem exists_staging_representative_row_path {k : ℕ} (hk : 2 ≤ k)
    [NeZero (k^4)] (B : Board (k^4)) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ 1013*k^11 ∧
      (∀ (i : GroupIndex k) (c : Cell (k^4)),
        c ∈ stagingCells i → C c ∈ targetGroup i) ∧
      (∀ i : GroupIndex k, i ≠ lastGroup k hk →
        C (representativeDestination hk i) ∈ targetGroup i) := by
  obtain ⟨C,p,hp,hs,hr,_⟩ := exists_staging_representative_row_path_with_blank hk B
  exact ⟨C,p,hp,hs,hr⟩

/-- The explicit representative row discharges the count-based preparation
requirement. No hypothesis about available source tiles is needed. -/
theorem exists_staging_lastRepresentatives_path {k : ℕ} (hk : 2 ≤ k)
    [NeZero (k^4)] (B : Board (k^4)) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ 1013*k^11 ∧
      (∀ (i : GroupIndex k) (c : Cell (k^4)),
        c ∈ stagingCells i → C c ∈ targetGroup i) ∧
      LastRepresentatives hk C := by
  obtain ⟨C,p,hp,hstage,hrep⟩ := exists_staging_representative_row_path hk B
  refine ⟨C,p,hp,hstage,?_⟩
  intro i hi
  have hc : representativeDestination hk i ∈ reservoirCells (lastGroup k hk) := by
    simpa only [mem_reservoirCells] using representative_destination_in_last_reservoir hk i
  unfold reservoirCount
  have hh := Finset.single_le_sum (f := fun x : Cell (k^4) =>
    if C x ∈ targetGroup i then 1 else 0) (fun _ _ => Nat.zero_le _) hc
  rw [if_pos (hrep i hi)] at hh
  omega

end
end SlidingPuzzle.Partition
