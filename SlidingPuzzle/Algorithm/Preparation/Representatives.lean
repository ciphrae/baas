import SlidingPuzzle.Paths
import SlidingPuzzle.Algorithm.Preparation.Capacity
import SlidingPuzzle.Algorithm.Preparation.Staging

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

/-- A staging construction: all compressed quotas and representatives are
filled, with the blank below row `k²` and right of column `k³`. The length bound
is doubled so that half-integer leading coefficients are retained. -/
def RepresentativeStaging {k : ℕ} (hk : 2 ≤ k) [NeZero (k^4)] (L : ℕ) : Prop :=
  ∀ B : Board (k^4), ∃ C : Board (k^4), ∃ p : Path B C,
    2*p.length ≤ L ∧
    (∀ (i : GroupIndex k) (c : Cell (k^4)),
      c ∈ stagingCells i → C c ∈ targetGroup i) ∧
    (∀ i : GroupIndex k, i ≠ lastGroup k hk →
      C (representativeSource hk i) ∈ targetGroup i) ∧
    k^2+1 ≤ (blank C).1.val ∧ k^3 ≤ (blank C).2.val

end
end SlidingPuzzle.Partition
