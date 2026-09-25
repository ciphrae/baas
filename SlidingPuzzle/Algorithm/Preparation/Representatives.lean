import SlidingPuzzle.Paths
import SlidingPuzzle.Algorithm.Preparation.Capacity
import SlidingPuzzle.Algorithm.Preparation.Staging

/-! Stage the corridor quotas and install last-reservoir representatives.

The spare tiles start on row `2k²`, to the right of the compressed staging area.
A single row translation deposits them on row `n - 3` in the last reservoir.
The access path and translation both preserve all original staging cells.
This is a preparation subphase; spreading the staged corridors remains separate.
-/
namespace SlidingPuzzle.Partition
noncomputable section
open Classical

theorem preparation_geometry {n k : ℕ} (hk : Dims n k) :
    k^2 + 3 ≤ k^3 ∧ 2*k^2 ≤ k^3 ∧ k^3 + k^2 ≤ n ∧
      k^3 + 4 ≤ n ∧ k + 3 ≤ k^3 ∧ k^3 ≤ side n k ∧ 2*side n k ≤ n := by
  obtain ⟨hk2, hsq, htwo, hs3, hks⟩ := hk.facts
  have hns : 2*side n k ≤ n := (Nat.mul_le_mul_right _ hk2).trans_eq hks
  have hksq : k ≤ k^2 := by nlinarith
  omega

/-- Source of the spare representative for group `i`, outside the original quotas. -/
def representativeSource {n k : ℕ} (hk : Dims n k) (i : GroupIndex k) : Cell n :=
  (⟨2*k^2, by have := preparation_geometry hk; omega⟩,
   ⟨n-k^2+i.val, by
     have := preparation_geometry hk
     have hi : i.val < k^2 := by simp [pow_two]
     omega⟩)

private theorem representativeSource_not_staging {n k : ℕ} (hk : Dims n k)
    (i j : GroupIndex k) : representativeSource hk i ∉ stagingCells j := by
  intro h
  have hh := stagingCells_compressed hk h
  have := preparation_geometry hk
  change 2*k^2 < 2*k^2 ∨ n-k^2+i.val < k^3 at hh
  omega

private theorem representativeSource_injective {n k : ℕ} (hk : Dims n k) :
    Function.Injective (representativeSource hk) := by
  intro i j h
  apply Fin.ext
  have := congrArg (fun c : Cell n => c.2.val) h
  change n-k^2+i.val = n-k^2+j.val at this
  omega

/-- Add one spare tile to every nonfinal group's compressed quota. -/
def representativeStagingCells {n k : ℕ} (hk : Dims n k) (i : GroupIndex k) :
    Finset (Cell n) :=
  if i = lastGroup k hk then stagingCells i
  else insert (representativeSource hk i) (stagingCells i)

theorem mem_representativeStagingCells {n k : ℕ} (hk : Dims n k)
    (i : GroupIndex k) (c : Cell n) :
    c ∈ representativeStagingCells hk i ↔
      c ∈ stagingCells i ∨ (i ≠ lastGroup k hk ∧ c = representativeSource hk i) := by
  by_cases hi : i = lastGroup k hk <;> simp [representativeStagingCells, hi, or_comm]

theorem representativeStagingCells_disjoint {n k : ℕ} (hk : Dims n k) :
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

theorem representativeStagingCells_capacity {n k : ℕ} (hk : Dims n k)
    [NeZero n] (i : GroupIndex k) :
    (representativeStagingCells hk i).card ≤ (targetGroup (n := n) i).card := by
  by_cases hi : i = lastGroup k hk
  · simp only [representativeStagingCells, if_pos hi]
    rw [card_stagingCells hk]
    exact card_targetGroup_ge_corridor_quota hk i
  · simp only [representativeStagingCells, if_neg hi]
    rw [Finset.card_insert_of_notMem (representativeSource_not_staging hk i i),
      card_stagingCells hk]
    exact card_targetGroup_ge_corridor_quota_add_one_of_ne_last hk i hi

/-- The final representative positions, kept explicit for subsequent translations. -/
def representativeDestination {n k : ℕ} (hk : Dims n k) (i : GroupIndex k) : Cell n :=
  (⟨n-3, by have := preparation_geometry hk; omega⟩,
   (representativeSource hk i).2)

/-- The translated spare row lies inside the last reservoir. -/
theorem representative_destination_in_last_reservoir {n k : ℕ} (hk : Dims n k)
    (i : GroupIndex k) :
    reservoir (lastGroup k hk) (representativeDestination hk i) := by
  have hg := preparation_geometry hk
  have hi : i.val < k^2 := by simp [pow_two]
  have hk2 := hk.two_le
  have he : (k-1)*side n k + side n k = n := by
    calc
      (k-1)*side n k + side n k = (k-1+1)*side n k := by ring
      _ = k*side n k := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
      _ = n := hk.mul_side
  have h2k : 2*k+3 ≤ side n k := by have := hk.sq_add_le; nlinarith
  simp only [reservoir, lastGroup, groupRow, groupCol, Equiv.symm_apply_apply,
    representativeDestination, representativeSource, Nat.add_mul, Nat.one_mul]
  omega

/-- A staging construction: all compressed quotas and representatives are
filled, with the blank below row `2k²` and right of column `k³`. The length bound
is doubled so that half-integer leading coefficients are retained. -/
def RepresentativeStaging {n k : ℕ} (hk : Dims n k) [NeZero n] (L : ℕ) : Prop :=
  ∀ B : Board n, ∃ C : Board n, ∃ p : Path B C,
    2*p.length ≤ L ∧
    (∀ (i : GroupIndex k) (c : Cell n),
      c ∈ stagingCells i → C c ∈ targetGroup i) ∧
    (∀ i : GroupIndex k, i ≠ lastGroup k hk →
      C (representativeSource hk i) ∈ targetGroup i) ∧
    2*k^2+1 ≤ (blank C).1.val ∧ k^3 ≤ (blank C).2.val

end
end SlidingPuzzle.Partition
