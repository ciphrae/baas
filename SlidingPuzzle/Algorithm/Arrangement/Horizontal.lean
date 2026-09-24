import SlidingPuzzle.Algorithm.Cardinalities
import SlidingPuzzle.Moves.BulkExchangeSchedule

/-! Arrangement's second schedule: exchange the off-diagonal horizontal slices. -/
namespace SlidingPuzzle.Partition
variable {k : ℕ}

abbrev SliceIndex (k : ℕ) := GroupIndex k × Fin k

def sliceDestination (i : SliceIndex k) : GroupIndex k :=
  finProdFinEquiv (groupRow i.1,i.2)

def slicePartner (i : SliceIndex k) : SliceIndex k :=
  (sliceDestination i,groupCol i.1)

@[simp] theorem slicePartner_involutive : Function.Involutive (slicePartner (k := k)) := by
  intro i
  simp only [slicePartner,sliceDestination,groupRow,groupCol,Equiv.symm_apply_apply]
  exact Prod.ext (finProdFinEquiv.apply_symm_apply i.1) rfl

@[simp] theorem sliceDestination_partner (i : SliceIndex k) :
    sliceDestination (slicePartner i) = i.1 := by
  simp only [slicePartner,sliceDestination,groupRow,groupCol,Equiv.symm_apply_apply]
  exact finProdFinEquiv.apply_symm_apply i.1

/-- A slice is fixed exactly when its column block is already correct. -/
theorem slicePartner_eq_self (i : SliceIndex k) :
    slicePartner i = i ↔ i.2 = groupCol i.1 := by
  constructor
  · intro h
    exact (congrArg Prod.snd h).symm
  · intro h
    apply Prod.ext
    · change finProdFinEquiv (groupRow i.1,i.2) = i.1
      rw [h]
      exact finProdFinEquiv.apply_symm_apply i.1
    · exact h.symm

/-- One slice per group is already in its destination square. -/
theorem card_horizontal_active :
    ((Finset.univ : Finset (SliceIndex k)).filter
      (fun i => slicePartner i ≠ i)).card = k^3-k^2 := by
  classical
  have hfixed : ((Finset.univ : Finset (SliceIndex k)).filter
      (fun i => slicePartner i = i)).card = k*k := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    simp [slicePartner_eq_self]
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (SliceIndex k))) (fun i => slicePartner i = i)
  rw [hfixed] at h
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h
  calc
    _ = k*k*k-k*k := Nat.eq_sub_of_add_eq' h
    _ = k^3-k^2 := by congr 1 <;> ring

/-- A horizontal slice lies in the square indexed by its row block and column block. -/
theorem horizontalSlice_subset_square (hk : 2 ≤ k) (i : SliceIndex k)
    {x : Cell (k^4)} (hx : x ∈ horizontalSliceCells i.1 i.2) :
    square (sliceDestination i) x := by
  obtain ⟨hH,hlo,hhi⟩ := mem_horizontalSliceCells _ _ _ |>.mp hx
  have hk3 : k ≤ k^3 := by nlinarith [Nat.mul_le_mul_left k (Nat.pow_le_pow_left hk 2)]
  have hcol := (groupCol i.1).isLt
  simp only [square,sliceDestination,groupRow,groupCol,Equiv.symm_apply_apply]
  change x.1.val = (groupRow i.1).val*k^3+(groupCol i.1).val at hH
  change (groupRow i.1).val*k^3 ≤ x.1.val ∧
    x.1.val < ((groupRow i.1).val+1)*k^3 ∧
    i.2.val*k^3 ≤ x.2.val ∧ x.2.val < (i.2.val+1)*k^3
  refine ⟨by omega,?_,hlo,hhi⟩
  simp only [Nat.add_mul,Nat.one_mul]
  omega

/-- The horizontal slices form pairwise disjoint regions. -/
theorem horizontalSlice_disjoint (hk : 2 ≤ k) (i j : SliceIndex k) (hij : i ≠ j) :
    Disjoint (horizontalSliceCells (n := k^4) i.1 i.2) (horizontalSliceCells j.1 j.2) := by
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  have hH := horizontal_unique hk (mem_horizontalSliceCells _ _ _ |>.mp hxi).1
    (mem_horizontalSliceCells _ _ _ |>.mp hxj).1
  have hs := square_unique hk (horizontalSlice_subset_square hk i hxi)
    (horizontalSlice_subset_square hk j hxj)
  have hc : i.2=j.2 := by
    have hh := congrArg groupCol hs
    simpa [sliceDestination,groupCol] using hh
  exact hij (Prod.ext hH hc)

/-- Sort all horizontal slices into their containing squares, restoring every
vertical corridor and reservoir. -/
theorem exists_horizontal_arrangement_path [NeZero (k^4)] (hk : 2 ≤ k) (B : Board (k^4))
    (hH : ∀ (i : GroupIndex k) x, horizontal i x → B x ∈ targetGroup i) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ (24*k^3+2032)*(k^3-k^2)*k^4 ∧ blank C = blank B ∧
      (∀ (i : SliceIndex k) x, x ∈ horizontalSliceCells i.1 i.2 →
        C x ∈ targetGroup (sliceDestination i)) ∧
      (∀ (i j : GroupIndex k) x, vertical i j x → C x = B x) ∧
      (∀ (i : GroupIndex k) x, reservoir i x → C x = B x) := by
  classical
  have hn : 4 ≤ k^4 := by nlinarith [Nat.pow_le_pow_left hk 4]
  let S : SliceIndex k → Finset (Cell (k^4)) := fun i => horizontalSliceCells i.1 i.2
  have hsize : ∀ i, 2 ≤ (S i).card ∧ (S i).card ≤ k^3 := by
    intro i
    dsimp [S]
    rw [card_horizontalSlice hk rfl]
    exact ⟨by nlinarith [Nat.pow_le_pow_left hk 3],le_rfl⟩
  have hcard : ∀ i, (S i).card = (S (slicePartner i)).card := by
    intro i
    dsimp [S]
    rw [card_horizontalSlice hk rfl,card_horizontalSlice hk rfl]
  have hzero : ∀ i x, x ∈ S i → B x ≠ 0 := by
    intro i x hx hz
    have hh := hH i.1 x (mem_horizontalSliceCells _ _ _ |>.mp hx).1
    exact zero_not_mem_targetGroup i.1 (hz ▸ hh)
  obtain ⟨C,p,hp,hbC,hC,hfix⟩ := exists_bulk_involution_region_path_active B hn S slicePartner
    slicePartner_involutive (horizontalSlice_disjoint hk) (k^3) (by nlinarith [Nat.mul_le_mul_right (k^3) hk]) hsize hcard hzero
    (fun i t => t ∈ targetGroup (sliceDestination i)) Finset.univ (by simp)
    (by intro i _ x hx; simpa using hH i.1 x (mem_horizontalSliceCells _ _ _ |>.mp hx).1)
  refine ⟨C,p,?_,hbC,?_,?_,?_⟩
  · simpa only [card_horizontal_active] using hp
  · intro i x hx
    exact hC i (Finset.mem_univ _) x hx
  · intro i j x hx
    apply hfix
    intro a _ ha
    exact horizontal_not_vertical hk (mem_horizontalSliceCells _ _ _ |>.mp ha).1 hx
  · intro i x hx
    apply hfix
    intro a _ ha
    exact horizontal_not_reservoir hk (mem_horizontalSliceCells _ _ _ |>.mp ha).1 hx
end SlidingPuzzle.Partition
