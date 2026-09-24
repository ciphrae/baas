import SlidingPuzzle.Algorithm.ArrangementVertical
import SlidingPuzzle.Algorithm.ArrangementHorizontal
import SlidingPuzzle.Algorithm.PhaseContracts

/-! The complete arrangement phase, with an all-moves bound of order k^11.
The current generic exchange schedule gives coefficient 274. -/
namespace SlidingPuzzle.Partition
variable {k : ℕ} [NeZero (k^4)]

/-- A shared-staging exchange costs only 48 per tile, plus one boundary
remainder per pair. The smallest dimension is checked separately. -/
theorem arrangement_budget_le (k : ℕ) (hk : 2 ≤ k) :
    (24*(k^3-k)+2032)*(k^4-k^2)*k^4 +
      (24*k^3+2032)*(k^3-k^2)*k^4 ≤ 274*k^11 := by
  by_cases he : k=2
  · subst k; norm_num
  have hk3 : 3 ≤ k := by omega
  have h₁ : (24*(k^3-k)+2032)*(k^4-k^2)*k^4 ≤ (24*k^3+2032)*k^4*k^4 := by
    gcongr <;> exact Nat.sub_le _ _
  have h₂ : (24*k^3+2032)*(k^3-k^2)*k^4 ≤ (24*k^3+2032)*k^3*k^4 := by
    gcongr; exact Nat.sub_le _ _
  have h10 : 3*k^10 ≤ k^11 := by nlinarith [Nat.mul_le_mul_right (k^10) hk3]
  have h8 : 27*k^8 ≤ k^11 := by nlinarith [Nat.mul_le_mul_right (k^8) (Nat.pow_le_pow_left hk3 3)]
  have h7 : 81*k^7 ≤ k^11 := by nlinarith [Nat.mul_le_mul_right (k^7) (Nat.pow_le_pow_left hk3 4)]
  have hsum := Nat.add_le_add h₁ h₂
  apply hsum.trans
  nlinarith only [h10,h8,h7,Nat.zero_le (k^11)]

/-- Sort every nonblank tile into its target square. The two exchange schedules
return the blank and restore the initially sorted reservoirs exactly. -/
theorem exists_arrangement_path (hk : 2 ≤ k) (B : Board (k^4))
    (hclear : Clear (k := k) B) (hsorted : ReservoirSorted (k := k) B) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ 274*k^11 ∧ blank C = blank B ∧
      SquaresSorted (k := k) C ∧
      ∀ (i : GroupIndex k) x, reservoir i x → C x = B x := by
  obtain ⟨D,p,hp,hbD,hDV,hDH,hDR⟩ := exists_vertical_arrangement_path hk B hclear
  have hH : ∀ (i : GroupIndex k) x, horizontal i x → D x ∈ targetGroup i := by
    intro i x hx
    rw [hDH i x hx]
    exact hclear.1 i x hx
  obtain ⟨C,q,hq,hbC,hCH,hCV,hCR⟩ := exists_horizontal_arrangement_path hk D hH
  have hR (i : GroupIndex k) (x : Cell (k^4)) (hx : reservoir i x) : C x = B x :=
    (hCR i x hx).trans (hDR i x hx)
  refine ⟨C,p.append q,?_,hbC.trans hbD,?_,hR⟩
  · rw [Path.length_append]
    exact (Nat.add_le_add hp hq).trans (arrangement_budget_le k hk)
  · intro i x hxi hnonzero
    rcases covers hk rfl x with ⟨j,hxH⟩ | ⟨j,l,hxV⟩ | ⟨j,hxR⟩
    · let a : SliceIndex k := (j,groupCol i)
      have hxa : x ∈ horizontalSliceCells a.1 a.2 := by
        apply (mem_horizontalSliceCells _ _ _).mpr
        exact ⟨hxH,hxi.2.2⟩
      have he : sliceDestination a = i :=
        square_unique hk (horizontalSlice_subset_square hk a hxa) hxi
      rw [← he]
      exact hCH a x hxa
    · have he : j=i := square_unique hk (vertical_subset_square hk hxV) hxi
      rw [hCV j l x hxV,← he]
      exact hDV j l x hxV
    · have he : j=i := square_unique hk (reservoir_subset_square hxR) hxi
      rw [hR j x hxR,← he]
      apply hsorted j x hxR
      rwa [hR j x hxR] at hnonzero
end SlidingPuzzle.Partition

namespace SlidingPuzzle.Algorithm
open SlidingPuzzle.Partition

/-- The two exchange schedules discharge the arrangement contract. -/
theorem arrangeContract_bulk : ArrangeContract 274 := by
  intro k hk
  let : NeZero (k^4) := ⟨by positivity⟩
  apply BoundedPhase.of_length_bound
  intro B hB
  obtain ⟨C,p,hp,hblank,hsorted,_⟩ := exists_arrangement_path hk B hB.clear hB.sorted
  refine ⟨C,p,Arranged.of_path hB.reachable p hsorted ?_,hp⟩
  rw [hblank]
  exact reservoir_subset_square hB.blank_last
end SlidingPuzzle.Algorithm

namespace SlidingPuzzle.Algorithm
/-- Compatibility with the earlier, looser phase package. -/
theorem arrangeContract : ArrangeContract 3277 := by
  intro k hk B hB
  obtain ⟨C,p,hC,hp⟩ := arrangeContract_bulk k hk B hB
  exact ⟨C,p,hC,hp.trans (by gcongr; norm_num)⟩
end SlidingPuzzle.Algorithm
