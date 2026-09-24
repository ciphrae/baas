import SlidingPuzzle.Algorithm.PhaseStates
import SlidingPuzzle.Algorithm.Arrangement.Vertical
import SlidingPuzzle.Algorithm.Arrangement.Horizontal

/-! Phase III (Arrangement). Exchange the vertical corridors pairwise and then
the horizontal slices, so that every tile lies in its own square. Reservoirs and
the blank are restored. -/
namespace SlidingPuzzle
noncomputable section
open Classical
namespace Partition
section
variable {k : ℕ} [NeZero (k^4)]

theorem exists_arrangement_path (hk : 2 ≤ k) (B : Board (k^4))
    (hclear : Clear (k := k) B) (hsorted : ReservoirSorted (k := k) B) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ (24*(k^3-k)+2032)*(k^4-k^2)*k^4 + (24*k^3+2032)*(k^3-k^2)*k^4 ∧ blank C = blank B ∧
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
    exact Nat.add_le_add hp hq
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

end
end Partition
end
end SlidingPuzzle
