import SlidingPuzzle.Algorithm.PhaseStates
import SlidingPuzzle.Algorithm.Arrangement.Vertical
import SlidingPuzzle.Algorithm.Arrangement.Horizontal

/-! Phase III (Arrangement). Exchange the vertical corridors pairwise, moving one
family next to the other (`exists_vertical_arrangement_path_near`), then the
horizontal corridor rows, so that every tile lies in its own square. Reservoirs and the
blank are restored. -/
namespace SlidingPuzzle
noncomputable section
open Classical
namespace Partition
section
variable {n k : ℕ} [NeZero n]

theorem exists_arrangement_path (hk : Dims n k) (B : Board n)
    (hclear : Clear (k := k) B) (hsorted : ReservoirSorted (k := k) B)
    (hblank : ∃ g : GroupIndex k, reservoir g (blank B)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 3*(k^5*side n k^2)+22*(k*side n k^3) + (24*side n k+2032)*(4*k^3)*n ∧
      blank C = blank B ∧
      SquaresSorted (k := k) C ∧
      ∀ (i : GroupIndex k) x, reservoir i x → C x = B x := by
  obtain ⟨D,p,hp,hbD,hDV,hDH,hDR⟩ := exists_vertical_arrangement_path_near hk B hclear hblank
  have hp' := hp.trans (sum_vcost_le hk)
  have hH : ∀ (i : GroupIndex k) x, horizontal i x → D x ∈ targetGroup i := by
    intro i x hx
    rw [hDH i x hx]
    exact hclear.1 i x hx
  obtain ⟨C,q,hq,hbC,hCH,hCV,hCR⟩ := exists_horizontal_arrangement_path hk D hH
  have hR (i : GroupIndex k) (x : Cell n) (hx : reservoir i x) : C x = B x :=
    (hCR i x hx).trans (hDR i x hx)
  refine ⟨C,p.append q,?_,hbC.trans hbD,?_,hR⟩
  · rw [Path.length_append]
    exact Nat.add_le_add hp' hq
  · intro i x hxi hnonzero
    rcases covers hk x with ⟨j,hxH⟩ | ⟨j,l,hxV⟩ | ⟨j,hxR⟩
    · obtain ⟨a, hxa⟩ := exists_slot_of_horizontal hk hxH
      have he : slotGroup a = i := square_unique hk (slotCells_subset_square hk a hxa) hxi
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
