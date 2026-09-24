import SlidingPuzzle.Algorithm.PreparationVertical
import SlidingPuzzle.Algorithm.PhaseContracts

/-! Complete preparation: stage quotas, install representatives, and spread both
corridor families, with a uniform all-moves bound. -/
namespace SlidingPuzzle
namespace Partition

/- Preparation is a concrete legal construction for every board. Its endpoint
has clear corridors and a nonblank representative of every nonfinal group in
the last reservoir. The initial board need not be reachable. -/
/-- Preparation inherits any protected-prefix bound. -/
theorem exists_preparation_path_of_bound {P k : ℕ}
    (hprefix : PrefixPathBound P) (hk : 2 ≤ k) [NeZero (k^4)]
    (B : Board (k^4)) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ (P+29)*k^11 ∧ Clear (k := k) C ∧ LastRepresentatives hk C := by
  classical
  obtain ⟨A,p,hp,_,hH,hV,hR,hb⟩ := exists_horizontal_prepared_path_with_blank_of_bound hprefix hk B
  obtain ⟨C,q,hq,hclear,hfix⟩ := exists_vertical_preparation_path hk A hb hH hV
  refine ⟨C,p.append q,?_,hclear,?_⟩
  · rw [Path.length_append]
    nlinarith
  · intro i hi
    have hc : representativeDestination hk i ∈ reservoirCells (lastGroup k hk) := by
      simpa only [mem_reservoirCells] using representative_destination_in_last_reservoir hk i
    have hmem : C (representativeDestination hk i) ∈ targetGroup i := by
      rw [hfix]
      exact hR i hi
    unfold reservoirCount
    have hh := Finset.single_le_sum (f := fun x : Cell (k^4) =>
      if C x ∈ targetGroup i then 1 else 0) (fun _ _ => Nat.zero_le _) hc
    rw [if_pos hmem] at hh
    omega

theorem exists_preparation_path {k : ℕ} (hk : 2 ≤ k) [NeZero (k^4)]
    (B : Board (k^4)) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ 1033*k^11 ∧ Clear (k := k) C ∧ LastRepresentatives hk C := by
  exact exists_preparation_path_of_bound prefixPathBound_current hk B

end Partition
namespace Algorithm

/-- The first of the four algorithmic phase contracts is now discharged. -/
theorem preparationContract : PreparationContract 1033 := by
  intro k hk
  letI : NeZero (k^4) := ⟨by positivity⟩
  apply BoundedPhase.of_length_bound
  intro B hB
  obtain ⟨C,p,hp,hclear,hrep⟩ := Partition.exists_preparation_path hk B
  exact ⟨C,p,Partition.Prepared.of_path hB p hclear hrep,hp⟩

/-- The sole place where the shared prefix cost enters Preparation. -/
theorem preparationContract_of_prefix_bound {P : ℕ}
    (hprefix : PrefixPathBound P) : PreparationContract (P+29) := by
  intro k hk
  letI : NeZero (k^4) := ⟨by positivity⟩
  apply BoundedPhase.of_length_bound
  intro B hB
  obtain ⟨C,p,hp,hclear,hrep⟩ := Partition.exists_preparation_path_of_bound hprefix hk B
  exact ⟨C,p,Partition.Prepared.of_path hB p hclear hrep,hp⟩

end Algorithm
end SlidingPuzzle
