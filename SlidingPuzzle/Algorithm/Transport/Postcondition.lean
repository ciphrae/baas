import SlidingPuzzle.Algorithm.Transport.BoardMatrix

/-! Postconditions translating the count transport abstraction back to the
concrete reservoir partition. -/
namespace SlidingPuzzle.Partition
noncomputable section
open Classical

/-- Zero off-diagonal mass says exactly that every off-diagonal entry vanishes. -/
theorem offdiagMass_eq_zero_iff {m : ℕ} (C : TransportCounts.CountMatrix m) :
    TransportCounts.offdiagMass C = 0 ↔
      ∀ r c, r ≠ c → C r c = 0 := by
  constructor
  · intro h r c hrc
    have hsum : ∑ i, TransportCounts.incoming C i = 0 := by
      simpa only [← TransportCounts.offdiagMass_eq_sum_incoming] using h
    have hzero : TransportCounts.incoming C c = 0 := by
      have hle : TransportCounts.incoming C c ≤ ∑ i, TransportCounts.incoming C i :=
        Finset.single_le_sum (s := Finset.univ) (f := TransportCounts.incoming C)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      omega
    exact TransportCounts.incoming_zero_entry C hzero hrc
  · intro h
    unfold TransportCounts.offdiagMass
    apply Finset.sum_eq_zero
    intro r _
    apply Finset.sum_eq_zero
    intro c _
    by_cases hrc : r = c
    · simp [hrc]
    · simp [hrc, h r c hrc]

/-- A reservoir is sorted precisely when its concrete transport matrix has no
off-diagonal mass. -/
theorem reservoirSorted_iff_boardMatrix_offdiagMass_eq_zero {n k : ℕ} [NeZero n]
    (hk : Dims n k) (B : Board n) :
    ReservoirSorted (k := k) B ↔
      TransportCounts.offdiagMass (boardMatrix hk B) = 0 := by
  constructor
  · intro hsorted
    apply (offdiagMass_eq_zero_iff _).mpr
    intro r c hrc
    by_contra hne
    have hpos : 0 < boardMatrix hk B r c := Nat.pos_of_ne_zero hne
    obtain ⟨a, ha, hgroup⟩ := (reservoirCount_pos_iff B _ _).mp (by
      simpa only [boardMatrix] using hpos)
    have hnonzero : (B a).val ≠ 0 := by
      intro hz
      have he : B a = 0 := Fin.ext hz
      rw [he] at hgroup
      exact zero_not_mem_targetGroup _ hgroup
    have hsorted' := hsorted (transportIndex k hk r) a ha hnonzero
    have hindices : transportIndex k hk r = transportIndex k hk c := by
      by_contra hrc'
      exact (Finset.disjoint_left.mp (targetGroups_disjoint hk hrc')) hsorted' hgroup
    exact hrc ((transportIndex k hk).injective hindices)
  · intro hmass i a ha hnonzero
    obtain ⟨j, hj⟩ := targetGroups_cover hk (B a) hnonzero
    by_cases hji : j = i
    · simpa [hji] using hj
    · have hrc : (transportIndex k hk).symm i ≠ (transportIndex k hk).symm j := by
        intro h
        apply hji
        exact (by simpa using (congrArg (transportIndex k hk) h).symm)
      have hzero : reservoirCount B i j = 0 := by
        simpa only [boardMatrix, Equiv.apply_symm_apply] using
          ((offdiagMass_eq_zero_iff _).mp hmass _ _ hrc)
      have hpos : 0 < reservoirCount B i j :=
        (reservoirCount_pos_iff B i j).mpr ⟨a, ha, hj⟩
      omega

/-- Once the corridors are clear and every nonblank reservoir tile is in its
own target group, the blank occupies the final reservoir. -/
theorem clear_reservoirSorted_blank_in_lastReservoir {n k : ℕ} [NeZero n]
    (hk : Dims n k) (B : Board n)
    (hclear : Clear (k := k) B) (hsorted : ReservoirSorted (k := k) B) :
    reservoir (lastGroup k hk) (blank B) := by
  obtain ⟨i, hi⟩ := blank_in_reservoir hk B hclear
  let b := (transportIndex k hk).symm i
  have hb : reservoir (transportIndex k hk b) (blank B) := by
    simpa [b] using hi
  have hmass : TransportCounts.offdiagMass (boardMatrix hk B) = 0 :=
    (reservoirSorted_iff_boardMatrix_offdiagMass_eq_zero hk B).mp hsorted
  have hall := (offdiagMass_eq_zero_iff _).mp hmass
  have hincoming : TransportCounts.incoming (boardMatrix hk B) b = 0 := by
    unfold TransportCounts.incoming
    apply Finset.sum_eq_zero
    intro r _
    by_cases hr : r = b
    · simp [hr]
    · simp [hr, hall r b hr]
  have hinvariant : TransportCounts.LastInvariant (boardMatrix hk B) := by
    intro c _ _ r hrc
    exact hall r c hrc
  obtain ⟨hblast, _⟩ := TransportCounts.terminal_of_margins (boardMatrix hk B) b
    ((side n k-k)*(side n k-k^2)) (boardMatrix_margins hk B hclear b hb) hinvariant hincoming
  rw [← transportIndex_last k hk, ← hblast]
  exact hb

end
end SlidingPuzzle.Partition
