import SlidingPuzzle.Algorithm.Transport.BoardMatrix

/-! A transport iteration moves only tiles from one target group. Treating the
blank as a member of that group gives an invariant which composes even while
the blank is inside a corridor. At the endpoint it determines the count update. -/
namespace SlidingPuzzle.Partition
noncomputable section
open Classical

variable {n k : ℕ} [NeZero n]

/-- Group memberships agree after temporarily assigning the blank to group i. -/
def GroupEquivalent (i : GroupIndex k) (A B : Board n) : Prop :=
  ∀ (c : Cell n) (j : GroupIndex k),
    (A c ∈ targetGroup j ∨ (c = blank A ∧ j = i)) ↔
      (B c ∈ targetGroup j ∨ (c = blank B ∧ j = i))

theorem GroupEquivalent.refl (i : GroupIndex k) (B : Board n) : GroupEquivalent i B B :=
  fun _ _ => Iff.rfl

theorem GroupEquivalent.symm {i : GroupIndex k} {A B : Board n}
    (h : GroupEquivalent i A B) : GroupEquivalent i B A := fun c j => (h c j).symm

theorem GroupEquivalent.trans {i : GroupIndex k} {A B C : Board n}
    (h : GroupEquivalent i A B) (h' : GroupEquivalent i B C) : GroupEquivalent i A C :=
  fun c j => (h c j).trans (h' c j)

omit [NeZero n] in
theorem targetGroup_membership_iff (hk : Dims n k) {t : Tile n} {i : GroupIndex k}
    (ht : t ∈ targetGroup i) (j : GroupIndex k) : t ∈ targetGroup j ↔ j = i := by
  constructor
  · intro hj
    by_contra hji
    exact Finset.disjoint_left.mp (targetGroups_disjoint hk hji) hj ht
  · rintro rfl; exact ht

/-- Any jump or ordinary move which exchanges the blank with a tile of group
i preserves the filled-blank group invariant. -/
theorem groupEquivalent_swap (hk : Dims n k) (B : Board n) (i : GroupIndex k)
    (b : Cell n) (ht : B b ∈ targetGroup i) :
    GroupEquivalent i B (swapCells B (blank B) b) := by
  have hne : b ≠ blank B := by
    intro h
    have hz : B (blank B) = 0 := B.apply_symm_apply 0
    rw [h, hz] at ht
    exact zero_not_mem_targetGroup i ht
  intro c j
  rw [blank_swapCells]
  by_cases ha : c = blank B
  · subst c
    simp only [swapCells_at_left, show B (blank B) = 0 from B.apply_symm_apply 0,
      zero_not_mem_targetGroup, false_or, true_and,
      targetGroup_membership_iff hk ht j]
    simp [hne.symm]
  · by_cases hb : c = b
    · subst c
      simp only [swapCells_at_right, show B (blank B) = 0 from B.apply_symm_apply 0,
        zero_not_mem_targetGroup, targetGroup_membership_iff hk ht j]
      simp [hne]
    · rw [swapCells_preserves B ha hb]
      simp [ha, hb]

/-- A region filled with one group (apart from its blank) may be rearranged
arbitrarily without changing the invariant, provided outside cells are fixed. -/
theorem groupEquivalent_of_region (hk : Dims n k) (i : GroupIndex k)
    (A B : Board n) (S : Set (Cell n)) (ha : blank A ∈ S) (hb : blank B ∈ S)
    (hA : ∀ c ∈ S, c ≠ blank A → A c ∈ targetGroup i)
    (hB : ∀ c ∈ S, c ≠ blank B → B c ∈ targetGroup i)
    (hfix : ∀ c, c ∉ S → B c = A c) : GroupEquivalent i A B := by
  intro c j
  by_cases hc : c ∈ S
  · have hlocal (D : Board n) (hd : c ≠ blank D → D c ∈ targetGroup i) :
        (D c ∈ targetGroup j ∨ (c = blank D ∧ j = i)) ↔ j = i := by
      by_cases hz : c = blank D
      · subst c
        simp [show D (blank D) = 0 from D.apply_symm_apply 0]
      · simp [hz, targetGroup_membership_iff hk (hd hz) j]
    exact (hlocal A (hA c hc)).trans (hlocal B (hB c hc)).symm
  · have hca : c ≠ blank A := fun h => hc (h ▸ ha)
    have hcb : c ≠ blank B := fun h => hc (h ▸ hb)
    rw [hfix c hc]
    simp [hca, hcb]

/-- A corridor containing group i in the input still contains group i at every
nonblank cell of a group-equivalent intermediate board. -/
theorem GroupEquivalent.mem_targetGroup {i : GroupIndex k} {A B : Board n}
    (h : GroupEquivalent i A B) {c : Cell n}
    (hc : A c ∈ targetGroup i) (hne : c ≠ blank B) : B c ∈ targetGroup i := by
  rcases (h c i).mp (Or.inl hc) with ht | hb
  · exact ht
  · exact (hne hb.1).elim

/-- Equal final blank locations remove the temporary group assignment. -/
theorem GroupEquivalent.membership_iff {i : GroupIndex k} {A B : Board n}
    (h : GroupEquivalent i A B) (hb : blank A = blank B)
    (c : Cell n) (j : GroupIndex k) : A c ∈ targetGroup j ↔ B c ∈ targetGroup j := by
  by_cases hc : c = blank A
  · have ha0 : A c = 0 := by rw [hc]; exact A.apply_symm_apply 0
    have hb0 : B c = 0 := by rw [hc, hb]; exact B.apply_symm_apply 0
    simp [ha0, hb0]
  · have hc' : c ≠ blank B := by rwa [← hb]
    simpa [hc, hc'] using h c j

/-- Group equivalence preserves Clear when the final blank lies in a reservoir. -/
theorem GroupEquivalent.clear (hk : Dims n k) {i : GroupIndex k} {A B : Board n}
    (h : GroupEquivalent i A B) (hA : Clear (k := k) A)
    {s : GroupIndex k} (hb : reservoir s (blank B)) :
    Clear (k := k) B := by
  constructor
  · intro j c hc
    rcases (h c j).mp (Or.inl (hA.1 j c hc)) with ht | hz
    · exact ht
    · exact (horizontal_not_reservoir hk (hz.1 ▸ hc) hb).elim
  · intro j l c hc
    rcases (h c l).mp (Or.inl (hA.2 j l c hc)) with ht | hz
    · exact ht
    · exact (vertical_not_reservoir hk (hz.1 ▸ hc) hb).elim

/-- The endpoint of any group-i route to the selected source tile has exactly
the count effect of a direct blank/tile swap, even if corridor labels moved. -/
theorem GroupEquivalent.boardMatrix_eq_swap (hk : Dims n k) (i : GroupIndex k)
    (A B : Board n) (b : Cell n) (ht : A b ∈ targetGroup i)
    (h : GroupEquivalent i A B) (hb : blank B = b) :
    boardMatrix hk B = boardMatrix hk (swapCells A (blank A) b) := by
  have he := h.symm.trans (groupEquivalent_swap hk A i b ht)
  have heblank : blank B = blank (swapCells A (blank A) b) := by simpa using hb
  funext r c
  unfold boardMatrix reservoirCount
  apply Finset.sum_congr rfl
  intro x _
  simp only [he.membership_iff heblank x (transportIndex k hk c)]

end
end SlidingPuzzle.Partition
