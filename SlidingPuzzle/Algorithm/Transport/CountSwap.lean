import SlidingPuzzle.Algorithm.BoardCounts
import SlidingPuzzle.Moves.Local

/-! The effect on reservoir counts of a blank/tile transposition.
This specifies the endpoint effect; it does not claim arbitrary transpositions are legal moves. -/
namespace SlidingPuzzle.Partition
noncomputable section
open Classical

private theorem sum_two_changes {α : Type*} [Fintype α] [DecidableEq α]
    (f g : α → ℕ) (a b : α) (hab : a ≠ b)
    (h : ∀ c, c ≠ a → c ≠ b → f c=g c) :
    (∑ c, f c) + g a + g b = (∑ c, g c) + f a + f b := by
  have ha : a ∈ (Finset.univ : Finset α) := Finset.mem_univ a
  have hb : b ∈ (Finset.univ : Finset α).erase a := by simp [hab.symm]
  have hf := Finset.sum_erase_add _ f ha
  have hg := Finset.sum_erase_add _ g ha
  have hf' := Finset.sum_erase_add _ f hb
  have hg' := Finset.sum_erase_add _ g hb
  have he : (∑ c ∈ (Finset.univ.erase a).erase b, f c) =
      ∑ c ∈ (Finset.univ.erase a).erase b, g c := by
    apply Finset.sum_congr rfl
    intro c hc
    exact h c (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1 (Finset.mem_erase.mp hc).1
  omega

/-- A swap changes reservoir counts only by removing and inserting its two endpoint labels. -/
theorem reservoirCount_swap_balance {n k : ℕ} (B : Board n) (a b : Cell n)
    (hab : a ≠ b) (r c : GroupIndex k) :
    reservoirCount (swapCells B a b) r c +
      (if reservoir r a ∧ B a ∈ targetGroup c then 1 else 0) +
      (if reservoir r b ∧ B b ∈ targetGroup c then 1 else 0) =
    reservoirCount B r c +
      (if reservoir r a ∧ B b ∈ targetGroup c then 1 else 0) +
      (if reservoir r b ∧ B a ∈ targetGroup c then 1 else 0) := by
  have h := sum_two_changes
    (fun x : Cell n => if reservoir r x ∧ swapCells B a b x ∈ targetGroup c then 1 else 0)
    (fun x : Cell n => if reservoir r x ∧ B x ∈ targetGroup c then 1 else 0)
    a b hab (fun x hxa hxb => by rw [swapCells_preserves B hxa hxb])
  simp only [swapCells_at_left,swapCells_at_right] at h
  simpa only [reservoirCount,reservoirCells,Finset.sum_filter,ite_and,ite_self] using h

/-- Reservoir swaps preserve the clear corridor condition. -/
theorem clear_swap_reservoirs {n k : ℕ} (hk : Dims n k) (B : Board n)
    (hB : Clear (k := k) B) {a b : Cell n} {i j : GroupIndex k}
    (ha : reservoir i a) (hb : reservoir j b) : Clear (k := k) (swapCells B a b) := by
  constructor
  · intro l c hc
    rw [swapCells_preserves B
      (fun h => horizontal_not_reservoir hk (h ▸ hc) ha)
      (fun h => horizontal_not_reservoir hk (h ▸ hc) hb)]
    exact hB.1 l c hc
  · intro l m c hc
    rw [swapCells_preserves B
      (fun h => vertical_not_reservoir hk (h ▸ hc) ha)
      (fun h => vertical_not_reservoir hk (h ▸ hc) hb)]
    exact hB.2 l m c hc
/-- Exchanging the blank with an incoming tile gives exactly the count algorithm's update. -/
theorem reservoirCount_transport_swap {n k : ℕ} [NeZero n] (hk : Dims n k)
    (B : Board n) {a b : Cell n} {i j : GroupIndex k}
    (ha : reservoir i a) (hb : reservoir j b) (hji : j ≠ i)
    (hblank : blank B=a) (ht : B b ∈ targetGroup i) (r c : GroupIndex k) :
    reservoirCount (swapCells B a b) r c =
      if r=j ∧ c=i then reservoirCount B r c-1
      else if r=i ∧ c=i then reservoirCount B r c+1
      else reservoirCount B r c := by
  have hab : a ≠ b := by
    intro h
    exact hji (reservoir_unique hk hb (h ▸ ha))
  have hz : B a=0 := by rw [← hblank]; exact B.apply_symm_apply 0
  have har : reservoir r a ↔ r=i :=
    ⟨fun h => reservoir_unique hk h ha, fun h => h ▸ ha⟩
  have hbr : reservoir r b ↔ r=j :=
    ⟨fun h => reservoir_unique hk h hb, fun h => h ▸ hb⟩
  have htc : B b ∈ targetGroup c ↔ c=i := by
    constructor
    · intro hc
      by_contra h
      exact (Finset.disjoint_left.mp (targetGroups_disjoint hk h)) hc ht
    · rintro rfl; exact ht
  have h := reservoirCount_swap_balance B a b hab r c
  simp only [hz,zero_not_mem_targetGroup,and_false,if_false,Nat.add_zero,har,hbr,htc] at h
  split_ifs with hs hd
  · rcases hs with ⟨rfl,rfl⟩
    simp [hji] at h
    omega
  · rcases hd with ⟨rfl,rfl⟩
    simpa [hji.symm] using h
  · simpa only [hs,hd,if_false,Nat.add_zero] using h
/-- A positive reservoir count supplies an actual tile position. -/
theorem reservoirCount_pos_iff {n k : ℕ} (B : Board n) (i j : GroupIndex k) :
    0 < reservoirCount B i j ↔ ∃ c : Cell n, reservoir i c ∧ B c ∈ targetGroup j := by
  constructor
  · intro h
    by_contra hex
    have hz : reservoirCount B i j=0 := by
      apply Finset.sum_eq_zero
      intro c hc
      have ht : B c ∉ targetGroup j :=
        fun ht => hex ⟨c,(mem_reservoirCells i c).mp hc,ht⟩
      simp [ht]
    omega
  · rintro ⟨c,hc,ht⟩
    have h := Finset.single_le_sum (fun x (_hx : x ∈ reservoirCells i) =>
      Nat.zero_le (if B x ∈ targetGroup j then 1 else 0)) ((mem_reservoirCells i c).mpr hc)
    have h' : 1 ≤ reservoirCount B i j := by simpa [ht,reservoirCount] using h
    omega

end
end SlidingPuzzle.Partition
