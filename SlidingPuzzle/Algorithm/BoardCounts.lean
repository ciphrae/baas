import SlidingPuzzle.Algorithm.Cardinalities

/-! Counts of actual board labels in the paper's regions. -/
namespace SlidingPuzzle.Partition
noncomputable section
open Classical

/-- A nonblank tile belongs to exactly one target group. -/
theorem sum_targetGroup_indicator {n k : ℕ} (hk : 2 ≤ k) (hn : n=k^4) (t : Tile n) :
    (∑ j : GroupIndex k, if t ∈ targetGroup j then 1 else 0) =
      if t.val = 0 then 0 else 1 := by
  by_cases ht : t.val=0
  · simp [mem_targetGroup,ht]
  · obtain ⟨j,hj⟩ := targetGroups_cover hk hn t ht
    rw [if_neg ht]
    rw [Finset.sum_eq_single j]
    · simp [hj]
    · intro l _ hlj
      have hl : t ∉ targetGroup l := by
        intro hl
        exact (Finset.disjoint_left.mp (targetGroups_disjoint hk hlj)) hl hj
      simp [hl]
    · simp

/-- Number of tiles destined for group `j` currently in reservoir `i`. -/
def reservoirCount {n k : ℕ} (B : Board n) (i j : GroupIndex k) : ℕ :=
    ∑ c ∈ reservoirCells i, if B c ∈ targetGroup j then 1 else 0

/-- All target-group counts exhaust a reservoir except for its possible blank. -/
theorem reservoirCount_row {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hn : n=k^4)
    (B : Board n) (i : GroupIndex k) :
    (∑ j : GroupIndex k, reservoirCount B i j) +
      (if reservoir i (blank B) then 1 else 0) = (k^3-k)*(k^3-k^2) := by
  have hz (c : Cell n) : (B c).val=0 ↔ c=blank B := by
    constructor
    · intro h
      apply B.injective
      exact (Fin.ext h).trans (B.apply_symm_apply 0).symm
    · rintro rfl
      simp [blank,position]
  have he : (∑ j : GroupIndex k, reservoirCount B i j) =
      ((reservoirCells i).erase (blank B)).card := by
    unfold reservoirCount
    rw [Finset.sum_comm]
    simp_rw [sum_targetGroup_indicator hk hn, hz]
    rw [Finset.card_eq_sum_ones]
    have hf : (reservoirCells i).erase (blank B) =
        (reservoirCells i).filter (fun c => c ≠ blank B) := by ext c; simp [and_comm]
    rw [hf, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : c=blank B <;> simp [h]
  rw [he]
  have hc := card_reservoir hn i
  by_cases h : reservoir i (blank B)
  · rw [if_pos h]
    exact (Finset.card_erase_add_one ((mem_reservoirCells i _).mpr h)).trans hc
  · rw [if_neg h, Nat.add_zero, Finset.erase_eq_of_notMem (by simpa using h), hc]
/-- Counting a target group over an entire board is independent of its arrangement. -/
theorem board_targetGroup_count {n k : ℕ} (B : Board n) (j : GroupIndex k) :
    (∑ c : Cell n, if B c ∈ targetGroup j then 1 else 0) =
      (targetGroup (n := n) j).card := by
  calc
    _ = ∑ t : Tile n, if t ∈ targetGroup j then 1 else 0 :=
      Fintype.sum_equiv B _ _ (fun _ => rfl)
    _ = _ := by simp [targetGroup]

/-- Every cell is counted exactly once among horizontal, vertical, and reservoir regions. -/
theorem sum_region_indicators {n k : ℕ} (hk : 2 ≤ k) (hn : n=k^4) (c : Cell n) :
    (∑ i : GroupIndex k, if horizontal i c then 1 else 0) +
    (∑ i : GroupIndex k, ∑ j : GroupIndex k, if vertical i j c then 1 else 0) +
    (∑ i : GroupIndex k, if reservoir i c then 1 else 0) = 1 := by
  obtain h | h | h := covers hk hn c
  · obtain ⟨i,hi⟩ := h
    have hv : ∀ a b : GroupIndex k, ¬ vertical a b c :=
      fun a b h => horizontal_not_vertical hk hi h
    have hr : ∀ a : GroupIndex k, ¬ reservoir a c :=
      fun a h => horizontal_not_reservoir hk hi h
    simp only [hv, hr, if_false, Finset.sum_const_zero, Nat.add_zero]
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro a _ ha
      have : ¬ horizontal a c := fun h => ha (horizontal_unique hk h hi)
      simp [this]
    · simp
  · obtain ⟨i,j,hij⟩ := h
    have hh : ∀ a : GroupIndex k, ¬ horizontal a c :=
      fun a h => horizontal_not_vertical hk h hij
    have hr : ∀ a : GroupIndex k, ¬ reservoir a c :=
      fun a h => vertical_not_reservoir hk hij h
    simp only [hh, hr, if_false, Finset.sum_const_zero, Nat.zero_add, Nat.add_zero]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · simp [hij]
      · intro b _ hb
        have : ¬ vertical i b c := fun h => hb (vertical_unique hk h hij).2
        simp [this]
      · simp
    · intro a _ ha
      apply Finset.sum_eq_zero
      intro b _
      have : ¬ vertical a b c := fun h => ha (vertical_unique hk h hij).1
      simp [this]
    · simp
  · obtain ⟨i,hi⟩ := h
    have hh : ∀ a : GroupIndex k, ¬ horizontal a c :=
      fun a h => horizontal_not_reservoir hk h hi
    have hv : ∀ a b : GroupIndex k, ¬ vertical a b c :=
      fun a b h => vertical_not_reservoir hk h hi
    simp only [hh, hv, if_false, Finset.sum_const_zero, Nat.zero_add]
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro a _ ha
      have : ¬ reservoir a c := fun h => ha (reservoir_unique hk h hi)
      simp [this]
    · simp

/-- Summation over the board splits into the three disjoint region families. -/
theorem sum_regions {n k : ℕ} (hk : 2 ≤ k) (hn : n=k^4) (w : Cell n → ℕ) :
    (∑ c, w c) =
    (∑ i : GroupIndex k, ∑ c ∈ horizontalCells i, w c) +
    (∑ i : GroupIndex k, ∑ j : GroupIndex k, ∑ c ∈ verticalCells i j, w c) +
    (∑ i : GroupIndex k, ∑ c ∈ reservoirCells i, w c) := by
  have h (c : Cell n) := congrArg (fun a : ℕ => a * w c) (sum_region_indicators hk hn c)
  simp only [Nat.add_mul, Finset.sum_mul, ite_mul, one_mul, zero_mul] at h
  simp only [horizontalCells, verticalCells, reservoirCells, Finset.sum_filter]
  rw [Finset.sum_comm (f := fun i c => if horizontal i c then w c else 0)]
  rw [Finset.sum_comm (f := fun i c => if reservoir i c then w c else 0)]
  have hv : (∑ i : GroupIndex k, ∑ j : GroupIndex k,
      ∑ c : Cell n, if vertical i j c then w c else 0) =
      ∑ c : Cell n, ∑ i : GroupIndex k, ∑ j : GroupIndex k,
        if vertical i j c then w c else 0 := by
    simp_rw [Finset.sum_comm (f := fun j c => if vertical _ j c then w c else 0)]
    rw [Finset.sum_comm]
  rw [hv, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun c _ => (h c).symm)

private theorem indicator_of_mem_group {n k : ℕ} (hk : 2 ≤ k)
    {t : Tile n} {i : GroupIndex k} (ht : t ∈ targetGroup i) (j : GroupIndex k) :
    (if t ∈ targetGroup j then 1 else 0 : ℕ) = if i=j then 1 else 0 := by
  by_cases h : i=j
  · subst j; simp [ht]
  · have hnot : t ∉ targetGroup j :=
      fun hj => (Finset.disjoint_left.mp (targetGroups_disjoint hk h)) ht hj
    simp [h,hnot]

/-- Clear corridors contain a fixed number of labels from every target group. -/
theorem clear_corridor_count {n k : ℕ} (hk : 2 ≤ k) (hn : n=k^4)
    (B : Board n) (hB : Clear (k := k) B) (j : GroupIndex k) :
    (∑ i : GroupIndex k, ∑ c ∈ horizontalCells i,
      if B c ∈ targetGroup j then 1 else 0) +
    (∑ i : GroupIndex k, ∑ l : GroupIndex k, ∑ c ∈ verticalCells i l,
      if B c ∈ targetGroup j then 1 else 0) = n + k^2*(k^3-k) := by
  have hh (i : GroupIndex k) :
      (∑ c ∈ horizontalCells i, if B c ∈ targetGroup j then 1 else 0) =
        if i=j then n else 0 := by
    calc
      _ = ∑ _c ∈ horizontalCells (n := n) i, if i=j then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro c hc
        exact indicator_of_mem_group hk (hB.1 i c ((mem_horizontalCells i c).mp hc)) j
      _ = _ := by split_ifs <;> simp [card_horizontal hk hn]
  have hv (i l : GroupIndex k) :
      (∑ c ∈ verticalCells i l, if B c ∈ targetGroup j then 1 else 0) =
        if l=j then k^3-k else 0 := by
    calc
      _ = ∑ _c ∈ verticalCells (n := n) i l, if l=j then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro c hc
        exact indicator_of_mem_group hk (hB.2 i l c ((mem_verticalCells i l c).mp hc)) j
      _ = _ := by split_ifs <;> simp [card_vertical hk hn]
  simp_rw [hh,hv]
  simp [GroupIndex, pow_two]

/-- The column totals follow from the target-group size and the clear corridors. -/
theorem reservoirCount_column {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hn : n=k^4)
    (B : Board n) (hB : Clear (k := k) B) (j : GroupIndex k) :
    (∑ i : GroupIndex k, reservoirCount B i j) +
      (if square j (blank (target n)) then 1 else 0) = (k^3-k)*(k^3-k^2) := by
  have htotal := sum_regions hk hn (fun c : Cell n => if B c ∈ targetGroup j then 1 else 0)
  rw [board_targetGroup_count B j, clear_corridor_count hk hn B hB j] at htotal
  have hcard := card_targetGroup hn j
  have hk2 : k ≤ k^2 := by nlinarith
  have hk3 : k^2 ≤ k^3 := by nlinarith [Nat.mul_le_mul_left k hk2]
  have hcap : (k^3-k)*(k^3-k^2) + (n+k^2*(k^3-k)) = k^6 := by
    rw [hn]
    have h1 : k^3-k+k=k^3 := Nat.sub_add_cancel (hk2.trans hk3)
    have h2 : k^3-k^2+k^2=k^3 := Nat.sub_add_cancel hk3
    nlinarith [sq_nonneg (k^3), Nat.mul_sub_left_distrib (k^3-k) (k^3) (k^2)]
  unfold reservoirCount
  omega

end
end SlidingPuzzle.Partition
