import SlidingPuzzle.Algorithm.Cardinalities

/-! The compressed staging regions used before the corridor-clearing phase. -/
namespace SlidingPuzzle.Partition

noncomputable section
open Classical

private def axis (n lo hi : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun x => lo ≤ x.val ∧ x.val < hi

private theorem card_axis (n lo hi : ℕ) (hhi : hi ≤ n) :
    (axis n lo hi).card = hi - lo := by
  unfold axis
  rw [← Fintype.card_subtype]
  let e : {x : Fin n // lo ≤ x.val ∧ x.val < hi} ≃ Fin (hi-lo) :=
    { toFun := fun x => ⟨x.val.val-lo, by have := x.property; omega⟩
      invFun := fun x => ⟨⟨x.val+lo, by have := x.isLt; omega⟩,
        by change lo ≤ x.val+lo ∧ x.val+lo < hi; have := x.isLt; omega⟩
      left_inv := by intro x; apply Subtype.ext; apply Fin.ext; have := x.property; simp; omega
      right_inv := by intro x; apply Fin.ext; simp }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

private theorem card_rectangle {n : ℕ} (xl xh yl yh : ℕ) (hx : xh ≤ n) (hy : yh ≤ n) :
    (Finset.univ.filter (fun c : Cell n =>
      xl ≤ c.1.val ∧ c.1.val < xh ∧ yl ≤ c.2.val ∧ c.2.val < yh)).card =
      (xh-xl)*(yh-yl) := by
  have he : (Finset.univ.filter (fun c : Cell n =>
      xl ≤ c.1.val ∧ c.1.val < xh ∧ yl ≤ c.2.val ∧ c.2.val < yh)) =
      (axis n xl xh).product (axis n yl yh) := by
    ext c
    simp [axis, and_assoc]
  rw [he]
  calc
    _ = (axis n xl xh).card * (axis n yl yh).card := Finset.card_product _ _
    _ = _ := by rw [card_axis n xl xh hx, card_axis n yl yh hy]

private theorem cube_le_fourth (k : ℕ) (hk : 2 ≤ k) : k^3 ≤ k^4 := by
  calc
    k^3 ≤ k*k^3 := Nat.le_mul_of_pos_left _ (by omega)
    _ = k^4 := by ring

private theorem square_le_cube (k : ℕ) (hk : 2 ≤ k) : k^2 ≤ k^3 := by
  have hk2 : k ≤ k^2 := by nlinarith
  nlinarith [Nat.mul_le_mul_left k hk2]

private theorem block_end_le {n k : ℕ} (hn : n = k^4) (a : Fin k) :
    (a.val+1)*k^3 ≤ n := by
  calc
    (a.val+1)*k^3 ≤ k*k^3 := Nat.mul_le_mul_right _ a.isLt
    _ = n := by rw [hn]; ring

/-- The first horizontal part of group `i`'s staging area. -/
def stagingA {n k : ℕ} (i : GroupIndex k) : Finset (Cell n) :=
  Finset.univ.filter fun c => horizontal i c ∧ c.2.val < k^3

/-- The second horizontal part of group `i`'s staging area. -/
def stagingB {n k : ℕ} (i : GroupIndex k) : Finset (Cell n) :=
  Finset.univ.filter fun c => c.1.val = i.val ∧ k^3 ≤ c.2.val

/-- The strip in square `j` reserved for destination group `i`. -/
def stagingC {n k : ℕ} (j i : GroupIndex k) : Finset (Cell n) :=
  Finset.univ.filter fun c =>
    (groupRow j).val*k^3+k ≤ c.1.val ∧
    c.1.val < ((groupRow j).val+1)*k^3 ∧
    c.2.val = (groupCol j).val*k^2+i.val

/-- All cells initially set aside for destination group `i`. -/
def stagingCells {n k : ℕ} (i : GroupIndex k) : Finset (Cell n) :=
  stagingA i ∪ stagingB i ∪ Finset.univ.biUnion fun j => stagingC j i

@[simp] theorem mem_stagingA {n k : ℕ} (i : GroupIndex k) (c : Cell n) :
    c ∈ stagingA i ↔ horizontal i c ∧ c.2.val < k^3 := by simp [stagingA]

@[simp] theorem mem_stagingB {n k : ℕ} (i : GroupIndex k) (c : Cell n) :
    c ∈ stagingB i ↔ c.1.val = i.val ∧ k^3 ≤ c.2.val := by
  simp [stagingB]

@[simp] theorem mem_stagingC {n k : ℕ} (j i : GroupIndex k) (c : Cell n) :
    c ∈ stagingC j i ↔
      (groupRow j).val*k^3+k ≤ c.1.val ∧
      c.1.val < ((groupRow j).val+1)*k^3 ∧
      c.2.val = (groupCol j).val*k^2+i.val := by
  simp [stagingC]

@[simp] theorem mem_stagingCells {n k : ℕ} (i : GroupIndex k) (c : Cell n) :
    c ∈ stagingCells i ↔ c ∈ stagingA i ∨ c ∈ stagingB i ∨ ∃ j, c ∈ stagingC j i := by
  simp [stagingCells]

theorem card_stagingA {n k : ℕ} (hk : 2 ≤ k) (hn : n = k^4) (i : GroupIndex k) :
    (stagingA (n := n) i).card = k^3 := by
  have hrow : (groupRow i).val*k^3+(groupCol i).val+1 ≤ n := by
    have hblock := block_end_le hn (groupRow i)
    have hcube : k ≤ k^3 := by
      exact (show k ≤ k^2 by nlinarith).trans (square_le_cube k hk)
    have hcol : (groupCol i).val+1 ≤ k^3 := (by omega : (groupCol i).val+1 ≤ k).trans hcube
    calc
      (groupRow i).val*k^3+(groupCol i).val+1 =
          (groupRow i).val*k^3+((groupCol i).val+1) := by omega
      _ ≤ (groupRow i).val*k^3+k^3 := Nat.add_le_add_left hcol _
      _ = ((groupRow i).val+1)*k^3 := by rw [Nat.add_mul]; ring
      _ ≤ n := hblock
  have hcube : k^3 ≤ n := hn ▸ cube_le_fourth k hk
  have he : stagingA (n := n) i = Finset.univ.filter fun c : Cell n =>
      (groupRow i).val*k^3+(groupCol i).val ≤ c.1.val ∧
      c.1.val < (groupRow i).val*k^3+(groupCol i).val+1 ∧
      0 ≤ c.2.val ∧ c.2.val < k^3 := by
    ext c
    simp only [mem_stagingA, horizontal, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [he, card_rectangle _ _ 0 (k^3) hrow hcube]
  simp

theorem card_stagingB {n k : ℕ} (hk : 2 ≤ k) (hn : n = k^4) (i : GroupIndex k) :
    (stagingB (n := n) i).card = n-k^3 := by
  have hcube : k^3 ≤ n := hn ▸ cube_le_fourth k hk
  have hrow : i.val+1 ≤ n := by
    have hi : i.val+1 ≤ k^2 := by
      have : i.val+1 ≤ k*k := by omega
      simpa [pow_two] using this
    exact hi.trans ((square_le_cube k hk).trans hcube)
  have he : stagingB (n := n) i = Finset.univ.filter fun c : Cell n =>
      i.val ≤ c.1.val ∧ c.1.val < i.val+1 ∧ k^3 ≤ c.2.val ∧ c.2.val < n := by
    ext c
    simp only [mem_stagingB, Finset.mem_filter, Finset.mem_univ, true_and]
    have := c.1.isLt
    have := c.2.isLt
    omega
  rw [he, card_rectangle i.val (i.val+1) (k^3) n hrow le_rfl]
  simp

theorem card_stagingC {n k : ℕ} (hk : 2 ≤ k) (hn : n = k^4)
    (j i : GroupIndex k) :
    (stagingC (n := n) j i).card = k^3-k := by
  have hrow := block_end_le hn (groupRow j)
  have hcube : k^3 ≤ n := hn ▸ cube_le_fourth k hk
  have hcol : (groupCol j).val*k^2+i.val+1 ≤ n := by
    have hbound : (groupCol j).val*k^2+i.val+1 ≤ k^3 := by
      have hb : (groupCol j).val+1 ≤ k := by omega
      have hi : i.val+1 ≤ k^2 := by
        have : i.val+1 ≤ k*k := by omega
        simpa [pow_two] using this
      nlinarith [Nat.mul_le_mul_right (k^2) hb]
    exact hbound.trans hcube
  have he : stagingC (n := n) j i = Finset.univ.filter fun c : Cell n =>
      (groupRow j).val*k^3+k ≤ c.1.val ∧
      c.1.val < ((groupRow j).val+1)*k^3 ∧
      (groupCol j).val*k^2+i.val ≤ c.2.val ∧
      c.2.val < (groupCol j).val*k^2+i.val+1 := by
    ext c
    simp only [mem_stagingC, Finset.mem_filter, Finset.mem_univ, true_and]
    have := c.2.isLt
    omega
  rw [he, card_rectangle _ _ _ _ hrow hcol]
  rw [Nat.add_mul]
  have hr : (groupRow j).val*k^3 + 1*k^3 - ((groupRow j).val*k^3+k) = k^3-k := by
    omega
  have hc : (groupCol j).val*k^2+i.val+1 - ((groupCol j).val*k^2+i.val) = 1 := by
    omega
  rw [hr, hc]
  simp

private theorem stagingC_row_mod {n k : ℕ} (hk : 2 ≤ k)
    {j i : GroupIndex k} {c : Cell n} (h : c ∈ stagingC j i) :
    k ≤ c.1.val % k^3 := by
  have h' := (mem_stagingC j i c).mp h
  have hd : c.1.val / k^3 = (groupRow j).val := by
    apply Nat.div_eq_of_lt_le
    · have := h'.1
      omega
    · exact h'.2.1
  have he := Nat.div_add_mod' c.1.val (k^3)
  rw [hd] at he
  have := h'.1
  omega

private theorem stagingC_col_lt_cube {n k : ℕ} (hk : 2 ≤ k)
    {j i : GroupIndex k} {c : Cell n} (h : c ∈ stagingC j i) : c.2.val < k^3 := by
  have h' := (mem_stagingC j i c).mp h
  rw [h'.2.2]
  have hb : (groupCol j).val+1 ≤ k := by omega
  have hi : i.val+1 ≤ k^2 := by
    have : i.val+1 ≤ k*k := by omega
    simpa [pow_two] using this
  nlinarith [Nat.mul_le_mul_right (k^2) hb]

private theorem stagingC_col_div {n k : ℕ} {j i : GroupIndex k} {c : Cell n}
    (h : c ∈ stagingC j i) : c.2.val / k^2 = (groupCol j).val := by
  have h' := (mem_stagingC j i c).mp h
  rw [h'.2.2]
  apply Nat.div_eq_of_lt_le
  · omega
  · have hi : i.val < k^2 := by simpa [pow_two] using i.isLt
    simp only [Nat.add_mul,Nat.one_mul]
    omega

private theorem stagingC_destination_unique {n k : ℕ} {i i' j j' : GroupIndex k}
    {c : Cell n} (h : c ∈ stagingC j i) (h' : c ∈ stagingC j' i') : i = i' := by
  have hb : groupCol j = groupCol j' := Fin.ext
    ((stagingC_col_div h).symm.trans (stagingC_col_div h'))
  apply Fin.ext
  have hc := (mem_stagingC j i c).mp h
  have hc' := (mem_stagingC j' i' c).mp h'
  have he : (groupCol j).val*k^2+i.val = (groupCol j').val*k^2+i'.val :=
    hc.2.2.symm.trans hc'.2.2
  rw [hb] at he
  omega

private theorem stagingC_pairwise_disjoint {n k : ℕ} (hk : 2 ≤ k) (i : GroupIndex k) :
    (Set.univ : Set (GroupIndex k)).PairwiseDisjoint (fun j => stagingC (n := n) j i) := by
  intro j _ j' _ hnon
  apply Finset.disjoint_left.mpr
  intro c hc hc'
  apply hnon
  exact (by
    have hc0 := (mem_stagingC j i c).mp hc
    have hc0' := (mem_stagingC j' i c).mp hc'
    apply finProdFinEquiv.symm.injective
    apply Prod.ext
    · have hrow : c.1.val / k^3 = (groupRow j).val := by
        apply Nat.div_eq_of_lt_le
        · have := hc0.1; omega
        · exact hc0.2.1
      have hrow' : c.1.val / k^3 = (groupRow j').val := by
        apply Nat.div_eq_of_lt_le
        · have := hc0'.1; omega
        · exact hc0'.2.1
      exact Fin.ext (hrow.symm.trans hrow')
    · apply Fin.ext
      have he : (groupCol j).val*k^2+i.val = (groupCol j').val*k^2+i.val :=
        hc0.2.2.symm.trans hc0'.2.2
      exact Nat.eq_of_mul_eq_mul_right (by positivity) (Nat.add_right_cancel he))

/-- The combined compressed strips for destination group `i`. -/
def stagingCs {n k : ℕ} (i : GroupIndex k) : Finset (Cell n) :=
  Finset.univ.biUnion fun j => stagingC j i

theorem card_stagingCs {n k : ℕ} (hk : 2 ≤ k) (hn : n = k^4) (i : GroupIndex k) :
    (stagingCs (n := n) i).card = k^2*(k^3-k) := by
  unfold stagingCs
  rw [Finset.card_biUnion (by simpa using stagingC_pairwise_disjoint hk i)]
  simp_rw [card_stagingC hk hn]
  simp [GroupIndex, pow_two]

private theorem stagingA_disjoint_stagingB {n k : ℕ} (i : GroupIndex k) :
    Disjoint (stagingA (n := n) i) (stagingB i) := by
  apply Finset.disjoint_left.mpr
  intro c hA hB
  have hA' := (mem_stagingA i c).mp hA
  have hB' := (mem_stagingB i c).mp hB
  omega

private theorem stagingA_disjoint_stagingC {n k : ℕ} (hk : 2 ≤ k)
    (i j : GroupIndex k) : Disjoint (stagingA (n := n) i) (stagingC j i) := by
  apply Finset.disjoint_left.mpr
  intro c hA hC
  have hA' := (mem_stagingA i c).mp hA
  have hC' := (mem_stagingC j i c).mp hC
  have hsmall := horizontal_mod hk hA'.1
  have hlarge := stagingC_row_mod hk hC
  omega

private theorem stagingB_disjoint_stagingC {n k : ℕ} (hk : 2 ≤ k)
    (i j : GroupIndex k) : Disjoint (stagingB (n := n) i) (stagingC j i) := by
  apply Finset.disjoint_left.mpr
  intro c hB hC
  have hB' := (mem_stagingB i c).mp hB
  have hsmall := stagingC_col_lt_cube hk hC
  omega

private theorem stagingA_disjoint_stagingCs {n k : ℕ} (hk : 2 ≤ k) (i : GroupIndex k) :
    Disjoint (stagingA (n := n) i) (stagingCs i) := by
  apply Finset.disjoint_left.mpr
  intro c hA hCs
  obtain ⟨j, hC⟩ : ∃ j, c ∈ stagingC j i := by simpa [stagingCs] using hCs
  exact (Finset.disjoint_left.mp (stagingA_disjoint_stagingC hk i j) hA hC)

private theorem stagingB_disjoint_stagingCs {n k : ℕ} (hk : 2 ≤ k) (i : GroupIndex k) :
    Disjoint (stagingB (n := n) i) (stagingCs i) := by
  apply Finset.disjoint_left.mpr
  intro c hB hCs
  obtain ⟨j, hC⟩ : ∃ j, c ∈ stagingC j i := by simpa [stagingCs] using hCs
  exact (Finset.disjoint_left.mp (stagingB_disjoint_stagingC hk i j) hB hC)

/-- The complete initial staging quota for a destination group. -/
theorem card_stagingCells {n k : ℕ} (hk : 2 ≤ k) (hn : n = k^4) (i : GroupIndex k) :
    (stagingCells (n := n) i).card = n + k^2 * (k^3-k) := by
  change ((stagingA i ∪ stagingB i) ∪ stagingCs i).card = n + k^2 * (k^3-k)
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_union_of_disjoint (stagingA_disjoint_stagingB i)]
    rw [card_stagingA hk hn, card_stagingB hk hn, card_stagingCs hk hn]
    have hcube : k^3 ≤ n := hn ▸ cube_le_fourth k hk
    omega
  · exact Finset.disjoint_union_left.mpr
      ⟨stagingA_disjoint_stagingCs hk i, stagingB_disjoint_stagingCs hk i⟩

/-- A cell placed in two staging quotas has the same destination group. -/
theorem stagingCells_destination_unique {n k : ℕ} (hk : 2 ≤ k)
    {i i' : GroupIndex k} {c : Cell n}
    (h : c ∈ stagingCells i) (h' : c ∈ stagingCells i') : i = i' := by
  rcases (mem_stagingCells i c).mp h with hA | hB | ⟨j, hC⟩
  · rcases (mem_stagingCells i' c).mp h' with hA' | hB' | ⟨j', hC'⟩
    · exact horizontal_unique hk (mem_stagingA i c |>.mp hA).1
        (mem_stagingA i' c |>.mp hA').1
    · have hA0 := (mem_stagingA i c).mp hA
      have hB'0 := (mem_stagingB i' c).mp hB'
      omega
    · have hA0 := (mem_stagingA i c).mp hA
      have := horizontal_mod hk hA0.1
      have := stagingC_row_mod hk hC'
      omega
  · rcases (mem_stagingCells i' c).mp h' with hA' | hB' | ⟨j', hC'⟩
    · have hB0 := (mem_stagingB i c).mp hB
      have hA'0 := (mem_stagingA i' c).mp hA'
      omega
    · have hB0 := (mem_stagingB i c).mp hB
      have hB'0 := (mem_stagingB i' c).mp hB'
      exact Fin.ext (hB0.1.symm.trans hB'0.1)
    · have hB0 := (mem_stagingB i c).mp hB
      have := stagingC_col_lt_cube hk hC'
      omega
  · rcases (mem_stagingCells i' c).mp h' with hA' | hB' | ⟨j', hC'⟩
    · have := stagingC_row_mod hk hC
      have hA'0 := (mem_stagingA i' c).mp hA'
      have := horizontal_mod hk hA'0.1
      omega
    · have := stagingC_col_lt_cube hk hC
      have hB'0 := (mem_stagingB i' c).mp hB'
      omega
    · exact stagingC_destination_unique hC hC'

/-- Staging quotas for distinct destination groups are disjoint. -/
theorem stagingCells_disjoint {n k : ℕ} (hk : 2 ≤ k) {i i' : GroupIndex k}
    (hii' : i ≠ i') : Disjoint (stagingCells (n := n) i) (stagingCells i') := by
  apply Finset.disjoint_left.mpr
  intro c hi hi'
  exact hii' (stagingCells_destination_unique hk hi hi')

/-- The staging area leaves the rectangle below row `k²` and to the right of
column `k³` free for representative routing. -/
theorem stagingCells_compressed {n k : ℕ} (hk : 2 ≤ k)
    {i : GroupIndex k} {c : Cell n} (h : c ∈ stagingCells i) :
    c.1.val < k^2 ∨ c.2.val < k^3 := by
  rcases (mem_stagingCells i c).mp h with hA | hB | ⟨j,hC⟩
  · exact Or.inr (mem_stagingA i c |>.mp hA).2
  · left
    rw [(mem_stagingB i c |>.mp hB).1]
    simpa [pow_two] using i.isLt
  · exact Or.inr (stagingC_col_lt_cube hk hC)

end
end SlidingPuzzle.Partition
