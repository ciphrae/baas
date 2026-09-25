import SlidingPuzzle.Algorithm.Cardinalities

/-! The compressed staging regions used before the corridor-clearing phase. -/
namespace SlidingPuzzle.Partition

noncomputable section
open Classical

private theorem square_le_cube (k : ℕ) (hk : 2 ≤ k) : k^2 ≤ k^3 := by
  have hk2 : k ≤ k^2 := by nlinarith
  nlinarith [Nat.mul_le_mul_left k hk2]

/-- The first horizontal part of group `i`'s staging area. -/
def stagingA {n k : ℕ} (i : GroupIndex k) : Finset (Cell n) :=
  Finset.univ.filter fun c => horizontal i c ∧ c.2.val < k^3

/-- The staged row for one of the two rows of `H_i`: the corridor row with bands
compressed to height `2k`, so that staged row `ρ` belongs in row
`horizontalDestination s (2k) ρ`. -/
def stagedRow (k : ℕ) (i : GroupIndex k) (low : Bool) : ℕ :=
  if low then nextBand k (groupRow i).val * (2*k) + k + (groupCol i).val
  else (groupRow i).val * (2*k) + (groupCol i).val

theorem stagedRow_lt {k : ℕ} (hk : 2 ≤ k) (i : GroupIndex k) (low : Bool) :
    stagedRow k i low < 2*k^2 := by
  have hb := (groupCol i).isLt
  have ha := (groupRow i).isLt
  have hn := nextBand_lt hk (groupRow i).val
  unfold stagedRow
  cases low <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · nlinarith
  · nlinarith

/-- The second horizontal part of group `i`'s staging area. -/
def stagingB {n k : ℕ} (i : GroupIndex k) : Finset (Cell n) :=
  Finset.univ.filter fun c =>
    (c.1.val = stagedRow k i false ∨ c.1.val = stagedRow k i true) ∧ k^3 ≤ c.2.val

/-- The strip in square `j` reserved for destination group `i`. -/
def stagingC {n k : ℕ} (j i : GroupIndex k) : Finset (Cell n) :=
  Finset.univ.filter fun c =>
    (groupRow j).val*side n k+2*k ≤ c.1.val ∧
    c.1.val < ((groupRow j).val+1)*side n k ∧
    c.2.val = (groupCol j).val*k^2+i.val

/-- All cells initially set aside for destination group `i`. -/
def stagingCells {n k : ℕ} (i : GroupIndex k) : Finset (Cell n) :=
  stagingA i ∪ stagingB i ∪ Finset.univ.biUnion fun j => stagingC j i

@[simp] theorem mem_stagingA {n k : ℕ} (i : GroupIndex k) (c : Cell n) :
    c ∈ stagingA i ↔ horizontal i c ∧ c.2.val < k^3 := by simp [stagingA]

@[simp] theorem mem_stagingB {n k : ℕ} (i : GroupIndex k) (c : Cell n) :
    c ∈ stagingB i ↔
      (c.1.val = stagedRow k i false ∨ c.1.val = stagedRow k i true) ∧ k^3 ≤ c.2.val := by
  simp [stagingB]

@[simp] theorem mem_stagingC {n k : ℕ} (j i : GroupIndex k) (c : Cell n) :
    c ∈ stagingC j i ↔
      (groupRow j).val*side n k+2*k ≤ c.1.val ∧
      c.1.val < ((groupRow j).val+1)*side n k ∧
      c.2.val = (groupCol j).val*k^2+i.val := by
  simp [stagingC]

@[simp] theorem mem_stagingCells {n k : ℕ} (i : GroupIndex k) (c : Cell n) :
    c ∈ stagingCells i ↔ c ∈ stagingA i ∨ c ∈ stagingB i ∨ ∃ j, c ∈ stagingC j i := by
  simp [stagingCells]

theorem card_stagingA {n k : ℕ} (hk : Dims n k) (i : GroupIndex k) :
    (stagingA (n := n) i).card = 2*k^3 := by
  obtain ⟨h1, h2, h3⟩ := horizontal_rows hk i
  have he : stagingA (n := n) i = Finset.univ.filter fun c : Cell n =>
      (c.1.val = corridorRow (n := n) i false ∨ c.1.val = corridorRow (n := n) i true) ∧
      0 ≤ c.2.val ∧ c.2.val < k^3 := by
    ext c
    simp only [mem_stagingA, horizontal, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [he, card_two_rows _ _ _ _ h1 h2 h3 hk.cube_le_n]
  simp

/-- The two staged rows of a group are distinct. -/
theorem stagedRow_ne {k : ℕ} (hk : 2 ≤ k) (i : GroupIndex k) :
    stagedRow k i false ≠ stagedRow k i true := by
  have hb := (groupCol i).isLt
  have ha := (groupRow i).isLt
  unfold stagedRow
  simp only [Bool.false_eq_true, ↓reduceIte]
  intro h
  rcases lt_trichotomy (groupRow i).val (nextBand k (groupRow i).val) with hl | hl | hl
  · have := Nat.mul_le_mul_right (2*k)
      (show (groupRow i).val+1 ≤ nextBand k (groupRow i).val by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  · exfalso; unfold nextBand at hl
    rcases Nat.lt_or_ge ((groupRow i).val+1) k with h' | h'
    · rw [Nat.mod_eq_of_lt h'] at hl; omega
    · rw [show (groupRow i).val+1 = k by omega, Nat.mod_self] at hl; omega
  · have := Nat.mul_le_mul_right (2*k)
      (show nextBand k (groupRow i).val+1 ≤ (groupRow i).val by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; omega

/-- A staged row determines its group. -/
theorem stagedRow_inj {k : ℕ} (hk : 2 ≤ k) {i i' : GroupIndex k} {l l' : Bool}
    (h : stagedRow k i l = stagedRow k i' l') : i = i' := by
  have hbi := (groupCol i).isLt
  have hbj := (groupCol i').isLt
  have hri := (groupRow i).isLt
  have hrj := (groupRow i').isLt
  have hnext : ∀ a b : ℕ, a < k → b < k → nextBand k a = nextBand k b → a = b := by
    intro a b ha hb h
    unfold nextBand at h
    by_cases ha' : a + 1 = k <;> by_cases hb' : b + 1 = k
    · omega
    · rw [ha', Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at h; omega
    · rw [hb', Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at h; omega
    · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h; omega
  have hdm : ∀ a o : ℕ, o < 2*k → (a*(2*k)+o)/(2*k) = a ∧ (a*(2*k)+o)%(2*k) = o := by
    intro a o ho
    refine ⟨?_, ?_⟩
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt ho]; simp
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ho]
  have key : ∀ (j : GroupIndex k) (l : Bool), (groupCol j).val < k →
      (stagedRow k j l)/(2*k) = (if l then nextBand k (groupRow j).val else (groupRow j).val) ∧
      (stagedRow k j l)%(2*k) = (if l then k else 0) + (groupCol j).val := by
    intro j l hj
    unfold stagedRow
    cases l <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    · exact hdm _ _ (by omega)
    · rw [Nat.add_assoc]; exact hdm _ _ (by omega)
  obtain ⟨h1, h2⟩ := key i l hbi
  obtain ⟨h1', h2'⟩ := key i' l' hbj
  rw [h] at h1 h2
  apply finProdFinEquiv.symm.injective
  cases l <;> cases l' <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at h1 h2 h1' h2'
  · exact Prod.ext (Fin.ext (h1.symm.trans h1'))
      (Fin.ext (show (groupCol i).val = (groupCol i').val by omega))
  · omega
  · omega
  · exact Prod.ext (Fin.ext (hnext _ _ hri hrj (h1.symm.trans h1')))
      (Fin.ext (show (groupCol i).val = (groupCol i').val by omega))

theorem card_stagingB {n k : ℕ} (hk : Dims n k) (i : GroupIndex k) :
    (stagingB (n := n) i).card = 2*(n-k^3) := by
  have hcube : k^3 ≤ n := hk.cube_le_n
  have hr1 := stagedRow_lt hk.two_le i false
  have hr2 := stagedRow_lt hk.two_le i true
  have h2 : 2*k^2 ≤ k^3 := hk.facts.2.2.1
  have he : stagingB (n := n) i = Finset.univ.filter fun c : Cell n =>
      (c.1.val = stagedRow k i false ∨ c.1.val = stagedRow k i true) ∧
      k^3 ≤ c.2.val ∧ c.2.val < n := by
    ext c
    simp only [mem_stagingB, Finset.mem_filter, Finset.mem_univ, true_and]
    have := c.2.isLt
    omega
  rw [he, card_two_rows _ _ _ _ (stagedRow_ne hk.two_le i) (by omega) (by omega) le_rfl]

theorem card_stagingC {n k : ℕ} (hk : Dims n k)
    (j i : GroupIndex k) :
    (stagingC (n := n) j i).card = side n k-2*k := by
  have hrow := hk.block_le (groupRow j)
  have hcube : k^3 ≤ n := hk.cube_le_n
  have hcol : (groupCol j).val*k^2+i.val+1 ≤ n := by
    have hbound : (groupCol j).val*k^2+i.val+1 ≤ k^3 := by
      have hb : (groupCol j).val+1 ≤ k := by omega
      have hi : i.val+1 ≤ k^2 := by
        have : i.val+1 ≤ k*k := by omega
        simp [pow_two]
      nlinarith [Nat.mul_le_mul_right (k^2) hb]
    exact hbound.trans hcube
  have he : stagingC (n := n) j i = Finset.univ.filter fun c : Cell n =>
      (groupRow j).val*side n k+2*k ≤ c.1.val ∧
      c.1.val < ((groupRow j).val+1)*side n k ∧
      (groupCol j).val*k^2+i.val ≤ c.2.val ∧
      c.2.val < (groupCol j).val*k^2+i.val+1 := by
    ext c
    simp only [mem_stagingC, Finset.mem_filter, Finset.mem_univ, true_and]
    have := c.2.isLt
    omega
  rw [he, card_rectangle _ _ _ _ hrow hcol]
  rw [Nat.add_mul]
  have hr : (groupRow j).val*side n k + 1*side n k - ((groupRow j).val*side n k+2*k) =
      side n k-2*k := by
    omega
  have hc : (groupCol j).val*k^2+i.val+1 - ((groupCol j).val*k^2+i.val) = 1 := by
    omega
  rw [hr, hc]
  simp

private theorem stagingC_row_mod {n k : ℕ} (hk : Dims n k)
    {j i : GroupIndex k} {c : Cell n} (h : c ∈ stagingC j i) :
    2*k ≤ c.1.val % side n k := by
  have h' := (mem_stagingC j i c).mp h
  have hd : c.1.val / side n k = (groupRow j).val := by
    apply Nat.div_eq_of_lt_le
    · have := h'.1
      omega
    · exact h'.2.1
  have he := Nat.div_add_mod' c.1.val (side n k)
  rw [hd] at he
  have := h'.1
  omega

private theorem stagingC_col_lt_cube {n k : ℕ} (_hk : Dims n k)
    {j i : GroupIndex k} {c : Cell n} (h : c ∈ stagingC j i) : c.2.val < k^3 := by
  have h' := (mem_stagingC j i c).mp h
  rw [h'.2.2]
  have hb : (groupCol j).val+1 ≤ k := by omega
  have hi : i.val+1 ≤ k^2 := by
    have : i.val+1 ≤ k*k := by omega
    simp [pow_two]
  nlinarith [Nat.mul_le_mul_right (k^2) hb]

private theorem stagingC_col_div {n k : ℕ} {j i : GroupIndex k} {c : Cell n}
    (h : c ∈ stagingC j i) : c.2.val / k^2 = (groupCol j).val := by
  have h' := (mem_stagingC j i c).mp h
  rw [h'.2.2]
  apply Nat.div_eq_of_lt_le
  · omega
  · have hi : i.val < k^2 := by simp [pow_two]
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

private theorem stagingC_pairwise_disjoint {n k : ℕ} (hk : Dims n k) (i : GroupIndex k) :
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
    · have hrow : c.1.val / side n k = (groupRow j).val := by
        apply Nat.div_eq_of_lt_le
        · have := hc0.1; omega
        · exact hc0.2.1
      have hrow' : c.1.val / side n k = (groupRow j').val := by
        apply Nat.div_eq_of_lt_le
        · have := hc0'.1; omega
        · exact hc0'.2.1
      exact Fin.ext (hrow.symm.trans hrow')
    · apply Fin.ext
      have he : (groupCol j).val*k^2+i.val = (groupCol j').val*k^2+i.val :=
        hc0.2.2.symm.trans hc0'.2.2
      exact Nat.eq_of_mul_eq_mul_right (by have := hk.two_le; positivity) (Nat.add_right_cancel he))

/-- The combined compressed strips for destination group `i`. -/
def stagingCs {n k : ℕ} (i : GroupIndex k) : Finset (Cell n) :=
  Finset.univ.biUnion fun j => stagingC j i

theorem card_stagingCs {n k : ℕ} (hk : Dims n k) (i : GroupIndex k) :
    (stagingCs (n := n) i).card = k^2*(side n k-2*k) := by
  unfold stagingCs
  rw [Finset.card_biUnion (by simpa using stagingC_pairwise_disjoint hk i)]
  simp_rw [card_stagingC hk]
  simp [GroupIndex, pow_two]

private theorem stagingA_disjoint_stagingB {n k : ℕ} (i : GroupIndex k) :
    Disjoint (stagingA (n := n) i) (stagingB i) := by
  apply Finset.disjoint_left.mpr
  intro c hA hB
  have hA' := (mem_stagingA i c).mp hA
  have hB' := (mem_stagingB i c).mp hB
  omega

private theorem stagingA_disjoint_stagingC {n k : ℕ} (hk : Dims n k)
    (i j : GroupIndex k) : Disjoint (stagingA (n := n) i) (stagingC j i) := by
  apply Finset.disjoint_left.mpr
  intro c hA hC
  have hA' := (mem_stagingA i c).mp hA
  have hC' := (mem_stagingC j i c).mp hC
  have hsmall := horizontal_mod hk hA'.1
  have hlarge := stagingC_row_mod hk hC
  omega

private theorem stagingB_disjoint_stagingC {n k : ℕ} (hk : Dims n k)
    (i j : GroupIndex k) : Disjoint (stagingB (n := n) i) (stagingC j i) := by
  apply Finset.disjoint_left.mpr
  intro c hB hC
  have hB' := (mem_stagingB i c).mp hB
  have hsmall := stagingC_col_lt_cube hk hC
  omega

private theorem stagingA_disjoint_stagingCs {n k : ℕ} (hk : Dims n k) (i : GroupIndex k) :
    Disjoint (stagingA (n := n) i) (stagingCs i) := by
  apply Finset.disjoint_left.mpr
  intro c hA hCs
  obtain ⟨j, hC⟩ : ∃ j, c ∈ stagingC j i := by simpa [stagingCs] using hCs
  exact (Finset.disjoint_left.mp (stagingA_disjoint_stagingC hk i j) hA hC)

private theorem stagingB_disjoint_stagingCs {n k : ℕ} (hk : Dims n k) (i : GroupIndex k) :
    Disjoint (stagingB (n := n) i) (stagingCs i) := by
  apply Finset.disjoint_left.mpr
  intro c hB hCs
  obtain ⟨j, hC⟩ : ∃ j, c ∈ stagingC j i := by simpa [stagingCs] using hCs
  exact (Finset.disjoint_left.mp (stagingB_disjoint_stagingC hk i j) hB hC)

/-- The complete initial staging quota for a destination group. -/
theorem card_stagingCells {n k : ℕ} (hk : Dims n k) (i : GroupIndex k) :
    (stagingCells (n := n) i).card = 2*n + k^2 * (side n k-2*k) := by
  change ((stagingA i ∪ stagingB i) ∪ stagingCs i).card = 2*n + k^2 * (side n k-2*k)
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_union_of_disjoint (stagingA_disjoint_stagingB i)]
    rw [card_stagingA hk, card_stagingB hk, card_stagingCs hk]
    have hcube : k^3 ≤ n := hk.cube_le_n
    omega
  · exact Finset.disjoint_union_left.mpr
      ⟨stagingA_disjoint_stagingCs hk i, stagingB_disjoint_stagingCs hk i⟩

/-- A cell placed in two staging quotas has the same destination group. -/
theorem stagingCells_destination_unique {n k : ℕ} (hk : Dims n k)
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
      rcases hB0.1 with h1 | h1 <;> rcases hB'0.1 with h2 | h2 <;>
        exact stagedRow_inj hk.two_le (h1.symm.trans h2)
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
theorem stagingCells_disjoint {n k : ℕ} (hk : Dims n k) {i i' : GroupIndex k}
    (hii' : i ≠ i') : Disjoint (stagingCells (n := n) i) (stagingCells i') := by
  apply Finset.disjoint_left.mpr
  intro c hi hi'
  exact hii' (stagingCells_destination_unique hk hi hi')

/-- The staging area leaves the rectangle below row `2k²` and to the right of
column `k³` free for representative routing. -/
theorem stagingCells_compressed {n k : ℕ} (hk : Dims n k)
    {i : GroupIndex k} {c : Cell n} (h : c ∈ stagingCells i) :
    c.1.val < 2*k^2 ∨ c.2.val < k^3 := by
  rcases (mem_stagingCells i c).mp h with hA | hB | ⟨j,hC⟩
  · exact Or.inr (mem_stagingA i c |>.mp hA).2
  · left
    have := stagedRow_lt hk.two_le i false
    have := stagedRow_lt hk.two_le i true
    rcases (mem_stagingB i c |>.mp hB).1 with h | h <;> omega
  · exact Or.inr (stagingC_col_lt_cube hk hC)

end
end SlidingPuzzle.Partition
