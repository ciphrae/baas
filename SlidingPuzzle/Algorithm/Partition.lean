import SlidingPuzzle.Basic

/-! The partition of Section 4.1 (printed pp. 138–139).

The board of side `n = k*s` is divided into a `k × k` grid of squares of side
`s = side n k`, one per target group. The paper takes `n = k⁴` and `s = k³`;
here any `s ≥ k³` is allowed (`Dims`), which lets arbitrary board sides be
reduced to this case with fewer than `k` outer layers.

In square `i` (block row `groupRow i`, block column `groupCol i`), the first
`2k` rows are horizontal corridors, the first `k²` columns of the remaining rows
are the vertical corridors `V(i,j)`, and the rest is the reservoir. The
horizontal corridor `H_i` has two full rows: row `b` of its own band (as in the
paper) and row `k+b` of the band below, `b = groupCol i` (cyclically, so the
last band's second rows lie in the first band). The second row lets a transfer
leave its band downward without crossing it. The blank is kept separate from
target groups. -/
namespace SlidingPuzzle
namespace Partition

abbrev GroupIndex (k : ℕ) := Fin (k * k)

/-- The side of each square. -/
def side (n k : ℕ) : ℕ := n / k

/-- Admissible dimensions: a `k × k` grid of squares of side at least `k³`. -/
structure Dims (n k : ℕ) : Prop where
  two_le : 2 ≤ k
  cube_le : k^3 ≤ side n k
  mul_side : k * side n k = n

theorem side_fourth {k : ℕ} (hk : 0 < k) : side (k^4) k = k^3 := by
  unfold side
  rw [show k^4 = k^3*k by ring]
  exact Nat.mul_div_cancel _ hk

theorem Dims.fourth {k : ℕ} (hk : 2 ≤ k) : Dims (k^4) k := by
  have hs := side_fourth (show 0 < k by omega)
  exact ⟨hk, hs.ge, by rw [hs]; ring⟩

/-- Arithmetic consequences of `Dims` used throughout. -/
theorem Dims.facts {n k : ℕ} (h : Dims n k) :
    2 ≤ k ∧ 4 ≤ k^2 ∧ 2*k^2 ≤ k^3 ∧ k^3 ≤ side n k ∧ k * side n k = n := by
  have hk := h.two_le
  have h2 : 4 ≤ k^2 := by nlinarith
  have h3 : 2*k^2 ≤ k^3 := by nlinarith [Nat.mul_le_mul_right (k^2) hk]
  exact ⟨hk, h2, h3, h.cube_le, h.mul_side⟩

/-- `Dims` can be supplied wherever only `2 ≤ k` is needed. -/
instance {n k : ℕ} : CoeOut (Dims n k) (2 ≤ k) := ⟨fun h => h.two_le⟩

theorem Dims.side_pos {n k : ℕ} (h : Dims n k) : 0 < side n k :=
  lt_of_lt_of_le (pow_pos (by have := h.two_le; omega) 3) h.cube_le

theorem Dims.k_add_two_le {n k : ℕ} (h : Dims n k) : k + 2 ≤ side n k := by
  obtain ⟨hk, h2, h3, hs, -⟩ := h.facts; nlinarith

theorem Dims.sq_add_le {n k : ℕ} (h : Dims n k) : k^2 + k + 2 ≤ side n k := by
  obtain ⟨hk, h2, h3, hs, -⟩ := h.facts; nlinarith

theorem Dims.two_le_n {n k : ℕ} (h : Dims n k) : 4 ≤ n := by
  obtain ⟨hk, h2, h3, hs, hks⟩ := h.facts
  rw [← hks]; nlinarith

theorem Dims.block_le {n k : ℕ} (h : Dims n k) (a : Fin k) : (a.val+1)*side n k ≤ n := by
  calc
    (a.val+1)*side n k ≤ k*side n k := Nat.mul_le_mul_right _ a.isLt
    _ = n := h.mul_side

theorem Dims.cube_le_n {n k : ℕ} (h : Dims n k) : k^3 ≤ n := by
  have := h.cube_le; have := h.mul_side
  have : side n k ≤ k * side n k := Nat.le_mul_of_pos_left _ (by have := h.two_le; omega)
  omega

/-- Weaker dimensions, enough for Finish: squares of side at least `8`. -/
structure FDims (n k : ℕ) : Prop where
  two_le : 2 ≤ k
  eight_le : 8 ≤ side n k
  mul_side : k * side n k = n

theorem Dims.toFDims {n k : ℕ} (h : Dims n k) : FDims n k := by
  refine ⟨h.two_le, ?_, h.mul_side⟩
  have := h.cube_le; have := Nat.pow_le_pow_left h.two_le 3; omega

/-- `FDims` can be supplied wherever only `2 ≤ k` is needed. -/
instance {n k : ℕ} : CoeOut (FDims n k) (2 ≤ k) := ⟨fun h => h.two_le⟩

theorem FDims.side_pos {n k : ℕ} (h : FDims n k) : 0 < side n k := by
  have := h.eight_le; omega

theorem FDims.two_le_n {n k : ℕ} (h : FDims n k) : 4 ≤ n := by
  have := h.eight_le; have := h.two_le; rw [← h.mul_side]; nlinarith

def groupRow {k : ℕ} (i : GroupIndex k) : Fin k := (finProdFinEquiv.symm i).1
def groupCol {k : ℕ} (i : GroupIndex k) : Fin k := (finProdFinEquiv.symm i).2

/-- The band below band `a`, cyclically. -/
def nextBand (k a : ℕ) : ℕ := (a + 1) % k

/-- The upper (`low = false`) or lower (`low = true`) row of `H_i`. -/
def corridorRow {n k : ℕ} (i : GroupIndex k) (low : Bool) : ℕ :=
  if low then nextBand k (groupRow i).val * side n k + k + (groupCol i).val
  else (groupRow i).val * side n k + (groupCol i).val

/-- The horizontal corridor `H_i`: two full board rows. -/
def horizontal {n k : ℕ} (i : GroupIndex k) (c : Cell n) : Prop :=
  c.1.val = corridorRow (n := n) i false ∨ c.1.val = corridorRow (n := n) i true

/-- The vertical corridor `V(i,j)` in square `i`, reserved for group `j`. -/
def vertical {n k : ℕ} (i j : GroupIndex k) (c : Cell n) : Prop :=
  (groupRow i).val * side n k + 2 * k ≤ c.1.val ∧
  c.1.val < ((groupRow i).val + 1) * side n k ∧
  c.2.val = (groupCol i).val * side n k + j.val

/-- The reservoir of square `i`. -/
def reservoir {n k : ℕ} (i : GroupIndex k) (c : Cell n) : Prop :=
  (groupRow i).val * side n k + 2 * k ≤ c.1.val ∧
  c.1.val < ((groupRow i).val + 1) * side n k ∧
  (groupCol i).val * side n k + k^2 ≤ c.2.val ∧
  c.2.val < ((groupCol i).val + 1) * side n k

/-- Square `i`, the target region of group `i`. -/
def square {n k : ℕ} (i : GroupIndex k) (c : Cell n) : Prop :=
  (groupRow i).val * side n k ≤ c.1.val ∧
  c.1.val < ((groupRow i).val + 1) * side n k ∧
  (groupCol i).val * side n k ≤ c.2.val ∧
  c.2.val < ((groupCol i).val + 1) * side n k

noncomputable def targetGroup {n k : ℕ} (i : GroupIndex k) : Finset (Tile n) := by
  classical
  exact Finset.univ.filter fun t => t.val ≠ 0 ∧ square i (position (target n) t)

@[simp] theorem mem_targetGroup {n k : ℕ} (i : GroupIndex k) (t : Tile n) :
    t ∈ targetGroup i ↔ t.val ≠ 0 ∧ square i (position (target n) t) := by
  classical
  simp [targetGroup]

@[simp] theorem zero_not_mem_targetGroup {n k : ℕ} [NeZero n] (i : GroupIndex k) :
    (0 : Tile n) ∉ targetGroup i := by simp

/-- The H and V regions contain only the prescribed nonblank group. -/
def Clear {n k : ℕ} (B : Board n) : Prop :=
  (∀ (i : GroupIndex k) (c : Cell n), horizontal i c → B c ∈ targetGroup i) ∧
  (∀ (i j : GroupIndex k) (c : Cell n), vertical i j c → B c ∈ targetGroup j)

/-- Correct reservoir membership explicitly excludes zero. -/
def ReservoirSorted {n k : ℕ} (B : Board n) : Prop :=
  ∀ (i : GroupIndex k) (c : Cell n), reservoir i c → (B c).val ≠ 0 → B c ∈ targetGroup i

private theorem block_lt {n k : ℕ} (hd : Dims n k) (x : Fin n) :
    x.val / side n k < k := by
  have hs : 0 < side n k := lt_of_lt_of_le (by have := hd.two_le; positivity) hd.cube_le
  apply (Nat.div_lt_iff_lt_mul hs).mpr
  calc
    x.val < n := x.isLt
    _ = k * side n k := hd.mul_side.symm

private theorem side_ge {n k : ℕ} (hd : Dims n k) : k ≤ side n k ∧ k^2 < side n k := by
  obtain ⟨hk2, h2, h3, hs, -⟩ := hd.facts
  constructor <;> nlinarith

private theorem two_k_lt_side {n k : ℕ} (hd : Dims n k) : 2*k < side n k := by
  obtain ⟨hk2, h2, h3, hs, -⟩ := hd.facts
  nlinarith

theorem nextBand_lt {k : ℕ} (hk : 2 ≤ k) (a : ℕ) : nextBand k a < k :=
  Nat.mod_lt _ (by omega)

/-- The two rows of `H_i` in terms of the band and the offset within it. -/
theorem horizontal_iff {n k : ℕ} (hd : Dims n k) (i : GroupIndex k) (c : Cell n) :
    horizontal i c ↔
      (c.1.val / side n k = (groupRow i).val ∧ c.1.val % side n k = (groupCol i).val) ∨
      (c.1.val / side n k = nextBand k (groupRow i).val ∧
        c.1.val % side n k = k + (groupCol i).val) := by
  have hs := two_k_lt_side hd
  have hb := (groupCol i).isLt
  have hxd := Nat.div_add_mod' c.1.val (side n k)
  have hx := Nat.mod_lt c.1.val (show 0 < side n k by omega)
  unfold horizontal corridorRow
  simp only [Bool.false_eq_true, ↓reduceIte]
  constructor
  · rintro (h | h)
    · left
      have hd' : c.1.val / side n k = (groupRow i).val :=
        Nat.div_eq_of_lt_le (by omega) (by rw [Nat.add_mul]; omega)
      refine ⟨hd', ?_⟩
      rw [hd'] at hxd; omega
    · right
      have hd' : c.1.val / side n k = nextBand k (groupRow i).val :=
        Nat.div_eq_of_lt_le (by omega) (by rw [Nat.add_mul]; omega)
      refine ⟨hd', ?_⟩
      rw [hd'] at hxd; omega
  · rintro (⟨hd', h⟩ | ⟨hd', h⟩) <;> rw [hd'] at hxd
    · left; omega
    · right; omega

/-- Every cell belongs to one of the three region families. -/
theorem covers {n k : ℕ} (hd : Dims n k) (c : Cell n) :
    (∃ i : GroupIndex k, horizontal i c) ∨
    (∃ i j : GroupIndex k, vertical i j c) ∨
    (∃ i : GroupIndex k, reservoir i c) := by
  obtain ⟨hk2, -, -, hs3, -⟩ := hd.facts
  have hsg := two_k_lt_side hd
  let a : Fin k := ⟨c.1.val / side n k, block_lt hd c.1⟩
  let b : Fin k := ⟨c.2.val / side n k, block_lt hd c.2⟩
  have hk3 : 0 < side n k := lt_of_lt_of_le (by positivity) hs3
  have hx := Nat.mod_lt c.1.val hk3
  have hy := Nat.mod_lt c.2.val hk3
  have hxd := Nat.div_add_mod' c.1.val (side n k)
  have hyd := Nat.div_add_mod' c.2.val (side n k)
  by_cases hH : c.1.val % side n k < k
  · left
    refine ⟨finProdFinEquiv (a, ⟨c.1.val % side n k, hH⟩), (horizontal_iff hd _ c).mpr ?_⟩
    simp [groupRow, groupCol, a]
  by_cases hH' : c.1.val % side n k < 2*k
  · left
    let a' : Fin k := ⟨(a.val + (k-1)) % k, Nat.mod_lt _ (by omega)⟩
    refine ⟨finProdFinEquiv (a', ⟨c.1.val % side n k - k, by omega⟩),
      (horizontal_iff hd _ c).mpr (Or.inr ?_)⟩
    simp only [groupRow, groupCol, Equiv.symm_apply_apply, a', nextBand]
    refine ⟨?_, by omega⟩
    have ha := a.isLt
    change c.1.val / side n k = ((c.1.val / side n k + (k-1)) % k + 1) % k
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
      show c.1.val / side n k + (k-1) + 1 = c.1.val / side n k + k by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt ha]
  · by_cases hV : c.2.val % side n k < k*k
    · right; left
      refine ⟨finProdFinEquiv (a,b), ⟨c.2.val % side n k, hV⟩, ?_⟩
      simp only [vertical, groupRow, groupCol, Equiv.symm_apply_apply, a, b, Nat.add_mul, Nat.one_mul]
      refine ⟨by omega, by omega, hyd.symm⟩
    · right; right
      refine ⟨finProdFinEquiv (a,b), ?_⟩
      simp only [reservoir, groupRow, groupCol, Equiv.symm_apply_apply, a, b, Nat.add_mul, Nat.one_mul]
      have hkk : k*k = k^2 := by ring
      refine ⟨by omega, by omega, by omega, by omega⟩

/-- In a clear state the blank lies in a reservoir. -/
theorem blank_in_reservoir {n k : ℕ} [NeZero n]
    (hd : Dims n k) (B : Board n) (hclear : Clear (k := k) B) :
    ∃ i : GroupIndex k, reservoir i (blank B) := by
  rcases covers hd (blank B) with ⟨i, hi⟩ | ⟨i,j,hij⟩ | hR
  · have h := hclear.1 i (blank B) hi
    have hz : B (blank B) = 0 := by simp [blank, position]
    rw [hz] at h
    exact (zero_not_mem_targetGroup i h).elim
  · have h := hclear.2 i j (blank B) hij
    have hz : B (blank B) = 0 := by simp [blank, position]
    rw [hz] at h
    exact (zero_not_mem_targetGroup j h).elim
  · exact hR

theorem horizontal_mod {n k : ℕ} (hd : Dims n k) {i : GroupIndex k} {c : Cell n}
    (h : horizontal i c) : c.1.val % side n k < 2*k := by
  have hb := (groupCol i).isLt
  rcases (horizontal_iff hd i c).mp h with h | h <;> omega

theorem horizontal_of_corridorRow {n k : ℕ} {i : GroupIndex k} (low : Bool)
    {c : Cell n} (h : c.1.val = corridorRow (n := n) i low) : horizontal i c := by
  unfold horizontal
  cases low
  · exact Or.inl h
  · exact Or.inr h

private theorem row_div {n k : ℕ} (_hd : Dims n k) {i : GroupIndex k} {c : Cell n}
    (hl : (groupRow i).val * side n k ≤ c.1.val)
    (hu : c.1.val < ((groupRow i).val + 1) * side n k) :
    c.1.val / side n k = (groupRow i).val :=
  Nat.div_eq_of_lt_le hl hu

private theorem col_div {n k : ℕ} {i : GroupIndex k} {c : Cell n}
    (hl : (groupCol i).val * side n k ≤ c.2.val)
    (hu : c.2.val < ((groupCol i).val + 1) * side n k) :
    c.2.val / side n k = (groupCol i).val :=
  Nat.div_eq_of_lt_le hl hu

theorem vertical_row_mod {n k : ℕ} (hd : Dims n k) {i j : GroupIndex k} {c : Cell n}
    (h : vertical i j c) : 2*k ≤ c.1.val % side n k := by
  have hd := row_div (i := i) hd (by have := h.1; omega) h.2.1
  have he := Nat.div_add_mod' c.1.val (side n k)
  rw [hd] at he
  have := h.1
  omega

theorem vertical_col_mod {n k : ℕ} (hd : Dims n k) {i j : GroupIndex k} {c : Cell n}
    (h : vertical i j c) : c.2.val % side n k < k^2 := by
  have hj : j.val < k^2 := by simp [pow_two]
  have hj3 := hj.trans_le (side_ge hd).2.le
  rw [h.2.2]
  simpa [Nat.add_mod, Nat.mod_eq_of_lt hj3] using hj

theorem reservoir_row_mod {n k : ℕ} (hd : Dims n k) {i : GroupIndex k} {c : Cell n}
    (h : reservoir i c) : 2*k ≤ c.1.val % side n k := by
  have hd := row_div (i := i) hd (by have := h.1; omega) h.2.1
  have he := Nat.div_add_mod' c.1.val (side n k)
  rw [hd] at he
  have := h.1
  omega

theorem reservoir_col_mod {n k : ℕ} {i : GroupIndex k} {c : Cell n}
    (h : reservoir i c) : k^2 ≤ c.2.val % side n k := by
  have hd := col_div (by have := h.2.2.1; omega) h.2.2.2
  have he := Nat.div_add_mod' c.2.val (side n k)
  rw [hd] at he
  have := h.2.2.1
  omega

theorem horizontal_not_vertical {n k : ℕ} (hd : Dims n k)
    {i j l : GroupIndex k} {c : Cell n} (hH : horizontal i c) (hV : vertical j l c) : False := by
  have := horizontal_mod hd hH
  have := vertical_row_mod hd hV
  omega

theorem horizontal_not_reservoir {n k : ℕ} (hd : Dims n k)
    {i j : GroupIndex k} {c : Cell n} (hH : horizontal i c) (hR : reservoir j c) : False := by
  have := horizontal_mod hd hH
  have := reservoir_row_mod hd hR
  omega

theorem vertical_not_reservoir {n k : ℕ} (hd : Dims n k)
    {i j l : GroupIndex k} {c : Cell n} (hV : vertical i j c) (hR : reservoir l c) : False := by
  have := vertical_col_mod hd hV
  have := reservoir_col_mod hR
  omega

theorem square_unique {n k : ℕ} (hd : Dims n k)
    {i j : GroupIndex k} {c : Cell n} (hi : square i c) (hj : square j c) : i = j := by
  have hr : groupRow i = groupRow j := Fin.ext ((row_div hd hi.1 hi.2.1).symm.trans
    (row_div hd hj.1 hj.2.1))
  have hc : groupCol i = groupCol j := Fin.ext ((col_div hi.2.2.1 hi.2.2.2).symm.trans
    (col_div hj.2.2.1 hj.2.2.2))
  apply finProdFinEquiv.symm.injective
  exact Prod.ext hr hc

theorem targetGroups_disjoint {n k : ℕ} (hd : Dims n k)
    {i j : GroupIndex k} (hij : i ≠ j) : Disjoint (targetGroup (n := n) i) (targetGroup j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro t hi hj
  exact hij (square_unique hd (mem_targetGroup i t |>.mp hi).2 (mem_targetGroup j t |>.mp hj).2)

/-- Every target cell lies in a square. -/
theorem square_covers {n k : ℕ} (hd : Dims n k) (c : Cell n) :
    ∃ i : GroupIndex k, square i c := by
  let a : Fin k := ⟨c.1.val / side n k, block_lt hd c.1⟩
  let b : Fin k := ⟨c.2.val / side n k, block_lt hd c.2⟩
  refine ⟨finProdFinEquiv (a,b), ?_⟩
  have hp : 0 < side n k := hd.side_pos
  have hx := Nat.mod_lt c.1.val hp
  have hy := Nat.mod_lt c.2.val hp
  have hxd := Nat.div_add_mod' c.1.val (side n k)
  have hyd := Nat.div_add_mod' c.2.val (side n k)
  simp only [square, groupRow, groupCol, Equiv.symm_apply_apply, a,b, Nat.add_mul, Nat.one_mul]
  exact ⟨Nat.div_mul_le_self _ _, by nlinarith, Nat.div_mul_le_self _ _, by nlinarith⟩

theorem targetGroups_cover {n k : ℕ} (hd : Dims n k)
    (t : Tile n) (ht : t.val ≠ 0) : ∃ i : GroupIndex k, t ∈ targetGroup i := by
  obtain ⟨i, hi⟩ := square_covers hd (position (target n) t)
  exact ⟨i, (mem_targetGroup i t).mpr ⟨ht,hi⟩⟩

theorem reservoir_subset_square {n k : ℕ} {i : GroupIndex k} {c : Cell n}
    (h : reservoir i c) : square i c := by
  unfold square
  exact ⟨by have := h.1; omega, h.2.1, by have := h.2.2.1; omega, h.2.2.2⟩

theorem vertical_subset_square {n k : ℕ} (hd : Dims n k)
    {i j : GroupIndex k} {c : Cell n} (h : vertical i j c) : square i c := by
  have hj : j.val < side n k := (show j.val < k^2 by simpa only [pow_two] using j.isLt).trans_le
    (side_ge hd).2.le
  have he := h.2.2
  unfold square
  refine ⟨by have := h.1; omega, h.2.1, ?_, ?_⟩
  · omega
  · simp only [Nat.add_mul, Nat.one_mul]
    omega

theorem reservoir_unique {n k : ℕ} (hd : Dims n k) {i j : GroupIndex k} {c : Cell n}
    (hi : reservoir i c) (hj : reservoir j c) : i=j :=
  square_unique hd (reservoir_subset_square hi) (reservoir_subset_square hj)

theorem vertical_unique {n k : ℕ} (hd : Dims n k) {i j i' j' : GroupIndex k} {c : Cell n}
    (h : vertical i j c) (h' : vertical i' j' c) : i=i' ∧ j=j' := by
  have hi := square_unique hd (vertical_subset_square hd h) (vertical_subset_square hd h')
  subst i'
  refine ⟨rfl, Fin.ext ?_⟩
  have := h.2.2
  have := h'.2.2
  omega

theorem horizontal_unique {n k : ℕ} (hd : Dims n k) {i j : GroupIndex k} {c : Cell n}
    (hi : horizontal i c) (hj : horizontal j c) : i=j := by
  have hbi := (groupCol i).isLt
  have hbj := (groupCol j).isLt
  have hri := (groupRow i).isLt
  have hrj := (groupRow j).isLt
  have hk := hd.two_le
  have hnext : ∀ a b : ℕ, a < k → b < k → nextBand k a = nextBand k b → a = b := by
    intro a b ha hb h
    unfold nextBand at h
    by_cases ha' : a + 1 = k <;> by_cases hb' : b + 1 = k
    · omega
    · rw [ha', Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at h; omega
    · rw [hb', Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at h; omega
    · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h; omega
  rcases (horizontal_iff hd i c).mp hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases (horizontal_iff hd j c).mp hj with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · apply finProdFinEquiv.symm.injective
    exact Prod.ext (Fin.ext (h1.symm.trans h1'))
      (Fin.ext (show (groupCol i).val = (groupCol j).val by omega))
  · omega
  · omega
  · apply finProdFinEquiv.symm.injective
    exact Prod.ext (Fin.ext (hnext _ _ hri hrj (h1.symm.trans h1')))
      (Fin.ext (show (groupCol i).val = (groupCol j).val by omega))

theorem FDims.square_unique {n k : ℕ} (_hd : FDims n k)
    {i j : GroupIndex k} {c : Cell n} (hi : square i c) (hj : square j c) : i = j := by
  have hr : groupRow i = groupRow j := Fin.ext ((Nat.div_eq_of_lt_le hi.1 hi.2.1).symm.trans
    (Nat.div_eq_of_lt_le hj.1 hj.2.1))
  have hc : groupCol i = groupCol j := Fin.ext ((Nat.div_eq_of_lt_le hi.2.2.1 hi.2.2.2).symm.trans
    (Nat.div_eq_of_lt_le hj.2.2.1 hj.2.2.2))
  apply finProdFinEquiv.symm.injective
  exact Prod.ext hr hc

theorem FDims.square_covers {n k : ℕ} (hd : FDims n k) (c : Cell n) :
    ∃ i : GroupIndex k, square i c := by
  have hp : 0 < side n k := hd.side_pos
  have hlt : ∀ x : Fin n, x.val / side n k < k := fun x =>
    (Nat.div_lt_iff_lt_mul hp).mpr (by have := x.isLt; rw [hd.mul_side]; exact this)
  let a : Fin k := ⟨c.1.val / side n k, hlt c.1⟩
  let b : Fin k := ⟨c.2.val / side n k, hlt c.2⟩
  refine ⟨finProdFinEquiv (a,b), ?_⟩
  have hxd := Nat.div_add_mod' c.1.val (side n k)
  have hyd := Nat.div_add_mod' c.2.val (side n k)
  have hx := Nat.mod_lt c.1.val hp
  have hy := Nat.mod_lt c.2.val hp
  simp only [square, groupRow, groupCol, Equiv.symm_apply_apply, a,b, Nat.add_mul, Nat.one_mul]
  exact ⟨Nat.div_mul_le_self _ _, by nlinarith, Nat.div_mul_le_self _ _, by nlinarith⟩

end Partition
end SlidingPuzzle
