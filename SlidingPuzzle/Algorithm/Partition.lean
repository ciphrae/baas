import SlidingPuzzle.Basic

/-! Direct definitions of the partition in Section 4.1, printed pp. 138–139.
Coordinates and groups follow the paper. The blank is kept separate from target
label groups; no containment condition silently classifies the blank as a tile. -/
namespace SlidingPuzzle
namespace Partition

abbrev GroupIndex (k : ℕ) := Fin (k * k)

def groupRow {k : ℕ} (i : GroupIndex k) : Fin k := (finProdFinEquiv.symm i).1
def groupCol {k : ℕ} (i : GroupIndex k) : Fin k := (finProdFinEquiv.symm i).2

def horizontal {n k : ℕ} (i : GroupIndex k) (c : Cell n) : Prop :=
  c.1.val = (groupRow i).val * k^3 + (groupCol i).val

def vertical {n k : ℕ} (i j : GroupIndex k) (c : Cell n) : Prop :=
  (groupRow i).val * k^3 + k ≤ c.1.val ∧
  c.1.val < ((groupRow i).val + 1) * k^3 ∧
  c.2.val = (groupCol i).val * k^3 + j.val

def reservoir {n k : ℕ} (i : GroupIndex k) (c : Cell n) : Prop :=
  (groupRow i).val * k^3 + k ≤ c.1.val ∧
  c.1.val < ((groupRow i).val + 1) * k^3 ∧
  (groupCol i).val * k^3 + k^2 ≤ c.2.val ∧
  c.2.val < ((groupCol i).val + 1) * k^3

def square {n k : ℕ} (i : GroupIndex k) (c : Cell n) : Prop :=
  (groupRow i).val * k^3 ≤ c.1.val ∧
  c.1.val < ((groupRow i).val + 1) * k^3 ∧
  (groupCol i).val * k^3 ≤ c.2.val ∧
  c.2.val < ((groupCol i).val + 1) * k^3

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

private theorem block_lt {n k : ℕ} (hk : 2 ≤ k) (hn : n = k^4) (x : Fin n) :
    x.val / k^3 < k := by
  have hk3 : 0 < k^3 := by positivity
  apply (Nat.div_lt_iff_lt_mul hk3).mpr
  calc
    x.val < n := x.isLt
    _ = k * k^3 := by rw [hn]; ring

/-- Every cell belongs to one of the three region families. -/
theorem covers {n k : ℕ} (hk : 2 ≤ k) (hn : n = k^4) (c : Cell n) :
    (∃ i : GroupIndex k, horizontal i c) ∨
    (∃ i j : GroupIndex k, vertical i j c) ∨
    (∃ i : GroupIndex k, reservoir i c) := by
  let a : Fin k := ⟨c.1.val / k^3, block_lt hk hn c.1⟩
  let b : Fin k := ⟨c.2.val / k^3, block_lt hk hn c.2⟩
  have hk3 : 0 < k^3 := by positivity
  have hx := Nat.mod_lt c.1.val hk3
  have hy := Nat.mod_lt c.2.val hk3
  have hxd := Nat.div_add_mod' c.1.val (k^3)
  have hyd := Nat.div_add_mod' c.2.val (k^3)
  by_cases hH : c.1.val % k^3 < k
  · left
    refine ⟨finProdFinEquiv (a, ⟨c.1.val % k^3, hH⟩), ?_⟩
    simpa [horizontal, groupRow, groupCol, a] using hxd.symm
  · by_cases hV : c.2.val % k^3 < k*k
    · right; left
      refine ⟨finProdFinEquiv (a,b), ⟨c.2.val % k^3, hV⟩, ?_⟩
      simp only [vertical, groupRow, groupCol, Equiv.symm_apply_apply, a, b, Nat.add_mul, Nat.one_mul]
      constructor
      · omega
      constructor
      · omega
      · exact hyd.symm
    · right; right
      refine ⟨finProdFinEquiv (a,b), ?_⟩
      simp only [reservoir, groupRow, groupCol, Equiv.symm_apply_apply, a, b, Nat.add_mul, Nat.one_mul]
      have hkk : k*k = k^2 := by ring
      constructor
      · omega
      constructor
      · omega
      constructor <;> omega

/-- In a clear state the blank lies in a reservoir. -/
theorem blank_in_reservoir {n k : ℕ} [NeZero n]
    (hk : 2 ≤ k) (hn : n = k^4) (B : Board n) (hclear : Clear (k := k) B) :
    ∃ i : GroupIndex k, reservoir i (blank B) := by
  rcases covers hk hn (blank B) with ⟨i, hi⟩ | ⟨i,j,hij⟩ | hR
  · have h := hclear.1 i (blank B) hi
    have hz : B (blank B) = 0 := by simp [blank, position]
    rw [hz] at h
    exact (zero_not_mem_targetGroup i h).elim
  · have h := hclear.2 i j (blank B) hij
    have hz : B (blank B) = 0 := by simp [blank, position]
    rw [hz] at h
    exact (zero_not_mem_targetGroup j h).elim
  · exact hR

private theorem cube_ge (k : ℕ) (hk : 2 ≤ k) : k ≤ k^3 ∧ k^2 ≤ k^3 := by
  have h1 : 1 ≤ k := by omega
  have h2 : k ≤ k^2 := by nlinarith
  constructor <;> nlinarith [Nat.mul_le_mul_left k h2]

theorem horizontal_mod {n k : ℕ} (hk : 2 ≤ k) {i : GroupIndex k} {c : Cell n}
    (h : horizontal i c) : c.1.val % k^3 < k := by
  have hb : (groupCol i).val < k^3 := (groupCol i).isLt.trans_le (cube_ge k hk).1
  rw [horizontal] at h
  rw [h]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hb]

private theorem row_div {n k : ℕ} (_hk : 2 ≤ k) {i : GroupIndex k} {c : Cell n}
    (hl : (groupRow i).val * k^3 ≤ c.1.val)
    (hu : c.1.val < ((groupRow i).val + 1) * k^3) :
    c.1.val / k^3 = (groupRow i).val :=
  Nat.div_eq_of_lt_le hl hu

private theorem col_div {n k : ℕ} {i : GroupIndex k} {c : Cell n}
    (hl : (groupCol i).val * k^3 ≤ c.2.val)
    (hu : c.2.val < ((groupCol i).val + 1) * k^3) :
    c.2.val / k^3 = (groupCol i).val :=
  Nat.div_eq_of_lt_le hl hu

theorem vertical_row_mod {n k : ℕ} (hk : 2 ≤ k) {i j : GroupIndex k} {c : Cell n}
    (h : vertical i j c) : k ≤ c.1.val % k^3 := by
  have hd := row_div hk (by have := h.1; omega) h.2.1
  have he := Nat.div_add_mod' c.1.val (k^3)
  rw [hd] at he
  have := h.1
  omega

theorem vertical_col_mod {n k : ℕ} (hk : 2 ≤ k) {i j : GroupIndex k} {c : Cell n}
    (h : vertical i j c) : c.2.val % k^3 < k^2 := by
  have hj : j.val < k^2 := by simp [pow_two]
  have hj3 := hj.trans_le (cube_ge k hk).2
  rw [h.2.2]
  simpa [Nat.add_mod, Nat.mod_eq_of_lt hj3] using hj

theorem reservoir_row_mod {n k : ℕ} (hk : 2 ≤ k) {i : GroupIndex k} {c : Cell n}
    (h : reservoir i c) : k ≤ c.1.val % k^3 := by
  have hd := row_div hk (by have := h.1; omega) h.2.1
  have he := Nat.div_add_mod' c.1.val (k^3)
  rw [hd] at he
  have := h.1
  omega

theorem reservoir_col_mod {n k : ℕ} {i : GroupIndex k} {c : Cell n}
    (h : reservoir i c) : k^2 ≤ c.2.val % k^3 := by
  have hd := col_div (by have := h.2.2.1; omega) h.2.2.2
  have he := Nat.div_add_mod' c.2.val (k^3)
  rw [hd] at he
  have := h.2.2.1
  omega

theorem horizontal_not_vertical {n k : ℕ} (hk : 2 ≤ k)
    {i j l : GroupIndex k} {c : Cell n} (hH : horizontal i c) (hV : vertical j l c) : False := by
  have := horizontal_mod hk hH
  have := vertical_row_mod hk hV
  omega

theorem horizontal_not_reservoir {n k : ℕ} (hk : 2 ≤ k)
    {i j : GroupIndex k} {c : Cell n} (hH : horizontal i c) (hR : reservoir j c) : False := by
  have := horizontal_mod hk hH
  have := reservoir_row_mod hk hR
  omega

theorem vertical_not_reservoir {n k : ℕ} (hk : 2 ≤ k)
    {i j l : GroupIndex k} {c : Cell n} (hV : vertical i j c) (hR : reservoir l c) : False := by
  have := vertical_col_mod hk hV
  have := reservoir_col_mod hR
  omega

theorem square_unique {n k : ℕ} (hk : 2 ≤ k)
    {i j : GroupIndex k} {c : Cell n} (hi : square i c) (hj : square j c) : i = j := by
  have hr : groupRow i = groupRow j := Fin.ext ((row_div hk hi.1 hi.2.1).symm.trans
    (row_div hk hj.1 hj.2.1))
  have hc : groupCol i = groupCol j := Fin.ext ((col_div hi.2.2.1 hi.2.2.2).symm.trans
    (col_div hj.2.2.1 hj.2.2.2))
  apply finProdFinEquiv.symm.injective
  exact Prod.ext hr hc

theorem targetGroups_disjoint {n k : ℕ} (hk : 2 ≤ k)
    {i j : GroupIndex k} (hij : i ≠ j) : Disjoint (targetGroup (n := n) i) (targetGroup j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro t hi hj
  exact hij (square_unique hk (mem_targetGroup i t |>.mp hi).2 (mem_targetGroup j t |>.mp hj).2)

/-- Every target cell lies in a square. -/
theorem square_covers {n k : ℕ} (hk : 2 ≤ k) (hn : n=k^4) (c : Cell n) :
    ∃ i : GroupIndex k, square i c := by
  let a : Fin k := ⟨c.1.val / k^3, block_lt hk hn c.1⟩
  let b : Fin k := ⟨c.2.val / k^3, block_lt hk hn c.2⟩
  refine ⟨finProdFinEquiv (a,b), ?_⟩
  have hp : 0 < k^3 := by positivity
  have hx := Nat.mod_lt c.1.val hp
  have hy := Nat.mod_lt c.2.val hp
  have hxd := Nat.div_add_mod' c.1.val (k^3)
  have hyd := Nat.div_add_mod' c.2.val (k^3)
  simp only [square, groupRow, groupCol, Equiv.symm_apply_apply, a,b, Nat.add_mul, Nat.one_mul]
  exact ⟨Nat.div_mul_le_self _ _, by nlinarith, Nat.div_mul_le_self _ _, by nlinarith⟩

theorem targetGroups_cover {n k : ℕ} (hk : 2 ≤ k) (hn : n=k^4)
    (t : Tile n) (ht : t.val ≠ 0) : ∃ i : GroupIndex k, t ∈ targetGroup i := by
  obtain ⟨i, hi⟩ := square_covers hk hn (position (target n) t)
  exact ⟨i, (mem_targetGroup i t).mpr ⟨ht,hi⟩⟩

theorem reservoir_subset_square {n k : ℕ} {i : GroupIndex k} {c : Cell n}
    (h : reservoir i c) : square i c := by
  unfold square
  exact ⟨by have := h.1; omega, h.2.1, by have := h.2.2.1; omega, h.2.2.2⟩

theorem vertical_subset_square {n k : ℕ} (hk : 2 ≤ k)
    {i j : GroupIndex k} {c : Cell n} (h : vertical i j c) : square i c := by
  have hj : j.val < k^3 := (show j.val < k^2 by simpa only [pow_two] using j.isLt).trans_le
    (cube_ge k hk).2
  have he := h.2.2
  unfold square
  refine ⟨by have := h.1; omega, h.2.1, ?_, ?_⟩
  · omega
  · simp only [Nat.add_mul, Nat.one_mul]
    omega

theorem reservoir_unique {n k : ℕ} (hk : 2 ≤ k) {i j : GroupIndex k} {c : Cell n}
    (hi : reservoir i c) (hj : reservoir j c) : i=j :=
  square_unique hk (reservoir_subset_square hi) (reservoir_subset_square hj)

theorem vertical_unique {n k : ℕ} (hk : 2 ≤ k) {i j i' j' : GroupIndex k} {c : Cell n}
    (h : vertical i j c) (h' : vertical i' j' c) : i=i' ∧ j=j' := by
  have hi := square_unique hk (vertical_subset_square hk h) (vertical_subset_square hk h')
  subst i'
  refine ⟨rfl, Fin.ext ?_⟩
  have := h.2.2
  have := h'.2.2
  omega

theorem horizontal_unique {n k : ℕ} (hk : 2 ≤ k) {i j : GroupIndex k} {c : Cell n}
    (hi : horizontal i c) (hj : horizontal j c) : i=j := by
  have hi' : c.1.val / k^3 = (groupRow i).val := by
    apply row_div hk
    · have := hi; unfold horizontal at this; omega
    · have hb := (groupCol i).isLt.trans_le (cube_ge k hk).1
      unfold horizontal at hi
      simp only [Nat.add_mul, Nat.one_mul]
      omega
  have hj' : c.1.val / k^3 = (groupRow j).val := by
    apply row_div hk
    · have := hj; unfold horizontal at this; omega
    · have hb := (groupCol j).isLt.trans_le (cube_ge k hk).1
      unfold horizontal at hj
      simp only [Nat.add_mul, Nat.one_mul]
      omega
  have hr : groupRow i = groupRow j := Fin.ext (hi'.symm.trans hj')
  have hc : groupCol i = groupCol j := by
    apply Fin.ext
    unfold horizontal at hi hj
    rw [hr] at hi
    omega
  apply finProdFinEquiv.symm.injective
  exact Prod.ext hr hc

end Partition
end SlidingPuzzle
