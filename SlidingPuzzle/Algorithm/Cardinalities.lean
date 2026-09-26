import SlidingPuzzle.Algorithm.Partition
import SlidingPuzzle.Target

/-! Finite cardinalities of the paper's partition, proved directly from intervals. -/
namespace SlidingPuzzle.Partition

noncomputable section
open Classical

def axis (n lo hi : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun x => lo ≤ x.val ∧ x.val < hi

theorem card_axis (n lo hi : ℕ) (hhi : hi ≤ n) :
    (axis n lo hi).card = hi - lo := by
  classical
  unfold axis
  rw [← Fintype.card_subtype]
  let e : {x : Fin n // lo ≤ x.val ∧ x.val < hi} ≃ Fin (hi-lo) :=
    { toFun := fun x => ⟨x.val.val-lo, by have := x.property; omega⟩
      invFun := fun x => ⟨⟨x.val+lo, by have := x.isLt; omega⟩, by change lo ≤ x.val+lo ∧ x.val+lo < hi; have := x.isLt; omega⟩
      left_inv := by intro x; apply Subtype.ext; apply Fin.ext; have := x.property; simp; omega
      right_inv := by intro x; apply Fin.ext; simp }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

theorem card_rectangle {n : ℕ} (xl xh yl yh : ℕ) (hx : xh ≤ n) (hy : yh ≤ n) :
    (Finset.univ.filter (fun c : Cell n =>
      xl ≤ c.1.val ∧ c.1.val < xh ∧ yl ≤ c.2.val ∧ c.2.val < yh)).card =
      (xh-xl)*(yh-yl) := by
  classical
  have he : (Finset.univ.filter (fun c : Cell n =>
      xl ≤ c.1.val ∧ c.1.val < xh ∧ yl ≤ c.2.val ∧ c.2.val < yh)) =
      (axis n xl xh).product (axis n yl yh) := by
    ext c
    simp [axis, and_assoc]
  rw [he]
  calc
    _ = (axis n xl xh).card * (axis n yl yh).card := Finset.card_product _ _
    _ = _ := by rw [card_axis n xl xh hx, card_axis n yl yh hy]

private theorem side_ge' {n k : ℕ} (hd : Dims n k) : k ≤ side n k ∧ k^2 ≤ side n k := by
  obtain ⟨hk2, h2, h3, hs, -⟩ := hd.facts
  constructor <;> nlinarith

theorem block_end_le {n k : ℕ} (hd : Dims n k) (a : Fin k) :
    (a.val+1)*side n k ≤ n := by
  calc
    (a.val+1)*side n k ≤ k*side n k := Nat.mul_le_mul_right _ a.isLt
    _ = n := hd.mul_side

def horizontalCells {n k : ℕ} (i : GroupIndex k) : Finset (Cell n) := by
  classical
  exact Finset.univ.filter (horizontal i)

def verticalCells {n k : ℕ} (i j : GroupIndex k) : Finset (Cell n) := by
  classical
  exact Finset.univ.filter (vertical i j)

def reservoirCells {n k : ℕ} (i : GroupIndex k) : Finset (Cell n) := by
  classical
  exact Finset.univ.filter (reservoir i)

def squareCells {n k : ℕ} (i : GroupIndex k) : Finset (Cell n) := by
  classical
  exact Finset.univ.filter (square i)

/-- Two distinct rows over a column interval. -/
theorem card_two_rows {n : ℕ} (r₁ r₂ yl yh : ℕ) (hr : r₁ ≠ r₂) (hr₁ : r₁ < n)
    (hr₂ : r₂ < n) (hy : yh ≤ n) :
    (Finset.univ.filter (fun c : Cell n =>
      (c.1.val = r₁ ∨ c.1.val = r₂) ∧ yl ≤ c.2.val ∧ c.2.val < yh)).card = 2*(yh-yl) := by
  classical
  have he : (Finset.univ.filter (fun c : Cell n =>
      (c.1.val = r₁ ∨ c.1.val = r₂) ∧ yl ≤ c.2.val ∧ c.2.val < yh)) =
      Finset.univ.filter (fun c : Cell n =>
        r₁ ≤ c.1.val ∧ c.1.val < r₁+1 ∧ yl ≤ c.2.val ∧ c.2.val < yh) ∪
      Finset.univ.filter (fun c : Cell n =>
        r₂ ≤ c.1.val ∧ c.1.val < r₂+1 ∧ yl ≤ c.2.val ∧ c.2.val < yh) := by
    ext c; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]; omega
  rw [he, Finset.card_union_of_disjoint, card_rectangle _ _ _ _ (by omega) hy,
    card_rectangle _ _ _ _ (by omega) hy]
  · simp only [Nat.add_sub_cancel_left, one_mul]; ring
  · apply Finset.disjoint_left.mpr
    intro c h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    omega

/-- The two rows of `H_i` are distinct rows of the board. -/
theorem horizontal_rows {n k : ℕ} (hd : Dims n k) (i : GroupIndex k) :
    corridorRow (n := n) i false ≠ corridorRow (n := n) i true ∧
    corridorRow (n := n) i false < n ∧ corridorRow (n := n) i true < n := by
  have hb := (groupCol i).isLt
  obtain ⟨hk2, h2, h3, hs, -⟩ := hd.facts
  have h2k : 2*k < side n k := by nlinarith
  have hn1 := nextBand_lt hk2 (groupRow i).val
  have he := block_end_le hd (groupRow i)
  have he' : (nextBand k (groupRow i).val+1)*side n k ≤ n := block_end_le hd ⟨_, hn1⟩
  simp only [Nat.add_mul, Nat.one_mul] at he he'
  unfold corridorRow
  simp only [Bool.false_eq_true, ↓reduceIte, ]
  refine ⟨fun h => ?_, by omega, by omega⟩
  rcases lt_trichotomy (groupRow i).val (nextBand k (groupRow i).val) with hl | hl | hl
  · have := Nat.mul_le_mul_right (side n k) (show (groupRow i).val+1 ≤ nextBand k (groupRow i).val by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  · exfalso; unfold nextBand at hl
    have hk := (groupRow i).isLt
    rcases Nat.lt_or_ge ((groupRow i).val+1) k with h' | h'
    · rw [Nat.mod_eq_of_lt h'] at hl; omega
    · rw [show (groupRow i).val+1 = k by omega, Nat.mod_self] at hl; omega
  · have := Nat.mul_le_mul_right (side n k) (show nextBand k (groupRow i).val+1 ≤ (groupRow i).val by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; omega

@[simp] theorem mem_horizontalCells {n k : ℕ} (i : GroupIndex k) (c : Cell n) :
    c ∈ horizontalCells i ↔ horizontal i c := by classical simp [horizontalCells]
@[simp] theorem mem_verticalCells {n k : ℕ} (i j : GroupIndex k) (c : Cell n) :
    c ∈ verticalCells i j ↔ vertical i j c := by classical simp [verticalCells]
@[simp] theorem mem_reservoirCells {n k : ℕ} (i : GroupIndex k) (c : Cell n) :
    c ∈ reservoirCells i ↔ reservoir i c := by classical simp [reservoirCells]
@[simp] theorem mem_squareCells {n k : ℕ} (i : GroupIndex k) (c : Cell n) :
    c ∈ squareCells i ↔ square i c := by classical simp [squareCells]

theorem card_horizontal {n k : ℕ} (hd : Dims n k) (i : GroupIndex k) :
    (horizontalCells (n := n) i).card = 2*n := by
  classical
  obtain ⟨h1, h2, h3⟩ := horizontal_rows hd i
  have he : horizontalCells (n := n) i = Finset.univ.filter (fun c : Cell n =>
      (c.1.val = corridorRow (n := n) i false ∨ c.1.val = corridorRow (n := n) i true) ∧
      0 ≤ c.2.val ∧ c.2.val < n) := by
    ext c
    simp only [mem_horizontalCells, Finset.mem_filter, Finset.mem_univ, true_and, horizontal]
    have := c.2.isLt
    omega
  rw [he, card_two_rows _ _ _ _ h1 h2 h3 le_rfl]
  simp

theorem card_vertical {n k : ℕ} (hd : Dims n k) (i j : GroupIndex k) :
    (verticalCells (n := n) i j).card = side n k-2*k := by
  classical
  let x := (groupRow i).val*side n k
  let y := (groupCol i).val*side n k+j.val
  have hx := block_end_le hd (groupRow i)
  have hy : y+1 ≤ n := by
    have he := block_end_le hd (groupCol i)
    have hj : j.val < k^2 := by simpa only [pow_two] using j.isLt
    have hg := (side_ge' hd).2
    dsimp [y]
    nlinarith
  have he : verticalCells (n := n) i j =
      Finset.univ.filter (fun c : Cell n => x+2*k ≤ c.1.val ∧
        c.1.val < ((groupRow i).val+1)*side n k ∧ y ≤ c.2.val ∧ c.2.val < y+1) := by
    ext c
    simp only [mem_verticalCells, vertical, Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp [x,y]
    omega
  rw [he, card_rectangle (x+2*k) _ y (y+1) hx hy]
  dsimp [x]
  simp only [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left, mul_one]
  omega

theorem card_reservoir {n k : ℕ} (hd : Dims n k) (i : GroupIndex k) :
    (reservoirCells (n := n) i).card = (side n k-2*k)*(side n k-k^2) := by
  classical
  have h := card_rectangle (n := n) ((groupRow i).val*side n k+2*k)
    (((groupRow i).val+1)*side n k)
    ((groupCol i).val*side n k+k^2) (((groupCol i).val+1)*side n k)
    (block_end_le hd (groupRow i)) (block_end_le hd (groupCol i))
  have he : reservoirCells (n := n) i = Finset.univ.filter (fun c : Cell n =>
      (groupRow i).val*side n k+2*k ≤ c.1.val ∧ c.1.val < ((groupRow i).val+1)*side n k ∧
      (groupCol i).val*side n k+k^2 ≤ c.2.val ∧ c.2.val < ((groupCol i).val+1)*side n k) := by
    ext c
    simp only [mem_reservoirCells, reservoir, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [he, h, Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.add_sub_add_left,
    Nat.add_sub_add_left]

theorem card_square {n k : ℕ} (hd : Dims n k) (i : GroupIndex k) :
    (squareCells (n := n) i).card = side n k^2 := by
  classical
  unfold squareCells square
  have h := card_rectangle (n := n) ((groupRow i).val*side n k) (((groupRow i).val+1)*side n k)
    ((groupCol i).val*side n k) (((groupCol i).val+1)*side n k)
    (block_end_le hd (groupRow i)) (block_end_le hd (groupCol i))
  convert h using 1 <;> simp [Nat.add_mul]; ring

/-- Target groups are exactly the square's labels, with the blank removed. -/
theorem targetGroup_eq_image_erase {n k : ℕ} [NeZero n] (i : GroupIndex k) :
    targetGroup (n := n) i = ((squareCells i).image (target n)).erase 0 := by
  classical
  ext t
  simp only [mem_targetGroup, Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨ht,hs⟩
    refine ⟨by intro h; apply ht; simp [h], position (target n) t, ?_, ?_⟩
    · exact (mem_squareCells i _).mpr hs
    · exact (target n).apply_symm_apply t
  · rintro ⟨ht,c,hc,rfl⟩
    refine ⟨by intro h; apply ht; exact Fin.ext h, ?_⟩
    simpa [position] using (mem_squareCells i c).mp hc

/-- The only missing label in a square is its blank, when present. -/
theorem card_targetGroup {n k : ℕ} [NeZero n] (hd : Dims n k) (i : GroupIndex k) :
    (targetGroup (n := n) i).card + (if square i (blank (target n)) then 1 else 0) = side n k^2 := by
  classical
  have hc : ((squareCells (n := n) i).image (target n)).card = side n k^2 := by
    rw [Finset.card_image_of_injective _ (target n).injective, card_square hd]
  have hz : (0 : Tile n) ∈ (squareCells i).image (target n) ↔ square i (blank (target n)) := by
    constructor
    · intro h
      obtain ⟨c,hc,hc0⟩ := Finset.mem_image.mp h
      have he : c = blank (target n) := (target n).injective (by simpa [blank,position] using hc0)
      simpa [he] using (mem_squareCells i c).mp hc
    · intro h
      exact Finset.mem_image.mpr ⟨blank (target n), (mem_squareCells i _).mpr h,
        (target n).apply_symm_apply 0⟩
  rw [targetGroup_eq_image_erase]
  split_ifs with h
  · exact (Finset.card_erase_add_one (hz.mpr h)).trans hc
  · rw [Finset.erase_eq_of_notMem (mt hz.mp h), Nat.add_zero, hc]

/-- The last group in row-major order. -/
def lastGroup (k : ℕ) (hk : 2 ≤ k) : GroupIndex k :=
  finProdFinEquiv (⟨k-1, by omega⟩, ⟨k-1, by omega⟩)

theorem lastGroup_val (k : ℕ) (hk : 2 ≤ k) : (lastGroup k hk).val = k*k-1 := by
  simp [lastGroup, finProdFinEquiv]
  have h : k-1+1=k := by omega
  have h2 : k*k-1+1=k*k := Nat.sub_add_cancel (by nlinarith)
  nlinarith

theorem square_target_blank {n k : ℕ} [NeZero n] (hd : Dims n k)
    (j : GroupIndex k) : square j (blank (target n)) ↔ j=lastGroup k hd := by
  have hb : blank (target n) =
      (⟨n-1, Nat.sub_lt (NeZero.pos n) (by omega)⟩,
       ⟨n-1, Nat.sub_lt (NeZero.pos n) (by omega)⟩) := by
    apply (target n).injective
    rw [target_bottomRight]
    exact (target n).apply_symm_apply 0
  have hlast : square (lastGroup k hd) (blank (target n)) := by
    rw [hb]
    simp only [square,lastGroup,groupRow,groupCol,Equiv.symm_apply_apply]
    have hp : 0<side n k := hd.side_pos
    have hkm : k-1+1=k := by have := hd.two_le; omega
    have he' : (k-1+1)*side n k=n := by rw [hkm]; exact hd.mul_side
    have he : (k-1)*side n k+side n k=n := by
      have h := he'; rw [Nat.add_mul, Nat.one_mul] at h; exact h
    exact ⟨by omega, by omega, by omega, by omega⟩
  exact ⟨fun h => square_unique hd h hlast, fun h => h ▸ hlast⟩


theorem FDims.square_target_blank {n k : ℕ} [NeZero n] (hd : FDims n k)
    (j : GroupIndex k) : square j (blank (target n)) ↔ j=lastGroup k hd := by
  have hb : blank (target n) =
      (⟨n-1, Nat.sub_lt (NeZero.pos n) (by omega)⟩,
       ⟨n-1, Nat.sub_lt (NeZero.pos n) (by omega)⟩) := by
    apply (target n).injective
    rw [target_bottomRight]
    exact (target n).apply_symm_apply 0
  have hlast : square (lastGroup k hd) (blank (target n)) := by
    rw [hb]
    simp only [square,lastGroup,groupRow,groupCol,Equiv.symm_apply_apply]
    have hp : 0<side n k := hd.side_pos
    have hkm : k-1+1=k := by have := hd.two_le; omega
    have he' : (k-1+1)*side n k=n := by rw [hkm]; exact hd.mul_side
    have he : (k-1)*side n k+side n k=n := by
      have h := he'; rw [Nat.add_mul, Nat.one_mul] at h; exact h
    exact ⟨by omega, by omega, by omega, by omega⟩
  exact ⟨fun h => hd.square_unique h hlast, fun h => h ▸ hlast⟩

end
end SlidingPuzzle.Partition
