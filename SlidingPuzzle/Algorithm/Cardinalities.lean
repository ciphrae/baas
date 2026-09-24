import SlidingPuzzle.Algorithm.Partition
import SlidingPuzzle.Target

/-! Finite cardinalities of the paper's partition, proved directly from intervals. -/
namespace SlidingPuzzle.Partition

noncomputable section
open Classical

private def axis (n lo hi : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun x => lo ≤ x.val ∧ x.val < hi

private theorem card_axis (n lo hi : ℕ) (hhi : hi ≤ n) :
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

private theorem card_rectangle {n : ℕ} (xl xh yl yh : ℕ) (hx : xh ≤ n) (hy : yh ≤ n) :
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

private theorem cube_ge (k : ℕ) (hk : 2 ≤ k) : k ≤ k^3 ∧ k^2 ≤ k^3 := by
  have h2 : k ≤ k^2 := by nlinarith
  constructor <;> nlinarith [Nat.mul_le_mul_left k h2]

private theorem block_end_le {n k : ℕ} (hn : n = k^4) (a : Fin k) :
    (a.val+1)*k^3 ≤ n := by
  calc
    (a.val+1)*k^3 ≤ k*k^3 := Nat.mul_le_mul_right _ a.isLt
    _ = n := by rw [hn]; ring

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

/-- The part of a horizontal corridor in a single column block. -/
def horizontalSliceCells {n k : ℕ} (i : GroupIndex k) (b : Fin k) : Finset (Cell n) := by
  classical
  exact Finset.univ.filter fun c => horizontal i c ∧
    b.val*k^3 ≤ c.2.val ∧ c.2.val < (b.val+1)*k^3

@[simp] theorem mem_horizontalSliceCells {n k : ℕ} (i : GroupIndex k) (b : Fin k)
    (c : Cell n) : c ∈ horizontalSliceCells i b ↔
      horizontal i c ∧ b.val*k^3 ≤ c.2.val ∧ c.2.val < (b.val+1)*k^3 := by
  simp [horizontalSliceCells]

theorem card_horizontalSlice {n k : ℕ} (hk : 2 ≤ k) (hn : n=k^4)
    (i : GroupIndex k) (b : Fin k) : (horizontalSliceCells (n := n) i b).card = k^3 := by
  let r := (groupRow i).val*k^3+(groupCol i).val
  have hr : r+1 ≤ n := by
    have he := block_end_le hn (groupRow i)
    have hb := (groupCol i).isLt
    have hg := (cube_ge k hk).1
    dsimp [r]
    nlinarith
  have he : horizontalSliceCells (n := n) i b = Finset.univ.filter (fun c : Cell n =>
      r ≤ c.1.val ∧ c.1.val < r+1 ∧ b.val*k^3 ≤ c.2.val ∧ c.2.val < (b.val+1)*k^3) := by
    ext c
    simp only [mem_horizontalSliceCells,horizontal,Finset.mem_filter,Finset.mem_univ,true_and]
    dsimp [r]
    omega
  rw [he,card_rectangle r (r+1) _ _ hr (block_end_le hn b)]
  simp [Nat.add_mul]

@[simp] theorem mem_horizontalCells {n k : ℕ} (i : GroupIndex k) (c : Cell n) :
    c ∈ horizontalCells i ↔ horizontal i c := by classical simp [horizontalCells]
@[simp] theorem mem_verticalCells {n k : ℕ} (i j : GroupIndex k) (c : Cell n) :
    c ∈ verticalCells i j ↔ vertical i j c := by classical simp [verticalCells]
@[simp] theorem mem_reservoirCells {n k : ℕ} (i : GroupIndex k) (c : Cell n) :
    c ∈ reservoirCells i ↔ reservoir i c := by classical simp [reservoirCells]
@[simp] theorem mem_squareCells {n k : ℕ} (i : GroupIndex k) (c : Cell n) :
    c ∈ squareCells i ↔ square i c := by classical simp [squareCells]

theorem card_horizontal {n k : ℕ} (hk : 2 ≤ k) (hn : n=k^4) (i : GroupIndex k) :
    (horizontalCells (n := n) i).card = n := by
  classical
  let r := (groupRow i).val*k^3+(groupCol i).val
  have hrow : r+1 ≤ n := by
    have he := block_end_le hn (groupRow i)
    have hb := (groupCol i).isLt
    have hg := (cube_ge k hk).1
    dsimp [r]
    nlinarith
  have he : horizontalCells (n := n) i =
      Finset.univ.filter (fun c : Cell n => r ≤ c.1.val ∧ c.1.val < r+1 ∧
        0 ≤ c.2.val ∧ c.2.val < n) := by
    ext c
    simp only [mem_horizontalCells, horizontal, Finset.mem_filter, Finset.mem_univ, true_and]
    have := c.2.isLt
    dsimp [r]
    omega
  rw [he, card_rectangle r (r+1) 0 n hrow le_rfl]
  simp

theorem card_vertical {n k : ℕ} (hk : 2 ≤ k) (hn : n=k^4) (i j : GroupIndex k) :
    (verticalCells (n := n) i j).card = k^3-k := by
  classical
  let x := (groupRow i).val*k^3
  let y := (groupCol i).val*k^3+j.val
  have hx := block_end_le hn (groupRow i)
  have hy : y+1 ≤ n := by
    have he := block_end_le hn (groupCol i)
    have hj : j.val < k^2 := by simpa only [pow_two] using j.isLt
    have hg := (cube_ge k hk).2
    dsimp [y]
    nlinarith
  have he : verticalCells (n := n) i j =
      Finset.univ.filter (fun c : Cell n => x+k ≤ c.1.val ∧
        c.1.val < ((groupRow i).val+1)*k^3 ∧ y ≤ c.2.val ∧ c.2.val < y+1) := by
    ext c
    simp only [mem_verticalCells, vertical, Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp [x,y]
    omega
  rw [he, card_rectangle (x+k) _ y (y+1) hx hy]
  dsimp [x]
  simp [Nat.add_mul, Nat.add_sub_add_left]

theorem card_reservoir {n k : ℕ} (hn : n=k^4) (i : GroupIndex k) :
    (reservoirCells (n := n) i).card = (k^3-k)*(k^3-k^2) := by
  classical
  unfold reservoirCells reservoir
  have h := card_rectangle (n := n) ((groupRow i).val*k^3+k) (((groupRow i).val+1)*k^3)
    ((groupCol i).val*k^3+k^2) (((groupCol i).val+1)*k^3)
    (block_end_le hn (groupRow i)) (block_end_le hn (groupCol i))
  simpa [Nat.add_mul, Nat.add_sub_add_left] using h

theorem card_square {n k : ℕ} (hn : n=k^4) (i : GroupIndex k) :
    (squareCells (n := n) i).card = k^6 := by
  classical
  unfold squareCells square
  have h := card_rectangle (n := n) ((groupRow i).val*k^3) (((groupRow i).val+1)*k^3)
    ((groupCol i).val*k^3) (((groupCol i).val+1)*k^3)
    (block_end_le hn (groupRow i)) (block_end_le hn (groupCol i))
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
theorem card_targetGroup {n k : ℕ} [NeZero n] (hn : n=k^4) (i : GroupIndex k) :
    (targetGroup (n := n) i).card + (if square i (blank (target n)) then 1 else 0) = k^6 := by
  classical
  have hc : ((squareCells (n := n) i).image (target n)).card = k^6 := by
    rw [Finset.card_image_of_injective _ (target n).injective, card_square hn]
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

theorem square_target_blank {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hn : n=k^4)
    (j : GroupIndex k) : square j (blank (target n)) ↔ j=lastGroup k hk := by
  have hb : blank (target n) =
      (⟨n-1, Nat.sub_lt (NeZero.pos n) (by omega)⟩,
       ⟨n-1, Nat.sub_lt (NeZero.pos n) (by omega)⟩) := by
    apply (target n).injective
    rw [target_bottomRight]
    exact (target n).apply_symm_apply 0
  have hlast : square (lastGroup k hk) (blank (target n)) := by
    rw [hb]
    simp only [square,lastGroup,groupRow,groupCol,Equiv.symm_apply_apply]
    have hp : 0<k^3 := by positivity
    have hkm : k-1+1=k := by omega
    have he : (k-1)*k^3+k^3=n := by nlinarith [show k*k^3=n by rw [hn]; ring]
    have he' : (k-1+1)*k^3=n := by rw [hkm,hn]; ring
    exact ⟨by omega, by omega, by omega, by omega⟩
  exact ⟨fun h => square_unique hk h hlast, fun h => h ▸ hlast⟩

end
end SlidingPuzzle.Partition
