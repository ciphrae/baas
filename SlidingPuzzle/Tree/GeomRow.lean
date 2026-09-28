import SlidingPuzzle.Tree.OpInsert
import SlidingPuzzle.Hub.PrimWalk

/-! # Geometry of a row lane with its landing strip

`lineCell H u` parametrizes row `H.b*s + H.o` from the far end of the landing
strip: `u < s` is the landing strip (region of `rowLand H`), `u = s + p` is
position `p` of the lane. -/
namespace SlidingPuzzle.Tree

open SlidingPuzzle.Hub
open SlidingPuzzle.Hub.LayoutAux

variable {n k s q : ℕ} [NeZero n] (L : LaneSys k q)

/-- Column of `lineCell`. -/
def lineCol (s : ℕ) (H : LaneI k q) (u : ℕ) : ℕ :=
  if H.side then H.t.val * s + u else H.t.val * s + s - 1 - u

/-- The row of a lane from the far end of its landing strip. -/
def lineCell (s : ℕ) (H : LaneI k q) (u : ℕ) : Cell n :=
  mkCell n (H.b.val * s + H.o.val) (lineCol s H u)

theorem lineCell_fst (td : TDims n k s q) (H : LaneI k q) (u : ℕ) :
    (lineCell (n := n) s H u).1.val = H.b.val * s + H.o.val := by
  apply mkCell_fst
  have := td.band_le H.b.isLt
  have := H.o.isLt
  have := td.q_lt_s
  omega

theorem lineCell_snd (td : TDims n k s q) (H : LaneI k q) (u : ℕ) (hu : u < s + rowLen L s H) :
    (lineCell (n := n) s H u).2.val = lineCol s H u := by
  apply mkCell_snd
  have := td.band_le H.t.isLt
  have := NeZero.pos n
  obtain ⟨h1, h2⟩ := blen_side L H
  unfold lineCol
  cases h : H.side
  · simp only [Bool.false_eq_true, if_false]; omega
  · simp only [if_true]
    unfold rowLen at hu
    have := h1 h
    have e : (H.t.val + 1 + blen L H) * s ≤ k * s :=
      Nat.mul_le_mul_right s (show H.t.val + 1 + blen L H ≤ k by omega)
    rw [td.mul, add_mul, add_mul, one_mul] at e
    omega

theorem lineCell_rowCell (td : TDims n k s q) (H : LaneI k q) (p : ℕ) (hp : p < rowLen L s H) :
    lineCell (n := n) s H (s + p) = rowCell s H p := by
  apply cell_ext
  · rw [lineCell_fst td, rowCell_fst td]
  · rw [lineCell_snd L td H _ (by omega), rowCell_snd L td H p hp]
    have hb := rowLen_bound L td H p hp
    unfold lineCol rowCol
    cases h : H.side
    · simp only [Bool.false_eq_true, if_false]; have := hb.2 h; omega
    · simp only [if_true]; omega

theorem key_lineCell_strip (td : TDims n k s q) (H : LaneI k q) (hpos : 0 < blen L H) (u : ℕ)
    (hu : u < s) : key L td.hd (lineCell (n := n) s H u) = some (rowLand H) := by
  apply (key_eq_some L td.hd).mpr
  apply region_strip L td H hpos (o' := if H.side then u else s - 1 - u) (lineCell_fst td H u)
  · rw [lineCell_snd L td H u (by omega)]
    unfold lineCol
    split_ifs <;> omega
  · split_ifs <;> omega

theorem lineCell_adj (td : TDims n k s q) (H : LaneI k q) (u : ℕ)
    (hu : u + 1 < s + rowLen L s H) :
    gridDistance (lineCell (n := n) s H u) (lineCell s H (u + 1)) = 1 := by
  simp only [gridDistance, lineCell_fst td, lineCell_snd L td H u (by omega),
    lineCell_snd L td H (u + 1) hu, Nat.dist]
  unfold lineCol
  have hs := td.s_pos
  obtain ⟨h1, h2⟩ := blen_side L H
  unfold rowLen at hu
  cases h : H.side
  · have := Nat.mul_le_mul_right s (h2 h)
    simp only [Bool.false_eq_true, if_false]; omega
  · simp only [if_true]; omega

theorem lineCell_inj (td : TDims n k s q) (H : LaneI k q) {u u' : ℕ}
    (hu : u < s + rowLen L s H) (hu' : u' < s + rowLen L s H)
    (h : lineCell (n := n) s H u = lineCell s H u') : u = u' := by
  have e := congrArg (fun x : Cell n => x.2.val) h
  simp only [lineCell_snd L td H u hu, lineCell_snd L td H u' hu'] at e
  have hb := rowLen_bound L td H
  unfold lineCol at e
  cases hs : H.side
  · simp only [hs, Bool.false_eq_true, if_false] at e
    have h1 : u - s < rowLen L s H ∨ u < s := by omega
    have h2 : u' - s < rowLen L s H ∨ u' < s := by omega
    have b1 : ∀ p, p < rowLen L s H → p < H.t.val * s := fun p hp => (hb p hp).2 hs
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · have := b1 _ h1; have := b1 _ h2; omega
    · have := b1 _ h1; omega
    · have := b1 _ h2; omega
    · omega
  · simp only [hs, if_true] at e; omega

/-- Tiles moving toward their target block column step efficiently (from
position `u+1` to `u`, once past the strip's far end). -/
theorem moveCost_lineCell (td : TDims n k s q) (H : LaneI k q) (u : ℕ) (hsu : s ≤ u + 1)
    (hu : u + 1 < s + rowLen L s H) (T : Tile n) (hT : rowGood H (classOf td.hd T)) :
    moveCost (lineCell (n := n) s H u) (lineCell s H (u + 1)) T = 0 := by
  have hc : (position (target n) T).2.val / s = (classOf td.hd T).2.val := rfl
  have hb := (div_eq_iff_bounds td.s_pos).mp hc
  unfold rowGood at hT
  unfold moveCost
  rw [if_pos]
  simp only [gridDistance, lineCell_fst td, lineCell_snd L td H u (by omega),
    lineCell_snd L td H (u + 1) hu, Nat.dist]
  unfold lineCol
  cases h : H.side
  · simp only [h, Bool.false_eq_true, if_false] at hT ⊢
    have : H.t.val * s ≤ (classOf td.hd T).2.val * s := Nat.mul_le_mul_right s hT
    have := Nat.mul_le_mul_right s ((blen_side L H).2 h)
    unfold rowLen at hu
    omega
  · simp only [h, if_true] at hT ⊢
    have : (classOf td.hd T).2.val * s + s ≤ H.t.val * s + s := by
      have := Nat.mul_le_mul_right s (show (classOf td.hd T).2.val ≤ H.t.val from hT)
      omega
    omega

/-- The insertion position of a row hop lies in the lane, above the source
block's reservoir column farthest from the landing block. -/
theorem rowPos_geom (td : TDims n k s q) (H : LaneI k q) (J : Fin k) (hJ : LIn L H J) :
    rowPos k s H J < rowLen L s H ∧
    rowCol s H (rowPos k s H J) = (if H.side then J.val * s + s - 1 else J.val * s + k) := by
  have hks := td.k_lt_s
  have hs := td.s_pos
  unfold LIn InPiece at hJ
  unfold rowPos rowLen rowCol LaneSys.pdist
  cases h : H.side
  · simp only [h, Bool.false_eq_true, if_false] at hJ ⊢
    obtain ⟨m, hm⟩ : ∃ m, H.t.val = J.val + 1 + m := ⟨H.t.val - J.val - 1, by omega⟩
    have hd1 : Nat.dist J.val H.t.val - 1 = m := by unfold Nat.dist; omega
    rw [hd1]
    have e1 : H.t.val * s = J.val * s + (m + 1) * s := by rw [hm]; ring
    have e2 : (m + 1) * s ≤ blen L H * s := Nat.mul_le_mul_right s (by omega)
    rw [add_mul, one_mul] at e1 e2
    constructor <;> omega
  · simp only [h, if_true] at hJ ⊢
    obtain ⟨m, hm⟩ : ∃ m, J.val = H.t.val + 1 + m := ⟨J.val - H.t.val - 1, by omega⟩
    have hd1 : Nat.dist J.val H.t.val - 1 = m := by unfold Nat.dist; omega
    rw [hd1]
    have e1 : J.val * s = H.t.val * s + (m + 1) * s := by rw [hm]; ring
    have e2 : (m + 1) * s ≤ blen L H * s := Nat.mul_le_mul_right s (by omega)
    rw [add_mul, one_mul] at e1 e2
    constructor <;> omega

end SlidingPuzzle.Tree
