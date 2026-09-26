import SlidingPuzzle.Hub.PrimRes
import SlidingPuzzle.Hub.PrimWalk

/-! # Geometry of a row corridor with its landing strip

`lineCell H u` parametrizes the row `R(b,c)` of a row half `H = (b,c,right)`
starting from the far end of the landing strip: `u < s` is the landing strip
(region of the hub `(b,c)`), `u = s + q` is position `q` of the half. -/
namespace SlidingPuzzle.Hub

variable {n k s : ℕ} [NeZero n]

/-- Column of `lineCell`. -/
def lineCol (s : ℕ) (H : RowH k) (u : ℕ) : ℕ :=
  if H.2.2 then H.2.1.val * s + u else H.2.1.val * s + s - 1 - u

/-- The row `R(b,c)` from the far end of the landing strip. -/
def lineCell (k s : ℕ) (H : RowH k) (u : ℕ) : Cell n :=
  mkCell n (H.1.val * s + H.2.1.val) (lineCol s H u)

theorem lineCell_fst (hd : HDims n k s) (H : RowH k) (u : ℕ) :
    (lineCell (n := n) k s H u).1.val = H.1.val * s + H.2.1.val := by
  apply mkCell_fst
  have := hd.band_le H.1.isLt
  have := H.2.1.isLt
  have := hd.k_lt_s
  omega

theorem lineCell_snd (hd : HDims n k s) (H : RowH k) (u : ℕ) (hu : u < s + rowLen k s H) :
    (lineCell (n := n) k s H u).2.val = lineCol s H u := by
  apply mkCell_snd
  have := hd.band_le H.2.1.isLt
  have := NeZero.pos n
  unfold lineCol
  cases h : H.2.2
  · simp only [Bool.false_eq_true, if_false]; omega
  · simp only [if_true]
    unfold rowLen at hu
    rw [h, if_pos rfl] at hu
    have hc := H.2.1.isLt
    have e : H.2.1.val * s + s + (k - 1 - H.2.1.val) * s = n := by
      rw [← hd.mul, ← add_one_mul, ← add_mul]; congr 1; omega
    omega

theorem lineCell_rowCell (hd : HDims n k s) (H : RowH k) (q : ℕ) (hq : q < rowLen k s H) :
    lineCell (n := n) k s H (s + q) = rowCell k s H q := by
  apply cell_ext
  · rw [lineCell_fst hd, rowCell_fst hd]
  · rw [lineCell_snd hd H _ (by omega), rowCell_snd hd H q hq]
    have hb := rowLen_bound hd H q hq
    unfold lineCol rowCol
    cases h : H.2.2
    · simp only [Bool.false_eq_true, if_false]; have := hb.2 h; omega
    · simp only [if_true]; omega

theorem keyOf_lineCell_strip (hd : HDims n k s) (H : RowH k) (u : ℕ) (hu : u < s) :
    keyOf hd (lineCell (n := n) k s H u) = some (H.1, H.2.1) := by
  have hc := H.2.1.isLt
  have hks := hd.k_lt_s
  apply keyOf_coords_some hd (Q := (H.1, H.2.1)) (o := H.2.1.val)
    (o' := if H.2.2 then u else s - 1 - u) (lineCell_fst hd H u)
  · rw [lineCell_snd hd H u (by omega)]
    unfold lineCol
    dsimp only
    split_ifs <;> omega
  · omega
  · split_ifs <;> omega
  · left; rfl

theorem lineCell_adj (hd : HDims n k s) (H : RowH k) (u : ℕ) (hu : u + 1 < s + rowLen k s H) :
    gridDistance (lineCell (n := n) k s H u) (lineCell k s H (u + 1)) = 1 := by
  simp only [gridDistance, lineCell_fst hd, lineCell_snd hd H u (by omega),
    lineCell_snd hd H (u + 1) hu, Nat.dist]
  unfold lineCol
  unfold rowLen at hu
  split_ifs at hu ⊢ <;> omega

theorem lineCell_inj (hd : HDims n k s) (H : RowH k) {u u' : ℕ}
    (hu : u < s + rowLen k s H) (hu' : u' < s + rowLen k s H)
    (h : lineCell (n := n) k s H u = lineCell k s H u') : u = u' := by
  have e := congrArg (fun x : Cell n => x.2.val) h
  simp only [lineCell_snd hd H u hu, lineCell_snd hd H u' hu'] at e
  unfold lineCol at e
  unfold rowLen at hu hu'
  split_ifs at e hu hu' <;> omega

/-- Clean tiles move toward their target block on the row (from position
`u+1` to `u`, once the tile is past the strip's far end). -/
theorem moveCost_lineCell (hd : HDims n k s) (H : RowH k) (u : ℕ) (hsu : s ≤ u + 1)
    (hu : u + 1 < s + rowLen k s H) (T : Tile n) (hT : (classOf hd T).2 = H.2.1) :
    moveCost (lineCell (n := n) k s H u) (lineCell k s H (u + 1)) T = 0 := by
  have hc : (position (target n) T).2.val / s = H.2.1.val := by
    have := congrArg Fin.val hT
    simpa [classOf, sqOf] using this
  have hb := (div_eq_iff_bounds hd.s_pos).mp hc
  unfold moveCost
  rw [if_pos]
  simp only [gridDistance, lineCell_fst hd, lineCell_snd hd H u (by omega),
    lineCell_snd hd H (u + 1) hu, Nat.dist]
  unfold lineCol
  unfold rowLen at hu
  split_ifs at hu ⊢ <;> omega

end SlidingPuzzle.Hub
