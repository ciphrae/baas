import SlidingPuzzle.Tree.OpHopR

/-! # Geometry of a column lane

Consecutive positions of a column lane are either adjacent (same band) or
separated by a row group (`q + 1` rows apart, an odd jump since `q` is even).
Tiles moving toward their target band step efficiently. -/
namespace SlidingPuzzle.Tree
open SlidingPuzzle.Hub
open SlidingPuzzle.Hub.LayoutAux

variable {n k s q : ℕ} [NeZero n] (L : LaneSys k q)

omit [NeZero n] in
/-- The insertion position of a column hop: in the source band, at row offset
`k` (lanes after the landing band) or `s - 1` (before it). -/
theorem colPos_geom (td : TDims n k s q) (V : LaneI k q) (I : Fin k) (hI : LIn L V I) :
    colPos k s q V I < colLen L s V ∧ cBand s q V (colPos k s q V I) = I.val ∧
      cOff s q V (colPos k s q V I) = (if V.side then k else s - 1) := by
  have hks := td.k_lt_s
  have hm : 0 < s - q := by have := td.q_lt_s; omega
  have hqk := td.q_le
  unfold LIn InPiece at hI
  unfold colPos colLen cBand cOff LaneSys.pdist
  cases h : V.side
  · simp only [h, Bool.false_eq_true, if_false, add_zero] at hI ⊢
    have hd1 : Nat.dist I.val V.t.val - 1 = V.t.val - I.val - 1 := by unfold Nat.dist; omega
    rw [hd1, Nat.mul_div_cancel _ hm, Nat.mul_mod_left]
    refine ⟨Nat.mul_lt_mul_of_pos_right (by omega) hm, by omega, by omega⟩
  · simp only [h, if_true] at hI ⊢
    have hd1 : Nat.dist I.val V.t.val - 1 = I.val - V.t.val - 1 := by unfold Nat.dist; omega
    rw [hd1]
    have d := divmod (b := I.val - V.t.val - 1) (show k - q < s - q by omega)
    rw [d.1, d.2]
    refine ⟨?_, by omega, by omega⟩
    have := Nat.mul_le_mul_right (s - q) (show I.val - V.t.val - 1 + 1 ≤ blen L V by omega)
    rw [add_mul, one_mul] at this
    omega

omit [NeZero n] in
theorem cBand_zero (V : LaneI k q) :
    cBand s q V 0 = (if V.side then V.t.val + 1 else V.t.val - 1) ∧
    cOff s q V 0 = (if V.side then q else s - 1) := by
  unfold cBand cOff; simp

/-- Two consecutive positions of a column lane. -/
theorem colCell_step (td : TDims n k s q) (V : LaneI k q) (p : ℕ) (hp : p + 1 < colLen L s V) :
    (colCell (n := n) s V p).2 = (colCell (n := n) s V (p + 1)).2 ∧
    (((p + 1) % (s - q) = 0 ∧
        Nat.dist (colCell (n := n) s V p).1.val (colCell (n := n) s V (p + 1)).1.val = q + 1) ∨
      ((p + 1) % (s - q) ≠ 0 ∧
        (V.side = true → (colCell (n := n) s V (p + 1)).1.val =
          (colCell (n := n) s V p).1.val + 1) ∧
        (V.side = false → (colCell (n := n) s V p).1.val =
          (colCell (n := n) s V (p + 1)).1.val + 1))) := by
  have hm : 0 < s - q := by have := td.q_lt_s; omega
  refine ⟨Fin.ext (by rw [colCell_snd td, colCell_snd td]), ?_⟩
  rw [colCell_fst L td V p (by omega), colCell_fst L td V (p + 1) hp]
  have hdq := colPos_div_lt L td V (p + 1) hp
  have hbs := blen_side L V
  have hqs := td.q_lt_s
  unfold cBand cOff
  rcases Hub.divmod_succ hm p with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · left
    refine ⟨h1, ?_⟩
    rw [h2] at hdq
    rw [h1, h2]
    cases e : V.side
    · have := hbs.2 e
      simp only [Bool.false_eq_true, if_false]
      generalize p / (s - q) = x at *
      generalize p % (s - q) = y at *
      have : (V.t.val - 1 - x) * s = (V.t.val - 1 - (x + 1)) * s + s := by
        rw [← add_one_mul]; congr 1; omega
      simp only [Nat.dist]; omega
    · simp only [if_true]
      generalize p / (s - q) = x at *
      generalize p % (s - q) = y at *
      have : (V.t.val + 1 + (x + 1)) * s = (V.t.val + 1 + x) * s + s := by ring
      simp only [Nat.dist]; omega
  · right
    refine ⟨by omega, ?_, ?_⟩ <;> intro e <;> rw [h1, h2] <;> simp only [e, Bool.false_eq_true,
      if_false, if_true] <;> generalize p / (s - q) = x at * <;> omega

/-- Tiles moving toward their target band step efficiently on adjacent steps. -/
theorem moveCost_colCell (td : TDims n k s q) (V : LaneI k q) (p : ℕ)
    (hp : p + 1 < colLen L s V) (hstep : (p + 1) % (s - q) ≠ 0) (T : Tile n)
    (hT : colGood V (classOf td.hd T)) :
    moveCost (colCell (n := n) s V p) (colCell s V (p + 1)) T = 0 := by
  have hr : (position (target n) T).1.val / s = (classOf td.hd T).1.val := rfl
  have hb := (div_eq_iff_bounds td.s_pos).mp hr
  obtain ⟨hcol, hcase⟩ := colCell_step (n := n) L td V p hp
  rcases hcase with ⟨h1, -⟩ | ⟨-, hlow, hup⟩
  · exact absurd h1 hstep
  have r0 := colCell_fst (n := n) L td V p (by omega)
  have bb := cBand_in L td V p (by omega)
  have ob := cOff_bounds td V p
  unfold colGood at hT
  unfold InPiece at bb
  unfold moveCost
  rw [if_pos]
  simp only [gridDistance, hcol, Nat.dist]
  cases e : V.side
  · simp only [e, Bool.false_eq_true, if_false] at hT bb
    have := hup e
    have := band_lt_band s bb.1
    have := Nat.mul_le_mul_right s hT
    omega
  · simp only [e, if_true] at hT bb
    have := hlow e
    have := band_lt_band s (lt_of_le_of_lt hT bb.1)
    omega

end SlidingPuzzle.Tree
