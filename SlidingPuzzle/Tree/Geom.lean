import SlidingPuzzle.Tree.Layout

/-! # Geometry of the tree layout

Coordinates of lane cells, that they are lane cells (`key = none`), injectivity,
and the converse: every lane cell is a lane position. -/
namespace SlidingPuzzle.Tree

open SlidingPuzzle.Hub (Sq HDims sqOf classOf mkCell reservoir mkCell_fst mkCell_snd
  div_eq_iff_bounds band_lt_band cell_ext)
open SlidingPuzzle.Hub.LayoutAux

variable {n k s q : ℕ} (L : LaneSys k q)

theorem TDims.s_pos (td : TDims n k s q) : 0 < s := td.hd.s_pos
theorem TDims.k_lt_s (td : TDims n k s q) : k < s := td.hd.k_lt_s
theorem TDims.q_lt_s (td : TDims n k s q) : q < s := lt_of_le_of_lt td.q_le td.k_lt_s
theorem TDims.band_le (td : TDims n k s q) {b : ℕ} (hb : b < k) : b * s + s ≤ n := td.hd.band_le hb
theorem TDims.mul (td : TDims n k s q) : k * s = n := td.hd.mul

theorem divmod' {s b o : ℕ} (ho : o < s) : (b * s + o) / s = b ∧ (b * s + o) % s = o :=
  divmod ho

/-- Pieces lie inside `[0, k)`. -/
theorem inPiece_lt {t : Fin k} {o : Fin q} {side : Bool} {J : ℕ}
    (h : InPiece (L.len o t side) t side J) : J < k := by
  have := L.right_lt o t
  have := t.isLt
  cases side <;> simp only [InPiece, Bool.false_eq_true, if_false, if_true] at h <;> omega

theorem blen_side (H : LaneI k q) :
    (H.side = true → H.t.val + blen L H < k) ∧ (H.side = false → blen L H ≤ H.t.val) := by
  constructor
  · intro h; have := L.right_lt H.o H.t; unfold blen; rw [h]; exact this
  · intro h; have := L.left_le H.o H.t; unfold blen; rw [h]; exact this

/-! ## Row lanes -/

section rows
variable [NeZero n]

/-- Column of position `p` of a row lane. -/
def rowCol (s : ℕ) (H : LaneI k q) (p : ℕ) : ℕ :=
  if H.side then H.t.val * s + s + p else H.t.val * s - 1 - p

/-- Block column of position `p` of a row lane. -/
def rowBlk (s : ℕ) (H : LaneI k q) (p : ℕ) : ℕ :=
  if H.side then H.t.val + 1 + p / s else H.t.val - 1 - p / s

theorem rowCell_fst (td : TDims n k s q) (H : LaneI k q) (p : ℕ) :
    (rowCell (n := n) s H p).1.val = H.b.val * s + H.o.val := by
  unfold rowCell
  apply mkCell_fst
  have := td.band_le H.b.isLt
  have := H.o.isLt
  have := td.q_lt_s
  omega

omit [NeZero n] in
theorem rowLen_bound (td : TDims n k s q) (H : LaneI k q) (p : ℕ) (hp : p < rowLen L s H) :
    (H.side = true → H.t.val * s + s + p < n) ∧ (H.side = false → p < H.t.val * s) := by
  unfold rowLen at hp
  obtain ⟨h1, h2⟩ := blen_side L H
  constructor
  · intro h
    have := h1 h
    have e : (H.t.val + 1 + blen L H) * s ≤ k * s :=
      Nat.mul_le_mul_right s (show H.t.val + 1 + blen L H ≤ k by omega)
    rw [td.mul, add_mul, add_mul, one_mul] at e
    omega
  · intro h
    have := Nat.mul_le_mul_right s (h2 h)
    omega

theorem rowCell_snd (td : TDims n k s q) (H : LaneI k q) (p : ℕ) (hp : p < rowLen L s H) :
    (rowCell (n := n) s H p).2.val = rowCol s H p := by
  have hb := rowLen_bound L td H p hp
  have e : (if H.side then (H.t.val + 1) * s + p else H.t.val * s - 1 - p) = rowCol s H p := by
    unfold rowCol; split_ifs <;> ring
  unfold rowCell
  rw [e]
  apply mkCell_snd
  have := td.band_le H.t.isLt
  have := NeZero.pos n
  unfold rowCol
  cases h : H.side
  · simp only [Bool.false_eq_true, if_false]; omega
  · simp only [if_true]; exact hb.1 h

omit [NeZero n] in
theorem rowCol_div (td : TDims n k s q) (H : LaneI k q) (p : ℕ) (hp : p < rowLen L s H) :
    rowCol s H p / s = rowBlk s H p ∧ rowCol s H p % s = (if H.side then p % s else s - 1 - p % s) := by
  have hs := td.s_pos
  have hb := rowLen_bound L td H p hp
  have e1 := Nat.div_add_mod p s
  have e2 := Nat.mod_lt p hs
  unfold rowCol rowBlk
  cases h : H.side
  · simp only [Bool.false_eq_true, if_false]
    have := hb.2 h
    have hpt : p / s < H.t.val := by
      apply Nat.div_lt_of_lt_mul; rw [mul_comm]; exact this
    have e3 : H.t.val * s - 1 - p = (H.t.val - 1 - p / s) * s + (s - 1 - p % s) := by
      have : (H.t.val - 1 - p / s) * s + s * (p / s) + s = H.t.val * s := by
        rw [mul_comm s, ← add_mul, ← add_one_mul]; congr 1; omega
      omega
    rw [e3]; exact divmod (by omega)
  · simp only [if_true]
    have e3 : H.t.val * s + s + p = (H.t.val + 1 + p / s) * s + p % s := by
      rw [add_mul, add_mul, one_mul, mul_comm (p / s)]; omega
    rw [e3]; exact divmod e2

omit [NeZero n] in
/-- The block of a row position lies in the lane's piece. -/
theorem rowBlk_in (td : TDims n k s q) (H : LaneI k q) (p : ℕ) (hp : p < rowLen L s H) :
    InPiece (blen L H) H.t.val H.side (rowBlk s H p) := by
  have hs := td.s_pos
  have hq : p / s < blen L H := by
    unfold rowLen at hp
    apply Nat.div_lt_of_lt_mul; rw [mul_comm]; exact hp
  have hb := blen_side L H
  unfold InPiece rowBlk
  generalize p / s = x at *
  cases h : H.side
  · simp only [Bool.false_eq_true, if_false]; have := hb.2 h; omega
  · simp only [if_true]; omega

theorem rowCell_lane (td : TDims n k s q) (H : LaneI k q) (p : ℕ) (hp : p < rowLen L s H) :
    LaneCell L s (rowCell (n := n) s H p) := by
  left
  have hq := H.o.isLt
  have hqs := td.q_lt_s
  have d := divmod (b := H.b.val) (show H.o.val < s by omega)
  rw [rowCell_fst td H p]
  refine ⟨by rw [d.2]; exact hq, ?_⟩
  simp only [d.2]
  refine ⟨H.t, H.side, ?_⟩
  rw [rowCell_snd L td H p hp, (rowCol_div L td H p hp).1]
  exact rowBlk_in L td H p hp

theorem rowCell_inj (td : TDims n k s q) {H H' : LaneI k q} {p p' : ℕ}
    (hp : p < rowLen L s H) (hp' : p' < rowLen L s H')
    (h : (rowCell (n := n) s H p) = rowCell s H' p') : H = H' ∧ p = p' := by
  have e1 := congrArg (fun x : Cell n => x.1.val) h
  have e2 := congrArg (fun x : Cell n => x.2.val) h
  simp only [rowCell_fst td, rowCell_snd L td _ _ hp, rowCell_snd L td _ _ hp'] at e1 e2
  have hqs := td.q_lt_s
  obtain ⟨hb, ho⟩ := divmod_eq (by have := H.o.isLt; omega) (by have := H'.o.isLt; omega) e1
  have hbb : H.b = H'.b := Fin.ext hb
  have hoo : H.o = H'.o := Fin.ext ho
  -- the same block lies in both pieces
  have i1 := rowBlk_in L td H p hp
  have i2 := rowBlk_in L td H' p' hp'
  have hbl : rowBlk s H p = rowBlk s H' p' := by
    rw [← (rowCol_div L td H p hp).1, ← (rowCol_div L td H' p' hp').1, e2]
  rw [hbl] at i1
  unfold blen at i1 i2
  rw [hoo] at i1
  obtain ⟨ht, hsd⟩ := L.disj H'.o H.t H'.t H.side H'.side _ i1 i2
  have hH : H = H' := by
    cases H; cases H'; simp only at hbb hoo ht hsd; subst hbb hoo ht hsd; rfl
  subst hH
  refine ⟨rfl, ?_⟩
  have hb1 := rowLen_bound L td H p hp
  have hb2 := rowLen_bound L td H p' hp'
  unfold rowCol at e2
  cases h : H.side
  · have := hb1.2 h; have := hb2.2 h
    rw [h] at e2; simp only [Bool.false_eq_true, if_false] at e2; omega
  · rw [h] at e2; simp only [if_true] at e2; omega

end rows

/-! ## Column lanes -/

section cols
variable [NeZero n]

omit [NeZero n] in
theorem cOff_bounds (td : TDims n k s q) (V : LaneI k q) (p : ℕ) :
    q ≤ cOff s q V p ∧ cOff s q V p < s := by
  have hm : 0 < s - q := by have := td.q_lt_s; omega
  have := Nat.mod_lt p hm
  unfold cOff
  split_ifs <;> omega

omit [NeZero n] in
theorem colPos_div_lt (td : TDims n k s q) (V : LaneI k q) (p : ℕ) (hp : p < colLen L s V) :
    p / (s - q) < blen L V := by
  have hm : 0 < s - q := by have := td.q_lt_s; omega
  exact (Nat.div_lt_iff_lt_mul hm).mpr hp

omit [NeZero n] in
theorem cBand_in (td : TDims n k s q) (V : LaneI k q) (p : ℕ) (hp : p < colLen L s V) :
    InPiece (blen L V) V.t.val V.side (cBand s q V p) := by
  have hd := colPos_div_lt L td V p hp
  have hb := blen_side L V
  unfold InPiece cBand
  generalize p / (s - q) = x at *
  cases h : V.side
  · simp only [Bool.false_eq_true, if_false]; have := hb.2 h; omega
  · simp only [if_true]; omega

omit [NeZero n] in
theorem cBand_lt (td : TDims n k s q) (V : LaneI k q) (p : ℕ) (hp : p < colLen L s V) :
    cBand s q V p < k := by
  have := cBand_in L td V p hp
  exact inPiece_lt L this

theorem colCell_snd (td : TDims n k s q) (V : LaneI k q) (p : ℕ) :
    (colCell (n := n) s V p).2.val = V.b.val * s + V.o.val := by
  unfold colCell
  apply mkCell_snd
  have := td.band_le V.b.isLt
  have := V.o.isLt
  have := td.q_lt_s
  omega

theorem colCell_fst (td : TDims n k s q) (V : LaneI k q) (p : ℕ) (hp : p < colLen L s V) :
    (colCell (n := n) s V p).1.val = cBand s q V p * s + cOff s q V p := by
  unfold colCell
  apply mkCell_fst
  have := td.band_le (cBand_lt L td V p hp)
  have := (cOff_bounds td V p).2
  omega

theorem colCell_lane (td : TDims n k s q) (V : LaneI k q) (p : ℕ) (hp : p < colLen L s V) :
    LaneCell L s (colCell (n := n) s V p) := by
  right
  have ho := cOff_bounds td V p
  have hq := V.o.isLt
  have hqs := td.q_lt_s
  have d1 := divmod (b := cBand s q V p) ho.2
  have d2 := divmod (b := V.b.val) (show V.o.val < s by omega)
  rw [colCell_fst L td V p hp, colCell_snd td V p]
  refine ⟨by rw [d1.2]; exact ho.1, by rw [d2.2]; exact hq, ?_⟩
  simp only [d2.2, d1.1]
  exact ⟨V.t, V.side, cBand_in L td V p hp⟩

theorem colCell_inj (td : TDims n k s q) {V V' : LaneI k q} {p p' : ℕ}
    (hp : p < colLen L s V) (hp' : p' < colLen L s V')
    (h : (colCell (n := n) s V p) = colCell s V' p') : V = V' ∧ p = p' := by
  have e1 := congrArg (fun x : Cell n => x.1.val) h
  have e2 := congrArg (fun x : Cell n => x.2.val) h
  simp only [colCell_fst L td _ _ hp, colCell_fst L td _ _ hp', colCell_snd td] at e1 e2
  have hqs := td.q_lt_s
  have hm : 0 < s - q := by omega
  have ho := cOff_bounds td V p
  have ho' := cOff_bounds td V' p'
  obtain ⟨hB, hO⟩ := divmod_eq ho.2 ho'.2 e1
  obtain ⟨hc, hoo⟩ := divmod_eq (by have := V.o.isLt; omega) (by have := V'.o.isLt; omega) e2
  have i1 := cBand_in L td V p hp
  have i2 := cBand_in L td V' p' hp'
  rw [hB] at i1
  unfold blen at i1 i2
  have hoo' : V.o = V'.o := Fin.ext hoo
  rw [hoo'] at i1
  obtain ⟨ht, hsd⟩ := L.disj V'.o V.t V'.t V.side V'.side _ i1 i2
  have hV : V = V' := by
    cases V; cases V'; simp only at hc hoo' ht hsd
    have hc' := Fin.ext hc
    subst hc' hoo' ht hsd; rfl
  subst hV
  refine ⟨rfl, ?_⟩
  have b1 := colPos_div_lt L td V p hp
  have b2 := colPos_div_lt L td V p' hp'
  have r1 := Nat.mod_add_div p (s - q)
  have r2 := Nat.mod_add_div p' (s - q)
  have l1 := Nat.mod_lt p hm
  have l2 := Nat.mod_lt p' hm
  have bs := blen_side L V
  simp only [cBand, cOff] at hB hO
  cases h : V.side <;> simp only [h, Bool.false_eq_true, if_false, if_true] at hB hO bs
  · have := bs.2 trivial
    have e3 : p / (s - q) = p' / (s - q) := by omega
    have e4 : p % (s - q) = p' % (s - q) := by omega
    rw [← r1, ← r2, e3, e4]
  · have e3 : p / (s - q) = p' / (s - q) := by omega
    have e4 : p % (s - q) = p' % (s - q) := by omega
    rw [← r1, ← r2, e3, e4]

theorem rowCell_ne_colCell (td : TDims n k s q) (H V : LaneI k q) (p p' : ℕ)
    (hp' : p' < colLen L s V) : (rowCell (n := n) s H p) ≠ colCell s V p' := by
  intro h
  have e1 := congrArg (fun x : Cell n => x.1.val) h
  simp only [rowCell_fst td, colCell_fst L td _ _ hp'] at e1
  have ho := cOff_bounds td V p'
  have hqs := td.q_lt_s
  have hq := H.o.isLt
  have := divmod_eq (show H.o.val < s by omega) ho.2 e1
  omega

end cols

end SlidingPuzzle.Tree
