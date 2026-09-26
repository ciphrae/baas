import SlidingPuzzle.Hub.Interface
import SlidingPuzzle.Paths
import SlidingPuzzle.Algorithm.Accounting
import SlidingPuzzle.Moves.Block
import SlidingPuzzle.Moves.BlankAccess
import SlidingPuzzle.Hub.LayoutAux

/-! # The hub layout on boards

Cells, squares, classes, corridor cells and regions for a board of side
`n = k*s` (`HDims n k s`), the relation `Rel` between a board and an `IState`,
and the count of misplaced tiles that Cleanup pays for. -/
namespace SlidingPuzzle.Hub

variable {n k s : ℕ}

theorem HDims.div_lt (hd : HDims n k s) (x : Fin n) : x.val / s < k := by
  have hs : 0 < s := by have := hd.room; omega
  apply (Nat.div_lt_iff_lt_mul hs).mpr
  calc x.val < n := x.isLt
    _ = k * s := hd.mul.symm

/-- The square containing a cell. -/
def sqOf (hd : HDims n k s) (x : Cell n) : Sq k :=
  (⟨x.1.val / s, hd.div_lt x.1⟩, ⟨x.2.val / s, hd.div_lt x.2⟩)

/-- The class of a tile: the square of its target cell. -/
def classOf (hd : HDims n k s) (t : Tile n) : Sq k := sqOf hd (position (target n) t)

/-- Cell of a board from natural coordinates (reduced mod `n`; exact in range). -/
def mkCell (n : ℕ) [NeZero n] (r c : ℕ) : Cell n := (Fin.ofNat n r, Fin.ofNat n c)

/-- Position `q` of the row half `H = (b, c, right)`: row `b*s + c`, column
`(c+1)*s + q` (right) or `c*s - 1 - q` (left). -/
def rowCell (k s : ℕ) [NeZero n] (H : RowH k) (q : ℕ) : Cell n :=
  mkCell n (H.1.val * s + H.2.1.val)
    (if H.2.2 then (H.2.1.val + 1) * s + q else H.2.1.val * s - 1 - q)

/-- Position `q` of the column half `V = (c, a, lower)`: column `c*s + a`; with
`m = s - k`, band `a+1+q/m` at row offset `k + q%m` (lower) or band `a-1-q/m`
at row offset `s-1-q%m` (upper). -/
def colCell (k s : ℕ) [NeZero n] (V : ColH k) (q : ℕ) : Cell n :=
  mkCell n
    (if V.2.2 then (V.2.1.val + 1 + q / (s - k)) * s + (k + q % (s - k))
      else (V.2.1.val - 1 - q / (s - k)) * s + (s - 1 - q % (s - k)))
    (V.1.val * s + V.2.1.val)

/-- The region of square `Q`: its reservoir (row and column offsets `≥ k`), its
landing strip (row offset `Q.2`) and its own column piece (row offset `≥ k`,
column offset `Q.1`). -/
def region (k s : ℕ) (Q : Sq k) (x : Cell n) : Prop :=
  x.1.val / s = Q.1.val ∧ x.2.val / s = Q.2.val ∧
    (x.1.val % s = Q.2.val ∨
      (k ≤ x.1.val % s ∧ (k ≤ x.2.val % s ∨ x.2.val % s = Q.1.val)))

instance (k s : ℕ) (Q : Sq k) (x : Cell n) : Decidable (region k s Q x) := by
  unfold region; infer_instance

/-- The reservoir rectangle of square `Q`. -/
def reservoir (k s : ℕ) (Q : Sq k) (x : Cell n) : Prop :=
  x.1.val / s = Q.1.val ∧ x.2.val / s = Q.2.val ∧ k ≤ x.1.val % s ∧ k ≤ x.2.val % s

instance (k s : ℕ) (Q : Sq k) (x : Cell n) : Decidable (reservoir k s Q x) := by
  unfold reservoir; infer_instance

/-- Nonblank tiles of class `y` in the region of `Q`. -/
noncomputable def regionCount (hd : HDims n k s) (B : Board n) (Q y : Sq k) : ℕ := by
  classical
  exact (Finset.univ.filter fun x : Cell n =>
    region k s Q x ∧ (B x).val ≠ 0 ∧ classOf hd (B x) = y).card

/-- A board realizes an `IState`: corridor positions hold nonblank tiles of the
recorded classes, region counts agree, and the blank is in the reservoir of
the recorded square. -/
def Rel (hd : HDims n k s) [NeZero n] (B : Board n) (σ : IState k) : Prop :=
  (∀ H q, q < rowLen k s H →
    (B (rowCell k s H q)).val ≠ 0 ∧ classOf hd (B (rowCell k s H q)) = σ.row H q) ∧
  (∀ V q, q < colLen k s V →
    (B (colCell k s V q)).val ≠ 0 ∧ classOf hd (B (colCell k s V q)) = σ.col V q) ∧
  (∀ Q y, regionCount hd B Q y = σ.cnt Q y) ∧
  reservoir k s σ.blank (blank B)

/-- Nonblank tiles outside the square of their target. -/
noncomputable def misplaced (hd : HDims n k s) (B : Board n) : ℕ := by
  classical
  exact (Finset.univ.filter fun x : Cell n =>
    (B x).val ≠ 0 ∧ classOf hd (B x) ≠ sqOf hd x).card

/-- The `IState` read off a board. -/
noncomputable def absState (hd : HDims n k s) [NeZero n] (B : Board n) : IState k where
  row H q := classOf hd (B (rowCell k s H q))
  col V q := classOf hd (B (colCell k s V q))
  cnt := regionCount hd B
  blank := sqOf hd (blank B)

/-! ## Decoding cells: regions, row positions, column positions -/

namespace LayoutFacts

open LayoutAux Finset

/-! ## Cells of the layout -/

theorem hs_pos (hd : HDims n k s) : 0 < s := by have := hd.room; omega

theorem hk_lt_s (hd : HDims n k s) : k < s := by have := hd.room; omega

theorem mkCell_val [NeZero n] {r c : ℕ} (hr : r < n) (hc : c < n) :
    (mkCell n r c).1.val = r ∧ (mkCell n r c).2.val = c := by
  simp [mkCell, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hc]

/-- Coordinates of a row-half position. -/
theorem rowCell_val (hd : HDims n k s) [NeZero n] (H : RowH k) {q : ℕ}
    (hq : q < rowLen k s H) :
    (rowCell (n := n) k s H q).1.val = H.1.val * s + H.2.1.val ∧
    (rowCell (n := n) k s H q).2.val =
      (if H.2.2 then (H.2.1.val + 1) * s + q else H.2.1.val * s - 1 - q) := by
  obtain ⟨b, c, r⟩ := H
  have hc := c.isLt
  have hb := b.isLt
  have hks := hk_lt_s hd
  apply mkCell_val
  · rw [← hd.mul]; exact block_lt hb (by omega)
  · rw [← hd.mul]
    cases r
    · simp only [rowLen, Bool.false_eq_true, ite_false] at hq ⊢
      have := Nat.mul_le_mul_right s hc.le
      omega
    · simp only [rowLen, ite_true] at hq ⊢
      have := sub_mul_add (s := s) hc
      omega

/-- Coordinates of a column-half position: band and row offset. -/
theorem colCell_val (hd : HDims n k s) [NeZero n] (V : ColH k) {q : ℕ}
    (hq : q < colLen k s V) :
    (colCell (n := n) k s V q).2.val = V.1.val * s + V.2.1.val ∧
    ∃ band off, (colCell (n := n) k s V q).1.val = band * s + off ∧ band < k ∧ k ≤ off ∧
      off < s ∧
      (if V.2.2 then V.2.1.val < band ∧ q = (band - V.2.1.val - 1) * (s - k) + (off - k)
       else band < V.2.1.val ∧ q = (V.2.1.val - 1 - band) * (s - k) + (s - 1 - off)) := by
  obtain ⟨c, a, r⟩ := V
  have hc := c.isLt
  have ha := a.isLt
  have hks := hk_lt_s hd
  have hcol : c.val * s + a.val < n := by rw [← hd.mul]; exact block_lt hc (by omega)
  set m := s - k with hm_def
  have hmk : k + m = s := by omega
  have hm : 0 < m := by omega
  have hqd := Nat.div_add_mod' q m
  have hqm := Nat.mod_lt q hm
  cases r
  · simp only [colLen, Bool.false_eq_true, ite_false] at hq ⊢
    have h1 : q / m < a.val := div_lt_of_lt_mul' hq
    rw [show colCell (n := n) k s (c, a, false) q =
      mkCell n ((a.val - 1 - q / m) * s + (s - 1 - q % m)) (c.val * s + a.val) from rfl]
    generalize q / m = t at *
    generalize q % m = u at *
    have hrow : (a.val - 1 - t) * s + (s - 1 - u) < n := by
      rw [← hd.mul]; exact block_lt (by omega) (by omega)
    refine ⟨(mkCell_val hrow hcol).2, a.val - 1 - t, s - 1 - u,
      (mkCell_val hrow hcol).1, by omega, by omega, by omega, by omega, ?_⟩
    have e1 : a.val - 1 - (a.val - 1 - t) = t := by omega
    have e2 : s - 1 - (s - 1 - u) = u := by omega
    rw [e1, e2]; omega
  · simp only [colLen, ite_true] at hq ⊢
    have h1 : q / m < k - 1 - a.val := div_lt_of_lt_mul' hq
    rw [show colCell (n := n) k s (c, a, true) q =
      mkCell n ((a.val + 1 + q / m) * s + (k + q % m)) (c.val * s + a.val) from rfl]
    generalize q / m = t at *
    generalize q % m = u at *
    have hrow : (a.val + 1 + t) * s + (k + u) < n := by
      rw [← hd.mul]; exact block_lt (by omega) (by omega)
    refine ⟨(mkCell_val hrow hcol).2, a.val + 1 + t, k + u,
      (mkCell_val hrow hcol).1, by omega, by omega, by omega, by omega, ?_⟩
    have e1 : a.val + 1 + t - a.val - 1 = t := by omega
    have e2 : k + u - k = u := by omega
    rw [e1, e2]; omega

/-- A row-half position lies in the corridor rows, outside the landing strip. -/
theorem rowCell_facts (hd : HDims n k s) [NeZero n] (H : RowH k) {q : ℕ}
    (hq : q < rowLen k s H) :
    (rowCell (n := n) k s H q).1.val / s = H.1.val ∧
    (rowCell (n := n) k s H q).1.val % s = H.2.1.val ∧
    (rowCell (n := n) k s H q).2.val / s ≠ H.2.1.val := by
  have v := rowCell_val hd H hq
  have hks := hk_lt_s hd
  have hs := hs_pos hd
  have hc := H.2.1.isLt
  have hdm := divmod (b := H.1.val) (show H.2.1.val < s by omega)
  rw [v.1]
  refine ⟨hdm.1, hdm.2, fun he => ?_⟩
  have hb := div_eq_bounds hs he
  rw [v.2] at hb
  obtain ⟨b, c, r⟩ := H
  simp only [rowLen] at hq
  cases r
  · simp only [Bool.false_eq_true, ite_false] at hb hq
    omega
  · simp only [ite_true] at hb hq
    rw [Nat.succ_mul] at hb
    omega

/-- A column-half position lies below the row group, in a corridor column,
outside its own band. -/
theorem colCell_facts (hd : HDims n k s) [NeZero n] (V : ColH k) {q : ℕ}
    (hq : q < colLen k s V) :
    (colCell (n := n) k s V q).2.val / s = V.1.val ∧
    (colCell (n := n) k s V q).2.val % s = V.2.1.val ∧
    k ≤ (colCell (n := n) k s V q).1.val % s ∧
    (colCell (n := n) k s V q).1.val / s ≠ V.2.1.val := by
  obtain ⟨v2, band, off, v1, hband, hk, hoff, hq'⟩ := colCell_val hd V hq
  have hks := hk_lt_s hd
  have ha := V.2.1.isLt
  have hdm := divmod (b := V.1.val) (show V.2.1.val < s by omega)
  have hdm' := divmod (b := band) hoff
  rw [v2, v1]
  refine ⟨hdm.1, hdm.2, by rw [hdm'.2]; exact hk, ?_⟩
  rw [hdm'.1]
  split_ifs at hq' <;> omega

theorem rowCell_inj (hd : HDims n k s) [NeZero n] {H H' : RowH k} {q q' : ℕ}
    (hq : q < rowLen k s H) (hq' : q' < rowLen k s H')
    (h : rowCell (n := n) k s H q = rowCell k s H' q') : H = H' ∧ q = q' := by
  have v := rowCell_val hd H hq
  have v' := rowCell_val hd H' hq'
  have e1 := congrArg (fun x : Cell n => x.1.val) h
  have e2 := congrArg (fun x : Cell n => x.2.val) h
  rw [v.1, v'.1] at e1
  rw [v.2, v'.2] at e2
  have hks := hk_lt_s hd
  obtain ⟨b, c, r⟩ := H
  obtain ⟨b', c', r'⟩ := H'
  have hc := c.isLt
  have hc' := c'.isLt
  obtain ⟨hb, hcc⟩ := divmod_eq (by omega) (by omega) e1
  have hb' : b = b' := Fin.ext hb
  have hcc' : c = c' := Fin.ext hcc
  subst hb' hcc'
  simp only [rowLen] at hq hq'
  cases r <;> cases r' <;> dsimp only at e2 hq hq' <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, Nat.succ_mul] at e2 hq hq' <;>
    first | exact ⟨rfl, by omega⟩ | (exfalso; omega)

theorem colCell_inj (hd : HDims n k s) [NeZero n] {V V' : ColH k} {q q' : ℕ}
    (hq : q < colLen k s V) (hq' : q' < colLen k s V')
    (h : colCell (n := n) k s V q = colCell k s V' q') : V = V' ∧ q = q' := by
  obtain ⟨v2, band, off, v1, hband, hk, hoff, hf⟩ := colCell_val hd V hq
  obtain ⟨v2', band', off', v1', hband', hk', hoff', hf'⟩ := colCell_val hd V' hq'
  have e1 := congrArg (fun x : Cell n => x.1.val) h
  have e2 := congrArg (fun x : Cell n => x.2.val) h
  rw [v1, v1'] at e1
  rw [v2, v2'] at e2
  have hks := hk_lt_s hd
  obtain ⟨c, a, r⟩ := V
  obtain ⟨c', a', r'⟩ := V'
  have ha := a.isLt
  have ha' := a'.isLt
  obtain ⟨hcc, haa⟩ := divmod_eq (by omega) (by omega) e2
  obtain ⟨hbb, hoo⟩ := divmod_eq hoff hoff' e1
  have hcc' : c = c' := Fin.ext hcc
  have haa' : a = a' := Fin.ext haa
  subst hcc' haa' hbb hoo
  cases r <;> cases r' <;> dsimp only at hf hf' <;>
    simp only [Bool.false_eq_true, ite_false, ite_true] at hf hf' <;>
    first | exact ⟨rfl, by omega⟩ | (exfalso; omega)

/-- The cell is position `q < rowLen` of some row half. -/
def IsRowPos (k s : ℕ) [NeZero n] (x : Cell n) : Prop :=
  ∃ H : RowH k, ∃ q, q < rowLen k s H ∧ rowCell k s H q = x

/-- The cell is position `q < colLen` of some column half. -/
def IsColPos (k s : ℕ) [NeZero n] (x : Cell n) : Prop :=
  ∃ V : ColH k, ∃ q, q < colLen k s V ∧ colCell k s V q = x

theorem rowCell_eq (hd : HDims n k s) [NeZero n] (H : RowH k) {q : ℕ}
    (hq : q < rowLen k s H) {x : Cell n} (h1 : x.1.val = H.1.val * s + H.2.1.val)
    (h2 : x.2.val = if H.2.2 then (H.2.1.val + 1) * s + q else H.2.1.val * s - 1 - q) :
    rowCell k s H q = x := by
  have v := rowCell_val hd H hq
  exact Prod.ext (Fin.ext (v.1.trans h1.symm)) (Fin.ext (v.2.trans h2.symm))

/-- Every cell that is not a region cell is a row or column position. -/
theorem row_or_col_of_not_region (hd : HDims n k s) [NeZero n] (x : Cell n)
    (hreg : ¬ region k s (sqOf hd x) x) : IsRowPos k s x ∨ IsColPos k s x := by
  have hs := hs_pos hd
  have hks := hk_lt_s hd
  have hn : n = k * s := hd.mul.symm
  have hx1 := Nat.div_add_mod' x.1.val s
  have hx2 := Nat.div_add_mod' x.2.val s
  have hb := hd.div_lt x.1
  have hB := hd.div_lt x.2
  have hi := Nat.mod_lt x.1.val hs
  have hj := Nat.mod_lt x.2.val hs
  have hx2n := x.2.isLt
  have hreg' : ¬ (x.1.val % s = x.2.val / s ∨
      (k ≤ x.1.val % s ∧ (k ≤ x.2.val % s ∨ x.2.val % s = x.1.val / s))) :=
    fun h => hreg ⟨rfl, rfl, h⟩
  clear hreg
  generalize x.1.val / s = b at *
  generalize x.1.val % s = i at *
  generalize x.2.val / s = B at *
  generalize x.2.val % s = j at *
  by_cases hik : i < k
  · left
    by_cases hlt : i < B
    · have hle : (i + 1) * s ≤ B * s := Nat.mul_le_mul_right _ hlt
      have hsum := sub_mul_add (s := s) hik
      have hq : x.2.val - (i + 1) * s < (k - 1 - i) * s := by omega
      exact ⟨(⟨b, hb⟩, ⟨i, hik⟩, true), _, hq, rowCell_eq hd _ hq (by simp; omega)
        (by simp; omega)⟩
    · have hle : (B + 1) * s ≤ i * s := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.succ_mul] at hle
      have hq : i * s - 1 - x.2.val < i * s := by omega
      exact ⟨(⟨b, hb⟩, ⟨i, hik⟩, false), _, hq, rowCell_eq hd _ hq (by simp; omega)
        (by simp; omega)⟩
  · right
    have hjk : j < k := by omega
    have hjb : j ≠ b := by omega
    set m := s - k with hm_def
    have hmk : k + m = s := by omega
    by_cases hlow : j < b
    · have hle := Nat.mul_le_mul_right m (show b - j - 1 + 1 ≤ k - 1 - j by omega)
      rw [Nat.succ_mul] at hle
      have hq : (b - j - 1) * m + (i - k) < (k - 1 - j) * m := by omega
      have hq' : _ < colLen k s ((⟨B, hB⟩, ⟨j, hjk⟩, true) : ColH k) := hq
      refine ⟨_, _, hq', ?_⟩
      obtain ⟨v2, band, off, v1, hband, hk, hoff, hf⟩ := colCell_val hd _ hq'
      dsimp only at hf v2
      simp only [ite_true] at hf
      obtain ⟨e1, e2⟩ := divmod_eq (s := m) (by omega) (by omega) hf.2.symm
      have hbb : band = b := by omega
      subst hbb
      exact Prod.ext (Fin.ext (by rw [v1]; omega)) (Fin.ext (by rw [v2]; omega))
    · have hle := Nat.mul_le_mul_right m (show j - 1 - b + 1 ≤ j by omega)
      rw [Nat.succ_mul] at hle
      have hq : (j - 1 - b) * m + (s - 1 - i) < j * m := by omega
      have hq' : _ < colLen k s ((⟨B, hB⟩, ⟨j, hjk⟩, false) : ColH k) := hq
      refine ⟨_, _, hq', ?_⟩
      obtain ⟨v2, band, off, v1, hband, hk, hoff, hf⟩ := colCell_val hd _ hq'
      dsimp only at hf v2
      simp only [Bool.false_eq_true, ite_false] at hf
      obtain ⟨e1, e2⟩ := divmod_eq (s := m) (by omega) (by omega) hf.2.symm
      have hbb : band = b := by omega
      subst hbb
      exact Prod.ext (Fin.ext (by rw [v1]; omega)) (Fin.ext (by rw [v2]; omega))

theorem region_sqOf (hd : HDims n k s) {Q : Sq k} {x : Cell n} (h : region k s Q x) :
    sqOf hd x = Q :=
  Prod.ext (Fin.ext h.1) (Fin.ext h.2.1)

theorem region_not_row (hd : HDims n k s) [NeZero n] {Q : Sq k} {x : Cell n}
    (hr : region k s Q x) (hx : IsRowPos k s x) : False := by
  obtain ⟨H, q, hq, rfl⟩ := hx
  obtain ⟨f1, f2, f3⟩ := rowCell_facts hd H hq
  obtain ⟨-, r2, r3⟩ := hr
  have := H.2.1.isLt
  omega

theorem region_not_col (hd : HDims n k s) [NeZero n] {Q : Sq k} {x : Cell n}
    (hr : region k s Q x) (hx : IsColPos k s x) : False := by
  obtain ⟨V, q, hq, rfl⟩ := hx
  obtain ⟨f1, f2, f3, f4⟩ := colCell_facts hd V hq
  obtain ⟨r1, -, r3⟩ := hr
  have := V.2.1.isLt
  have := Q.2.isLt
  omega

theorem row_not_col (hd : HDims n k s) [NeZero n] {x : Cell n}
    (hr : IsRowPos k s x) (hc : IsColPos k s x) : False := by
  obtain ⟨H, q, hq, rfl⟩ := hr
  obtain ⟨V, q', hq', he⟩ := hc
  obtain ⟨-, f2, -⟩ := rowCell_facts hd H hq
  obtain ⟨-, -, g3, -⟩ := colCell_facts hd V hq'
  rw [he] at g3
  have := H.2.1.isLt
  omega

/-! ## Counting cells by kind -/

open Finset

theorem sum_region_card (hd : HDims n k s) (P : Cell n → Prop) [DecidablePred P] :
    ∑ Q : Sq k, #(univ.filter fun x => region k s Q x ∧ P x) =
      #(univ.filter fun x => region k s (sqOf hd x) x ∧ P x) := by
  rw [card_eq_sum_card_fiberwise (f := sqOf hd) (t := univ) (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun Q _ => ?_
  rw [filter_filter]
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hr, hp⟩
    have he := region_sqOf hd hr
    exact ⟨⟨he ▸ hr, hp⟩, he⟩
  · rintro ⟨⟨hr, hp⟩, he⟩
    exact ⟨he ▸ hr, hp⟩

open Classical in
theorem sum_row_card (hd : HDims n k s) [NeZero n] (P : Cell n → Prop) [DecidablePred P] :
    ∑ H : RowH k, #((range (rowLen k s H)).filter fun q => P (rowCell k s H q)) =
      #(univ.filter fun x => IsRowPos k s x ∧ P x) := by
  rw [← card_sigma]
  apply card_bij (fun p _ => rowCell (n := n) k s p.1 p.2)
  · rintro ⟨H, q⟩ hp
    simp only [mem_sigma, mem_univ, true_and, mem_filter, mem_range] at hp ⊢
    exact ⟨⟨H, q, hp.1, rfl⟩, hp.2⟩
  · rintro ⟨H, q⟩ hp ⟨H', q'⟩ hp' he
    simp only [mem_sigma, mem_univ, true_and, mem_filter, mem_range] at hp hp'
    obtain ⟨rfl, rfl⟩ := rowCell_inj hd hp.1 hp'.1 he
    rfl
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    obtain ⟨⟨H, q, hq, rfl⟩, hp⟩ := hx
    exact ⟨⟨H, q⟩, by simp [hq, hp], rfl⟩

open Classical in
theorem sum_col_card (hd : HDims n k s) [NeZero n] (P : Cell n → Prop) [DecidablePred P] :
    ∑ V : ColH k, #((range (colLen k s V)).filter fun q => P (colCell k s V q)) =
      #(univ.filter fun x => IsColPos k s x ∧ P x) := by
  rw [← card_sigma]
  apply card_bij (fun p _ => colCell (n := n) k s p.1 p.2)
  · rintro ⟨V, q⟩ hp
    simp only [mem_sigma, mem_univ, true_and, mem_filter, mem_range] at hp ⊢
    exact ⟨⟨V, q, hp.1, rfl⟩, hp.2⟩
  · rintro ⟨V, q⟩ hp ⟨V', q'⟩ hp' he
    simp only [mem_sigma, mem_univ, true_and, mem_filter, mem_range] at hp hp'
    obtain ⟨rfl, rfl⟩ := colCell_inj hd hp.1 hp'.1 he
    rfl
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    obtain ⟨⟨V, q, hq, rfl⟩, hp⟩ := hx
    exact ⟨⟨V, q⟩, by simp [hq, hp], rfl⟩

open Classical in
theorem card_kinds (hd : HDims n k s) [NeZero n] (P : Cell n → Prop) [DecidablePred P] :
    #(univ.filter fun x => region k s (sqOf hd x) x ∧ P x) +
    #(univ.filter fun x => IsRowPos k s x ∧ P x) +
    #(univ.filter fun x => IsColPos k s x ∧ P x) = #(univ.filter P) := by
  rw [← card_union_of_disjoint, ← card_union_of_disjoint]
  · congr 1
    ext x
    simp only [mem_union, mem_filter, mem_univ, true_and]
    constructor
    · rintro ((⟨_, h⟩ | ⟨_, h⟩) | ⟨_, h⟩) <;> exact h
    · intro h
      by_cases hr : region k s (sqOf hd x) x
      · exact Or.inl (Or.inl ⟨hr, h⟩)
      · rcases row_or_col_of_not_region hd x hr with h' | h'
        · exact Or.inl (Or.inr ⟨h', h⟩)
        · exact Or.inr ⟨h', h⟩
  · rw [disjoint_union_left]
    constructor
    · exact disjoint_filter.mpr fun x _ h1 h2 => region_not_col hd h1.1 h2.1
    · exact disjoint_filter.mpr fun x _ h1 h2 => row_not_col hd h1.1 h2.1
  · exact disjoint_filter.mpr fun x _ h1 h2 => region_not_row hd h1.1 h2.1

/-- Counting any set of cells by regions, row positions and column positions. -/
theorem count_decomp (hd : HDims n k s) [NeZero n] (P : Cell n → Prop) [DecidablePred P] :
    (∑ Q : Sq k, #(univ.filter fun x => region k s Q x ∧ P x)) +
    (∑ H : RowH k, #((range (rowLen k s H)).filter fun q => P (rowCell k s H q))) +
    (∑ V : ColH k, #((range (colLen k s V)).filter fun q => P (colCell k s V q))) =
      #(univ.filter P) := by
  rw [sum_region_card hd, sum_row_card hd, sum_col_card hd, card_kinds hd]

/-! ## Counting inside one square -/

/-- Cells of a square correspond to offset pairs. -/
theorem card_square (hd : HDims n k s) (Q : Sq k) (R : ℕ → ℕ → Prop)
    [∀ i j, Decidable (R i j)] :
    #(univ.filter fun x : Cell n => x.1.val / s = Q.1.val ∧ x.2.val / s = Q.2.val ∧
      R (x.1.val % s) (x.2.val % s)) =
      #((range s ×ˢ range s).filter fun p => R p.1 p.2) := by
  have hs := hs_pos hd
  apply card_bij (fun x _ => (x.1.val % s, x.2.val % s))
  · intro x hx
    simp only [mem_filter, mem_univ, true_and, mem_product, mem_range] at hx ⊢
    exact ⟨⟨Nat.mod_lt _ hs, Nat.mod_lt _ hs⟩, hx.2.2⟩
  · intro x hx y hy he
    simp only [mem_filter, mem_univ, true_and, Prod.mk.injEq] at hx hy he
    have h1 := Nat.div_add_mod' x.1.val s
    have h2 := Nat.div_add_mod' x.2.val s
    have h3 := Nat.div_add_mod' y.1.val s
    have h4 := Nat.div_add_mod' y.2.val s
    rw [hx.1, he.1] at h1
    rw [hx.2.1, he.2] at h2
    rw [hy.1] at h3
    rw [hy.2.1] at h4
    exact Prod.ext (Fin.ext (h1.symm.trans h3)) (Fin.ext (h2.symm.trans h4))
  · rintro ⟨i, j⟩ hp
    simp only [mem_filter, mem_product, mem_range] at hp
    have hi : Q.1.val * s + i < n := by rw [← hd.mul]; exact block_lt Q.1.isLt hp.1.1
    have hj : Q.2.val * s + j < n := by rw [← hd.mul]; exact block_lt Q.2.isLt hp.1.2
    have d1 := divmod (b := Q.1.val) hp.1.1
    have d2 := divmod (b := Q.2.val) hp.1.2
    refine ⟨(⟨_, hi⟩, ⟨_, hj⟩), ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      rw [d1.1, d2.1, d1.2, d2.2]
      exact ⟨rfl, rfl, hp.2⟩
    · simp only [d1.2, d2.2]

theorem regionSize_eq (hks : k ≤ s) (hk : 1 ≤ k) :
    s + (s - k) * (s - k + 1) = regionSize k s := by
  obtain ⟨m, rfl⟩ : ∃ m, s = k + m := ⟨s - k, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  unfold regionSize sqCorridor
  have e1 : j + 1 + m - (j + 1) = m := by omega
  have e2 : j + 1 - 1 = j := by omega
  rw [e1, e2]
  have e3 : (j + 1 + m) ^ 2 = (j * (j + 1 + m) + j * m) + ((j + 1 + m) + m * (m + 1)) := by ring
  rw [e3]
  omega

theorem card_region (hd : HDims n k s) (Q : Sq k) :
    #(univ.filter fun x : Cell n => region k s Q x) = regionSize k s := by
  have hks := hk_lt_s hd
  have hk := hd.two_le
  have hQ1 := Q.1.isLt
  have hQ2 := Q.2.isLt
  rw [← regionSize_eq hks.le (by omega)]
  have h := card_square hd Q (fun i j => i = Q.2.val ∨ (k ≤ i ∧ (k ≤ j ∨ j = Q.1.val)))
  refine (Eq.trans ?_ h).trans ?_
  · rfl
  have he : ((range s ×ˢ range s).filter fun p : ℕ × ℕ =>
      p.1 = Q.2.val ∨ (k ≤ p.1 ∧ (k ≤ p.2 ∨ p.2 = Q.1.val))) =
      ({Q.2.val} ×ˢ range s) ∪ (Ico k s ×ˢ insert Q.1.val (Ico k s)) := by
    ext ⟨i, j⟩
    simp only [mem_filter, mem_product, mem_range, mem_union, mem_singleton, mem_Ico,
      mem_insert]
    omega
  rw [he, card_union_of_disjoint, card_product, card_product, card_singleton, card_range,
    card_insert_of_notMem, Nat.card_Ico]
  · ring
  · simp only [mem_Ico]; omega
  · rw [disjoint_left]
    rintro ⟨i, j⟩ h1 h2
    simp only [mem_product, mem_singleton, mem_Ico] at h1 h2
    omega

theorem card_sqOf (hd : HDims n k s) (y : Sq k) :
    #(univ.filter fun z : Cell n => sqOf hd z = y) = s ^ 2 := by
  have h := card_square hd y (fun _ _ => True)
  rw [filter_true_of_mem (fun _ _ => trivial), card_product, card_range] at h
  rw [sq, ← h]
  congr 1
  ext z
  simp only [mem_filter, mem_univ, true_and, and_true, sqOf, Prod.ext_iff, Fin.ext_iff]

theorem val_ne_zero_of_ne_blank [NeZero n] {B : Board n} {x : Cell n} (h : x ≠ blank B) :
    (B x).val ≠ 0 := by
  intro h0
  apply h
  have hx : B x = 0 := Fin.ext h0
  unfold blank position
  rw [← hx, Equiv.symm_apply_apply]

theorem eq_blank_of_val_eq_zero [NeZero n] {B : Board n} {x : Cell n} (h : (B x).val = 0) :
    x = blank B := by
  by_contra hne
  exact val_ne_zero_of_ne_blank hne h

theorem isLast_iff (hd : HDims n k s) [NeZero n] (y : Sq k) :
    IsLast y ↔ sqOf hd (blank (target n)) = y := by
  rw [blank_target_eq]
  have hs := hs_pos hd
  have hk := hd.two_le
  have he : n - 1 = (k - 1) * s + (s - 1) := by
    rw [← hd.mul]
    have : (k - 1) * s + s = k * s := by
      rw [← Nat.succ_mul]; congr 1; omega
    omega
  have d := divmod (b := k - 1) (show s - 1 < s by omega)
  rw [← he] at d
  simp only [IsLast, sqOf, Prod.ext_iff, Fin.ext_iff, d.1]
  tauto

/-- Class `y` has `s²` nonblank tiles, one fewer for the last class. -/
theorem card_class (hd : HDims n k s) [NeZero n] (B : Board n) (y : Sq k) :
    #(univ.filter fun x => (B x).val ≠ 0 ∧ classOf hd (B x) = y) =
      s ^ 2 - if IsLast y then 1 else 0 := by
  have step1 : #(univ.filter fun x => (B x).val ≠ 0 ∧ classOf hd (B x) = y) =
      #(univ.filter fun z : Cell n => (target n z).val ≠ 0 ∧ sqOf hd z = y) := by
    apply card_bij (fun x _ => position (target n) (B x))
    · intro x hx
      simp only [mem_filter, mem_univ, true_and, position, Equiv.apply_symm_apply] at hx ⊢
      exact hx
    · intro x _ x' _ he
      exact B.injective ((target n).symm.injective he)
    · intro z hz
      refine ⟨B.symm (target n z), ?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and, Equiv.apply_symm_apply] at hz ⊢
        refine ⟨hz.1, ?_⟩
        simp only [classOf, position, Equiv.symm_apply_apply]
        exact hz.2
      · simp [position]
  rw [step1, ← card_sqOf hd y]
  rw [← card_filter_add_card_filter_not (s := univ.filter fun z : Cell n => sqOf hd z = y)
    (fun z => (target n z).val ≠ 0), filter_filter, filter_filter]
  have e2 : (univ.filter fun z : Cell n => sqOf hd z = y ∧ ¬ (target n z).val ≠ 0) =
      if IsLast y then {blank (target n)} else ∅ := by
    ext z
    simp only [mem_filter, mem_univ, true_and, not_not]
    constructor
    · rintro ⟨h1, h2⟩
      have hz := eq_blank_of_val_eq_zero h2
      subst hz
      rw [if_pos ((isLast_iff hd y).mpr h1)]
      exact mem_singleton_self _
    · intro h
      split_ifs at h with hy
      · rw [mem_singleton] at h
        subst h
        refine ⟨(isLast_iff hd y).mp hy, ?_⟩
        simp [blank, position]
      · simp at h
  rw [e2]
  have e1 : (univ.filter fun z : Cell n => sqOf hd z = y ∧ (target n z).val ≠ 0) =
      (univ.filter fun z : Cell n => (target n z).val ≠ 0 ∧ sqOf hd z = y) := by
    ext z; simp only [mem_filter, mem_univ, true_and]; tauto
  rw [e1]
  split_ifs <;> simp

theorem rowCell_nonblank (hd : HDims n k s) [NeZero n] {B : Board n}
    (hb : reservoir k s (sqOf hd (blank B)) (blank B)) (H : RowH k) {q : ℕ}
    (hq : q < rowLen k s H) : (B (rowCell k s H q)).val ≠ 0 := by
  refine val_ne_zero_of_ne_blank fun he => ?_
  have f := (rowCell_facts hd H hq).2.1
  rw [he] at f
  have := hb.2.2.1
  have := H.2.1.isLt
  omega

theorem colCell_nonblank (hd : HDims n k s) [NeZero n] {B : Board n}
    (hb : reservoir k s (sqOf hd (blank B)) (blank B)) (V : ColH k) {q : ℕ}
    (hq : q < colLen k s V) : (B (colCell k s V q)).val ≠ 0 := by
  refine val_ne_zero_of_ne_blank fun he => ?_
  have f := (colCell_facts hd V hq).2.1
  rw [he] at f
  have := hb.2.2.2
  have := V.2.1.isLt
  omega

theorem sum_rowLen : ∑ H : RowH k, rowLen k s H = k * (k * ((k - 1) * s)) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, rowLen, ite_true, Bool.false_eq_true,
    ite_false]
  have e : ∀ c : Fin k, (k - 1 - c.val) * s + c.val * s = (k - 1) * s := by
    intro c; rw [← Nat.add_mul]; congr 1; have := c.isLt; omega
  simp only [e, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

theorem sum_colLen : ∑ V : ColH k, colLen k s V = k * (k * ((k - 1) * (s - k))) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, colLen, ite_true, Bool.false_eq_true,
    ite_false]
  have e : ∀ c : Fin k, (k - 1 - c.val) * (s - k) + c.val * (s - k) = (k - 1) * (s - k) := by
    intro c; rw [← Nat.add_mul]; congr 1; have := c.isLt; omega
  simp only [e, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

theorem sum_corridor : (∑ H : RowH k, rowLen k s H) + (∑ V : ColH k, colLen k s V) =
    k ^ 2 * sqCorridor k s := by
  rw [sum_rowLen, sum_colLen, sqCorridor]; ring

end LayoutFacts

open Finset LayoutAux LayoutFacts

/-! ## Facts about the layout -/

/-- A board with its blank in a reservoir realizes its own abstraction. -/
theorem rel_absState (hd : HDims n k s) [NeZero n] (B : Board n)
    (hb : reservoir k s (sqOf hd (blank B)) (blank B)) : Rel hd B (absState hd B) :=
  ⟨fun H _ hq => ⟨rowCell_nonblank hd hb H hq, rfl⟩,
    fun V _ hq => ⟨colCell_nonblank hd hb V hq, rfl⟩, fun _ _ => rfl, hb⟩

theorem LayoutFacts.reservoir_region {Q : Sq k} {x : Cell n} (h : reservoir k s Q x) : region k s Q x :=
  ⟨h.1, h.2.1, Or.inr ⟨h.2.2.1, Or.inl h.2.2.2⟩⟩

/-- Every region has `regionSize` cells, one of them possibly the blank. -/
theorem absState_regionTotal (hd : HDims n k s) [NeZero n] (B : Board n)
    (hb : reservoir k s (sqOf hd (blank B)) (blank B)) (Q : Sq k) :
    (∑ y, (absState hd B).cnt Q y) + (if (absState hd B).blank = Q then 1 else 0) =
      regionSize k s := by
  show (∑ y, regionCount hd B Q y) + (if sqOf hd (blank B) = Q then 1 else 0) = _
  have h1 : ∑ y, regionCount hd B Q y =
      #(univ.filter fun x => region k s Q x ∧ (B x).val ≠ 0) := by
    rw [card_eq_sum_card_fiberwise (f := fun x => classOf hd (B x)) (t := univ)
      (fun _ _ => mem_univ _)]
    refine sum_congr rfl fun y _ => ?_
    unfold regionCount
    rw [filter_filter]
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    tauto
  have h2 := card_filter_add_card_filter_not (s := univ.filter fun x : Cell n => region k s Q x)
    (fun x => (B x).val ≠ 0)
  rw [filter_filter, filter_filter, card_region hd] at h2
  have h3 : #(univ.filter fun x => region k s Q x ∧ ¬ (B x).val ≠ 0) =
      if sqOf hd (blank B) = Q then 1 else 0 := by
    split_ifs with hQ
    · rw [card_eq_one]
      refine ⟨blank B, ?_⟩
      ext x
      simp only [mem_filter, mem_univ, true_and, not_not, mem_singleton]
      constructor
      · rintro ⟨-, h⟩
        exact eq_blank_of_val_eq_zero h
      · rintro rfl
        refine ⟨reservoir_region (hQ ▸ hb), ?_⟩
        simp [blank, position]
    · rw [card_eq_zero, filter_eq_empty_iff]
      rintro x - ⟨hr, h⟩
      have hx := eq_blank_of_val_eq_zero (not_not.mp h)
      subst hx
      exact hQ (region_sqOf hd hr)
  rw [h1, ← h3, h2]

/-- Every class has `s²` tiles, the last one `s² - 1` besides the blank. -/
theorem absState_classTotal (hd : HDims n k s) [NeZero n] (B : Board n)
    (hb : reservoir k s (sqOf hd (blank B)) (blank B)) (y : Sq k) :
    (∑ Q, (absState hd B).cnt Q y) + (absState hd B).corrCount s y =
      s ^ 2 - (if IsLast y then 1 else 0) := by
  have hc := count_decomp hd (fun x => (B x).val ≠ 0 ∧ classOf hd (B x) = y)
  rw [card_class hd B y] at hc
  rw [← hc, add_assoc]
  congr 1
  unfold IState.corrCount
  congr 1
  · refine sum_congr rfl fun H _ => ?_
    congr 1
    refine filter_congr fun q hq => ?_
    have := rowCell_nonblank hd hb H (mem_range.mp hq)
    simp only [absState]
    tauto
  · refine sum_congr rfl fun V _ => ?_
    congr 1
    refine filter_congr fun q hq => ?_
    have := colCell_nonblank hd hb V (mem_range.mp hq)
    simp only [absState]
    tauto

/-- Misplaced tiles lie in corridors or are counted by `offCount`. -/
theorem misplaced_le_of_rel (hd : HDims n k s) [NeZero n] {B : Board n} {σ : IState k}
    (hR : Rel hd B σ) : misplaced hd B ≤ k ^ 2 * sqCorridor k s + σ.offCount := by
  have hc := count_decomp hd (fun x => (B x).val ≠ 0 ∧ classOf hd (B x) ≠ sqOf hd x)
  have hm : misplaced hd B =
      #(univ.filter fun x => (B x).val ≠ 0 ∧ classOf hd (B x) ≠ sqOf hd x) := rfl
  have hreg : ∀ Q : Sq k,
      #(univ.filter fun x => region k s Q x ∧ ((B x).val ≠ 0 ∧ classOf hd (B x) ≠ sqOf hd x)) =
        ∑ y : Sq k, if y = Q then 0 else σ.cnt Q y := by
    intro Q
    rw [card_eq_sum_card_fiberwise (f := fun x => classOf hd (B x)) (t := univ)
      (fun _ _ => mem_univ _)]
    refine sum_congr rfl fun y _ => ?_
    rw [filter_filter]
    split_ifs with hyQ
    · rw [card_eq_zero, filter_eq_empty_iff]
      rintro x - ⟨⟨hr, -, hne⟩, he⟩
      exact hne (he.trans (hyQ.trans (region_sqOf hd hr).symm))
    · rw [← hR.2.2.1 Q y]
      unfold regionCount
      congr 1
      ext x
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨⟨hr, h0, -⟩, he⟩
        exact ⟨hr, h0, he⟩
      · rintro ⟨hr, h0, he⟩
        refine ⟨⟨hr, h0, ?_⟩, he⟩
        rw [he, region_sqOf hd hr]
        exact hyQ
  have hrow : (∑ H : RowH k, #((range (rowLen k s H)).filter fun q =>
      (B (rowCell k s H q)).val ≠ 0 ∧ classOf hd (B (rowCell k s H q)) ≠
        sqOf hd (rowCell k s H q))) ≤ ∑ H : RowH k, rowLen k s H :=
    sum_le_sum fun H _ => (card_filter_le _ _).trans (card_range _).le
  have hcol : (∑ V : ColH k, #((range (colLen k s V)).filter fun q =>
      (B (colCell k s V q)).val ≠ 0 ∧ classOf hd (B (colCell k s V q)) ≠
        sqOf hd (colCell k s V q))) ≤ ∑ V : ColH k, colLen k s V :=
    sum_le_sum fun V _ => (card_filter_le _ _).trans (card_range _).le
  have hsum := sum_corridor (k := k) (s := s)
  simp only [hreg] at hc
  have hoff : σ.offCount = ∑ Q : Sq k, ∑ y : Sq k, if y = Q then 0 else σ.cnt Q y := rfl
  omega

/-- The blank can be brought into a reservoir cheaply. -/
theorem exists_normalize (hd : HDims n k s) [NeZero n] (B : Board n) :
    ∃ C : Board n, ∃ p : Path B C,
      reservoir k s (sqOf hd (blank C)) (blank C) ∧ p.inefficientMoves ≤ 2 * n := by
  have hs := hs_pos hd
  have hks := hk_lt_s hd
  set x := blank B
  have hb1 := hd.div_lt x.1
  have hb2 := hd.div_lt x.2
  have c1 : x.1.val / s * s + (s - 1) < n :=
    (block_lt hb1 (show s - 1 < s by omega)).trans_eq hd.mul
  have c2 : x.2.val / s * s + (s - 1) < n :=
    (block_lt hb2 (show s - 1 < s by omega)).trans_eq hd.mul
  obtain ⟨C, p, hC, hp, -⟩ := exists_blank_access_path_preserving B (⟨_, c1⟩, ⟨_, c2⟩)
  have d1 := divmod (b := x.1.val / s) (show s - 1 < s by omega)
  have d2 := divmod (b := x.2.val / s) (show s - 1 < s by omega)
  refine ⟨C, p, ?_, p.inefficientMoves_le_length.trans (hp.trans ?_)⟩
  · rw [hC]
    refine ⟨rfl, rfl, ?_, ?_⟩
    · show k ≤ (x.1.val / s * s + (s - 1)) % s
      rw [d1.2]; omega
    · show k ≤ (x.2.val / s * s + (s - 1)) % s
      rw [d2.2]; omega
  · have e1 := div_eq_bounds hs (rfl : x.1.val / s = _)
    have e2 := div_eq_bounds hs (rfl : x.2.val / s = _)
    have hsn : s ≤ n := by
      rw [← hd.mul]; exact Nat.le_mul_of_pos_left s (by have := hd.two_le; omega)
    simp only [gridDistance, Nat.dist]
    omega

end SlidingPuzzle.Hub
