import SlidingPuzzle.Tree.Geom

/-! # Regions, keys and counting cells in the tree layout -/
namespace SlidingPuzzle.Tree

open SlidingPuzzle.Hub (Sq HDims sqOf classOf mkCell reservoir mkCell_fst mkCell_snd
  div_eq_iff_bounds band_lt_band cell_ext misplaced)
open SlidingPuzzle.Hub.LayoutAux
open Finset

variable {n k s q : ℕ} (L : LaneSys k q)

theorem region_sqOf (hd : HDims n k s) {Q : Sq k} {x : Cell n} (h : region L s Q x) :
    sqOf hd x = Q :=
  Prod.ext (Fin.ext h.1) (Fin.ext h.2.1)

theorem key_eq_some (hd : HDims n k s) {x : Cell n} {Q : Sq k} :
    key L hd x = some Q ↔ region L s Q x := by
  unfold key
  constructor
  · intro h
    split_ifs at h with hr
    · cases h; exact hr
  · intro h
    rw [region_sqOf L hd h, if_pos h]

theorem key_eq_none (hd : HDims n k s) {x : Cell n} :
    key L hd x = none ↔ LaneCell L s x := by
  unfold key
  constructor
  · intro h
    split_ifs at h with hr
    by_contra hl
    exact hr ⟨rfl, rfl, hl⟩
  · intro h
    rw [if_neg (fun hr => hr.2.2 h)]

theorem ne_of_key {hd : HDims n k s} {x y : Cell n} (h : key L hd x ≠ key L hd y) : x ≠ y :=
  fun e => h (by rw [e])

theorem region_of_reservoir (td : TDims n k s q) {Q : Sq k} {x : Cell n}
    (h : reservoir k s Q x) : region L s Q x := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, ?_⟩
  have := td.q_le
  rintro (⟨hq, -⟩ | ⟨-, hq, -⟩) <;> omega

theorem key_reservoir (td : TDims n k s q) {Q : Sq k} {x : Cell n} (h : reservoir k s Q x) :
    key L td.hd x = some Q := (key_eq_some L td.hd).mpr (region_of_reservoir L td h)

theorem key_rowCell [NeZero n] (td : TDims n k s q) (H : LaneI k q) (p : ℕ)
    (hp : p < rowLen L s H) : key L td.hd (rowCell (n := n) s H p) = none :=
  (key_eq_none L td.hd).mpr (rowCell_lane L td H p hp)

theorem key_colCell [NeZero n] (td : TDims n k s q) (V : LaneI k q) (p : ℕ)
    (hp : p < colLen L s V) : key L td.hd (colCell (n := n) s V p) = none :=
  (key_eq_none L td.hd).mpr (colCell_lane L td V p hp)

theorem region_coords {Q : Sq k} {x : Cell n} {β o γ o' : ℕ} (hs : 0 < s)
    (h1 : x.1.val = β * s + o) (h2 : x.2.val = γ * s + o') (ho : o < s) (ho' : o' < s) :
    region L s Q x ↔ β = Q.1.val ∧ γ = Q.2.val ∧
      ¬ ((∃ h : o < q, Covered L ⟨o, h⟩ γ) ∨ (q ≤ o ∧ ∃ h : o' < q, Covered L ⟨o', h⟩ β)) := by
  unfold region LaneCell
  have d1 := divmod (b := β) ho
  have d2 := divmod (b := γ) ho'
  rw [h1, h2, d1.1, d1.2, d2.1, d2.2]

/-- A cell of the landing strip of a nonempty row lane is in the landing region. -/
theorem region_strip (td : TDims n k s q) (H : LaneI k q) (hpos : 0 < blen L H)
    {x : Cell n} {o' : ℕ} (h1 : x.1.val = H.b.val * s + H.o.val)
    (h2 : x.2.val = H.t.val * s + o') (ho' : o' < s) : region L s (rowLand H) x := by
  have hqs := td.q_lt_s
  have hq := H.o.isLt
  rw [region_coords L td.s_pos h1 h2 (by omega) ho']
  refine ⟨rfl, rfl, ?_⟩
  rintro (⟨h, t', side', hin⟩ | ⟨h, -⟩)
  · exact L.avoid H.o H.t t' H.side side' hpos hin
  · omega

/-- A cell of the own column piece of a nonempty column lane (row offset
`≥ q`) is in the landing region. -/
theorem region_ownCol (td : TDims n k s q) (V : LaneI k q) (hpos : 0 < blen L V)
    {x : Cell n} {o : ℕ} (h1 : x.1.val = V.t.val * s + o) (ho : q ≤ o) (ho' : o < s)
    (h2 : x.2.val = V.b.val * s + V.o.val) : region L s (colLand V) x := by
  have hqs := td.q_lt_s
  have hq := V.o.isLt
  rw [region_coords L td.s_pos h1 h2 ho' (by omega)]
  refine ⟨rfl, rfl, ?_⟩
  rintro (⟨h, -⟩ | ⟨-, h, t', side', hin⟩)
  · omega
  · exact L.avoid V.o V.t t' V.side side' hpos hin

/-! ## Decoding lane cells -/

section decode
variable [NeZero n]

/-- The cell is a row-lane position. -/
def IsRowPos (s : ℕ) (x : Cell n) : Prop :=
  ∃ H : LaneI k q, ∃ p, p < rowLen L s H ∧ rowCell s H p = x

/-- The cell is a column-lane position. -/
def IsColPos (s : ℕ) (x : Cell n) : Prop :=
  ∃ V : LaneI k q, ∃ p, p < colLen L s V ∧ colCell s V p = x

theorem row_or_col_of_lane (td : TDims n k s q) (x : Cell n) (hx : LaneCell L s x) :
    IsRowPos L s x ∨ IsColPos L s x := by
  have hs := td.s_pos
  have hqs := td.q_lt_s
  have hx1 := Nat.div_add_mod' x.1.val s
  have hx2 := Nat.div_add_mod' x.2.val s
  have hb := td.hd.div_lt x.1
  have hB := td.hd.div_lt x.2
  have hi := Nat.mod_lt x.1.val hs
  have hj := Nat.mod_lt x.2.val hs
  rcases hx with ⟨hiq, t, side, hin⟩ | ⟨hiq, hjq, t, side, hin⟩
  · left
    set H : LaneI k q := ⟨⟨_, hb⟩, ⟨_, hiq⟩, t, side⟩
    have hbl : blen L H = L.len ⟨_, hiq⟩ t side := rfl
    have hr : (rowCell (n := n) s H 0).1.val = x.1.val := by
      rw [rowCell_fst td]; simp only [H]; omega
    cases side
    · simp only [InPiece, Bool.false_eq_true, if_false] at hin
      have e1 : (x.2.val / s + 1) * s ≤ t.val * s := Nat.mul_le_mul_right s hin.1
      have e2 : t.val * s ≤ (x.2.val / s + L.len ⟨_, hiq⟩ t false) * s :=
        Nat.mul_le_mul_right s hin.2
      rw [add_mul, one_mul] at e1
      rw [add_mul] at e2
      have hp : t.val * s - 1 - x.2.val < rowLen L s H := by
        unfold rowLen; rw [hbl]; omega
      refine ⟨H, _, hp, cell_ext (by rw [rowCell_fst td]; simp only [H]; omega) ?_⟩
      rw [rowCell_snd L td H _ hp]; unfold rowCol; simp only [H, Bool.false_eq_true, if_false]
      omega
    · simp only [InPiece, if_true] at hin
      have e1 : (t.val + 1) * s ≤ x.2.val / s * s := Nat.mul_le_mul_right s hin.1
      have e2 : x.2.val / s * s ≤ (t.val + L.len ⟨_, hiq⟩ t true) * s :=
        Nat.mul_le_mul_right s hin.2
      rw [add_mul, one_mul] at e1
      rw [add_mul] at e2
      have hp : x.2.val - (t.val + 1) * s < rowLen L s H := by
        unfold rowLen; rw [hbl, add_mul, one_mul]; omega
      refine ⟨H, _, hp, cell_ext (by rw [rowCell_fst td]; simp only [H]; omega) ?_⟩
      rw [rowCell_snd L td H _ hp]; unfold rowCol; simp only [H, if_true]
      rw [add_mul, one_mul] at hp ⊢
      omega
  · right
    set V : LaneI k q := ⟨⟨_, hB⟩, ⟨_, hjq⟩, t, side⟩
    have hbl : blen L V = L.len ⟨_, hjq⟩ t side := rfl
    set m := s - q with hm_def
    have hm : 0 < m := by omega
    have hsnd : (colCell (n := n) s V 0).2.val = x.2.val := by
      rw [colCell_snd td]; simp only [V]; omega
    cases side
    · simp only [InPiece, Bool.false_eq_true, if_false] at hin
      have hp : (t.val - 1 - x.1.val / s) * m + (s - 1 - x.1.val % s) < colLen L s V := by
        unfold colLen; rw [hbl, ← hm_def]
        have := Nat.mul_le_mul_right m (show t.val - 1 - x.1.val / s + 1 ≤
          L.len ⟨_, hjq⟩ t false by omega)
        rw [add_mul, one_mul] at this
        omega
      refine ⟨V, _, hp, cell_ext ?_ (by rw [colCell_snd td]; simp only [V]; omega)⟩
      rw [colCell_fst L td V _ hp]
      have d := divmod (b := t.val - 1 - x.1.val / s) (show s - 1 - x.1.val % s < m by omega)
      unfold cBand cOff
      simp only [V, Bool.false_eq_true, if_false, ← hm_def, d.1, d.2]
      have : t.val - 1 - (t.val - 1 - x.1.val / s) = x.1.val / s := by
        clear * - hin; generalize x.1.val / s = β at *; omega
      rw [this]
      omega
    · simp only [InPiece, if_true] at hin
      have hp : (x.1.val / s - t.val - 1) * m + (x.1.val % s - q) < colLen L s V := by
        unfold colLen; rw [hbl, ← hm_def]
        have := Nat.mul_le_mul_right m (show x.1.val / s - t.val - 1 + 1 ≤
          L.len ⟨_, hjq⟩ t true by omega)
        rw [add_mul, one_mul] at this
        omega
      refine ⟨V, _, hp, cell_ext ?_ (by rw [colCell_snd td]; simp only [V]; omega)⟩
      rw [colCell_fst L td V _ hp]
      have d := divmod (b := x.1.val / s - t.val - 1) (show x.1.val % s - q < m by omega)
      unfold cBand cOff
      simp only [V, if_true, ← hm_def, d.1, d.2]
      have : t.val + 1 + (x.1.val / s - t.val - 1) = x.1.val / s := by
        clear * - hin; generalize x.1.val / s = β at *; omega
      rw [this]
      omega

theorem lane_of_rowPos (td : TDims n k s q) {x : Cell n} (h : IsRowPos L s x) : LaneCell L s x := by
  obtain ⟨H, p, hp, rfl⟩ := h
  exact rowCell_lane L td H p hp

theorem lane_of_colPos (td : TDims n k s q) {x : Cell n} (h : IsColPos L s x) : LaneCell L s x := by
  obtain ⟨V, p, hp, rfl⟩ := h
  exact colCell_lane L td V p hp

theorem row_not_col (td : TDims n k s q) {x : Cell n} (hr : IsRowPos L s x)
    (hc : IsColPos L s x) : False := by
  obtain ⟨H, p, -, rfl⟩ := hr
  obtain ⟨V, p', hp', he⟩ := hc
  exact rowCell_ne_colCell L td H V p p' hp' he.symm

/-! ## Counting cells by kind -/

theorem sum_region_card (hd : HDims n k s) (P : Cell n → Prop) [DecidablePred P] :
    ∑ Q : Sq k, #(univ.filter fun x => region L s Q x ∧ P x) =
      #(univ.filter fun x => region L s (sqOf hd x) x ∧ P x) := by
  classical
  rw [card_eq_sum_card_fiberwise (f := sqOf hd) (t := univ) (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun Q _ => ?_
  rw [filter_filter]
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hr, hp⟩
    have he := region_sqOf L hd hr
    exact ⟨⟨he ▸ hr, hp⟩, he⟩
  · rintro ⟨⟨hr, hp⟩, he⟩
    exact ⟨he ▸ hr, hp⟩

open Classical in
theorem sum_row_card (td : TDims n k s q) (P : Cell n → Prop) [DecidablePred P] :
    ∑ H : LaneI k q, #((range (rowLen L s H)).filter fun p => P (rowCell s H p)) =
      #(univ.filter fun x => IsRowPos L s x ∧ P x) := by
  rw [← card_sigma]
  apply card_bij (fun p _ => rowCell (n := n) s p.1 p.2)
  · rintro ⟨H, p⟩ hp
    simp only [mem_sigma, mem_univ, true_and, mem_filter, mem_range] at hp ⊢
    exact ⟨⟨H, p, hp.1, rfl⟩, hp.2⟩
  · rintro ⟨H, p⟩ hp ⟨H', p'⟩ hp' he
    simp only [mem_sigma, mem_univ, true_and, mem_filter, mem_range] at hp hp'
    obtain ⟨rfl, rfl⟩ := rowCell_inj L td hp.1 hp'.1 he
    rfl
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    obtain ⟨⟨H, p, hp, rfl⟩, hP⟩ := hx
    exact ⟨⟨H, p⟩, by simp [hp, hP], rfl⟩

open Classical in
theorem sum_col_card (td : TDims n k s q) (P : Cell n → Prop) [DecidablePred P] :
    ∑ V : LaneI k q, #((range (colLen L s V)).filter fun p => P (colCell s V p)) =
      #(univ.filter fun x => IsColPos L s x ∧ P x) := by
  rw [← card_sigma]
  apply card_bij (fun p _ => colCell (n := n) s p.1 p.2)
  · rintro ⟨V, p⟩ hp
    simp only [mem_sigma, mem_univ, true_and, mem_filter, mem_range] at hp ⊢
    exact ⟨⟨V, p, hp.1, rfl⟩, hp.2⟩
  · rintro ⟨V, p⟩ hp ⟨V', p'⟩ hp' he
    simp only [mem_sigma, mem_univ, true_and, mem_filter, mem_range] at hp hp'
    obtain ⟨rfl, rfl⟩ := colCell_inj L td hp.1 hp'.1 he
    rfl
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    obtain ⟨⟨V, p, hp, rfl⟩, hP⟩ := hx
    exact ⟨⟨V, p⟩, by simp [hp, hP], rfl⟩

open Classical in
theorem card_kinds (td : TDims n k s q) (P : Cell n → Prop) [DecidablePred P] :
    #(univ.filter fun x => region L s (sqOf td.hd x) x ∧ P x) +
    #(univ.filter fun x => IsRowPos L s x ∧ P x) +
    #(univ.filter fun x => IsColPos L s x ∧ P x) = #(univ.filter P) := by
  rw [← card_union_of_disjoint, ← card_union_of_disjoint]
  · congr 1
    ext x
    simp only [mem_union, mem_filter, mem_univ, true_and]
    constructor
    · rintro ((⟨_, h⟩ | ⟨_, h⟩) | ⟨_, h⟩) <;> exact h
    · intro h
      by_cases hl : LaneCell L s x
      · rcases row_or_col_of_lane L td x hl with h' | h'
        · exact Or.inl (Or.inr ⟨h', h⟩)
        · exact Or.inr ⟨h', h⟩
      · exact Or.inl (Or.inl ⟨⟨rfl, rfl, hl⟩, h⟩)
  · rw [disjoint_union_left]
    constructor
    · exact disjoint_filter.mpr fun x _ h1 h2 => h1.1.2.2 (lane_of_colPos L td h2.1)
    · exact disjoint_filter.mpr fun x _ h1 h2 => row_not_col L td h1.1 h2.1
  · exact disjoint_filter.mpr fun x _ h1 h2 => h1.1.2.2 (lane_of_rowPos L td h2.1)

/-- Counting any set of cells by regions, row positions and column positions. -/
theorem count_decomp (td : TDims n k s q) (P : Cell n → Prop) [DecidablePred P] :
    (∑ Q : Sq k, #(univ.filter fun x => region L s Q x ∧ P x)) +
    (∑ H : LaneI k q, #((range (rowLen L s H)).filter fun p => P (rowCell s H p))) +
    (∑ V : LaneI k q, #((range (colLen L s V)).filter fun p => P (colCell s V p))) =
      #(univ.filter P) := by
  classical
  rw [sum_region_card L td.hd, sum_row_card L td, sum_col_card L td, card_kinds L td]

end decode

end SlidingPuzzle.Tree
