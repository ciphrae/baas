import SlidingPuzzle.Hub.PrimCount

/-! # Geometry of the hub layout

Coordinates of corridor cells, which cells are corridor cells (`keyOf = none`)
and which lie in a region, injectivity of the corridor parametrizations.
Everything is reduced to linear arithmetic with `b*s` as atoms: a cell with
row `β*s + o` (`o < s`) is in band `β` at offset `o`. -/
namespace SlidingPuzzle.Hub

variable {n k s : ℕ}

/-! ## Arithmetic -/

theorem HDims.s_pos (hd : HDims n k s) : 0 < s := by have := hd.room; omega

theorem HDims.k_lt_s (hd : HDims n k s) : k < s := by have := hd.room; omega

theorem HDims.band_le (hd : HDims n k s) {b : ℕ} (hb : b < k) : b * s + s ≤ n := by
  rw [← hd.mul]
  have := Nat.mul_le_mul_right s (show b + 1 ≤ k from hb)
  rwa [add_mul, one_mul] at this

theorem HDims.two_le_n (hd : HDims n k s) : 2 ≤ n := by
  have := hd.band_le (b := 0) (by have := hd.two_le; omega)
  have := hd.room
  omega

theorem band_lt_band (s : ℕ) {a b : ℕ} (h : a < b) : a * s + s ≤ b * s := by
  have := Nat.mul_le_mul_right s (show a + 1 ≤ b from h)
  rwa [add_mul, one_mul] at this

theorem band_le_band (s : ℕ) {a b : ℕ} (h : a ≤ b) : a * s ≤ b * s :=
  Nat.mul_le_mul_right s h

theorem div_eq_iff_bounds {s a b : ℕ} (hs : 0 < s) : a / s = b ↔ b * s ≤ a ∧ a < b * s + s := by
  constructor
  · rintro rfl
    refine ⟨Nat.div_mul_le_self a s, ?_⟩
    have := (Nat.div_lt_iff_lt_mul hs (x := a) (y := a / s + 1)).mp (by omega)
    rwa [add_mul, one_mul] at this
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · have := (Nat.div_lt_iff_lt_mul hs (x := a) (y := b + 1)).mpr (by rw [add_mul, one_mul]; exact h2)
      omega
    · exact (Nat.le_div_iff_mul_le hs).mpr h1

theorem divmod_eq {s b o : ℕ} (ho : o < s) : (b * s + o) / s = b ∧ (b * s + o) % s = o := by
  have hs : 0 < s := by omega
  exact (Nat.div_mod_unique hs).mpr ⟨by rw [mul_comm]; omega, ho⟩

/-- Successor of a position in `m`-blocks. -/
theorem divmod_succ {m : ℕ} (hm : 0 < m) (q : ℕ) :
    ((q + 1) % m = 0 ∧ (q + 1) / m = q / m + 1 ∧ q % m + 1 = m) ∨
      ((q + 1) % m = q % m + 1 ∧ (q + 1) / m = q / m ∧ q % m + 1 < m) := by
  have h := Nat.mod_add_div q m
  have hlt := Nat.mod_lt q hm
  rcases Nat.lt_or_ge (q % m + 1) m with h1 | h1
  · right
    have := (Nat.div_mod_unique hm (a := q + 1) (d := q / m) (c := q % m + 1)).mpr
      ⟨by omega, h1⟩
    exact ⟨this.2, this.1, h1⟩
  · left
    have := (Nat.div_mod_unique hm (a := q + 1) (d := q / m + 1) (c := 0)).mpr
      ⟨by rw [mul_add, mul_one]; omega, hm⟩
    exact ⟨this.2, this.1, by omega⟩

/-! ## Cells -/

section cells
variable [NeZero n]

theorem mkCell_fst {r c : ℕ} (hr : r < n) : (mkCell n r c).1.val = r := by
  simp [mkCell, Nat.mod_eq_of_lt hr]

theorem mkCell_snd {r c : ℕ} (hc : c < n) : (mkCell n r c).2.val = c := by
  simp [mkCell, Nat.mod_eq_of_lt hc]

omit [NeZero n] in
theorem cell_ext {x y : Cell n} (h1 : x.1.val = y.1.val) (h2 : x.2.val = y.2.val) : x = y :=
  Prod.ext (Fin.ext h1) (Fin.ext h2)

omit [NeZero n] in
theorem cell_ne_of_fst {x y : Cell n} (h : x.1.val ≠ y.1.val) : x ≠ y :=
  fun e => h (by rw [e])

omit [NeZero n] in
theorem cell_ne_of_snd {x y : Cell n} (h : x.2.val ≠ y.2.val) : x ≠ y :=
  fun e => h (by rw [e])

end cells

/-! ## Regions in coordinates -/

theorem region_coords (hd : HDims n k s) {Q : Sq k} {x : Cell n} {β o γ o' : ℕ}
    (h1 : x.1.val = β * s + o) (h2 : x.2.val = γ * s + o') (ho : o < s) (ho' : o' < s) :
    region k s Q x ↔ β = Q.1.val ∧ γ = Q.2.val ∧
      (o = Q.2.val ∨ (k ≤ o ∧ (k ≤ o' ∨ o' = Q.1.val))) := by
  unfold region
  rw [h1, h2, (divmod_eq ho).1, (divmod_eq ho).2, (divmod_eq ho').1, (divmod_eq ho').2]

theorem keyOf_coords_some (hd : HDims n k s) {Q : Sq k} {x : Cell n} {o o' : ℕ}
    (h1 : x.1.val = Q.1.val * s + o) (h2 : x.2.val = Q.2.val * s + o') (ho : o < s)
    (ho' : o' < s) (h : o = Q.2.val ∨ (k ≤ o ∧ (k ≤ o' ∨ o' = Q.1.val))) :
    keyOf hd x = some Q :=
  (keyOf_eq_some hd).mpr ((region_coords hd h1 h2 ho ho').mpr ⟨rfl, rfl, h⟩)

theorem keyOf_coords_none (hd : HDims n k s) {x : Cell n} {β o γ o' : ℕ}
    (h1 : x.1.val = β * s + o) (h2 : x.2.val = γ * s + o') (ho : o < s) (ho' : o' < s)
    (h : ¬ (o = γ ∨ (k ≤ o ∧ (k ≤ o' ∨ o' = β)))) :
    keyOf hd x = none := by
  rw [keyOf_eq_none]
  intro Q hQ
  obtain ⟨hb, hc, hr⟩ := (region_coords hd h1 h2 ho ho').mp hQ
  subst hb hc
  exact h hr

theorem region_bounds (hd : HDims n k s) {Q : Sq k} {x : Cell n} (h : region k s Q x) :
    Q.1.val * s ≤ x.1.val ∧ x.1.val < Q.1.val * s + s ∧
      Q.2.val * s ≤ x.2.val ∧ x.2.val < Q.2.val * s + s := by
  obtain ⟨h1, h2, -⟩ := h
  have a := (div_eq_iff_bounds hd.s_pos).mp h1
  have b := (div_eq_iff_bounds hd.s_pos).mp h2
  omega

theorem reservoir_iff (hd : HDims n k s) {Q : Sq k} {x : Cell n} :
    reservoir k s Q x ↔ Q.1.val * s + k ≤ x.1.val ∧ x.1.val < Q.1.val * s + s ∧
      Q.2.val * s + k ≤ x.2.val ∧ x.2.val < Q.2.val * s + s := by
  unfold reservoir
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have a := (div_eq_iff_bounds hd.s_pos).mp h1
    have b := (div_eq_iff_bounds hd.s_pos).mp h2
    have c := mod_of_div h1
    have d := mod_of_div h2
    omega
  · rintro ⟨h1, h2, h3, h4⟩
    have a : x.1.val / s = Q.1.val := (div_eq_iff_bounds hd.s_pos).mpr ⟨by omega, h2⟩
    have b : x.2.val / s = Q.2.val := (div_eq_iff_bounds hd.s_pos).mpr ⟨by omega, h4⟩
    have c := mod_of_div a
    have d := mod_of_div b
    omega
where
  mod_of_div {a b : ℕ} (h : a / s = b) : a % s + b * s = a := by
    rw [← h, mul_comm]; exact Nat.mod_add_div a s

theorem region_of_reservoir {Q : Sq k} {x : Cell n} (h : reservoir k s Q x) :
    region k s Q x := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, Or.inr ⟨h3, Or.inl h4⟩⟩

theorem keyOf_reservoir (hd : HDims n k s) {Q : Sq k} {x : Cell n} (h : reservoir k s Q x) :
    keyOf hd x = some Q := (keyOf_eq_some hd).mpr (region_of_reservoir h)

/-- Two cells of the same key. -/
theorem keyOf_eq_of_region (hd : HDims n k s) {Q : Sq k} {x y : Cell n}
    (hx : region k s Q x) (hy : region k s Q y) : keyOf hd x = keyOf hd y := by
  rw [(keyOf_eq_some hd).mpr hx, (keyOf_eq_some hd).mpr hy]

theorem ne_of_keyOf {hd : HDims n k s} {x y : Cell n} (h : keyOf hd x ≠ keyOf hd y) :
    x ≠ y := fun e => h (by rw [e])

/-! ## Row corridors -/

section rows
variable [NeZero n]

/-- Column of position `q` of a row half. -/
def rowCol (s : ℕ) (H : RowH k) (q : ℕ) : ℕ :=
  if H.2.2 then H.2.1.val * s + s + q else H.2.1.val * s - 1 - q

theorem rowCell_fst (hd : HDims n k s) (H : RowH k) (q : ℕ) :
    (rowCell (n := n) k s H q).1.val = H.1.val * s + H.2.1.val := by
  unfold rowCell
  apply mkCell_fst
  have := hd.band_le H.1.isLt
  have := H.2.1.isLt
  have := hd.k_lt_s
  omega

theorem rowLen_bound (hd : HDims n k s) (H : RowH k) (q : ℕ) (hq : q < rowLen k s H) :
    (H.2.2 = true → H.2.1.val * s + s + q < n) ∧ (H.2.2 = false → q < H.2.1.val * s) := by
  unfold rowLen at hq
  constructor
  · intro h
    rw [h, if_pos rfl] at hq
    have hc := H.2.1.isLt
    have e : H.2.1.val * s + s + (k - 1 - H.2.1.val) * s = n := by
      rw [← hd.mul, ← add_one_mul, ← add_mul]; congr 1; omega
    omega
  · intro h
    rw [h] at hq
    simpa using hq

theorem rowCell_snd (hd : HDims n k s) (H : RowH k) (q : ℕ) (hq : q < rowLen k s H) :
    (rowCell (n := n) k s H q).2.val = rowCol s H q := by
  have hb := rowLen_bound hd H q hq
  have e : (if H.2.2 then (H.2.1.val + 1) * s + q else H.2.1.val * s - 1 - q) = rowCol s H q := by
    unfold rowCol; split_ifs <;> ring
  unfold rowCell
  rw [e]
  apply mkCell_snd
  have := hd.band_le H.2.1.isLt
  have := NeZero.pos n
  unfold rowCol
  cases h : H.2.2
  · simp only [Bool.false_eq_true, if_false]; omega
  · simp only [if_true]
    exact hb.1 h

/-- The block column of a row position is not the row's own block. -/
theorem rowCol_block (hd : HDims n k s) (H : RowH k) (q : ℕ) (hq : q < rowLen k s H) :
    ¬ (H.2.1.val * s ≤ rowCol s H q ∧ rowCol s H q < H.2.1.val * s + s) := by
  have hb := rowLen_bound hd H q hq
  unfold rowCol
  cases h : H.2.2
  · simp only [Bool.false_eq_true, if_false]; have := hb.2 h; omega
  · simp only [if_true]; omega

theorem keyOf_rowCell (hd : HDims n k s) (H : RowH k) (q : ℕ) (hq : q < rowLen k s H) :
    keyOf hd (rowCell (n := n) k s H q) = none := by
  rw [keyOf_eq_none]
  intro Q hQ
  have h1 := rowCell_fst (n := n) hd H q
  have h2 := rowCell_snd (n := n) hd H q hq
  have hc := H.2.1.isLt
  have hks := hd.k_lt_s
  obtain ⟨hr, hcol, hoff⟩ := hQ
  rw [h1] at hr hoff
  rw [(divmod_eq (by omega : H.2.1.val < s)).2] at hoff
  rcases hoff with hoff | ⟨hoff, -⟩
  · rw [h2, ← hoff] at hcol
    exact rowCol_block hd H q hq ((div_eq_iff_bounds hd.s_pos).mp hcol)
  · omega

theorem rowCell_inj (hd : HDims n k s) {H H' : RowH k} {q q' : ℕ}
    (hq : q < rowLen k s H) (hq' : q' < rowLen k s H')
    (h : (rowCell (n := n) k s H q) = rowCell k s H' q') : H = H' ∧ q = q' := by
  have e1 := congrArg (fun x : Cell n => x.1.val) h
  have e2 := congrArg (fun x : Cell n => x.2.val) h
  simp only [rowCell_fst hd, rowCell_snd hd _ _ hq, rowCell_snd hd _ _ hq'] at e1 e2
  have hks := hd.k_lt_s
  have d1 := divmod_eq (b := H.1.val) (by have := H.2.1.isLt; omega : H.2.1.val < s)
  have d2 := divmod_eq (b := H'.1.val) (by have := H'.2.1.isLt; omega : H'.2.1.val < s)
  rw [e1] at d1
  have hb : H.1 = H'.1 := Fin.ext (by rw [← d1.1, d2.1])
  have hc : H.2.1 = H'.2.1 := Fin.ext (by rw [← d1.2, d2.2])
  have b1 := rowLen_bound hd H q hq
  have b2 := rowLen_bound hd H' q' hq'
  rw [← hc] at b2
  unfold rowCol at e2
  rw [← hc] at e2
  obtain ⟨H1, H2, H3⟩ := H
  obtain ⟨H1', H2', H3'⟩ := H'
  simp only at hb hc e2 b1 b2 ⊢
  subst hb hc
  cases H3 <;> cases H3' <;> simp at e2 b1 b2 ⊢ <;> omega

end rows

/-! ## Column corridors -/

section cols
variable [NeZero n]

/-- Band of position `q` of a column half. -/
def cBand (k s : ℕ) (V : ColH k) (q : ℕ) : ℕ :=
  if V.2.2 then V.2.1.val + 1 + q / (s - k) else V.2.1.val - 1 - q / (s - k)

/-- Row offset of position `q` of a column half. -/
def cOff (k s : ℕ) (V : ColH k) (q : ℕ) : ℕ :=
  if V.2.2 then k + q % (s - k) else s - 1 - q % (s - k)

theorem cOff_bounds (hd : HDims n k s) (V : ColH k) (q : ℕ) :
    k ≤ cOff k s V q ∧ cOff k s V q < s := by
  have hm : 0 < s - k := by have := hd.k_lt_s; omega
  have := Nat.mod_lt q hm
  unfold cOff
  split_ifs <;> omega

omit [NeZero n] in
theorem colPos_div_lt (hd : HDims n k s) (V : ColH k) (q : ℕ) (hq : q < colLen k s V) :
    q / (s - k) < (if V.2.2 then k - 1 - V.2.1.val else V.2.1.val) := by
  have hm : 0 < s - k := by have := hd.k_lt_s; omega
  exact (Nat.div_lt_iff_lt_mul hm).mpr (by unfold colLen at hq; split_ifs at hq ⊢ <;> assumption)

theorem cBand_bounds (hd : HDims n k s) (V : ColH k) (q : ℕ) (hq : q < colLen k s V) :
    cBand k s V q < k ∧ cBand k s V q ≠ V.2.1.val ∧
      (V.2.2 = true → V.2.1.val < cBand k s V q) ∧
      (V.2.2 = false → cBand k s V q < V.2.1.val) := by
  have hm : 0 < s - k := by have := hd.k_lt_s; omega
  have ha := V.2.1.isLt
  have hdiv := colPos_div_lt hd V q hq
  unfold cBand
  generalize q / (s - k) = t at *
  cases h : V.2.2 <;> simp [h] at hdiv ⊢ <;> omega

theorem colCell_snd (hd : HDims n k s) (V : ColH k) (q : ℕ) :
    (colCell (n := n) k s V q).2.val = V.1.val * s + V.2.1.val := by
  unfold colCell
  apply mkCell_snd
  have := hd.band_le V.1.isLt
  have := V.2.1.isLt
  have := hd.k_lt_s
  omega

theorem colCell_fst (hd : HDims n k s) (V : ColH k) (q : ℕ) (hq : q < colLen k s V) :
    (colCell (n := n) k s V q).1.val = cBand k s V q * s + cOff k s V q := by
  have hb := cBand_bounds hd V q hq
  have ho := cOff_bounds hd V q
  have e : (colCell (n := n) k s V q) =
      mkCell n (cBand k s V q * s + cOff k s V q) (V.1.val * s + V.2.1.val) := by
    unfold colCell cBand cOff
    split_ifs <;> rfl
  rw [e]
  apply mkCell_fst
  have := hd.band_le hb.1
  omega

theorem keyOf_colCell (hd : HDims n k s) (V : ColH k) (q : ℕ) (hq : q < colLen k s V) :
    keyOf hd (colCell (n := n) k s V q) = none := by
  have hb := cBand_bounds hd V q hq
  have ho := cOff_bounds hd V q
  have ha := V.2.1.isLt
  have hks := hd.k_lt_s
  apply keyOf_coords_none hd (colCell_fst hd V q hq) (colCell_snd hd V q) ho.2 (by omega)
  omega

theorem colCell_inj (hd : HDims n k s) {V V' : ColH k} {q q' : ℕ}
    (hq : q < colLen k s V) (hq' : q' < colLen k s V')
    (h : (colCell (n := n) k s V q) = colCell k s V' q') : V = V' ∧ q = q' := by
  have e1 := congrArg (fun x : Cell n => x.1.val) h
  have e2 := congrArg (fun x : Cell n => x.2.val) h
  simp only [colCell_fst hd _ _ hq, colCell_fst hd _ _ hq', colCell_snd hd] at e1 e2
  have hks := hd.k_lt_s
  have hm : 0 < s - k := by omega
  have ho := cOff_bounds hd V q
  have ho' := cOff_bounds hd V' q'
  have d1 := divmod_eq (b := cBand k s V q) ho.2
  have d2 := divmod_eq (b := cBand k s V' q') ho'.2
  rw [e1] at d1
  have hB : cBand k s V q = cBand k s V' q' := by rw [← d1.1, d2.1]
  have hO : cOff k s V q = cOff k s V' q' := by rw [← d1.2, d2.2]
  have c1 := divmod_eq (b := V.1.val) (by have := V.2.1.isLt; omega : V.2.1.val < s)
  have c2 := divmod_eq (b := V'.1.val) (by have := V'.2.1.isLt; omega : V'.2.1.val < s)
  rw [e2] at c1
  have hc : V.1 = V'.1 := Fin.ext (by rw [← c1.1, c2.1])
  have ha : V.2.1 = V'.2.1 := Fin.ext (by rw [← c1.2, c2.2])
  have b1 := colPos_div_lt hd V q hq
  have b2 := colPos_div_lt hd V' q' hq'
  have r1 := Nat.mod_add_div q (s - k)
  have r2 := Nat.mod_add_div q' (s - k)
  have l1 := Nat.mod_lt q hm
  have l2 := Nat.mod_lt q' hm
  obtain ⟨V1, V2, V3⟩ := V
  obtain ⟨V1', V2', V3'⟩ := V'
  simp only at hc ha hB hO b1 b2 ⊢
  subst hc ha
  simp only [cBand, cOff] at hB hO
  cases V3 <;> cases V3' <;> simp only [Bool.false_eq_true, if_false, if_true,
    Prod.mk.injEq, true_and, reduceCtorEq] at hB hO b1 b2 ⊢
  · have e3 : q / (s - k) = q' / (s - k) := by omega
    have e4 : q % (s - k) = q' % (s - k) := by omega
    rw [← r1, ← r2, e3, e4]
  · exfalso; clear * - hB b1 b2; generalize q / (s - k) = x at *; generalize q' / (s - k) = y at *; omega
  · exfalso; clear * - hB b1 b2; generalize q / (s - k) = x at *; generalize q' / (s - k) = y at *; omega
  · have e3 : q / (s - k) = q' / (s - k) := by omega
    have e4 : q % (s - k) = q' % (s - k) := by omega
    rw [← r1, ← r2, e3, e4]

theorem rowCell_ne_colCell (hd : HDims n k s) (H : RowH k) (V : ColH k) (q q' : ℕ)
    (hq' : q' < colLen k s V) : (rowCell (n := n) k s H q) ≠ colCell k s V q' := by
  intro h
  have e1 := congrArg (fun x : Cell n => x.1.val) h
  simp only [rowCell_fst hd, colCell_fst hd _ _ hq'] at e1
  have ho := cOff_bounds hd V q'
  have hks := hd.k_lt_s
  have d1 := divmod_eq (b := H.1.val) (by have := H.2.1.isLt; omega : H.2.1.val < s)
  have d2 := divmod_eq (b := cBand k s V q') ho.2
  rw [e1] at d1
  have := H.2.1.isLt
  omega

end cols

end SlidingPuzzle.Hub
