/-
Copyright (c) 2026 The Zhong formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhong formalisation contributors
-/
import Zhong.Potential

/-!
# The Manhattan-distance potential

This file formalises Definition 11 and Proposition 7 of Zhong (2023): the Manhattan
distance `D` to the target board is a potential function, and in fact every move changes
`D` by exactly `±1` (so `D` satisfies the strengthened property `IsPotential1`).
-/

namespace Zhong

open Equiv

variable {n m : ℕ}

/-- Manhattan distance between two cells. -/
def cellDist (a b : Cell n m) : ℕ :=
  Nat.dist a.1.1 b.1.1 + Nat.dist a.2.1 b.2.1

/-- The position of the label `i` in the board `B`. -/
def posOf (B : Board n m) (i : Fin (n * m)) : Cell n m := B.symm i

/-- The set of tile labels (all labels except the blank `0`). -/
def tileSet (n : ℕ) [NeZero (n * n)] : Finset (Fin (n * n)) :=
  Finset.univ.filter (fun i => i ≠ 0)

/-- Definition 11: the Manhattan distance to the target board. -/
noncomputable def D [NeZero (n * n)] (B : Board n n) : ℕ :=
  ∑ i ∈ tileSet n, cellDist (posOf B i) ((target n n).symm i)

/-! ### Arithmetic of `Nat.dist` -/

theorem natDist_succ_left' (m k : ℕ) :
    Nat.dist (m + 1) k = Nat.dist m k + 1 ∨ Nat.dist m k = Nat.dist (m + 1) k + 1 := by
  unfold Nat.dist; omega

theorem natDist_succ_left (m k : ℕ) :
    |(Nat.dist (m + 1) k : ℤ) - (Nat.dist m k : ℤ)| = 1 := by
  rcases natDist_succ_left' m k with h | h
  · rw [h]; push_cast; rw [abs_of_pos] <;> norm_num
  · rw [h]; push_cast; rw [abs_of_neg] <;> norm_num

theorem natDist_pred_left (m k : ℕ) :
    |(Nat.dist m k : ℤ) - (Nat.dist (m + 1) k : ℤ)| = 1 := by
  rw [abs_sub_comm]; exact natDist_succ_left m k

theorem abs_sub_add_comm (a b c : ℤ) : |(a + c) - (b + c)| = |a - b| := by
  rw [show (a + c) - (b + c) = a - b by ring]

theorem abs_add_sub_comm (a b c : ℤ) : |(c + a) - (c + b)| = |a - b| := by
  rw [show (c + a) - (c + b) = a - b by ring]

/-! ### How `act` moves the blank and the tiles -/

theorem symm_act [NeZero (n * m)] {B : Board n m} {δ : Dir} {c' : Cell n m}
    (h : neighbor? (blank B) δ = some c') :
    (act B δ).symm = B.symm.trans (Equiv.swap (blank B) c') := by
  rw [act_of_neighbor? h, Equiv.symm_trans, Equiv.symm_swap]

theorem posOf_act [NeZero (n * m)] {B : Board n m} {δ : Dir} {c' : Cell n m}
    (h : neighbor? (blank B) δ = some c') (i : Fin (n * m)) :
    posOf (act B δ) i = Equiv.swap (blank B) c' (posOf B i) := by
  simp only [posOf, symm_act h, Equiv.trans_apply]

/-- The tile that sits at the neighbour `c'` moves onto the blank. -/
theorem posOf_act_tile [NeZero (n * m)] {B : Board n m} {δ : Dir} {c' : Cell n m}
    (h : neighbor? (blank B) δ = some c') :
    posOf (act B δ) (B c') = blank B := by
  rw [posOf_act h]
  simp only [posOf, Equiv.symm_apply_apply, Equiv.swap_apply_right]

/-- Every other tile keeps its position. -/
theorem posOf_act_of_ne [NeZero (n * m)] {B : Board n m} {δ : Dir} {c' : Cell n m}
    (h : neighbor? (blank B) δ = some c') {i : Fin (n * m)}
    (hi0 : i ≠ 0) (hi : i ≠ B c') :
    posOf (act B δ) i = posOf B i := by
  rw [posOf_act h]
  refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
  · intro hc
    have h' : B (posOf B i) = B (blank B) := congrArg B hc
    have : i = 0 := by simpa [posOf, blank] using h'
    exact hi0 this
  · intro hc
    have h' : B (posOf B i) = B c' := congrArg B hc
    have : i = B c' := by simpa [posOf] using h'
    exact hi this

/-! ### Adjacent cells change the distance by one -/

theorem cellDist_neighbor {δ : Dir} {a b q : Cell n m} (h : neighbor? a δ = some b) :
    |(cellDist b q : ℤ) - (cellDist a q : ℤ)| = 1 := by
  cases δ
  case U =>
    rw [neighbor?] at h
    by_cases hc : a.1.1 + 1 < n
    · rw [dif_pos hc] at h
      injection h with hb; subst hb
      simp only [cellDist]; push_cast; rw [abs_sub_add_comm]
      exact natDist_succ_left _ _
    · rw [dif_neg hc] at h; exact absurd h (by simp)
  case D =>
    rw [neighbor?] at h
    by_cases hc : 0 < a.1.1
    · rw [if_pos hc] at h
      injection h with hb; subst hb
      simp only [cellDist]; push_cast; rw [abs_sub_add_comm]
      have hpred : a.1.1 - 1 + 1 = a.1.1 := by omega
      have := natDist_pred_left (a.1.1 - 1) q.1.1
      rwa [hpred] at this
    · rw [if_neg hc] at h; exact absurd h (by simp)
  case L =>
    rw [neighbor?] at h
    by_cases hc : a.2.1 + 1 < m
    · rw [dif_pos hc] at h
      injection h with hb; subst hb
      simp only [cellDist]; push_cast; rw [abs_add_sub_comm]
      exact natDist_succ_left _ _
    · rw [dif_neg hc] at h; exact absurd h (by simp)
  case R =>
    rw [neighbor?] at h
    by_cases hc : 0 < a.2.1
    · rw [if_pos hc] at h
      injection h with hb; subst hb
      simp only [cellDist]; push_cast; rw [abs_add_sub_comm]
      have hpred : a.2.1 - 1 + 1 = a.2.1 := by omega
      have := natDist_pred_left (a.2.1 - 1) q.2.1
      rwa [hpred] at this
    · rw [if_neg hc] at h; exact absurd h (by simp)

/-! ### Proposition 7 -/

theorem isPotential1_D [NeZero (n * n)] :
    IsPotential1 (fun B : Board n n => (D B : ℤ)) := by
  intro B δ ha
  obtain ⟨c', hc'⟩ : ∃ c', neighbor? (blank B) δ = some c' := by
    unfold Applicable at ha
    cases h : neighbor? (blank B) δ with
    | none => simp [h] at ha
    | some c' => exact ⟨c', rfl⟩
  let f : Fin (n * n) → ℕ :=
    fun i => cellDist (posOf (act B δ) i) ((target n n).symm i)
  let g : Fin (n * n) → ℕ :=
    fun i => cellDist (posOf B i) ((target n n).symm i)
  have hi₀ : B c' ∈ tileSet n := by
    simp only [tileSet, Finset.mem_filter, Finset.mem_univ, true_and]
    intro hzero
    exact neighbor?_ne hc' (by rw [blank, ← hzero]; simp)
  have hDact : D (act B δ) = ∑ i ∈ tileSet n, f i := rfl
  have hDold : D B = ∑ i ∈ tileSet n, g i := rfl
  have key : (∑ i ∈ tileSet n, f i) + g (B c') = (∑ i ∈ tileSet n, g i) + f (B c') := by
    rw [(Finset.sum_erase_add _ f hi₀).symm, (Finset.sum_erase_add _ g hi₀).symm]
    have hcongr : ∑ i ∈ (tileSet n).erase (B c'), f i
        = ∑ i ∈ (tileSet n).erase (B c'), g i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi_ne : i ≠ B c' := (Finset.mem_erase.mp hi).1
      have hi0 : i ≠ 0 := by
        have : i ∈ tileSet n := (Finset.mem_erase.mp hi).2
        simpa [tileSet] using this
      change f i = g i
      simp only [f, g]
      rw [posOf_act_of_ne hc' hi0 hi_ne]
    rw [hcongr]; ring
  have hdiff : (D (act B δ) : ℤ) - (D B : ℤ) = (f (B c') : ℤ) - (g (B c') : ℤ) := by
    rw [hDact, hDold]
    push_cast
    have := congrArg (fun x : ℕ => (x : ℤ)) key
    push_cast at this
    linarith
  have hf : f (B c') = cellDist (blank B) ((target n n).symm (B c')) := by
    simp only [f, posOf_act_tile hc']
  have hg : g (B c') = cellDist c' ((target n n).symm (B c')) := by
    simp only [g, posOf, Equiv.symm_apply_apply]
  have hbound : |(f (B c') : ℤ) - (g (B c') : ℤ)| = 1 := by
    rw [hf, hg, abs_sub_comm]
    exact cellDist_neighbor hc'
  rw [hdiff, hbound]

/-! ## Extremal Manhattan distance (M4)

This section proves the two extremal bounds of step 5 of the proof of Proposition 9:
`D B ≤ n³` for every board, and `D B ≥ n³ - O(n²)` for the board obtained by rotating
the target by 180°.  The upper bound uses the triangle inequality through the centre of
the board; the lower bound evaluates the rotation explicitly. -/

/-- Casting `Nat.dist` to `ℤ` yields the absolute difference. -/
theorem cast_dist (a b : ℕ) : (Nat.dist a b : ℤ) = |(a : ℤ) - (b : ℤ)| := by
  rcases le_total a b with h | h
  · have hd : Nat.dist a b = b - a := by rw [Nat.dist, Nat.sub_eq_zero_of_le h, zero_add]
    rw [hd, Nat.cast_sub h, abs_of_nonpos (by omega : (a : ℤ) - (b : ℤ) ≤ 0)]
    ring
  · have hd : Nat.dist a b = a - b := by rw [Nat.dist, Nat.sub_eq_zero_of_le h, add_zero]
    rw [hd, Nat.cast_sub h, abs_of_nonneg (by omega : (0 : ℤ) ≤ (a : ℤ) - (b : ℤ))]

/-- `G n = ∑_{x<n} |2x - (n-1)|` is twice the total distance from the indices
`0, …, n-1` to the centre `(n-1)/2` of a row of length `n`. -/
def G (n : ℕ) : ℤ :=
  ∑ x ∈ Finset.range n, |(2 : ℤ) * (x : ℤ) - ((n : ℤ) - 1)|

/-- Two-step recurrence for `G`. -/
theorem G_rec (n : ℕ) : G (n + 2) = G n + 2 * ((n : ℤ) + 1) := by
  unfold G
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  have hmid : ∀ k : ℕ,
      |(2 : ℤ) * (((k + 1 : ℕ)) : ℤ) - ((((n + 2 : ℕ)) : ℤ) - 1)|
        = |(2 : ℤ) * (k : ℤ) - ((n : ℤ) - 1)| := by
    intro k
    have h1 : (((k + 1 : ℕ)) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
    have h2 : ((((n + 2 : ℕ)) : ℤ) - 1) = (n : ℤ) + 1 := by push_cast; ring
    rw [h1, h2]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun k _ => hmid k)]
  have h0 : |(2 : ℤ) * ((0 : ℕ) : ℤ) - ((((n + 2 : ℕ)) : ℤ) - 1)| = (n : ℤ) + 1 := by
    have h2 : ((((n + 2 : ℕ)) : ℤ) - 1) = (n : ℤ) + 1 := by push_cast; ring
    rw [h2, Nat.cast_zero, mul_zero, zero_sub, abs_neg]
    exact abs_of_nonneg (by omega)
  have hlast : |(2 : ℤ) * (((n + 1 : ℕ)) : ℤ) - ((((n + 2 : ℕ)) : ℤ) - 1)|
      = (n : ℤ) + 1 := by
    have h1 : (((n + 1 : ℕ)) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    have h2 : ((((n + 2 : ℕ)) : ℤ) - 1) = (n : ℤ) + 1 := by push_cast; ring
    rw [h1, h2, show (2 : ℤ) * ((n : ℤ) + 1) - ((n : ℤ) + 1) = (n : ℤ) + 1 by ring]
    exact abs_of_nonneg (by omega)
  rw [h0, hlast]
  ring

/-- Upper bound for `G`: `2 G n ≤ n²`. -/
theorem two_mul_G_le_sq (n : ℕ) : 2 * G n ≤ (n : ℤ) ^ 2 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [G]
  | one => simp [G]
  | more k _ ihk1 =>
      rw [G_rec]
      have hcast : (((k + 2 : ℕ)) : ℤ) = (k : ℤ) + 2 := by push_cast; ring
      rw [hcast]
      nlinarith [ihk1]

/-- Lower bound for `G`: `n² ≤ 2 G n + 1`. -/
theorem sq_le_two_mul_G_add (n : ℕ) : (n : ℤ) ^ 2 ≤ 2 * G n + 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [G]
  | one => simp [G]
  | more k ihk _ =>
      rw [G_rec]
      have hcast : (((k + 2 : ℕ)) : ℤ) = (k : ℤ) + 2 := by push_cast; ring
      rw [hcast]
      nlinarith [ihk]

/-- Reindex a sum over `Fin n` as a sum over `range n`. -/
theorem sum_fin_abs_eq_range (n : ℕ) :
    ∑ x : Fin n, |(2 : ℤ) * (x : ℤ) - ((n : ℤ) - 1)|
      = ∑ x ∈ Finset.range n, |(2 : ℤ) * (x : ℤ) - ((n : ℤ) - 1)| := by
  simpa using Fin.sum_univ_eq_sum_range
    (fun j : ℕ => |(2 : ℤ) * (j : ℤ) - ((n : ℤ) - 1)|) n

/-- Sum of `|2x - (n-1)|` over all cells, taking only the row coordinate. -/
theorem sum_cell_row [NeZero (n * n)] :
    ∑ c : Cell n n, |(2 : ℤ) * (c.1.1 : ℤ) - ((n : ℤ) - 1)| = (n : ℤ) * G n := by
  rw [Fintype.sum_prod_type]
  have hinner : ∀ x : Fin n,
      ∑ _y : Fin n, |(2 : ℤ) * (x : ℤ) - ((n : ℤ) - 1)|
        = (n : ℤ) * |(2 : ℤ) * (x : ℤ) - ((n : ℤ) - 1)| := by
    intro x
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_congr rfl (fun x _ => hinner x)]
  have hfac : (∑ x : Fin n, (n : ℤ) * |(2 : ℤ) * (x : ℤ) - ((n : ℤ) - 1)|)
      = (∑ x : Fin n, |(2 : ℤ) * (x : ℤ) - ((n : ℤ) - 1)|) * (n : ℤ) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  rw [hfac, mul_comm, G, sum_fin_abs_eq_range]

/-- Sum of `|2y - (n-1)|` over all cells, taking only the column coordinate. -/
theorem sum_cell_col [NeZero (n * n)] :
    ∑ c : Cell n n, |(2 : ℤ) * (c.2.1 : ℤ) - ((n : ℤ) - 1)| = (n : ℤ) * G n := by
  rw [Fintype.sum_prod_type]
  have hinner : ∑ y : Fin n, |(2 : ℤ) * (y : ℤ) - ((n : ℤ) - 1)| = G n := by
    rw [G, sum_fin_abs_eq_range]
  rw [Finset.sum_congr rfl (fun _x _ => hinner)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The set of tiles is the full label set with the blank removed. -/
theorem tileSet_eq_erase [NeZero (n * n)] :
    tileSet n = (Finset.univ : Finset (Fin (n * n))).erase 0 := by
  ext i
  simp [tileSet]

/-- Row-coordinate contribution of the tiles of a board is at most `n G n`. -/
theorem sum_row_abs_le [NeZero (n * n)] (B : Board n n) :
    ∑ i ∈ tileSet n, |(2 : ℤ) * (posOf B i).1.1 - ((n : ℤ) - 1)| ≤ (n : ℤ) * G n := by
  rw [tileSet]
  calc ∑ i ∈ Finset.univ.filter (fun i : Fin (n * n) => i ≠ 0),
          |(2 : ℤ) * (posOf B i).1.1 - ((n : ℤ) - 1)|
      ≤ ∑ i : Fin (n * n), |(2 : ℤ) * (posOf B i).1.1 - ((n : ℤ) - 1)| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => abs_nonneg _)
    _ = ∑ c : Cell n n, |(2 : ℤ) * (c.1.1 : ℤ) - ((n : ℤ) - 1)| := by
        have h := Equiv.sum_comp B.symm
          (fun c : Cell n n => |(2 : ℤ) * (c.1.1 : ℤ) - ((n : ℤ) - 1)|)
        simpa [posOf] using h
    _ = (n : ℤ) * G n := sum_cell_row

/-- Column-coordinate contribution of the tiles of a board is at most `n G n`. -/
theorem sum_col_abs_le [NeZero (n * n)] (B : Board n n) :
    ∑ i ∈ tileSet n, |(2 : ℤ) * (posOf B i).2.1 - ((n : ℤ) - 1)| ≤ (n : ℤ) * G n := by
  rw [tileSet]
  calc ∑ i ∈ Finset.univ.filter (fun i : Fin (n * n) => i ≠ 0),
          |(2 : ℤ) * (posOf B i).2.1 - ((n : ℤ) - 1)|
      ≤ ∑ i : Fin (n * n), |(2 : ℤ) * (posOf B i).2.1 - ((n : ℤ) - 1)| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => abs_nonneg _)
    _ = ∑ c : Cell n n, |(2 : ℤ) * (c.2.1 : ℤ) - ((n : ℤ) - 1)| := by
        have h := Equiv.sum_comp B.symm
          (fun c : Cell n n => |(2 : ℤ) * (c.2.1 : ℤ) - ((n : ℤ) - 1)|)
        simpa [posOf] using h
    _ = (n : ℤ) * G n := sum_cell_col

/-- The row-coordinate contribution of the tiles is at least `n G n - (n-1)`: dropping
the blank's tile loses at most `n - 1`. -/
theorem sum_row_abs_lower [NeZero (n * n)] (B : Board n n) :
    (n : ℤ) * G n - ((n : ℤ) - 1)
      ≤ ∑ i ∈ tileSet n, |(2 : ℤ) * (posOf B i).1.1 - ((n : ℤ) - 1)| := by
  have hcomp : ∑ i : Fin (n * n), |(2 : ℤ) * (posOf B i).1.1 - ((n : ℤ) - 1)|
      = ∑ c : Cell n n, |(2 : ℤ) * (c.1.1 : ℤ) - ((n : ℤ) - 1)| := by
    have h := Equiv.sum_comp B.symm
      (fun c : Cell n n => |(2 : ℤ) * (c.1.1 : ℤ) - ((n : ℤ) - 1)|)
    simpa [posOf] using h
  have hsplit : ∑ i : Fin (n * n), |(2 : ℤ) * (posOf B i).1.1 - ((n : ℤ) - 1)|
      = (∑ i ∈ tileSet n, |(2 : ℤ) * (posOf B i).1.1 - ((n : ℤ) - 1)|)
        + |(2 : ℤ) * (posOf B 0).1.1 - ((n : ℤ) - 1)| := by
    rw [tileSet_eq_erase]
    exact (Finset.sum_erase_add (Finset.univ : Finset (Fin (n * n)))
      (fun i => |(2 : ℤ) * (posOf B i).1.1 - ((n : ℤ) - 1)|)
      (Finset.mem_univ 0)).symm
  have hbound : |(2 : ℤ) * (posOf B 0).1.1 - ((n : ℤ) - 1)| ≤ (n : ℤ) - 1 := by
    rw [abs_le]
    have hx : ((posOf B 0).1.1 : ℤ) < (n : ℤ) := by exact_mod_cast (posOf B 0).1.2
    constructor <;> omega
  have htot : ∑ i : Fin (n * n), |(2 : ℤ) * (posOf B i).1.1 - ((n : ℤ) - 1)|
      = (n : ℤ) * G n := by
    rw [hcomp, sum_cell_row]
  linarith [hsplit, hbound, htot]

/-- The column-coordinate contribution of the tiles is at least `n G n - (n-1)`. -/
theorem sum_col_abs_lower [NeZero (n * n)] (B : Board n n) :
    (n : ℤ) * G n - ((n : ℤ) - 1)
      ≤ ∑ i ∈ tileSet n, |(2 : ℤ) * (posOf B i).2.1 - ((n : ℤ) - 1)| := by
  have hcomp : ∑ i : Fin (n * n), |(2 : ℤ) * (posOf B i).2.1 - ((n : ℤ) - 1)|
      = ∑ c : Cell n n, |(2 : ℤ) * (c.2.1 : ℤ) - ((n : ℤ) - 1)| := by
    have h := Equiv.sum_comp B.symm
      (fun c : Cell n n => |(2 : ℤ) * (c.2.1 : ℤ) - ((n : ℤ) - 1)|)
    simpa [posOf] using h
  have hsplit : ∑ i : Fin (n * n), |(2 : ℤ) * (posOf B i).2.1 - ((n : ℤ) - 1)|
      = (∑ i ∈ tileSet n, |(2 : ℤ) * (posOf B i).2.1 - ((n : ℤ) - 1)|)
        + |(2 : ℤ) * (posOf B 0).2.1 - ((n : ℤ) - 1)| := by
    rw [tileSet_eq_erase]
    exact (Finset.sum_erase_add (Finset.univ : Finset (Fin (n * n)))
      (fun i => |(2 : ℤ) * (posOf B i).2.1 - ((n : ℤ) - 1)|)
      (Finset.mem_univ 0)).symm
  have hbound : |(2 : ℤ) * (posOf B 0).2.1 - ((n : ℤ) - 1)| ≤ (n : ℤ) - 1 := by
    rw [abs_le]
    have hx : ((posOf B 0).2.1 : ℤ) < (n : ℤ) := by exact_mod_cast (posOf B 0).2.2
    constructor <;> omega
  have htot : ∑ i : Fin (n * n), |(2 : ℤ) * (posOf B i).2.1 - ((n : ℤ) - 1)|
      = (n : ℤ) * G n := by
    rw [hcomp, sum_cell_col]
  linarith [hsplit, hbound, htot]

/-- Pointwise estimate: twice a Manhattan step is bounded by the sum of the four
scaled distances to the centre. -/
theorem two_mul_cellDist_le (a b : Cell n n) :
    2 * (cellDist a b : ℤ)
      ≤ |(2 : ℤ) * (a.1.1 : ℤ) - ((n : ℤ) - 1)|
        + |(2 : ℤ) * (b.1.1 : ℤ) - ((n : ℤ) - 1)|
        + |(2 : ℤ) * (a.2.1 : ℤ) - ((n : ℤ) - 1)|
        + |(2 : ℤ) * (b.2.1 : ℤ) - ((n : ℤ) - 1)| := by
  have hcd : (cellDist a b : ℤ)
      = |(a.1.1 : ℤ) - (b.1.1 : ℤ)| + |(a.2.1 : ℤ) - (b.2.1 : ℤ)| := by
    simp only [cellDist]
    push_cast
    rw [cast_dist, cast_dist]
  rw [hcd]
  have hrow : 2 * |(a.1.1 : ℤ) - (b.1.1 : ℤ)|
      ≤ |(2 : ℤ) * (a.1.1 : ℤ) - ((n : ℤ) - 1)|
        + |(2 : ℤ) * (b.1.1 : ℤ) - ((n : ℤ) - 1)| := by
    have h := abs_sub_le ((2 : ℤ) * (a.1.1 : ℤ)) ((n : ℤ) - 1) ((2 : ℤ) * (b.1.1 : ℤ))
    have e : (2 : ℤ) * (a.1.1 : ℤ) - (2 : ℤ) * (b.1.1 : ℤ)
        = 2 * ((a.1.1 : ℤ) - (b.1.1 : ℤ)) := by ring
    rw [e, abs_mul] at h
    have e2 : |((n : ℤ) - 1) - (2 : ℤ) * (b.1.1 : ℤ)|
        = |(2 : ℤ) * (b.1.1 : ℤ) - ((n : ℤ) - 1)| := abs_sub_comm _ _
    rw [e2] at h
    norm_num at h
    exact h
  have hcol : 2 * |(a.2.1 : ℤ) - (b.2.1 : ℤ)|
      ≤ |(2 : ℤ) * (a.2.1 : ℤ) - ((n : ℤ) - 1)|
        + |(2 : ℤ) * (b.2.1 : ℤ) - ((n : ℤ) - 1)| := by
    have h := abs_sub_le ((2 : ℤ) * (a.2.1 : ℤ)) ((n : ℤ) - 1) ((2 : ℤ) * (b.2.1 : ℤ))
    have e : (2 : ℤ) * (a.2.1 : ℤ) - (2 : ℤ) * (b.2.1 : ℤ)
        = 2 * ((a.2.1 : ℤ) - (b.2.1 : ℤ)) := by ring
    rw [e, abs_mul] at h
    have e2 : |((n : ℤ) - 1) - (2 : ℤ) * (b.2.1 : ℤ)|
        = |(2 : ℤ) * (b.2.1 : ℤ) - ((n : ℤ) - 1)| := abs_sub_comm _ _
    rw [e2] at h
    norm_num at h
    exact h
  linarith

/-- **The target board has zero Manhattan distance.** -/
theorem D_target [NeZero (n * n)] : D (target n n) = 0 := by
  unfold D
  apply Finset.sum_eq_zero
  intro i _
  simp [posOf, cellDist]

/-- **Upper bound (step 5).** The Manhattan distance is at most `n³`. -/
theorem D_le_cube [NeZero (n * n)] (B : Board n n) : D B ≤ n ^ 3 := by
  have hsum : 2 * (D B : ℤ)
      = ∑ i ∈ tileSet n, 2 * (cellDist (posOf B i) (posOf (target n n) i) : ℤ) := by
    unfold D posOf
    push_cast
    rw [Finset.mul_sum]
  have hA : ∑ i ∈ tileSet n, |(2 : ℤ) * (posOf B i).1.1 - ((n : ℤ) - 1)|
      ≤ (n : ℤ) * G n :=
    sum_row_abs_le B
  have hB : ∑ i ∈ tileSet n, |(2 : ℤ) * (posOf (target n n) i).1.1 - ((n : ℤ) - 1)|
      ≤ (n : ℤ) * G n :=
    sum_row_abs_le (target n n)
  have hC : ∑ i ∈ tileSet n, |(2 : ℤ) * (posOf B i).2.1 - ((n : ℤ) - 1)|
      ≤ (n : ℤ) * G n :=
    sum_col_abs_le B
  have hD : ∑ i ∈ tileSet n, |(2 : ℤ) * (posOf (target n n) i).2.1 - ((n : ℤ) - 1)|
      ≤ (n : ℤ) * G n :=
    sum_col_abs_le (target n n)
  have hdecomp :
      ∑ i ∈ tileSet n,
          (|(2 : ℤ) * (posOf B i).1.1 - ((n : ℤ) - 1)|
            + |(2 : ℤ) * (posOf (target n n) i).1.1 - ((n : ℤ) - 1)|
            + |(2 : ℤ) * (posOf B i).2.1 - ((n : ℤ) - 1)|
            + |(2 : ℤ) * (posOf (target n n) i).2.1 - ((n : ℤ) - 1)|)
        = (∑ i ∈ tileSet n, |(2 : ℤ) * (posOf B i).1.1 - ((n : ℤ) - 1)|)
          + (∑ i ∈ tileSet n, |(2 : ℤ) * (posOf (target n n) i).1.1 - ((n : ℤ) - 1)|)
          + (∑ i ∈ tileSet n, |(2 : ℤ) * (posOf B i).2.1 - ((n : ℤ) - 1)|)
          + (∑ i ∈ tileSet n, |(2 : ℤ) * (posOf (target n n) i).2.1 - ((n : ℤ) - 1)|) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hpt : ∑ i ∈ tileSet n, 2 * (cellDist (posOf B i) (posOf (target n n) i) : ℤ)
      ≤ ∑ i ∈ tileSet n,
          (|(2 : ℤ) * (posOf B i).1.1 - ((n : ℤ) - 1)|
            + |(2 : ℤ) * (posOf (target n n) i).1.1 - ((n : ℤ) - 1)|
            + |(2 : ℤ) * (posOf B i).2.1 - ((n : ℤ) - 1)|
            + |(2 : ℤ) * (posOf (target n n) i).2.1 - ((n : ℤ) - 1)|) :=
    Finset.sum_le_sum (fun i _ => two_mul_cellDist_le (posOf B i) (posOf (target n n) i))
  have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
  have h2nG : 2 * ((n : ℤ) * G n) ≤ (n : ℤ) ^ 3 := by
    calc 2 * ((n : ℤ) * G n) = (n : ℤ) * (2 * G n) := by ring
      _ ≤ (n : ℤ) * (n : ℤ) ^ 2 := mul_le_mul_of_nonneg_left (two_mul_G_le_sq n) hn
      _ = (n : ℤ) ^ 3 := by ring
  have hfinal : 2 * (D B : ℤ) ≤ 2 * (n : ℤ) ^ 3 := by
    calc 2 * (D B : ℤ)
        = ∑ i ∈ tileSet n, 2 * (cellDist (posOf B i) (posOf (target n n) i) : ℤ) := hsum
      _ ≤ ∑ i ∈ tileSet n,
            (|(2 : ℤ) * (posOf B i).1.1 - ((n : ℤ) - 1)|
              + |(2 : ℤ) * (posOf (target n n) i).1.1 - ((n : ℤ) - 1)|
              + |(2 : ℤ) * (posOf B i).2.1 - ((n : ℤ) - 1)|
              + |(2 : ℤ) * (posOf (target n n) i).2.1 - ((n : ℤ) - 1)|) := hpt
      _ = (∑ i ∈ tileSet n, |(2 : ℤ) * (posOf B i).1.1 - ((n : ℤ) - 1)|)
          + (∑ i ∈ tileSet n, |(2 : ℤ) * (posOf (target n n) i).1.1 - ((n : ℤ) - 1)|)
          + (∑ i ∈ tileSet n, |(2 : ℤ) * (posOf B i).2.1 - ((n : ℤ) - 1)|)
          + (∑ i ∈ tileSet n, |(2 : ℤ) * (posOf (target n n) i).2.1 - ((n : ℤ) - 1)|)
        := hdecomp
      _ ≤ 4 * ((n : ℤ) * G n) := by linarith [hA, hB, hC, hD]
      _ = 2 * (2 * ((n : ℤ) * G n)) := by ring
      _ ≤ 2 * (n : ℤ) ^ 3 := by linarith [h2nG]
  have : (D B : ℤ) ≤ (n : ℤ) ^ 3 := by linarith
  have hnn : ((n ^ 3 : ℕ) : ℤ) = (n : ℤ) ^ 3 := by push_cast; ring
  rw [← hnn] at this
  exact_mod_cast this

/-- Rotation of a cell by 180°. -/
def rev (n : ℕ) : Cell n n ≃ Cell n n where
  toFun c := (⟨n - 1 - c.1.1, by have := c.1.2; omega⟩,
              ⟨n - 1 - c.2.1, by have := c.2.2; omega⟩)
  invFun c := (⟨n - 1 - c.1.1, by have := c.1.2; omega⟩,
               ⟨n - 1 - c.2.1, by have := c.2.2; omega⟩)
  left_inv c := by ext <;> simp only [] <;> omega
  right_inv c := by ext <;> simp only [] <;> omega

@[simp] theorem rev_apply_fst (n : ℕ) (c : Cell n n) : (rev n c).1.1 = n - 1 - c.1.1 := rfl

@[simp] theorem rev_apply_snd (n : ℕ) (c : Cell n n) : (rev n c).2.1 = n - 1 - c.2.1 := rfl

theorem rev_rev (n : ℕ) (c : Cell n n) : rev n (rev n c) = c := by
  ext <;> simp only [rev_apply_fst, rev_apply_snd] <;> omega

theorem rev_symm (n : ℕ) : (rev n).symm = rev n := by
  refine Equiv.ext (fun c => ?_)
  rw [Equiv.symm_apply_eq]
  exact (rev_rev n c).symm

/-- **Lower bound (step 5).** The board obtained by rotating the target by 180° has
Manhattan distance at least `n³ - 3n²`. -/
theorem D_rev_lower [NeZero (n * n)] :
    (n : ℤ) ^ 3 ≤ (D ((rev n).trans (target n n)) : ℤ) + 3 * (n : ℤ) ^ 2 := by
  have hB : ∀ i, ((rev n).trans (target n n)).symm i = rev n ((target n n).symm i) := by
    intro i
    rw [Equiv.symm_trans]
    simp only [Equiv.trans_apply, rev_symm]
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (fun h => NeZero.ne (n * n) (by simp [h]))
  have hcell : ∀ p : Cell n n,
      (cellDist (rev n p) p : ℤ)
        = |(2 : ℤ) * (p.1.1 : ℤ) - ((n : ℤ) - 1)|
          + |(2 : ℤ) * (p.2.1 : ℤ) - ((n : ℤ) - 1)| := by
    intro p
    have hx : ((n - 1 - p.1.1 : ℕ) : ℤ) = (n : ℤ) - 1 - (p.1.1 : ℤ) := by
      rw [Nat.cast_sub (by omega : p.1.1 ≤ n - 1), Nat.cast_sub hn1]
      ring
    have hy : ((n - 1 - p.2.1 : ℕ) : ℤ) = (n : ℤ) - 1 - (p.2.1 : ℤ) := by
      rw [Nat.cast_sub (by omega : p.2.1 ≤ n - 1), Nat.cast_sub hn1]
      ring
    simp only [cellDist, rev_apply_fst, rev_apply_snd]
    push_cast
    rw [cast_dist, cast_dist, hx, hy]
    have h1 : (n : ℤ) - 1 - (p.1.1 : ℤ) - (p.1.1 : ℤ)
        = -((2 : ℤ) * (p.1.1 : ℤ) - ((n : ℤ) - 1)) := by ring
    have h2 : (n : ℤ) - 1 - (p.2.1 : ℤ) - (p.2.1 : ℤ)
        = -((2 : ℤ) * (p.2.1 : ℤ) - ((n : ℤ) - 1)) := by ring
    rw [h1, abs_neg, h2, abs_neg]
  have hD : (D ((rev n).trans (target n n)) : ℤ)
      = (∑ i ∈ tileSet n, |(2 : ℤ) * (((target n n).symm i).1.1 : ℤ) - ((n : ℤ) - 1)|)
        + (∑ i ∈ tileSet n,
            |(2 : ℤ) * (((target n n).symm i).2.1 : ℤ) - ((n : ℤ) - 1)|) := by
    unfold D
    push_cast
    simp only [posOf]
    rw [Finset.sum_congr rfl (fun i _ => by rw [hB i, hcell ((target n n).symm i)])]
    rw [Finset.sum_add_distrib]
  have hrow : (n : ℤ) * G n - ((n : ℤ) - 1)
      ≤ ∑ i ∈ tileSet n,
          |(2 : ℤ) * (((target n n).symm i).1.1 : ℤ) - ((n : ℤ) - 1)| := by
    simpa only [posOf] using sum_row_abs_lower (target n n)
  have hcol : (n : ℤ) * G n - ((n : ℤ) - 1)
      ≤ ∑ i ∈ tileSet n,
          |(2 : ℤ) * (((target n n).symm i).2.1 : ℤ) - ((n : ℤ) - 1)| := by
    simpa only [posOf] using sum_col_abs_lower (target n n)
  have hG : (n : ℤ) ^ 2 ≤ 2 * G n + 1 := sq_le_two_mul_G_add n
  have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
  have hnpos : 0 < n := Nat.pos_of_ne_zero (fun h => NeZero.ne (n * n) (by simp [h]))
  have h2nG : (n : ℤ) ^ 3 - (n : ℤ) ≤ 2 * ((n : ℤ) * G n) := by
    have := mul_le_mul_of_nonneg_left hG hn
    nlinarith
  have hDlow : 2 * ((n : ℤ) * G n - ((n : ℤ) - 1))
      ≤ (D ((rev n).trans (target n n)) : ℤ) := by
    rw [hD]
    linarith [hrow, hcol]
  have hsq : (0 : ℤ) ≤ 3 * (n : ℤ) ^ 2 - 3 * (n : ℤ) + 2 := by
    have h1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hnpos
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ (n : ℤ) by omega)
      (show (0 : ℤ) ≤ (n : ℤ) - 1 by omega)]
  nlinarith [hDlow, h2nG, hsq]

end Zhong
