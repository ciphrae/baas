import Zhong.Basic
/-
Copyright (c) 2026 The Zhong formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhong formalisation contributors
-/

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

/-! ### How `act` moves the blank and the tiles -/

/-! ### Adjacent cells change the distance by one -/

/-! ### Proposition 7 -/

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
