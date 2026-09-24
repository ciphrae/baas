/-
Copyright (c) 2026 The Zhong formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhong formalisation contributors
-/
import Zhong.Orbit
import Zhong.Manhattan

/-!
# The expected Manhattan distance (step 4 of Proposition 9)

This file formalises the analytic part of step 4 in the proof of Proposition 9 of
Zhong (2023): the expected value of the Manhattan-distance potential `D` over the
orbit of the target board.

The combinatorial input is Parberry's symmetry statement [2] that, for `B` uniform in
the orbit `O`, the position `posOf B i` of a fixed tile `i` is uniform on the set of
cells.  We package this as the hypothesis `UniformMarginals` and show that it forces

`E[D] = (2/3) n³ - (5/3) n + 1`,

which is `(2/3) n³ + O(n)`, in particular `(2/3) n³ + O(n²)` as required by the paper.

The remaining, non-analytic step — proving `UniformMarginals` from the 15-puzzle group
theory — is isolated in `UniformMarginals` so that the arithmetic here is independent
of it.  See `PLAN.md` milestone M5.
-/

namespace Zhong

open Equiv

variable {n : ℕ}

/-! ### The row-distance sum -/

/-- `rowDistSum n a` is the sum of the distances from `a` to every index of `Fin n`,
i.e. `∑_{x < n} |x - a|`. -/
def rowDistSum (n : ℕ) (a : Fin n) : ℤ :=
  ∑ x : Fin n, (Nat.dist (x : ℕ) (a : ℕ) : ℤ)

/-- The row-distance sum written with absolute values. -/
theorem rowDistSum_eq_abs (n : ℕ) (a : Fin n) :
    rowDistSum n a = ∑ x : Fin n, |(x : ℤ) - (a : ℤ)| := by
  unfold rowDistSum
  apply Finset.sum_congr rfl
  intro x _
  rw [cast_dist]

/-- Sum of the reversed index `n - x` over `Fin n`. -/
theorem two_mul_sum_fin_sub (n : ℕ) :
    2 * (∑ a : Fin n, ((n : ℤ) - (a : ℤ))) = (n : ℤ) * ((n : ℤ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hlast : (((n + 1 : ℕ) : ℤ) - (n : ℤ)) = 1 := by push_cast; ring
      have hstep : ∀ a : Fin n, (((n + 1 : ℕ) : ℤ) - (a : ℤ)) = ((n : ℤ) - (a : ℤ)) + 1 := by
        intro a; push_cast; ring
      rw [Finset.sum_congr rfl (fun a _ => hstep a), Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hlast]
      have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
      rw [hcast]
      nlinarith [ih]

/-- `rowDistSum` splits over the last index. -/
theorem rowDistSum_castSucc (n : ℕ) (a : Fin n) :
    rowDistSum (n + 1) (Fin.castSucc a) = rowDistSum n a + ((n : ℤ) - (a : ℤ)) := by
  unfold rowDistSum
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  have hlast : (Nat.dist n (a : ℕ) : ℤ) = (n : ℤ) - (a : ℤ) := by
    rw [cast_dist, abs_of_nonneg]
    have : (a : ℤ) ≤ (n : ℤ) := by exact_mod_cast le_of_lt a.isLt
    linarith
  rw [hlast]

/-- `rowDistSum` at the last index. -/
theorem two_mul_rowDistSum_last (n : ℕ) :
    2 * rowDistSum (n + 1) (Fin.last n) = (n : ℤ) * ((n : ℤ) + 1) := by
  unfold rowDistSum
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [Nat.dist_self, Nat.cast_zero, add_zero]
  have hcongr : (∑ x : Fin n, (Nat.dist (x : ℕ) n : ℤ))
      = ∑ x : Fin n, ((n : ℤ) - (x : ℤ)) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [cast_dist, abs_sub_comm, abs_of_nonneg]
    have : (x : ℤ) ≤ (n : ℤ) := by exact_mod_cast le_of_lt x.isLt
    linarith
  rw [hcongr]
  exact two_mul_sum_fin_sub n

/-- The total of the row-distance sums: `∑_a ∑_x |x - a| = n(n²-1)/3`. -/
theorem three_mul_sum_rowDistSum (n : ℕ) :
    3 * (∑ a : Fin n, rowDistSum n a) = (n : ℤ) * ((n : ℤ) ^ 2 - 1) := by
  induction n with
  | zero => simp [rowDistSum]
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      have hsplit : (∑ a : Fin n, rowDistSum (n + 1) (Fin.castSucc a))
          = (∑ a : Fin n, rowDistSum n a) + ∑ a : Fin n, ((n : ℤ) - (a : ℤ)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        rw [rowDistSum_castSucc]
      rw [hsplit]
      have hR := two_mul_rowDistSum_last n
      have hU := two_mul_sum_fin_sub n
      have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
      rw [hcast]
      nlinarith [ih, hR, hU]

/-! ### Summing the cell distances -/

/-- The sum of the Manhattan distances from a fixed cell `p` to all cells. -/
theorem sum_cellDist (p : Cell n n) :
    ∑ c : Cell n n, (cellDist c p : ℤ)
      = (n : ℤ) * (rowDistSum n p.1 + rowDistSum n p.2) := by
  rw [Fintype.sum_prod_type]
  simp only [cellDist, Nat.cast_add]
  have hinner : ∀ x : Fin n,
      (∑ y : Fin n, ((Nat.dist (x : ℕ) (p.1 : ℕ) : ℤ) + (Nat.dist (y : ℕ) (p.2 : ℕ) : ℤ)))
        = (n : ℤ) * (Nat.dist (x : ℕ) (p.1 : ℕ) : ℤ) + rowDistSum n p.2 := by
    intro x
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    simp only [rowDistSum]
  rw [Finset.sum_congr rfl (fun x _ => hinner x)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  simp only [rowDistSum]
  ring

/-- The row-distance sum is nonnegative. -/
theorem rowDistSum_nonneg (n : ℕ) (a : Fin n) : 0 ≤ rowDistSum n a := by
  unfold rowDistSum
  positivity

/-- The row-distance sum is at most `n(n-1)`. -/
theorem rowDistSum_le (n : ℕ) (a : Fin n) :
    rowDistSum n a ≤ (n : ℤ) * ((n : ℤ) - 1) := by
  unfold rowDistSum
  calc ∑ x : Fin n, (Nat.dist (x : ℕ) (a : ℕ) : ℤ) ≤ ∑ _x : Fin n, ((n : ℤ) - 1) := by
        apply Finset.sum_le_sum
        intro x _
        rw [cast_dist, abs_le]
        have h1 := x.isLt
        have h2 := a.isLt
        constructor <;> omega
    _ = (n : ℤ) * ((n : ℤ) - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Reindexing a sum over the tiles by the cells: as `i` runs over `tileSet`, the target
position `(target n n).symm i` runs over all cells except the blank position. -/
theorem sum_tileSet_comp_target [NeZero (n * n)] (f : Cell n n → ℤ) :
    ∑ i ∈ tileSet n, f ((target n n).symm i)
      = (∑ c : Cell n n, f c) - f ((target n n).symm 0) := by
  rw [tileSet_eq_erase]
  have h0 : (0 : Fin (n * n)) ∈ (Finset.univ : Finset (Fin (n * n))) := Finset.mem_univ 0
  have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin (n * n)))
    (fun i => f ((target n n).symm i)) h0
  rw [← Equiv.sum_comp (target n n).symm f, ← hsum]
  ring

/-- The sum over the tiles of the total distance to their target cells. -/
theorem sum_tileSet_cellDist [NeZero (n * n)] :
    ∑ i ∈ tileSet n, ∑ c : Cell n n, (cellDist c ((target n n).symm i) : ℤ)
      = (n : ℤ) * (2 * (n : ℤ) * (∑ a : Fin n, rowDistSum n a)
          - rowDistSum n (posOf (target n n) 0).1
          - rowDistSum n (posOf (target n n) 0).2) := by
  have h1 : ∀ i : Fin (n * n),
      (∑ c : Cell n n, (cellDist c ((target n n).symm i) : ℤ))
        = (n : ℤ) * (rowDistSum n ((target n n).symm i).1
            + rowDistSum n ((target n n).symm i).2) :=
    fun i => sum_cellDist _
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  rw [sum_tileSet_comp_target (fun c => rowDistSum n c.1),
      sum_tileSet_comp_target (fun c => rowDistSum n c.2)]
  have hrow : (∑ c : Cell n n, rowDistSum n c.1)
      = (n : ℤ) * (∑ a : Fin n, rowDistSum n a) := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.mul_sum]
  have hcol : (∑ c : Cell n n, rowDistSum n c.2)
      = (n : ℤ) * (∑ a : Fin n, rowDistSum n a) := by
    rw [Fintype.sum_prod_type]
    simp [Finset.sum_const, Finset.card_univ, Finset.mul_sum]
  rw [hrow, hcol]
  simp only [posOf]
  ring

/-! ### Uniform marginals and the expected distance -/

/-- Uniform-marginal property of the orbit of `B`: each tile occupies each cell equally
often.  This is the symmetry statement of Parberry [2] used in step 4 of Proposition 9. -/
def UniformMarginals [NeZero (n * n)] (B : Board n n) : Prop :=
  ∀ i ∈ tileSet n, ∀ c : Cell n n,
    ((orbit B).filter (fun B' => posOf B' i = c)).card * (n * n) = (orbit B).card

/-- The average of `D` over the orbit of `B`, as a rational number. -/
noncomputable def avgD [NeZero (n * n)] (B : Board n n) : ℚ :=
  (∑ B' ∈ orbit B, (D B' : ℚ)) / ((orbit B).card : ℚ)

/-- Under uniform marginals, the total Manhattan distance over the orbit is determined by
the target geometry: `n² · ∑_{B' ∈ O} D B' = |O| · ∑_i ∑_c dist(c, p_i)`. -/
theorem sum_D_orbit_mul [NeZero (n * n)] {B : Board n n} (h : UniformMarginals B) :
    ((n * n : ℕ) : ℚ) * (∑ B' ∈ orbit B, (D B' : ℚ))
      = ((orbit B).card : ℚ)
          * (∑ i ∈ tileSet n, ∑ c : Cell n n, (cellDist c ((target n n).symm i) : ℚ)) := by
  have hD : ∀ B' : Board n n, (D B' : ℚ)
      = ∑ i ∈ tileSet n, (cellDist (posOf B' i) ((target n n).symm i) : ℚ) := by
    intro B'
    simp only [D, Nat.cast_sum]
  rw [Finset.sum_congr rfl (fun B' _ => hD B'), Finset.sum_comm]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_fiberwise' (orbit B) (fun B' => posOf B' i)
        (fun c => (cellDist c ((target n n).symm i) : ℚ))]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc := h i hi c
  have hcQ : (((orbit B).filter (fun B' => posOf B' i = c)).card : ℚ) * ((n * n : ℕ) : ℚ)
      = ((orbit B).card : ℚ) := by
    exact_mod_cast hc
  push_cast at hcQ ⊢
  nlinarith [hcQ]

/-- **Step 4 of Proposition 9, analytic part.**  Under uniform marginals the expected
Manhattan distance over the orbit is `(2/3) n³ + O(n)`. -/
theorem avgD_bounds [NeZero (n * n)] {B : Board n n} (h : UniformMarginals B) :
    (2 / 3 : ℚ) * (n : ℚ) ^ 3 - (8 / 3) * (n : ℚ) + 2 ≤ avgD B ∧
      avgD B ≤ (2 / 3 : ℚ) * (n : ℚ) ^ 3 - (2 / 3) * (n : ℚ) := by
  have hcardpos : 0 < (orbit B).card := Finset.card_pos.mpr ⟨B, mem_orbit_self B⟩
  have hcard : ((orbit B).card : ℚ) ≠ 0 := by positivity
  have hnQ : ((n * n : ℕ) : ℚ) ≠ 0 := by
    have := NeZero.ne (n * n)
    positivity
  have hmain := sum_D_orbit_mul h
  have havg : avgD B
      = (∑ i ∈ tileSet n, ∑ c : Cell n n, (cellDist c ((target n n).symm i) : ℚ))
        / ((n * n : ℕ) : ℚ) := by
    rw [avgD, div_eq_div_iff hcard hnQ]
    rw [mul_comm (∑ B' ∈ orbit B, (D B' : ℚ)) (((n * n : ℕ) : ℚ)),
        mul_comm (∑ i ∈ tileSet n, ∑ c : Cell n n, (cellDist c ((target n n).symm i) : ℚ))
          ((orbit B).card : ℚ)]
    exact hmain
  -- the arithmetic identity for the tile-distance total, cast to `ℚ`
  have hT := sum_tileSet_cellDist (n := n)
  have hTQ : (∑ i ∈ tileSet n, ∑ c : Cell n n, (cellDist c ((target n n).symm i) : ℚ))
      = (n : ℚ) * (2 * (n : ℚ) * (∑ a : Fin n, (rowDistSum n a : ℚ))
          - (rowDistSum n (posOf (target n n) 0).1 : ℚ)
          - (rowDistSum n (posOf (target n n) 0).2 : ℚ)) := by
    have := congrArg (fun z : ℤ => (z : ℚ)) hT
    push_cast at this
    exact this
  have hS : 3 * (∑ a : Fin n, (rowDistSum n a : ℚ)) = (n : ℚ) * ((n : ℚ) ^ 2 - 1) := by
    have := congrArg (fun z : ℤ => (z : ℚ)) (three_mul_sum_rowDistSum n)
    push_cast at this
    exact this
  have hR1nn : (0 : ℚ) ≤ (rowDistSum n (posOf (target n n) 0).1 : ℚ) := by
    exact_mod_cast rowDistSum_nonneg n _
  have hR2nn : (0 : ℚ) ≤ (rowDistSum n (posOf (target n n) 0).2 : ℚ) := by
    exact_mod_cast rowDistSum_nonneg n _
  have hR1le : (rowDistSum n (posOf (target n n) 0).1 : ℚ)
      ≤ (n : ℚ) * ((n : ℚ) - 1) := by
    exact_mod_cast rowDistSum_le n _
  have hR2le : (rowDistSum n (posOf (target n n) 0).2 : ℚ)
      ≤ (n : ℚ) * ((n : ℚ) - 1) := by
    exact_mod_cast rowDistSum_le n _
  rw [havg, hTQ]
  have hn2 : ((n * n : ℕ) : ℚ) = (n : ℚ) ^ 2 := by push_cast; ring
  have hSval : (∑ a : Fin n, (rowDistSum n a : ℚ)) = ((n : ℚ) ^ 3 - (n : ℚ)) / 3 := by
    nlinarith [hS]
  have hn0 : (0 : ℚ) ≤ (n : ℚ) := by positivity
  have hnpos : (0 : ℚ) < (n : ℚ) := by
    have : 0 < n := Nat.pos_of_ne_zero (fun hn => NeZero.ne (n * n) (by rw [hn, mul_zero]))
    exact_mod_cast this
  constructor
  · rw [hn2, le_div_iff₀ (pow_pos hnpos 2)]
    nlinarith [hSval, hR1le, hR2le, hn0]
  · rw [hn2, div_le_iff₀ (pow_pos hnpos 2)]
    nlinarith [hSval, hR1nn, hR2nn]

end Zhong

