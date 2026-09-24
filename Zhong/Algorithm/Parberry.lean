import Zhong.Algorithm.Lift
/-
Copyright (c) 2026 The Zhong formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhong formalisation contributors
-/

/-!
# Parberry's reduction-of-order algorithm (M7)

This file begins the tile-by-tile reduction-of-order routine of Proposition 4.  The
placement primitives of `Algorithm/Place.lean` move a tile *already inside* the active
`2 × m` strip.  The first ingredient needed for the row assembly is therefore a way to
*raise* a tile from an arbitrary row of the active region into the strip without
disturbing the cells already placed above it.

The construction is the explicit word `raiseStepR = U L D D R`.  If the blank sits at
`(a, y)` and the tile at `(a+1, y)`, then `U` pushes the tile up to `(a, y)` (the blank
moving to `(a+1, y)`); the detour `L D D R` then carries the blank around the tile to
`(a-1, y)`, so the pair `(blank, tile)` has moved up by one row.  Repeating this
`k` times raises the tile by `k` rows.

All the moves stay in rows `≥ a - k`, so cells above are fixed; this is the support
statement that lets the row assembly preserve already-placed tiles.
-/

namespace Zhong

open Equiv

variable {n m : ℕ}

local notation "c(" a "," b ")" => ((⟨a, by omega⟩ : Fin n), (⟨b, by omega⟩ : Fin m))

/-! ### Explicit neighbours -/

theorem nb_U (a y : ℕ) (h : a + 1 < n) (hy : y < m) :
    neighbor? c(a,y) Dir.U = some c(a+1,y) := by
  simp only [neighbor?]
  rw [dif_pos (show (c(a,y) : Cell n m).1.1 + 1 < n by simp only; omega)]

theorem nb_L (a y : ℕ) (h : y + 1 < m) (ha : a < n) :
    neighbor? c(a,y) Dir.L = some c(a,y+1) := by
  simp only [neighbor?]
  rw [dif_pos (show (c(a,y) : Cell n m).2.1 + 1 < m by simp only; omega)]

theorem nb_D (a y : ℕ) (h : 0 < a) (ha : a < n) (hy : y < m) :
    neighbor? c(a,y) Dir.D = some c(a-1,y) := by
  simp only [neighbor?]
  rw [if_pos (show 0 < (c(a,y) : Cell n m).1.1 by simp only; omega)]

theorem nb_R (a y : ℕ) (h : 0 < y) (ha : a < n) (hy : y < m) :
    neighbor? c(a,y) Dir.R = some c(a,y-1) := by
  simp only [neighbor?]
  rw [if_pos (show 0 < (c(a,y) : Cell n m).2.1 by simp only; omega)]

/-! ### The one-row raise step -/

/-- The raise step `U L D D R`: with the blank at `(a,y)` and the tile at `(a+1,y)` it
moves the tile to `(a,y)` and the blank to `(a-1,y)`. -/
def raiseStepR : List Dir := [Dir.U, Dir.L, Dir.D, Dir.D, Dir.R]

/-- The permutation induced by the raise step. -/
theorem raiseStepR_permOf (a y : ℕ) (ha : a + 1 < n) (ha0 : 0 < a) (hy : y + 1 < m) :
    permOf c(a,y) raiseStepR
      = Equiv.swap c(a,y) c(a+1,y) * (Equiv.swap c(a+1,y) c(a+1,y+1)
        * (Equiv.swap c(a+1,y+1) c(a,y+1) * (Equiv.swap c(a,y+1) c(a-1,y+1)
        * Equiv.swap c(a-1,y+1) c(a-1,y)))) := by
  have hU : neighbor? c(a,y) Dir.U = some c(a+1,y) := nb_U a y ha (by omega)
  have hL : neighbor? c(a+1,y) Dir.L = some c(a+1,y+1) := nb_L (a+1) y hy (by omega)
  have hD : neighbor? c(a+1,y+1) Dir.D = some c(a,y+1) := nb_D (a+1) (y+1) (by omega) (by omega) (by omega)
  have hD2 : neighbor? c(a,y+1) Dir.D = some c(a-1,y+1) := nb_D a (y+1) (by omega) (by omega) (by omega)
  have hR : neighbor? c(a-1,y+1) Dir.R = some c(a-1,y) := nb_R (a-1) (y+1) (by omega) (by omega) (by omega)
  unfold raiseStepR
  rw [permOf_cons_of_neighbor? hU, permOf_cons_of_neighbor? hL, permOf_cons_of_neighbor? hD,
      permOf_cons_of_neighbor? hD2, permOf_cons_of_neighbor? hR]
  simp only [permOf_nil, mul_one]

/-- The raise step sends its own cell to the tile's cell. -/
theorem raiseStepR_apply_base (a y : ℕ) (ha : a + 1 < n) (ha0 : 0 < a) (hy : y + 1 < m) :
    permOf c(a,y) raiseStepR c(a,y) = c(a+1,y) := by
  rw [raiseStepR_permOf a y ha ha0 hy]
  simp only [Equiv.Perm.mul_apply]
  have n1 : c(a,y) ≠ c(a-1,y+1) := by
    intro h; simp only [Prod.mk.injEq, Fin.mk.injEq] at h; omega
  have n2 : c(a,y) ≠ c(a-1,y) := by
    intro h; simp only [Prod.mk.injEq, Fin.mk.injEq] at h; omega
  have n3 : c(a,y) ≠ c(a,y+1) := by
    intro h; simp only [Prod.mk.injEq, Fin.mk.injEq] at h; omega
  have n4 : c(a,y) ≠ c(a+1,y+1) := by
    intro h; simp only [Prod.mk.injEq, Fin.mk.injEq] at h; omega
  have n5 : c(a,y) ≠ c(a+1,y) := by
    intro h; simp only [Prod.mk.injEq, Fin.mk.injEq] at h; omega
  rw [Equiv.swap_apply_of_ne_of_ne n1 n2, Equiv.swap_apply_of_ne_of_ne n3 n1,
    Equiv.swap_apply_of_ne_of_ne n4 n3, Equiv.swap_apply_of_ne_of_ne n5 n4,
    Equiv.swap_apply_left]

/-- The raise step fixes every cell in a row strictly above its support. -/
theorem raiseStepR_fixes (a y : ℕ) (ha : a + 1 < n) (ha0 : 1 < a) (hy : y + 1 < m)
    {z : Cell n m} (hz : z.1.val ≤ a - 2) : permOf c(a,y) raiseStepR z = z := by
  rw [raiseStepR_permOf a y ha (by omega) hy]
  simp only [Equiv.Perm.mul_apply]
  have n1 : z ≠ c(a-1,y+1) := by
    intro h; have := congrArg (fun w : Cell n m => w.1.val) h; simp only at this; omega
  have n2 : z ≠ c(a-1,y) := by
    intro h; have := congrArg (fun w : Cell n m => w.1.val) h; simp only at this; omega
  have n3 : z ≠ c(a,y+1) := by
    intro h; have := congrArg (fun w : Cell n m => w.1.val) h; simp only at this; omega
  have n4 : z ≠ c(a+1,y+1) := by
    intro h; have := congrArg (fun w : Cell n m => w.1.val) h; simp only at this; omega
  have n5 : z ≠ c(a+1,y) := by
    intro h; have := congrArg (fun w : Cell n m => w.1.val) h; simp only at this; omega
  have n6 : z ≠ c(a,y) := by
    intro h; have := congrArg (fun w : Cell n m => w.1.val) h; simp only at this; omega
  have hS1 : Equiv.swap c(a,y) c(a+1,y) z = z := Equiv.swap_apply_of_ne_of_ne n6 n5
  have hS2 : Equiv.swap c(a+1,y) c(a+1,y+1) z = z := Equiv.swap_apply_of_ne_of_ne n5 n4
  have hS3 : Equiv.swap c(a+1,y+1) c(a,y+1) z = z := Equiv.swap_apply_of_ne_of_ne n4 n3
  have hS4 : Equiv.swap c(a,y+1) c(a-1,y+1) z = z := Equiv.swap_apply_of_ne_of_ne n3 n1
  have hS5 : Equiv.swap c(a-1,y+1) c(a-1,y) z = z := Equiv.swap_apply_of_ne_of_ne n1 n2
  rw [hS5, hS4, hS3, hS2, hS1]

/-- Applicability of the raise step. -/
theorem raiseStepR_applicable (a y : ℕ) (ha : a + 1 < n) (ha0 : 0 < a) (hy : y + 1 < m) :
    ApplicableFrom c(a,y) raiseStepR := by
  have hU : neighbor? c(a,y) Dir.U = some c(a+1,y) := nb_U a y ha (by omega)
  have hL : neighbor? c(a+1,y) Dir.L = some c(a+1,y+1) := nb_L (a+1) y hy (by omega)
  have hD : neighbor? c(a+1,y+1) Dir.D = some c(a,y+1) := nb_D (a+1) (y+1) (by omega) (by omega) (by omega)
  have hD2 : neighbor? c(a,y+1) Dir.D = some c(a-1,y+1) := nb_D a (y+1) (by omega) (by omega) (by omega)
  have hR : neighbor? c(a-1,y+1) Dir.R = some c(a-1,y) := nb_R (a-1) (y+1) (by omega) (by omega) (by omega)
  unfold raiseStepR
  refine ⟨c(a+1,y), hU, ?_⟩
  rw [applicableFrom_cons_of_neighbor? hL]
  refine ⟨c(a,y+1), hD, ?_⟩
  rw [applicableFrom_cons_of_neighbor? hD2]
  refine ⟨c(a-1,y), hR, ?_⟩
  exact trivial

/-- The trace of the raise step. -/
theorem raiseStepR_trace (a y : ℕ) (ha : a + 1 < n) (ha0 : 0 < a) (hy : y + 1 < m) :
    trace c(a,y) raiseStepR = c(a-1,y) := by
  have hU : neighbor? c(a,y) Dir.U = some c(a+1,y) := nb_U a y ha (by omega)
  have hL : neighbor? c(a+1,y) Dir.L = some c(a+1,y+1) := nb_L (a+1) y hy (by omega)
  have hD : neighbor? c(a+1,y+1) Dir.D = some c(a,y+1) := nb_D (a+1) (y+1) (by omega) (by omega) (by omega)
  have hD2 : neighbor? c(a,y+1) Dir.D = some c(a-1,y+1) := nb_D a (y+1) (by omega) (by omega) (by omega)
  have hR : neighbor? c(a-1,y+1) Dir.R = some c(a-1,y) := nb_R (a-1) (y+1) (by omega) (by omega) (by omega)
  unfold raiseStepR
  rw [trace_cons_of_neighbor? hU, trace_cons_of_neighbor? hL, trace_cons_of_neighbor? hD,
      trace_cons_of_neighbor? hD2, trace_cons_of_neighbor? hR]
  rfl

/-! ### The terminal word `U L D`

After the tile has been raised to row `r+2` with the blank at `r+1`, the word `U L D` moves
the tile to row `r+1` and parks the blank at `(r+1, y+1)` (still inside the strip). -/

/-- The terminal word `U L D`. -/
def walkEnd : List Dir := [Dir.U, Dir.L, Dir.D]

theorem walkEnd_permOf (a y : ℕ) (ha : a + 1 < n) (hy : y + 1 < m) :
    permOf c(a,y) walkEnd
      = Equiv.swap c(a,y) c(a+1,y) * (Equiv.swap c(a+1,y) c(a+1,y+1)
        * Equiv.swap c(a+1,y+1) c(a,y+1)) := by
  have hU : neighbor? c(a,y) Dir.U = some c(a+1,y) := nb_U a y ha (by omega)
  have hL : neighbor? c(a+1,y) Dir.L = some c(a+1,y+1) := nb_L (a+1) y hy (by omega)
  have hD : neighbor? c(a+1,y+1) Dir.D = some c(a,y+1) := nb_D (a+1) (y+1) (by omega) (by omega) (by omega)
  unfold walkEnd
  rw [permOf_cons_of_neighbor? hU, permOf_cons_of_neighbor? hL, permOf_cons_of_neighbor? hD]
  simp only [permOf_nil, mul_one]

theorem walkEnd_applicable (a y : ℕ) (ha : a + 1 < n) (hy : y + 1 < m) :
    ApplicableFrom c(a,y) walkEnd := by
  have hU : neighbor? c(a,y) Dir.U = some c(a+1,y) := nb_U a y ha (by omega)
  have hL : neighbor? c(a+1,y) Dir.L = some c(a+1,y+1) := nb_L (a+1) y hy (by omega)
  have hD : neighbor? c(a+1,y+1) Dir.D = some c(a,y+1) := nb_D (a+1) (y+1) (by omega) (by omega) (by omega)
  unfold walkEnd
  refine ⟨c(a+1,y), hU, ?_⟩
  rw [applicableFrom_cons_of_neighbor? hL]
  refine ⟨c(a,y+1), hD, ?_⟩
  exact trivial

theorem walkEnd_trace (a y : ℕ) (ha : a + 1 < n) (hy : y + 1 < m) :
    trace c(a,y) walkEnd = c(a,y+1) := by
  have hU : neighbor? c(a,y) Dir.U = some c(a+1,y) := nb_U a y ha (by omega)
  have hL : neighbor? c(a+1,y) Dir.L = some c(a+1,y+1) := nb_L (a+1) y hy (by omega)
  have hD : neighbor? c(a+1,y+1) Dir.D = some c(a,y+1) := nb_D (a+1) (y+1) (by omega) (by omega) (by omega)
  unfold walkEnd
  rw [trace_cons_of_neighbor? hU, trace_cons_of_neighbor? hL, trace_cons_of_neighbor? hD]
  rfl

/-- The terminal word sends its own cell to the tile's cell. -/
theorem walkEnd_apply_base (a y : ℕ) (ha : a + 1 < n) (hy : y + 1 < m) :
    permOf c(a,y) walkEnd c(a,y) = c(a+1,y) := by
  rw [walkEnd_permOf a y ha hy]
  simp only [Equiv.Perm.mul_apply]
  have n1 : c(a,y) ≠ c(a+1,y+1) := by
    intro h; simp only [Prod.mk.injEq, Fin.mk.injEq] at h; omega
  have n2 : c(a,y) ≠ c(a,y+1) := by
    intro h; simp only [Prod.mk.injEq, Fin.mk.injEq] at h; omega
  have n3 : c(a,y) ≠ c(a+1,y) := by
    intro h; simp only [Prod.mk.injEq, Fin.mk.injEq] at h; omega
  rw [Equiv.swap_apply_of_ne_of_ne n1 n2, Equiv.swap_apply_of_ne_of_ne n3 n1,
    Equiv.swap_apply_left]

/-- The terminal word fixes every cell in a row strictly above its support. -/
theorem walkEnd_fixes (a y : ℕ) (ha : a + 1 < n) (hy : y + 1 < m)
    {z : Cell n m} (hz : z.1.val + 1 ≤ a) : permOf c(a,y) walkEnd z = z := by
  rw [walkEnd_permOf a y ha hy]
  simp only [Equiv.Perm.mul_apply]
  have n1 : z ≠ c(a+1,y+1) := by
    intro h; have := congrArg (fun w : Cell n m => w.1.val) h; simp only at this; omega
  have n2 : z ≠ c(a,y+1) := by
    intro h; have := congrArg (fun w : Cell n m => w.1.val) h; simp only at this; omega
  have n3 : z ≠ c(a+1,y) := by
    intro h; have := congrArg (fun w : Cell n m => w.1.val) h; simp only at this; omega
  have n4 : z ≠ c(a,y) := by
    intro h; have := congrArg (fun w : Cell n m => w.1.val) h; simp only at this; omega
  have hS1 : Equiv.swap c(a,y) c(a+1,y) z = z := Equiv.swap_apply_of_ne_of_ne n4 n3
  have hS2 : Equiv.swap c(a+1,y) c(a+1,y+1) z = z := Equiv.swap_apply_of_ne_of_ne n3 n1
  have hS3 : Equiv.swap c(a+1,y+1) c(a,y+1) z = z := Equiv.swap_apply_of_ne_of_ne n1 n2
  rw [hS3, hS2, hS1]

/-! ### The recursive walk -/

/-- `walkAuxR a y k` starts with the blank at `(a,y)` and the tile at `(a+1,y)`, performs
`k` raise steps and then the terminal word, so the tile ends at `(a-k, y)`. -/
def walkAuxR : ℕ → ℕ → ℕ → List Dir
  | _a, _y, 0 => walkEnd
  | a, y, k + 1 => raiseStepR ++ walkAuxR (a - 1) y k

@[simp] theorem walkAuxR_zero (a y : ℕ) : walkAuxR a y 0 = walkEnd := rfl

@[simp] theorem walkAuxR_succ (a y k : ℕ) :
    walkAuxR a y (k + 1) = raiseStepR ++ walkAuxR (a - 1) y k := rfl

/-- Specification of the recursive walk. -/
theorem walkAuxR_spec (a y k : ℕ) (ha : a + 1 < n) (hk : k ≤ a) (hy : y + 1 < m) :
    ApplicableFrom c(a,y) (walkAuxR a y k) ∧
    trace c(a,y) (walkAuxR a y k) = c(a-k,y+1) ∧
    (∀ z : Cell n m, z.1.val + k + 1 ≤ a → permOf c(a,y) (walkAuxR a y k) z = z) ∧
    permOf c(a,y) (walkAuxR a y k) c(a-k,y) = c(a+1,y) := by
  induction k generalizing a with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [walkAuxR] using walkEnd_applicable a y ha hy
      · simpa [walkAuxR] using walkEnd_trace a y ha hy
      · intro z hz
        simpa [walkAuxR] using walkEnd_fixes a y ha hy (by omega)
      · simpa [walkAuxR] using walkEnd_apply_base a y ha hy
  | succ k ih =>
      have ha2 : 0 < a := by omega
      have hstep := raiseStepR_applicable a y ha ha2 hy
      have htrace := raiseStepR_trace a y ha ha2 hy
      have hIH := ih (a := a - 1) (by omega) (by omega)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [walkAuxR_succ, applicableFrom_append, htrace]
        exact ⟨hstep, hIH.1⟩
      · rw [walkAuxR_succ, trace_append, htrace, hIH.2.1]
        exact Prod.ext (Fin.ext (by simp only; omega)) rfl
      · intro z hz
        rw [walkAuxR_succ, permOf_append, htrace, Equiv.Perm.mul_apply]
        rw [hIH.2.2.1 z (by omega), raiseStepR_fixes a y ha (by omega) hy (by omega)]
      · rw [walkAuxR_succ, permOf_append, htrace, Equiv.Perm.mul_apply]
        have harg : ((⟨a - (k + 1), by omega⟩ : Fin n), (⟨y, by omega⟩ : Fin m))
            = ((⟨a - 1 - k, by omega⟩ : Fin n), (⟨y, by omega⟩ : Fin m)) :=
          Prod.ext (Fin.ext (by simp only; omega)) rfl
        rw [harg, hIH.2.2.2]
        rw [show ((⟨a - 1 + 1, by omega⟩ : Fin n), (⟨y, by omega⟩ : Fin m))
              = ((⟨a, by omega⟩ : Fin n), (⟨y, by omega⟩ : Fin m)) from
            Prod.ext (Fin.ext (by simp only; omega)) rfl,
          raiseStepR_apply_base a y ha (by omega) hy]

/-- The trace set of the raise step stays in the two columns `y, y+1`. -/
theorem raiseStepR_traceSet_col (a y : ℕ) (ha : a + 1 < n) (ha0 : 0 < a) (hy : y + 1 < m) :
    ∀ z ∈ traceSet c(a,y) raiseStepR, y ≤ z.2.val ∧ z.2.val ≤ y + 1 := by
  have hU : neighbor? c(a,y) Dir.U = some c(a+1,y) := nb_U a y ha (by omega)
  have hL : neighbor? c(a+1,y) Dir.L = some c(a+1,y+1) := nb_L (a+1) y hy (by omega)
  have hD : neighbor? c(a+1,y+1) Dir.D = some c(a,y+1) := nb_D (a+1) (y+1) (by omega) (by omega) (by omega)
  have hD2 : neighbor? c(a,y+1) Dir.D = some c(a-1,y+1) := nb_D a (y+1) (by omega) (by omega) (by omega)
  have hR : neighbor? c(a-1,y+1) Dir.R = some c(a-1,y) := nb_R (a-1) (y+1) (by omega) (by omega) (by omega)
  intro z hz
  unfold raiseStepR at hz
  rw [traceSet_cons_of_neighbor? hU, traceSet_cons_of_neighbor? hL, traceSet_cons_of_neighbor? hD,
      traceSet_cons_of_neighbor? hD2, traceSet_cons_of_neighbor? hR, traceSet_nil] at hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only <;> omega

/-- The trace set of the terminal word stays in the two columns `y, y+1`. -/
theorem walkEnd_traceSet_col (a y : ℕ) (ha : a + 1 < n) (hy : y + 1 < m) :
    ∀ z ∈ traceSet c(a,y) walkEnd, y ≤ z.2.val ∧ z.2.val ≤ y + 1 := by
  have hU : neighbor? c(a,y) Dir.U = some c(a+1,y) := nb_U a y ha (by omega)
  have hL : neighbor? c(a+1,y) Dir.L = some c(a+1,y+1) := nb_L (a+1) y hy (by omega)
  have hD : neighbor? c(a+1,y+1) Dir.D = some c(a,y+1) := nb_D (a+1) (y+1) (by omega) (by omega) (by omega)
  intro z hz
  unfold walkEnd at hz
  rw [traceSet_cons_of_neighbor? hU, traceSet_cons_of_neighbor? hL, traceSet_cons_of_neighbor? hD,
      traceSet_nil] at hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only <;> omega

/-- The trace set of the recursive walk stays in the two columns `y, y+1`. -/
theorem walkAuxR_traceSet_col (a y k : ℕ) (ha : a + 1 < n) (hk : k ≤ a) (hy : y + 1 < m) :
    ∀ z ∈ traceSet c(a,y) (walkAuxR a y k), y ≤ z.2.val ∧ z.2.val ≤ y + 1 := by
  induction k generalizing a with
  | zero => simpa [walkAuxR] using walkEnd_traceSet_col a y ha hy
  | succ k ih =>
      rw [walkAuxR_succ, traceSet_append]
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact raiseStepR_traceSet_col a y ha (by omega) hy z hz
      · rw [raiseStepR_trace a y ha (by omega) hy] at hz
        exact ih (a-1) (by omega) (by omega) z hz

/-! ### The blank never visits the tile during navigation

To raise a tile we first bring the blank to the cell directly above it.  The navigation
must not disturb the tile, so we need to know which cells the blank visits.  For a
straight vertical or horizontal run these are easy to describe. -/

theorem traceSet_replicate_D (r i j : ℕ) (hir : i ≤ r) (hr : r < n) (hc : j < m) :
    ∀ z ∈ traceSet c(r,j) (List.replicate i Dir.D),
      z.2 = (⟨j, hc⟩ : Fin m) ∧ r - i ≤ z.1.val ∧ z.1.val ≤ r := by
  induction i generalizing r with
  | zero =>
      intro z hz
      rw [List.replicate_zero, traceSet_nil, Finset.mem_singleton] at hz
      subst hz
      exact ⟨rfl, by change r - 0 ≤ r; omega, le_rfl⟩
  | succ i ih =>
      rw [List.replicate_succ]
      have hD : neighbor? c(r,j) Dir.D = some c(r-1,j) := nb_D r j (by omega) hr hc
      rw [traceSet_cons_of_neighbor? hD]
      intro z hz
      rcases Finset.mem_insert.mp hz with hz | hz
      · subst hz; exact ⟨rfl, by change r - (i + 1) ≤ r; omega, le_rfl⟩
      · obtain ⟨h1, h2, h3⟩ := ih (r-1) (by omega) (by omega) z hz
        exact ⟨h1, by omega, by omega⟩

theorem traceSet_replicate_U (r i j : ℕ) (hri : r + i < n) (hc : j < m) :
    ∀ z ∈ traceSet c(r,j) (List.replicate i Dir.U),
      z.2 = (⟨j, hc⟩ : Fin m) ∧ r ≤ z.1.val ∧ z.1.val ≤ r + i := by
  induction i generalizing r with
  | zero =>
      intro z hz
      rw [List.replicate_zero, traceSet_nil, Finset.mem_singleton] at hz
      subst hz
      exact ⟨rfl, le_rfl, by change r ≤ r + 0; omega⟩
  | succ i ih =>
      rw [List.replicate_succ]
      have hU : neighbor? c(r,j) Dir.U = some c(r+1,j) := nb_U r j (by omega) hc
      rw [traceSet_cons_of_neighbor? hU]
      intro z hz
      rcases Finset.mem_insert.mp hz with hz | hz
      · subst hz; exact ⟨rfl, le_rfl, by change r ≤ r + (i + 1); omega⟩
      · obtain ⟨h1, h2, h3⟩ := ih (r+1) (by omega) z hz
        exact ⟨h1, by omega, by omega⟩

theorem traceSet_replicate_L (r i j : ℕ) (hci : j + i < m) (hr : r < n) :
    ∀ z ∈ traceSet c(r,j) (List.replicate i Dir.L), z.1 = (⟨r, hr⟩ : Fin n) := by
  induction i generalizing j with
  | zero =>
      intro z hz
      rw [List.replicate_zero, traceSet_nil, Finset.mem_singleton] at hz
      subst hz
      rfl
  | succ i ih =>
      rw [List.replicate_succ]
      have hL : neighbor? c(r,j) Dir.L = some c(r,j+1) := nb_L r j (by omega) hr
      rw [traceSet_cons_of_neighbor? hL]
      intro z hz
      rcases Finset.mem_insert.mp hz with hz | hz
      · subst hz; rfl
      · exact ih (j+1) (by omega) z hz

theorem traceSet_replicate_R (r i j : ℕ) (hic : i ≤ j) (hr : r < n) (hc : j < m) :
    ∀ z ∈ traceSet c(r,j) (List.replicate i Dir.R), z.1 = (⟨r, hr⟩ : Fin n) := by
  induction i generalizing j with
  | zero =>
      intro z hz
      rw [List.replicate_zero, traceSet_nil, Finset.mem_singleton] at hz
      subst hz
      rfl
  | succ i ih =>
      rw [List.replicate_succ]
      have hR : neighbor? c(r,j) Dir.R = some c(r,j-1) := nb_R r j (by omega) hr hc
      rw [traceSet_cons_of_neighbor? hR]
      intro z hz
      rcases Finset.mem_insert.mp hz with hz | hz
      · subst hz; rfl
      · exact ih (j-1) (by omega) (by omega) z hz

theorem moveXWord_traceSet (x0 y0 x : ℕ) (hx : x < n) (hx0 : x0 < n) (hy0 : y0 < m) :
    ∀ z ∈ traceSet c(x0,y0) (moveXWord x0 x),
      z.2 = (⟨y0, hy0⟩ : Fin m) ∧ min x0 x ≤ z.1.val ∧ z.1.val ≤ max x0 x := by
  unfold moveXWord
  by_cases h : x < x0
  · rw [if_pos h]
    intro z hz
    obtain ⟨h1, h2, h3⟩ := traceSet_replicate_D x0 (x0 - x) y0 (by omega) hx0 hy0 z hz
    exact ⟨h1, by omega, by omega⟩
  · rw [if_neg h]
    intro z hz
    obtain ⟨h1, h2, h3⟩ := traceSet_replicate_U x0 (x - x0) y0 (by omega) hy0 z hz
    exact ⟨h1, by omega, by omega⟩

theorem moveYWord_traceSet (r y0 y : ℕ) (hy : y < m) (hr : r < n) (hy0 : y0 < m) :
    ∀ z ∈ traceSet c(r,y0) (moveYWord y0 y), z.1 = (⟨r, hr⟩ : Fin n) := by
  unfold moveYWord
  by_cases h : y < y0
  · rw [if_pos h]
    exact traceSet_replicate_R r (y0 - y) y0 (by omega) hr hy0
  · rw [if_neg h]
    exact traceSet_replicate_L r (y - y0) y0 (by omega) hr

/-- Column bounds for a rightward run. -/
theorem traceSet_replicate_R_col (r i j : ℕ) (hic : i ≤ j) (hr : r < n) (hc : j < m) :
    ∀ z ∈ traceSet c(r,j) (List.replicate i Dir.R), j - i ≤ z.2.val ∧ z.2.val ≤ j := by
  induction i generalizing j with
  | zero =>
      intro z hz
      rw [List.replicate_zero, traceSet_nil, Finset.mem_singleton] at hz
      subst hz
      exact ⟨by change j - 0 ≤ j; omega, le_rfl⟩
  | succ i ih =>
      rw [List.replicate_succ]
      have hR : neighbor? c(r,j) Dir.R = some c(r,j-1) := nb_R r j (by omega) hr hc
      rw [traceSet_cons_of_neighbor? hR]
      intro z hz
      rcases Finset.mem_insert.mp hz with hz | hz
      · subst hz
        exact ⟨by change j - (i + 1) ≤ j; omega, le_rfl⟩
      · obtain ⟨h1, h2⟩ := ih (j-1) (by omega) (by omega) z hz
        exact ⟨by omega, by omega⟩

/-- Column bounds for a leftward run. -/
theorem traceSet_replicate_L_col (r i j : ℕ) (hci : j + i < m) (hr : r < n) :
    ∀ z ∈ traceSet c(r,j) (List.replicate i Dir.L), j ≤ z.2.val ∧ z.2.val ≤ j + i := by
  induction i generalizing j with
  | zero =>
      intro z hz
      rw [List.replicate_zero, traceSet_nil, Finset.mem_singleton] at hz
      subst hz
      exact ⟨le_rfl, by change j ≤ j + 0; omega⟩
  | succ i ih =>
      rw [List.replicate_succ]
      have hL : neighbor? c(r,j) Dir.L = some c(r,j+1) := nb_L r j (by omega) hr
      rw [traceSet_cons_of_neighbor? hL]
      intro z hz
      rcases Finset.mem_insert.mp hz with hz | hz
      · subst hz
        exact ⟨le_rfl, by change j ≤ j + (i + 1); omega⟩
      · obtain ⟨h1, h2⟩ := ih (j+1) (by omega) z hz
        exact ⟨by omega, by omega⟩

/-- Column bounds for a horizontal run. -/
theorem moveYWord_traceSet_col (r y0 y : ℕ) (hy : y < m) (hr : r < n) (hy0 : y0 < m) :
    ∀ z ∈ traceSet c(r,y0) (moveYWord y0 y),
      min y0 y ≤ z.2.val ∧ z.2.val ≤ max y0 y := by
  unfold moveYWord
  by_cases h : y < y0
  · rw [if_pos h]
    intro z hz
    obtain ⟨h1, h2⟩ := traceSet_replicate_R_col r (y0 - y) y0 (by omega) hr hy0 z hz
    exact ⟨by omega, by omega⟩
  · rw [if_neg h]
    intro z hz
    obtain ⟨h1, h2⟩ := traceSet_replicate_L_col r (y - y0) y0 (by omega) hr z hz
    exact ⟨by omega, by omega⟩

/-- Column bounds for `moveToWord`. -/
theorem moveToWord_traceSet_col (x0 y0 x y : ℕ) (hx : x < n) (hy : y < m) (hx0 : x0 < n)
    (hy0 : y0 < m) :
    ∀ z ∈ traceSet c(x0,y0) (moveToWord x0 y0 x y),
      min y0 y ≤ z.2.val ∧ z.2.val ≤ max y0 y := by
  intro z hz
  rw [moveToWord, traceSet_append] at hz
  rcases Finset.mem_union.mp hz with hz | hz
  · obtain ⟨h1, _⟩ := moveXWord_traceSet x0 y0 x hx hx0 hy0 z hz
    rw [h1]
    exact ⟨min_le_left _ _, le_max_left _ _⟩
  · rw [trace_moveXWord x0 y0 x hx hx0 hy0] at hz
    exact moveYWord_traceSet_col x y0 y hy (by omega) hy0 z hz

/-- A word whose trace stays in columns `≥ lo` fixes every cell of a smaller column. -/
theorem permOf_fixes_of_traceSet_col {p : Cell n m} {σ : List Dir} {lo : ℕ}
    (h : ∀ z ∈ traceSet p σ, lo ≤ z.2.val) :
    ∀ z : Cell n m, z.2.val < lo → permOf p σ z = z := by
  intro z hz
  apply permOf_apply_of_not_mem_traceSet
  intro hmem
  have := h z hmem
  omega

/-- Row bounds for `moveToWord`. -/
theorem moveToWord_traceSet_row (x0 y0 x y : ℕ) (hx : x < n) (hy : y < m) (hx0 : x0 < n)
    (hy0 : y0 < m) :
    ∀ z ∈ traceSet c(x0,y0) (moveToWord x0 y0 x y),
      min x0 x ≤ z.1.val ∧ z.1.val ≤ max x0 x := by
  intro z hz
  rw [moveToWord, traceSet_append] at hz
  rcases Finset.mem_union.mp hz with hz | hz
  · obtain ⟨_, h1, h2⟩ := moveXWord_traceSet x0 y0 x hx hx0 hy0 z hz
    exact ⟨h1, h2⟩
  · rw [trace_moveXWord x0 y0 x hx hx0 hy0] at hz
    have h1 := moveYWord_traceSet x y0 y hy (by omega) hy0 z hz
    rw [h1]
    exact ⟨min_le_right _ _, le_max_right _ _⟩

/-- A word whose trace stays in rows `≥ lo` fixes every cell of a smaller row. -/
theorem permOf_fixes_of_traceSet_row {p : Cell n m} {σ : List Dir} {lo : ℕ}
    (h : ∀ z ∈ traceSet p σ, lo ≤ z.1.val) :
    ∀ z : Cell n m, z.1.val < lo → permOf p σ z = z := by
  intro z hz
  apply permOf_apply_of_not_mem_traceSet
  intro hmem
  have := h z hmem
  omega

/-- **`moveToWord` confined to rows `≥ lo`.**  If both the starting cell and the destination
lie in rows `≥ lo`, then every cell of a row `< lo` is fixed. -/
theorem moveToWord_fixes_of_row_lt {x0 y0 x y lo : ℕ} (hx : x < n) (hy : y < m)
    (hx0 : x0 < n) (hy0 : y0 < m) (hlo0 : lo ≤ x0) (hlox : lo ≤ x) :
    ∀ z : Cell n m, z.1.val < lo →
      permOf c(x0,y0) (moveToWord x0 y0 x y) z = z := by
  apply permOf_fixes_of_traceSet_row
  intro z hz
  obtain ⟨hmin, _⟩ := moveToWord_traceSet_row x0 y0 x y hx hy hx0 hy0 z hz
  omega

/-! ### Navigating the blank above the tile

`navToAbove` is the case where the blank starts in a different column from the tile (or
already above it): the word `moveToWord` moves the blank down/up its column and then across
row `x-1`, never visiting the tile. -/

theorem length_moveToWord_le (x0 y0 x y : ℕ) (hx : x < n) (hx0 : x0 < n) (hy : y < m)
    (hy0 : y0 < m) : (moveToWord x0 y0 x y).length ≤ n + m := by
  rw [length_moveToWord]
  have h1 : Nat.dist x0 x ≤ n := by rw [Nat.dist_eq_max_sub_min]; omega
  have h2 : Nat.dist y0 y ≤ m := by rw [Nat.dist_eq_max_sub_min]; omega
  omega

theorem navToAbove (r x0 y0 x y : ℕ) (hx : x < n) (hx0 : x0 < n) (hy : y < m) (hy0 : y0 < m)
    (hx0r : r + 1 ≤ x0) (hxr : r + 1 ≤ x - 1)
    (havoid : y0 ≠ y ∨ x0 < x) :
    ApplicableFrom c(x0,y0) (moveToWord x0 y0 (x-1) y) ∧
    trace c(x0,y0) (moveToWord x0 y0 (x-1) y) = c(x-1,y) ∧
    permOf c(x0,y0) (moveToWord x0 y0 (x-1) y) c(x,y) = c(x,y) ∧
    (∀ z : Cell n m, z.1.val ≤ r → permOf c(x0,y0) (moveToWord x0 y0 (x-1) y) z = z) ∧
    (∀ z ∈ traceSet c(x0,y0) (moveToWord x0 y0 (x-1) y),
      min y0 y ≤ z.2.val ∧ z.2.val ≤ max y0 y) := by
  have hx1 : x - 1 < n := by omega
  have happ := applicableFrom_moveToWord x0 y0 (x-1) y hx1 hy hx0 hy0
  have htr := trace_moveToWord x0 y0 (x-1) y hx1 hy hx0 hy0
  have hbound : ∀ z ∈ traceSet c(x0,y0) (moveToWord x0 y0 (x-1) y),
      (z.2 = (⟨y0, hy0⟩ : Fin m) ∧ min x0 (x-1) ≤ z.1.val ∧ z.1.val ≤ max x0 (x-1))
        ∨ z.1.val = x - 1 := by
    intro z hz
    rw [moveToWord, traceSet_append] at hz
    rcases Finset.mem_union.mp hz with hz | hz
    · left
      exact moveXWord_traceSet x0 y0 (x-1) hx1 hx0 hy0 z hz
    · right
      rw [trace_moveXWord x0 y0 (x-1) hx1 hx0 hy0] at hz
      have := moveYWord_traceSet (x-1) y0 y hy (by omega) hy0 z hz
      exact congrArg Fin.val this
  have hcol := moveToWord_traceSet_col x0 y0 (x-1) y hx1 hy hx0 hy0
  refine ⟨happ, htr, ?_, ?_, hcol⟩
  · apply permOf_apply_of_not_mem_traceSet
    intro hmem
    rcases hbound (c(x,y)) hmem with ⟨h1, h2, h3⟩ | h3
    · rcases havoid with hyy | hxx
      · have : y = y0 := by
          have hc := congrArg Fin.val h1
          simpa only [Fin.val_mk] using hc
        exact hyy this.symm
      · have hz1 : (c(x,y) : Cell n m).1.val = x := rfl
        rw [hz1, max_eq_right (by omega : x0 ≤ x - 1)] at h3
        omega
    · have hz1 : (c(x,y) : Cell n m).1.val = x := rfl
      omega
  · intro z hz
    apply permOf_apply_of_not_mem_traceSet
    intro hmem
    rcases hbound z hmem with ⟨h1, h2, h3⟩ | h3
    · have : r + 1 ≤ min x0 (x - 1) := by omega
      omega
    · omega

theorem navAbove (r x0 y0 x y : ℕ) (hx : x < n) (hx0 : x0 < n) (hy : y < m) (hy0 : y0 < m)
    (hx0r : r + 1 ≤ x0) (hxr : r + 1 ≤ x - 1) (_hm : 2 ≤ m) (hy1 : y + 1 < m)
    (hne : ¬ (x0 = x ∧ y0 = y)) :
    ∃ σ : List Dir, ApplicableFrom c(x0,y0) σ ∧ trace c(x0,y0) σ = c(x-1,y) ∧
      permOf c(x0,y0) σ c(x,y) = c(x,y) ∧
      (∀ z : Cell n m, z.1.val ≤ r → permOf c(x0,y0) σ z = z) ∧
      (∀ z ∈ traceSet c(x0,y0) σ, min y0 y ≤ z.2.val ∧ z.2.val ≤ max y0 (y+1)) ∧
      σ.length ≤ 2 * n + 2 * m + 1 := by
  by_cases hdet : y0 = y ∧ x0 > x
  · obtain ⟨hyy, hx0x⟩ := hdet
    subst y0
    have hL : neighbor? c(x0,y) Dir.L = some c(x0,y+1) := nb_L x0 y hy1 hx0
    obtain ⟨happ, htr, hfix, hsup, hcol⟩ :=
      navToAbove r x0 (y+1) x y hx hx0 hy (by omega) hx0r hxr (Or.inl (by omega))
    refine ⟨Dir.L :: moveToWord x0 (y+1) (x-1) y, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (applicableFrom_cons_of_neighbor? (σ := moveToWord x0 (y+1) (x-1) y) hL).mpr happ
    · exact (trace_cons_of_neighbor? (σ := moveToWord x0 (y+1) (x-1) y) hL).trans htr
    · rw [permOf_cons_of_neighbor? (σ := moveToWord x0 (y+1) (x-1) y) hL, Equiv.Perm.mul_apply, hfix,
        Equiv.swap_apply_of_ne_of_ne
          (by intro hh; have h2 : x = x0 := by
                simpa only [Fin.val_mk] using congrArg (fun w : Cell n m => w.1.val) hh
              omega)
          (by intro hh; have h2 : x = x0 := by
                simpa only [Fin.val_mk] using congrArg (fun w : Cell n m => w.1.val) hh
              omega)]
    · intro z hz
      rw [permOf_cons_of_neighbor? (σ := moveToWord x0 (y+1) (x-1) y) hL, Equiv.Perm.mul_apply, hsup z hz,
        Equiv.swap_apply_of_ne_of_ne
          (by intro hh; have h2 : z.1.val = x0 := by
                simpa only [Fin.val_mk] using congrArg (fun w : Cell n m => w.1.val) hh
              omega)
          (by intro hh; have h2 : z.1.val = x0 := by
                simpa only [Fin.val_mk] using congrArg (fun w : Cell n m => w.1.val) hh
              omega)]
    · intro z hz
      rw [traceSet_cons_of_neighbor? (σ := moveToWord x0 (y+1) (x-1) y) hL] at hz
      rcases Finset.mem_insert.mp hz with hz | hz
      · subst hz
        exact ⟨by simp, by simp⟩
      · obtain ⟨h1, h2⟩ := hcol z hz
        exact ⟨by omega, by omega⟩
    · rw [List.length_cons]
      have := length_moveToWord_le x0 (y+1) (x-1) y (by omega) hx0 hy (by omega)
      omega
  · have havoid : y0 ≠ y ∨ x0 < x := by
      rcases lt_trichotomy x0 x with h | h | h
      · exact Or.inr h
      · subst h
        by_cases hyy : y0 = y
        · exact absurd ⟨rfl, hyy⟩ hne
        · exact Or.inl hyy
      · by_cases hyy : y0 = y
        · exact absurd ⟨hyy, h⟩ hdet
        · exact Or.inl hyy
    obtain ⟨happ, htr, hfix, hsup, hcol⟩ := navToAbove r x0 y0 x y hx hx0 hy hy0 hx0r hxr havoid
    refine ⟨_, happ, htr, hfix, hsup, ?_, ?_⟩
    · intro z hz
      obtain ⟨h1, h2⟩ := hcol z hz
      exact ⟨by omega, by omega⟩
    · have := length_moveToWord_le x0 y0 (x-1) y (by omega) hx0 hy hy0
      omega

@[simp] theorem raiseStepR_length : raiseStepR.length = 5 := rfl

@[simp] theorem walkEnd_length : walkEnd.length = 3 := rfl

theorem walkAuxR_length (a y k : ℕ) : (walkAuxR a y k).length = 5 * k + 3 := by
  induction k generalizing a with
  | zero => simp [walkAuxR]
  | succ k ih => rw [walkAuxR_succ, List.length_append, raiseStepR_length, ih]; ring

/-! ### Raising a tile into the strip

Combining the navigation with the recursive walk: given the blank anywhere in the active
region (`x0 ≥ r+1`) and a tile at `(x,y)` with `x ≥ r+2`, we obtain an `O(n)`-move word
that moves the tile to `(r+1,y)` and parks the blank at `(r+1,y+1)`, fixing every cell in
rows `≤ r`. -/

theorem raiseTile (r x0 y0 x y : ℕ) (hx : x < n) (hx0 : x0 < n) (hy : y < m) (hy1 : y + 1 < m)
    (hy0 : y0 < m)
    (hm : 2 ≤ m) (hxr : r + 2 ≤ x) (hx0r : r + 1 ≤ x0) (hne : ¬ (x0 = x ∧ y0 = y)) :
    ∃ σ : List Dir, ApplicableFrom c(x0,y0) σ ∧
      trace c(x0,y0) σ = c(r+1,y+1) ∧
      permOf c(x0,y0) σ c(r+1,y) = c(x,y) ∧
      (∀ z : Cell n m, z.1.val ≤ r → permOf c(x0,y0) σ z = z) ∧
      (∀ z ∈ traceSet c(x0,y0) σ, min y0 y ≤ z.2.val ∧ z.2.val ≤ max y0 (y+1)) ∧
      σ.length ≤ (2 * n + 2 * m + 1) + (5 * (x - r) + 3) := by
  have hxr1 : r + 1 ≤ x - 1 := by omega
  obtain ⟨σn, happn, htrn, hfixn, hsupn, hcoln, hlen⟩ :=
    navAbove r x0 y0 x y hx hx0 hy hy0 hx0r hxr1 hm hy1 hne
  have hx' : (x - 1) + 1 = x := by omega
  have hwalk := walkAuxR_spec (x-1) y (x-r-2) (by rw [hx']; exact hx) (by omega) hy1
  have hcell : ((⟨(x-1)-(x-r-2), by omega⟩ : Fin n), (⟨y+1, by omega⟩ : Fin m))
      = ((⟨r+1, by omega⟩ : Fin n), (⟨y+1, by omega⟩ : Fin m)) :=
    Prod.ext (Fin.ext (by simp only; omega)) rfl
  have hcell2 : ((⟨r+1, by omega⟩ : Fin n), (⟨y, by omega⟩ : Fin m))
      = ((⟨(x-1)-(x-r-2), by omega⟩ : Fin n), (⟨y, by omega⟩ : Fin m)) :=
    Prod.ext (Fin.ext (by simp only; omega)) rfl
  have hcell3 : ((⟨(x-1)+1, by omega⟩ : Fin n), (⟨y, by omega⟩ : Fin m))
      = ((⟨x, by omega⟩ : Fin n), (⟨y, by omega⟩ : Fin m)) :=
    Prod.ext (Fin.ext (by simp only; omega)) rfl
  have hwalkcol := walkAuxR_traceSet_col (x-1) y (x-r-2) (by rw [hx']; exact hx) (by omega) hy1
  have hcol : ∀ z ∈ traceSet c(x0,y0) (σn ++ walkAuxR (x-1) y (x-r-2)),
      min y0 y ≤ z.2.val ∧ z.2.val ≤ max y0 (y+1) := by
    intro z hz
    rw [traceSet_append, htrn] at hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hcoln z hz
    · obtain ⟨h1, h2⟩ := hwalkcol z hz
      exact ⟨by omega, by omega⟩
  refine ⟨σn ++ walkAuxR (x-1) y (x-r-2), ?_, ?_, ?_, ?_, hcol, ?_⟩
  · rw [applicableFrom_append, htrn]; exact ⟨happn, hwalk.1⟩
  · rw [trace_append, htrn, hwalk.2.1, hcell]
  · rw [permOf_append, htrn, hcell2, Equiv.Perm.mul_apply, hwalk.2.2.2, hcell3, hfixn]
  · intro z hz
    rw [permOf_append, htrn, Equiv.Perm.mul_apply, hwalk.2.2.1 z (by omega), hsupn z hz]
  · rw [List.length_append, walkAuxR_length]; omega

/-- The mirror image of `raiseTile`: when the tile lies in the last column (`0 < y`) the
blank is parked on the *left* of the raised tile.  It is obtained by transporting `raiseTile`
along the column reflection `colRefl`. -/
theorem raiseTileLeft (r x0 y0 x y : ℕ) (hx : x < n) (hx0 : x0 < n) (hy : y < m)
    (hy0 : y0 < m) (hm : 2 ≤ m) (hypos : 0 < y) (hxr : r + 2 ≤ x) (hx0r : r + 1 ≤ x0)
    (hne : ¬ (x0 = x ∧ y0 = y)) (lo : ℕ) (hlo0 : lo ≤ y0) (hloy : lo ≤ y - 1) :
    ∃ σ : List Dir, ApplicableFrom c(x0,y0) σ ∧
      trace c(x0,y0) σ = c(r+1,y-1) ∧
      permOf c(x0,y0) σ c(r+1,y) = c(x,y) ∧
      (∀ z : Cell n m, z.1.val ≤ r → permOf c(x0,y0) σ z = z) ∧
      (∀ z : Cell n m, z.2.val < lo → permOf c(x0,y0) σ z = z) ∧
      σ.length ≤ (2 * n + 2 * m + 1) + (5 * (x - r) + 3) := by
  have hy' : (m - 1 - y) + 1 < m := by omega
  have hy0' : m - 1 - y0 < m := by omega
  obtain ⟨σ, hap, htr, heff, hfix, hcol, hlen⟩ :=
    raiseTile r x0 (m - 1 - y0) x (m - 1 - y) hx hx0 (by omega) hy' hy0' hm hxr hx0r (by
      intro h
      exact hne ⟨h.1, by omega⟩)
  have hstep : ∀ (c : Cell n m) (δ : Dir) (c' : Cell n m),
      neighbor? c δ = some c' → neighbor? (colRefl n m c) (reflDir δ) = some (colRefl n m c') := by
    intro c δ c' hc'
    have := neighbor?_colRefl c δ
    rw [hc'] at this
    simpa using this
  have hp : colRefl n m c(x0, m-1-y0) = c(x0,y0) := by
    rw [colRefl_apply]; congr 1; apply Fin.ext; rw [Fin.val_rev]; simp only; omega
  have htrc : colRefl n m c(r+1, (m-1-y)+1) = c(r+1,y-1) := by
    rw [colRefl_apply]; congr 1; apply Fin.ext; rw [Fin.val_rev]; simp only; omega
  have hqc : colRefl n m c(r+1, m-1-y) = c(r+1,y) := by
    rw [colRefl_apply]; congr 1; apply Fin.ext; rw [Fin.val_rev]; simp only; omega
  have htc : colRefl n m c(x, m-1-y) = c(x,y) := by
    rw [colRefl_apply]; congr 1; apply Fin.ext; rw [Fin.val_rev]; simp only; omega
  have hzz : ∀ z : Cell n m, colRefl n m (colRefl n m z) = z := by
    intro z; rw [colRefl_apply, colRefl_apply]; congr 1; exact Fin.rev_rev z.2
  have hrow : ∀ z : Cell n m, (colRefl n m z).1.val = z.1.val := by
    intro z; rfl
  refine ⟨σ.map reflDir, ?_, ?_, ?_, ?_, ?_, by simpa using hlen⟩
  · have := applicableFrom_map_of_neighbor_map (ι := colRefl n m) (f := reflDir) hstep hap
    simpa [hp] using this
  · have := trace_map_of_neighbor_map (ι := colRefl n m) (f := reflDir) hstep
      (c(x0, m-1-y0)) σ hap
    rw [htr] at this
    simpa [hp, htrc] using this
  · have := permOf_map_apply_of_neighbor_map (ι := colRefl n m) (f := reflDir)
      (colRefl n m).injective hstep (c(x0, m-1-y0)) σ hap (c(r+1, m-1-y))
    rw [heff] at this
    simpa [hp, hqc, htc] using this
  · intro z hz
    have := permOf_map_apply_of_neighbor_map (ι := colRefl n m) (f := reflDir)
      (colRefl n m).injective hstep (c(x0, m-1-y0)) σ hap (colRefl n m z)
    rw [hfix (colRefl n m z) (by rw [hrow]; exact hz), hzz] at this
    simpa [hp] using this
  · intro z hz
    rw [← hp]
    have hmap := permOf_map_apply_of_neighbor_map (ι := colRefl n m) (f := reflDir)
      (colRefl n m).injective hstep (c(x0, m-1-y0)) σ hap (colRefl n m z)
    rw [hzz z] at hmap
    have hznot : colRefl n m z ∉ traceSet c(x0, m-1-y0) σ := by
      intro hmem
      obtain ⟨_, h2⟩ := hcol (colRefl n m z) hmem
      rw [colRefl_apply] at h2
      simp only [Fin.val_rev] at h2
      omega
    rw [permOf_apply_of_not_mem_traceSet hznot] at hmap
    rw [hmap, hzz z]

/-! ### The per-tile placement theorem

Combining `raiseTile` with the placement primitives of `Algorithm/Place.lean` gives the
per-tile step of Parberry's reduction-of-order algorithm.  The tile is first raised into
the lower row of the active `2 × m` strip (rows `r, r+1`) and then placed into the target
cell `(r, yc)` of the strip's upper row.  The placement primitives only touch the strip,
so every other cell of rows `≤ r` — in particular every already-placed tile — is fixed.

After `raiseTile` the blank sits immediately to the right of the raised tile, so the two
cells have opposite colours and only two of the four placement cases can occur: the tile
and the target share a colour (`A = C ≠ P`, the chain `p → a → v → c → p`), or the target
shares the blank's colour (`A ≠ P = C`, the chain `p → u → c → a → p`).  The auxiliary is
chosen in the strip's lower row, where the row assembly has not yet placed anything. -/

end Zhong
