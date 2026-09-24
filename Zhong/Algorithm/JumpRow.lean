/-
Copyright (c) 2026 The Zhong formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhong formalisation contributors
-/
import Zhong.Algorithm.Jump

/-!
# The same-row jump (Lemma 2 of Zhong 2023, remaining orientation)

Lemma 2 of Zhong (2023) swaps the blank with a tile at odd Manhattan distance in a
`2 × m` or `m × 2` board.  `Algorithm/Jump.lean` handles the case where the target is in
the other row at even column offset, and `Algorithm/Orient.lean` transports that to the
other row/column.  The case where the blank and the target lie in the *same* row (equivalently
the same column of an `m × 2` board) is not reachable from those by a board symmetry.

This file builds it explicitly.  The basic gadget `row0Gadget` is a closed walk at `(0,c)`
acting as the three-cycle `(0,c+1) → (0,c+3) → (0,c+2)`; chaining shifted copies produces the
reverse cycle of row `0`, and a final horizontal run turns it into the transposition of the
blank with the tile at `(0, c + 2l + 1)`.
-/

namespace Zhong

open Equiv

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

variable {m : ℕ}

/-- The head `U L D L L U R` of the same-row gadget. -/
def row0Head : List Dir := [Dir.U, Dir.L, Dir.D, Dir.L, Dir.L, Dir.U, Dir.R]

/-- The square loop `D R U L` used inside the same-row gadget. -/
def row0Loop : List Dir := [Dir.D, Dir.R, Dir.U, Dir.L]

/-- The same-row gadget `τ ρ τ⁻¹`, a closed walk at its base. -/
def row0Gadget : List Dir := row0Head ++ row0Loop ++ invWord row0Head

/-! ### The head `U L D L L U R` -/

/-- The explicit permutation of the head `U L D L L U R` starting at `(0,c)`. -/
theorem permOf_row0Head {c : Fin m} (hc : c.val + 3 < m) :
    permOf (top c) row0Head
      = Equiv.swap (top c) (bot c)
        * Equiv.swap (bot c) (bot (⟨c.val + 1, by omega⟩ : Fin m))
        * Equiv.swap (bot (⟨c.val + 1, by omega⟩ : Fin m))
            (top (⟨c.val + 1, by omega⟩ : Fin m))
        * Equiv.swap (top (⟨c.val + 1, by omega⟩ : Fin m))
            (top (⟨c.val + 2, by omega⟩ : Fin m))
        * Equiv.swap (top (⟨c.val + 2, by omega⟩ : Fin m))
            (top (⟨c.val + 3, by omega⟩ : Fin m))
        * Equiv.swap (top (⟨c.val + 3, by omega⟩ : Fin m))
            (bot (⟨c.val + 3, by omega⟩ : Fin m))
        * Equiv.swap (bot (⟨c.val + 3, by omega⟩ : Fin m))
            (bot (⟨c.val + 2, by omega⟩ : Fin m)) := by
  have hc1 : c.val + 1 < m := by omega
  have hc2 : c.val + 2 < m := by omega
  have hc3 : c.val + 3 < m := hc
  have h1 : neighbor? (top c) Dir.U = some (bot c) := by
    simp [top, bot]
  have h2 : neighbor? (bot c) Dir.L = some (bot (⟨c.val + 1, hc1⟩ : Fin m)) := by
    simpa [bot] using (neighbor?_mk_L (x := (1 : Fin 2)) (y := c) hc1)
  have h3 : neighbor? (bot (⟨c.val + 1, hc1⟩ : Fin m)) Dir.D
      = some (top (⟨c.val + 1, hc1⟩ : Fin m)) := by
    simpa [top, bot] using
      (neighbor?_mk_D (x := (1 : Fin 2)) (y := (⟨c.val + 1, hc1⟩ : Fin m)) (by decide))
  have h4 : neighbor? (top (⟨c.val + 1, hc1⟩ : Fin m)) Dir.L
      = some (top (⟨c.val + 2, hc2⟩ : Fin m)) := by
    simpa [top] using (neighbor?_mk_L (x := (0 : Fin 2))
      (y := (⟨c.val + 1, hc1⟩ : Fin m)) (by simp only; omega))
  have h5 : neighbor? (top (⟨c.val + 2, hc2⟩ : Fin m)) Dir.L
      = some (top (⟨c.val + 3, hc3⟩ : Fin m)) := by
    simpa [top] using (neighbor?_mk_L (x := (0 : Fin 2))
      (y := (⟨c.val + 2, hc2⟩ : Fin m)) (by simp only; omega))
  have h6 : neighbor? (top (⟨c.val + 3, hc3⟩ : Fin m)) Dir.U
      = some (bot (⟨c.val + 3, hc3⟩ : Fin m)) := by
    simpa [top, bot] using
      (neighbor?_mk_U (x := (0 : Fin 2)) (y := (⟨c.val + 3, hc3⟩ : Fin m)) (by decide))
  have h7 : neighbor? (bot (⟨c.val + 3, hc3⟩ : Fin m)) Dir.R
      = some (bot (⟨c.val + 2, hc2⟩ : Fin m)) := by
    simpa [bot] using (neighbor?_mk_R (x := (1 : Fin 2))
      (y := (⟨c.val + 3, hc3⟩ : Fin m)) (by simp only [Fin.val_mk]; omega))
  unfold row0Head
  rw [permOf_cons_of_neighbor? h1, permOf_cons_of_neighbor? h2,
      permOf_cons_of_neighbor? h3, permOf_cons_of_neighbor? h4,
      permOf_cons_of_neighbor? h5, permOf_cons_of_neighbor? h6,
      permOf_cons_of_neighbor? h7, permOf_nil, mul_one]
  rw [bot_fin hc1 (by omega), bot_fin hc2 (by omega), bot_fin hc3 (by omega),
      top_fin hc1 (by omega), top_fin hc2 (by omega), top_fin hc3 (by omega)]
  group

/-- The head `U L D L L U R` sends `(0,c+1)` to `(0,c+2)`. -/
theorem row0Head_apply_top1 {c : Fin m} (hc : c.val + 3 < m) :
    permOf (top c) row0Head (top (⟨c.val + 1, by omega⟩ : Fin m))
      = top (⟨c.val + 2, by omega⟩ : Fin m) := by
  rw [permOf_row0Head hc]
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  rw [Equiv.swap_apply_of_ne_of_ne (a := bot (⟨c.val + 3, by omega⟩ : Fin m))
        (b := bot (⟨c.val + 2, by omega⟩ : Fin m))
        (show top (⟨c.val + 1, by omega⟩ : Fin m) ≠ bot (⟨c.val + 3, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega)
        (show top (⟨c.val + 1, by omega⟩ : Fin m) ≠ bot (⟨c.val + 2, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega),
      Equiv.swap_apply_of_ne_of_ne (a := top (⟨c.val + 3, by omega⟩ : Fin m))
        (b := bot (⟨c.val + 3, by omega⟩ : Fin m))
        (show top (⟨c.val + 1, by omega⟩ : Fin m) ≠ top (⟨c.val + 3, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega)
        (show top (⟨c.val + 1, by omega⟩ : Fin m) ≠ bot (⟨c.val + 3, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega),
      Equiv.swap_apply_of_ne_of_ne (a := top (⟨c.val + 2, by omega⟩ : Fin m))
        (b := top (⟨c.val + 3, by omega⟩ : Fin m))
        (show top (⟨c.val + 1, by omega⟩ : Fin m) ≠ top (⟨c.val + 2, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega)
        (show top (⟨c.val + 1, by omega⟩ : Fin m) ≠ top (⟨c.val + 3, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega),
      Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (a := bot (⟨c.val + 1, by omega⟩ : Fin m))
        (b := top (⟨c.val + 1, by omega⟩ : Fin m))
        (show top (⟨c.val + 2, by omega⟩ : Fin m) ≠ bot (⟨c.val + 1, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega)
        (show top (⟨c.val + 2, by omega⟩ : Fin m) ≠ top (⟨c.val + 1, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega),
      Equiv.swap_apply_of_ne_of_ne (a := bot c) (b := bot (⟨c.val + 1, by omega⟩ : Fin m))
        (show top (⟨c.val + 2, by omega⟩ : Fin m) ≠ bot c by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega)
        (show top (⟨c.val + 2, by omega⟩ : Fin m) ≠ bot (⟨c.val + 1, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega),
      Equiv.swap_apply_of_ne_of_ne (a := top c) (b := bot c)
        (show top (⟨c.val + 2, by omega⟩ : Fin m) ≠ top c by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega)
        (show top (⟨c.val + 2, by omega⟩ : Fin m) ≠ bot c by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega)]

/-- The head `U L D L L U R` sends `(0,c+2)` to `(0,c+3)`. -/
theorem row0Head_apply_top2 {c : Fin m} (hc : c.val + 3 < m) :
    permOf (top c) row0Head (top (⟨c.val + 2, by omega⟩ : Fin m))
      = top (⟨c.val + 3, by omega⟩ : Fin m) := by
  rw [permOf_row0Head hc]
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  rw [Equiv.swap_apply_of_ne_of_ne (a := bot (⟨c.val + 3, by omega⟩ : Fin m))
        (b := bot (⟨c.val + 2, by omega⟩ : Fin m))
        (show top (⟨c.val + 2, by omega⟩ : Fin m) ≠ bot (⟨c.val + 3, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega)
        (show top (⟨c.val + 2, by omega⟩ : Fin m) ≠ bot (⟨c.val + 2, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega),
      Equiv.swap_apply_of_ne_of_ne (a := top (⟨c.val + 3, by omega⟩ : Fin m))
        (b := bot (⟨c.val + 3, by omega⟩ : Fin m))
        (show top (⟨c.val + 2, by omega⟩ : Fin m) ≠ top (⟨c.val + 3, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega)
        (show top (⟨c.val + 2, by omega⟩ : Fin m) ≠ bot (⟨c.val + 3, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega),
      Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (a := top (⟨c.val + 1, by omega⟩ : Fin m))
        (b := top (⟨c.val + 2, by omega⟩ : Fin m))
        (show top (⟨c.val + 3, by omega⟩ : Fin m) ≠ top (⟨c.val + 1, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega)
        (show top (⟨c.val + 3, by omega⟩ : Fin m) ≠ top (⟨c.val + 2, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega),
      Equiv.swap_apply_of_ne_of_ne (a := bot (⟨c.val + 1, by omega⟩ : Fin m))
        (b := top (⟨c.val + 1, by omega⟩ : Fin m))
        (show top (⟨c.val + 3, by omega⟩ : Fin m) ≠ bot (⟨c.val + 1, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega)
        (show top (⟨c.val + 3, by omega⟩ : Fin m) ≠ top (⟨c.val + 1, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega),
      Equiv.swap_apply_of_ne_of_ne (a := bot c) (b := bot (⟨c.val + 1, by omega⟩ : Fin m))
        (show top (⟨c.val + 3, by omega⟩ : Fin m) ≠ bot c by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega)
        (show top (⟨c.val + 3, by omega⟩ : Fin m) ≠ bot (⟨c.val + 1, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega),
      Equiv.swap_apply_of_ne_of_ne (a := top c) (b := bot c)
        (show top (⟨c.val + 3, by omega⟩ : Fin m) ≠ top c by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega)
        (show top (⟨c.val + 3, by omega⟩ : Fin m) ≠ bot c by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega)]

/-- The head `U L D L L U R` sends `(1,c+1)` to `(0,c+1)`. -/
theorem row0Head_apply_bot1 {c : Fin m} (hc : c.val + 3 < m) :
    permOf (top c) row0Head (bot (⟨c.val + 1, by omega⟩ : Fin m))
      = top (⟨c.val + 1, by omega⟩ : Fin m) := by
  rw [permOf_row0Head hc]
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  rw [Equiv.swap_apply_of_ne_of_ne (a := bot (⟨c.val + 3, by omega⟩ : Fin m))
        (b := bot (⟨c.val + 2, by omega⟩ : Fin m))
        (show bot (⟨c.val + 1, by omega⟩ : Fin m) ≠ bot (⟨c.val + 3, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega)
        (show bot (⟨c.val + 1, by omega⟩ : Fin m) ≠ bot (⟨c.val + 2, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega),
      Equiv.swap_apply_of_ne_of_ne (a := top (⟨c.val + 3, by omega⟩ : Fin m))
        (b := bot (⟨c.val + 3, by omega⟩ : Fin m))
        (show bot (⟨c.val + 1, by omega⟩ : Fin m) ≠ top (⟨c.val + 3, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega)
        (show bot (⟨c.val + 1, by omega⟩ : Fin m) ≠ bot (⟨c.val + 3, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega),
      Equiv.swap_apply_of_ne_of_ne (a := top (⟨c.val + 2, by omega⟩ : Fin m))
        (b := top (⟨c.val + 3, by omega⟩ : Fin m))
        (show bot (⟨c.val + 1, by omega⟩ : Fin m) ≠ top (⟨c.val + 2, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega)
        (show bot (⟨c.val + 1, by omega⟩ : Fin m) ≠ top (⟨c.val + 3, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega),
      Equiv.swap_apply_of_ne_of_ne (a := top (⟨c.val + 1, by omega⟩ : Fin m))
        (b := top (⟨c.val + 2, by omega⟩ : Fin m))
        (show bot (⟨c.val + 1, by omega⟩ : Fin m) ≠ top (⟨c.val + 1, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega)
        (show bot (⟨c.val + 1, by omega⟩ : Fin m) ≠ top (⟨c.val + 2, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega),
      Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (a := bot c) (b := bot (⟨c.val + 1, by omega⟩ : Fin m))
        (show top (⟨c.val + 1, by omega⟩ : Fin m) ≠ bot c by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega)
        (show top (⟨c.val + 1, by omega⟩ : Fin m) ≠ bot (⟨c.val + 1, by omega⟩ : Fin m) by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega),
      Equiv.swap_apply_of_ne_of_ne (a := top c) (b := bot c)
        (show top (⟨c.val + 1, by omega⟩ : Fin m) ≠ top c by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega)
        (show top (⟨c.val + 1, by omega⟩ : Fin m) ≠ bot c by
          intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
          simp only [Prod.mk.injEq] at this; omega)]

/-- The trace of the head `U L D L L U R` starting at `(0,c)` is `(1,c+2)`. -/
theorem trace_row0Head {c : Fin m} (hc : c.val + 3 < m) :
    trace (top c) row0Head = bot (⟨c.val + 2, by omega⟩ : Fin m) := by
  have hc1 : c.val + 1 < m := by omega
  have hc2 : c.val + 2 < m := by omega
  have hc3 : c.val + 3 < m := hc
  have h1 : neighbor? (top c) Dir.U = some (bot c) := by
    simp [top, bot]
  have h2 : neighbor? (bot c) Dir.L = some (bot (⟨c.val + 1, hc1⟩ : Fin m)) := by
    simpa [bot] using (neighbor?_mk_L (x := (1 : Fin 2)) (y := c) hc1)
  have h3 : neighbor? (bot (⟨c.val + 1, hc1⟩ : Fin m)) Dir.D
      = some (top (⟨c.val + 1, hc1⟩ : Fin m)) := by
    simpa [top, bot] using
      (neighbor?_mk_D (x := (1 : Fin 2)) (y := (⟨c.val + 1, hc1⟩ : Fin m)) (by decide))
  have h4 : neighbor? (top (⟨c.val + 1, hc1⟩ : Fin m)) Dir.L
      = some (top (⟨c.val + 2, hc2⟩ : Fin m)) := by
    simpa [top] using (neighbor?_mk_L (x := (0 : Fin 2))
      (y := (⟨c.val + 1, hc1⟩ : Fin m)) (by simp only; omega))
  have h5 : neighbor? (top (⟨c.val + 2, hc2⟩ : Fin m)) Dir.L
      = some (top (⟨c.val + 3, hc3⟩ : Fin m)) := by
    simpa [top] using (neighbor?_mk_L (x := (0 : Fin 2))
      (y := (⟨c.val + 2, hc2⟩ : Fin m)) (by simp only; omega))
  have h6 : neighbor? (top (⟨c.val + 3, hc3⟩ : Fin m)) Dir.U
      = some (bot (⟨c.val + 3, hc3⟩ : Fin m)) := by
    simpa [top, bot] using
      (neighbor?_mk_U (x := (0 : Fin 2)) (y := (⟨c.val + 3, hc3⟩ : Fin m)) (by decide))
  have h7 : neighbor? (bot (⟨c.val + 3, hc3⟩ : Fin m)) Dir.R
      = some (bot (⟨c.val + 2, hc2⟩ : Fin m)) := by
    simpa [bot] using (neighbor?_mk_R (x := (1 : Fin 2))
      (y := (⟨c.val + 3, hc3⟩ : Fin m)) (by simp only [Fin.val_mk]; omega))
  unfold row0Head
  rw [trace_cons_of_neighbor? h1, trace_cons_of_neighbor? h2,
      trace_cons_of_neighbor? h3, trace_cons_of_neighbor? h4,
      trace_cons_of_neighbor? h5, trace_cons_of_neighbor? h6,
      trace_cons_of_neighbor? h7, trace_nil]

/-- The head `U L D L L U R` is applicable from `(0,c)` when `c + 3 < m`. -/
theorem applicableFrom_row0Head {c : Fin m} (hc : c.val + 3 < m) :
    ApplicableFrom (top c) row0Head := by
  have hc1 : c.val + 1 < m := by omega
  have hc2 : c.val + 2 < m := by omega
  have hc3 : c.val + 3 < m := hc
  have h1 : neighbor? (top c) Dir.U = some (bot c) := by
    simp [top, bot]
  have h2 : neighbor? (bot c) Dir.L = some (bot (⟨c.val + 1, hc1⟩ : Fin m)) := by
    simpa [bot] using (neighbor?_mk_L (x := (1 : Fin 2)) (y := c) hc1)
  have h3 : neighbor? (bot (⟨c.val + 1, hc1⟩ : Fin m)) Dir.D
      = some (top (⟨c.val + 1, hc1⟩ : Fin m)) := by
    simpa [top, bot] using
      (neighbor?_mk_D (x := (1 : Fin 2)) (y := (⟨c.val + 1, hc1⟩ : Fin m)) (by decide))
  have h4 : neighbor? (top (⟨c.val + 1, hc1⟩ : Fin m)) Dir.L
      = some (top (⟨c.val + 2, hc2⟩ : Fin m)) := by
    simpa [top] using (neighbor?_mk_L (x := (0 : Fin 2))
      (y := (⟨c.val + 1, hc1⟩ : Fin m)) (by simp only; omega))
  have h5 : neighbor? (top (⟨c.val + 2, hc2⟩ : Fin m)) Dir.L
      = some (top (⟨c.val + 3, hc3⟩ : Fin m)) := by
    simpa [top] using (neighbor?_mk_L (x := (0 : Fin 2))
      (y := (⟨c.val + 2, hc2⟩ : Fin m)) (by simp only; omega))
  have h6 : neighbor? (top (⟨c.val + 3, hc3⟩ : Fin m)) Dir.U
      = some (bot (⟨c.val + 3, hc3⟩ : Fin m)) := by
    simpa [top, bot] using
      (neighbor?_mk_U (x := (0 : Fin 2)) (y := (⟨c.val + 3, hc3⟩ : Fin m)) (by decide))
  have h7 : neighbor? (bot (⟨c.val + 3, hc3⟩ : Fin m)) Dir.R
      = some (bot (⟨c.val + 2, hc2⟩ : Fin m)) := by
    simpa [bot] using (neighbor?_mk_R (x := (1 : Fin 2))
      (y := (⟨c.val + 3, hc3⟩ : Fin m)) (by simp only [Fin.val_mk]; omega))
  unfold row0Head
  refine ⟨bot c, h1, ?_⟩
  rw [applicableFrom_cons_of_neighbor? h2]
  refine ⟨top (⟨c.val + 1, hc1⟩ : Fin m), h3, ?_⟩
  rw [applicableFrom_cons_of_neighbor? h4]
  refine ⟨top (⟨c.val + 3, hc3⟩ : Fin m), h5, ?_⟩
  rw [applicableFrom_cons_of_neighbor? h6]
  refine ⟨bot (⟨c.val + 2, hc2⟩ : Fin m), h7, ?_⟩
  exact trivial

/-! ### The square loop `D R U L` -/

/-- The explicit permutation of the loop `D R U L` starting at `(1,c+2)`. -/
theorem permOf_row0Loop {c : Fin m} (hc : c.val + 3 < m) :
    permOf (bot (⟨c.val + 2, by omega⟩ : Fin m)) row0Loop
      = Equiv.swap (top (⟨c.val + 2, by omega⟩ : Fin m))
          (top (⟨c.val + 1, by omega⟩ : Fin m))
        * Equiv.swap (top (⟨c.val + 1, by omega⟩ : Fin m))
          (bot (⟨c.val + 1, by omega⟩ : Fin m)) := by
  have hc1 : c.val + 1 < m := by omega
  have hc2 : c.val + 2 < m := by omega
  have h1 : neighbor? (bot (⟨c.val + 2, hc2⟩ : Fin m)) Dir.D
      = some (top (⟨c.val + 2, hc2⟩ : Fin m)) := by
    simpa [top, bot] using
      (neighbor?_mk_D (x := (1 : Fin 2)) (y := (⟨c.val + 2, hc2⟩ : Fin m)) (by decide))
  have h2 : neighbor? (top (⟨c.val + 2, hc2⟩ : Fin m)) Dir.R
      = some (top (⟨c.val + 1, hc1⟩ : Fin m)) := by
    simpa [top] using (neighbor?_mk_R (x := (0 : Fin 2))
      (y := (⟨c.val + 2, hc2⟩ : Fin m)) (by simp only [Fin.val_mk]; omega))
  have h3 : neighbor? (top (⟨c.val + 1, hc1⟩ : Fin m)) Dir.U
      = some (bot (⟨c.val + 1, hc1⟩ : Fin m)) := by
    simpa [top, bot] using
      (neighbor?_mk_U (x := (0 : Fin 2)) (y := (⟨c.val + 1, hc1⟩ : Fin m)) (by decide))
  have h4 : neighbor? (bot (⟨c.val + 1, hc1⟩ : Fin m)) Dir.L
      = some (bot (⟨c.val + 2, hc2⟩ : Fin m)) := by
    simpa [bot] using (neighbor?_mk_L (x := (1 : Fin 2))
      (y := (⟨c.val + 1, hc1⟩ : Fin m)) (by simp only; omega))
  have hab : bot (⟨c.val + 2, hc2⟩ : Fin m) ≠ top (⟨c.val + 2, hc2⟩ : Fin m) := by
    intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
    simp only [Prod.mk.injEq] at this; omega
  have hac : bot (⟨c.val + 2, hc2⟩ : Fin m) ≠ top (⟨c.val + 1, hc1⟩ : Fin m) := by
    intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
    simp only [Prod.mk.injEq] at this; omega
  have had : bot (⟨c.val + 2, hc2⟩ : Fin m) ≠ bot (⟨c.val + 1, hc1⟩ : Fin m) := by
    intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
    simp only [Prod.mk.injEq] at this; omega
  have hbc : top (⟨c.val + 2, hc2⟩ : Fin m) ≠ top (⟨c.val + 1, hc1⟩ : Fin m) := by
    intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
    simp only [Prod.mk.injEq] at this; omega
  have hbd : top (⟨c.val + 2, hc2⟩ : Fin m) ≠ bot (⟨c.val + 1, hc1⟩ : Fin m) := by
    intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
    simp only [Prod.mk.injEq] at this; omega
  have hcd : top (⟨c.val + 1, hc1⟩ : Fin m) ≠ bot (⟨c.val + 1, hc1⟩ : Fin m) := by
    intro h; have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
    simp only [Prod.mk.injEq] at this; omega
  unfold row0Loop
  rw [permOf_cons_of_neighbor? h1, permOf_cons_of_neighbor? h2,
      permOf_cons_of_neighbor? h3, permOf_cons_of_neighbor? h4, permOf_nil, mul_one]
  rw [← mul_assoc, ← mul_assoc]
  rw [swap_mul_swap_mul_swap_mul_swap
        (a := bot (⟨c.val + 2, hc2⟩ : Fin m)) (b := top (⟨c.val + 2, hc2⟩ : Fin m))
        (c := top (⟨c.val + 1, hc1⟩ : Fin m)) (d := bot (⟨c.val + 1, hc1⟩ : Fin m))
        hab hac had hbc hbd hcd]

/-- The trace of the loop `D R U L` starting at `(1,c+2)` is `(1,c+2)`. -/
theorem trace_row0Loop {c : Fin m} (hc : c.val + 3 < m) :
    trace (bot (⟨c.val + 2, by omega⟩ : Fin m)) row0Loop
      = bot (⟨c.val + 2, by omega⟩ : Fin m) := by
  have hc1 : c.val + 1 < m := by omega
  have hc2 : c.val + 2 < m := by omega
  have h1 : neighbor? (bot (⟨c.val + 2, hc2⟩ : Fin m)) Dir.D
      = some (top (⟨c.val + 2, hc2⟩ : Fin m)) := by
    simpa [top, bot] using
      (neighbor?_mk_D (x := (1 : Fin 2)) (y := (⟨c.val + 2, hc2⟩ : Fin m)) (by decide))
  have h2 : neighbor? (top (⟨c.val + 2, hc2⟩ : Fin m)) Dir.R
      = some (top (⟨c.val + 1, hc1⟩ : Fin m)) := by
    simpa [top] using (neighbor?_mk_R (x := (0 : Fin 2))
      (y := (⟨c.val + 2, hc2⟩ : Fin m)) (by simp only [Fin.val_mk]; omega))
  have h3 : neighbor? (top (⟨c.val + 1, hc1⟩ : Fin m)) Dir.U
      = some (bot (⟨c.val + 1, hc1⟩ : Fin m)) := by
    simpa [top, bot] using
      (neighbor?_mk_U (x := (0 : Fin 2)) (y := (⟨c.val + 1, hc1⟩ : Fin m)) (by decide))
  have h4 : neighbor? (bot (⟨c.val + 1, hc1⟩ : Fin m)) Dir.L
      = some (bot (⟨c.val + 2, hc2⟩ : Fin m)) := by
    simpa [bot] using (neighbor?_mk_L (x := (1 : Fin 2))
      (y := (⟨c.val + 1, hc1⟩ : Fin m)) (by simp only; omega))
  unfold row0Loop
  rw [trace_cons_of_neighbor? h1, trace_cons_of_neighbor? h2,
      trace_cons_of_neighbor? h3, trace_cons_of_neighbor? h4, trace_nil]

/-! ### The gadget -/

/-- **The same-row gadget.**  `τ ρ τ⁻¹` is a closed walk at `(0,c)` acting as the three-cycle
`(0,c+1) → (0,c+3) → (0,c+2)` on row `0` and fixing everything else. -/
theorem permOf_row0Gadget {c : Fin m} (hc : c.val + 3 < m) :
    permOf (top c) row0Gadget
      = Equiv.swap (top (⟨c.val + 3, by omega⟩ : Fin m))
          (top (⟨c.val + 2, by omega⟩ : Fin m))
        * Equiv.swap (top (⟨c.val + 2, by omega⟩ : Fin m))
          (top (⟨c.val + 1, by omega⟩ : Fin m)) := by
  set A : Equiv.Perm (Cell 2 m) := permOf (top c) row0Head with hA
  have hB := permOf_row0Loop (c := c) hc
  have hinv : permOf (bot (⟨c.val + 2, by omega⟩ : Fin m)) (invWord row0Head) = A⁻¹ := by
    rw [hA, ← trace_row0Head hc]
    exact permOf_invWord (applicableFrom_row0Head hc)
  have hdecomp : permOf (top c) row0Gadget
      = A * (Equiv.swap (top (⟨c.val + 2, by omega⟩ : Fin m))
              (top (⟨c.val + 1, by omega⟩ : Fin m))
            * Equiv.swap (top (⟨c.val + 1, by omega⟩ : Fin m))
              (bot (⟨c.val + 1, by omega⟩ : Fin m)) * A⁻¹) := by
    unfold row0Gadget
    rw [List.append_assoc, permOf_append, trace_row0Head hc, permOf_append,
        trace_row0Loop hc, hinv, hB, hA]
  have hconj1 : A * Equiv.swap (top (⟨c.val + 2, by omega⟩ : Fin m))
        (top (⟨c.val + 1, by omega⟩ : Fin m)) * A⁻¹
      = Equiv.swap (top (⟨c.val + 3, by omega⟩ : Fin m))
          (top (⟨c.val + 2, by omega⟩ : Fin m)) := by
    rw [hA, ← Equiv.swap_apply_apply (permOf (top c) row0Head)
          (top (⟨c.val + 2, by omega⟩ : Fin m)) (top (⟨c.val + 1, by omega⟩ : Fin m)),
        row0Head_apply_top2 hc, row0Head_apply_top1 hc]
  have hconj2 : A * Equiv.swap (top (⟨c.val + 1, by omega⟩ : Fin m))
        (bot (⟨c.val + 1, by omega⟩ : Fin m)) * A⁻¹
      = Equiv.swap (top (⟨c.val + 2, by omega⟩ : Fin m))
          (top (⟨c.val + 1, by omega⟩ : Fin m)) := by
    rw [hA, ← Equiv.swap_apply_apply (permOf (top c) row0Head)
          (top (⟨c.val + 1, by omega⟩ : Fin m)) (bot (⟨c.val + 1, by omega⟩ : Fin m)),
        row0Head_apply_top1 hc, row0Head_apply_bot1 hc]
  rw [hdecomp]
  have hsplit : A * (Equiv.swap (top (⟨c.val + 2, by omega⟩ : Fin m))
              (top (⟨c.val + 1, by omega⟩ : Fin m))
            * Equiv.swap (top (⟨c.val + 1, by omega⟩ : Fin m))
              (bot (⟨c.val + 1, by omega⟩ : Fin m)) * A⁻¹)
      = (A * Equiv.swap (top (⟨c.val + 2, by omega⟩ : Fin m))
            (top (⟨c.val + 1, by omega⟩ : Fin m)) * A⁻¹)
        * (A * Equiv.swap (top (⟨c.val + 1, by omega⟩ : Fin m))
            (bot (⟨c.val + 1, by omega⟩ : Fin m)) * A⁻¹) := by group
  rw [hsplit, hconj1, hconj2]

/-- The gadget is a closed walk at its base. -/
theorem trace_row0Gadget {c : Fin m} (hc : c.val + 3 < m) :
    trace (top c) row0Gadget = top c := by
  have htrace := trace_row0Head hc
  have happ := applicableFrom_row0Head hc
  unfold row0Gadget
  rw [List.append_assoc, trace_append, htrace, trace_append, trace_row0Loop hc,
      ← htrace, trace_invWord happ]

/-- The gadget has length `18`. -/
theorem row0Gadget_length : row0Gadget.length = 18 := rfl

end Zhong

namespace Zhong

open Equiv

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

variable {m : ℕ}

/-! ### The reverse cycle of the first row -/

/-- `row0Rev c k` is the reverse cycle `(0,c) → (0,c+k) → (0,c+k-1) → ⋯ → (0,c)` on the
first row of a `2 × m` board, written as the inverse of the horizontal `L`-run. -/
noncomputable def row0Rev (c : Fin m) (k : ℕ) (h : c.val + k < m) : Equiv.Perm (Cell 2 m) :=
  (permOf (top c) (List.replicate k Dir.L))⁻¹

@[simp] theorem row0Rev_zero (c : Fin m) (h : c.val + 0 < m) : row0Rev c 0 h = 1 := by
  simp [row0Rev]

/-- The gadget is the reverse cycle of length two at `(0,c+1)`. -/
theorem row0Gadget_eq_row0Rev {c : Fin m} (hc : c.val + 3 < m) :
    permOf (top c) row0Gadget
      = row0Rev (⟨c.val + 1, by omega⟩ : Fin m) 2 (by simp only; omega) := by
  rw [row0Rev, show List.replicate 2 Dir.L = [Dir.L, Dir.L] from rfl]
  have h1 : neighbor? (top (⟨c.val + 1, by omega⟩ : Fin m)) Dir.L
      = some (top (⟨c.val + 2, by omega⟩ : Fin m)) := by
    simpa [top] using (neighbor?_mk_L (x := (0 : Fin 2))
      (y := (⟨c.val + 1, by omega⟩ : Fin m)) (by simp only; omega))
  have h2 : neighbor? (top (⟨c.val + 2, by omega⟩ : Fin m)) Dir.L
      = some (top (⟨c.val + 3, by omega⟩ : Fin m)) := by
    simpa [top] using (neighbor?_mk_L (x := (0 : Fin 2))
      (y := (⟨c.val + 2, by omega⟩ : Fin m)) (by simp only; omega))
  rw [permOf_cons_of_neighbor? h1, permOf_cons_of_neighbor? h2, permOf_nil, mul_one,
      mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv,
      Equiv.swap_comm (top (⟨c.val + 2, by omega⟩ : Fin m))
        (top (⟨c.val + 3, by omega⟩ : Fin m)),
      Equiv.swap_comm (top (⟨c.val + 1, by omega⟩ : Fin m))
        (top (⟨c.val + 2, by omega⟩ : Fin m))]
  exact permOf_row0Gadget hc

/-- Concatenating two horizontal runs on the first row. -/
theorem forward_mul0 {c : Fin m} (k : ℕ) (hk : c.val + 2 + k < m) (hc : c.val + 2 < m) :
    permOf (top c) (List.replicate 2 Dir.L)
      * permOf (top (⟨c.val + 2, hc⟩ : Fin m)) (List.replicate k Dir.L)
      = permOf (top c) (List.replicate (k + 2) Dir.L) := by
  rw [show List.replicate (k + 2) Dir.L
        = List.replicate 2 Dir.L ++ List.replicate k Dir.L from by
        rw [show k + 2 = 2 + k from by omega, List.replicate_add]]
  rw [permOf_append]
  have htrace : trace (top c) (List.replicate 2 Dir.L) = top (⟨c.val + 2, hc⟩ : Fin m) := by
    rw [trace_replicate_L2 (0 : Fin 2) (c := c) 2 hc]
  rw [htrace]

/-- Chaining the reverse cycle with the gadget at its left end extends the interval by two. -/
theorem row0Rev_mul_gadget {c : Fin m} (hc : c.val + 3 < m) (k : ℕ)
    (h : c.val + 3 + k < m) :
    row0Rev (⟨c.val + 3, by omega⟩ : Fin m) k h * permOf (top c) row0Gadget
      = row0Rev (⟨c.val + 1, by omega⟩ : Fin m) (k + 2) (by simp only; omega) := by
  rw [row0Gadget_eq_row0Rev hc]
  rw [show row0Rev (⟨c.val + 3, by omega⟩ : Fin m) k h
        = (permOf (top (⟨c.val + 3, by omega⟩ : Fin m))
            (List.replicate k Dir.L))⁻¹ from rfl]
  rw [show row0Rev (⟨c.val + 1, by omega⟩ : Fin m) 2 (by simp only; omega)
        = (permOf (top (⟨c.val + 1, by omega⟩ : Fin m))
            (List.replicate 2 Dir.L))⁻¹ from rfl]
  rw [← mul_inv_rev]
  rw [forward_mul0 (c := ⟨c.val + 1, by omega⟩) k (by simp only; omega)
        (by simp only; omega)]
  rw [row0Rev]

/-! ### The closed part of the same-row jump word -/

/-- The closed part of the same-row jump word: `l` conjugated gadgets producing the reverse
cycle of length `2l` on the first row. -/
def row0Closed : ℕ → List Dir
  | 0 => []
  | l + 1 => [Dir.L, Dir.L] ++ row0Closed l ++ [Dir.R, Dir.R] ++ row0Gadget

@[simp] theorem row0Closed_zero : row0Closed 0 = [] := rfl

theorem row0Closed_succ (l : ℕ) :
    row0Closed (l + 1) = [Dir.L, Dir.L] ++ row0Closed l ++ [Dir.R, Dir.R] ++ row0Gadget :=
  rfl

/-- The same-row jump word of Lemma 2: the closed part, then `L^{2l+1}`. -/
def row0Word (l : ℕ) : List Dir := row0Closed l ++ List.replicate (2 * l + 1) Dir.L

/-- Two permutations that each fix the other's moved points commute. -/
theorem mul_comm_of_fixes {α : Type*} (P Q : Equiv.Perm α)
    (hPQ : ∀ x, Q x ≠ x → P x = x) (hQP : ∀ x, P x ≠ x → Q x = x) : P * Q = Q * P := by
  ext x
  change P (Q x) = Q (P x)
  by_cases hx : Q x = x
  · rw [hx]
    by_cases hp : P x = x
    · rw [hp, hx]
    · have hPP : P (P x) ≠ P x := fun h => hp (P.injective h)
      rw [hQP (P x) hPP]
  · have hPx : P x = x := hPQ x hx
    have hQx : Q (Q x) ≠ Q x := fun h => hx (Q.injective h)
    rw [hPQ (Q x) hQx, hPx]

/-- A permutation fixing the first-row interval of a horizontal run conjugates it to itself. -/
theorem row0_conj (l : ℕ) (c : Fin m) (hc : c.val + 2 * l + 3 < m) :
    permOf (top c) [Dir.L, Dir.L]
      * row0Rev (⟨c.val + 3, by omega⟩ : Fin m) (2 * l) (by simp only; omega)
      * (permOf (top c) [Dir.L, Dir.L])⁻¹
      = row0Rev (⟨c.val + 3, by omega⟩ : Fin m) (2 * l)
          (by simp only; omega) := by
  have hP : ∀ x : Cell 2 m,
      (row0Rev (⟨c.val + 3, by omega⟩ : Fin m) (2 * l) (by simp only; omega)) x ≠ x →
      permOf (top c) [Dir.L, Dir.L] x = x := by
    intro x hx
    have hfix := (permOf_replicate_L2 (0 : Fin 2) (2 * l)
      (⟨c.val + 3, by omega⟩ : Fin m) (by simp only; omega)).2.2
    have hL : permOf (top (⟨c.val + 3, by omega⟩ : Fin m))
        (List.replicate (2 * l) Dir.L) x ≠ x := by
      intro h
      apply hx
      rw [row0Rev]
      change (permOf (top (⟨c.val + 3, by omega⟩ : Fin m))
        (List.replicate (2 * l) Dir.L)).symm x = x
      rw [Equiv.symm_apply_eq]
      exact h.symm
    have hnot := fun hc' => hL (hfix x hc')
    have hx0 : x.1 = 0 := by
      by_contra h
      exact hnot (Or.inl h)
    have hxge : c.val + 3 ≤ x.2.val := by
      by_contra h
      exact hnot (Or.inr (Or.inl (by simp only; omega)))
    have hfix2 := (permOf_replicate_L2 (0 : Fin 2) 2 c (by omega)).2.2
    exact hfix2 x (Or.inr (Or.inr (by omega)))
  have hQ : ∀ x : Cell 2 m, permOf (top c) [Dir.L, Dir.L] x ≠ x →
      (row0Rev (⟨c.val + 3, by omega⟩ : Fin m) (2 * l)
        (by simp only; omega)) x = x := by
    intro x hx
    have hfix := (permOf_replicate_L2 (0 : Fin 2) 2 c (by omega)).2.2
    have hPx : permOf (top c) [Dir.L, Dir.L] x ≠ x := hx
    have hnot := fun hc' => hPx (hfix x hc')
    have hx0 : x.1 = 0 := by
      by_contra h
      exact hnot (Or.inl h)
    have hxlt : x.2.val < c.val + 3 := by
      by_contra h
      exact hnot (Or.inr (Or.inr (by omega)))
    have hfixL := (permOf_replicate_L2 (0 : Fin 2) (2 * l)
      (⟨c.val + 3, by omega⟩ : Fin m) (by simp only; omega)).2.2
    have hLx : permOf (top (⟨c.val + 3, by omega⟩ : Fin m))
        (List.replicate (2 * l) Dir.L) x = x := hfixL x (Or.inr (Or.inl hxlt))
    rw [row0Rev]
    change (permOf (top (⟨c.val + 3, by omega⟩ : Fin m))
      (List.replicate (2 * l) Dir.L)).symm x = x
    rw [Equiv.symm_apply_eq]
    exact hLx.symm
  have hcomm := mul_comm_of_fixes (permOf (top c) [Dir.L, Dir.L])
    (row0Rev (⟨c.val + 3, by omega⟩ : Fin m) (2 * l) (by simp only; omega))
    hP hQ
  rw [hcomm]
  group

/-- The closed part is a closed walk at its base. -/
theorem trace_row0Closed : ∀ (l : ℕ) (c : Fin m) (hc : c.val + 2 * l + 1 < m),
    trace (top c) (row0Closed l) = top c := by
  intro l
  induction l with
  | zero => intro c hc; rw [row0Closed_zero, trace_nil]
  | succ l ih =>
      intro c hc
      have hc2 : c.val + 2 < m := by omega
      have hc3 : c.val + 3 < m := by omega
      have hc2l : (⟨c.val + 2, hc2⟩ : Fin m).val + 2 * l + 1 < m := by
        simp only; omega
      have htraceLL : trace (top c) [Dir.L, Dir.L] = top (⟨c.val + 2, hc2⟩ : Fin m) := by
        have := trace_replicate_L2 (0 : Fin 2) (c := c) 2 hc2
        simpa [List.replicate] using this
      have hR2 : trace (top (⟨c.val + 2, hc2⟩ : Fin m)) [Dir.R, Dir.R] = top c := by
        have h1 : neighbor? (top c) Dir.L = some (top (⟨c.val + 1, by omega⟩ : Fin m)) := by
          simpa [top] using (neighbor?_mk_L (x := (0 : Fin 2)) (y := c) (by omega))
        have h2 : neighbor? (top (⟨c.val + 1, by omega⟩ : Fin m)) Dir.L
            = some (top (⟨c.val + 2, hc2⟩ : Fin m)) := by
          simpa [top] using (neighbor?_mk_L (x := (0 : Fin 2))
            (y := (⟨c.val + 1, by omega⟩ : Fin m)) (by simp only; omega))
        have happ : ApplicableFrom (top c) [Dir.L, Dir.L] := by
          refine ⟨top (⟨c.val + 1, by omega⟩ : Fin m), h1, ?_⟩
          rw [applicableFrom_cons_of_neighbor? h2]
          exact trivial
        have h := trace_invWord happ
        rw [htraceLL] at h
        simpa [invWord] using h
      rw [row0Closed_succ, List.append_assoc, List.append_assoc, trace_append,
          htraceLL, trace_append, ih (⟨c.val + 2, hc2⟩ : Fin m) hc2l,
          trace_append, hR2, trace_row0Gadget hc3]

/-- The closed part induces the reverse cycle of the first row. -/
theorem permOf_row0Closed : ∀ (l : ℕ) (c : Fin m) (hc : c.val + 2 * l + 1 < m),
    permOf (top c) (row0Closed l)
      = row0Rev (⟨c.val + 1, by omega⟩ : Fin m) (2 * l)
          (by simp only; omega) := by
  intro l
  induction l with
  | zero =>
      intro c hc
      rw [row0Closed_zero, permOf_nil]
      simp [row0Rev]
  | succ l ih =>
      intro c hc
      have hc2 : c.val + 2 < m := by omega
      have hc3 : c.val + 3 < m := by omega
      have hc2l : (⟨c.val + 2, hc2⟩ : Fin m).val + 2 * l + 1 < m := by
        simp only; omega
      have htraceLL : trace (top c) [Dir.L, Dir.L] = top (⟨c.val + 2, hc2⟩ : Fin m) := by
        have := trace_replicate_L2 (0 : Fin 2) (c := c) 2 hc2
        simpa [List.replicate] using this
      have hR2trace : trace (top (⟨c.val + 2, hc2⟩ : Fin m)) [Dir.R, Dir.R] = top c := by
        have h1 : neighbor? (top c) Dir.L = some (top (⟨c.val + 1, by omega⟩ : Fin m)) := by
          simpa [top] using (neighbor?_mk_L (x := (0 : Fin 2)) (y := c) (by omega))
        have h2 : neighbor? (top (⟨c.val + 1, by omega⟩ : Fin m)) Dir.L
            = some (top (⟨c.val + 2, hc2⟩ : Fin m)) := by
          simpa [top] using (neighbor?_mk_L (x := (0 : Fin 2))
            (y := (⟨c.val + 1, by omega⟩ : Fin m)) (by simp only; omega))
        have happ : ApplicableFrom (top c) [Dir.L, Dir.L] := by
          refine ⟨top (⟨c.val + 1, by omega⟩ : Fin m), h1, ?_⟩
          rw [applicableFrom_cons_of_neighbor? h2]
          exact trivial
        have h := trace_invWord happ
        rw [htraceLL] at h
        simpa [invWord] using h
      have hR2perm : permOf (top (⟨c.val + 2, hc2⟩ : Fin m)) [Dir.R, Dir.R]
          = (permOf (top c) [Dir.L, Dir.L])⁻¹ := by
        have h1 : neighbor? (top c) Dir.L = some (top (⟨c.val + 1, by omega⟩ : Fin m)) := by
          simpa [top] using (neighbor?_mk_L (x := (0 : Fin 2)) (y := c) (by omega))
        have h2 : neighbor? (top (⟨c.val + 1, by omega⟩ : Fin m)) Dir.L
            = some (top (⟨c.val + 2, hc2⟩ : Fin m)) := by
          simpa [top] using (neighbor?_mk_L (x := (0 : Fin 2))
            (y := (⟨c.val + 1, by omega⟩ : Fin m)) (by simp only; omega))
        have happ : ApplicableFrom (top c) [Dir.L, Dir.L] := by
          refine ⟨top (⟨c.val + 1, by omega⟩ : Fin m), h1, ?_⟩
          rw [applicableFrom_cons_of_neighbor? h2]
          exact trivial
        have h := permOf_invWord happ
        rw [htraceLL] at h
        simpa [invWord] using h
      have hC := ih (⟨c.val + 2, hc2⟩ : Fin m) hc2l
      have hconj := row0_conj l c (by omega)
      have hgadget := permOf_row0Gadget hc3
      rw [row0Closed_succ, List.append_assoc, List.append_assoc, permOf_append,
          htraceLL, permOf_append, hC,
          trace_row0Closed l (⟨c.val + 2, hc2⟩ : Fin m) hc2l,
          permOf_append, hR2trace, hR2perm, hgadget]
      rw [show (permOf (top c) [Dir.L, Dir.L])
              * (row0Rev (⟨c.val + 3, by omega⟩ : Fin m) (2 * l)
                    (by simp only; omega)
                  * ((permOf (top c) [Dir.L, Dir.L])⁻¹
                    * (Equiv.swap (top (⟨c.val + 3, by omega⟩ : Fin m))
                          (top (⟨c.val + 2, by omega⟩ : Fin m))
                      * Equiv.swap (top (⟨c.val + 2, by omega⟩ : Fin m))
                          (top (⟨c.val + 1, by omega⟩ : Fin m)))))
            = (permOf (top c) [Dir.L, Dir.L]
                * row0Rev (⟨c.val + 3, by omega⟩ : Fin m) (2 * l)
                    (by simp only; omega)
                * (permOf (top c) [Dir.L, Dir.L])⁻¹)
              * (Equiv.swap (top (⟨c.val + 3, by omega⟩ : Fin m))
                    (top (⟨c.val + 2, by omega⟩ : Fin m))
                * Equiv.swap (top (⟨c.val + 2, by omega⟩ : Fin m))
                    (top (⟨c.val + 1, by omega⟩ : Fin m))) from by group]
      rw [hconj, ← permOf_row0Gadget hc3]
      simpa only [Nat.mul_succ] using row0Rev_mul_gadget hc3 (2 * l) (by omega)

/-- **Lemma 2 (Zhong 2023), same-row case.**  On a `2 × m` board whose blank is at `(0,c)`,
the word `row0Word l` swaps the blank with the tile at `(0, c + 2l + 1)`. -/
theorem permOf_row0Word {c : Fin m} (l : ℕ) (hc : c.val + 2 * l + 1 < m) :
    permOf (top c) (row0Word l)
      = Equiv.swap (top c) (top (⟨c.val + 2 * l + 1, hc⟩ : Fin m)) := by
  have hclosed := permOf_row0Closed l c hc
  have htrace := trace_row0Closed l c hc
  have hL : permOf (top c) [Dir.L] = Equiv.swap (top c) (top (⟨c.val + 1, by omega⟩ : Fin m)) := by
    have h1 : neighbor? (top c) Dir.L = some (top (⟨c.val + 1, by omega⟩ : Fin m)) := by
      simpa [top] using (neighbor?_mk_L (x := (0 : Fin 2)) (y := c) (by omega))
    rw [permOf_cons_of_neighbor? h1, permOf_nil, mul_one]
  have hLtr : trace (top c) [Dir.L] = top (⟨c.val + 1, by omega⟩ : Fin m) := by
    have h1 : neighbor? (top c) Dir.L = some (top (⟨c.val + 1, by omega⟩ : Fin m)) := by
      simpa [top] using (neighbor?_mk_L (x := (0 : Fin 2)) (y := c) (by omega))
    rw [trace_cons_of_neighbor? h1, trace_nil]
  have hF : permOf (top (⟨c.val + 1, by omega⟩ : Fin m)) (List.replicate (2 * l) Dir.L)
      = (row0Rev (⟨c.val + 1, by omega⟩ : Fin m) (2 * l)
          (by simp only; omega))⁻¹ := by
    rw [row0Rev, inv_inv]
  have htop : row0Rev (⟨c.val + 1, by omega⟩ : Fin m) (2 * l)
      (by simp only; omega) (top c) = top c := by
    rw [row0Rev]
    change (permOf (top (⟨c.val + 1, by omega⟩ : Fin m))
      (List.replicate (2 * l) Dir.L)).symm (top c) = top c
    rw [Equiv.symm_apply_eq]
    exact ((permOf_replicate_L2 (0 : Fin 2) (2 * l)
      (⟨c.val + 1, by omega⟩ : Fin m) (by simp only; omega)).2.2 (top c)
        (Or.inr (Or.inl (by simp only; omega)))).symm
  have hbot : row0Rev (⟨c.val + 1, by omega⟩ : Fin m) (2 * l)
      (by simp only; omega) (top (⟨c.val + 1, by omega⟩ : Fin m))
      = top (⟨c.val + 2 * l + 1, hc⟩ : Fin m) := by
    rw [row0Rev]
    change (permOf (top (⟨c.val + 1, by omega⟩ : Fin m))
      (List.replicate (2 * l) Dir.L)).symm (top (⟨c.val + 1, by omega⟩ : Fin m))
      = top (⟨c.val + 2 * l + 1, hc⟩ : Fin m)
    have hlast := (permOf_replicate_L2 (0 : Fin 2) (2 * l)
      (⟨c.val + 1, by omega⟩ : Fin m) (by simp only; omega)).2.1
    rw [Equiv.symm_apply_eq]
    rw [show top (⟨c.val + 2 * l + 1, hc⟩ : Fin m)
          = top (⟨c.val + 1 + 2 * l, by omega⟩ : Fin m) from by
          congr 1; apply Fin.ext; simp only; omega]
    exact hlast.symm
  rw [row0Word,
      show row0Closed l ++ List.replicate (2 * l + 1) Dir.L
        = row0Closed l ++ ([Dir.L] ++ List.replicate (2 * l) Dir.L) from by
        simp [List.replicate_succ],
      permOf_append, hclosed, htrace, permOf_append, hL, hLtr, hF]
  rw [← mul_assoc, ← Equiv.swap_apply_apply
        (row0Rev (⟨c.val + 1, by omega⟩ : Fin m) (2 * l)
          (by simp only; omega)) (top c) (top (⟨c.val + 1, by omega⟩ : Fin m)),
      htop, hbot]

/-- The closed part of the same-row word has length `22 l`. -/
theorem row0Closed_length (l : ℕ) : (row0Closed l).length = 22 * l := by
  induction l with
  | zero => rfl
  | succ l ih =>
      simp only [row0Closed_succ, List.length_append, List.length_cons, List.length_nil,
        row0Gadget_length, ih]
      omega

/-- The same-row word has length `24 l + 1`, i.e. `O(l)`. -/
theorem row0Word_length (l : ℕ) : (row0Word l).length = 24 * l + 1 := by
  simp only [row0Word, List.length_append, List.length_replicate, row0Closed_length]
  omega

end Zhong
