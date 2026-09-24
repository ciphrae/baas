import Zhong.Orbit
import Zhong.Group
/-
Copyright (c) 2026 The Zhong formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhong formalisation contributors
-/

/-!
# The `2 × 2` base case

The reduction-of-order algorithm terminates with a `2 × 2` block.  This file solves that
block by exhaustive evaluation: `Board 2 2` has `24` states, of which `12` are reachable, and
the diameter is `6`.  The solving words are tabulated in `solve22Table` and their correctness
is checked by `decide` over the finite type.

The parity criterion `reachable_sign_relPerm` (the necessary direction of Proposition 3, which
holds for every board size) supplies the hypothesis in the form the table expects.
-/

namespace Zhong

open Equiv

/-- The labels of a `2 × 2` board in row-major order `(0,0), (0,1), (1,0), (1,1)`. -/
def boardTuple (B : Board 2 2) : Fin 4 × Fin 4 × Fin 4 × Fin 4 :=
  (B (0, 0), B (0, 1), B (1, 0), B (1, 1))

/-- The solving table for the `2 × 2` puzzle: for each reachable label tuple, a word taking
that board to the target. -/
def solve22Table : List ((Fin 4 × Fin 4 × Fin 4 × Fin 4) × List Dir) :=
  [ ((1, 2, 3, 0), []),
    ((1, 0, 3, 2), [Dir.U]),
    ((1, 2, 0, 3), [Dir.L]),
    ((0, 1, 3, 2), [Dir.L, Dir.U]),
    ((0, 2, 1, 3), [Dir.U, Dir.L]),
    ((2, 0, 1, 3), [Dir.R, Dir.U, Dir.L]),
    ((3, 1, 0, 2), [Dir.D, Dir.L, Dir.U]),
    ((2, 3, 1, 0), [Dir.D, Dir.R, Dir.U, Dir.L]),
    ((3, 1, 2, 0), [Dir.R, Dir.D, Dir.L, Dir.U]),
    ((2, 3, 0, 1), [Dir.L, Dir.D, Dir.R, Dir.U, Dir.L]),
    ((3, 0, 2, 1), [Dir.U, Dir.R, Dir.D, Dir.L, Dir.U]),
    ((0, 3, 2, 1), [Dir.L, Dir.U, Dir.R, Dir.D, Dir.L, Dir.U]) ]

/-- A solving word for a `2 × 2` board, read off from `solve22Table`. -/
def solve22 (B : Board 2 2) : List Dir :=
  (solve22Table.find? (fun p => p.1 == boardTuple B)).elim [] Prod.snd

/-- The solving words all have length at most `6`. -/
theorem solve22_length : ∀ B : Board 2 2, (solve22 B).length ≤ 6 := by
  decide

/-- **Correctness of the `2 × 2` table.**  Every board satisfying the parity condition is
solved by `solve22`. -/
theorem solve22_correct : ∀ B : Board 2 2,
    Equiv.Perm.sign (relPerm B (target 2 2))
      = cellParity (blank B) * cellParity (blank (target 2 2)) →
    actSeq B (solve22 B) = target 2 2 := by
  decide

/-- The solving words are applicable from the blank of the board they solve. -/
theorem solve22_applicable : ∀ B : Board 2 2, ApplicableFrom (blank B) (solve22 B) := by
  decide

end Zhong
