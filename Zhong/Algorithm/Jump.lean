/-
Copyright (c) 2026 The Zhong formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhong formalisation contributors
-/
import Zhong.ClosedWalk

/-!
# The jump primitive (Lemma 2 of Zhong 2023)

On a `2 × m` board whose blank is at `(0, y₀)`, the paper's Lemma 2 swaps the blank
with the tile at `(1, y₀ + 2l)` using `O(l)` moves.  This file formalises the explicit
word and its effect.

The word is built from the gadget

`g = U L L D R U R D L L U R R D = τ ρ τ⁻¹`,  `τ = U L L D R`, `ρ = U R D L`,

which is a closed walk at its base `(0, c)` and acts as the three-cycle
`(1,c) → (1,c+2) → (1,c+1) → (1,c)` on the cells of the second row, fixing everything
else.  Conjugating this gadget by the horizontal run `L^c` places it at an arbitrary
column, and chaining the conjugates produces the `(2l+1)`-cycle of the second row that,
together with the final `U L^{2l}`, becomes the transposition of the blank with the tile
at `(1, y₀ + 2l)`.
-/

namespace Zhong

open Equiv

set_option linter.unusedVariables false

variable {m : ℕ}

/-- The first row of a `2 × m` board. -/
abbrev top (c : Fin m) : Cell 2 m := ((0 : Fin 2), c)

/-- The second row of a `2 × m` board. -/
abbrev bot (c : Fin m) : Cell 2 m := ((1 : Fin 2), c)

theorem top_fin {m : ℕ} {a : ℕ} (h1 h2 : a < m) :
    top (⟨a, h1⟩ : Fin m) = top (⟨a, h2⟩ : Fin m) := by congr 1

theorem bot_fin {m : ℕ} {a : ℕ} (h1 h2 : a < m) :
    bot (⟨a, h1⟩ : Fin m) = bot (⟨a, h2⟩ : Fin m) := by congr 1

/-! ### A generic six-cycle lemma

The product `(a b)(b c)(c d)(d e)(e f)` of adjacent transpositions along a simple path
of six distinct points is the six-cycle `a → b → c → d → e → f → a`. -/

section SixCycle

variable {α : Type*} [DecidableEq α] {a b c d e f : α}

theorem sixCycle_apply_a
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) :
    (Equiv.swap a b * Equiv.swap b c * Equiv.swap c d * Equiv.swap d e
      * Equiv.swap e f) a = b := by
  change Equiv.swap a b (Equiv.swap b c (Equiv.swap c d (Equiv.swap d e
    (Equiv.swap e f a)))) = b
  rw [Equiv.swap_apply_of_ne_of_ne hae haf,
      Equiv.swap_apply_of_ne_of_ne had hae,
      Equiv.swap_apply_of_ne_of_ne hac had,
      Equiv.swap_apply_of_ne_of_ne hab hac,
      Equiv.swap_apply_left]

theorem sixCycle_apply_b
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) :
    (Equiv.swap a b * Equiv.swap b c * Equiv.swap c d * Equiv.swap d e
      * Equiv.swap e f) b = c := by
  change Equiv.swap a b (Equiv.swap b c (Equiv.swap c d (Equiv.swap d e
    (Equiv.swap e f b)))) = c
  rw [Equiv.swap_apply_of_ne_of_ne hbe hbf,
      Equiv.swap_apply_of_ne_of_ne hbd hbe,
      Equiv.swap_apply_of_ne_of_ne hbc hbd,
      Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]

theorem sixCycle_apply_c
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) :
    (Equiv.swap a b * Equiv.swap b c * Equiv.swap c d * Equiv.swap d e
      * Equiv.swap e f) c = d := by
  change Equiv.swap a b (Equiv.swap b c (Equiv.swap c d (Equiv.swap d e
    (Equiv.swap e f c)))) = d
  rw [Equiv.swap_apply_of_ne_of_ne hce hcf,
      Equiv.swap_apply_of_ne_of_ne hcd hce,
      Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hbd.symm hcd.symm,
      Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm]

end SixCycle

/-- `U L L D R`: the head `τ` of the jump gadget. -/
def jumpHead : List Dir := [Dir.U, Dir.L, Dir.L, Dir.D, Dir.R]

/-- The square loop `U R D L` used inside the jump gadget. -/
def jumpLoop : List Dir := [Dir.U, Dir.R, Dir.D, Dir.L]

/-- The basic jump gadget `τ ρ τ⁻¹`, a closed walk at its base. -/
def jumpGadget : List Dir := jumpHead ++ jumpLoop ++ invWord jumpHead

/-! ### The head `U L L D R` -/

/-- The explicit permutation of the head `U L L D R` starting at `(0,c)`: the six-cycle
`(0,c) → (1,c) → (1,c+1) → (1,c+2) → (0,c+2) → (0,c+1) → (0,c)`. -/
theorem permOf_jumpHead {c : Fin m} (hc : c.val + 2 < m) :
    permOf (top c) jumpHead
      = Equiv.swap (top c) (bot c)
        * Equiv.swap (bot c) (bot (⟨c.val + 1, by omega⟩ : Fin m))
        * Equiv.swap (bot (⟨c.val + 1, by omega⟩ : Fin m))
            (bot (⟨c.val + 2, by omega⟩ : Fin m))
        * Equiv.swap (bot (⟨c.val + 2, by omega⟩ : Fin m))
            (top (⟨c.val + 2, by omega⟩ : Fin m))
        * Equiv.swap (top (⟨c.val + 2, by omega⟩ : Fin m))
            (top (⟨c.val + 1, by omega⟩ : Fin m)) := by
  have hc1 : c.val + 1 < m := by omega
  have hc2 : c.val + 2 < m := hc
  have h1 : neighbor? (top c) Dir.U = some (bot c) := by
    simp [top, bot]
  have h2 : neighbor? (bot c) Dir.L = some (bot (⟨c.val + 1, hc1⟩ : Fin m)) := by
    simpa [bot] using (neighbor?_mk_L (x := (1 : Fin 2)) (y := c) hc1)
  have h3 : neighbor? (bot (⟨c.val + 1, hc1⟩ : Fin m)) Dir.L
      = some (bot (⟨c.val + 2, hc2⟩ : Fin m)) := by
    simpa [bot] using
      (neighbor?_mk_L (x := (1 : Fin 2)) (y := (⟨c.val + 1, hc1⟩ : Fin m)) hc2)
  have h4 : neighbor? (bot (⟨c.val + 2, hc2⟩ : Fin m)) Dir.D
      = some (top (⟨c.val + 2, hc2⟩ : Fin m)) := by
    simpa [top, bot] using
      (neighbor?_mk_D (x := (1 : Fin 2)) (y := (⟨c.val + 2, hc2⟩ : Fin m)) (by decide))
  have h5 : neighbor? (top (⟨c.val + 2, hc2⟩ : Fin m)) Dir.R
      = some (top (⟨c.val + 1, hc1⟩ : Fin m)) := by
    simpa [top] using
      (neighbor?_mk_R (x := (0 : Fin 2)) (y := (⟨c.val + 2, hc2⟩ : Fin m))
        (by simp only [Fin.val_mk]; omega))
  unfold jumpHead
  rw [permOf_cons_of_neighbor? h1, permOf_cons_of_neighbor? h2,
      permOf_cons_of_neighbor? h3, permOf_cons_of_neighbor? h4,
      permOf_cons_of_neighbor? h5, permOf_nil, mul_one]
  rw [bot_fin hc1 (by omega), bot_fin hc2 (by omega), top_fin hc2 (by omega),
      top_fin hc1 (by omega)]
  group

/-- The six cells of the head are pairwise distinct. -/
theorem jumpHead_cells_ne {c : Fin m} (hc : c.val + 2 < m) :
    top c ≠ bot c ∧ top c ≠ bot (⟨c.val + 1, by omega⟩ : Fin m) ∧
    top c ≠ bot (⟨c.val + 2, by omega⟩ : Fin m) ∧
    top c ≠ top (⟨c.val + 2, by omega⟩ : Fin m) ∧
    top c ≠ top (⟨c.val + 1, by omega⟩ : Fin m) ∧
    bot c ≠ bot (⟨c.val + 1, by omega⟩ : Fin m) ∧
    bot c ≠ bot (⟨c.val + 2, by omega⟩ : Fin m) ∧
    bot c ≠ top (⟨c.val + 2, by omega⟩ : Fin m) ∧
    bot c ≠ top (⟨c.val + 1, by omega⟩ : Fin m) ∧
    bot (⟨c.val + 1, by omega⟩ : Fin m) ≠ bot (⟨c.val + 2, by omega⟩ : Fin m) ∧
    bot (⟨c.val + 1, by omega⟩ : Fin m) ≠ top (⟨c.val + 2, by omega⟩ : Fin m) ∧
    bot (⟨c.val + 1, by omega⟩ : Fin m) ≠ top (⟨c.val + 1, by omega⟩ : Fin m) ∧
    bot (⟨c.val + 2, by omega⟩ : Fin m) ≠ top (⟨c.val + 2, by omega⟩ : Fin m) ∧
    bot (⟨c.val + 2, by omega⟩ : Fin m) ≠ top (⟨c.val + 1, by omega⟩ : Fin m) ∧
    top (⟨c.val + 2, by omega⟩ : Fin m) ≠ top (⟨c.val + 1, by omega⟩ : Fin m) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h
     have hh := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
     simp only [Prod.mk.injEq] at hh
     omega)

/-- The action of the head `U L L D R` on `(0,c)`. -/
theorem jumpHead_apply_top {c : Fin m} (hc : c.val + 2 < m) :
    permOf (top c) jumpHead (top c) = bot c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    jumpHead_cells_ne hc
  rw [permOf_jumpHead hc]
  exact sixCycle_apply_a h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15

/-- The action of the head `U L L D R` on `(1,c)`. -/
theorem jumpHead_apply_bot {c : Fin m} (hc : c.val + 2 < m) :
    permOf (top c) jumpHead (bot c) = bot (⟨c.val + 1, by omega⟩ : Fin m) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    jumpHead_cells_ne hc
  rw [permOf_jumpHead hc]
  exact sixCycle_apply_b h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15

/-- The action of the head `U L L D R` on `(1,c+1)`. -/
theorem jumpHead_apply_bot1 {c : Fin m} (hc : c.val + 2 < m) :
    permOf (top c) jumpHead (bot (⟨c.val + 1, by omega⟩ : Fin m))
      = bot (⟨c.val + 2, by omega⟩ : Fin m) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    jumpHead_cells_ne hc
  rw [permOf_jumpHead hc]
  exact sixCycle_apply_c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15

/-- The head `U L L D R` is applicable from `(0,c)` when `c + 2 < m`. -/
theorem applicableFrom_jumpHead {c : Fin m} (hc : c.val + 2 < m) :
    ApplicableFrom (top c) jumpHead := by
  have hc1 : c.val + 1 < m := by omega
  have hc2 : c.val + 2 < m := hc
  have h1 : neighbor? (top c) Dir.U = some (bot c) := by
    simp [top, bot]
  have h2 : neighbor? (bot c) Dir.L = some (bot (⟨c.val + 1, hc1⟩ : Fin m)) := by
    simpa [bot] using (neighbor?_mk_L (x := (1 : Fin 2)) (y := c) hc1)
  have h3 : neighbor? (bot (⟨c.val + 1, hc1⟩ : Fin m)) Dir.L
      = some (bot (⟨c.val + 2, hc2⟩ : Fin m)) := by
    simpa [bot] using
      (neighbor?_mk_L (x := (1 : Fin 2)) (y := (⟨c.val + 1, hc1⟩ : Fin m)) hc2)
  have h4 : neighbor? (bot (⟨c.val + 2, hc2⟩ : Fin m)) Dir.D
      = some (top (⟨c.val + 2, hc2⟩ : Fin m)) := by
    simpa [top, bot] using
      (neighbor?_mk_D (x := (1 : Fin 2)) (y := (⟨c.val + 2, hc2⟩ : Fin m)) (by decide))
  have h5 : neighbor? (top (⟨c.val + 2, hc2⟩ : Fin m)) Dir.R
      = some (top (⟨c.val + 1, hc1⟩ : Fin m)) := by
    simpa [top] using
      (neighbor?_mk_R (x := (0 : Fin 2)) (y := (⟨c.val + 2, hc2⟩ : Fin m))
        (by simp only [Fin.val_mk]; omega))
  unfold jumpHead
  refine ⟨bot c, h1, ?_⟩
  rw [applicableFrom_cons_of_neighbor? h2]
  refine ⟨bot (⟨c.val + 2, hc2⟩ : Fin m), h3, ?_⟩
  rw [applicableFrom_cons_of_neighbor? h4]
  refine ⟨top (⟨c.val + 1, hc1⟩ : Fin m), h5, ?_⟩
  exact trivial

/-- The trace of the head `U L L D R` starting at `(0,c)` is `(0,c+1)`. -/
theorem trace_jumpHead {c : Fin m} (hc : c.val + 2 < m) :
    trace (top c) jumpHead = top (⟨c.val + 1, by omega⟩ : Fin m) := by
  have hc1 : c.val + 1 < m := by omega
  have hc2 : c.val + 2 < m := hc
  have h1 : neighbor? (top c) Dir.U = some (bot c) := by
    simp [top, bot]
  have h2 : neighbor? (bot c) Dir.L = some (bot (⟨c.val + 1, hc1⟩ : Fin m)) := by
    simpa [bot] using (neighbor?_mk_L (x := (1 : Fin 2)) (y := c) hc1)
  have h3 : neighbor? (bot (⟨c.val + 1, hc1⟩ : Fin m)) Dir.L
      = some (bot (⟨c.val + 2, hc2⟩ : Fin m)) := by
    simpa [bot] using
      (neighbor?_mk_L (x := (1 : Fin 2)) (y := (⟨c.val + 1, hc1⟩ : Fin m)) hc2)
  have h4 : neighbor? (bot (⟨c.val + 2, hc2⟩ : Fin m)) Dir.D
      = some (top (⟨c.val + 2, hc2⟩ : Fin m)) := by
    simpa [top, bot] using
      (neighbor?_mk_D (x := (1 : Fin 2)) (y := (⟨c.val + 2, hc2⟩ : Fin m)) (by decide))
  have h5 : neighbor? (top (⟨c.val + 2, hc2⟩ : Fin m)) Dir.R
      = some (top (⟨c.val + 1, hc1⟩ : Fin m)) := by
    simpa [top] using
      (neighbor?_mk_R (x := (0 : Fin 2)) (y := (⟨c.val + 2, hc2⟩ : Fin m))
        (by simp only [Fin.val_mk]; omega))
  unfold jumpHead
  rw [trace_cons_of_neighbor? h1, trace_cons_of_neighbor? h2,
      trace_cons_of_neighbor? h3, trace_cons_of_neighbor? h4,
      trace_cons_of_neighbor? h5, trace_nil]

/-! ### The square loop `U R D L` -/

/-- The explicit permutation of the loop `U R D L` starting at `(0,c+1)`: the three-cycle
`(1,c+1) → (1,c) → (0,c) → (1,c+1)`, fixing everything else. -/
theorem permOf_jumpLoop {c : Fin m} (hc : c.val + 2 < m) :
    permOf (top (⟨c.val + 1, by omega⟩ : Fin m)) jumpLoop
      = Equiv.swap (bot (⟨c.val + 1, by omega⟩ : Fin m)) (bot c)
        * Equiv.swap (bot c) (top c) := by
  have hc1 : c.val + 1 < m := by omega
  have hc2 : c.val + 2 < m := hc
  have h1 : neighbor? (top (⟨c.val + 1, hc1⟩ : Fin m)) Dir.U
      = some (bot (⟨c.val + 1, hc1⟩ : Fin m)) := by
    simpa [top, bot] using
      (neighbor?_mk_U (x := (0 : Fin 2)) (y := (⟨c.val + 1, hc1⟩ : Fin m)) (by decide))
  have h2 : neighbor? (bot (⟨c.val + 1, hc1⟩ : Fin m)) Dir.R = some (bot c) := by
    simpa [bot] using
      (neighbor?_mk_R (x := (1 : Fin 2)) (y := (⟨c.val + 1, hc1⟩ : Fin m))
        (by simp only [Fin.val_mk]; omega))
  have h3 : neighbor? (bot c) Dir.D = some (top c) := by
    simp [top, bot]
  have h4 : neighbor? (top c) Dir.L = some (top (⟨c.val + 1, hc1⟩ : Fin m)) := by
    simpa [top] using (neighbor?_mk_L (x := (0 : Fin 2)) (y := c) hc1)
  have hab : top (⟨c.val + 1, hc1⟩ : Fin m) ≠ bot (⟨c.val + 1, hc1⟩ : Fin m) := by
    intro h; have hh := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
    simp only [Prod.mk.injEq] at hh; omega
  have hac : top (⟨c.val + 1, hc1⟩ : Fin m) ≠ bot c := by
    intro h; have hh := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
    simp only [Prod.mk.injEq] at hh; omega
  have had : top (⟨c.val + 1, hc1⟩ : Fin m) ≠ top c := by
    intro h; have hh := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
    simp only [Prod.mk.injEq] at hh; omega
  have hbc : bot (⟨c.val + 1, hc1⟩ : Fin m) ≠ bot c := by
    intro h; have hh := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
    simp only [Prod.mk.injEq] at hh; omega
  have hbd : bot (⟨c.val + 1, hc1⟩ : Fin m) ≠ top c := by
    intro h; have hh := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
    simp only [Prod.mk.injEq] at hh; omega
  have hcd : bot c ≠ top c := by
    intro h; have hh := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) h
    simp only [Prod.mk.injEq] at hh; omega
  unfold jumpLoop
  rw [permOf_cons_of_neighbor? h1, permOf_cons_of_neighbor? h2,
      permOf_cons_of_neighbor? h3, permOf_cons_of_neighbor? h4, permOf_nil, mul_one]
  rw [← mul_assoc, ← mul_assoc]
  rw [swap_mul_swap_mul_swap_mul_swap
        (a := top (⟨c.val + 1, hc1⟩ : Fin m)) (b := bot (⟨c.val + 1, hc1⟩ : Fin m))
        (c := bot c) (d := top c) hab hac had hbc hbd hcd]

/-- The trace of the loop `U R D L` starting at `(0,c+1)` is `(0,c+1)`. -/
theorem trace_jumpLoop {c : Fin m} (hc : c.val + 2 < m) :
    trace (top (⟨c.val + 1, by omega⟩ : Fin m)) jumpLoop
      = top (⟨c.val + 1, by omega⟩ : Fin m) := by
  have hc1 : c.val + 1 < m := by omega
  have h1 : neighbor? (top (⟨c.val + 1, hc1⟩ : Fin m)) Dir.U
      = some (bot (⟨c.val + 1, hc1⟩ : Fin m)) := by
    simpa [top, bot] using
      (neighbor?_mk_U (x := (0 : Fin 2)) (y := (⟨c.val + 1, hc1⟩ : Fin m)) (by decide))
  have h2 : neighbor? (bot (⟨c.val + 1, hc1⟩ : Fin m)) Dir.R = some (bot c) := by
    simpa [bot] using
      (neighbor?_mk_R (x := (1 : Fin 2)) (y := (⟨c.val + 1, hc1⟩ : Fin m))
        (by simp only [Fin.val_mk]; omega))
  have h3 : neighbor? (bot c) Dir.D = some (top c) := by
    simp [top, bot]
  have h4 : neighbor? (top c) Dir.L = some (top (⟨c.val + 1, hc1⟩ : Fin m)) := by
    simpa [top] using (neighbor?_mk_L (x := (0 : Fin 2)) (y := c) hc1)
  unfold jumpLoop
  rw [trace_cons_of_neighbor? h1, trace_cons_of_neighbor? h2,
      trace_cons_of_neighbor? h3, trace_cons_of_neighbor? h4, trace_nil]

/-! ### The gadget -/

/-- **The jump gadget.**  `τ ρ τ⁻¹` is a closed walk at `(0,c)` acting as the three-cycle
`(1,c) → (1,c+2) → (1,c+1) → (1,c)` on the second row and fixing everything else. -/
theorem permOf_jumpGadget {c : Fin m} (hc : c.val + 2 < m) :
    permOf (top c) jumpGadget
      = Equiv.swap (bot (⟨c.val + 2, by omega⟩ : Fin m))
          (bot (⟨c.val + 1, by omega⟩ : Fin m))
        * Equiv.swap (bot (⟨c.val + 1, by omega⟩ : Fin m)) (bot c) := by
  set A : Equiv.Perm (Cell 2 m) := permOf (top c) jumpHead with hA
  have hB := permOf_jumpLoop (c := c) hc
  have hinv : permOf (top (⟨c.val + 1, by omega⟩ : Fin m)) (invWord jumpHead) = A⁻¹ := by
    rw [hA, ← trace_jumpHead hc]
    exact permOf_invWord (applicableFrom_jumpHead hc)
  have hdecomp : permOf (top c) jumpGadget
      = A * (Equiv.swap (bot (⟨c.val + 1, by omega⟩ : Fin m)) (bot c)
              * Equiv.swap (bot c) (top c) * A⁻¹) := by
    unfold jumpGadget
    rw [List.append_assoc, permOf_append, trace_jumpHead hc, permOf_append,
        trace_jumpLoop hc, hinv, hB, hA]
  have hconj1 : A * Equiv.swap (bot (⟨c.val + 1, by omega⟩ : Fin m)) (bot c) * A⁻¹
      = Equiv.swap (bot (⟨c.val + 2, by omega⟩ : Fin m))
          (bot (⟨c.val + 1, by omega⟩ : Fin m)) := by
    rw [hA, ← Equiv.swap_apply_apply (permOf (top c) jumpHead)
          (bot (⟨c.val + 1, by omega⟩ : Fin m)) (bot c),
        jumpHead_apply_bot1 hc, jumpHead_apply_bot hc]
  have hconj2 : A * Equiv.swap (bot c) (top c) * A⁻¹
      = Equiv.swap (bot (⟨c.val + 1, by omega⟩ : Fin m)) (bot c) := by
    rw [hA, ← Equiv.swap_apply_apply (permOf (top c) jumpHead) (bot c) (top c),
        jumpHead_apply_bot hc, jumpHead_apply_top hc]
  rw [hdecomp]
  have hsplit : A * (Equiv.swap (bot (⟨c.val + 1, by omega⟩ : Fin m)) (bot c)
              * Equiv.swap (bot c) (top c) * A⁻¹)
      = (A * Equiv.swap (bot (⟨c.val + 1, by omega⟩ : Fin m)) (bot c) * A⁻¹)
        * (A * Equiv.swap (bot c) (top c) * A⁻¹) := by group
  rw [hsplit, hconj1, hconj2]

/-! ### The horizontal run on a `2 × m` board -/

/-- The trace of a horizontal `L`-run on a `2 × m` board, in any row. -/
theorem trace_replicate_L2 (r : Fin 2) (k : ℕ) :
    ∀ (c : Fin m) (hk : c.val + k < m),
      trace (r, c) (List.replicate k Dir.L) = (r, ⟨c.val + k, hk⟩) := by
  induction k with
  | zero =>
      intro c hk
      rw [List.replicate_zero, trace_nil]
      exact Prod.ext rfl (Fin.ext (by simp))
  | succ k ih =>
      intro c hk
      have hc1 : c.val + 1 < m := by omega
      have hL : neighbor? (r, c) Dir.L = some (r, (⟨c.val + 1, hc1⟩ : Fin m)) := by
        simpa using (neighbor?_mk_L (x := r) (y := c) hc1)
      rw [List.replicate_succ, trace_cons_of_neighbor? hL,
          ih (⟨c.val + 1, hc1⟩ : Fin m) (by simp only; omega)]
      exact Prod.ext rfl (Fin.ext (by simp only; omega))

/-- The action of a horizontal `L`-run on a `2 × m` board: within the row it is the
successor map, and it fixes the other row and the cells outside its interval. -/
theorem permOf_replicate_L2 (r : Fin 2) (k : ℕ) :
    ∀ (c : Fin m) (hk : c.val + k < m),
      (∀ i (hi : i < k),
          permOf (r, c) (List.replicate k Dir.L)
            (r, ⟨c.val + i, by omega⟩) = (r, ⟨c.val + i + 1, by omega⟩)) ∧
      (permOf (r, c) (List.replicate k Dir.L) (r, ⟨c.val + k, hk⟩) = (r, c)) ∧
      (∀ x : Cell 2 m,
          (x.1 ≠ r ∨ x.2.val < c.val ∨ c.val + k < x.2.val) →
          permOf (r, c) (List.replicate k Dir.L) x = x) := by
  induction k with
  | zero =>
      intro c hk
      refine ⟨?_, ?_, ?_⟩
      · intro i hi; omega
      · rw [List.replicate_zero, permOf_nil]; rfl
      · intro x _; rw [List.replicate_zero, permOf_nil]; rfl
  | succ k ih =>
      intro c hk
      have hc1 : c.val + 1 < m := by omega
      have hL : neighbor? (r, c) Dir.L = some (r, (⟨c.val + 1, hc1⟩ : Fin m)) := by
        simpa using (neighbor?_mk_L (x := r) (y := c) hc1)
      have hk1 : (⟨c.val + 1, hc1⟩ : Fin m).val + k < m := by
        simp only; omega
      obtain ⟨ih1, ih2, ih3⟩ := ih (⟨c.val + 1, hc1⟩ : Fin m) hk1
      have hstep : ∀ x : Cell 2 m,
          permOf (r, c) (List.replicate (k + 1) Dir.L) x
            = Equiv.swap (r, c) (r, (⟨c.val + 1, hc1⟩ : Fin m))
              (permOf (r, (⟨c.val + 1, hc1⟩ : Fin m))
                (List.replicate k Dir.L) x) := by
        intro x
        rw [List.replicate_succ, permOf_cons_of_neighbor? hL]
        rfl
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        rw [hstep]
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · have hfix := ih3 (r, c) (Or.inr (Or.inl (by show c.val < c.val + 1; omega)))
          rw [show (r, (⟨c.val + 0, by omega⟩ : Fin m)) = (r, c) from
                Prod.ext rfl (Fin.ext (by simp))]
          rw [hfix, Equiv.swap_apply_left]
        · have hcell : (r, (⟨c.val + i, by omega⟩ : Fin m))
              = (r, (⟨(⟨c.val + 1, hc1⟩ : Fin m).val + (i - 1), by omega⟩ : Fin m)) :=
            Prod.ext rfl (Fin.ext (by simp only; omega))
          rw [hcell]
          have h := ih1 (i - 1) (by omega)
          rw [h]
          have hne1 : (r, (⟨(⟨c.val + 1, hc1⟩ : Fin m).val + (i - 1) + 1,
              by omega⟩ : Fin m)) ≠ (r, c) := by
            intro hcon
            have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) hcon
            simp only [Prod.mk.injEq] at this
            omega
          have hne2 : (r, (⟨(⟨c.val + 1, hc1⟩ : Fin m).val + (i - 1) + 1,
              by omega⟩ : Fin m)) ≠ (r, (⟨c.val + 1, hc1⟩ : Fin m)) := by
            intro hcon
            have := congrArg (fun x : Cell 2 m => (x.1.val, x.2.val)) hcon
            simp only [Prod.mk.injEq] at this
            omega
          rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
          congr 1
          apply Fin.ext
          simp only
          omega
      · rw [hstep]
        have hcell : (r, (⟨c.val + (k + 1), by omega⟩ : Fin m))
            = (r, (⟨(⟨c.val + 1, hc1⟩ : Fin m).val + k, by omega⟩ : Fin m)) :=
          Prod.ext rfl (Fin.ext (by simp only; omega))
        rw [hcell, ih2, Equiv.swap_apply_right]
      · intro x hx
        rw [hstep]
        have hfix : permOf (r, (⟨c.val + 1, hc1⟩ : Fin m))
            (List.replicate k Dir.L) x = x := by
          apply ih3
          rcases hx with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl (by show x.2.val < c.val + 1; omega))
          · exact Or.inr (Or.inr (by show c.val + 1 + k < x.2.val; omega))
        rw [hfix]
        have hne1 : x ≠ (r, c) := by
          intro hcon
          rcases hx with h | h | h
          · exact h (by rw [hcon])
          · rw [hcon] at h; simp only at h; omega
          · rw [hcon] at h; simp only at h; omega
        have hne2 : x ≠ (r, (⟨c.val + 1, hc1⟩ : Fin m)) := by
          intro hcon
          rcases hx with h | h | h
          · exact h (by rw [hcon])
          · rw [hcon] at h; simp only at h; omega
          · rw [hcon] at h; simp only at h; omega
        rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]

/-- A horizontal `L`-run on a `2 × m` board fixes the cells of the other row. -/
theorem permOf_replicate_L2_fixes {r : Fin 2} {c : Fin m} {k : ℕ} (hk : c.val + k < m)
    {x : Cell 2 m} (hx : x.1 ≠ r) :
    permOf (r, c) (List.replicate k Dir.L) x = x :=
  (permOf_replicate_L2 r k c hk).2.2 x (Or.inl hx)

/-! ### The reverse cycle of the second row -/

/-- `row1Rev c k` is the reverse cycle `(1,c) → (1,c+k) → (1,c+k-1) → ⋯ → (1,c)` on the
second row of a `2 × m` board, written as the inverse of the horizontal `L`-run. -/
noncomputable def row1Rev (c : Fin m) (k : ℕ) (h : c.val + k < m) : Equiv.Perm (Cell 2 m) :=
  (permOf (bot c) (List.replicate k Dir.L))⁻¹

@[simp] theorem row1Rev_zero (c : Fin m) (h : c.val + 0 < m) : row1Rev c 0 h = 1 := by
  simp [row1Rev]

/-- The gadget three-cycle is the reverse cycle of length two at its left end. -/
theorem gadget_eq_row1Rev {c : Fin m} (hc : c.val + 2 < m) :
    Equiv.swap (bot (⟨c.val + 2, by omega⟩ : Fin m)) (bot (⟨c.val + 1, by omega⟩ : Fin m))
      * Equiv.swap (bot (⟨c.val + 1, by omega⟩ : Fin m)) (bot c)
      = row1Rev c 2 hc := by
  rw [row1Rev, show List.replicate 2 Dir.L = [Dir.L, Dir.L] from rfl]
  have h1 : neighbor? (bot c) Dir.L = some (bot (⟨c.val + 1, by omega⟩ : Fin m)) := by
    simpa [bot] using (neighbor?_mk_L (x := (1 : Fin 2)) (y := c) (by omega))
  have h2 : neighbor? (bot (⟨c.val + 1, by omega⟩ : Fin m)) Dir.L
      = some (bot (⟨c.val + 2, by omega⟩ : Fin m)) := by
    simpa [bot] using (neighbor?_mk_L (x := (1 : Fin 2))
      (y := (⟨c.val + 1, by omega⟩ : Fin m)) (by simp only; omega))
  rw [permOf_cons_of_neighbor? h1, permOf_cons_of_neighbor? h2, permOf_nil, mul_one]
  rw [mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv,
      Equiv.swap_comm (bot (⟨c.val + 1, by omega⟩ : Fin m))
        (bot (⟨c.val + 2, by omega⟩ : Fin m)),
      Equiv.swap_comm (bot c) (bot (⟨c.val + 1, by omega⟩ : Fin m))]

/-- A permutation fixing the second row conjugates the horizontal run to itself. -/
theorem conj_forward {P : Equiv.Perm (Cell 2 m)} (hfix : ∀ j : Fin m, P (bot j) = bot j) :
    ∀ (k : ℕ) (c : Fin m) (hk : c.val + k < m),
      P * permOf (bot c) (List.replicate k Dir.L) * P⁻¹
        = permOf (bot c) (List.replicate k Dir.L) := by
  intro k
  induction k with
  | zero => intro c hk; simp
  | succ k ih =>
      intro c hk
      have hc1 : c.val + 1 < m := by omega
      have hk1 : (⟨c.val + 1, hc1⟩ : Fin m).val + k < m := by
        simp only; omega
      have hL : neighbor? (bot c) Dir.L = some (bot (⟨c.val + 1, hc1⟩ : Fin m)) := by
        simpa [bot] using (neighbor?_mk_L (x := (1 : Fin 2)) (y := c) hc1)
      rw [List.replicate_succ, permOf_cons_of_neighbor? hL]
      calc P * (Equiv.swap (bot c) (bot (⟨c.val + 1, hc1⟩ : Fin m))
              * permOf (bot (⟨c.val + 1, hc1⟩ : Fin m)) (List.replicate k Dir.L)) * P⁻¹
          = (P * Equiv.swap (bot c) (bot (⟨c.val + 1, hc1⟩ : Fin m)) * P⁻¹)
            * (P * permOf (bot (⟨c.val + 1, hc1⟩ : Fin m)) (List.replicate k Dir.L)
                * P⁻¹) := by group
        _ = Equiv.swap (bot c) (bot (⟨c.val + 1, hc1⟩ : Fin m))
              * permOf (bot (⟨c.val + 1, hc1⟩ : Fin m)) (List.replicate k Dir.L) := by
              rw [← Equiv.swap_apply_apply P (bot c) (bot (⟨c.val + 1, hc1⟩ : Fin m)),
                  hfix, hfix, ih (⟨c.val + 1, hc1⟩ : Fin m) hk1]

/-- A permutation fixing the second row conjugates the reverse cycle to itself. -/
theorem conj_row1Rev {P : Equiv.Perm (Cell 2 m)} (hfix : ∀ j : Fin m, P (bot j) = bot j)
    (c : Fin m) (k : ℕ) (hk : c.val + k < m) :
    P * row1Rev c k hk * P⁻¹ = row1Rev c k hk := by
  rw [row1Rev]
  rw [show P * (permOf (bot c) (List.replicate k Dir.L))⁻¹ * P⁻¹
        = (P * permOf (bot c) (List.replicate k Dir.L) * P⁻¹)⁻¹ from by group,
      conj_forward hfix k c hk]

/-- Concatenating two horizontal runs. -/
theorem forward_mul {c : Fin m} (k : ℕ) (hk : c.val + k < m)
    (hc : c.val + 2 < m) :
    permOf (bot c) (List.replicate 2 Dir.L)
      * permOf (bot (⟨c.val + 2, hc⟩ : Fin m)) (List.replicate k Dir.L)
      = permOf (bot c) (List.replicate (k + 2) Dir.L) := by
  rw [show List.replicate (k + 2) Dir.L
        = List.replicate 2 Dir.L ++ List.replicate k Dir.L from by
        rw [show k + 2 = 2 + k from by omega, List.replicate_add]]
  rw [permOf_append]
  have htrace : trace (bot c) (List.replicate 2 Dir.L) = bot (⟨c.val + 2, hc⟩ : Fin m) := by
    rw [trace_replicate_L2 (1 : Fin 2) (c := c) 2 hc]
  rw [htrace]

/-- Chaining the reverse cycle with the gadget three-cycle at its left end extends the
interval by two cells. -/
theorem row1Rev_mul_gadget {c : Fin m} (hc : c.val + 2 < m) (k : ℕ) (h : c.val + 2 + k < m) :
    row1Rev (⟨c.val + 2, hc⟩ : Fin m) k h
      * (Equiv.swap (bot (⟨c.val + 2, hc⟩ : Fin m)) (bot (⟨c.val + 1, by omega⟩ : Fin m))
          * Equiv.swap (bot (⟨c.val + 1, by omega⟩ : Fin m)) (bot c))
      = row1Rev c (k + 2) (by omega) := by
  rw [show row1Rev (⟨c.val + 2, hc⟩ : Fin m) k h
        = (permOf (bot (⟨c.val + 2, hc⟩ : Fin m)) (List.replicate k Dir.L))⁻¹ from rfl]
  rw [gadget_eq_row1Rev (c := c) hc]
  rw [show row1Rev c 2 hc = (permOf (bot c) (List.replicate 2 Dir.L))⁻¹ from rfl]
  rw [← mul_inv_rev]
  rw [forward_mul (c := c) k (by omega) hc]
  rfl

/-! ### The closed part of the jump word -/

/-- The closed part of the jump word: `l` conjugated gadgets producing the reverse cycle
of length `2l` on the second row. -/
def jumpClosed : ℕ → List Dir
  | 0 => []
  | l + 1 => [Dir.L, Dir.L] ++ jumpClosed l ++ [Dir.R, Dir.R] ++ jumpGadget

@[simp] theorem jumpClosed_zero : jumpClosed 0 = [] := rfl

theorem jumpClosed_succ (l : ℕ) :
    jumpClosed (l + 1) = [Dir.L, Dir.L] ++ jumpClosed l ++ [Dir.R, Dir.R] ++ jumpGadget :=
  rfl

/-- The jump word of Lemma 2: the closed part, then `U` and `L^{2l}`. -/
def jumpWord (l : ℕ) : List Dir := jumpClosed l ++ [Dir.U] ++ List.replicate (2 * l) Dir.L

/-- The gadget is a closed walk at its base. -/
theorem trace_jumpGadget {c : Fin m} (hc : c.val + 2 < m) :
    trace (top c) jumpGadget = top c := by
  have htrace := trace_jumpHead hc
  have happ := applicableFrom_jumpHead hc
  unfold jumpGadget
  rw [List.append_assoc, trace_append, htrace, trace_append, trace_jumpLoop hc,
      ← htrace, trace_invWord happ]

/-- The closed part is a closed walk at its base. -/
theorem trace_jumpClosed : ∀ (l : ℕ) (c : Fin m) (hc : c.val + 2 * l < m),
    trace (top c) (jumpClosed l) = top c := by
  intro l
  induction l with
  | zero => intro c hc; rw [jumpClosed_zero, trace_nil]
  | succ l ih =>
      intro c hc
      have hc2 : c.val + 2 < m := by omega
      have hc2l : (⟨c.val + 2, hc2⟩ : Fin m).val + 2 * l < m := by
        simp only; omega
      have htraceLL : trace (top c) [Dir.L, Dir.L] = top (⟨c.val + 2, hc2⟩ : Fin m) := by
        have := trace_replicate_L2 (0 : Fin 2) (c := c) 2 hc2
        simpa [List.replicate] using this
      have happ : ApplicableFrom (top c) [Dir.L, Dir.L] := by
        have h1 : neighbor? (top c) Dir.L = some (top (⟨c.val + 1, by omega⟩ : Fin m)) := by
          simpa [top] using (neighbor?_mk_L (x := (0 : Fin 2)) (y := c) (by omega))
        have h2 : neighbor? (top (⟨c.val + 1, by omega⟩ : Fin m)) Dir.L
            = some (top (⟨c.val + 2, by omega⟩ : Fin m)) := by
          simpa [top] using (neighbor?_mk_L (x := (0 : Fin 2))
            (y := (⟨c.val + 1, by omega⟩ : Fin m)) (by simp only; omega))
        refine ⟨top (⟨c.val + 1, by omega⟩ : Fin m), h1, ?_⟩
        rw [applicableFrom_cons_of_neighbor? h2]
        exact trivial
      have hR2 : trace (top (⟨c.val + 2, hc2⟩ : Fin m)) [Dir.R, Dir.R] = top c := by
        have h := trace_invWord happ
        rw [htraceLL] at h
        simpa [invWord] using h
      rw [jumpClosed_succ, List.append_assoc, List.append_assoc, trace_append,
          htraceLL, trace_append, ih (⟨c.val + 2, hc2⟩ : Fin m) hc2l,
          trace_append, hR2, trace_jumpGadget hc2]

/-- The closed part induces the reverse cycle of the second row. -/
theorem permOf_jumpClosed : ∀ (l : ℕ) (c : Fin m) (hc : c.val + 2 * l < m),
    permOf (top c) (jumpClosed l) = row1Rev c (2 * l) hc := by
  intro l
  induction l with
  | zero =>
      intro c hc
      rw [jumpClosed_zero, permOf_nil]
      exact (row1Rev_zero c hc).symm
  | succ l ih =>
      intro c hc
      have hc2 : c.val + 2 < m := by omega
      have hc2l : (⟨c.val + 2, hc2⟩ : Fin m).val + 2 * l < m := by
        simp only; omega
      have htraceLL : trace (top c) [Dir.L, Dir.L] = top (⟨c.val + 2, hc2⟩ : Fin m) := by
        have := trace_replicate_L2 (0 : Fin 2) (c := c) 2 hc2
        simpa [List.replicate] using this
      have happ : ApplicableFrom (top c) [Dir.L, Dir.L] := by
        have h1 : neighbor? (top c) Dir.L = some (top (⟨c.val + 1, by omega⟩ : Fin m)) := by
          simpa [top] using (neighbor?_mk_L (x := (0 : Fin 2)) (y := c) (by omega))
        have h2 : neighbor? (top (⟨c.val + 1, by omega⟩ : Fin m)) Dir.L
            = some (top (⟨c.val + 2, by omega⟩ : Fin m)) := by
          simpa [top] using (neighbor?_mk_L (x := (0 : Fin 2))
            (y := (⟨c.val + 1, by omega⟩ : Fin m)) (by simp only; omega))
        refine ⟨top (⟨c.val + 1, by omega⟩ : Fin m), h1, ?_⟩
        rw [applicableFrom_cons_of_neighbor? h2]
        exact trivial
      have hR2trace : trace (top (⟨c.val + 2, hc2⟩ : Fin m)) [Dir.R, Dir.R] = top c := by
        have h := trace_invWord happ
        rw [htraceLL] at h
        simpa [invWord] using h
      have hR2perm : permOf (top (⟨c.val + 2, hc2⟩ : Fin m)) [Dir.R, Dir.R]
          = (permOf (top c) [Dir.L, Dir.L])⁻¹ := by
        have h := permOf_invWord happ
        rw [htraceLL] at h
        simpa [invWord] using h
      have hP : permOf (top c) [Dir.L, Dir.L]
            * row1Rev (⟨c.val + 2, hc2⟩ : Fin m) (2 * l) hc2l
            * (permOf (top c) [Dir.L, Dir.L])⁻¹
          = row1Rev (⟨c.val + 2, hc2⟩ : Fin m) (2 * l) hc2l := by
        apply conj_row1Rev
        intro j
        exact permOf_replicate_L2_fixes (r := (0 : Fin 2)) (c := c) (k := 2) hc2
          (x := bot j) (by simp)
      have hgadget := permOf_jumpGadget hc2
      rw [jumpClosed_succ, List.append_assoc, List.append_assoc, permOf_append,
          htraceLL, permOf_append, ih (⟨c.val + 2, hc2⟩ : Fin m) hc2l,
          trace_jumpClosed l (⟨c.val + 2, hc2⟩ : Fin m) hc2l,
          permOf_append, hR2trace, hR2perm, hgadget]
      rw [show (permOf (top c) [Dir.L, Dir.L])
              * (row1Rev (⟨c.val + 2, hc2⟩ : Fin m) (2 * l) hc2l
                * ((permOf (top c) [Dir.L, Dir.L])⁻¹
                  * (Equiv.swap (bot (⟨c.val + 2, hc2⟩ : Fin m))
                        (bot (⟨c.val + 1, by omega⟩ : Fin m))
                    * Equiv.swap (bot (⟨c.val + 1, by omega⟩ : Fin m)) (bot c))))
            = (permOf (top c) [Dir.L, Dir.L]
                * row1Rev (⟨c.val + 2, hc2⟩ : Fin m) (2 * l) hc2l
                * (permOf (top c) [Dir.L, Dir.L])⁻¹)
              * (Equiv.swap (bot (⟨c.val + 2, hc2⟩ : Fin m))
                    (bot (⟨c.val + 1, by omega⟩ : Fin m))
                * Equiv.swap (bot (⟨c.val + 1, by omega⟩ : Fin m)) (bot c)) from by group]
      rw [hP]
      exact row1Rev_mul_gadget (c := c) hc2 (2 * l) (by omega)

/-- **Lemma 2 (Zhong 2023), canonical case.**  On a `2 × m` board whose blank is at
`(0,c)`, the word `jumpWord l` swaps the blank with the tile at `(1, c + 2l)`. -/
theorem permOf_jumpWord {c : Fin m} (l : ℕ) (hc : c.val + 2 * l < m) :
    permOf (top c) (jumpWord l) = Equiv.swap (top c) (bot (⟨c.val + 2 * l, hc⟩ : Fin m)) := by
  have hclosed := permOf_jumpClosed l c hc
  have htrace := trace_jumpClosed l c hc
  have hU : permOf (top c) [Dir.U] = Equiv.swap (top c) (bot c) := by
    have h1 : neighbor? (top c) Dir.U = some (bot c) := by
      simp [top, bot]
    rw [permOf_cons_of_neighbor? h1, permOf_nil, mul_one]
  have hUtr : trace (top c) [Dir.U] = bot c := by
    have h1 : neighbor? (top c) Dir.U = some (bot c) := by
      simp [top, bot]
    rw [trace_cons_of_neighbor? h1, trace_nil]
  have hF : permOf (bot c) (List.replicate (2 * l) Dir.L)
      = (row1Rev c (2 * l) hc)⁻¹ := by
    rw [row1Rev, inv_inv]
  have htop : row1Rev c (2 * l) hc (top c) = top c := by
    rw [row1Rev]
    change (permOf (bot c) (List.replicate (2 * l) Dir.L)).symm (top c) = top c
    rw [Equiv.symm_apply_eq]
    exact ((permOf_replicate_L2 (1 : Fin 2) (2 * l) c hc).2.2 (top c)
      (Or.inl (by simp))).symm
  have hbot : row1Rev c (2 * l) hc (bot c) = bot (⟨c.val + 2 * l, hc⟩ : Fin m) := by
    rw [row1Rev]
    change (permOf (bot c) (List.replicate (2 * l) Dir.L)).symm (bot c)
      = bot (⟨c.val + 2 * l, hc⟩ : Fin m)
    rw [Equiv.symm_apply_eq]
    exact ((permOf_replicate_L2 (1 : Fin 2) (2 * l) c hc).2.1).symm
  rw [jumpWord,
      show jumpClosed l ++ [Dir.U] ++ List.replicate (2 * l) Dir.L
        = jumpClosed l ++ ([Dir.U] ++ List.replicate (2 * l) Dir.L) from by
        simp [List.append_assoc],
      permOf_append, hclosed, htrace, permOf_append, hU, hUtr, hF]
  rw [← mul_assoc, ← Equiv.swap_apply_apply (row1Rev c (2 * l) hc) (top c) (bot c),
      htop, hbot]

/-- The gadget has length `14`. -/
theorem jumpGadget_length : jumpGadget.length = 14 := rfl

/-- The closed part of the jump word has length `18 l`. -/
theorem jumpClosed_length (l : ℕ) : (jumpClosed l).length = 18 * l := by
  induction l with
  | zero => rfl
  | succ l ih =>
      simp only [jumpClosed_succ, List.length_append, List.length_cons, List.length_nil,
        jumpGadget_length, ih]
      omega

/-- The jump word has length `20 l + 1`, i.e. `O(l)`. -/
theorem jumpWord_length (l : ℕ) : (jumpWord l).length = 20 * l + 1 := by
  simp only [jumpWord, List.length_append, List.length_cons, List.length_nil,
    List.length_replicate, jumpClosed_length]
  omega

end Zhong
