/-
Copyright (c) 2026 The Zhong formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhong formalisation contributors
-/
import Zhong.Algorithm.Jump

/-!
# Orientations of the jump primitive

Lemma 2 of Zhong (2023) is stated for an `m × 2` or `2 × m` board and an arbitrary target
cell `(x, y)` with `x + y + x₀ + y₀` odd.  `Algorithm/Jump.lean` proves the canonical
orientation: on a `2 × m` board with the blank at `(0, c)` and target `(1, c + 2l)`.

This file transports that result to the other orientations using the board symmetries:

* `flipDir` / `rowSwap2` swap the two rows (`U ↔ D`);
* `reflDir` / `colRefl` reflect the columns (`L ↔ R`);
* `transDir` / `transEquiv` transpose the board (`U ↔ L`, `D ↔ R`).

The key transport lemma is `permOf_map`: if a cell equivalence `φ` carries the neighbour
relation for a direction map `f`, then `permOf (φ p) (σ.map f) = φ.permCongr (permOf p σ)`.
-/

namespace Zhong

open Equiv

variable {n m n' m' : ℕ}

/-! ### Direction maps -/

/-- The direction map induced by reflecting the columns (`L ↔ R`). -/
def reflDir : Dir → Dir
  | Dir.U => Dir.U
  | Dir.D => Dir.D
  | Dir.L => Dir.R
  | Dir.R => Dir.L

/-- The direction map induced by swapping the two rows (`U ↔ D`). -/
def flipDir : Dir → Dir
  | Dir.U => Dir.D
  | Dir.D => Dir.U
  | Dir.L => Dir.L
  | Dir.R => Dir.R

/-- The direction map induced by transposing the board (`U ↔ L`, `D ↔ R`). -/
def transDir : Dir → Dir
  | Dir.U => Dir.L
  | Dir.D => Dir.R
  | Dir.L => Dir.U
  | Dir.R => Dir.D

/-! ### Cell symmetries -/

/-- Reflection of the columns of an `n × m` board. -/
def colRefl (n m : ℕ) : Cell n m ≃ Cell n m :=
  Equiv.prodCongr (Equiv.refl (Fin n)) Fin.revPerm

/-- Swap of the two rows of a `2 × m` board. -/
def rowSwap2 (m : ℕ) : Cell 2 m ≃ Cell 2 m :=
  Equiv.prodCongr Fin.revPerm (Equiv.refl (Fin m))

/-- Transposition of an `n × m` board. -/
def transEquiv (n m : ℕ) : Cell n m ≃ Cell m n := Equiv.prodComm (Fin n) (Fin m)

@[simp] theorem colRefl_apply (c : Cell n m) : colRefl n m c = (c.1, c.2.rev) := rfl
@[simp] theorem rowSwap2_apply (c : Cell 2 m) : rowSwap2 m c = (c.1.rev, c.2) := rfl
@[simp] theorem transEquiv_apply (c : Cell n m) : transEquiv n m c = (c.2, c.1) := rfl

/-! ### The neighbour relations -/

theorem neighbor?_colRefl (c : Cell n m) (δ : Dir) :
    neighbor? (colRefl n m c) (reflDir δ) = (neighbor? c δ).map (colRefl n m) := by
  have hU : ∀ (x : Fin n) (y : Fin m),
      neighbor? ((x, y.rev) : Cell n m) Dir.U =
        (neighbor? ((x, y) : Cell n m) Dir.U).map (colRefl n m) := by
    intro x y
    by_cases h : x.1 + 1 < n
    · rw [neighbor?_mk_U h, neighbor?_mk_U h]; rfl
    · rw [neighbor?, dif_neg h, neighbor?, dif_neg h]; rfl
  have hD : ∀ (x : Fin n) (y : Fin m),
      neighbor? ((x, y.rev) : Cell n m) Dir.D =
        (neighbor? ((x, y) : Cell n m) Dir.D).map (colRefl n m) := by
    intro x y
    by_cases h : 0 < x.1
    · rw [neighbor?_mk_D h, neighbor?_mk_D h]; rfl
    · rw [neighbor?, if_neg h, neighbor?, if_neg h]; rfl
  have hL : ∀ (x : Fin n) (y : Fin m),
      neighbor? ((x, y.rev) : Cell n m) Dir.R =
        (neighbor? ((x, y) : Cell n m) Dir.L).map (colRefl n m) := by
    intro x y
    by_cases h : y.1 + 1 < m
    · have hrev : 0 < (y.rev).val := by rw [Fin.val_rev]; omega
      rw [neighbor?_mk_L h, neighbor?_mk_R hrev, Option.map_some]
      simp only [Option.some.injEq, colRefl_apply]
      exact Prod.ext rfl (Fin.ext (by simp only [Fin.val_rev]; omega))
    · have hrev : ¬ 0 < (y.rev).val := by rw [Fin.val_rev]; omega
      simp only [neighbor?]
      rw [dif_neg h, if_neg hrev]
      rfl
  have hR : ∀ (x : Fin n) (y : Fin m),
      neighbor? ((x, y.rev) : Cell n m) Dir.L =
        (neighbor? ((x, y) : Cell n m) Dir.R).map (colRefl n m) := by
    intro x y
    by_cases h : 0 < y.1
    · have hrev : (y.rev).val + 1 < m := by rw [Fin.val_rev]; omega
      rw [neighbor?_mk_R h, neighbor?_mk_L hrev, Option.map_some]
      simp only [Option.some.injEq, colRefl_apply]
      exact Prod.ext rfl (Fin.ext (by simp only [Fin.val_rev]; omega))
    · have hrev : ¬ (y.rev).val + 1 < m := by rw [Fin.val_rev]; omega
      simp only [neighbor?]
      rw [dif_neg hrev, if_neg h]
      rfl
  cases δ <;> simp only [reflDir]
  · exact hU c.1 c.2
  · exact hD c.1 c.2
  · exact hL c.1 c.2
  · exact hR c.1 c.2

theorem neighbor?_rowSwap2 (c : Cell 2 m) (δ : Dir) :
    neighbor? (rowSwap2 m c) (flipDir δ) = (neighbor? c δ).map (rowSwap2 m) := by
  obtain ⟨x, y⟩ := c
  fin_cases x <;> cases δ <;>
    simp only [flipDir, neighbor?, rowSwap2_apply, Fin.rev] <;>
    split_ifs <;> simp_all

theorem neighbor?_transEquiv (c : Cell n m) (δ : Dir) :
    neighbor? (transEquiv n m c) (transDir δ) = (neighbor? c δ).map (transEquiv n m) := by
  obtain ⟨i, j⟩ := c
  cases δ <;> simp only [transDir, transEquiv_apply]
  · by_cases h : i.1 + 1 < n
    · rw [neighbor?_mk_L h, neighbor?_mk_U h]; rfl
    · rw [neighbor?, dif_neg h, neighbor?, dif_neg h]; rfl
  · by_cases h : 0 < i.1
    · rw [neighbor?_mk_R h, neighbor?_mk_D h]; rfl
    · rw [neighbor?, if_neg h, neighbor?, if_neg h]; rfl
  · by_cases h : j.1 + 1 < m
    · rw [neighbor?_mk_U h, neighbor?_mk_L h]; rfl
    · rw [neighbor?, dif_neg h, neighbor?, dif_neg h]; rfl
  · by_cases h : 0 < j.1
    · rw [neighbor?_mk_D h, neighbor?_mk_R h]; rfl
    · rw [neighbor?, if_neg h, neighbor?, if_neg h]; rfl

/-! ### Transport of `permOf` along a symmetry -/

/-- Conjugation of a transposition by a cell equivalence. -/
theorem permCongr_swap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (φ : α ≃ β) (a b : α) :
    φ.permCongr (Equiv.swap a b) = Equiv.swap (φ a) (φ b) := by
  ext x
  rw [Equiv.permCongr_apply]
  by_cases hx : x = φ a
  · subst hx; simp
  · by_cases hx2 : x = φ b
    · subst hx2; simp
    · rw [Equiv.swap_apply_of_ne_of_ne hx hx2]
      have h1 : φ.symm x ≠ a := fun h => hx (by rw [← h, Equiv.apply_symm_apply])
      have h2 : φ.symm x ≠ b := fun h => hx2 (by rw [← h, Equiv.apply_symm_apply])
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.apply_symm_apply]

/-- A cell equivalence carrying the neighbour relation carries the induced permutations. -/
theorem permOf_map (φ : Cell n m ≃ Cell n' m') (f : Dir → Dir)
    (h : ∀ c δ, neighbor? (φ c) (f δ) = (neighbor? c δ).map φ) :
    ∀ (p : Cell n m) (σ : List Dir),
      permOf (φ p) (σ.map f) = φ.permCongr (permOf p σ) := by
  intro p σ
  induction σ generalizing p with
  | nil => apply Equiv.ext; intro x; simp [Equiv.permCongr_apply]
  | cons δ τ ih =>
      rw [List.map_cons]
      cases hd : neighbor? p δ with
      | none =>
          have hφ : neighbor? (φ p) (f δ) = none := by rw [h p δ, hd]; rfl
          rw [permOf_cons_of_neighbor?_eq_none hd, permOf_cons_of_neighbor?_eq_none hφ]
          exact ih p
      | some c' =>
          have hφ : neighbor? (φ p) (f δ) = some (φ c') := by rw [h p δ, hd]; rfl
          rw [permOf_cons_of_neighbor? hd, permOf_cons_of_neighbor? hφ,
              Equiv.permCongr_mul, ih c', permCongr_swap]

/-! ### The orientations of Lemma 2 -/

/-- The row-swapped jump word. -/
def flipJumpWord (l : ℕ) : List Dir := (jumpWord l).map flipDir

/-- The column-reflected jump word. -/
def reflJumpWord (l : ℕ) : List Dir := (jumpWord l).map reflDir

/-- **Lemma 2, blank in row `1`.**  On a `2 × m` board with the blank at `(1, c)`, the
word `flipJumpWord l` swaps the blank with the tile at `(0, c + 2l)`. -/
theorem permOf_flipJumpWord {c : Fin m} (l : ℕ) (hc : c.val + 2 * l < m) :
    permOf (bot c) (flipJumpWord l)
      = Equiv.swap (bot c) (top (⟨c.val + 2 * l, hc⟩ : Fin m)) := by
  have h := permOf_map (rowSwap2 m) flipDir (neighbor?_rowSwap2) (top c) (jumpWord l)
  rw [permOf_jumpWord l hc] at h
  have htop : rowSwap2 m (top c) = bot c := by
    simp [top, bot, rowSwap2_apply, Fin.rev_zero, Fin.last]
  have hbot : rowSwap2 m (bot (⟨c.val + 2 * l, hc⟩ : Fin m))
      = top (⟨c.val + 2 * l, hc⟩ : Fin m) := by
    have h1 : (1 : Fin 2).rev = 0 := by decide
    simp [top, bot, rowSwap2_apply, h1]
  rw [permCongr_swap, htop, hbot] at h
  exact h

/-- **Lemma 2, target to the left.**  On a `2 × m` board with the blank at `(0, c)`, the
word `reflJumpWord l` swaps the blank with the tile at `(1, c - 2l)`. -/
theorem permOf_reflJumpWord {c : Fin m} (l : ℕ) (hc : 2 * l ≤ c.val) :
    permOf (top c) (reflJumpWord l)
      = Equiv.swap (top c) (bot (⟨c.val - 2 * l, by omega⟩ : Fin m)) := by
  have hcle : (c.rev).val + 2 * l < m := by rw [Fin.val_rev]; omega
  have h := permOf_map (colRefl 2 m) reflDir (neighbor?_colRefl) (top c.rev) (jumpWord l)
  rw [permOf_jumpWord l hcle] at h
  have htop : colRefl 2 m (top c.rev) = top c := by
    simp [top, colRefl_apply, Fin.rev_rev]
  have hbot : colRefl 2 m (bot (⟨(c.rev).val + 2 * l, hcle⟩ : Fin m))
      = bot (⟨c.val - 2 * l, by omega⟩ : Fin m) := by
    simp only [colRefl_apply, bot, Prod.mk.injEq, true_and]
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  rw [permCongr_swap, htop, hbot] at h
  exact h

/-! ### Board forms -/

/-! ### Lengths -/

@[simp] theorem flipJumpWord_length (l : ℕ) : (flipJumpWord l).length = 20 * l + 1 := by
  simp [flipJumpWord, jumpWord_length]

@[simp] theorem reflJumpWord_length (l : ℕ) : (reflJumpWord l).length = 20 * l + 1 := by
  simp [reflJumpWord, jumpWord_length]

end Zhong
