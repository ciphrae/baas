/-
Copyright (c) 2026 The Zhong formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhong formalisation contributors
-/
import Mathlib

/-!
# The sliding puzzle: boards, moves, and operation sequences

This file sets up the combinatorial model used in Zhong, *Additive Approximation
Algorithms for Sliding Puzzle* (2023).

* `Cell n m` is the set of cells of an `n × m` board.
* `Board n m` is a bijection from cells to labels `Fin (n*m)`; the label `0` is the
  blank cell.
* `Dir` is the set of moves `U, D, L, R`; `act` applies a move.
* `actSeq` applies a list of moves.

All conventions follow Section 2 of the paper.
-/

namespace Zhong

open Equiv

/-- A cell of an `n × m` board, indexed by `(row, column)`. -/
abbrev Cell (n m : ℕ) := Fin n × Fin m

/-- A board is a bijection from cells to labels `Fin (n*m)`.  The label `0` is the
blank cell.  (The paper allows any distinct labels; we normalise to `Fin (n*m)`.) -/
abbrev Board (n m : ℕ) := Cell n m ≃ Fin (n * m)

/-- The four single-tile moves. -/
inductive Dir : Type
  | U : Dir
  | D : Dir
  | L : Dir
  | R : Dir
  deriving DecidableEq, Repr

instance : Fintype Dir :=
  ⟨{Dir.U, Dir.D, Dir.L, Dir.R}, by intro x; cases x <;> simp⟩

namespace Dir


end Dir

variable {n m : ℕ}

/-- The blank cell of a board. -/
def blank [NeZero (n * m)] (B : Board n m) : Cell n m := B.symm 0

/-- The neighbouring cell reached by moving the blank in direction `δ`, if it exists. -/
def neighbor? (c : Cell n m) : Dir → Option (Cell n m)
  | Dir.U =>
      if h : c.1.1 + 1 < n then some (⟨c.1.1 + 1, h⟩, c.2) else none
  | Dir.D =>
      if 0 < c.1.1 then
        some (⟨c.1.1 - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) c.1.2⟩, c.2)
      else none
  | Dir.L =>
      if h : c.2.1 + 1 < m then some (c.1, ⟨c.2.1 + 1, h⟩) else none
  | Dir.R =>
      if 0 < c.2.1 then
        some (c.1, ⟨c.2.1 - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) c.2.2⟩)
      else none

/-- A move is applicable to `B` if the blank has a neighbour in that direction. -/
def Applicable [NeZero (n * m)] (B : Board n m) (δ : Dir) : Prop :=
  (neighbor? (blank B) δ).isSome

instance [NeZero (n * m)] (B : Board n m) (δ : Dir) : Decidable (Applicable B δ) :=
  inferInstanceAs (Decidable (neighbor? (blank B) δ).isSome)

/-- Act a single move on a board.  If the move is not applicable the board is
unchanged.  The move swaps the blank with its neighbour, i.e. it precomposes the
board with the cell transposition. -/
def act [NeZero (n * m)] (B : Board n m) (δ : Dir) : Board n m :=
  match neighbor? (blank B) δ with
  | some c' => (Equiv.swap (blank B) c').trans B
  | none => B

/-- Act a list of moves (an operation sequence). -/
def actSeq [NeZero (n * m)] (B : Board n m) (σ : List Dir) : Board n m :=
  σ.foldl act B

/-- The standard target board of the `n × m` rectangular puzzle:
`BT (x, y) = (m*x + y + 1) mod (m*n)`. -/
noncomputable def target (n m : ℕ) : Board n m :=
  (finProdFinEquiv (m := n) (n := m)).trans (finRotate (n * m))

/-- The value of `finProdFinEquiv` on a cell. -/
@[simp] theorem finProdFinEquiv_val (x : Fin n) (y : Fin m) :
    (finProdFinEquiv ((x, y) : Fin n × Fin m)).val = y.val + m * x.val := rfl

/-- The blank cell of the target board is the bottom-right corner `(n-1, m-1)`. -/
theorem target_last [NeZero (n * m)] (hn : 0 < n) (hm : 0 < m) (hnm1 : 1 < n * m) :
    target n m (((⟨n - 1, by omega⟩ : Fin n), (⟨m - 1, by omega⟩ : Fin m)) : Cell n m) = 0 := by
  have hnm : 0 < n * m := by omega
  have hprod : finProdFinEquiv
      (((⟨n - 1, by omega⟩ : Fin n), (⟨m - 1, by omega⟩ : Fin m)) : Cell n m)
      = (⟨n * m - 1, by omega⟩ : Fin (n * m)) := by
    apply Fin.ext
    simp only [finProdFinEquiv_val]
    rw [Nat.mul_comm n m]
    have h1 : m * (n - 1) = m * n - m := by rw [Nat.mul_sub_left_distrib]; ring
    rw [h1]
    have h2 : m ≤ m * n := by
      calc m = m * 1 := by ring
        _ ≤ m * n := Nat.mul_le_mul_left m hn
    omega
  have hrot : finRotate (n * m) (⟨n * m - 1, by omega⟩ : Fin (n * m)) = 0 := by
    rw [finRotate_apply]
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_zero]
    rw [Fin.val_one', Nat.mod_eq_of_lt hnm1]
    rw [show n * m - 1 + 1 = n * m from by omega, Nat.mod_self]
  simp only [target, Equiv.trans_apply, hprod, hrot]

/-- The target board has label `0` only at the bottom-right corner. -/
theorem target_ne_zero [NeZero (n * m)] (r : ℕ) (yc : ℕ) (hyc : yc < m) (hr : r + 1 < n) :
    target n m (((⟨r, by omega⟩ : Fin n), (⟨yc, hyc⟩ : Fin m)) : Cell n m) ≠ 0 := by
  intro hzero
  have hnm1 : 1 < n * m := by
    have := Nat.mul_le_mul (show 2 ≤ n by omega) (show 1 ≤ m by omega)
    omega
  have hlast := target_last (n := n) (m := m) (by omega) (by omega) hnm1
  have heq : target n m (((⟨r, by omega⟩ : Fin n), (⟨yc, hyc⟩ : Fin m)) : Cell n m)
      = target n m (((⟨n - 1, by omega⟩ : Fin n), (⟨m - 1, by omega⟩ : Fin m)) : Cell n m) := by
    rw [hzero, hlast]
  have hcell := (target n m).injective heq
  have := congrArg (fun w : Cell n m => w.1.val) hcell
  simp only at this
  omega

/-! ### Basic lemmas -/

@[simp] theorem actSeq_nil [NeZero (n * m)] (B : Board n m) : actSeq B [] = B := rfl

theorem actSeq_cons [NeZero (n * m)] (B : Board n m) (δ : Dir) (σ : List Dir) :
    actSeq B (δ :: σ) = actSeq (act B δ) σ := rfl

theorem actSeq_append [NeZero (n * m)] (B : Board n m) (σ₁ σ₂ : List Dir) :
    actSeq B (σ₁ ++ σ₂) = actSeq (actSeq B σ₁) σ₂ := by
  simp [actSeq, List.foldl_append]

/-- When the move is applicable, `act` is the transposition of blank and neighbour. -/
theorem act_of_neighbor? [NeZero (n * m)] {B : Board n m} {δ : Dir} {c' : Cell n m}
    (h : neighbor? (blank B) δ = some c') :
    act B δ = (Equiv.swap (blank B) c').trans B := by
  simp only [act, h]

/-- The blank after an applicable move is the neighbour. -/
theorem blank_act_of_neighbor? [NeZero (n * m)] {B : Board n m} {δ : Dir} {c' : Cell n m}
    (h : neighbor? (blank B) δ = some c') : blank (act B δ) = c' := by
  rw [act_of_neighbor? h, blank, Equiv.symm_trans_apply, Equiv.symm_swap]
  exact Equiv.swap_apply_left _ _

/-- If the move is not applicable, `act` fixes the board. -/
theorem act_of_neighbor?_eq_none [NeZero (n * m)] {B : Board n m} {δ : Dir}
    (h : neighbor? (blank B) δ = none) : act B δ = B := by
  simp only [act, h]

/-- If the move is not applicable, `act` fixes the board. -/
theorem act_of_not_applicable [NeZero (n * m)] {B : Board n m} {δ : Dir}
    (h : ¬ Applicable B δ) : act B δ = B := by
  unfold Applicable at h
  cases hh : neighbor? (blank B) δ with
  | none => exact act_of_neighbor?_eq_none hh
  | some c' => exact absurd (by simp [hh]) h

/-- The neighbour of a cell is different from it. -/
theorem neighbor?_ne {c c' : Cell n m} {δ : Dir} (h : neighbor? c δ = some c') : c' ≠ c := by
  intro hcc
  have h2 : neighbor? c δ = some c := by simpa [hcc] using h
  clear h c' hcc
  cases δ <;> simp only [neighbor?] at h2 <;> split_ifs at h2 <;>
    simp_all [Prod.ext_iff, Fin.ext_iff] <;>
    omega

end Zhong
