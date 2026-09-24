/-
Copyright (c) 2026 The Zhong formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhong formalisation contributors
-/
import Zhong.ClosedWalk
import Zhong.Algorithm.Move

/-!
# The shift primitive (Lemma 1 of Zhong 2023)

This file formalises Lemma 1 of Zhong (2023): the explicit operation sequence

`θ_m = L D R D L^{m-1} (R U L D R)^{m-2} U² R D² L U R U`

on a `3 × m` board whose blank is at `(2, 0)`.  Acting `θ_m` moves the first row
`B(0, 0:m)` down to the second row `B(1, 0:m)`, fixes the third row, and returns the
blank to `(2, 0)`.

The proof decomposes `θ_m` into

* the head `L D R D L^{m-1}`, which walks the blank from `(2,0)` to `(0,m-1)`;
* the sweep `(R U L D R)^{m-2}`, which processes the columns from right to left;
* the tail `U² R D² L U R U`, which returns the blank to `(2,0)`.

The sweep is handled by a general induction (`sweepWord_apply`) that tracks the action
of `(R U L D R)^k` on the columns of the board.
-/

namespace Zhong

open Equiv

/-- The five-move block `R U L D R`, the workhorse of the sweep. -/
def sweepBlock : List Dir := [Dir.R, Dir.U, Dir.L, Dir.D, Dir.R]

/-- The head of the shift word: `L D R D L^{m-1}`. -/
def headWord (m : ℕ) : List Dir :=
  [Dir.L, Dir.D, Dir.R, Dir.D] ++ List.replicate (m - 1) Dir.L

/-- The tail of the shift word: `U² R D² L U R U`. -/
def tailWord : List Dir :=
  [Dir.U, Dir.U, Dir.R, Dir.D, Dir.D, Dir.L, Dir.U, Dir.R, Dir.U]

/-- `sweepWord k = (R U L D R)^k`. -/
def sweepWord : ℕ → List Dir
  | 0 => []
  | k + 1 => sweepWord k ++ sweepBlock

/-- The full shift word `θ_m`. -/
def shiftWord (m : ℕ) : List Dir :=
  headWord m ++ sweepWord (m - 2) ++ tailWord

@[simp] theorem sweepWord_zero : sweepWord 0 = [] := rfl

theorem sweepWord_succ (k : ℕ) : sweepWord (k + 1) = sweepWord k ++ sweepBlock := rfl

/-! ### The single sweep block

The block `R U L D R` starting at `(0, j)` (with `0 < j`) is the four-cycle
`(0,j) → (1,j-1) → (1,j) → (0,j-1) → (0,j)`. -/

/-- The predecessor column. -/
theorem fin_pred_lt {m j : ℕ} (hj : 0 < j) (hjm : j < m) : j - 1 < m :=
  Nat.lt_of_le_of_lt (Nat.sub_le _ _) hjm

/-- The product of the five transpositions of the sweep block. -/
theorem permOf_sweepBlock_eq {m : ℕ} (j : Fin m) (hj : 0 < j.val) :
    permOf ((0 : Fin 3), j) sweepBlock
      = Equiv.swap ((0 : Fin 3), j) ((0 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩)
        * Equiv.swap ((0 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩)
            ((1 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩)
        * Equiv.swap ((1 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩) ((1 : Fin 3), j)
        * Equiv.swap ((1 : Fin 3), j) ((0 : Fin 3), j)
        * Equiv.swap ((0 : Fin 3), j) ((0 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩) := by
  have hR : neighbor? ((0 : Fin 3), j) Dir.R
      = some ((0 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩) := neighbor?_mk_R hj
  have hU : neighbor? ((0 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩) Dir.U
      = some ((1 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩) := by
    simp
  have hL : neighbor? ((1 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩) Dir.L
      = some ((1 : Fin 3), j) := by
    have hlt : (⟨j.val - 1, fin_pred_lt hj j.isLt⟩ : Fin m).val + 1 < m := by
      simp only [Fin.val_mk]; omega
    have hfin : (⟨(⟨j.val - 1, fin_pred_lt hj j.isLt⟩ : Fin m).val + 1, hlt⟩ : Fin m) = j := by
      apply Fin.ext
      change (⟨j.val - 1, fin_pred_lt hj j.isLt⟩ : Fin m).val + 1 = j.val
      have hc : (⟨j.val - 1, fin_pred_lt hj j.isLt⟩ : Fin m).val = j.val - 1 := rfl
      omega
    rw [neighbor?_mk_L hlt, hfin]
  have hD : neighbor? ((1 : Fin 3), j) Dir.D
      = some ((0 : Fin 3), j) := by
    simp
  have hR2 : neighbor? ((0 : Fin 3), j) Dir.R
      = some ((0 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩) := hR
  unfold sweepBlock
  rw [permOf_cons_of_neighbor? hR, permOf_cons_of_neighbor? hU,
      permOf_cons_of_neighbor? hL, permOf_cons_of_neighbor? hD,
      permOf_cons_of_neighbor? hR2, permOf_nil, mul_one]
  group

/-- The product of the five transpositions of the sweep block is the four-cycle
`a → c → d → b → a`. -/
theorem fourCycle_apply_a {α : Type*} [DecidableEq α] {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (Equiv.swap a b * Equiv.swap b c * Equiv.swap c d * Equiv.swap d a * Equiv.swap a b) a
      = c := by
  rw [swap_mul_swap_mul_swap_mul_swap hab hac had hbc hbd hcd]
  change (Equiv.swap b c * Equiv.swap c d) (Equiv.swap a b a) = c
  rw [Equiv.swap_apply_left]
  exact swap_mul_swap_apply_left hbc hbd

theorem fourCycle_apply_b {α : Type*} [DecidableEq α] {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (Equiv.swap a b * Equiv.swap b c * Equiv.swap c d * Equiv.swap d a * Equiv.swap a b) b
      = a := by
  rw [swap_mul_swap_mul_swap_mul_swap hab hac had hbc hbd hcd]
  change (Equiv.swap b c * Equiv.swap c d) (Equiv.swap a b b) = a
  rw [Equiv.swap_apply_right]
  rw [show (Equiv.swap b c * Equiv.swap c d) a = a from by
    rw [Equiv.Perm.coe_mul, Function.comp_apply,
        Equiv.swap_apply_of_ne_of_ne hac had, Equiv.swap_apply_of_ne_of_ne hab hac]]

theorem fourCycle_apply_c {α : Type*} [DecidableEq α] {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (Equiv.swap a b * Equiv.swap b c * Equiv.swap c d * Equiv.swap d a * Equiv.swap a b) c
      = d := by
  rw [swap_mul_swap_mul_swap_mul_swap hab hac had hbc hbd hcd]
  change (Equiv.swap b c * Equiv.swap c d) (Equiv.swap a b c) = d
  rw [Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
  exact swap_mul_swap_apply_mid hcd hbc hbd

theorem fourCycle_apply_d {α : Type*} [DecidableEq α] {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (Equiv.swap a b * Equiv.swap b c * Equiv.swap c d * Equiv.swap d a * Equiv.swap a b) d
      = b := by
  rw [swap_mul_swap_mul_swap_mul_swap hab hac had hbc hbd hcd]
  change (Equiv.swap b c * Equiv.swap c d) (Equiv.swap a b d) = b
  rw [Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm]
  exact swap_mul_swap_apply_right hbd

/-- The four cells of a sweep block are pairwise distinct. -/
theorem sweepBlock_cells_ne {m : ℕ} (j : Fin m) (hj : 0 < j.val) :
    ((0 : Fin 3), j) ≠ ((0 : Fin 3), (⟨j.val - 1, fin_pred_lt hj j.isLt⟩ : Fin m)) ∧
    ((0 : Fin 3), j) ≠ ((1 : Fin 3), (⟨j.val - 1, fin_pred_lt hj j.isLt⟩ : Fin m)) ∧
    ((0 : Fin 3), j) ≠ ((1 : Fin 3), j) ∧
    ((0 : Fin 3), (⟨j.val - 1, fin_pred_lt hj j.isLt⟩ : Fin m))
        ≠ ((1 : Fin 3), (⟨j.val - 1, fin_pred_lt hj j.isLt⟩ : Fin m)) ∧
    ((0 : Fin 3), (⟨j.val - 1, fin_pred_lt hj j.isLt⟩ : Fin m)) ≠ ((1 : Fin 3), j) ∧
    ((1 : Fin 3), (⟨j.val - 1, fin_pred_lt hj j.isLt⟩ : Fin m)) ≠ ((1 : Fin 3), j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h
     have h2 := congrArg (fun x : Cell 3 m => (x.1.val, x.2.val)) h
     simp only [Prod.fst, Prod.snd, Fin.val_mk, Prod.mk.injEq] at h2
     omega)

/-- The block fixes cells outside its `2 × 2` support. -/
theorem permOf_sweepBlock_of_not_mem {m : ℕ} (j : Fin m) (hj : 0 < j.val)
    {x : Cell 3 m}
    (h1 : x ≠ ((0 : Fin 3), j))
    (h2 : x ≠ ((0 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩))
    (h3 : x ≠ ((1 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩))
    (h4 : x ≠ ((1 : Fin 3), j)) :
    permOf ((0 : Fin 3), j) sweepBlock x = x := by
  have hR : neighbor? ((0 : Fin 3), j) Dir.R
      = some ((0 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩) := neighbor?_mk_R hj
  have hU : neighbor? ((0 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩) Dir.U
      = some ((1 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩) := by
    simp
  have hL : neighbor? ((1 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩) Dir.L
      = some ((1 : Fin 3), j) := by
    have hlt : (⟨j.val - 1, fin_pred_lt hj j.isLt⟩ : Fin m).val + 1 < m := by
      simp only [Fin.val_mk]; omega
    have hfin : (⟨(⟨j.val - 1, fin_pred_lt hj j.isLt⟩ : Fin m).val + 1, hlt⟩ : Fin m) = j := by
      apply Fin.ext
      change (⟨j.val - 1, fin_pred_lt hj j.isLt⟩ : Fin m).val + 1 = j.val
      have hc : (⟨j.val - 1, fin_pred_lt hj j.isLt⟩ : Fin m).val = j.val - 1 := rfl
      omega
    rw [neighbor?_mk_L hlt, hfin]
  have hD : neighbor? ((1 : Fin 3), j) Dir.D
      = some ((0 : Fin 3), j) := by
    simp
  apply permOf_apply_of_not_mem_traceSet
  intro hmem
  unfold sweepBlock at hmem
  rw [traceSet_cons_of_neighbor? hR] at hmem
  rw [Finset.mem_insert] at hmem
  rcases hmem with h | hmem
  · exact h1 h
  rw [traceSet_cons_of_neighbor? hU] at hmem
  rw [Finset.mem_insert] at hmem
  rcases hmem with h | hmem
  · exact h2 h
  rw [traceSet_cons_of_neighbor? hL] at hmem
  rw [Finset.mem_insert] at hmem
  rcases hmem with h | hmem
  · exact h3 h
  rw [traceSet_cons_of_neighbor? hD] at hmem
  rw [Finset.mem_insert] at hmem
  rcases hmem with h | hmem
  · exact h4 h
  rw [traceSet_cons_of_neighbor? hR, traceSet_nil] at hmem
  rw [Finset.mem_insert] at hmem
  rcases hmem with h | hmem
  · exact h1 h
  rw [Finset.mem_singleton] at hmem
  exact h2 hmem

/-- The sweep block sends `(0,j)` to `(1,j-1)`. -/
theorem permOf_sweepBlock_a {m : ℕ} (j : Fin m) (hj : 0 < j.val) :
    permOf ((0 : Fin 3), j) sweepBlock ((0 : Fin 3), j)
      = ((1 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := sweepBlock_cells_ne j hj
  rw [permOf_sweepBlock_eq j hj]
  exact fourCycle_apply_a hab hac had hbc hbd hcd

/-- The sweep block sends `(0,j-1)` to `(0,j)`. -/
theorem permOf_sweepBlock_b {m : ℕ} (j : Fin m) (hj : 0 < j.val) :
    permOf ((0 : Fin 3), j) sweepBlock ((0 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩)
      = ((0 : Fin 3), j) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := sweepBlock_cells_ne j hj
  rw [permOf_sweepBlock_eq j hj]
  exact fourCycle_apply_b hab hac had hbc hbd hcd

/-- The sweep block sends `(1,j-1)` to `(1,j)`. -/
theorem permOf_sweepBlock_c {m : ℕ} (j : Fin m) (hj : 0 < j.val) :
    permOf ((0 : Fin 3), j) sweepBlock ((1 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩)
      = ((1 : Fin 3), j) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := sweepBlock_cells_ne j hj
  rw [permOf_sweepBlock_eq j hj]
  exact fourCycle_apply_c hab hac had hbc hbd hcd

/-- The sweep block sends `(1,j)` to `(0,j-1)`. -/
theorem permOf_sweepBlock_d {m : ℕ} (j : Fin m) (hj : 0 < j.val) :
    permOf ((0 : Fin 3), j) sweepBlock ((1 : Fin 3), j)
      = ((0 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := sweepBlock_cells_ne j hj
  rw [permOf_sweepBlock_eq j hj]
  exact fourCycle_apply_d hab hac had hbc hbd hcd

/-- The action of the sweep block as an if-then-else. -/
theorem permOf_sweepBlock_apply {m : ℕ} (j : Fin m) (hj : 0 < j.val) (x : Cell 3 m) :
    permOf ((0 : Fin 3), j) sweepBlock x =
      (if x = ((0 : Fin 3), j) then ((1 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩)
       else if x = ((1 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩) then ((1 : Fin 3), j)
       else if x = ((1 : Fin 3), j) then ((0 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩)
       else if x = ((0 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩) then ((0 : Fin 3), j)
       else x) := by
  by_cases h1 : x = ((0 : Fin 3), j)
  · subst h1; rw [if_pos rfl, permOf_sweepBlock_a j hj]
  · rw [if_neg h1]
    by_cases h2 : x = ((1 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩)
    · subst h2; rw [if_pos rfl, permOf_sweepBlock_c j hj]
    · rw [if_neg h2]
      by_cases h3 : x = ((1 : Fin 3), j)
      · subst h3; rw [if_pos rfl, permOf_sweepBlock_d j hj]
      · rw [if_neg h3]
        by_cases h4 : x = ((0 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩)
        · subst h4; rw [if_pos rfl, permOf_sweepBlock_b j hj]
        · rw [if_neg h4]
          exact permOf_sweepBlock_of_not_mem j hj h1 h4 h2 h3

/-- The sweep block returns the blank to `(0,j-1)`. -/
theorem trace_sweepBlock {m : ℕ} (j : Fin m) (hj : 0 < j.val) :
    trace ((0 : Fin 3), j) sweepBlock = ((0 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩) := by
  have hR : neighbor? ((0 : Fin 3), j) Dir.R
      = some ((0 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩) := neighbor?_mk_R hj
  have hU : neighbor? ((0 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩) Dir.U
      = some ((1 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩) := by
    simp
  have hL : neighbor? ((1 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩) Dir.L
      = some ((1 : Fin 3), j) := by
    have hlt : (⟨j.val - 1, fin_pred_lt hj j.isLt⟩ : Fin m).val + 1 < m := by
      simp only [Fin.val_mk]; omega
    have hfin : (⟨(⟨j.val - 1, fin_pred_lt hj j.isLt⟩ : Fin m).val + 1, hlt⟩ : Fin m) = j := by
      apply Fin.ext
      change (⟨j.val - 1, fin_pred_lt hj j.isLt⟩ : Fin m).val + 1 = j.val
      have hc : (⟨j.val - 1, fin_pred_lt hj j.isLt⟩ : Fin m).val = j.val - 1 := rfl
      omega
    rw [neighbor?_mk_L hlt, hfin]
  have hD : neighbor? ((1 : Fin 3), j) Dir.D
      = some ((0 : Fin 3), j) := by
    simp
  unfold sweepBlock
  rw [trace_cons_of_neighbor? hR, trace_cons_of_neighbor? hU,
      trace_cons_of_neighbor? hL, trace_cons_of_neighbor? hD, trace_cons_of_neighbor? hR,
      trace_nil]

/-! ### The sweep

`sweepFun m start k` is the action of `(R U L D R)^k` on a `3 × m` board when the
blank starts at `(0, start)`.  It moves the `k` rightmost columns `[start-k, start]` of
the first two rows: column `start-k` is sent to column `start`, and every column
`c > start-k` is sent to column `c-1` of the other row. -/

noncomputable def sweepFun (m : ℕ) (lo hi : ℕ) (hhi : hi < m) (x : Cell 3 m) :
    Cell 3 m :=
  if _ : x.1 = (2 : Fin 3) then x
  else if hlt : x.2.val < lo then x
  else if hgt : hi < x.2.val then x
  else if h0 : x.1 = (0 : Fin 3) then
    (if heq : x.2.val = lo then ((0 : Fin 3), (⟨hi, hhi⟩ : Fin m))
     else ((1 : Fin 3), (⟨x.2.val - 1, by omega⟩ : Fin m)))
  else
    (if heq : x.2.val = lo then ((1 : Fin 3), (⟨hi, hhi⟩ : Fin m))
     else ((0 : Fin 3), (⟨x.2.val - 1, by omega⟩ : Fin m)))

@[simp] theorem sweepFun_row2 {m : ℕ} (lo hi : ℕ) (hhi : hi < m) (c : Fin m) :
    sweepFun m lo hi hhi ((2 : Fin 3), c) = ((2 : Fin 3), c) := by
  unfold sweepFun
  rw [dif_pos rfl]

theorem sweepFun_of_lt {m : ℕ} (lo hi : ℕ) (hhi : hi < m) {r : Fin 3} {c : Fin m}
    (h : c.val < lo) :
    sweepFun m lo hi hhi (r, c) = (r, c) := by
  unfold sweepFun
  by_cases hr : (r, c).1 = (2 : Fin 3)
  · rw [dif_pos hr]
  · rw [dif_neg hr, dif_pos h]

theorem sweepFun_of_gt {m : ℕ} (lo hi : ℕ) (hhi : hi < m) {r : Fin 3} {c : Fin m}
    (h : hi < c.val) :
    sweepFun m lo hi hhi (r, c) = (r, c) := by
  unfold sweepFun
  by_cases hr : (r, c).1 = (2 : Fin 3)
  · rw [dif_pos hr]
  · rw [dif_neg hr]
    by_cases hlt : c.val < lo
    · rw [dif_pos hlt]
    · rw [dif_neg hlt, dif_pos h]

theorem sweepFun_row0_eq {m : ℕ} (lo hi : ℕ) (hhi : hi < m) (hle : lo ≤ hi) {c : Fin m}
    (h : c.val = lo) :
    sweepFun m lo hi hhi ((0 : Fin 3), c) = ((0 : Fin 3), (⟨hi, hhi⟩ : Fin m)) := by
  unfold sweepFun
  rw [dif_neg (by simp : ¬ ((0 : Fin 3), c).1 = (2 : Fin 3))]
  rw [dif_neg (by omega : ¬ c.val < lo)]
  rw [dif_neg (by omega : ¬ hi < c.val)]
  rw [dif_pos (by simp : ((0 : Fin 3), c).1 = (0 : Fin 3)), dif_pos h]

theorem sweepFun_row1_eq {m : ℕ} (lo hi : ℕ) (hhi : hi < m) (hle : lo ≤ hi) {c : Fin m}
    (h : c.val = lo) :
    sweepFun m lo hi hhi ((1 : Fin 3), c) = ((1 : Fin 3), (⟨hi, hhi⟩ : Fin m)) := by
  unfold sweepFun
  rw [dif_neg (by simp : ¬ ((1 : Fin 3), c).1 = (2 : Fin 3))]
  rw [dif_neg (by omega : ¬ c.val < lo)]
  rw [dif_neg (by omega : ¬ hi < c.val)]
  rw [dif_neg (by simp : ¬ ((1 : Fin 3), c).1 = (0 : Fin 3)), dif_pos h]

theorem sweepFun_row0_gt {m : ℕ} (lo hi : ℕ) (hhi : hi < m) {c : Fin m}
    (h1 : lo < c.val) (h2 : c.val ≤ hi) :
    sweepFun m lo hi hhi ((0 : Fin 3), c)
      = ((1 : Fin 3), (⟨c.val - 1, by omega⟩ : Fin m)) := by
  unfold sweepFun
  rw [dif_neg (by simp : ¬ ((0 : Fin 3), c).1 = (2 : Fin 3))]
  rw [dif_neg (by omega : ¬ c.val < lo)]
  rw [dif_neg (by omega : ¬ hi < c.val)]
  rw [dif_pos (by simp : ((0 : Fin 3), c).1 = (0 : Fin 3)),
      dif_neg (by omega : ¬ c.val = lo)]

theorem sweepFun_row1_gt {m : ℕ} (lo hi : ℕ) (hhi : hi < m) {c : Fin m}
    (h1 : lo < c.val) (h2 : c.val ≤ hi) :
    sweepFun m lo hi hhi ((1 : Fin 3), c)
      = ((0 : Fin 3), (⟨c.val - 1, by omega⟩ : Fin m)) := by
  unfold sweepFun
  rw [dif_neg (by simp : ¬ ((1 : Fin 3), c).1 = (2 : Fin 3))]
  rw [dif_neg (by omega : ¬ c.val < lo)]
  rw [dif_neg (by omega : ¬ hi < c.val)]
  rw [dif_neg (by simp : ¬ ((1 : Fin 3), c).1 = (0 : Fin 3)),
      dif_neg (by omega : ¬ c.val = lo)]

/-- The blank of the sweep is the trace. -/
theorem trace_sweepWord {m : ℕ} (k : ℕ) :
    ∀ (start : ℕ) (hk : k ≤ start) (hstart : start < m),
      trace ((0 : Fin 3), (⟨start, hstart⟩ : Fin m)) (sweepWord k)
        = ((0 : Fin 3), (⟨start - k, by omega⟩ : Fin m)) := by
  induction k with
  | zero =>
      intro start _ hstart
      simp only [sweepWord_zero, trace_nil, Nat.sub_zero]
  | succ k ih =>
      intro start hk hstart
      rw [sweepWord_succ, trace_append, ih start (by omega) hstart]
      have hc : (⟨start - k, by omega⟩ : Fin m).val = start - k := rfl
      have hj : 0 < (⟨start - k, by omega⟩ : Fin m).val := by omega
      rw [trace_sweepBlock (⟨start - k, by omega⟩ : Fin m) hj]
      congr 1

/-- The sweep is the identity when its interval is empty. -/
theorem sweepFun_self {m : ℕ} (hi : ℕ) (hhi : hi < m) (x : Cell 3 m) :
    sweepFun m hi hi hhi x = x := by
  unfold sweepFun
  by_cases h2 : x.1 = (2 : Fin 3)
  · rw [dif_pos h2]
  · rw [dif_neg h2]
    by_cases hlt : x.2.val < hi
    · rw [dif_pos hlt]
    · rw [dif_neg hlt]
      by_cases hgt : hi < x.2.val
      · rw [dif_pos hgt]
      · rw [dif_neg hgt]
        by_cases h0 : x.1 = (0 : Fin 3)
        · rw [dif_pos h0]
          by_cases heq : x.2.val = hi
          · rw [dif_pos heq]
            have hx2 : x.2 = (⟨hi, hhi⟩ : Fin m) := Fin.ext (by rw [heq])
            exact Prod.ext h0.symm hx2.symm
          · rw [dif_neg heq]
            exact absurd (by omega : x.2.val = hi) heq
        · rw [dif_neg h0]
          by_cases heq : x.2.val = hi
          · rw [dif_pos heq]
            have hx2 : x.2 = (⟨hi, hhi⟩ : Fin m) := Fin.ext (by rw [heq])
            have h1 : x.1 = (1 : Fin 3) := by
              apply Fin.ext
              have := x.1.isLt
              omega
            exact Prod.ext h1.symm hx2.symm
          · rw [dif_neg heq]
            exact absurd (by omega : x.2.val = hi) heq

/-- One more sweep block extends the sweep by one column. -/
theorem sweepFun_block {m : ℕ} (lo hi : ℕ) (hhi : hi < m) (hle : lo ≤ hi) (j : Fin m)
    (hj : j.val = lo) (hj0 : 0 < j.val) (x : Cell 3 m) :
    sweepFun m lo hi hhi (permOf ((0 : Fin 3), j) sweepBlock x)
      = sweepFun m (lo - 1) hi hhi x := by
  rw [permOf_sweepBlock_apply j hj0]
  by_cases h1 : x = ((0 : Fin 3), j)
  · subst h1
    rw [if_pos rfl,
        sweepFun_of_lt (lo := lo) (hi := hi) (hhi := hhi) (r := (1 : Fin 3))
          (c := (⟨j.val - 1, fin_pred_lt hj0 j.isLt⟩ : Fin m)) (by rw [Fin.val_mk]; omega)]
    rw [sweepFun_row0_gt (lo := lo - 1) (hi := hi) (hhi := hhi) (c := j)
      (by omega) (by omega)]
  · rw [if_neg h1]
    by_cases h2 : x = ((1 : Fin 3), (⟨j.val - 1, fin_pred_lt hj0 j.isLt⟩ : Fin m))
    · subst h2
      rw [if_pos rfl, sweepFun_row1_eq (lo := lo) (hi := hi) (hhi := hhi) (hle := hle)
        (c := j) hj]
      rw [sweepFun_row1_eq (lo := lo - 1) (hi := hi) (hhi := hhi) (hle := by omega)
        (c := (⟨j.val - 1, fin_pred_lt hj0 j.isLt⟩ : Fin m)) (by rw [Fin.val_mk]; omega)]
    · rw [if_neg h2]
      by_cases h3 : x = ((1 : Fin 3), j)
      · subst h3
        rw [if_pos rfl,
            sweepFun_of_lt (lo := lo) (hi := hi) (hhi := hhi) (r := (0 : Fin 3))
              (c := (⟨j.val - 1, fin_pred_lt hj0 j.isLt⟩ : Fin m)) (by rw [Fin.val_mk]; omega)]
        rw [sweepFun_row1_gt (lo := lo - 1) (hi := hi) (hhi := hhi) (c := j)
          (by omega) (by omega)]
      · rw [if_neg h3]
        by_cases h4 : x = ((0 : Fin 3), (⟨j.val - 1, fin_pred_lt hj0 j.isLt⟩ : Fin m))
        · subst h4
          rw [if_pos rfl, sweepFun_row0_eq (lo := lo) (hi := hi) (hhi := hhi) (hle := hle)
            (c := j) hj]
          rw [sweepFun_row0_eq (lo := lo - 1) (hi := hi) (hhi := hhi) (hle := by omega)
            (c := (⟨j.val - 1, fin_pred_lt hj0 j.isLt⟩ : Fin m)) (by rw [Fin.val_mk]; omega)]
        · rw [if_neg h4]
          by_cases hrow2 : x.1 = (2 : Fin 3)
          · have hxeq : x = ((2 : Fin 3), x.2) := Prod.ext hrow2 rfl
            rw [hxeq,
                sweepFun_row2 (lo := lo) (hi := hi) (hhi := hhi) (c := x.2),
                sweepFun_row2 (lo := lo - 1) (hi := hi) (hhi := hhi) (c := x.2)]
          · have hne_lo : x.2.val ≠ lo := by
              intro heq
              have hx01 : x.1.val = 0 ∨ x.1.val = 1 := by
                have := x.1.isLt; omega
              rcases hx01 with h | h
              · exact h1 (Prod.ext (Fin.ext h) (Fin.ext (by rw [heq, hj])))
              · exact h3 (Prod.ext (Fin.ext h) (Fin.ext (by rw [heq, hj])))
            have hne_lo1 : x.2.val ≠ lo - 1 := by
              intro heq
              have hx01 : x.1.val = 0 ∨ x.1.val = 1 := by
                have := x.1.isLt; omega
              rcases hx01 with h | h
              · exact h4 (Prod.ext (Fin.ext h) (Fin.ext (by show x.2.val = j.val - 1; omega)))
              · exact h2 (Prod.ext (Fin.ext h) (Fin.ext (by show x.2.val = j.val - 1; omega)))
            by_cases hlt : x.2.val < lo - 1
            · rw [sweepFun_of_lt (lo := lo) (hi := hi) (hhi := hhi) (r := x.1) (c := x.2)
                    (by omega),
                  sweepFun_of_lt (lo := lo - 1) (hi := hi) (hhi := hhi) (r := x.1) (c := x.2)
                    hlt]
            · by_cases hgt : hi < x.2.val
              · rw [sweepFun_of_gt (lo := lo) (hi := hi) (hhi := hhi) (r := x.1) (c := x.2)
                      (by omega),
                    sweepFun_of_gt (lo := lo - 1) (hi := hi) (hhi := hhi) (r := x.1) (c := x.2)
                      hgt]
              · have hlo : lo < x.2.val := by omega
                by_cases hx0 : x.1 = (0 : Fin 3)
                · have hxeq : x = ((0 : Fin 3), x.2) := Prod.ext hx0 rfl
                  rw [hxeq,
                      sweepFun_row0_gt (lo := lo) (hi := hi) (hhi := hhi) (c := x.2)
                        hlo (by omega),
                      sweepFun_row0_gt (lo := lo - 1) (hi := hi) (hhi := hhi) (c := x.2)
                        (by omega) (by omega)]
                · have hx1 : x.1 = (1 : Fin 3) := by
                    apply Fin.ext
                    have := x.1.isLt; omega
                  have hxeq : x = ((1 : Fin 3), x.2) := Prod.ext hx1 rfl
                  rw [hxeq,
                      sweepFun_row1_gt (lo := lo) (hi := hi) (hhi := hhi) (c := x.2)
                        hlo (by omega),
                      sweepFun_row1_gt (lo := lo - 1) (hi := hi) (hhi := hhi) (c := x.2)
                        (by omega) (by omega)]

/-- The action of the sweep word is `sweepFun`. -/
theorem permOf_sweepWord {m : ℕ} (k : ℕ) :
    ∀ (start : ℕ) (hk : k ≤ start) (hstart : start < m) (x : Cell 3 m),
      permOf ((0 : Fin 3), (⟨start, hstart⟩ : Fin m)) (sweepWord k) x
        = sweepFun m (start - k) start hstart x := by
  induction k with
  | zero =>
      intro start _ hstart x
      rw [sweepWord_zero, permOf_nil]
      change x = sweepFun m (start - 0) start hstart x
      rw [Nat.sub_zero]
      exact (sweepFun_self start hstart x).symm
  | succ k ih =>
      intro start hk hstart x
      rw [sweepWord_succ, permOf_append, trace_sweepWord k start (by omega) hstart]
      change permOf ((0 : Fin 3), (⟨start, hstart⟩ : Fin m)) (sweepWord k)
          (permOf ((0 : Fin 3), (⟨start - k, by omega⟩ : Fin m)) sweepBlock x)
        = sweepFun m (start - (k + 1)) start hstart x
      rw [ih start (by omega) hstart]
      exact sweepFun_block (start - k) start hstart (by omega)
        (⟨start - k, by omega⟩ : Fin m) rfl (by show 0 < start - k; omega) x

/-- A four-edge path induces the five-cycle `a → b → c → d → e → a`. -/
theorem fiveCycle_apply_a {α : Type*} [DecidableEq α] {a b c d e : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c)
    (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    (Equiv.swap a b * Equiv.swap b c * Equiv.swap c d * Equiv.swap d e) a = b := by
  change Equiv.swap a b (Equiv.swap b c (Equiv.swap c d (Equiv.swap d e a))) = b
  rw [Equiv.swap_apply_of_ne_of_ne had hae, Equiv.swap_apply_of_ne_of_ne hac had,
      Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left]

theorem fiveCycle_apply_d {α : Type*} [DecidableEq α] {a b c d e : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c)
    (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    (Equiv.swap a b * Equiv.swap b c * Equiv.swap c d * Equiv.swap d e) d = e := by
  change Equiv.swap a b (Equiv.swap b c (Equiv.swap c d (Equiv.swap d e d))) = e
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hce.symm hde.symm,
      Equiv.swap_apply_of_ne_of_ne hbe.symm hce.symm,
      Equiv.swap_apply_of_ne_of_ne hae.symm hbe.symm]

theorem fiveCycle_apply_e {α : Type*} [DecidableEq α] {a b c d e : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c)
    (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    (Equiv.swap a b * Equiv.swap b c * Equiv.swap c d * Equiv.swap d e) e = a := by
  change Equiv.swap a b (Equiv.swap b c (Equiv.swap c d (Equiv.swap d e e))) = a
  rw [Equiv.swap_apply_right, Equiv.swap_apply_right, Equiv.swap_apply_right,
      Equiv.swap_apply_right]

/-! ### The horizontal run `L^k` -/

/-- A horizontal `L`-run induces the successor map on its row, fixes the cells outside
its row, and fixes the cells to the left of its start and to the right of its end. -/
theorem permOf_replicate_L {m : ℕ} (k : ℕ) :
    ∀ (c : Fin m) (hk : c.val + k < m),
      (∀ i (hi : i < k),
          permOf ((0 : Fin 3), c) (List.replicate k Dir.L)
            ((0 : Fin 3), (⟨c.val + i, by omega⟩ : Fin m))
            = ((0 : Fin 3), (⟨c.val + i + 1, by omega⟩ : Fin m))) ∧
      (permOf ((0 : Fin 3), c) (List.replicate k Dir.L)
            ((0 : Fin 3), (⟨c.val + k, hk⟩ : Fin m)) = ((0 : Fin 3), c)) ∧
      (∀ x : Cell 3 m,
          (x.1.val ≠ 0 ∨ x.2.val < c.val ∨ c.val + k < x.2.val) →
          permOf ((0 : Fin 3), c) (List.replicate k Dir.L) x = x) := by
  induction k with
  | zero =>
      intro c hk
      refine ⟨?_, ?_, ?_⟩
      · intro i hi; omega
      · rw [List.replicate_zero, permOf_nil]
        congr 1
      · intro x _
        rw [List.replicate_zero, permOf_nil]
        rfl
  | succ k ih =>
      intro c hk
      have hL : neighbor? ((0 : Fin 3), c) Dir.L
          = some ((0 : Fin 3), (⟨c.val + 1, by omega⟩ : Fin m)) := by
        have hlt : c.val + 1 < m := by omega
        have h := neighbor?_mk_L (x := (0 : Fin 3)) (y := c) hlt
        rw [h]
      have hk1 : (⟨c.val + 1, by omega⟩ : Fin m).val + k < m := by
        simp only [Fin.val_mk]; omega
      obtain ⟨ih1, ih2, ih3⟩ := ih (⟨c.val + 1, by omega⟩ : Fin m) hk1
      have hstep : ∀ x : Cell 3 m,
          permOf ((0 : Fin 3), c) (List.replicate (k + 1) Dir.L) x
            = Equiv.swap ((0 : Fin 3), c) ((0 : Fin 3), (⟨c.val + 1, by omega⟩ : Fin m))
              (permOf ((0 : Fin 3), (⟨c.val + 1, by omega⟩ : Fin m))
                (List.replicate k Dir.L) x) := by
        intro x
        rw [List.replicate_succ, permOf_cons_of_neighbor? hL]
        rfl
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        rw [hstep]
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · have hfix := ih3 ((0 : Fin 3), c)
            (Or.inr (Or.inl (by show c.val < c.val + 1; omega)))
          rw [show ((0 : Fin 3), (⟨c.val + 0, by omega⟩ : Fin m)) = ((0 : Fin 3), c) from
                Prod.ext rfl (Fin.ext (by simp))]
          rw [hfix, Equiv.swap_apply_left]
        · have hcell : ((0 : Fin 3), (⟨c.val + i, by omega⟩ : Fin m))
              = ((0 : Fin 3), (⟨(⟨c.val + 1, by omega⟩ : Fin m).val + (i - 1),
                  by omega⟩ : Fin m)) :=
            Prod.ext rfl (Fin.ext (by simp only [Fin.val_mk]; omega))
          rw [hcell]
          have h := ih1 (i - 1) (by omega)
          rw [h]
          have hne1 : ((0 : Fin 3), (⟨(⟨c.val + 1, by omega⟩ : Fin m).val + (i - 1) + 1,
              by omega⟩ : Fin m)) ≠ ((0 : Fin 3), c) := by
            intro hcon
            have := congrArg (fun x : Cell 3 m => (x.1.val, x.2.val)) hcon
            simp only [Prod.fst, Prod.snd, Fin.val_mk, Prod.mk.injEq] at this
            omega
          have hne2 : ((0 : Fin 3), (⟨(⟨c.val + 1, by omega⟩ : Fin m).val + (i - 1) + 1,
              by omega⟩ : Fin m)) ≠ ((0 : Fin 3), (⟨c.val + 1, by omega⟩ : Fin m)) := by
            intro hcon
            have := congrArg (fun x : Cell 3 m => (x.1.val, x.2.val)) hcon
            simp only [Prod.fst, Prod.snd, Fin.val_mk, Prod.mk.injEq] at this
            omega
          rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
          congr 1
          apply Fin.ext
          simp only [Fin.val_mk]
          omega
      · rw [hstep]
        have hcell : ((0 : Fin 3), (⟨c.val + (k + 1), by omega⟩ : Fin m))
            = ((0 : Fin 3), (⟨(⟨c.val + 1, by omega⟩ : Fin m).val + k, by omega⟩ : Fin m)) :=
          Prod.ext rfl (Fin.ext (by simp only [Fin.val_mk]; omega))
        rw [hcell]
        have h := ih2
        rw [h, Equiv.swap_apply_right]
      · intro x hx
        rw [hstep]
        have hfix : permOf ((0 : Fin 3), (⟨c.val + 1, by omega⟩ : Fin m))
            (List.replicate k Dir.L) x = x := by
          apply ih3
          rcases hx with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl (by show x.2.val < c.val + 1; omega))
          · exact Or.inr (Or.inr (by show c.val + 1 + k < x.2.val; omega))
        rw [hfix]
        have hne1 : x ≠ ((0 : Fin 3), c) := by
          intro hcon
          rcases hx with h | h | h
          · exact h (by simp [hcon])
          · rw [hcon] at h
            simp only [Prod.snd, Fin.val_mk] at h
            omega
          · rw [hcon] at h
            simp only [Prod.snd, Fin.val_mk] at h
            omega
        have hne2 : x ≠ ((0 : Fin 3), (⟨c.val + 1, by omega⟩ : Fin m)) := by
          intro hcon
          rcases hx with h | h | h
          · exact h (by simp [hcon])
          · rw [hcon] at h
            simp only [Prod.snd, Fin.val_mk] at h
            omega
          · rw [hcon] at h
            simp only [Prod.snd, Fin.val_mk] at h
            omega
        rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
/-! ### The head `L D R D L^{m-1}` -/

theorem trace_replicate_L {m : ℕ} (k : ℕ) :
    ∀ (c : Fin m) (hk : c.val + k < m),
      trace ((0 : Fin 3), c) (List.replicate k Dir.L)
        = ((0 : Fin 3), (⟨c.val + k, hk⟩ : Fin m)) := by
  induction k with
  | zero =>
      intro c hk
      rw [List.replicate_zero, trace_nil]
      exact Prod.ext rfl (Fin.ext (by simp))
  | succ k ih =>
      intro c hk
      have hlt : c.val + 1 < m := by omega
      have hL : neighbor? ((0 : Fin 3), c) Dir.L
          = some ((0 : Fin 3), (⟨c.val + 1, hlt⟩ : Fin m)) :=
        neighbor?_mk_L (x := (0 : Fin 3)) (y := c) hlt
      rw [List.replicate_succ, trace_cons_of_neighbor? hL]
      rw [ih (⟨c.val + 1, hlt⟩ : Fin m) (by simp only [Fin.val_mk]; omega)]
      exact Prod.ext rfl (Fin.ext (by simp only [Fin.val_mk]; omega))

theorem trace_LDRD {m : ℕ} (hm : 1 < m) :
    trace ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) [Dir.L, Dir.D, Dir.R, Dir.D]
      = ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) := by
  have hL : neighbor? ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) Dir.L
      = some ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) := by
    have hlt : (0 : ℕ) + 1 < m := by omega
    have h := neighbor?_mk_L (x := (2 : Fin 3)) (y := (⟨0, by omega⟩ : Fin m)) hlt
    rw [h]
  have hD1 : neighbor? ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.D
      = some ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) :=
    neighbor?_mk_D (x := (2 : Fin 3)) (y := (⟨1, hm⟩ : Fin m)) (by decide)
  have hR : neighbor? ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.R
      = some ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) := by
    simp
  have hD2 : neighbor? ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) Dir.D
      = some ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) :=
    neighbor?_mk_D (x := (1 : Fin 3)) (y := (⟨0, by omega⟩ : Fin m)) (by decide)
  rw [trace_cons_of_neighbor? hL, trace_cons_of_neighbor? hD1,
      trace_cons_of_neighbor? hR, trace_cons_of_neighbor? hD2, trace_nil]

theorem trace_headWord {m : ℕ} (hm : 1 < m) :
    trace ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) (headWord m)
      = ((0 : Fin 3), (⟨m - 1, by omega⟩ : Fin m)) := by
  unfold headWord
  rw [trace_append, trace_LDRD hm]
  rw [trace_replicate_L (m - 1) (⟨0, by omega⟩ : Fin m) (by simp only [Fin.val_mk]; omega)]
  exact Prod.ext rfl (Fin.ext (by simp))

/-- The product of the four transpositions of the head. -/
theorem permOf_LDRD_eq {m : ℕ} (hm : 1 < m) :
    permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) [Dir.L, Dir.D, Dir.R, Dir.D]
      = Equiv.swap ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) ((2 : Fin 3), (⟨1, hm⟩ : Fin m))
        * Equiv.swap ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) ((1 : Fin 3), (⟨1, hm⟩ : Fin m))
        * Equiv.swap ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) ((1 : Fin 3), (⟨0, by omega⟩ : Fin m))
        * Equiv.swap ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) := by
  have hL : neighbor? ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) Dir.L
      = some ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) := by
    have hlt : (0 : ℕ) + 1 < m := by omega
    have h := neighbor?_mk_L (x := (2 : Fin 3)) (y := (⟨0, by omega⟩ : Fin m)) hlt
    rw [h]
  have hD1 : neighbor? ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.D
      = some ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) :=
    neighbor?_mk_D (x := (2 : Fin 3)) (y := (⟨1, hm⟩ : Fin m)) (by decide)
  have hR : neighbor? ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.R
      = some ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) := by
    simp
  have hD2 : neighbor? ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) Dir.D
      = some ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) :=
    neighbor?_mk_D (x := (1 : Fin 3)) (y := (⟨0, by omega⟩ : Fin m)) (by decide)
  rw [permOf_cons_of_neighbor? hL, permOf_cons_of_neighbor? hD1,
      permOf_cons_of_neighbor? hR, permOf_cons_of_neighbor? hD2, permOf_nil, mul_one]
  group

/-- The head fixes cells outside its five-cell support. -/
theorem permOf_LDRD_of_not_mem {m : ℕ} (hm : 1 < m) {x : Cell 3 m}
    (h1 : x ≠ ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)))
    (h2 : x ≠ ((2 : Fin 3), (⟨1, hm⟩ : Fin m)))
    (h3 : x ≠ ((1 : Fin 3), (⟨1, hm⟩ : Fin m)))
    (h4 : x ≠ ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)))
    (h5 : x ≠ ((0 : Fin 3), (⟨0, by omega⟩ : Fin m))) :
    permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) [Dir.L, Dir.D, Dir.R, Dir.D] x = x := by
  have hL : neighbor? ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) Dir.L
      = some ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) := by
    have hlt : (0 : ℕ) + 1 < m := by omega
    have h := neighbor?_mk_L (x := (2 : Fin 3)) (y := (⟨0, by omega⟩ : Fin m)) hlt
    rw [h]
  have hD1 : neighbor? ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.D
      = some ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) :=
    neighbor?_mk_D (x := (2 : Fin 3)) (y := (⟨1, hm⟩ : Fin m)) (by decide)
  have hR : neighbor? ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.R
      = some ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) := by
    simp
  have hD2 : neighbor? ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) Dir.D
      = some ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) :=
    neighbor?_mk_D (x := (1 : Fin 3)) (y := (⟨0, by omega⟩ : Fin m)) (by decide)
  apply permOf_apply_of_not_mem_traceSet
  intro hmem
  rw [traceSet_cons_of_neighbor? hL] at hmem
  rw [Finset.mem_insert] at hmem
  rcases hmem with h | hmem
  · exact h1 h
  rw [traceSet_cons_of_neighbor? hD1] at hmem
  rw [Finset.mem_insert] at hmem
  rcases hmem with h | hmem
  · exact h2 h
  rw [traceSet_cons_of_neighbor? hR] at hmem
  rw [Finset.mem_insert] at hmem
  rcases hmem with h | hmem
  · exact h3 h
  rw [traceSet_cons_of_neighbor? hD2] at hmem
  rw [Finset.mem_insert] at hmem
  rcases hmem with h | hmem
  · exact h4 h
  rw [traceSet_nil, Finset.mem_singleton] at hmem
  exact h5 hmem

/-- The five cells of the head are pairwise distinct. -/
theorem LDRD_cells_ne {m : ℕ} (hm : 1 < m) :
    ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) ≠ ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) ∧
    ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) ≠ ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) ∧
    ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) ≠ ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) ∧
    ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) ≠ ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) ∧
    ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) ≠ ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) ∧
    ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) ≠ ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) ∧
    ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) ≠ ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) ∧
    ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) ≠ ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) ∧
    ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) ≠ ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) ∧
    ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) ≠ ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h
     have h2 := congrArg (fun x : Cell 3 m => (x.1.val, x.2.val)) h
     simp only [Prod.fst, Prod.snd, Fin.val_mk, Prod.mk.injEq] at h2
     omega)

/-- The head sends `(1,0)` to `(0,0)`. -/
theorem permOf_LDRD_d {m : ℕ} (hm : 1 < m) :
    permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) [Dir.L, Dir.D, Dir.R, Dir.D]
        ((1 : Fin 3), (⟨0, by omega⟩ : Fin m))
      = ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) := by
  obtain ⟨hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde⟩ := LDRD_cells_ne hm
  rw [permOf_LDRD_eq hm]
  exact fiveCycle_apply_d hab hac had hae hbc hbd hbe hcd hce hde

/-- The head sends `(0,0)` to `(2,0)`. -/
theorem permOf_LDRD_e {m : ℕ} (hm : 1 < m) :
    permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) [Dir.L, Dir.D, Dir.R, Dir.D]
        ((0 : Fin 3), (⟨0, by omega⟩ : Fin m))
      = ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) := by
  obtain ⟨hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde⟩ := LDRD_cells_ne hm
  rw [permOf_LDRD_eq hm]
  exact fiveCycle_apply_e hab hac had hae hbc hbd hbe hcd hce hde

/-- The head sends `(2,0)` to `(2,1)`. -/
theorem permOf_LDRD_a {m : ℕ} (hm : 1 < m) :
    permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) [Dir.L, Dir.D, Dir.R, Dir.D]
        ((2 : Fin 3), (⟨0, by omega⟩ : Fin m))
      = ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) := by
  obtain ⟨hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde⟩ := LDRD_cells_ne hm
  rw [permOf_LDRD_eq hm]
  exact fiveCycle_apply_a hab hac had hae hbc hbd hbe hcd hce hde

/-- The head fixes `(0,j)` for `j ≥ 1`. -/
theorem permOf_LDRD_fix_0 {m : ℕ} (hm : 1 < m) {j : ℕ} (hj : j < m) (hj1 : 1 ≤ j) :
    permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) [Dir.L, Dir.D, Dir.R, Dir.D]
        ((0 : Fin 3), (⟨j, hj⟩ : Fin m))
      = ((0 : Fin 3), (⟨j, hj⟩ : Fin m)) := by
  apply permOf_LDRD_of_not_mem hm
  · intro h; have := congrArg (fun x : Cell 3 m => (x.1.val, x.2.val)) h
    simp only [Prod.fst, Prod.snd, Fin.val_mk, Prod.mk.injEq] at this; omega
  · intro h; have := congrArg (fun x : Cell 3 m => (x.1.val, x.2.val)) h
    simp only [Prod.fst, Prod.snd, Fin.val_mk, Prod.mk.injEq] at this; omega
  · intro h; have := congrArg (fun x : Cell 3 m => (x.1.val, x.2.val)) h
    simp only [Prod.fst, Prod.snd, Fin.val_mk, Prod.mk.injEq] at this; omega
  · intro h; have := congrArg (fun x : Cell 3 m => (x.1.val, x.2.val)) h
    simp only [Prod.fst, Prod.snd, Fin.val_mk, Prod.mk.injEq] at this; omega
  · intro h; have := congrArg (fun x : Cell 3 m => (x.1.val, x.2.val)) h
    simp only [Prod.fst, Prod.snd, Fin.val_mk, Prod.mk.injEq] at this; omega

/-- The head fixes `(2,c)` for `c ≥ 2`. -/
theorem permOf_LDRD_fix_2 {m : ℕ} (hm : 1 < m) {c : ℕ} (hc : c < m) (hc2 : 2 ≤ c) :
    permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) [Dir.L, Dir.D, Dir.R, Dir.D]
        ((2 : Fin 3), (⟨c, hc⟩ : Fin m))
      = ((2 : Fin 3), (⟨c, hc⟩ : Fin m)) := by
  apply permOf_LDRD_of_not_mem hm
  · intro h; have := congrArg (fun x : Cell 3 m => (x.1.val, x.2.val)) h
    simp only [Prod.fst, Prod.snd, Fin.val_mk, Prod.mk.injEq] at this; omega
  · intro h; have := congrArg (fun x : Cell 3 m => (x.1.val, x.2.val)) h
    simp only [Prod.fst, Prod.snd, Fin.val_mk, Prod.mk.injEq] at this; omega
  · intro h; have := congrArg (fun x : Cell 3 m => (x.1.val, x.2.val)) h
    simp only [Prod.fst, Prod.snd, Fin.val_mk, Prod.mk.injEq] at this; omega
  · intro h; have := congrArg (fun x : Cell 3 m => (x.1.val, x.2.val)) h
    simp only [Prod.fst, Prod.snd, Fin.val_mk, Prod.mk.injEq] at this; omega
  · intro h; have := congrArg (fun x : Cell 3 m => (x.1.val, x.2.val)) h
    simp only [Prod.fst, Prod.snd, Fin.val_mk, Prod.mk.injEq] at this; omega

/-- The action of the head as `eps ∘ λ`. -/
theorem permOf_headWord_eq {m : ℕ} (hm : 1 < m) :
    permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) (headWord m)
      = permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) [Dir.L, Dir.D, Dir.R, Dir.D]
        * permOf ((0 : Fin 3), (⟨0, by omega⟩ : Fin m))
            (List.replicate (m - 1) Dir.L) := by
  unfold headWord
  rw [permOf_append, trace_LDRD hm]

/-- The head sends `(0,j)` to `(0,j+1)` for `j+1 < m`. -/
theorem permOf_headWord_0 {m : ℕ} (hm : 1 < m) (j : ℕ) (hj : j + 1 < m) :
    permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) (headWord m)
        ((0 : Fin 3), (⟨j, by omega⟩ : Fin m))
      = ((0 : Fin 3), (⟨j + 1, hj⟩ : Fin m)) := by
  rw [permOf_headWord_eq hm]
  change permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) [Dir.L, Dir.D, Dir.R, Dir.D]
      (permOf ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) (List.replicate (m - 1) Dir.L)
        ((0 : Fin 3), (⟨j, by omega⟩ : Fin m)))
    = ((0 : Fin 3), (⟨j + 1, hj⟩ : Fin m))
  have hlam := (permOf_replicate_L (m - 1) (⟨0, by omega⟩ : Fin m)
    (by simp only [Fin.val_mk]; omega)).1 j (by omega)
  rw [show ((0 : Fin 3), (⟨j, by omega⟩ : Fin m))
        = ((0 : Fin 3), (⟨(0 : ℕ) + j, by omega⟩ : Fin m)) from Prod.ext rfl (Fin.ext (by simp))]
  rw [hlam]
  rw [show permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) [Dir.L, Dir.D, Dir.R, Dir.D]
        ((0 : Fin 3), (⟨(0 : ℕ) + j + 1, by omega⟩ : Fin m))
      = ((0 : Fin 3), (⟨(0 : ℕ) + j + 1, by omega⟩ : Fin m)) from
      permOf_LDRD_fix_0 hm (by omega) (by omega)]
  exact Prod.ext rfl (Fin.ext (by simp))

/-- The head sends `(0,m-1)` to `(2,0)`. -/
theorem permOf_headWord_0_last {m : ℕ} (hm : 1 < m) :
    permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) (headWord m)
        ((0 : Fin 3), (⟨m - 1, by omega⟩ : Fin m))
      = ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) := by
  rw [permOf_headWord_eq hm]
  change permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) [Dir.L, Dir.D, Dir.R, Dir.D]
      (permOf ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) (List.replicate (m - 1) Dir.L)
        ((0 : Fin 3), (⟨m - 1, by omega⟩ : Fin m)))
    = ((2 : Fin 3), (⟨0, by omega⟩ : Fin m))
  have hlam := (permOf_replicate_L (m - 1) (⟨0, by omega⟩ : Fin m)
    (by simp only [Fin.val_mk]; omega)).2.1
  rw [show ((0 : Fin 3), (⟨m - 1, by omega⟩ : Fin m))
        = ((0 : Fin 3), (⟨(0 : ℕ) + (m - 1), by omega⟩ : Fin m)) from
        Prod.ext rfl (Fin.ext (by simp))]
  rw [hlam]
  rw [show permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) [Dir.L, Dir.D, Dir.R, Dir.D]
        ((0 : Fin 3), (⟨0, by omega⟩ : Fin m))
      = ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) from permOf_LDRD_e hm]

/-- The head sends `(1,0)` to `(0,0)`. -/
theorem permOf_headWord_10 {m : ℕ} (hm : 1 < m) :
    permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) (headWord m)
        ((1 : Fin 3), (⟨0, by omega⟩ : Fin m))
      = ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) := by
  rw [permOf_headWord_eq hm]
  change permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) [Dir.L, Dir.D, Dir.R, Dir.D]
      (permOf ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) (List.replicate (m - 1) Dir.L)
        ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)))
    = ((0 : Fin 3), (⟨0, by omega⟩ : Fin m))
  have hlam := (permOf_replicate_L (m - 1) (⟨0, by omega⟩ : Fin m)
    (by simp only [Fin.val_mk]; omega)).2.2 ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) (Or.inl (by simp))
  rw [hlam, permOf_LDRD_d hm]

/-- The head sends `(2,0)` to `(2,1)`. -/
theorem permOf_headWord_20 {m : ℕ} (hm : 1 < m) :
    permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) (headWord m)
        ((2 : Fin 3), (⟨0, by omega⟩ : Fin m))
      = ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) := by
  rw [permOf_headWord_eq hm]
  change permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) [Dir.L, Dir.D, Dir.R, Dir.D]
      (permOf ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) (List.replicate (m - 1) Dir.L)
        ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)))
    = ((2 : Fin 3), (⟨1, hm⟩ : Fin m))
  have hlam := (permOf_replicate_L (m - 1) (⟨0, by omega⟩ : Fin m)
    (by simp only [Fin.val_mk]; omega)).2.2 ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) (Or.inl (by simp))
  rw [hlam, permOf_LDRD_a hm]

/-- The head fixes `(2,c)` for `c ≥ 2`. -/
theorem permOf_headWord_2 {m : ℕ} (hm : 1 < m) {c : ℕ} (hc : c < m) (hc2 : 2 ≤ c) :
    permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) (headWord m)
        ((2 : Fin 3), (⟨c, hc⟩ : Fin m))
      = ((2 : Fin 3), (⟨c, hc⟩ : Fin m)) := by
  rw [permOf_headWord_eq hm]
  change permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) [Dir.L, Dir.D, Dir.R, Dir.D]
      (permOf ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) (List.replicate (m - 1) Dir.L)
        ((2 : Fin 3), (⟨c, hc⟩ : Fin m)))
    = ((2 : Fin 3), (⟨c, hc⟩ : Fin m))
  have hlam := (permOf_replicate_L (m - 1) (⟨0, by omega⟩ : Fin m)
    (by simp only [Fin.val_mk]; omega)).2.2 ((2 : Fin 3), (⟨c, hc⟩ : Fin m)) (Or.inl (by simp))
  rw [hlam, permOf_LDRD_fix_2 hm hc hc2]

/-! ### The tail `U U R D D L U R U` -/

theorem trace_tail_UU {m : ℕ} (hm : 1 < m) :
    trace ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) [Dir.U, Dir.U]
      = ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) := by
  have h1 : neighbor? ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.U
      = some ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) :=
    neighbor?_mk_U (x := (0 : Fin 3)) (y := (⟨1, hm⟩ : Fin m)) (by decide)
  have h2 : neighbor? ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.U
      = some ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) :=
    neighbor?_mk_U (x := (1 : Fin 3)) (y := (⟨1, hm⟩ : Fin m)) (by decide)
  rw [trace_cons_of_neighbor? h1, trace_cons_of_neighbor? h2, trace_nil]

theorem trace_tail_RDD {m : ℕ} (hm : 1 < m) :
    trace ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) [Dir.R, Dir.D, Dir.D]
      = ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) := by
  have h1 : neighbor? ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.R
      = some ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) := by
    simpa using (neighbor?_mk_R (x := (2 : Fin 3)) (y := (⟨1, hm⟩ : Fin m)) (by simp))
  have h2 : neighbor? ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) Dir.D
      = some ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) :=
    neighbor?_mk_D (x := (2 : Fin 3)) (y := (⟨0, by omega⟩ : Fin m)) (by decide)
  have h3 : neighbor? ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) Dir.D
      = some ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) :=
    neighbor?_mk_D (x := (1 : Fin 3)) (y := (⟨0, by omega⟩ : Fin m)) (by decide)
  rw [trace_cons_of_neighbor? h1, trace_cons_of_neighbor? h2, trace_cons_of_neighbor? h3,
      trace_nil]

theorem permOf_tailWord_eq {m : ℕ} (hm : 1 < m) :
    permOf ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) tailWord
      = permOf ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) [Dir.U, Dir.U]
        * permOf ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) [Dir.R, Dir.D, Dir.D]
        * permOf ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) [Dir.L, Dir.U, Dir.R, Dir.U] := by
  unfold tailWord
  rw [show [Dir.U, Dir.U, Dir.R, Dir.D, Dir.D, Dir.L, Dir.U, Dir.R, Dir.U]
        = ([Dir.U, Dir.U] ++ [Dir.R, Dir.D, Dir.D] ++ [Dir.L, Dir.U, Dir.R, Dir.U]) from rfl]
  rw [permOf_append, permOf_append, trace_append, trace_tail_UU hm, trace_tail_RDD hm]

theorem tail_UU_eq {m : ℕ} (hm : 1 < m) :
    permOf ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) [Dir.U, Dir.U]
      = Equiv.swap ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) ((1 : Fin 3), (⟨1, hm⟩ : Fin m))
        * Equiv.swap ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) := by
  have h1 : neighbor? ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.U
      = some ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) :=
    neighbor?_mk_U (x := (0 : Fin 3)) (y := (⟨1, hm⟩ : Fin m)) (by decide)
  have h2 : neighbor? ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.U
      = some ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) :=
    neighbor?_mk_U (x := (1 : Fin 3)) (y := (⟨1, hm⟩ : Fin m)) (by decide)
  rw [permOf_cons_of_neighbor? h1, permOf_cons_of_neighbor? h2, permOf_nil, mul_one]

theorem tail_RDD_eq {m : ℕ} (hm : 1 < m) :
    permOf ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) [Dir.R, Dir.D, Dir.D]
      = Equiv.swap ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) ((2 : Fin 3), (⟨0, by omega⟩ : Fin m))
        * Equiv.swap ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) ((1 : Fin 3), (⟨0, by omega⟩ : Fin m))
        * Equiv.swap ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) := by
  have h1 : neighbor? ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.R
      = some ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) := by
    simpa using (neighbor?_mk_R (x := (2 : Fin 3)) (y := (⟨1, hm⟩ : Fin m)) (by simp))
  have h2 : neighbor? ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) Dir.D
      = some ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) :=
    neighbor?_mk_D (x := (2 : Fin 3)) (y := (⟨0, by omega⟩ : Fin m)) (by decide)
  have h3 : neighbor? ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) Dir.D
      = some ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) :=
    neighbor?_mk_D (x := (1 : Fin 3)) (y := (⟨0, by omega⟩ : Fin m)) (by decide)
  rw [permOf_cons_of_neighbor? h1, permOf_cons_of_neighbor? h2, permOf_cons_of_neighbor? h3,
      permOf_nil, mul_one]
  group

theorem tail_LURU_eq {m : ℕ} (hm : 1 < m) :
    permOf ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) [Dir.L, Dir.U, Dir.R, Dir.U]
      = Equiv.swap ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) ((0 : Fin 3), (⟨1, hm⟩ : Fin m))
        * Equiv.swap ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) ((1 : Fin 3), (⟨1, hm⟩ : Fin m))
        * Equiv.swap ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) ((1 : Fin 3), (⟨0, by omega⟩ : Fin m))
        * Equiv.swap ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) := by
  have h1 : neighbor? ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) Dir.L
      = some ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) := by
    have h := neighbor?_mk_L (x := (0 : Fin 3)) (y := (⟨0, by omega⟩ : Fin m)) (by omega)
    rw [h]
  have h2 : neighbor? ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.U
      = some ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) :=
    neighbor?_mk_U (x := (0 : Fin 3)) (y := (⟨1, hm⟩ : Fin m)) (by decide)
  have h3 : neighbor? ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.R
      = some ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) := by
    simpa using (neighbor?_mk_R (x := (1 : Fin 3)) (y := (⟨1, hm⟩ : Fin m)) (by simp))
  have h4 : neighbor? ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) Dir.U
      = some ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) :=
    neighbor?_mk_U (x := (1 : Fin 3)) (y := (⟨0, by omega⟩ : Fin m)) (by decide)
  rw [permOf_cons_of_neighbor? h1, permOf_cons_of_neighbor? h2, permOf_cons_of_neighbor? h3,
      permOf_cons_of_neighbor? h4, permOf_nil, mul_one]
  group

theorem permOf_tailWord_eq' {m : ℕ} (hm : 1 < m) :
    permOf ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) tailWord
      = (Equiv.swap ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) ((1 : Fin 3), (⟨1, hm⟩ : Fin m))
          * Equiv.swap ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) ((2 : Fin 3), (⟨1, hm⟩ : Fin m)))
        * (Equiv.swap ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) ((2 : Fin 3), (⟨0, by omega⟩ : Fin m))
          * Equiv.swap ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) ((1 : Fin 3), (⟨0, by omega⟩ : Fin m))
          * Equiv.swap ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)))
        * (Equiv.swap ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) ((0 : Fin 3), (⟨1, hm⟩ : Fin m))
          * Equiv.swap ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) ((1 : Fin 3), (⟨1, hm⟩ : Fin m))
          * Equiv.swap ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) ((1 : Fin 3), (⟨0, by omega⟩ : Fin m))
          * Equiv.swap ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) ((2 : Fin 3), (⟨0, by omega⟩ : Fin m))) := by
  rw [permOf_tailWord_eq hm, tail_UU_eq hm, tail_RDD_eq hm, tail_LURU_eq hm]

theorem traceSet_tailWord_subset {m : ℕ} (hm : 1 < m) :
    ∀ y ∈ traceSet ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) tailWord, y.2.val ≤ 1 := by
  have h1 : neighbor? ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.U
      = some ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) :=
    neighbor?_mk_U (x := (0 : Fin 3)) (y := (⟨1, hm⟩ : Fin m)) (by decide)
  have h2 : neighbor? ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.U
      = some ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) :=
    neighbor?_mk_U (x := (1 : Fin 3)) (y := (⟨1, hm⟩ : Fin m)) (by decide)
  have h3 : neighbor? ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.R
      = some ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) := by
    simp
  have h4 : neighbor? ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) Dir.D
      = some ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) :=
    neighbor?_mk_D (x := (2 : Fin 3)) (y := (⟨0, by omega⟩ : Fin m)) (by decide)
  have h5 : neighbor? ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) Dir.D
      = some ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) :=
    neighbor?_mk_D (x := (1 : Fin 3)) (y := (⟨0, by omega⟩ : Fin m)) (by decide)
  have h6 : neighbor? ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) Dir.L
      = some ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) := by
    have h := neighbor?_mk_L (x := (0 : Fin 3)) (y := (⟨0, by omega⟩ : Fin m)) (by omega)
    rw [h]
  have h7 : neighbor? ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.U
      = some ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) := h1
  have h8 : neighbor? ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.R
      = some ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) := by
    simp
  have h9 : neighbor? ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) Dir.U
      = some ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) :=
    neighbor?_mk_U (x := (1 : Fin 3)) (y := (⟨0, by omega⟩ : Fin m)) (by decide)
  intro y hy
  unfold tailWord at hy
  rw [traceSet_cons_of_neighbor? h1, traceSet_cons_of_neighbor? h2,
      traceSet_cons_of_neighbor? h3, traceSet_cons_of_neighbor? h4,
      traceSet_cons_of_neighbor? h5, traceSet_cons_of_neighbor? h6,
      traceSet_cons_of_neighbor? h7, traceSet_cons_of_neighbor? h8,
      traceSet_cons_of_neighbor? h9, traceSet_nil] at hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals (simp only [Prod.snd, Fin.val_mk]; omega)

theorem tail_cells_ne {m : ℕ} (hm : 1 < m) :
    (((0 : Fin 3), (⟨1, hm⟩ : Fin m))) ≠ (((1 : Fin 3), (⟨1, hm⟩ : Fin m))) ∧
    (((0 : Fin 3), (⟨1, hm⟩ : Fin m))) ≠ (((2 : Fin 3), (⟨1, hm⟩ : Fin m))) ∧
    (((0 : Fin 3), (⟨1, hm⟩ : Fin m))) ≠ (((2 : Fin 3), (⟨0, by omega⟩ : Fin m))) ∧
    (((0 : Fin 3), (⟨1, hm⟩ : Fin m))) ≠ (((1 : Fin 3), (⟨0, by omega⟩ : Fin m))) ∧
    (((0 : Fin 3), (⟨1, hm⟩ : Fin m))) ≠ (((0 : Fin 3), (⟨0, by omega⟩ : Fin m))) ∧
    (((1 : Fin 3), (⟨1, hm⟩ : Fin m))) ≠ (((2 : Fin 3), (⟨1, hm⟩ : Fin m))) ∧
    (((1 : Fin 3), (⟨1, hm⟩ : Fin m))) ≠ (((2 : Fin 3), (⟨0, by omega⟩ : Fin m))) ∧
    (((1 : Fin 3), (⟨1, hm⟩ : Fin m))) ≠ (((1 : Fin 3), (⟨0, by omega⟩ : Fin m))) ∧
    (((1 : Fin 3), (⟨1, hm⟩ : Fin m))) ≠ (((0 : Fin 3), (⟨0, by omega⟩ : Fin m))) ∧
    (((2 : Fin 3), (⟨1, hm⟩ : Fin m))) ≠ (((2 : Fin 3), (⟨0, by omega⟩ : Fin m))) ∧
    (((2 : Fin 3), (⟨1, hm⟩ : Fin m))) ≠ (((1 : Fin 3), (⟨0, by omega⟩ : Fin m))) ∧
    (((2 : Fin 3), (⟨1, hm⟩ : Fin m))) ≠ (((0 : Fin 3), (⟨0, by omega⟩ : Fin m))) ∧
    (((2 : Fin 3), (⟨0, by omega⟩ : Fin m))) ≠ (((1 : Fin 3), (⟨0, by omega⟩ : Fin m))) ∧
    (((2 : Fin 3), (⟨0, by omega⟩ : Fin m))) ≠ (((0 : Fin 3), (⟨0, by omega⟩ : Fin m))) ∧
    (((1 : Fin 3), (⟨0, by omega⟩ : Fin m))) ≠ (((0 : Fin 3), (⟨0, by omega⟩ : Fin m))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h
     have := congrArg (fun x : Cell 3 m => (x.1.val, x.2.val)) h
     simp only [Prod.fst, Prod.snd, Fin.val_mk, Prod.mk.injEq] at this
     omega)

theorem tail_1_0 {m : ℕ} (hm : 1 < m) :
    permOf ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) tailWord ((1 : Fin 3), (⟨0, by omega⟩ : Fin m))
      = ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) := by
  obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf, hcd, hce, hcf, hde, hdf, hef⟩ := tail_cells_ne hm
  rw [permOf_tailWord_eq' hm]
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  grind

theorem tail_1_1 {m : ℕ} (hm : 1 < m) :
    permOf ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) tailWord ((1 : Fin 3), (⟨1, hm⟩ : Fin m))
      = ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) := by
  obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf, hcd, hce, hcf, hde, hdf, hef⟩ := tail_cells_ne hm
  rw [permOf_tailWord_eq' hm]
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  grind

theorem tail_1_c {m : ℕ} (hm : 1 < m) {c : ℕ} (hc : c < m) (hc2 : 2 ≤ c) :
    permOf ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) tailWord ((1 : Fin 3), (⟨c, hc⟩ : Fin m))
      = ((1 : Fin 3), (⟨c, hc⟩ : Fin m)) := by
  apply permOf_apply_of_not_mem_traceSet
  intro hmem
  have h := traceSet_tailWord_subset hm _ hmem
  simp only [Prod.snd, Fin.val_mk] at h
  omega

theorem tail_2_0 {m : ℕ} (hm : 1 < m) :
    permOf ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) tailWord ((2 : Fin 3), (⟨0, by omega⟩ : Fin m))
      = ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) := by
  obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf, hcd, hce, hcf, hde, hdf, hef⟩ := tail_cells_ne hm
  rw [permOf_tailWord_eq' hm]
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  grind

theorem tail_2_1 {m : ℕ} (hm : 1 < m) :
    permOf ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) tailWord ((2 : Fin 3), (⟨1, hm⟩ : Fin m))
      = ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) := by
  obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf, hcd, hce, hcf, hde, hdf, hef⟩ := tail_cells_ne hm
  rw [permOf_tailWord_eq' hm]
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  grind

theorem tail_2_c {m : ℕ} (hm : 1 < m) {c : ℕ} (hc : c < m) (hc2 : 2 ≤ c) :
    permOf ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) tailWord ((2 : Fin 3), (⟨c, hc⟩ : Fin m))
      = ((2 : Fin 3), (⟨c, hc⟩ : Fin m)) := by
  apply permOf_apply_of_not_mem_traceSet
  intro hmem
  have h := traceSet_tailWord_subset hm _ hmem
  simp only [Prod.snd, Fin.val_mk] at h
  omega

/-- The shift word sends the first row to the second row. -/
theorem permOf_shiftWord_row1 {m : ℕ} (hm : 1 < m) (c : Fin m) :
    permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) (shiftWord m) ((1 : Fin 3), c)
      = ((0 : Fin 3), c) := by
  have hsm : m - 1 < m := by omega
  have htrace2 : trace ((0 : Fin 3), (⟨m - 1, hsm⟩ : Fin m)) (sweepWord (m - 2))
      = ((0 : Fin 3), (⟨1, by omega⟩ : Fin m)) := by
    rw [trace_sweepWord (m - 2) (m - 1) (by omega) hsm]
    congr 1
    apply Fin.ext
    simp only [Fin.val_mk]
    omega
  rw [shiftWord, List.append_assoc, permOf_append, trace_headWord hm, permOf_append, htrace2]
  change permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) (headWord m)
      (permOf ((0 : Fin 3), (⟨m - 1, hsm⟩ : Fin m)) (sweepWord (m - 2))
        (permOf ((0 : Fin 3), (⟨1, by omega⟩ : Fin m)) tailWord ((1 : Fin 3), c)))
    = ((0 : Fin 3), c)
  rw [permOf_sweepWord (m - 2) (m - 1) (by omega) hsm,
      show (m - 1) - (m - 2) = 1 from by omega]
  by_cases hc0 : c.val = 0
  · have hc : c = (⟨0, by omega⟩ : Fin m) := Fin.ext (by rw [hc0])
    rw [hc, tail_1_0 hm]
    rw [show sweepFun m 1 (m - 1) hsm ((1 : Fin 3), (⟨0, by omega⟩ : Fin m))
          = ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) from
          sweepFun_of_lt (lo := 1) (hi := m - 1) (hhi := hsm) (r := (1 : Fin 3))
            (c := (⟨0, by omega⟩ : Fin m)) (by simp),
        permOf_headWord_10 hm]
  · by_cases hc1 : c.val = 1
    · have hc : c = (⟨1, hm⟩ : Fin m) := Fin.ext (by rw [hc1])
      rw [hc, tail_1_1 hm]
      rw [show sweepFun m 1 (m - 1) hsm ((0 : Fin 3), (⟨0, by omega⟩ : Fin m))
            = ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) from
            sweepFun_of_lt (lo := 1) (hi := m - 1) (hhi := hsm) (r := (0 : Fin 3))
              (c := (⟨0, by omega⟩ : Fin m)) (by simp)]
      have hhead := permOf_headWord_0 hm 0 (by omega)
      rw [show ((0 : Fin 3), (⟨(0 : ℕ) + 1, by omega⟩ : Fin m)) = ((0 : Fin 3), (⟨1, hm⟩ : Fin m))
            from Prod.ext rfl (Fin.ext (by simp))] at hhead
      rw [hhead]
    · have hc2 : 2 ≤ c.val := by omega
      rw [tail_1_c hm c.isLt hc2]
      rw [show sweepFun m 1 (m - 1) hsm ((1 : Fin 3), c)
            = ((0 : Fin 3), (⟨c.val - 1, by omega⟩ : Fin m)) from
            sweepFun_row1_gt (lo := 1) (hi := m - 1) (hhi := hsm) (c := c)
              (by omega) (by omega)]
      have hhead := permOf_headWord_0 hm (c.val - 1) (by omega)
      rw [show ((0 : Fin 3), (⟨(c.val - 1) + 1, by omega⟩ : Fin m)) = ((0 : Fin 3), c)
            from Prod.ext rfl (Fin.ext (by simp only [Fin.val_mk]; omega))] at hhead
      rw [hhead]

/-- The shift word fixes the third row. -/
theorem permOf_shiftWord_row2 {m : ℕ} (hm : 1 < m) (c : Fin m) :
    permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) (shiftWord m) ((2 : Fin 3), c)
      = ((2 : Fin 3), c) := by
  have hsm : m - 1 < m := by omega
  have htrace2 : trace ((0 : Fin 3), (⟨m - 1, hsm⟩ : Fin m)) (sweepWord (m - 2))
      = ((0 : Fin 3), (⟨1, by omega⟩ : Fin m)) := by
    rw [trace_sweepWord (m - 2) (m - 1) (by omega) hsm]
    congr 1
    apply Fin.ext
    simp only [Fin.val_mk]
    omega
  rw [shiftWord, List.append_assoc, permOf_append, trace_headWord hm, permOf_append, htrace2]
  change permOf ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) (headWord m)
      (permOf ((0 : Fin 3), (⟨m - 1, hsm⟩ : Fin m)) (sweepWord (m - 2))
        (permOf ((0 : Fin 3), (⟨1, by omega⟩ : Fin m)) tailWord ((2 : Fin 3), c)))
    = ((2 : Fin 3), c)
  rw [permOf_sweepWord (m - 2) (m - 1) (by omega) hsm,
      show (m - 1) - (m - 2) = 1 from by omega]
  by_cases hc0 : c.val = 0
  · have hc : c = (⟨0, by omega⟩ : Fin m) := Fin.ext (by rw [hc0])
    rw [hc, tail_2_0 hm]
    rw [show sweepFun m 1 (m - 1) hsm ((0 : Fin 3), (⟨1, by omega⟩ : Fin m))
          = ((0 : Fin 3), (⟨m - 1, hsm⟩ : Fin m)) from
          sweepFun_row0_eq (lo := 1) (hi := m - 1) (hhi := hsm) (hle := by omega)
            (c := (⟨1, by omega⟩ : Fin m)) (by rfl)]
    have hhead := permOf_headWord_0_last hm
    rw [show ((0 : Fin 3), (⟨m - 1, by omega⟩ : Fin m)) = ((0 : Fin 3), (⟨m - 1, hsm⟩ : Fin m))
          from Prod.ext rfl (Fin.ext rfl)] at hhead
    rw [hhead]
  · by_cases hc1 : c.val = 1
    · have hc : c = (⟨1, hm⟩ : Fin m) := Fin.ext (by rw [hc1])
      rw [hc, tail_2_1 hm]
      rw [show sweepFun m 1 (m - 1) hsm ((2 : Fin 3), (⟨0, by omega⟩ : Fin m))
            = ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) from
            sweepFun_row2 1 (m - 1) hsm (⟨0, by omega⟩ : Fin m),
          permOf_headWord_20 hm]
    · have hc2 : 2 ≤ c.val := by omega
      rw [tail_2_c hm c.isLt hc2]
      rw [show sweepFun m 1 (m - 1) hsm ((2 : Fin 3), c) = ((2 : Fin 3), c) from
            sweepFun_row2 1 (m - 1) hsm c,
          permOf_headWord_2 hm c.isLt hc2]

/-- The sweep word `(R U L D R)^k` has length `5k`. -/
theorem sweepWord_length (k : ℕ) : (sweepWord k).length = 5 * k := by
  induction k with
  | zero => simp
  | succ k ih => rw [sweepWord_succ, List.length_append, ih]; simp [sweepBlock]; omega

/-- The shift word has length `6m + 2`. -/
theorem shiftWord_length {m : ℕ} (hm : 1 < m) :
    (shiftWord m).length = 6 * m + 2 := by
  have h1 : (headWord m).length = m + 3 := by
    unfold headWord
    rw [List.length_append, List.length_replicate]
    simp
    omega
  have h2 : (sweepWord (m - 2)).length = 5 * (m - 2) := sweepWord_length (m - 2)
  have h3 : tailWord.length = 9 := rfl
  unfold shiftWord
  rw [List.length_append, List.length_append, h1, h2, h3]
  omega

/-! ### Applicability of the shift word

The explicit words of Lemma 1 are built from moves that never leave the `3 × m` strip.
This section records that fact, which is what lets the lifting in `Algorithm/Lift.lean`
transport the effect to a strip of a larger board. -/

/-- The head `L D R D` is applicable from `(2,0)`. -/
theorem applicableFrom_LDRD {m : ℕ} (hm : 1 < m) :
    ApplicableFrom ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) [Dir.L, Dir.D, Dir.R, Dir.D] := by
  have hL : neighbor? ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) Dir.L
      = some ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) := by
    have hlt : (0 : ℕ) + 1 < m := by omega
    have h := neighbor?_mk_L (x := (2 : Fin 3)) (y := (⟨0, by omega⟩ : Fin m)) hlt
    rw [h]
  have hD1 : neighbor? ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.D
      = some ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) :=
    neighbor?_mk_D (x := (2 : Fin 3)) (y := (⟨1, hm⟩ : Fin m)) (by decide)
  have hR : neighbor? ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.R
      = some ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) := by
    simp
  have hD2 : neighbor? ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) Dir.D
      = some ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) :=
    neighbor?_mk_D (x := (1 : Fin 3)) (y := (⟨0, by omega⟩ : Fin m)) (by decide)
  rw [applicableFrom_cons_of_neighbor? hL, applicableFrom_cons_of_neighbor? hD1,
      applicableFrom_cons_of_neighbor? hR, applicableFrom_cons_of_neighbor? hD2]
  exact trivial

/-- The head `L D R D L^{m-1}` is applicable from `(2,0)`. -/
theorem applicableFrom_headWord {m : ℕ} (hm : 1 < m) :
    ApplicableFrom ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) (headWord m) := by
  unfold headWord
  rw [applicableFrom_append]
  refine ⟨applicableFrom_LDRD hm, ?_⟩
  rw [trace_LDRD hm]
  exact applicableFrom_replicate_left (n := 3) (m := m) 0 (m - 1) 0 (by omega) (by decide)

/-- A single sweep block is applicable from `(0,j)` for `0 < j`. -/
theorem applicableFrom_sweepBlock {m : ℕ} (j : Fin m) (hj : 0 < j.val) :
    ApplicableFrom ((0 : Fin 3), j) sweepBlock := by
  have hR : neighbor? ((0 : Fin 3), j) Dir.R
      = some ((0 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩) := neighbor?_mk_R hj
  have hU : neighbor? ((0 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩) Dir.U
      = some ((1 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩) := by
    simp
  have hL : neighbor? ((1 : Fin 3), ⟨j.val - 1, fin_pred_lt hj j.isLt⟩) Dir.L
      = some ((1 : Fin 3), j) := by
    have hlt : (⟨j.val - 1, fin_pred_lt hj j.isLt⟩ : Fin m).val + 1 < m := by
      simp only [Fin.val_mk]; omega
    have hfin : (⟨(⟨j.val - 1, fin_pred_lt hj j.isLt⟩ : Fin m).val + 1, hlt⟩ : Fin m) = j := by
      apply Fin.ext
      change (⟨j.val - 1, fin_pred_lt hj j.isLt⟩ : Fin m).val + 1 = j.val
      have hc : (⟨j.val - 1, fin_pred_lt hj j.isLt⟩ : Fin m).val = j.val - 1 := rfl
      omega
    rw [neighbor?_mk_L hlt, hfin]
  have hD : neighbor? ((1 : Fin 3), j) Dir.D
      = some ((0 : Fin 3), j) := by
    simp
  unfold sweepBlock
  rw [applicableFrom_cons_of_neighbor? hR, applicableFrom_cons_of_neighbor? hU,
      applicableFrom_cons_of_neighbor? hL, applicableFrom_cons_of_neighbor? hD,
      applicableFrom_cons_of_neighbor? hR]
  exact trivial

/-- The sweep `(R U L D R)^k` is applicable from `(0,start)`. -/
theorem applicableFrom_sweepWord {m : ℕ} (k : ℕ) :
    ∀ (start : ℕ) (_hk : k ≤ start) (hstart : start < m),
      ApplicableFrom ((0 : Fin 3), (⟨start, hstart⟩ : Fin m)) (sweepWord k) := by
  induction k with
  | zero =>
      intro start _ _
      rw [sweepWord_zero]
      exact trivial
  | succ k ih =>
      intro start _hk hstart
      rw [sweepWord_succ, applicableFrom_append, trace_sweepWord k start (by omega) hstart]
      refine ⟨ih start (by omega) hstart, ?_⟩
      exact applicableFrom_sweepBlock (⟨start - k, by omega⟩ : Fin m)
        (by change 0 < start - k; omega)

/-- The tail `U U R D D L U R U` is applicable from `(0,1)`. -/
theorem applicableFrom_tailWord {m : ℕ} (hm : 1 < m) :
    ApplicableFrom ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) tailWord := by
  have h1 : neighbor? ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.U
      = some ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) :=
    neighbor?_mk_U (x := (0 : Fin 3)) (y := (⟨1, hm⟩ : Fin m)) (by decide)
  have h2 : neighbor? ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.U
      = some ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) :=
    neighbor?_mk_U (x := (1 : Fin 3)) (y := (⟨1, hm⟩ : Fin m)) (by decide)
  have h3 : neighbor? ((2 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.R
      = some ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) := by
    simp
  have h4 : neighbor? ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) Dir.D
      = some ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) :=
    neighbor?_mk_D (x := (2 : Fin 3)) (y := (⟨0, by omega⟩ : Fin m)) (by decide)
  have h5 : neighbor? ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) Dir.D
      = some ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) :=
    neighbor?_mk_D (x := (1 : Fin 3)) (y := (⟨0, by omega⟩ : Fin m)) (by decide)
  have h6 : neighbor? ((0 : Fin 3), (⟨0, by omega⟩ : Fin m)) Dir.L
      = some ((0 : Fin 3), (⟨1, hm⟩ : Fin m)) := by
    have h := neighbor?_mk_L (x := (0 : Fin 3)) (y := (⟨0, by omega⟩ : Fin m)) (by omega)
    rw [h]
  have h8 : neighbor? ((1 : Fin 3), (⟨1, hm⟩ : Fin m)) Dir.R
      = some ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) := by
    simp
  have h9 : neighbor? ((1 : Fin 3), (⟨0, by omega⟩ : Fin m)) Dir.U
      = some ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) :=
    neighbor?_mk_U (x := (1 : Fin 3)) (y := (⟨0, by omega⟩ : Fin m)) (by decide)
  unfold tailWord
  rw [applicableFrom_cons_of_neighbor? h1, applicableFrom_cons_of_neighbor? h2,
      applicableFrom_cons_of_neighbor? h3, applicableFrom_cons_of_neighbor? h4,
      applicableFrom_cons_of_neighbor? h5, applicableFrom_cons_of_neighbor? h6,
      applicableFrom_cons_of_neighbor? h1, applicableFrom_cons_of_neighbor? h8,
      applicableFrom_cons_of_neighbor? h9]
  exact trivial

/-- **Lemma 1 (Zhong 2023), applicability.**  The shift word `θ_m` is applicable from the
blank position `(2,0)` of a `3 × m` board. -/
theorem applicableFrom_shiftWord {m : ℕ} (hm : 1 < m) :
    ApplicableFrom ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) (shiftWord m) := by
  have hsm : m - 1 < m := by omega
  have htrace2 : trace ((0 : Fin 3), (⟨m - 1, hsm⟩ : Fin m)) (sweepWord (m - 2))
      = ((0 : Fin 3), (⟨1, by omega⟩ : Fin m)) := by
    rw [trace_sweepWord (m - 2) (m - 1) (by omega) hsm]
    congr 1
    apply Fin.ext
    simp only [Fin.val_mk]
    omega
  unfold shiftWord
  rw [List.append_assoc, applicableFrom_append, trace_headWord hm]
  refine ⟨applicableFrom_headWord hm, ?_⟩
  rw [applicableFrom_append]
  refine ⟨applicableFrom_sweepWord (m - 2) (m - 1) (by omega) hsm, ?_⟩
  rw [htrace2]
  simpa using applicableFrom_tailWord hm

end Zhong
