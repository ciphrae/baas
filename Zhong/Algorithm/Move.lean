/-
Copyright (c) 2026 The Zhong formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhong formalisation contributors
-/
import Zhong.ClosedWalk

/-!
# The `move-x` and `move-y` primitives

Zhong (2023) uses two elementary operations throughout the algorithm:

* `move-x(x)`: move the blank to row `x`;
* `move-y(y)`: move the blank to column `y`.

These are the operation sequences `moveXWord` and `moveYWord` below, built from
`List.replicate` of a single direction.  We prove that they move the blank as expected, that
they are applicable, and that their length is the distance travelled.
-/

namespace Zhong

open Equiv

variable {n m : ℕ}

/-- Move the blank down (`D`) by `i` rows. -/
theorem trace_replicate_down (r i c : ℕ) (hir : i ≤ r) (hr : r < n) (hc : c < m) :
    trace (((⟨r, hr⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m) (List.replicate i Dir.D)
      = (((⟨r - i, by omega⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m) := by
  induction i generalizing r with
  | zero => simp
  | succ i ih =>
      have hr0 : 0 < r := by omega
      have hstep : neighbor? (((⟨r, hr⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m) Dir.D
          = some (((⟨r - 1, by omega⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m) := by
        simp only [neighbor?]; rw [if_pos hr0]
      rw [List.replicate_succ, trace_cons_of_neighbor? hstep, ih (r := r - 1) (by omega) (by omega)]
      ext <;> simp <;> omega

/-- Move the blank right (`L`) by `i` columns. -/
theorem trace_replicate_left (r i c : ℕ) (hci : c + i < m) (hr : r < n) :
    trace (((⟨r, hr⟩ : Fin n), (⟨c, by omega⟩ : Fin m)) : Cell n m) (List.replicate i Dir.L)
      = (((⟨r, hr⟩ : Fin n), (⟨c + i, by omega⟩ : Fin m)) : Cell n m) := by
  induction i generalizing c with
  | zero => simp
  | succ i ih =>
      have hc1 : c + 1 < m := by omega
      have hstep : neighbor? (((⟨r, hr⟩ : Fin n), (⟨c, by omega⟩ : Fin m)) : Cell n m) Dir.L
          = some (((⟨r, hr⟩ : Fin n), (⟨c + 1, hc1⟩ : Fin m)) : Cell n m) := by
        simp only [neighbor?]; rw [dif_pos (by simpa using hc1)]
      rw [List.replicate_succ, trace_cons_of_neighbor? hstep, ih (c := c + 1) (by omega)]
      ext <;> simp <;> omega

/-- Move the blank left (`R`) by `i` columns. -/
theorem trace_replicate_right (r i c : ℕ) (hic : i ≤ c) (hr : r < n) (hc : c < m) :
    trace (((⟨r, hr⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m) (List.replicate i Dir.R)
      = (((⟨r, hr⟩ : Fin n), (⟨c - i, by omega⟩ : Fin m)) : Cell n m) := by
  induction i generalizing c with
  | zero => simp
  | succ i ih =>
      have hc0 : 0 < c := by omega
      have hstep : neighbor? (((⟨r, hr⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m) Dir.R
          = some (((⟨r, hr⟩ : Fin n), (⟨c - 1, by omega⟩ : Fin m)) : Cell n m) := by
        simp only [neighbor?]; rw [if_pos hc0]
      rw [List.replicate_succ, trace_cons_of_neighbor? hstep, ih (c := c - 1) (by omega) (by omega)]
      ext <;> simp <;> omega

theorem applicableFrom_replicate_down (r i c : ℕ) (hir : i ≤ r) (hr : r < n) (hc : c < m) :
    ApplicableFrom (((⟨r, hr⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m)
      (List.replicate i Dir.D) := by
  induction i generalizing r with
  | zero => simp
  | succ i ih =>
      refine ⟨(((⟨r - 1, by omega⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m), ?_, ?_⟩
      · simp only [neighbor?]; rw [if_pos (by omega : 0 < r)]
      · exact ih (r - 1) (by omega) (by omega)

theorem applicableFrom_replicate_left (r i c : ℕ) (hci : c + i < m) (hr : r < n) :
    ApplicableFrom (((⟨r, hr⟩ : Fin n), (⟨c, by omega⟩ : Fin m)) : Cell n m)
      (List.replicate i Dir.L) := by
  induction i generalizing c with
  | zero => simp
  | succ i ih =>
      refine ⟨(((⟨r, hr⟩ : Fin n), (⟨c + 1, by omega⟩ : Fin m)) : Cell n m), ?_, ?_⟩
      · simp only [neighbor?]; rw [dif_pos (by omega : c + 1 < m)]
      · exact ih (c + 1) (by omega)

theorem applicableFrom_replicate_right (r i c : ℕ) (hic : i ≤ c) (hr : r < n) (hc : c < m) :
    ApplicableFrom (((⟨r, hr⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m)
      (List.replicate i Dir.R) := by
  induction i generalizing c with
  | zero => simp
  | succ i ih =>
      refine ⟨(((⟨r, hr⟩ : Fin n), (⟨c - 1, by omega⟩ : Fin m)) : Cell n m), ?_, ?_⟩
      · simp only [neighbor?]; rw [if_pos (by omega : 0 < c)]
      · exact ih (c - 1) (by omega) (by omega)

/-- The operation sequence moving the blank from row `x0` to row `x`. -/
def moveXWord (x0 x : ℕ) : List Dir :=
  if x < x0 then List.replicate (x0 - x) Dir.D else List.replicate (x - x0) Dir.U

/-- The operation sequence moving the blank from column `y0` to column `y`. -/
def moveYWord (y0 y : ℕ) : List Dir :=
  if y < y0 then List.replicate (y0 - y) Dir.R else List.replicate (y - y0) Dir.L

@[simp] theorem moveXWord_of_lt {x0 x : ℕ} (h : x < x0) :
    moveXWord x0 x = List.replicate (x0 - x) Dir.D := if_pos h

@[simp] theorem moveXWord_of_le {x0 x : ℕ} (h : ¬ x < x0) :
    moveXWord x0 x = List.replicate (x - x0) Dir.U := if_neg h

@[simp] theorem moveYWord_of_lt {y0 y : ℕ} (h : y < y0) :
    moveYWord y0 y = List.replicate (y0 - y) Dir.R := if_pos h

@[simp] theorem moveYWord_of_le {y0 y : ℕ} (h : ¬ y < y0) :
    moveYWord y0 y = List.replicate (y - y0) Dir.L := if_neg h

/-- `moveXWord` moves the blank to the requested row. -/
theorem trace_moveXWord (r c x : ℕ) (hx : x < n) (hr : r < n) (hc : c < m) :
    trace (((⟨r, hr⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m) (moveXWord r x)
      = (((⟨x, hx⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m) := by
  unfold moveXWord
  by_cases h : x < r
  · rw [if_pos h, trace_replicate_down r (r - x) c (by omega) hr hc]
    ext <;> simp <;> omega
  · rw [if_neg h, trace_replicate_U r (x - r) c (by omega) hc]
    ext <;> simp <;> omega

/-- `moveYWord` moves the blank to the requested column. -/
theorem trace_moveYWord (r c y : ℕ) (hr : r < n) (hc : c < m) (hy : y < m) :
    trace (((⟨r, hr⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m) (moveYWord c y)
      = (((⟨r, hr⟩ : Fin n), (⟨y, hy⟩ : Fin m)) : Cell n m) := by
  unfold moveYWord
  by_cases h : y < c
  · rw [if_pos h, trace_replicate_right r (c - y) c (by omega) hr hc]
    ext <;> simp <;> omega
  · rw [if_neg h, trace_replicate_left r (y - c) c (by omega) hr]
    ext <;> simp <;> omega

theorem applicableFrom_moveXWord (r c x : ℕ) (hx : x < n) (hr : r < n) (hc : c < m) :
    ApplicableFrom (((⟨r, hr⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m) (moveXWord r x) := by
  unfold moveXWord
  by_cases h : x < r
  · rw [if_pos h]
    exact applicableFrom_replicate_down r (r - x) c (by omega) hr hc
  · rw [if_neg h]
    exact applicableFrom_replicate_U r (x - r) c (by omega) hc

theorem applicableFrom_moveYWord (r c y : ℕ) (hy : y < m) (hr : r < n) (hc : c < m) :
    ApplicableFrom (((⟨r, hr⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m) (moveYWord c y) := by
  unfold moveYWord
  by_cases h : y < c
  · rw [if_pos h]
    exact applicableFrom_replicate_right r (c - y) c (by omega) hr hc
  · rw [if_neg h]
    exact applicableFrom_replicate_left r (y - c) c (by omega) hr

theorem length_moveXWord (x0 x : ℕ) : (moveXWord x0 x).length = Nat.dist x0 x := by
  show (moveXWord x0 x).length = (x0 - x) + (x - x0)
  unfold moveXWord
  by_cases h : x < x0
  · rw [if_pos h, List.length_replicate]; omega
  · rw [if_neg h, List.length_replicate]; omega

theorem length_moveYWord (y0 y : ℕ) : (moveYWord y0 y).length = Nat.dist y0 y := by
  show (moveYWord y0 y).length = (y0 - y) + (y - y0)
  unfold moveYWord
  by_cases h : y < y0
  · rw [if_pos h, List.length_replicate]; omega
  · rw [if_neg h, List.length_replicate]; omega

end Zhong
