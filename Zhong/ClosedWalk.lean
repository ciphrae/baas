import Zhong.Orbit
import Zhong.Group
/-
Copyright (c) 2026 The Zhong formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhong formalisation contributors
-/

/-!
# Closed walks and the parity of the induced cell permutation

This file starts the group-theoretic part of the converse of Proposition 3 of
Zhong (2023).  A *closed walk* at a cell `p` is an operation sequence whose trace
returns the blank to `p`.  The set `H p` of cell permutations induced by closed
walks at `p` is the subgroup of the puzzle group that fixes `p`.

The first result is that the sign of the cell permutation induced by an arbitrary
operation sequence is the product of the parities of the starting and ending cells
of the blank (`sign_permOf`).  Consequently every closed walk induces an even
permutation, so `H p ≤ alternatingGroup`.
-/

namespace Zhong

open Equiv

variable {n m : ℕ}

/-- The sign of the cell permutation induced by `σ` is the parity of the trace of
the blank: `sign (permOf p σ) = cellParity p * cellParity (trace p σ)`. -/
theorem sign_permOf (p : Cell n m) (σ : List Dir) :
    Equiv.Perm.sign (permOf p σ) = cellParity p * cellParity (trace p σ) := by
  induction σ generalizing p with
  | nil => rw [trace_nil, permOf_nil, map_one]; exact (cellParity_sq p).symm
  | cons δ σ ih =>
      cases h : neighbor? p δ with
      | none =>
          rw [permOf_cons_of_neighbor?_eq_none h, trace_cons_of_neighbor?_eq_none h]
          exact ih p
      | some c' =>
          have hneg : (-1 : ℤˣ) = cellParity p * cellParity c' := by
            rw [cellParity_neighbor h, ← mul_assoc, cellParity_sq, one_mul]
          rw [permOf_cons_of_neighbor? h, trace_cons_of_neighbor? h, map_mul,
              Equiv.Perm.sign_swap (neighbor?_ne h).symm, ih c', hneg]
          rw [mul_assoc, ← mul_assoc (cellParity c') (cellParity c') (cellParity (trace c' σ)),
              cellParity_sq, one_mul]

/-- A closed walk at `p`. -/
def IsClosedWalk (p : Cell n m) (σ : List Dir) : Prop := trace p σ = p

/-- The subgroup of cell permutations induced by closed walks at `p`. -/
noncomputable def closedGroup (p : Cell n m) : Subgroup (Equiv.Perm (Cell n m)) :=
  Subgroup.closure {g : Equiv.Perm (Cell n m) | ∃ σ : List Dir, IsClosedWalk p σ ∧ permOf p σ = g}

theorem mem_closedGroup {p : Cell n m} {σ : List Dir} (h : IsClosedWalk p σ) :
    permOf p σ ∈ closedGroup p :=
  Subgroup.subset_closure ⟨σ, h, rfl⟩

/-- The product of four transpositions around a square equals the product of two of
them: `(a b)(b c)(c d)(d a) = (b c)(c d)` for four distinct points. -/
theorem swap_mul_swap_mul_swap_mul_swap {α : Type*} [DecidableEq α] {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Equiv.swap a b * Equiv.swap b c * Equiv.swap c d * Equiv.swap d a
      = Equiv.swap b c * Equiv.swap c d := by
  ext x
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  grind

/-! ### The basic `2 × 2` loop

Acting the four moves `L U R D` with the blank at the top-left corner of a `2 × 2`
block returns the blank and cycles the other three cells. -/

@[simp] theorem neighbor?_mk_L {x : Fin n} {y : Fin m} (h : y.1 + 1 < m) :
    neighbor? (x, y) Dir.L = some (x, ⟨y.1 + 1, h⟩) := by
  simp only [neighbor?]; rw [dif_pos h]

@[simp] theorem neighbor?_mk_U {x : Fin n} {y : Fin m} (h : x.1 + 1 < n) :
    neighbor? (x, y) Dir.U = some (⟨x.1 + 1, h⟩, y) := by
  simp only [neighbor?]; rw [dif_pos h]

@[simp] theorem neighbor?_mk_R {x : Fin n} {y : Fin m} (h : 0 < y.1) :
    neighbor? (x, y) Dir.R
      = some (x, ⟨y.1 - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) y.2⟩) := by
  simp only [neighbor?]; rw [if_pos h]

@[simp] theorem neighbor?_mk_D {x : Fin n} {y : Fin m} (h : 0 < x.1) :
    neighbor? (x, y) Dir.D
      = some (⟨x.1 - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.2⟩, y) := by
  simp only [neighbor?]; rw [if_pos h]

/-- The explicit form of the `2 × 2` loop permutation: the three-cycle on the other three
cells of the square. -/
theorem permOf_loop_at_eq (i : Fin n) (j : Fin m) (hi : i.1 + 1 < n) (hj : j.1 + 1 < m) :
    permOf (i, j) [Dir.L, Dir.U, Dir.R, Dir.D]
      = Equiv.swap (i, ⟨j.1 + 1, hj⟩) (⟨i.1 + 1, hi⟩, ⟨j.1 + 1, hj⟩)
        * Equiv.swap (⟨i.1 + 1, hi⟩, ⟨j.1 + 1, hj⟩) (⟨i.1 + 1, hi⟩, j) := by
  let c00 : Cell n m := (i, j)
  have hp1 : c00.2.1 + 1 < m := by simpa [c00] using hj
  let c01 : Cell n m := (c00.1, ⟨c00.2.1 + 1, hp1⟩)
  have hp2 : c01.1.1 + 1 < n := by simpa [c01, c00] using hi
  let c11 : Cell n m := (⟨c01.1.1 + 1, hp2⟩, c01.2)
  have hp3 : 0 < c11.2.1 := by simp [c11, c01, c00]
  let c10 : Cell n m := (c11.1, ⟨c11.2.1 - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) c11.2.2⟩)
  have hp4 : 0 < c10.1.1 := by simp [c10, c11, c01, c00]
  let c00' : Cell n m := (⟨c10.1.1 - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) c10.1.2⟩, c10.2)
  have h1 : neighbor? c00 Dir.L = some c01 := by
    simp only [neighbor?]; rw [dif_pos hp1]
  have h2 : neighbor? c01 Dir.U = some c11 := by
    simp only [neighbor?]; rw [dif_pos hp2]
  have h3 : neighbor? c11 Dir.R = some c10 := by
    simp only [neighbor?]; rw [if_pos hp3]
  have h4 : neighbor? c10 Dir.D = some c00' := by
    simp only [neighbor?]; rw [if_pos hp4]
  have hc00' : c00' = c00 := by
    ext <;> simp [c00', c10, c11, c01, c00]
  have hne0001 : c00 ≠ c01 := by
    intro hh; have := congrArg (fun x : Cell n m => x.2.1) hh; dsimp only [c00, c01] at this; omega
  have hne0011 : c00 ≠ c11 := by
    intro hh; have := congrArg (fun x : Cell n m => x.1.1) hh; dsimp only [c00, c11, c01] at this; omega
  have hne0010 : c00 ≠ c10 := by
    intro hh; have := congrArg (fun x : Cell n m => x.1.1) hh; dsimp only [c00, c10, c11, c01] at this; omega
  have hne0111 : c01 ≠ c11 := by
    intro hh; have := congrArg (fun x : Cell n m => x.1.1) hh; dsimp only [c01, c11, c00] at this; omega
  have hne0110 : c01 ≠ c10 := by
    intro hh; have := congrArg (fun x : Cell n m => x.2.1) hh; dsimp only [c01, c10, c11, c00] at this; omega
  have hne1110 : c11 ≠ c10 := by
    intro hh; have := congrArg (fun x : Cell n m => x.2.1) hh; dsimp only [c11, c10, c01, c00] at this; omega
  have e01 : c01 = (i, ⟨j.1 + 1, hj⟩) := by ext <;> simp [c01, c00]
  have e11 : c11 = (⟨i.1 + 1, hi⟩, ⟨j.1 + 1, hj⟩) := by ext <;> simp [c11, c01, c00]
  have e10 : c10 = (⟨i.1 + 1, hi⟩, j) := by ext <;> simp [c10, c11, c01, c00]
  change permOf c00 [Dir.L, Dir.U, Dir.R, Dir.D]
      = Equiv.swap (i, ⟨j.1 + 1, hj⟩) (⟨i.1 + 1, hi⟩, ⟨j.1 + 1, hj⟩)
        * Equiv.swap (⟨i.1 + 1, hi⟩, ⟨j.1 + 1, hj⟩) (⟨i.1 + 1, hi⟩, j)
  rw [permOf_cons_of_neighbor? h1, permOf_cons_of_neighbor? h2,
      permOf_cons_of_neighbor? h3, permOf_cons_of_neighbor? h4, permOf_nil, mul_one]
  rw [hc00']
  simp only [← mul_assoc]
  rw [swap_mul_swap_mul_swap_mul_swap (a := c00) (b := c01) (c := c11) (d := c10)
    hne0001 hne0011 hne0010 hne0111 hne0110 hne1110, e01, e11, e10]

/-- The `2 × 2` loop is a closed walk at its top-left corner. -/
theorem trace_loop_at (i : Fin n) (j : Fin m) (hi : i.1 + 1 < n) (hj : j.1 + 1 < m) :
    trace (i, j) [Dir.L, Dir.U, Dir.R, Dir.D] = (i, j) := by
  let c00 : Cell n m := (i, j)
  have hp1 : c00.2.1 + 1 < m := by simpa [c00] using hj
  let c01 : Cell n m := (c00.1, ⟨c00.2.1 + 1, hp1⟩)
  have hp2 : c01.1.1 + 1 < n := by simpa [c01, c00] using hi
  let c11 : Cell n m := (⟨c01.1.1 + 1, hp2⟩, c01.2)
  have hp3 : 0 < c11.2.1 := by simp [c11, c01, c00]
  let c10 : Cell n m := (c11.1, ⟨c11.2.1 - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) c11.2.2⟩)
  have hp4 : 0 < c10.1.1 := by simp [c10, c11, c01, c00]
  let c00' : Cell n m := (⟨c10.1.1 - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) c10.1.2⟩, c10.2)
  have h1 : neighbor? c00 Dir.L = some c01 := by
    simp only [neighbor?]; rw [dif_pos hp1]
  have h2 : neighbor? c01 Dir.U = some c11 := by
    simp only [neighbor?]; rw [dif_pos hp2]
  have h3 : neighbor? c11 Dir.R = some c10 := by
    simp only [neighbor?]; rw [if_pos hp3]
  have h4 : neighbor? c10 Dir.D = some c00' := by
    simp only [neighbor?]; rw [if_pos hp4]
  have hc00' : c00' = c00 := by
    ext <;> simp [c00', c10, c11, c01, c00]
  change trace c00 [Dir.L, Dir.U, Dir.R, Dir.D] = c00
  rw [trace_cons_of_neighbor? h1, trace_cons_of_neighbor? h2,
      trace_cons_of_neighbor? h3, trace_cons_of_neighbor? h4, trace_nil, hc00']

/-! ### Moving the `2 × 2` loop around

To get a three-cycle at an arbitrary `2 × 2` square we conjugate the basic loop by the path
that walks the blank from the top-left corner `(0, 0)` to the square.  The path is the
"L-shaped" word `pathWord i j` (first `j` left moves, then `i` up moves).  Because the path
never visits the three cells of the target square, the conjugation does not move those cells
and the conjugated permutation is the three-cycle itself. -/

/-- `j` left moves followed by `i` up moves: the path from `(0, c)` to `(i, c+j)`. -/
def pathWord (i : ℕ) : ℕ → List Dir
  | 0 => List.replicate i Dir.U
  | j + 1 => Dir.L :: pathWord i j

@[simp] theorem pathWord_zero (i : ℕ) : pathWord i 0 = List.replicate i Dir.U := rfl

theorem pathWord_succ (i j : ℕ) : pathWord i (j + 1) = Dir.L :: pathWord i j := rfl

theorem trace_replicate_U (r i c : ℕ) (hri : r + i < n) (hc : c < m) :
    trace (((⟨r, by omega⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m) (List.replicate i Dir.U)
      = (((⟨r + i, by omega⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m) := by
  induction i generalizing r with
  | zero => simp
  | succ i ih =>
      have hr' : r + 1 < n := by omega
      have hstep : neighbor? (((⟨r, by omega⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m) Dir.U
          = some (((⟨r + 1, hr'⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m) := by
        simp only [neighbor?]; rw [dif_pos (by simpa using hr')]
      rw [List.replicate_succ, trace_cons_of_neighbor? hstep,
          ih (r := r + 1) (by omega)]
      ext <;> simp <;> omega

theorem traceSet_replicate_U_subset (r i c : ℕ) (hri : r + i < n) (hc : c < m) :
    ∀ x ∈ traceSet (((⟨r, by omega⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m)
        (List.replicate i Dir.U),
      r ≤ x.1.1 ∧ x.1.1 ≤ r + i ∧ x.2.1 = c := by
  induction i generalizing r with
  | zero =>
      intro x hx
      rw [List.replicate_zero, traceSet_nil, Finset.mem_singleton] at hx
      subst hx
      simp
  | succ i ih =>
      intro x hx
      have hr' : r + 1 < n := by omega
      have hstep : neighbor? (((⟨r, by omega⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m) Dir.U
          = some (((⟨r + 1, hr'⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m) := by
        simp only [neighbor?]; rw [dif_pos (by simpa using hr')]
      rw [List.replicate_succ, traceSet_cons_of_neighbor? hstep, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · simp
      · have := ih (r := r + 1) (by omega) x hx
        omega

theorem trace_pathWord (i j c : ℕ) (hi : i < n) (hcj : c + j < m) :
    trace (((⟨0, by omega⟩ : Fin n), (⟨c, by omega⟩ : Fin m)) : Cell n m) (pathWord i j)
      = (((⟨i, hi⟩ : Fin n), (⟨c + j, by omega⟩ : Fin m)) : Cell n m) := by
  induction j generalizing c with
  | zero =>
      rw [pathWord_zero, trace_replicate_U 0 i c (by omega) (by omega)]
      ext <;> simp
  | succ j ih =>
      have hc1 : c + 1 < m := by omega
      have hstep : neighbor? (((⟨0, by omega⟩ : Fin n), (⟨c, by omega⟩ : Fin m)) : Cell n m) Dir.L
          = some (((⟨0, by omega⟩ : Fin n), (⟨c + 1, hc1⟩ : Fin m)) : Cell n m) := by
        simp only [neighbor?]; rw [dif_pos (by simpa using hc1)]
      rw [pathWord_succ, trace_cons_of_neighbor? hstep, ih (c := c + 1) (by omega)]
      ext <;> simp <;> omega

theorem traceSet_pathWord_subset (i j c : ℕ) (hi : i < n) (hcj : c + j < m) :
    ∀ x ∈ traceSet (((⟨0, by omega⟩ : Fin n), (⟨c, by omega⟩ : Fin m)) : Cell n m) (pathWord i j),
      (x.1.1 = 0 ∧ c ≤ x.2.1 ∧ x.2.1 ≤ c + j) ∨ (x.1.1 ≤ i ∧ x.2.1 = c + j) := by
  induction j generalizing c with
  | zero =>
      intro x hx
      have := traceSet_replicate_U_subset 0 i c (by omega) (by omega) x hx
      omega
  | succ j ih =>
      intro x hx
      have hc1 : c + 1 < m := by omega
      have hstep : neighbor? (((⟨0, by omega⟩ : Fin n), (⟨c, by omega⟩ : Fin m)) : Cell n m) Dir.L
          = some (((⟨0, by omega⟩ : Fin n), (⟨c + 1, hc1⟩ : Fin m)) : Cell n m) := by
        simp only [neighbor?]; rw [dif_pos (by simpa using hc1)]
      rw [pathWord_succ, traceSet_cons_of_neighbor? hstep, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · left; refine ⟨rfl, le_refl _, ?_⟩; simp only [Fin.val_mk]; omega
      · have := ih (c := c + 1) (by omega) x hx
        omega

theorem applicableFrom_replicate_U (r i c : ℕ) (hri : r + i < n) (hc : c < m) :
    ApplicableFrom (((⟨r, by omega⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m)
      (List.replicate i Dir.U) := by
  induction i generalizing r with
  | zero => simp
  | succ i ih =>
      refine ⟨(((⟨r + 1, by omega⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m), ?_, ?_⟩
      · simp only [neighbor?]; rw [dif_pos (by omega : r + 1 < n)]
      · exact ih (r + 1) (by omega)

theorem applicableFrom_pathWord (i j c : ℕ) (hi : i < n) (hcj : c + j < m) :
    ApplicableFrom (((⟨0, by omega⟩ : Fin n), (⟨c, by omega⟩ : Fin m)) : Cell n m) (pathWord i j) := by
  induction j generalizing c with
  | zero =>
      rw [pathWord_zero]
      exact applicableFrom_replicate_U 0 i c (by omega) (by omega)
  | succ j ih =>
      refine ⟨(((⟨0, by omega⟩ : Fin n), (⟨c + 1, by omega⟩ : Fin m)) : Cell n m), ?_, ?_⟩
      · simp only [neighbor?]; rw [dif_pos (by omega : c + 1 < m)]
      · exact ih (c + 1) (by omega)

/-- The explicit action of the conjugated `2 × 2` loop: it is the three-cycle
`(i,j+1) → (i+1,j+1) → (i+1,j) → (i,j+1)`. -/
theorem squareCycle_eq (i : Fin n) (j : Fin m) (hi : i.1 + 1 < n) (hj : j.1 + 1 < m) :
    permOf ((⟨0, by omega⟩, ⟨0, by omega⟩) : Cell n m)
        (pathWord i.1 j.1 ++ [Dir.L, Dir.U, Dir.R, Dir.D] ++ invWord (pathWord i.1 j.1))
      = Equiv.swap (i, ⟨j.1 + 1, hj⟩) (⟨i.1 + 1, hi⟩, ⟨j.1 + 1, hj⟩)
        * Equiv.swap (⟨i.1 + 1, hi⟩, ⟨j.1 + 1, hj⟩) (⟨i.1 + 1, hi⟩, j) := by
  let p : Cell n m := (⟨0, by omega⟩, ⟨0, by omega⟩)
  let c : Cell n m := (i, j)
  let γ : List Dir := pathWord i.1 j.1
  let a : Cell n m := (i, ⟨j.1 + 1, hj⟩)
  let b : Cell n m := (⟨i.1 + 1, hi⟩, ⟨j.1 + 1, hj⟩)
  let d : Cell n m := (⟨i.1 + 1, hi⟩, j)
  have htrace : trace p γ = c := by
    dsimp only [p, c, γ]
    rw [trace_pathWord (n := n) (m := m) i.1 j.1 0 (by omega) (by omega)]
    ext <;> simp
  have hinv : permOf c (invWord γ) = (permOf p γ)⁻¹ := by
    rw [← htrace]
    exact permOf_invWord (by dsimp only [p, γ]; exact applicableFrom_pathWord (n := n) (m := m) i.1 j.1 0 (by omega) (by omega))
  have hloop : permOf c [Dir.L, Dir.U, Dir.R, Dir.D] = Equiv.swap a b * Equiv.swap b d := by
    dsimp only [c, a, b, d]
    exact permOf_loop_at_eq i j hi hj
  have hfixa : permOf p γ a = a := by
    apply permOf_apply_of_not_mem_traceSet
    dsimp only [p, γ, a]
    intro hmem
    have h := traceSet_pathWord_subset (n := n) (m := m) i.1 j.1 0 (by omega) (by omega)
      ((i, ⟨j.1 + 1, hj⟩) : Cell n m) hmem
    simp only [Prod.fst, Prod.snd, Fin.val_mk] at h
    omega
  have hfixb : permOf p γ b = b := by
    apply permOf_apply_of_not_mem_traceSet
    dsimp only [p, γ, b]
    intro hmem
    have h := traceSet_pathWord_subset (n := n) (m := m) i.1 j.1 0 (by omega) (by omega)
      ((⟨i.1 + 1, hi⟩, ⟨j.1 + 1, hj⟩) : Cell n m) hmem
    simp only [Prod.fst, Prod.snd, Fin.val_mk] at h
    omega
  have hfixd : permOf p γ d = d := by
    apply permOf_apply_of_not_mem_traceSet
    dsimp only [p, γ, d]
    intro hmem
    have h := traceSet_pathWord_subset (n := n) (m := m) i.1 j.1 0 (by omega) (by omega)
      ((⟨i.1 + 1, hi⟩, j) : Cell n m) hmem
    simp only [Prod.fst, Prod.snd, Fin.val_mk] at h
    omega
  have hconj : permOf p γ * (Equiv.swap a b * Equiv.swap b d) * (permOf p γ)⁻¹
      = Equiv.swap a b * Equiv.swap b d := by
    have h1 : permOf p γ * Equiv.swap a b * (permOf p γ)⁻¹ = Equiv.swap a b := by
      rw [← Equiv.swap_apply_apply (permOf p γ) a b, hfixa, hfixb]
    have h2 : permOf p γ * Equiv.swap b d * (permOf p γ)⁻¹ = Equiv.swap b d := by
      rw [← Equiv.swap_apply_apply (permOf p γ) b d, hfixb, hfixd]
    calc permOf p γ * (Equiv.swap a b * Equiv.swap b d) * (permOf p γ)⁻¹
        = (permOf p γ * Equiv.swap a b * (permOf p γ)⁻¹)
            * (permOf p γ * Equiv.swap b d * (permOf p γ)⁻¹) := by group
      _ = Equiv.swap a b * Equiv.swap b d := by rw [h1, h2]
  have hword : permOf p (γ ++ [Dir.L, Dir.U, Dir.R, Dir.D] ++ invWord γ)
      = Equiv.swap a b * Equiv.swap b d := by
    rw [List.append_assoc, permOf_append, htrace, permOf_append,
        show trace c [Dir.L, Dir.U, Dir.R, Dir.D] = c from by
          dsimp only [c]; exact trace_loop_at i j hi hj,
        hinv, hloop]
    rw [← mul_assoc]
    exact hconj
  change permOf p (γ ++ [Dir.L, Dir.U, Dir.R, Dir.D] ++ invWord γ)
      = Equiv.swap a b * Equiv.swap b d
  exact hword

/-- The conjugated `2 × 2` loop is a member of the closed-walk group. -/
theorem squareCycle_mem (i : Fin n) (j : Fin m) (hi : i.1 + 1 < n) (hj : j.1 + 1 < m) :
    permOf ((⟨0, by omega⟩, ⟨0, by omega⟩) : Cell n m)
        (pathWord i.1 j.1 ++ [Dir.L, Dir.U, Dir.R, Dir.D] ++ invWord (pathWord i.1 j.1))
      ∈ closedGroup ((⟨0, by omega⟩, ⟨0, by omega⟩) : Cell n m) := by
  apply mem_closedGroup
  let p : Cell n m := (⟨0, by omega⟩, ⟨0, by omega⟩)
  let c : Cell n m := (i, j)
  let γ : List Dir := pathWord i.1 j.1
  have htrace : trace p γ = c := by
    dsimp only [p, c, γ]
    rw [trace_pathWord (n := n) (m := m) i.1 j.1 0 (by omega) (by omega)]
    ext <;> simp
  have hinv : trace c (invWord γ) = p := by
    rw [← htrace]
    exact trace_invWord (by dsimp only [p, γ]; exact applicableFrom_pathWord (n := n) (m := m) i.1 j.1 0 (by omega) (by omega))
  change trace p (γ ++ [Dir.L, Dir.U, Dir.R, Dir.D] ++ invWord γ) = p
  rw [List.append_assoc, trace_append, htrace, trace_append,
      show trace c [Dir.L, Dir.U, Dir.R, Dir.D] = c from by
        dsimp only [c]; exact trace_loop_at i j hi hj,
      hinv]

/-! ### Transitivity of the closed-walk group -/

/-- `a` and `b` lie in the same orbit under the closed-walk group at `p`. -/
abbrev SameOrbit (p a b : Cell n m) : Prop :=
  ∃ h : Equiv.Perm (Cell n m), h ∈ closedGroup p ∧ h a = b

theorem sameOrbit_refl (p a : Cell n m) : SameOrbit p a a :=
  ⟨1, Subgroup.one_mem _, rfl⟩

theorem sameOrbit_symm {p a b : Cell n m} (h : SameOrbit p a b) : SameOrbit p b a := by
  obtain ⟨g, hg, hgab⟩ := h
  exact ⟨g⁻¹, Subgroup.inv_mem _ hg, by rw [← hgab]; simp⟩

theorem sameOrbit_trans {p a b c : Cell n m} (h1 : SameOrbit p a b) (h2 : SameOrbit p b c) :
    SameOrbit p a c := by
  obtain ⟨g, hg, hgab⟩ := h1
  obtain ⟨k, hk, hkbc⟩ := h2
  exact ⟨k * g, Subgroup.mul_mem _ hk hg, by change k (g a) = c; rw [hgab, hkbc]⟩

theorem swap_mul_swap_apply_left {α : Type*} [DecidableEq α] {a b d : α} (hab : a ≠ b) (had : a ≠ d) :
    (Equiv.swap a b * Equiv.swap b d) a = b := by
  change Equiv.swap a b (Equiv.swap b d a) = b
  grind

theorem swap_mul_swap_apply_mid {α : Type*} [DecidableEq α] {a b d : α} (hbd : b ≠ d) (hab : a ≠ b) (had : a ≠ d) :
    (Equiv.swap a b * Equiv.swap b d) b = d := by
  change Equiv.swap a b (Equiv.swap b d b) = d
  grind

theorem swap_mul_swap_apply_right {α : Type*} [DecidableEq α] {a b d : α} (had : a ≠ d) :
    (Equiv.swap a b * Equiv.swap b d) d = a := by
  change Equiv.swap a b (Equiv.swap b d d) = a
  grind

theorem sameOrbit_square (i : Fin n) (j : Fin m) (hi : i.1 + 1 < n) (hj : j.1 + 1 < m) :
    SameOrbit ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m))
        (i, ⟨j.1 + 1, hj⟩) (⟨i.1 + 1, hi⟩, ⟨j.1 + 1, hj⟩) ∧
    SameOrbit ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m))
        (⟨i.1 + 1, hi⟩, ⟨j.1 + 1, hj⟩) (⟨i.1 + 1, hi⟩, j) ∧
    SameOrbit ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m))
        (⟨i.1 + 1, hi⟩, j) (i, ⟨j.1 + 1, hj⟩) := by
  have hab : ((i, ⟨j.1 + 1, hj⟩) : Cell n m) ≠ (⟨i.1 + 1, hi⟩, ⟨j.1 + 1, hj⟩) := by
    intro hh; have := congrArg (fun x : Cell n m => x.1.1) hh; simp at this
  have had : ((i, ⟨j.1 + 1, hj⟩) : Cell n m) ≠ (⟨i.1 + 1, hi⟩, j) := by
    intro hh; have := congrArg (fun x : Cell n m => x.1.1) hh; simp at this
  have hbd : ((⟨i.1 + 1, hi⟩, ⟨j.1 + 1, hj⟩) : Cell n m) ≠ (⟨i.1 + 1, hi⟩, j) := by
    intro hh; have := congrArg (fun x : Cell n m => x.2.1) hh; simp at this
  have h1 : permOf ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m))
        (pathWord i.1 j.1 ++ [Dir.L, Dir.U, Dir.R, Dir.D] ++ invWord (pathWord i.1 j.1))
      (i, ⟨j.1 + 1, hj⟩) = (⟨i.1 + 1, hi⟩, ⟨j.1 + 1, hj⟩) := by
    rw [squareCycle_eq i j hi hj]; exact swap_mul_swap_apply_left hab had
  have h2 : permOf ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m))
        (pathWord i.1 j.1 ++ [Dir.L, Dir.U, Dir.R, Dir.D] ++ invWord (pathWord i.1 j.1))
      (⟨i.1 + 1, hi⟩, ⟨j.1 + 1, hj⟩) = (⟨i.1 + 1, hi⟩, j) := by
    rw [squareCycle_eq i j hi hj]; exact swap_mul_swap_apply_mid hbd hab had
  have h3 : permOf ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m))
        (pathWord i.1 j.1 ++ [Dir.L, Dir.U, Dir.R, Dir.D] ++ invWord (pathWord i.1 j.1))
      (⟨i.1 + 1, hi⟩, j) = (i, ⟨j.1 + 1, hj⟩) := by
    rw [squareCycle_eq i j hi hj]; exact swap_mul_swap_apply_right had
  exact ⟨⟨_, squareCycle_mem i j hi hj, h1⟩, ⟨_, squareCycle_mem i j hi hj, h2⟩,
    ⟨_, squareCycle_mem i j hi hj, h3⟩⟩

/-! ### Transitivity of the closed-walk group

The three-cycles at neighbouring `2 × 2` squares generate enough of the closed-walk group
to move any cell to any other cell.  We record the two elementary adjacencies (horizontal
and vertical) and then walk along the grid to the base cell `(0, 1)`. -/

/-- Transporting `SameOrbit` along equalities of cells. -/
theorem sameOrbit_congr {p a a' b b' : Cell n m} (ha : a = a') (hb : b = b')
    (h : SameOrbit p a b) : SameOrbit p a' b' := by
  rwa [← ha, ← hb]

/-- Horizontal adjacency: for `i ≥ 1`, the cells `(i, j)` and `(i, j+1)` lie in the same
orbit under the closed-walk group. -/
theorem sameOrbit_H {i : Fin n} {j : Fin m} (hi : 0 < i.val) (hj : j.val + 1 < m) :
    SameOrbit ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) (i, j)
      (i, ⟨j.val + 1, hj⟩) := by
  let i' : Fin n := ⟨i.val - 1, by omega⟩
  have hi' : i'.val + 1 < n := by simp only [i']; omega
  have h := sameOrbit_symm (sameOrbit_square i' j hi' hj).2.1
  have e : (⟨i'.val + 1, hi'⟩ : Fin n) = i := Fin.ext (by simp only [i']; omega)
  rwa [e] at h

/-- Vertical adjacency: for `j ≥ 1`, the cells `(i, j)` and `(i+1, j)` lie in the same
orbit under the closed-walk group. -/
theorem sameOrbit_V {i : Fin n} {j : Fin m} (hi : i.val + 1 < n) (hj : 0 < j.val) :
    SameOrbit ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) (i, j)
      (⟨i.val + 1, hi⟩, j) := by
  let j' : Fin m := ⟨j.val - 1, by omega⟩
  have hj' : j'.val + 1 < m := by simp only [j']; omega
  have h := (sameOrbit_square i j' hi hj').1
  have e : (⟨j'.val + 1, hj'⟩ : Fin m) = j := Fin.ext (by simp only [j']; omega)
  rwa [e] at h

/-- The base relation `(1, 1) ~ (0, 1)`, read off the `2 × 2` square at the origin. -/
theorem sameOrbit_base (hn : 1 < n) (hm : 1 < m) :
    SameOrbit ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m))
      ((⟨1, hn⟩ : Fin n), (⟨1, hm⟩ : Fin m))
      ((⟨0, by omega⟩ : Fin n), (⟨1, hm⟩ : Fin m)) := by
  have h := sameOrbit_symm (sameOrbit_square (⟨0, by omega⟩ : Fin n) (⟨0, by omega⟩ : Fin m)
      (by omega) (by omega)).1
  exact sameOrbit_congr rfl rfl h

/-- Along a fixed row `i ≥ 1`, every cell is in the same orbit as `(i, 1)`. -/
theorem sameOrbit_row {i : Fin n} (hm : 1 < m) (hi : 0 < i.val) :
    ∀ j : Fin m, 0 < j.val →
      SameOrbit ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) (i, j)
        (i, (⟨1, hm⟩ : Fin m)) := by
  have aux : ∀ k : ℕ, ∀ j : Fin m, j.val = k + 1 →
      SameOrbit ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) (i, j)
        (i, (⟨1, hm⟩ : Fin m)) := by
    intro k
    refine Nat.caseStrongRecOn (motive := fun k => ∀ j : Fin m, j.val = k + 1 →
      SameOrbit ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) (i, j)
        (i, (⟨1, hm⟩ : Fin m))) k ?_ ?_
    · intro j hk
      have : j = (⟨1, hm⟩ : Fin m) := Fin.ext (by omega)
      rw [this]
      exact sameOrbit_refl _ _
    · intro k ih j hk
      let jm : Fin m := ⟨k + 1, by omega⟩
      have hjm : jm.val = k + 1 := rfl
      have hIH : SameOrbit ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m))
          (i, jm) (i, (⟨1, hm⟩ : Fin m)) := ih k le_rfl jm hjm
      have hedge : SameOrbit ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m))
          (i, jm) (i, j) := by
        have h := sameOrbit_H (i := i) (j := jm) hi (by simp only [jm]; omega)
        have e : (⟨jm.val + 1, (by simp only [jm]; omega : jm.val + 1 < m)⟩ : Fin m) = j := by
          apply Fin.ext
          show jm.val + 1 = j.val
          rw [hjm]
          omega
        rwa [e] at h
      exact sameOrbit_trans (sameOrbit_symm hedge) hIH
  intro j hj
  exact aux (j.val - 1) j (by omega)

/-- Along a fixed column `j ≥ 1`, every cell is in the same orbit as `(1, j)`. -/
theorem sameOrbit_col {j : Fin m} (hn : 1 < n) (hj : 0 < j.val) :
    ∀ i : Fin n, 0 < i.val →
      SameOrbit ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) (i, j)
        ((⟨1, hn⟩ : Fin n), j) := by
  have aux : ∀ k : ℕ, ∀ i : Fin n, i.val = k + 1 →
      SameOrbit ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) (i, j)
        ((⟨1, hn⟩ : Fin n), j) := by
    intro k
    refine Nat.caseStrongRecOn (motive := fun k => ∀ i : Fin n, i.val = k + 1 →
      SameOrbit ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) (i, j)
        ((⟨1, hn⟩ : Fin n), j)) k ?_ ?_
    · intro i hi1
      have : i = (⟨1, hn⟩ : Fin n) := Fin.ext (by omega)
      rw [this]
      exact sameOrbit_refl _ _
    · intro k ih i hi1
      let im : Fin n := ⟨k + 1, by omega⟩
      have him : im.val = k + 1 := rfl
      have hIH : SameOrbit ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m))
          (im, j) ((⟨1, hn⟩ : Fin n), j) := ih k le_rfl im him
      have hedge : SameOrbit ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m))
          (im, j) (i, j) := by
        have h := sameOrbit_V (i := im) (j := j) (by simp only [im]; omega) hj
        have e : (⟨im.val + 1, (by simp only [im]; omega : im.val + 1 < n)⟩ : Fin n) = i := by
          apply Fin.ext
          show im.val + 1 = i.val
          rw [him]
          omega
        rwa [e] at h
      exact sameOrbit_trans (sameOrbit_symm hedge) hIH
  intro i hi
  exact aux (i.val - 1) i (by omega)

/-- **Transitivity of the closed-walk group.**  For `n, m ≥ 2`, every cell other than the
base point `(0, 0)` lies in the same orbit under the closed-walk group as `(0, 1)`. -/
theorem sameOrbit_zero_one (hn : 1 < n) (hm : 1 < m) :
    ∀ c : Cell n m,
      c ≠ ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) →
      SameOrbit ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) c
        ((⟨0, by omega⟩ : Fin n), (⟨1, hm⟩ : Fin m)) := by
  intro c hc
  by_cases hi : 0 < c.1.val
  · by_cases hj : 0 < c.2.val
    · have hrow := sameOrbit_row (i := c.1) hm hi c.2 hj
      have hcol := sameOrbit_col (j := (⟨1, hm⟩ : Fin m)) hn (by simp) c.1 hi
      exact sameOrbit_trans hrow (sameOrbit_trans hcol (sameOrbit_base hn hm))
    · have hcz : c.2.val = 0 := by omega
      have hz : c.2 = (⟨0, by omega⟩ : Fin m) := Fin.ext hcz
      have h := sameOrbit_H (i := c.1) (j := (⟨0, by omega⟩ : Fin m)) hi (by simp; omega)
      have h' : SameOrbit ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) (c.1, c.2)
          (c.1, (⟨1, hm⟩ : Fin m)) := by
        have hh := h
        have hsrc : (c.1, (⟨0, by omega⟩ : Fin m)) = (c.1, c.2) := Prod.ext rfl hz.symm
        rw [hsrc] at hh
        exact hh
      have hcol := sameOrbit_col (j := (⟨1, hm⟩ : Fin m)) hn (by simp) c.1 hi
      exact sameOrbit_trans h' (sameOrbit_trans hcol (sameOrbit_base hn hm))
  · have hcx : c.1.val = 0 := by omega
    have hx : c.1 = (⟨0, by omega⟩ : Fin n) := Fin.ext hcx
    have hcj : 0 < c.2.val := by
      by_contra h
      have hz : c.2.val = 0 := by omega
      exact hc (Prod.ext (Fin.ext hcx) (Fin.ext hz))
    have h := sameOrbit_V (i := (⟨0, by omega⟩ : Fin n)) (j := c.2) (by simp; omega) hcj
    have h' : SameOrbit ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) (c.1, c.2)
        ((⟨1, hn⟩ : Fin n), c.2) := by
      have hh := h
      have hsrc : ((⟨0, by omega⟩ : Fin n), c.2) = (c.1, c.2) := Prod.ext hx.symm rfl
      rw [hsrc] at hh
      exact hh
    have hrow := sameOrbit_row (i := (⟨1, hn⟩ : Fin n)) hm (by simp) c.2 hcj
    exact sameOrbit_trans h' (sameOrbit_trans hrow (sameOrbit_base hn hm))

/-- Conjugating by the cell permutation of a path from `p` to `base` carries the closed-walk
group at `base` into the closed-walk group at `p`. -/
theorem conj_mem_closedGroup {p base : Cell n m} {β : List Dir}
    (hβ : trace p β = base) (happ : ApplicableFrom p β) {k : Equiv.Perm (Cell n m)}
    (hk : k ∈ closedGroup base) :
    permOf p β * k * (permOf p β)⁻¹ ∈ closedGroup p := by
  refine Subgroup.closure_induction ?mem ?one ?mul ?inv hk
  · intro x hx
    obtain ⟨σ, hσ, rfl⟩ := hx
    have hperm : permOf p (β ++ σ ++ invWord β)
        = permOf p β * permOf base σ * (permOf p β)⁻¹ := by
      rw [List.append_assoc, permOf_append, permOf_append, hβ, hσ, ← hβ,
        permOf_invWord happ, mul_assoc]
    have hclosed : trace p (β ++ σ ++ invWord β) = p := by
      rw [List.append_assoc, trace_append, trace_append, hβ, hσ, ← hβ,
        trace_invWord happ]
    rw [← hperm]
    exact mem_closedGroup hclosed
  · simp
  · intro x y hx hy ihx ihy
    have h : permOf p β * (x * y) * (permOf p β)⁻¹
        = (permOf p β * x * (permOf p β)⁻¹) * (permOf p β * y * (permOf p β)⁻¹) := by
      group
    rw [h]
    exact Subgroup.mul_mem _ ihx ihy
  · intro x hx ih
    have h : permOf p β * x⁻¹ * (permOf p β)⁻¹
        = (permOf p β * x * (permOf p β)⁻¹)⁻¹ := by
      group
    rw [h]
    exact Subgroup.inv_mem _ ih

/-- **Transitivity at an arbitrary base point.**  For `n, m ≥ 2` and any cell `p`, the
closed-walk group at `p` is transitive on the cells other than `p`. -/
theorem sameOrbit_transitive (hn : 1 < n) (hm : 1 < m) (p : Cell n m) :
    ∀ a b : Cell n m, a ≠ p → b ≠ p → SameOrbit p a b := by
  let base : Cell n m := ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m))
  let β : List Dir := invWord (pathWord p.1.val p.2.val)
  have hpath_trace : trace base (pathWord p.1.val p.2.val) = p := by
    rw [trace_pathWord (n := n) (m := m) p.1.val p.2.val 0 (by omega) (by omega)]
    ext <;> simp
  have hpath_app : ApplicableFrom base (pathWord p.1.val p.2.val) :=
    applicableFrom_pathWord (n := n) (m := m) p.1.val p.2.val 0 (by omega) (by omega)
  have hβ_trace : trace p β = base := by
    have h := trace_invWord hpath_app
    rw [hpath_trace] at h
    simpa only [β] using h
  have hβ_app : ApplicableFrom p β := by
    have h := applicableFrom_invWord hpath_app
    rw [hpath_trace] at h
    simpa only [β] using h
  let u : Equiv.Perm (Cell n m) := permOf p β
  have hu : u base = p := by
    have h : u.symm p = base := by
      dsimp only [u]
      rw [permOf_symm_apply, hβ_trace]
    exact ((Equiv.symm_apply_eq u).mp h).symm
  intro a b ha hb
  have ha' : u.symm a ≠ base := by
    intro h
    have : a = u base := by rw [← Equiv.apply_symm_apply u a, h]
    rw [hu] at this
    exact ha this
  have hb' : u.symm b ≠ base := by
    intro h
    have : b = u base := by rw [← Equiv.apply_symm_apply u b, h]
    rw [hu] at this
    exact hb this
  have hsame : SameOrbit base (u.symm a) (u.symm b) :=
    sameOrbit_trans (sameOrbit_zero_one hn hm (u.symm a) ha')
      (sameOrbit_symm (sameOrbit_zero_one hn hm (u.symm b) hb'))
  obtain ⟨k, hk, hkab⟩ := hsame
  have hmem : u * k * u⁻¹ ∈ closedGroup p := conj_mem_closedGroup hβ_trace hβ_app hk
  refine ⟨u * k * u⁻¹, hmem, ?_⟩
  change u (k (u.symm a)) = b
  rw [hkab, Equiv.apply_symm_apply]

end Zhong

