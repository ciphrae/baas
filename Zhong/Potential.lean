/-
Copyright (c) 2026 The Zhong formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhong formalisation contributors
-/
import Zhong.Orbit

/-!
# Potential functions

This file formalises Definition 9 and Proposition 5 of Zhong (2023).

The paper defines a potential function `ϕ : O → ℝ` by the one-sided inequality
`ϕ (δB) ≥ ϕ B - 1`, and then claims (Proposition 5)

`ϕ B - ϕ B' ≤ |σ| ≤ ϕ B - ϕ B' + 2k`

for `B' = B σ`, where `k` is the number of inefficient moves.  The upper bound is
*false* for an arbitrary one-sided potential: a move could increase `ϕ` by more than
`1`.  Both potentials actually used in the paper (the inversion number and the
Manhattan distance) change by at most `1` in absolute value, and this is exactly what
the proof needs.  We therefore introduce the strengthened notion `IsPotential1`
(`|ϕ (δB) - ϕ B| ≤ 1`), show it implies Definition 9, and prove Proposition 5 for it.
-/

namespace Zhong

open Equiv

variable {n m : ℕ}

/-- Definition 9: a potential function.  For every applicable move, `ϕ` may decrease
by at most `1`. -/
def IsPotential [NeZero (n * m)] (ϕ : Board n m → ℤ) : Prop :=
  ∀ (B : Board n m) (δ : Dir), Applicable B δ → ϕ (act B δ) ≥ ϕ B - 1

/-- The strengthened potential property needed for Proposition 5: every applicable
move changes `ϕ` by at most `1` in absolute value. -/
def IsPotential1 [NeZero (n * m)] (ϕ : Board n m → ℤ) : Prop :=
  ∀ (B : Board n m) (δ : Dir), Applicable B δ → |ϕ (act B δ) - ϕ B| ≤ 1

/-- A move is efficient (with respect to `ϕ`) if it decreases `ϕ` by exactly `1`. -/
def IsEfficient [NeZero (n * m)] (ϕ : Board n m → ℤ) (B : Board n m) (δ : Dir) : Prop :=
  ϕ (act B δ) = ϕ B - 1

instance [NeZero (n * m)] (ϕ : Board n m → ℤ) (B : Board n m) (δ : Dir) :
    Decidable (IsEfficient ϕ B δ) :=
  inferInstanceAs (Decidable (ϕ (act B δ) = ϕ B - 1))

theorem IsPotential1.isPotential [NeZero (n * m)] {ϕ : Board n m → ℤ}
    (h : IsPotential1 ϕ) : IsPotential ϕ := by
  intro B δ ha
  have h' := h B δ ha
  rw [abs_le] at h'
  linarith [h'.1]

/-- The number of moves in `σ` that are *not* efficient, starting from `B`. -/
def ineffCount [NeZero (n * m)] (ϕ : Board n m → ℤ) : Board n m → List Dir → ℕ
  | _, [] => 0
  | B, δ :: σ => (if IsEfficient ϕ B δ then 0 else 1) + ineffCount ϕ (act B δ) σ

@[simp] theorem ineffCount_nil [NeZero (n * m)] (ϕ : Board n m → ℤ) (B : Board n m) :
    ineffCount ϕ B [] = 0 := rfl

theorem ineffCount_cons [NeZero (n * m)] (ϕ : Board n m → ℤ) (B : Board n m)
    (δ : Dir) (σ : List Dir) :
    ineffCount ϕ B (δ :: σ)
      = (if IsEfficient ϕ B δ then 0 else 1) + ineffCount ϕ (act B δ) σ := rfl

/-- A single move decreases `ϕ` by at most `1` (for the strengthened potential). -/
theorem potential1_lower_step [NeZero (n * m)] {ϕ : Board n m → ℤ}
    (hϕ : IsPotential1 ϕ) (B : Board n m) (δ : Dir) :
    ϕ B - ϕ (act B δ) ≤ 1 := by
  by_cases ha : Applicable B δ
  · have h := hϕ B δ ha
    rw [abs_le] at h
    linarith [h.2]
  · rw [act_of_not_applicable ha]; simp

/-- The per-move contribution to the upper bound of Proposition 5. -/
theorem potential1_upper_step [NeZero (n * m)] {ϕ : Board n m → ℤ}
    (hϕ : IsPotential1 ϕ) (B : Board n m) (δ : Dir) :
    (1 : ℤ) ≤ ϕ B - ϕ (act B δ) + 2 * (if IsEfficient ϕ B δ then 0 else 1) := by
  by_cases ha : Applicable B δ
  · by_cases he : IsEfficient ϕ B δ
    · rw [if_pos he]; rw [IsEfficient] at he; omega
    · rw [if_neg he]
      have h := hϕ B δ ha
      rw [abs_le] at h
      rw [IsEfficient] at he
      have hne : ϕ (act B δ) - ϕ B ≠ -1 := by
        intro hc; exact he (by linarith)
      have hlt : (-1 : ℤ) < ϕ (act B δ) - ϕ B := lt_of_le_of_ne h.1 (Ne.symm hne)
      omega
  · have hB : act B δ = B := act_of_not_applicable ha
    rw [hB]
    have he : ¬ IsEfficient ϕ B δ := by
      rw [IsEfficient, hB]; intro hc; omega
    rw [if_neg he]; omega

/-- Proposition 5, lower bound: `ϕ B - ϕ (B σ) ≤ |σ|`. -/
theorem potential_lower [NeZero (n * m)] {ϕ : Board n m → ℤ}
    (hϕ : IsPotential1 ϕ) (B : Board n m) (σ : List Dir) :
    ϕ B - ϕ (actSeq B σ) ≤ (σ.length : ℤ) := by
  induction σ generalizing B with
  | nil => simp
  | cons δ σ ih =>
      rw [actSeq_cons, List.length_cons]
      have h1 := potential1_lower_step hϕ B δ
      have h2 := ih (act B δ)
      push_cast
      linarith

/-- Proposition 5, upper bound: `|σ| ≤ ϕ B - ϕ (B σ) + 2k` where `k` is the number of
inefficient moves. -/
theorem potential_upper [NeZero (n * m)] {ϕ : Board n m → ℤ}
    (hϕ : IsPotential1 ϕ) (B : Board n m) (σ : List Dir) :
    (σ.length : ℤ) ≤ ϕ B - ϕ (actSeq B σ) + 2 * (ineffCount ϕ B σ : ℤ) := by
  induction σ generalizing B with
  | nil => simp
  | cons δ σ ih =>
      rw [actSeq_cons, List.length_cons, ineffCount_cons]
      have h1 := potential1_upper_step hϕ B δ
      have h2 := ih (act B δ)
      push_cast
      linarith

/-- The lower bound of Proposition 5 applied to the optimal length: for reachable boards,
`ϕ B - ϕ B' ≤ OPT`. -/
theorem optLen_lower [NeZero (n * m)] {ϕ : Board n m → ℤ} (hϕ : IsPotential1 ϕ)
    {B B' : Board n m} (h : Reachable B B') :
    ϕ B - ϕ B' ≤ (optLen B B' : ℤ) := by
  obtain ⟨σ, hact, hlen⟩ := optLen_spec h
  have hlow := potential_lower hϕ B σ
  rw [hact, hlen] at hlow
  exact hlow

/-- The upper bound of Proposition 5 applied to the optimal length: any solving sequence
`σ` gives `OPT ≤ ϕ B - ϕ B' + 2 · (inefficient moves of σ)`. -/
theorem optLen_upper [NeZero (n * m)] {ϕ : Board n m → ℤ} (hϕ : IsPotential1 ϕ)
    {B B' : Board n m} (σ : List Dir) (h : actSeq B σ = B') :
    (optLen B B' : ℤ) ≤ ϕ B - ϕ B' + 2 * (ineffCount ϕ B σ : ℤ) := by
  have h1 : (optLen B B' : ℤ) ≤ (σ.length : ℤ) := by
    exact_mod_cast optLen_le_length σ h
  have h2 := potential_upper hϕ B σ
  rw [h] at h2
  linarith

end Zhong
