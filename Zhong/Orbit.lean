/-
Copyright (c) 2026 The Zhong formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhong formalisation contributors
-/
import Zhong.Basic

/-!
# Reachability, orbits, and optimal solution length

This file begins Section 2.2 of Zhong (2023): the orbit of a board and the optimal
solution length `OPT`.  The parity criterion (Proposition 3) is not yet formalised; see
`PLAN.md`, milestone M1.
-/

namespace Zhong

open Equiv

variable {n m : ℕ}

/-- `B'` is reachable from `B` by some operation sequence. -/
def Reachable [NeZero (n * m)] (B B' : Board n m) : Prop :=
  ∃ σ : List Dir, actSeq B σ = B'

/-- The orbit of a board: the finite set of boards reachable from it. -/
noncomputable def orbit [NeZero (n * m)] (B : Board n m) : Finset (Board n m) := by
  classical
  exact Finset.univ.filter (Reachable B)

theorem reachable_refl [NeZero (n * m)] (B : Board n m) : Reachable B B :=
  ⟨[], rfl⟩

theorem reachable_trans [NeZero (n * m)] {B₁ B₂ B₃ : Board n m}
    (h₁ : Reachable B₁ B₂) (h₂ : Reachable B₂ B₃) : Reachable B₁ B₃ := by
  obtain ⟨σ₁, rfl⟩ := h₁
  obtain ⟨σ₂, h₂⟩ := h₂
  exact ⟨σ₁ ++ σ₂, by rw [actSeq_append, h₂]⟩

theorem mem_orbit_self [NeZero (n * m)] (B : Board n m) : B ∈ orbit B := by
  classical
  simp [orbit, reachable_refl B]

/-- The optimal solution length from `B` to `B'`: the infimum of the lengths of
operation sequences taking `B` to `B'`. -/
noncomputable def optLen [NeZero (n * m)] (B B' : Board n m) : ℕ :=
  sInf { l : ℕ | ∃ σ : List Dir, σ.length = l ∧ actSeq B σ = B' }

/-- Any operation sequence gives an upper bound for the optimal length. -/
theorem optLen_le_length [NeZero (n * m)] {B B' : Board n m} (σ : List Dir)
    (h : actSeq B σ = B') : optLen B B' ≤ σ.length :=
  Nat.sInf_le ⟨σ, rfl, h⟩

/-- The optimal length is attained by some operation sequence (when `B'` is reachable). -/
theorem optLen_spec [NeZero (n * m)] {B B' : Board n m} (h : Reachable B B') :
    ∃ σ : List Dir, actSeq B σ = B' ∧ σ.length = optLen B B' := by
  have hne : { l : ℕ | ∃ σ : List Dir, σ.length = l ∧ actSeq B σ = B' }.Nonempty := by
    obtain ⟨σ, rfl⟩ := h
    exact ⟨σ.length, σ, rfl, rfl⟩
  obtain ⟨σ, hlen, hact⟩ := Nat.sInf_mem hne
  exact ⟨σ, hact, hlen⟩

/-! ### The parity invariant (Proposition 3, necessary direction)

Proposition 3 of Zhong (2023) characterises when two boards lie in the same orbit: the
permutation of the labels together with the parities of the two blank positions must have
matching parity.  The easy direction — that the invariant

`sign (relPerm target B) * (-1) ^ (x₀(B) + y₀(B))`

is preserved by every move — is proved in this section.  The converse (every even
relabelling of the target is reachable) is the subject of the remaining part of
milestone M1. -/

/-- The label permutation taking `B₁` to `B₂`, i.e. the unique `π` with `B₂ = π ∘ B₁`. -/
def relPerm (B₁ B₂ : Board n m) : Equiv.Perm (Fin (n * m)) := B₁.symm.trans B₂

/-- The sign of a board, relative to the target board.  This is the sign of the cell
permutation sending every cell to the cell whose target label currently occupies it. -/
noncomputable def boardSign (B : Board n m) : ℤˣ :=
  Equiv.Perm.sign (B.trans (target n m).symm)

/-- `(-1)` raised to the parity of the cell `(x, y)`. -/
def cellParity (c : Cell n m) : ℤˣ := (-1 : ℤˣ) ^ (c.1.1 + c.2.1)

/-- The parity invariant of Proposition 3. -/
noncomputable def invariant [NeZero (n * m)] (B : Board n m) : ℤˣ :=
  boardSign B * cellParity (blank B)

/-- Transposition is the reversed group multiplication on permutations. -/
theorem perm_trans_eq_mul {α : Type} (f g : Equiv.Perm α) : f.trans g = g * f := by
  ext x; rfl

/-- Every unit of `ℤ` is its own inverse. -/
theorem units_inv_eq_self (u : ℤˣ) : u⁻¹ = u := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num

/-- Every unit of `ℤ` squares to `1`. -/
theorem units_mul_self (u : ℤˣ) : u * u = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num

theorem cellParity_sq (c : Cell n m) : cellParity c * cellParity c = 1 := by
  unfold cellParity
  rw [← pow_add]
  have : c.1.1 + c.2.1 + (c.1.1 + c.2.1) = 2 * (c.1.1 + c.2.1) := by ring
  rw [this, pow_mul]
  simp

theorem boardSign_sq (B : Board n m) : boardSign B * boardSign B = 1 :=
  units_mul_self _

/-- The relative permutation is the conjugation, by the target, of the relative cell
permutation. -/
theorem relPerm_eq_permCongr (B₁ B₂ : Board n m) :
    relPerm B₁ B₂
      = (target n m).permCongr
          ((B₂.trans (target n m).symm) * (B₁.trans (target n m).symm)⁻¹) := by
  ext x
  simp [relPerm, Equiv.permCongr_def, Equiv.trans_apply]

/-- The sign of the relative permutation is the product of the two board signs. -/
theorem sign_relPerm (B₁ B₂ : Board n m) :
    Equiv.Perm.sign (relPerm B₁ B₂) = boardSign B₁ * boardSign B₂ := by
  rw [relPerm_eq_permCongr, Equiv.Perm.sign_permCongr, map_mul, map_inv,
      boardSign, boardSign, units_inv_eq_self]
  rw [mul_comm]

/-- The sign of the transposition of blank and neighbour. -/
theorem boardSign_act [NeZero (n * m)] {B : Board n m} {δ : Dir} {c' : Cell n m}
    (h : neighbor? (blank B) δ = some c') :
    boardSign (act B δ) = boardSign B * Equiv.Perm.sign (Equiv.swap (blank B) c') := by
  rw [boardSign, boardSign, act_of_neighbor? h]
  rw [Equiv.trans_assoc, perm_trans_eq_mul, map_mul]

/-- Adjacent cells have opposite parity. -/
theorem cellParity_neighbor {c c' : Cell n m} {δ : Dir}
    (h : neighbor? c δ = some c') : cellParity c' = cellParity c * (-1) := by
  cases δ
  case U =>
    rw [neighbor?] at h
    by_cases hc : c.1.1 + 1 < n
    · rw [dif_pos hc] at h; injection h with h'; subst h'
      unfold cellParity
      rw [show c.1.1 + 1 + c.2.1 = (c.1.1 + c.2.1) + 1 by omega, pow_succ]
    · rw [dif_neg hc] at h; exact absurd h (by simp)
  case D =>
    rw [neighbor?] at h
    by_cases hc : 0 < c.1.1
    · rw [if_pos hc] at h; injection h with h'; subst h'
      unfold cellParity
      rw [show c.1.1 + c.2.1 = ((c.1.1 - 1) + c.2.1) + 1 by omega, pow_succ]
      rw [mul_assoc, show (-1 : ℤˣ) * (-1) = 1 by norm_num, mul_one]
    · rw [if_neg hc] at h; exact absurd h (by simp)
  case L =>
    rw [neighbor?] at h
    by_cases hc : c.2.1 + 1 < m
    · rw [dif_pos hc] at h; injection h with h'; subst h'
      unfold cellParity
      rw [show c.1.1 + (c.2.1 + 1) = (c.1.1 + c.2.1) + 1 by omega, pow_succ]
    · rw [dif_neg hc] at h; exact absurd h (by simp)
  case R =>
    rw [neighbor?] at h
    by_cases hc : 0 < c.2.1
    · rw [if_pos hc] at h; injection h with h'; subst h'
      unfold cellParity
      rw [show c.1.1 + c.2.1 = (c.1.1 + (c.2.1 - 1)) + 1 by omega, pow_succ]
      rw [mul_assoc, show (-1 : ℤˣ) * (-1) = 1 by norm_num, mul_one]
    · rw [if_neg hc] at h; exact absurd h (by simp)

/-- The parity invariant is preserved by every applicable move. -/
theorem invariant_act [NeZero (n * m)] {B : Board n m} {δ : Dir}
    (ha : Applicable B δ) : invariant (act B δ) = invariant B := by
  obtain ⟨c', hc'⟩ : ∃ c', neighbor? (blank B) δ = some c' := by
    unfold Applicable at ha
    cases h : neighbor? (blank B) δ with
    | none => simp [h] at ha
    | some c' => exact ⟨c', rfl⟩
  rw [invariant, invariant, blank_act_of_neighbor? hc', boardSign_act hc',
      Equiv.Perm.sign_swap (neighbor?_ne hc').symm, cellParity_neighbor hc']
  calc (boardSign B * (-1)) * (cellParity (blank B) * (-1))
      = (boardSign B * cellParity (blank B)) * ((-1) * (-1)) := by ac_rfl
    _ = boardSign B * cellParity (blank B) := by
        rw [show (-1 : ℤˣ) * (-1) = 1 by norm_num, mul_one]

/-- The parity invariant is preserved along any operation sequence. -/
theorem invariant_actSeq [NeZero (n * m)] (B : Board n m) (σ : List Dir) :
    invariant (actSeq B σ) = invariant B := by
  induction σ generalizing B with
  | nil => simp
  | cons δ σ ih =>
      rw [actSeq_cons, ih (act B δ)]
      by_cases ha : Applicable B δ
      · exact invariant_act ha
      · rw [act_of_not_applicable ha]

/-- Reachable boards have the same parity invariant. -/
theorem reachable_invariant [NeZero (n * m)] {B₁ B₂ : Board n m}
    (h : Reachable B₁ B₂) : invariant B₁ = invariant B₂ := by
  obtain ⟨σ, rfl⟩ := h
  exact (invariant_actSeq B₁ σ).symm

/-- **Proposition 3 (necessary direction).**  If `B₁` and `B₂` lie in the same orbit, then
the permutation of labels taking `B₁` to `B₂` has the parity of the sum of the blank-cell
parities. -/
theorem reachable_sign_relPerm [NeZero (n * m)] {B₁ B₂ : Board n m}
    (h : Reachable B₁ B₂) :
    Equiv.Perm.sign (relPerm B₁ B₂) = cellParity (blank B₁) * cellParity (blank B₂) := by
  have hI : invariant B₁ = invariant B₂ := reachable_invariant h
  have key : ∀ a b p q : ℤˣ, a * a = 1 → b * b = 1 → p * p = 1 → q * q = 1 →
      a * p = b * q → a * b = p * q := by
    intro a b p q ha hb hp hq h
    have h1 : p = a * b * q := by
      calc p = (a * a) * p := by rw [ha, one_mul]
        _ = a * (a * p) := by rw [mul_assoc]
        _ = a * (b * q) := by rw [h]
        _ = a * b * q := by rw [mul_assoc]
    calc a * b = a * b * (q * q) := by rw [hq, mul_one]
      _ = (a * b * q) * q := by ac_rfl
      _ = p * q := by rw [← h1]
  rw [sign_relPerm]
  exact key _ _ _ _ (boardSign_sq B₁) (boardSign_sq B₂)
    (cellParity_sq _) (cellParity_sq _) hI

end Zhong
