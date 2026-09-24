/-
Copyright (c) 2026 The Zhong formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhong formalisation contributors
-/
import Zhong.Glue
import Zhong.Uniform

/-!
# The parity criterion for reachability (Proposition 3)

This file completes the converse of Proposition 3 of Zhong (2023).  The easy direction
(`reachable_sign_relPerm`, in `Orbit.lean`) shows that reachable boards have matching
parity invariant.  Here we prove the converse, using the group-theoretic description of
the closed-walk group (`altOn_compl_le_closedGroup`).

The key intermediate statement is `mem_walkSet_iff_sign`: a cell permutation `g` is
induced by some operation sequence starting with the blank at `p` if and only if
`sign g = cellParity p * cellParity (g⁻¹ p)`.  This is exactly the parity criterion, since
the cell permutation taking `B₁` to `B₂` has `g⁻¹ (blank B₁) = blank B₂` and the same
sign as `relPerm B₁ B₂`.
-/

namespace Zhong

open Equiv

variable {n m : ℕ}

/-- The sign of a walk permutation is determined by the parities of the initial and final
blank cells. -/
theorem sign_of_mem_walkSet [NeZero (n * m)] {p : Cell n m} {g : Equiv.Perm (Cell n m)}
    (hg : g ∈ walkSet p) :
    Equiv.Perm.sign g = cellParity p * cellParity (g⁻¹ p) := by
  obtain ⟨σ, rfl⟩ := mem_walkSet.mp hg
  rw [sign_permOf]
  congr 1
  exact congrArg cellParity (permOf_symm_apply p σ).symm

/-- **Parity criterion for walk permutations.**  For `m ≥ 3` and `n ≥ 2`, a cell
permutation `g` is realisable by an operation sequence starting with the blank at `p` if
and only if its sign is the product of the parities of `p` and `g⁻¹ p`. -/
theorem mem_walkSet_iff_sign [NeZero (n * m)] (hm : 3 ≤ m) (hn : 2 ≤ n) (p : Cell n m)
    (g : Equiv.Perm (Cell n m)) :
    g ∈ walkSet p ↔ Equiv.Perm.sign g = cellParity p * cellParity (g⁻¹ p) := by
  constructor
  · exact sign_of_mem_walkSet
  · intro hsign
    let q : Cell n m := g⁻¹ p
    obtain ⟨gq, hgq⟩ : (walkFiber p q).Nonempty := walkFiber_nonempty p q
    have hgq_walk : gq ∈ walkSet p := (mem_walkFiber.mp hgq).1
    have hgq_inv : gq⁻¹ p = q := (mem_walkFiber.mp hgq).2
    have hgq_sign : Equiv.Perm.sign gq = cellParity p * cellParity q := by
      rw [sign_of_mem_walkSet hgq_walk, hgq_inv]
    have hk_fix : (g * gq⁻¹) p = p := by
      rw [Equiv.Perm.mul_apply, hgq_inv]
      exact Equiv.apply_symm_apply g p
    have hk_sign : Equiv.Perm.sign (g * gq⁻¹) = 1 := by
      rw [map_mul, map_inv, hsign, hgq_sign]
      rw [show g⁻¹ p = q from rfl]
      group
    have hk_alt : g * gq⁻¹ ∈ altOn ((Finset.univ : Finset (Cell n m)) \ {p}) := by
      apply mem_altOn_of_fixes_compl
      · intro x hx
        have hxp : x = p := by
          by_contra h
          exact hx (Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, by simpa using h⟩)
        rw [hxp]; exact hk_fix
      · exact hk_sign
    have hk_mem : g * gq⁻¹ ∈ closedGroup p := altOn_compl_le_closedGroup hm hn p hk_alt
    have hmem := mul_mem_walkSet hk_mem hgq_walk
    have heq : (g * gq⁻¹) * gq = g := by group
    rwa [heq] at hmem

/-- **Proposition 3 (converse direction).**  If the relative permutation of two boards has
the parity of the blank-cell parities, then the boards are reachable from one another. -/
theorem reachable_of_sign_relPerm [NeZero (n * m)] (hm : 3 ≤ m) (hn : 2 ≤ n)
    {B₁ B₂ : Board n m}
    (h : Equiv.Perm.sign (relPerm B₁ B₂)
      = cellParity (blank B₁) * cellParity (blank B₂)) :
    Reachable B₁ B₂ := by
  let p : Cell n m := blank B₁
  let ρ : Equiv.Perm (Cell n m) := B₂.trans B₁.symm
  have hpc : relPerm B₁ B₂ = B₁.permCongr ρ := by
    simp only [Equiv.permCongr_def, relPerm, ρ, Equiv.trans_assoc, Equiv.symm_trans_self,
      Equiv.trans_refl]
  have hsignρ : Equiv.Perm.sign ρ = Equiv.Perm.sign (relPerm B₁ B₂) := by
    rw [hpc, Equiv.Perm.sign_permCongr]
  have hB1p : B₁ p = 0 := by
    show B₁ (B₁.symm 0) = 0
    exact Equiv.apply_symm_apply B₁ 0
  have hρinv : ρ⁻¹ p = blank B₂ := by
    change (B₂.trans B₁.symm).symm p = blank B₂
    rw [Equiv.symm_trans, Equiv.symm_symm]
    change B₂.symm (B₁ p) = B₂.symm 0
    rw [hB1p]
  have hρ : ρ ∈ walkSet p := by
    rw [mem_walkSet_iff_sign hm hn p ρ, hsignρ, hρinv, h]
  obtain ⟨σ, hσ⟩ := mem_walkSet.mp hρ
  refine ⟨σ, ?_⟩
  rw [actSeq_eq_permOf, hσ]
  change (B₂.trans B₁.symm).trans B₁ = B₂
  rw [Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.trans_refl]

/-- Reachability is symmetric. -/
theorem reachable_symm [NeZero (n * m)] (hm : 3 ≤ m) (hn : 2 ≤ n) {B₁ B₂ : Board n m}
    (h : Reachable B₁ B₂) : Reachable B₂ B₁ := by
  apply reachable_of_sign_relPerm hm hn
  have h1 := reachable_sign_relPerm h
  rw [sign_relPerm B₁ B₂] at h1
  rw [sign_relPerm B₂ B₁]
  rw [mul_comm (boardSign B₂) (boardSign B₁),
    mul_comm (cellParity (blank B₂)) (cellParity (blank B₁))]
  exact h1

end Zhong
