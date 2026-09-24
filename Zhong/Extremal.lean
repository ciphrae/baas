/-
Copyright (c) 2026 The Zhong formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhong formalisation contributors
-/
import Zhong.Reachable

/-!
# Extremal Manhattan distance (step 5 of Proposition 9)

`Manhattan.lean` proves the pointwise bound `D B ≤ n³` (`D_le_cube`) and the lower bound
`D (rev ∘ BT) ≥ n³ − 3n²` for the 180°-rotated target (`D_rev_lower`).  Here we show that
the rotated target actually lies in the orbit of the target, using the parity criterion of
Proposition 3 (`reachable_of_sign_relPerm`).  Consequently the maximum of `D` over the orbit
is at least `n³ − 3n²`, which is the extremal lower bound of step 5.

The two ingredients are that the 180° rotation is an even permutation of the cells
(`sign_rev`) and that it preserves the parity of a cell (`cellParity_rev`).
-/

namespace Zhong

open Equiv

variable {n : ℕ}

/-- The 180° rotation of the cells is an even permutation. -/
theorem sign_rev (n : ℕ) : Equiv.Perm.sign (rev n) = 1 := by
  have hrev : rev n = Equiv.prodCongr Fin.revPerm Fin.revPerm := by
    apply Equiv.ext
    rintro ⟨a, b⟩
    apply Prod.ext <;> apply Fin.ext <;>
      simp only [Equiv.prodCongr_apply, rev_apply_fst, rev_apply_snd, Prod.map,
        Fin.revPerm_apply, Fin.rev] <;> omega
  rw [hrev]
  rw [show Equiv.prodCongr Fin.revPerm Fin.revPerm =
      Equiv.prodCongr Fin.revPerm (Equiv.refl (Fin n)) *
      Equiv.prodCongr (Equiv.refl (Fin n)) Fin.revPerm from by
        apply Equiv.ext
        rintro ⟨a, b⟩
        apply Prod.ext <;> rfl]
  rw [map_mul, Equiv.prodCongr_refl_right, Equiv.prodCongr_refl_left,
    Equiv.Perm.sign_prodCongrLeft, Equiv.Perm.sign_prodCongrRight]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_add, show n + n = 2 * n by omega, pow_mul]
  rw [show (Equiv.Perm.sign Fin.revPerm) ^ 2 = 1 by rw [sq]; exact units_mul_self _]
  simp

/-- The 180° rotation preserves the parity of a cell. -/
theorem cellParity_rev (n : ℕ) (c : Cell n n) : cellParity (rev n c) = cellParity c := by
  apply Units.ext
  unfold cellParity
  rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
  rw [rev_apply_fst, rev_apply_snd]
  apply neg_one_pow_congr
  rw [Nat.even_iff, Nat.even_iff]
  omega

/-- The 180°-rotated target is reachable from the target. -/
theorem rev_trans_target_reachable (hn : 3 ≤ n) [NeZero (n * n)] :
    Reachable (target n n) ((rev n).trans (target n n)) := by
  apply reachable_of_sign_relPerm (n := n) (m := n) (by omega) (by omega)
  have hpc : relPerm (target n n) ((rev n).trans (target n n))
      = (target n n).permCongr (rev n) := by
    rw [Equiv.permCongr_def, relPerm, Equiv.trans_assoc]
  rw [hpc, Equiv.Perm.sign_permCongr, sign_rev]
  have hblank : blank ((rev n).trans (target n n)) = rev n (blank (target n n)) := by
    unfold blank
    rw [Equiv.symm_trans, rev_symm]
    rfl
  rw [hblank, cellParity_rev, cellParity_sq]

/-- The 180°-rotated target lies in the orbit of the target. -/
theorem rev_trans_target_mem_orbit (hn : 3 ≤ n) [NeZero (n * n)] :
    (rev n).trans (target n n) ∈ orbit (target n n) := by
  classical
  rw [orbit]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rev_trans_target_reachable hn⟩

/-- **Extremal lower bound (step 5).**  Some board in the orbit of the target has Manhattan
distance at least `n³ − 3n²`. -/
theorem exists_orbit_D_ge (hn : 3 ≤ n) [NeZero (n * n)] :
    ∃ B ∈ orbit (target n n), (n : ℤ) ^ 3 ≤ (D B : ℤ) + 3 * (n : ℤ) ^ 2 :=
  ⟨(rev n).trans (target n n), rev_trans_target_mem_orbit hn, D_rev_lower⟩

end Zhong
