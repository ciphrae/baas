/-
Copyright (c) 2026 The Zhong formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhong formalisation contributors
-/
import Zhong.Alternating

/-!
# Gluing alternating groups along a grid

This file proves the group-theoretic core of the converse of Proposition 3 of
Zhong (2023): the closed-walk group `closedGroup p` contains the alternating group on
the cells other than `p`.

The main ingredients are

* `star_le_alternating`: if a subgroup contains all the three-cycles
  `swap a b * swap b t` through a common edge `(a, b)`, then it contains the full
  alternating group;
* `altOn_union_le`: alternating groups on two finite sets whose intersection has at
  least two points generate the alternating group on the union;
* the geometric induction covering the board by overlapping `3 x 3` blocks.

-/

namespace Zhong

open Equiv

section

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem star_pair {α : Type*} [DecidableEq α] {a b y z : α} (hay : a ≠ y) (hby : b ≠ y) :
    (Equiv.swap a b * Equiv.swap b y) * (Equiv.swap a b * Equiv.swap b z)
      = Equiv.swap a y * Equiv.swap b z := by
  have h1 : Equiv.swap a b * Equiv.swap b y * Equiv.swap a b = Equiv.swap a y := by
    have := Equiv.swap_apply_apply (Equiv.swap a b) b y
    rw [Equiv.swap_inv, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hay) (Ne.symm hby)] at this
    exact this.symm
  calc (Equiv.swap a b * Equiv.swap b y) * (Equiv.swap a b * Equiv.swap b z)
      = (Equiv.swap a b * Equiv.swap b y * Equiv.swap a b) * Equiv.swap b z := by group
    _ = Equiv.swap a y * Equiv.swap b z := by rw [h1]

theorem star_triple {α : Type*} [DecidableEq α] {a b x y z : α}
    (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y) (haz : a ≠ z)
    (hbx : b ≠ x) (hby : b ≠ y) (hbz : b ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (Equiv.swap a b * Equiv.swap b y) * (Equiv.swap a b * Equiv.swap b z) *
    (Equiv.swap a b * Equiv.swap b x) * (Equiv.swap a b * Equiv.swap b y) *
    (Equiv.swap a b * Equiv.swap b z) = Equiv.swap y z * Equiv.swap z x := by
  set d := Equiv.swap a y * Equiv.swap b z with hd
  have hcomm : Equiv.swap a y * Equiv.swap b z = Equiv.swap b z * Equiv.swap a y := by
    have h := Equiv.swap_apply_apply (Equiv.swap b z) a y
    rw [Equiv.swap_apply_of_ne_of_ne hab haz,
        Equiv.swap_apply_of_ne_of_ne hby.symm hyz, Equiv.swap_inv] at h
    nth_rewrite 1 [h]
    rw [show (Equiv.swap b z * Equiv.swap a y * Equiv.swap b z) * Equiv.swap b z
          = (Equiv.swap b z * Equiv.swap a y) * (Equiv.swap b z * Equiv.swap b z) by group,
        Equiv.swap_mul_self, mul_one]
  have hd_inv : d⁻¹ = d := by
    rw [hd, mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv, hcomm]
  have hda : d a = y := by
    rw [hd]
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hab haz, Equiv.swap_apply_left]
  have hdb : d b = z := by
    rw [hd]
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne haz.symm hyz.symm]
  have hdx : d x = x := by
    rw [hd]
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hbx.symm hxz,
        Equiv.swap_apply_of_ne_of_ne hax.symm hxy]
  have hpair_yz : (Equiv.swap a b * Equiv.swap b y) * (Equiv.swap a b * Equiv.swap b z)
      = d := by
    rw [hd]; exact star_pair hay hby
  have hconj1 : d * Equiv.swap a b * d = Equiv.swap y z := by
    have h := Equiv.swap_apply_apply d a b
    rw [hd_inv, hda, hdb] at h
    exact h.symm
  have hconj2 : d * Equiv.swap b x * d = Equiv.swap z x := by
    have h := Equiv.swap_apply_apply d b x
    rw [hd_inv, hdb, hdx] at h
    exact h.symm
  have hsplit : d * (Equiv.swap a b * Equiv.swap b x) * d
      = (d * Equiv.swap a b * d) * (d * Equiv.swap b x * d) := by
    have hdd : d * d = 1 := by
      nth_rewrite 2 [← hd_inv]; exact mul_inv_cancel d
    calc d * (Equiv.swap a b * Equiv.swap b x) * d
        = d * Equiv.swap a b * (d * d) * Equiv.swap b x * d := by
          rw [hdd, mul_one]; group
      _ = (d * Equiv.swap a b * d) * (d * Equiv.swap b x * d) := by group
  calc (Equiv.swap a b * Equiv.swap b y) * (Equiv.swap a b * Equiv.swap b z) *
      (Equiv.swap a b * Equiv.swap b x) * (Equiv.swap a b * Equiv.swap b y) *
      (Equiv.swap a b * Equiv.swap b z)
      = (Equiv.swap a b * Equiv.swap b y) * (Equiv.swap a b * Equiv.swap b z) *
        (Equiv.swap a b * Equiv.swap b x) *
        ((Equiv.swap a b * Equiv.swap b y) * (Equiv.swap a b * Equiv.swap b z)) := by
          group
    _ = d * (Equiv.swap a b * Equiv.swap b x) * d := by rw [hpair_yz]
    _ = (d * Equiv.swap a b * d) * (d * Equiv.swap b x * d) := hsplit
    _ = Equiv.swap y z * Equiv.swap z x := by rw [hconj1, hconj2]

theorem swap_three_eq {α : Type*} [DecidableEq α] {x y z : α}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Equiv.swap y z * Equiv.swap z x = Equiv.swap x y * Equiv.swap y z := by
  ext w
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_def]
  by_cases hwx : w = x <;> by_cases hwy : w = y <;> by_cases hwz : w = z <;>
    simp_all [eq_comm]

theorem swap_q_a {α : Type*} [DecidableEq α] {a p q : α} (hap : a ≠ p) (haq : a ≠ q)
    (hpq : p ≠ q) :
    Equiv.swap q a * Equiv.swap a p = Equiv.swap a p * Equiv.swap p q := by
  ext w
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_def]
  by_cases hwa : w = a <;> by_cases hwp : w = p <;> by_cases hwq : w = q <;>
    simp_all [eq_comm]

/-- Rotating a three-cycle written as a product of two swaps. -/
theorem swap_three_rotate {α : Type*} [DecidableEq α] {p q r : α}
    (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) :
    Equiv.swap p q * Equiv.swap q r = Equiv.swap q r * Equiv.swap r p := by
  ext w
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_def]
  by_cases hwp : w = p <;> by_cases hwq : w = q <;> by_cases hwr : w = r <;>
    simp_all [eq_comm]

theorem star_conj_b {α : Type*} [DecidableEq α] {a b p q : α} (hab : a ≠ b)
    (hap : a ≠ p) (haq : a ≠ q) (hbp : b ≠ p) (hbq : b ≠ q) (hpq : p ≠ q) :
    (Equiv.swap a b * Equiv.swap b p) * (Equiv.swap a b * Equiv.swap b q) *
      (Equiv.swap a b * Equiv.swap b p)⁻¹ = Equiv.swap b p * Equiv.swap p q := by
  have hpa : p ≠ a := hap.symm
  have hpb : p ≠ b := hbp.symm
  have h1 : (Equiv.swap a b * Equiv.swap b p) a = b := by
    show Equiv.swap a b (Equiv.swap b p a) = b
    rw [Equiv.swap_apply_of_ne_of_ne hab hap, Equiv.swap_apply_left]
  have h2 : (Equiv.swap a b * Equiv.swap b p) b = p := by
    show Equiv.swap a b (Equiv.swap b p b) = p
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hap.symm hbp.symm]
  have h3 : (Equiv.swap a b * Equiv.swap b p) q = q := by
    show Equiv.swap a b (Equiv.swap b p q) = q
    rw [Equiv.swap_apply_of_ne_of_ne hbq.symm hpq.symm,
        Equiv.swap_apply_of_ne_of_ne haq.symm hbq.symm]
  rw [show (Equiv.swap a b * Equiv.swap b p) * (Equiv.swap a b * Equiv.swap b q) *
        (Equiv.swap a b * Equiv.swap b p)⁻¹
      = ((Equiv.swap a b * Equiv.swap b p) * Equiv.swap a b *
          (Equiv.swap a b * Equiv.swap b p)⁻¹) *
        ((Equiv.swap a b * Equiv.swap b p) * Equiv.swap b q *
          (Equiv.swap a b * Equiv.swap b p)⁻¹) by group]
  rw [← Equiv.swap_apply_apply, ← Equiv.swap_apply_apply]
  rw [h1, h2, h3]

theorem star_conj_a {α : Type*} [DecidableEq α] {a b p q : α} (hab : a ≠ b)
    (hap : a ≠ p) (haq : a ≠ q) (hbp : b ≠ p) (hbq : b ≠ q) (hpq : p ≠ q) :
    (Equiv.swap a b * Equiv.swap b q)⁻¹ * (Equiv.swap a b * Equiv.swap b p) *
      (Equiv.swap a b * Equiv.swap b q) = Equiv.swap a p * Equiv.swap p q := by
  set f := (Equiv.swap a b * Equiv.swap b q)⁻¹ with hf
  have hf_inv : f⁻¹ = Equiv.swap a b * Equiv.swap b q := by rw [hf, inv_inv]
  have hfa : f a = q := by
    rw [hf, mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]
    show Equiv.swap b q (Equiv.swap a b a) = q
    rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
  have hfb : f b = a := by
    rw [hf, mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]
    show Equiv.swap b q (Equiv.swap a b b) = a
    rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hab haq]
  have hfp : f p = p := by
    rw [hf, mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]
    show Equiv.swap b q (Equiv.swap a b p) = p
    rw [Equiv.swap_apply_of_ne_of_ne hap.symm hbp.symm,
        Equiv.swap_apply_of_ne_of_ne hbp.symm hpq]
  calc (Equiv.swap a b * Equiv.swap b q)⁻¹ * (Equiv.swap a b * Equiv.swap b p) *
        (Equiv.swap a b * Equiv.swap b q)
      = f * (Equiv.swap a b * Equiv.swap b p) * f⁻¹ := by rw [← hf, ← hf_inv]
    _ = (f * Equiv.swap a b * f⁻¹) * (f * Equiv.swap b p * f⁻¹) := by group
    _ = Equiv.swap (f a) (f b) * Equiv.swap (f b) (f p) := by
          rw [← Equiv.swap_apply_apply, ← Equiv.swap_apply_apply]
    _ = Equiv.swap q a * Equiv.swap a p := by rw [hfa, hfb, hfp]
    _ = Equiv.swap a p * Equiv.swap p q := swap_q_a hap haq hpq

theorem star_inv_pair {α : Type*} [DecidableEq α] {a b p : α} (hab : a ≠ b)
    (hap : a ≠ p) (hbp : b ≠ p) :
    Equiv.swap a p * Equiv.swap p b = (Equiv.swap a b * Equiv.swap b p)⁻¹ := by
  rw [mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]
  ext w
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_def]
  by_cases hwa : w = a <;> by_cases hwb : w = b <;> by_cases hwp : w = p <;>
    simp_all [eq_comm]


theorem star_le_alternating {β : Type*} [Fintype β] [DecidableEq β] {a b : β} (hab : a ≠ b)
    {G : Subgroup (Equiv.Perm β)}
    (h : ∀ t : β, t ≠ b → Equiv.swap a b * Equiv.swap b t ∈ G) :
    alternatingGroup β ≤ G := by
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
  rintro σ hσ
  by_cases ha : a ∈ σ.support
  · set p := σ a with hp
    set q := σ (σ a) with hq
    have hσeq : σ = Equiv.swap a p * Equiv.swap p q := by
      simpa [hp, hq] using (hσ.eq_swap_mul_swap_iff_mem_support.mpr ha)
    have hsupp : σ.support = {a, p, q} := by
      rw [hp, hq]; exact hσ.support_eq_iff_mem_support.mpr ha
    have hnodup : [a, σ a, σ (σ a)].Nodup := hσ.nodup_iff_mem_support.mpr ha
    have ha_not : a ∉ [σ a, σ (σ a)] := (List.nodup_cons.mp hnodup).1
    have htail : [σ a, σ (σ a)].Nodup := (List.nodup_cons.mp hnodup).2
    have ha_ne_p : a ≠ p := by rw [hp]; exact List.ne_of_not_mem_cons (List.nodup_cons.mp hnodup).1
    have ha_ne_q : a ≠ q := by
      rw [hq]
      exact List.ne_of_not_mem_cons
        (List.ne_and_not_mem_of_not_mem_cons (List.nodup_cons.mp hnodup).1).2
    have hp_ne_q : p ≠ q := by
      rw [hp, hq]; simpa using (List.nodup_cons.mp htail).1
    have hp_supp : p ∈ σ.support := by rw [hsupp]; simp
    have hq_supp : q ∈ σ.support := by rw [hsupp]; simp
    by_cases hb : b ∈ σ.support
    · have hbpq : b = p ∨ b = q := by
        have hmem : b ∈ ({a, p, q} : Finset β) := by rw [← hsupp]; exact hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        tauto
      rcases hbpq with hbp | hbq
      · subst hbp
        rw [hσeq]
        exact h q hp_ne_q.symm
      · subst hbq
        rw [hσeq, star_inv_pair hab ha_ne_p hp_ne_q.symm]
        exact G.inv_mem (h p hp_ne_q)
    · have hp_ne_b : p ≠ b := fun hh => hb (hh ▸ hp_supp)
      have hq_ne_b : q ≠ b := fun hh => hb (hh ▸ hq_supp)
      rw [hσeq]
      rw [← star_conj_a hab ha_ne_p ha_ne_q hp_ne_b.symm hq_ne_b.symm hp_ne_q]
      exact G.mul_mem (G.mul_mem (G.inv_mem (h q hq_ne_b)) (h p hp_ne_b)) (h q hq_ne_b)
  · by_cases hb : b ∈ σ.support
    · set p := σ b with hp
      set q := σ (σ b) with hq
      have hσeq : σ = Equiv.swap b p * Equiv.swap p q := by
        simpa [hp, hq] using (hσ.eq_swap_mul_swap_iff_mem_support.mpr hb)
      have hsupp : σ.support = {b, p, q} := by
        rw [hp, hq]; exact hσ.support_eq_iff_mem_support.mpr hb
      have hnodup : [b, σ b, σ (σ b)].Nodup := hσ.nodup_iff_mem_support.mpr hb
      have hb_not : b ∉ [σ b, σ (σ b)] := (List.nodup_cons.mp hnodup).1
      have htail : [σ b, σ (σ b)].Nodup := (List.nodup_cons.mp hnodup).2
      have hb_ne_p : b ≠ p := by rw [hp]; exact List.ne_of_not_mem_cons (List.nodup_cons.mp hnodup).1
      have hb_ne_q : b ≠ q := by
        rw [hq]
        exact List.ne_of_not_mem_cons
          (List.ne_and_not_mem_of_not_mem_cons (List.nodup_cons.mp hnodup).1).2
      have hp_ne_q : p ≠ q := by
        rw [hp, hq]; simpa using (List.nodup_cons.mp htail).1
      have hp_supp : p ∈ σ.support := by rw [hsupp]; simp
      have hq_supp : q ∈ σ.support := by rw [hsupp]; simp
      have ha_ne_p : a ≠ p := fun hh => ha (hh ▸ hp_supp)
      have ha_ne_q : a ≠ q := fun hh => ha (hh ▸ hq_supp)
      rw [hσeq]
      rw [← star_conj_b hab ha_ne_p ha_ne_q hb_ne_p hb_ne_q hp_ne_q]
      exact G.mul_mem (G.mul_mem (h p hb_ne_p.symm) (h q hb_ne_q.symm)) (G.inv_mem (h p hb_ne_p.symm))
    · obtain ⟨u, hu⟩ : σ.support.Nonempty :=
        Finset.card_pos.mp (by rw [hσ.card_support]; norm_num)
      set x := u with hx
      set y := σ u with hy
      set z := σ (σ u) with hz
      have hσeq : σ = Equiv.swap x y * Equiv.swap y z := by
        simpa [hx, hy, hz] using (hσ.eq_swap_mul_swap_iff_mem_support.mpr hu)
      have hsupp : σ.support = {x, y, z} := by
        rw [hx, hy, hz]; exact hσ.support_eq_iff_mem_support.mpr hu
      have hnodup : [u, σ u, σ (σ u)].Nodup := hσ.nodup_iff_mem_support.mpr hu
      have hu_not : u ∉ [σ u, σ (σ u)] := (List.nodup_cons.mp hnodup).1
      have htail : [σ u, σ (σ u)].Nodup := (List.nodup_cons.mp hnodup).2
      have hxy : x ≠ y := by rw [hx, hy]; exact List.ne_of_not_mem_cons (List.nodup_cons.mp hnodup).1
      have hxz : x ≠ z := by
        rw [hx, hz]
        exact List.ne_of_not_mem_cons
          (List.ne_and_not_mem_of_not_mem_cons (List.nodup_cons.mp hnodup).1).2
      have hyz : y ≠ z := by
        rw [hy, hz]; simpa using (List.nodup_cons.mp htail).1
      have hx_supp : x ∈ σ.support := by rw [hsupp]; simp
      have hy_supp : y ∈ σ.support := by rw [hsupp]; simp
      have hz_supp : z ∈ σ.support := by rw [hsupp]; simp
      have hx_ne_b : b ≠ x := fun hh => hb (hh ▸ hx_supp)
      have hy_ne_b : b ≠ y := fun hh => hb (hh ▸ hy_supp)
      have hz_ne_b : b ≠ z := fun hh => hb (hh ▸ hz_supp)
      have hx_ne_a : a ≠ x := fun hh => ha (hh ▸ hx_supp)
      have hy_ne_a : a ≠ y := fun hh => ha (hh ▸ hy_supp)
      have hz_ne_a : a ≠ z := fun hh => ha (hh ▸ hz_supp)
      rw [hσeq, ← swap_three_eq hxy hxz hyz,
        ← star_triple hab hx_ne_a hy_ne_a hz_ne_a hx_ne_b hy_ne_b hz_ne_b hxy hxz hyz]
      exact G.mul_mem (G.mul_mem (G.mul_mem (G.mul_mem (h y hy_ne_b.symm) (h z hz_ne_b.symm))
        (h x hx_ne_b.symm)) (h y hy_ne_b.symm)) (h z hz_ne_b.symm)

theorem threeCycle_mem_altOn {α : Type*} [DecidableEq α] {U : Finset α} {a b t : α}
    (ha : a ∈ U) (hb : b ∈ U) (ht : t ∈ U) (hab : a ≠ b) (hbt : b ≠ t) :
    Equiv.swap a b * Equiv.swap b t ∈ altOn U := by
  rcases eq_or_ne a t with rfl | hat
  · rw [Equiv.swap_comm b a, Equiv.swap_mul_self]
    exact Subgroup.one_mem _
  rw [altOn]
  refine Subgroup.mem_map.mpr ⟨Equiv.swap (⟨a, ha⟩ : ↥U) ⟨b, hb⟩ *
      Equiv.swap (⟨b, hb⟩ : ↥U) ⟨t, ht⟩, ?_, ?_⟩
  · apply Equiv.Perm.IsThreeCycle.mem_alternatingGroup
    rw [Equiv.swap_comm (⟨a, ha⟩ : ↥U) ⟨b, hb⟩]
    refine Equiv.Perm.isThreeCycle_swap_mul_swap_same ?_ ?_ ?_
    · exact fun h => hab.symm (congrArg Subtype.val h)
    · exact fun h => hbt (congrArg Subtype.val h)
    · exact fun h => hat (congrArg Subtype.val h)
  · rw [map_mul, Equiv.Perm.ofSubtype_swap_eq, Equiv.Perm.ofSubtype_swap_eq]

/-- Two alternating groups on finite sets with at least two common points generate the
alternating group on the union. -/
theorem altOn_union_le {α : Type*} [DecidableEq α] {U V : Finset α}
    {G : Subgroup (Equiv.Perm α)} (hU : altOn U ≤ G) (hV : altOn V ≤ G)
    {a b : α} (haU : a ∈ U) (hbU : b ∈ U) (haV : a ∈ V) (hbV : b ∈ V) (hab : a ≠ b) :
    altOn (U ∪ V) ≤ G := by
  let a' : ↥(U ∪ V) := ⟨a, Finset.mem_union_left _ haU⟩
  let b' : ↥(U ∪ V) := ⟨b, Finset.mem_union_left _ hbU⟩
  have hab' : a' ≠ b' := fun h => hab (congrArg Subtype.val h)
  have key : ∀ t : ↥(U ∪ V), t ≠ b' →
      Equiv.swap a' b' * Equiv.swap b' t ∈ G.comap (Equiv.Perm.ofSubtype (p := (· ∈ U ∪ V))) := by
    intro t ht
    rw [Subgroup.mem_comap, map_mul, Equiv.Perm.ofSubtype_swap_eq, Equiv.Perm.ofSubtype_swap_eq]
    rcases Finset.mem_union.mp t.2 with htU | htV
    · exact hU (threeCycle_mem_altOn haU hbU htU hab (fun h => ht (Subtype.ext h.symm)))
    · exact hV (threeCycle_mem_altOn haV hbV htV hab (fun h => ht (Subtype.ext h.symm)))
  rw [altOn]
  rw [Subgroup.map_le_iff_le_comap]
  exact star_le_alternating hab' key


section Grid
variable {n m : ℕ} [NeZero (n * m)]

set_option linter.unusedSectionVars false

def win (i : Fin n) (j : Fin m) (hi : i.1 + 1 < n) (hj : j.1 + 2 < m) : Fin 5 → Cell n m :=
  ![((⟨i.1 + 1, hi⟩ : Fin n), (⟨j.1 + 1, by omega⟩ : Fin m)),
    ((⟨i.1 + 1, hi⟩ : Fin n), j),
    (i, (⟨j.1 + 1, by omega⟩ : Fin m)),
    (i, (⟨j.1 + 2, hj⟩ : Fin m)),
    ((⟨i.1 + 1, hi⟩ : Fin n), (⟨j.1 + 2, hj⟩ : Fin m))]

def window (i : Fin n) (j : Fin m) (hi : i.1 + 1 < n) (hj : j.1 + 2 < m) : Finset (Cell n m) :=
  Finset.univ.image (win i j hi hj)

omit [NeZero (n * m)] in
theorem win_injective (i : Fin n) (j : Fin m) (hi : i.1 + 1 < n) (hj : j.1 + 2 < m) :
    Function.Injective (win i j hi hj) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [win, Fin.ext_iff, Prod.ext_iff]

theorem window_altOn_le (i : Fin n) (j : Fin m) (hi : i.1 + 1 < n) (hj : j.1 + 2 < m) :
    altOn (window i j hi hj) ≤
      closedGroup (((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) : Cell n m) := by
  let A : Cell n m := ((⟨i.1 + 1, hi⟩ : Fin n), (⟨j.1 + 1, by omega⟩ : Fin m))
  let B : Cell n m := ((⟨i.1 + 1, hi⟩ : Fin n), j)
  let C : Cell n m := (i, (⟨j.1 + 1, by omega⟩ : Fin m))
  have hAB : A ≠ B := by
    intro h; simp only [A, B, Prod.mk.injEq, Fin.ext_iff] at h; omega
  have hBC : B ≠ C := by
    intro h; simp only [B, C, Prod.mk.injEq, Fin.ext_iff] at h; omega
  have hAC : A ≠ C := by
    intro h; simp only [A, C, Prod.mk.injEq, Fin.ext_iff] at h; omega
  refine alt_five_le (win_injective i j hi hj) ?_ ?_
  · rw [show win i j hi hj 0 = A from rfl, show win i j hi hj 1 = B from rfl,
        show win i j hi hj 2 = C from rfl]
    rw [swap_three_rotate hAB hBC hAC, swap_three_rotate hBC hAC.symm hAB.symm]
    rw [← squareCycle_eq i j hi (by omega)]
    exact squareCycle_mem i j hi (by omega)
  · let B' : Cell n m := (i, (⟨j.1 + 2, hj⟩ : Fin m))
    let C' : Cell n m := ((⟨i.1 + 1, hi⟩ : Fin n), (⟨j.1 + 2, hj⟩ : Fin m))
    have hAB' : A ≠ B' := by
      intro h; simp only [A, B', Prod.mk.injEq, Fin.ext_iff] at h; omega
    have hB'C' : B' ≠ C' := by
      intro h; simp only [B', C', Prod.mk.injEq, Fin.ext_iff] at h; omega
    have hAC' : A ≠ C' := by
      intro h; simp only [A, C', Prod.mk.injEq, Fin.ext_iff] at h; omega
    rw [show win i j hi hj 0 = A from rfl, show win i j hi hj 3 = B' from rfl,
        show win i j hi hj 4 = C' from rfl]
    rw [swap_three_rotate hAB' hB'C' hAC']
    rw [← squareCycle_eq i (⟨j.1 + 1, by omega⟩ : Fin m) hi (by omega)]
    exact squareCycle_mem i (⟨j.1 + 1, by omega⟩ : Fin m) hi (by omega)

theorem mem_window_iff (i : Fin n) (j : Fin m) (hi : i.1 + 1 < n) (hj : j.1 + 2 < m)
    (c : Cell n m) :
    c ∈ window i j hi hj ↔
      c = win i j hi hj 0 ∨ c = win i j hi hj 1 ∨ c = win i j hi hj 2 ∨
      c = win i j hi hj 3 ∨ c = win i j hi hj 4 := by
  rw [window, Finset.mem_image]
  constructor
  · rintro ⟨k, -, rfl⟩
    fin_cases k <;> simp
  · rintro (h | h | h | h | h) <;> subst h <;> exact ⟨_, Finset.mem_univ _, rfl⟩

@[simp] theorem win_zero (i : Fin n) (j : Fin m) (hi : i.1 + 1 < n) (hj : j.1 + 2 < m) :
    win i j hi hj 0 = ((⟨i.1 + 1, hi⟩ : Fin n), (⟨j.1 + 1, by omega⟩ : Fin m)) := rfl

@[simp] theorem win_one (i : Fin n) (j : Fin m) (hi : i.1 + 1 < n) (hj : j.1 + 2 < m) :
    win i j hi hj 1 = ((⟨i.1 + 1, hi⟩ : Fin n), j) := rfl

@[simp] theorem win_two (i : Fin n) (j : Fin m) (hi : i.1 + 1 < n) (hj : j.1 + 2 < m) :
    win i j hi hj 2 = (i, (⟨j.1 + 1, by omega⟩ : Fin m)) := rfl

@[simp] theorem win_three (i : Fin n) (j : Fin m) (hi : i.1 + 1 < n) (hj : j.1 + 2 < m) :
    win i j hi hj 3 = (i, (⟨j.1 + 2, hj⟩ : Fin m)) := rfl

@[simp] theorem win_four (i : Fin n) (j : Fin m) (hi : i.1 + 1 < n) (hj : j.1 + 2 < m) :
    win i j hi hj 4 = ((⟨i.1 + 1, hi⟩ : Fin n), (⟨j.1 + 2, hj⟩ : Fin m)) := rfl

/-- The first `t` windows of row `i`. -/
def winsPrefix (i : Fin n) (hi : i.1 + 1 < n) (t : ℕ) : Finset (Cell n m) :=
  (Finset.range t).biUnion
    (fun j => if h : j + 2 < m then window i ⟨j, by omega⟩ hi h else ∅)

/-- All windows of row `i`. -/
def Wins (i : Fin n) (hi : i.1 + 1 < n) : Finset (Cell n m) := winsPrefix i hi (m - 2)

theorem window_subset_winsPrefix (i : Fin n) (hi : i.1 + 1 < n) {j t : ℕ} (hjt : j < t)
    (hj : j + 2 < m) : window i ⟨j, by omega⟩ hi hj ⊆ winsPrefix i hi t := by
  intro c hc
  rw [winsPrefix, Finset.mem_biUnion]
  exact ⟨j, Finset.mem_range.mpr hjt, by rw [dif_pos hj]; exact hc⟩

theorem winsPrefix_succ_of (i : Fin n) (hi : i.1 + 1 < n) (t : ℕ) (h : t + 2 < m) :
    winsPrefix i hi (t + 1) = winsPrefix i hi t ∪ window i ⟨t, by omega⟩ hi h := by
  rw [winsPrefix, Finset.range_add_one, Finset.biUnion_insert, dif_pos h, winsPrefix,
    Finset.union_comm]

theorem winsPrefix_succ_of_not (i : Fin n) (hi : i.1 + 1 < n) (t : ℕ) (h : ¬ t + 2 < m) :
    winsPrefix (m := m) i hi (t + 1) = winsPrefix (m := m) i hi t := by
  rw [winsPrefix, Finset.range_add_one, Finset.biUnion_insert, dif_neg h, Finset.empty_union,
    winsPrefix]

/-- A cell in row `i + 1` lies in the union of the windows of row `i`. -/
theorem mem_Wins_row_succ (hm : 3 ≤ m) (i : Fin n) (hi : i.1 + 1 < n) (y : Fin m) :
    ((⟨i.1 + 1, hi⟩ : Fin n), y) ∈ Wins i hi := by
  rw [Wins]
  by_cases hy : 2 ≤ y.val
  · have hjlt : y.val - 2 < m - 2 := by omega
    have hj2 : y.val - 2 + 2 < m := by omega
    refine window_subset_winsPrefix i hi (j := y.val - 2) (t := m - 2) hjlt hj2 ?_
    rw [mem_window_iff]
    refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    rw [win_four]
    ext <;> simp only [Fin.val_mk] <;> omega
  · have hyv : y.val ≤ 1 := by omega
    have hjlt : 0 < m - 2 := by omega
    have hj2 : 0 + 2 < m := by omega
    refine window_subset_winsPrefix i hi (j := 0) (t := m - 2) hjlt hj2 ?_
    rw [mem_window_iff]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hyv with h0 | h1
    · refine Or.inr (Or.inl ?_)
      rw [win_one]
      ext <;> simp only [Fin.val_mk] <;> omega
    · refine Or.inl ?_
      rw [win_zero]
      ext <;> simp only [Fin.val_mk] <;> omega

/-- A cell `(i, y)` with `y ≠ 0` lies in the union of the windows of row `i`. -/
theorem mem_Wins_row (hm : 3 ≤ m) (i : Fin n) (hi : i.1 + 1 < n) {y : Fin m}
    (hy : 0 < y.val) : (i, y) ∈ Wins i hi := by
  rw [Wins]
  by_cases hyl : y.val = m - 1
  · have hjlt : m - 3 < m - 2 := by omega
    have hj2 : m - 3 + 2 < m := by omega
    refine window_subset_winsPrefix i hi (j := m - 3) (t := m - 2) hjlt hj2 ?_
    rw [mem_window_iff]
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    rw [win_three]
    ext <;> simp only [Fin.val_mk] <;> omega
  · have hylt : y.val - 1 < m - 2 := by omega
    have hj2 : y.val - 1 + 2 < m := by omega
    refine window_subset_winsPrefix i hi (j := y.val - 1) (t := m - 2) hylt hj2 ?_
    rw [mem_window_iff]
    refine Or.inr (Or.inr (Or.inl ?_))
    rw [win_two]
    ext <;> simp only [Fin.val_mk] <;> omega

/-- The base cell `(0, 0)` of the board. -/
abbrev p0 : Cell n m :=
  (⟨0, Nat.pos_of_ne_zero (left_ne_zero_of_mul (NeZero.ne (n * m)))⟩,
   ⟨0, Nat.pos_of_ne_zero (right_ne_zero_of_mul (NeZero.ne (n * m)))⟩)

/-- Each prefix of the windows of a row generates at most the closed-walk group. -/
theorem altOn_winsPrefix_le (i : Fin n) (hi : i.1 + 1 < n) :
    ∀ t, altOn (winsPrefix i hi t) ≤ closedGroup (p0 : Cell n m) := by
  intro t
  induction t with
  | zero =>
      rw [winsPrefix, Finset.range_zero, Finset.biUnion_empty]
      intro g hg
      rw [altOn, Subgroup.mem_map] at hg
      obtain ⟨σ, -, rfl⟩ := hg
      haveI : Subsingleton (Equiv.Perm ↥(∅ : Finset (Cell n m))) := inferInstance
      rw [Subsingleton.elim σ 1, map_one]
      exact Subgroup.one_mem _
  | succ t ih =>
      by_cases h : t + 2 < m
      · rw [winsPrefix_succ_of i hi t h]
        rcases Nat.eq_zero_or_pos t with ht | ht
        · subst ht
          rw [winsPrefix, Finset.range_zero, Finset.biUnion_empty, Finset.empty_union]
          exact window_altOn_le i ⟨0, by omega⟩ hi h
        · refine altOn_union_le (G := closedGroup (p0 : Cell n m))
            (U := winsPrefix i hi t) (V := window i ⟨t, by omega⟩ hi h)
            (a := ((⟨i.1 + 1, hi⟩ : Fin n), (⟨t, by omega⟩ : Fin m)))
            (b := ((⟨i.1 + 1, hi⟩ : Fin n), (⟨t + 1, by omega⟩ : Fin m)))
            ih (window_altOn_le i ⟨t, by omega⟩ hi h) ?_ ?_ ?_ ?_ ?_
          · have ht1 : t - 1 + 2 < m := by omega
            have hlt : t - 1 < t := by omega
            exact window_subset_winsPrefix i hi hlt ht1
              (by rw [mem_window_iff]; left; rw [win_zero]; ext <;> simp only [Fin.val_mk] <;> omega)
          · have ht1 : t - 1 + 2 < m := by omega
            have hlt : t - 1 < t := by omega
            exact window_subset_winsPrefix i hi hlt ht1
              (by rw [mem_window_iff]; refine Or.inr (Or.inr (Or.inr (Or.inr ?_)));
                  rw [win_four]; ext <;> simp only [Fin.val_mk] <;> omega)
          · rw [mem_window_iff]; exact Or.inr (Or.inl (by rw [win_one]))
          · rw [mem_window_iff]; exact Or.inl (by rw [win_zero])
          · intro hh
            have := congrArg (fun x : Cell n m => x.2.val) hh
            simp only [Fin.val_mk] at this
            omega
      · rw [winsPrefix_succ_of_not i hi t h]; exact ih

/-- The cells in rows `≤ k`, except the base point. -/
def Region (k : ℕ) : Finset (Cell n m) :=
  (Finset.univ.filter (fun c : Cell n m => c.1.val ≤ k)) \ {p0}

theorem altOn_region_one_le (hm : 3 ≤ m) (hn : 2 ≤ n) :
    altOn (Region (n := n) (m := m) 1) ≤ closedGroup (p0 : Cell n m) := by
  have hi : (⟨0, by omega⟩ : Fin n).val + 1 < n := by simp; omega
  have hsub : Region (n := n) (m := m) 1 ⊆ Wins (⟨0, by omega⟩ : Fin n) hi := by
    intro c hc
    rw [Region, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_singleton] at hc
    obtain ⟨⟨-, hle⟩, hne⟩ := hc
    rcases (by omega : c.1.val = 0 ∨ c.1.val = 1) with h0 | h1
    · have hc1 : c.1 = (⟨0, by omega⟩ : Fin n) := Fin.ext h0
      have hy : 0 < c.2.val := by
        by_contra hh
        have hc2 : c.2 = (⟨0, by omega⟩ : Fin m) := Fin.ext (by omega)
        exact hne (Prod.ext hc1 hc2)
      have hmem := mem_Wins_row (n := n) (m := m) hm (⟨0, by omega⟩ : Fin n) hi hy
      have hc_eq : c = ((⟨0, by omega⟩ : Fin n), c.2) := Prod.ext hc1 rfl
      rwa [hc_eq]
    · have hc1 : c.1 = (⟨(⟨0, by omega⟩ : Fin n).val + 1, hi⟩ : Fin n) :=
        Fin.ext (by simp only [Fin.val_mk]; omega)
      have hmem := mem_Wins_row_succ (n := n) (m := m) hm (⟨0, by omega⟩ : Fin n) hi c.2
      have hc_eq : c = ((⟨(⟨0, by omega⟩ : Fin n).val + 1, hi⟩ : Fin n), c.2) := Prod.ext hc1 rfl
      rwa [hc_eq]
  exact le_trans (altOn_mono hsub) (altOn_winsPrefix_le (⟨0, by omega⟩ : Fin n) hi (m - 2))

theorem altOn_region_succ_le (hm : 3 ≤ m) (i : Fin n) (hi : i.1 + 1 < n) (hi1 : 1 ≤ i.val)
    (ih : altOn (Region (n := n) (m := m) i.val) ≤ closedGroup (p0 : Cell n m)) :
    altOn (Region (n := n) (m := m) (i.val + 1)) ≤ closedGroup (p0 : Cell n m) := by
  have hwins : altOn (Wins i hi) ≤ closedGroup (p0 : Cell n m) :=
    altOn_winsPrefix_le i hi (m - 2)
  have haReg : (i, (⟨1, by omega⟩ : Fin m)) ∈ Region (n := n) (m := m) i.val := by
    rw [Region, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_singleton]
    refine ⟨⟨Finset.mem_univ _, by simp⟩, ?_⟩
    intro h
    have := congrArg (fun x : Cell n m => x.1.val) h
    simp only [p0, Fin.val_mk] at this
    omega
  have hbReg : (i, (⟨2, by omega⟩ : Fin m)) ∈ Region (n := n) (m := m) i.val := by
    rw [Region, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_singleton]
    refine ⟨⟨Finset.mem_univ _, by simp⟩, ?_⟩
    intro h
    have := congrArg (fun x : Cell n m => x.1.val) h
    simp only [p0, Fin.val_mk] at this
    omega
  have haWin : (i, (⟨1, by omega⟩ : Fin m)) ∈ Wins i hi := mem_Wins_row hm i hi (by simp)
  have hbWin : (i, (⟨2, by omega⟩ : Fin m)) ∈ Wins i hi := mem_Wins_row hm i hi (by simp)
  have hunion : altOn (Region (n := n) (m := m) i.val ∪ Wins i hi) ≤ closedGroup (p0 : Cell n m) :=
    altOn_union_le ih hwins haReg hbReg haWin hbWin (by simp)
  have hsub : Region (n := n) (m := m) (i.val + 1) ⊆ Region (n := n) (m := m) i.val ∪ Wins i hi := by
    intro c hc
    rw [Region, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_singleton] at hc
    obtain ⟨⟨-, hle⟩, hne⟩ := hc
    rw [Finset.mem_union, Region, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_singleton]
    by_cases hlt : c.1.val ≤ i.val
    · exact Or.inl ⟨⟨Finset.mem_univ _, hlt⟩, hne⟩
    · right
      have hc1 : c.1 = (⟨i.val + 1, hi⟩ : Fin n) := Fin.ext (by simp only [Fin.val_mk]; omega)
      have hmem := mem_Wins_row_succ (n := n) (m := m) hm i hi c.2
      have hc_eq : c = ((⟨i.val + 1, hi⟩ : Fin n), c.2) := Prod.ext hc1 rfl
      rwa [hc_eq]
  exact le_trans (altOn_mono hsub) hunion

theorem altOn_region_le (hm : 3 ≤ m) (hn : 2 ≤ n) :
    ∀ k, 1 ≤ k → k ≤ n - 1 → altOn (Region (n := n) (m := m) k) ≤ closedGroup (p0 : Cell n m) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk1 hkn
    rcases (by omega : k = 1 ∨ 2 ≤ k) with hk | hk
    · subst hk
      exact altOn_region_one_le hm hn
    · have hkm1 : 1 ≤ k - 1 := by omega
      have hih : altOn (Region (n := n) (m := m) (k - 1)) ≤ closedGroup (p0 : Cell n m) :=
        ih (k - 1) (by omega) hkm1 (by omega)
      have hstep := altOn_region_succ_le (n := n) (m := m) hm
        (⟨k - 1, by omega⟩ : Fin n) (by simp only [Fin.val_mk]; omega)
        (by simp only [Fin.val_mk]; omega) hih
      rwa [show (⟨k - 1, by omega⟩ : Fin n).val + 1 = k from by simp only [Fin.val_mk]; omega] at hstep

/-- **The converse of Proposition 3 (group form).**  For `m ≥ 3` and `n ≥ 2`, the
closed-walk group at `(0, 0)` contains the alternating group on all the other cells. -/
theorem altOn_compl_p0_le (hm : 3 ≤ m) (hn : 2 ≤ n) :
    altOn ((Finset.univ : Finset (Cell n m)) \ {p0}) ≤ closedGroup (p0 : Cell n m) := by
  have h := altOn_region_le (n := n) (m := m) hm hn (n - 1) (by omega) (by omega)
  refine le_trans (altOn_mono ?_) h
  intro c hc
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hc
  rw [Region, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_singleton]
  exact ⟨⟨Finset.mem_univ _, by have := c.1.isLt; omega⟩, hc.2⟩

/-- **The converse of Proposition 3 (group form) at an arbitrary base point.**  For
`m ≥ 3` and `n ≥ 2`, the closed-walk group at any cell `p` contains the alternating group
on all the other cells. -/
theorem altOn_compl_le_closedGroup (hm : 3 ≤ m) (hn : 2 ≤ n) (p : Cell n m) :
    altOn ((Finset.univ : Finset (Cell n m)) \ {p}) ≤ closedGroup p := by
  let β : List Dir := invWord (pathWord p.1.val p.2.val)
  have hpath_trace : trace (p0 : Cell n m) (pathWord p.1.val p.2.val) = p := by
    rw [trace_pathWord (n := n) (m := m) p.1.val p.2.val 0 (by omega) (by omega)]
    ext <;> simp
  have hpath_app : ApplicableFrom (p0 : Cell n m) (pathWord p.1.val p.2.val) :=
    applicableFrom_pathWord (n := n) (m := m) p.1.val p.2.val 0 (by omega) (by omega)
  have hβ_trace : trace p β = (p0 : Cell n m) := by
    have h := trace_invWord hpath_app
    rw [hpath_trace] at h
    simpa only [β] using h
  have hβ_app : ApplicableFrom p β := by
    have h := applicableFrom_invWord hpath_app
    rw [hpath_trace] at h
    simpa only [β] using h
  let u : Equiv.Perm (Cell n m) := permOf p β
  have hu_inv : (Equiv.symm u) p = (p0 : Cell n m) := by
    dsimp only [u]
    change (permOf p β).symm p = (p0 : Cell n m)
    rw [permOf_symm_apply, hβ_trace]
  have hu_base : u (p0 : Cell n m) = p := by
    rw [← hu_inv]
    exact Equiv.apply_symm_apply u p
  intro g hg
  have hk : u⁻¹ * g * u ∈
      altOn (((Finset.univ : Finset (Cell n m)) \ {p}).map (u⁻¹).toEmbedding) :=
    conj_mem_altOn u⁻¹ hg
  have himg : ((Finset.univ : Finset (Cell n m)) \ {p}).map (u⁻¹).toEmbedding
      = Finset.univ \ {(p0 : Cell n m)} := by
    ext x
    simp only [Finset.mem_map, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_singleton, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨a, ha, rfl⟩
      intro hx
      apply ha
      calc a = u ((Equiv.symm u) a) := (Equiv.apply_symm_apply u a).symm
        _ = u (p0 : Cell n m) := congrArg u hx
        _ = p := hu_base
    · intro hx
      refine ⟨u x, ?_, by simp⟩
      intro h
      apply hx
      calc x = (Equiv.symm u) (u x) := (Equiv.symm_apply_apply u x).symm
        _ = (Equiv.symm u) p := congrArg (Equiv.symm u) h
        _ = (p0 : Cell n m) := hu_inv
  rw [himg] at hk
  have hkH : u⁻¹ * g * u ∈ closedGroup (p0 : Cell n m) := altOn_compl_p0_le hm hn hk
  have hconj := conj_mem_closedGroup hβ_trace hβ_app hkH
  have heq : u * (u⁻¹ * g * u) * u⁻¹ = g := by group
  rwa [heq] at hconj

end Grid

end

end Zhong

