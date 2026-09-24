import Zhong.Alternating
import Zhong.Expectation
/-
Copyright (c) 2026 The Zhong formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhong formalisation contributors
-/

/-!
# Uniform marginals of the orbit (step 4 of Proposition 9)

This file proves `UniformMarginals (target n n)`, the combinatorial input to step 4 of
Proposition 9.  The proof uses only the transitivity of the closed-walk group `H` on
`Cell \ {p₀}` (`sameOrbit_transitive`), not the full classification `H = alternatingGroup`.

The walk permutations `W = {permOf p₀ σ}` map bijectively onto the orbit `O` of the target
board.  The closed-walk group acts freely on `W` by left multiplication, and its orbits are
exactly the level sets of the blank position `g ↦ g⁻¹ p₀`; there are `n²` of them, each of
size `|H|`.  Within a fixed level set the positions of a given tile run over `Cell \ {p₀}`
with constant multiplicity, so the number of boards with a fixed tile in a fixed cell is
independent of the cell.  Summing over the `n²` cells then gives `UniformMarginals`.
-/

namespace Zhong

open Equiv

variable {n m : ℕ}

/-- The finite set of cell permutations induced by operation sequences starting with the
blank at `p`. -/
noncomputable def walkSet (p : Cell n m) : Finset (Equiv.Perm (Cell n m)) := by
  classical
  exact Finset.univ.filter (fun g => ∃ σ : List Dir, permOf p σ = g)

@[simp] theorem mem_walkSet {p : Cell n m} {g : Equiv.Perm (Cell n m)} :
    g ∈ walkSet p ↔ ∃ σ : List Dir, permOf p σ = g := by
  classical
  simp [walkSet]

/-- Left multiplication by an element of the closed-walk group preserves `walkSet`. -/
theorem mul_mem_walkSet {p : Cell n m} {h : Equiv.Perm (Cell n m)}
    (hh : h ∈ closedGroup p) {g : Equiv.Perm (Cell n m)} (hg : g ∈ walkSet p) :
    h * g ∈ walkSet p := by
  let K : Subgroup (Equiv.Perm (Cell n m)) :=
    { carrier := {h | ∀ g, g ∈ walkSet p → h * g ∈ walkSet p}
      one_mem' := by intro g hg; simpa using hg
      mul_mem' := by
        intro a b ha hb g hg
        have hbg : b * g ∈ walkSet p := hb g hg
        simpa only [mul_assoc] using ha (b * g) hbg
      inv_mem' := by
        intro a ha g hg
        have hsub : (walkSet p).image (fun x => a * x) ⊆ walkSet p := by
          intro y hy
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
          exact ha x hx
        have hcard : ((walkSet p).image (fun x => a * x)).card = (walkSet p).card :=
          Finset.card_image_of_injective _ (fun x y hxy => mul_left_cancel hxy)
        have heq : (walkSet p).image (fun x => a * x) = walkSet p :=
          Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
        have hmem : g ∈ (walkSet p).image (fun x => a * x) := by rw [heq]; exact hg
        obtain ⟨x, hx, hx'⟩ := Finset.mem_image.mp hmem
        have hxg : a⁻¹ * g = x := by rw [← hx', inv_mul_cancel_left]
        rw [hxg]; exact hx }
  have hgen : ∀ x ∈ {g : Equiv.Perm (Cell n m) | ∃ σ : List Dir,
      IsClosedWalk p σ ∧ permOf p σ = g}, x ∈ K := by
    rintro x ⟨σ, hσ, rfl⟩ g hg
    obtain ⟨τ, rfl⟩ := mem_walkSet.mp hg
    rw [mem_walkSet]
    exact ⟨σ ++ τ, permOf_append_of_trace_eq p σ τ hσ⟩
  exact (Subgroup.closure_le (K := K)).mpr hgen hh g hg

/-- The closed-walk group is contained in the walk set. -/
theorem closedGroup_le_walkSet (p : Cell n m) :
    (closedGroup p : Set (Equiv.Perm (Cell n m))) ⊆ walkSet p := by
  intro h hh
  have := mul_mem_walkSet hh (mem_walkSet.mpr ⟨[], rfl⟩)
  simpa using this

/-- The closed-walk group is exactly the part of the walk set fixing the base point. -/
theorem mem_closedGroup_iff_walkSet {p : Cell n m} {h : Equiv.Perm (Cell n m)} :
    h ∈ closedGroup p ↔ h ∈ walkSet p ∧ h p = p := by
  constructor
  · intro hh
    exact ⟨closedGroup_le_walkSet p hh, closedGroup_apply_self hh⟩
  · rintro ⟨hw, hp⟩
    obtain ⟨σ, rfl⟩ := mem_walkSet.mp hw
    have hsymm : (permOf p σ).symm p = p := (Equiv.symm_apply_eq (permOf p σ)).mpr hp.symm
    rw [permOf_symm_apply] at hsymm
    exact mem_closedGroup hsymm

/-- The orbit of the target board is the image of the walk set under `g ↦ g.trans BT`. -/
theorem orbit_eq_image [NeZero (n * n)] :
    orbit (target n n) = (walkSet (blank (target n n))).image (fun g => g.trans (target n n)) := by
  classical
  ext B'
  simp only [orbit, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨permOf (blank (target n n)) σ, mem_walkSet.mpr ⟨σ, rfl⟩, ?_⟩
    rw [← hσ, actSeq_eq_permOf]
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨σ, rfl⟩ := mem_walkSet.mp hg
    exact ⟨σ, actSeq_eq_permOf (target n n) σ⟩

/-- The walk set and the orbit have the same cardinality. -/
theorem walkSet_card_eq_orbit_card [NeZero (n * n)] :
    (walkSet (blank (target n n))).card = (orbit (target n n)).card := by
  rw [orbit_eq_image]
  exact (Finset.card_image_of_injective (walkSet (blank (target n n)))
    (fun g g' h => by
      have := congrArg (fun e : Board n n => e.trans (target n n).symm) h
      simpa [Equiv.trans_assoc] using this)).symm

/-- The closed-walk group as a finite set. -/
noncomputable def closedGroupFinset (p : Cell n m) : Finset (Equiv.Perm (Cell n m)) := by
  classical
  exact Finset.univ.filter (fun h => h ∈ closedGroup p)

@[simp] theorem mem_closedGroupFinset {p : Cell n m} {h : Equiv.Perm (Cell n m)} :
    h ∈ closedGroupFinset p ↔ h ∈ closedGroup p := by
  classical
  simp [closedGroupFinset]

/-- The elements of the closed-walk group sending `y` to `z`. -/
noncomputable def hFiber (p y z : Cell n m) : Finset (Equiv.Perm (Cell n m)) :=
  (closedGroupFinset p).filter (fun h => h y = z)

@[simp] theorem mem_hFiber {p y z : Cell n m} {h : Equiv.Perm (Cell n m)} :
    h ∈ hFiber p y z ↔ h ∈ closedGroup p ∧ h y = z := by
  classical
  simp [hFiber]

/-- The number of elements of `H` sending `y` to `z` is independent of `y` (as long as
`y, y', z` differ from the base point). -/
theorem hFiber_card_eq {p y y' z : Cell n m} (_hy : y ≠ p) (_hy' : y' ≠ p)
    (_hz : z ≠ p) (h : SameOrbit p y' y) :
    (hFiber p y z).card = (hFiber p y' z).card := by
  obtain ⟨k, hk, hky'⟩ := h
  refine Finset.card_bij (fun a _ => a * k) ?_ ?_ ?_
  · intro a ha
    rw [mem_hFiber] at ha ⊢
    exact ⟨Subgroup.mul_mem _ ha.1 hk, by rw [Equiv.Perm.mul_apply, hky', ha.2]⟩
  · intro a _ b _ hab
    exact mul_right_cancel hab
  · intro b hb
    rw [mem_hFiber] at hb
    refine ⟨b * k⁻¹, ?_, ?_⟩
    · rw [mem_hFiber]
      refine ⟨Subgroup.mul_mem _ hb.1 (Subgroup.inv_mem _ hk), ?_⟩
      have hk_inv : k⁻¹ y = y' := (Equiv.symm_apply_eq k).mpr hky'.symm
      rw [Equiv.Perm.mul_apply, hk_inv, hb.2]
    · rw [mul_assoc, inv_mul_cancel, mul_one]

/-- Any word can be replaced by an applicable one with the same induced permutation and
trace. -/
theorem exists_applicable_permOf (p : Cell n m) (σ : List Dir) :
    ∃ σ' : List Dir, ApplicableFrom p σ' ∧ permOf p σ' = permOf p σ ∧
      trace p σ' = trace p σ := by
  induction σ generalizing p with
  | nil => exact ⟨[], trivial, rfl, rfl⟩
  | cons δ σ ih =>
      cases h : neighbor? p δ with
      | none =>
          obtain ⟨σ', hσ'app, hσ'perm, hσ'trace⟩ := ih p
          exact ⟨σ', hσ'app, by rw [permOf_cons_of_neighbor?_eq_none h, hσ'perm],
            by rw [trace_cons_of_neighbor?_eq_none h, hσ'trace]⟩
      | some c' =>
          obtain ⟨σ', hσ'app, hσ'perm, hσ'trace⟩ := ih c'
          exact ⟨δ :: σ', ⟨c', h, hσ'app⟩,
            by simp only [permOf_cons_of_neighbor? h, hσ'perm],
            by simp only [trace_cons_of_neighbor? h, hσ'trace]⟩

/-- The walk set is generated by *applicable* words. -/
theorem mem_walkSet' {p : Cell n m} {g : Equiv.Perm (Cell n m)} :
    g ∈ walkSet p ↔ ∃ σ : List Dir, ApplicableFrom p σ ∧ permOf p σ = g := by
  constructor
  · intro hg
    obtain ⟨σ, rfl⟩ := mem_walkSet.mp hg
    obtain ⟨σ', hσ', hperm, _⟩ := exists_applicable_permOf p σ
    exact ⟨σ', hσ', hperm⟩
  · rintro ⟨σ, _, rfl⟩
    exact mem_walkSet.mpr ⟨σ, rfl⟩

/-- The permutations of the walk set whose blank ends at `q`. -/
noncomputable def walkFiber (p q : Cell n m) : Finset (Equiv.Perm (Cell n m)) :=
  (walkSet p).filter (fun g => g⁻¹ p = q)

@[simp] theorem mem_walkFiber {p q : Cell n m} {g : Equiv.Perm (Cell n m)} :
    g ∈ walkFiber p q ↔ g ∈ walkSet p ∧ g⁻¹ p = q := by
  classical
  simp [walkFiber]

/-- The quotient `g * gq⁻¹` of two walk permutations with the same blank endpoint is again
a walk permutation. -/
theorem mul_inv_mem_walkSet {p q : Cell n m} {g gq : Equiv.Perm (Cell n m)}
    (hg : g ∈ walkFiber p q) (hgq : gq ∈ walkFiber p q) :
    g * gq⁻¹ ∈ walkSet p := by
  obtain ⟨σ, hσapp, rfl⟩ := mem_walkSet'.mp (mem_walkFiber.mp hg).1
  obtain ⟨τ, hτapp, hτ⟩ := mem_walkSet'.mp (mem_walkFiber.mp hgq).1
  rw [← hτ]
  have htσ : trace p σ = q := by
    rw [← permOf_symm_apply p σ]
    exact (mem_walkFiber.mp hg).2
  have htτ : trace p τ = q := by
    rw [← permOf_symm_apply p τ, hτ]
    exact (mem_walkFiber.mp hgq).2
  rw [mem_walkSet']
  refine ⟨σ ++ invWord τ, ?_, ?_⟩
  · rw [applicableFrom_append]
    refine ⟨hσapp, ?_⟩
    rw [htσ]
    have hh : ApplicableFrom (trace p τ) (invWord τ) := applicableFrom_invWord hτapp
    rw [htτ] at hh
    exact hh
  · rw [permOf_append, htσ, ← htτ, permOf_invWord hτapp]

/-- The quotient `g * gq⁻¹` fixes the base point. -/
theorem mul_inv_apply_self {p q : Cell n m} {g gq : Equiv.Perm (Cell n m)}
    (hg : g ∈ walkFiber p q) (hgq : gq ∈ walkFiber p q) :
    (g * gq⁻¹) p = p := by
  rw [Equiv.Perm.mul_apply, (mem_walkFiber.mp hgq).2]
  have hgq_eq : g q = p := by
    have h := congrArg g (mem_walkFiber.mp hg).2
    rw [show g (g⁻¹ p) = p from Equiv.apply_symm_apply g p] at h
    exact h.symm
  rw [hgq_eq]

/-- There is an applicable word from any cell to any other cell. -/
theorem exists_word_to (p q : Cell n m) :
    ∃ σ : List Dir, ApplicableFrom p σ ∧ trace p σ = q := by
  let base : Cell n m :=
    (⟨0, by have := p.1.isLt; omega⟩, ⟨0, by have := p.2.isLt; omega⟩)
  have h1 : ApplicableFrom base (pathWord p.1.val p.2.val) :=
    applicableFrom_pathWord p.1.val p.2.val 0 (by omega) (by omega)
  have h1t : trace base (pathWord p.1.val p.2.val) = p := by
    rw [trace_pathWord p.1.val p.2.val 0 (by omega) (by omega)]
    ext <;> simp
  have h2 : ApplicableFrom base (pathWord q.1.val q.2.val) :=
    applicableFrom_pathWord q.1.val q.2.val 0 (by omega) (by omega)
  have h2t : trace base (pathWord q.1.val q.2.val) = q := by
    rw [trace_pathWord q.1.val q.2.val 0 (by omega) (by omega)]
    ext <;> simp
  have hback_trace : trace p (invWord (pathWord p.1.val p.2.val)) = base := by
    have := trace_invWord h1
    rw [h1t] at this
    exact this
  have hback_app : ApplicableFrom p (invWord (pathWord p.1.val p.2.val)) := by
    have := applicableFrom_invWord h1
    rw [h1t] at this
    exact this
  refine ⟨invWord (pathWord p.1.val p.2.val) ++ pathWord q.1.val q.2.val, ?_, ?_⟩
  · rw [applicableFrom_append]
    exact ⟨hback_app, by rw [hback_trace]; exact h2⟩
  · rw [trace_append, hback_trace, h2t]

/-- Every walk fiber is nonempty. -/
theorem walkFiber_nonempty (p q : Cell n m) : (walkFiber p q).Nonempty := by
  obtain ⟨σ, hσapp, hσt⟩ := exists_word_to p q
  refine ⟨permOf p σ, ?_⟩
  rw [mem_walkFiber]
  refine ⟨mem_walkSet.mpr ⟨σ, rfl⟩, ?_⟩
  change (permOf p σ).symm p = q
  rw [permOf_symm_apply, hσt]

/-- A chosen representative of each walk fiber. -/
noncomputable def walkRep (p q : Cell n m) : Equiv.Perm (Cell n m) :=
  (walkFiber_nonempty p q).choose

theorem walkRep_mem (p q : Cell n m) : walkRep p q ∈ walkFiber p q :=
  (walkFiber_nonempty p q).choose_spec

/-- The walk set is the disjoint union of its fibers. -/
theorem walkSet_eq_biUnion (p : Cell n m) :
    walkSet p = Finset.univ.biUnion (walkFiber p) := by
  classical
  ext g
  simp only [mem_walkFiber, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · intro hg; exact ⟨g⁻¹ p, hg, rfl⟩
  · rintro ⟨q, hg, _⟩; exact hg

/-- Splitting a filtered walk set over the blank endpoint. -/
theorem filter_walkSet_card (p c z : Cell n m) :
    ((walkSet p).filter (fun g => g c = z)).card =
      ∑ q : Cell n m, ((walkFiber p q).filter (fun g => g c = z)).card := by
  classical
  rw [walkSet_eq_biUnion, Finset.filter_biUnion]
  rw [Finset.card_biUnion (t := fun q => (walkFiber p q).filter (fun g => g c = z)) (by
    intro a _ b _ hne
    change Disjoint ((walkFiber p a).filter (fun g => g c = z))
      ((walkFiber p b).filter (fun g => g c = z))
    rw [Finset.disjoint_left]
    intro g hg hg'
    rw [Finset.mem_filter, mem_walkFiber] at hg hg'
    exact hne (hg.1.2.symm.trans hg'.1.2))]

/-- On a walk fiber the number of elements sending `c` to `z` is the `H`-fiber count. -/
theorem walkFiber_filter_card_eq {p q c z : Cell n m} {gq : Equiv.Perm (Cell n m)}
    (hgq : gq ∈ walkFiber p q) :
    ((walkFiber p q).filter (fun g => g c = z)).card = (hFiber p (gq c) z).card := by
  refine Finset.card_bij (fun g _ => g * gq⁻¹) ?_ ?_ ?_
  · intro g hg
    rw [Finset.mem_filter] at hg
    rw [mem_hFiber]
    refine ⟨?_, ?_⟩
    · rw [mem_closedGroup_iff_walkSet]
      exact ⟨mul_inv_mem_walkSet hg.1 hgq, mul_inv_apply_self hg.1 hgq⟩
    · rw [Equiv.Perm.mul_apply,
        show gq⁻¹ (gq c) = c from Equiv.symm_apply_apply gq c, hg.2]
  · intro a _ b _ hab
    exact mul_right_cancel hab
  · intro h hh
    rw [mem_hFiber] at hh
    refine ⟨h * gq, ?_, ?_⟩
    · rw [Finset.mem_filter, mem_walkFiber]
      refine ⟨⟨mul_mem_walkSet hh.1 (mem_walkFiber.mp hgq).1, ?_⟩, ?_⟩
      · rw [mul_inv_rev, Equiv.Perm.mul_apply,
          closedGroup_apply_self (Subgroup.inv_mem _ hh.1), (mem_walkFiber.mp hgq).2]
      · rw [Equiv.Perm.mul_apply, hh.2]
    · rw [mul_assoc, mul_inv_cancel, mul_one]

/-! ### The tile-count and uniform marginals -/

/-- The number of walk permutations sending the cell `c` to the target position of tile `i`. -/
noncomputable def tileCount [NeZero (n * n)] (i : Fin (n * n)) (c : Cell n n) : ℕ :=
  ((walkSet (blank (target n n))).filter (fun g => g c = (target n n).symm i)).card

/-- Splitting the tile-count over the blank endpoint. -/
theorem tileCount_eq_sum [NeZero (n * n)] (i : Fin (n * n)) (c : Cell n n) :
    tileCount i c = ∑ q : Cell n n,
      (hFiber (blank (target n n)) (walkRep (blank (target n n)) q c)
        ((target n n).symm i)).card := by
  unfold tileCount
  rw [filter_walkSet_card]
  exact Finset.sum_congr rfl (fun q _ =>
    walkFiber_filter_card_eq (walkRep_mem (blank (target n n)) q))

/-- The tile-count is independent of the cell (for a non-blank tile). -/
theorem tileCount_indep [NeZero (n * n)] (hn : 1 < n) (i : Fin (n * n))
    (hpi : (target n n).symm i ≠ blank (target n n)) (c c' : Cell n n) :
    tileCount i c = tileCount i c' := by
  let p := blank (target n n)
  let z := (target n n).symm i
  have hz : z ≠ p := hpi
  have hterm : ∀ (c q : Cell n n),
      (hFiber p (walkRep p q c) z).card = if q = c then 0 else (hFiber p z z).card := by
    intro c q
    by_cases hq : q = c
    · subst hq
      have hself : walkRep p q q = p := by
        have hmem := (mem_walkFiber.mp (walkRep_mem p q)).2
        have h2 := congrArg (walkRep p q) hmem
        rw [show (walkRep p q) ((walkRep p q)⁻¹ p) = p from
          Equiv.apply_symm_apply (walkRep p q) p] at h2
        exact h2.symm
      rw [hself, if_pos rfl, Finset.card_eq_zero, hFiber, Finset.filter_eq_empty_iff]
      intro h hh hp
      rw [mem_closedGroupFinset] at hh
      exact hz (by rw [← hp, closedGroup_apply_self hh])
    · rw [if_neg hq]
      have hy : walkRep p q c ≠ p := by
        intro hc
        apply hq
        have hmem := (mem_walkFiber.mp (walkRep_mem p q)).2
        have h2 := congrArg (walkRep p q) hmem
        rw [show (walkRep p q) ((walkRep p q)⁻¹ p) = p from
          Equiv.apply_symm_apply (walkRep p q) p] at h2
        exact (Equiv.injective (walkRep p q) (by rw [hc]; exact h2)).symm
      exact hFiber_card_eq hy hz hz (sameOrbit_transitive hn hn p z (walkRep p q c) hz hy)
  have hval : ∀ c, tileCount i c = ((n * n) - 1) * (hFiber p z z).card := by
    intro c
    rw [tileCount_eq_sum, Finset.sum_congr rfl (fun q _ => hterm c q)]
    rw [← Finset.add_sum_erase (Finset.univ)
      (fun q => if q = c then 0 else (hFiber p z z).card) (Finset.mem_univ c)]
    rw [if_pos rfl, zero_add,
      Finset.sum_congr rfl (fun q hq => if_neg (Finset.ne_of_mem_erase hq)),
      Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.erase c).card = (n * n) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ c)]
      simp
    rw [hcard]
    rfl
  rw [hval c, hval c']

/-- Summing the tile-count over all cells counts the walk set. -/
theorem sum_tileCount [NeZero (n * n)] (i : Fin (n * n)) :
    ∑ c : Cell n n, tileCount i c = (walkSet (blank (target n n))).card := by
  classical
  unfold tileCount
  rw [Finset.card_eq_sum_card_fiberwise (s := walkSet (blank (target n n)))
    (t := Finset.univ) (f := fun g => g⁻¹ ((target n n).symm i)) (by simp)]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  congr 1
  exact Finset.filter_congr (fun g _ => Iff.trans eq_comm (Equiv.symm_apply_eq g).symm)

/-- The orbit filter for tile `i` at cell `c` has the tile-count cardinality. -/
theorem orbit_filter_card_eq_tileCount [NeZero (n * n)] (i : Fin (n * n)) (c : Cell n n) :
    ((orbit (target n n)).filter (fun B' => posOf B' i = c)).card = tileCount i c := by
  rw [tileCount]
  symm
  refine Finset.card_bij (fun g _ => g.trans (target n n)) ?_ ?_ ?_
  · intro g hg
    rw [Finset.mem_filter] at hg ⊢
    refine ⟨?_, ?_⟩
    · rw [orbit_eq_image]
      exact Finset.mem_image.mpr ⟨g, hg.1, rfl⟩
    · rw [posOf, Equiv.symm_trans_apply, ← hg.2, Equiv.symm_apply_apply]
  · intro a _ b _ hab
    have := congrArg (fun e : Board n n => e.trans (target n n).symm) hab
    simpa [Equiv.trans_assoc] using this
  · intro B' hB'
    rw [Finset.mem_filter, orbit_eq_image] at hB'
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hB'.1
    refine ⟨g, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨hg, ?_⟩
    have h2 := hB'.2
    rw [posOf, Equiv.symm_trans_apply] at h2
    have h3 := congrArg g h2
    rw [Equiv.apply_symm_apply] at h3
    exact h3.symm

/-- **Uniform marginals of the target orbit** (step 4 of Proposition 9). -/
theorem uniformMarginals_target (hn : 1 < n) [NeZero (n * n)] :
    UniformMarginals (target n n) := by
  intro i hi c
  have hi0 : i ≠ 0 := by simpa [tileSet] using hi
  have hpi : (target n n).symm i ≠ blank (target n n) := by
    intro h
    apply hi0
    have h' : i = 0 := by
      have := congrArg (target n n) h
      simpa [blank] using this
    exact h'
  rw [orbit_filter_card_eq_tileCount, ← walkSet_card_eq_orbit_card]
  have hsum := sum_tileCount (n := n) i
  have hsum2 : ∑ c' : Cell n n, tileCount i c' = (n * n) * tileCount i c := by
    rw [Finset.sum_congr rfl (fun c' _ => tileCount_indep hn i hpi c' c)]
    simp
  rw [hsum2] at hsum
  rw [mul_comm]
  exact hsum

/-- **Step 4 of Proposition 9.**  The average Manhattan distance over the orbit of the
target is `(2/3)n³ + O(n)`. -/
theorem avgD_target_bounds (hn : 1 < n) [NeZero (n * n)] :
    (2 / 3 : ℚ) * (n : ℚ) ^ 3 - (8 / 3) * (n : ℚ) + 2 ≤ avgD (target n n) ∧
      avgD (target n n) ≤ (2 / 3 : ℚ) * (n : ℚ) ^ 3 - (2 / 3) * (n : ℚ) :=
  avgD_bounds (uniformMarginals_target hn)

end Zhong
