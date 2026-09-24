import Zhong.Basic
/-
Copyright (c) 2026 The Zhong formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhong formalisation contributors
-/

/-!
# The cell permutation induced by an operation sequence

Acting a list of moves on a board only permutes the *cells*: for every operation sequence
`σ` and board `B` there is a permutation `π` of the cells with `B σ = B ∘ π`.  This file
develops that permutation explicitly, together with the trace of the blank.

* `trace p σ` is the cell reached by the blank starting at `p` under `σ`.
* `permOf p σ` is the induced cell permutation.
* `actSeq_eq_permOf` : `actSeq B σ = (permOf (blank B) σ).trans B`.
* `blank_actSeq` : `blank (actSeq B σ) = trace (blank B) σ`.
* `permOf_append` / `trace_append` : composition.

These are the ingredients used to realise explicit 3-cycles of cells (the converse direction
of Proposition 3) and, later, the jump and shift primitives of Section 3.
-/

namespace Zhong

open Equiv

variable {n m : ℕ}

/-- The cell occupied by the blank after acting the sequence `σ`, starting with the blank
at `p`. -/
def trace (p : Cell n m) : List Dir → Cell n m
  | [] => p
  | δ :: σ =>
      match neighbor? p δ with
      | some c' => trace c' σ
      | none => trace p σ

/-- The permutation of cells induced by the sequence `σ` when the blank starts at `p`. -/
def permOf (p : Cell n m) : List Dir → Equiv.Perm (Cell n m)
  | [] => 1
  | δ :: σ =>
      match neighbor? p δ with
      | some c' => Equiv.swap p c' * permOf c' σ
      | none => permOf p σ

@[simp] theorem trace_nil (p : Cell n m) : trace p [] = p := rfl

@[simp] theorem permOf_nil (p : Cell n m) : permOf p [] = 1 := rfl

theorem trace_cons_of_neighbor? {p c' : Cell n m} {δ : Dir} {σ : List Dir}
    (h : neighbor? p δ = some c') : trace p (δ :: σ) = trace c' σ := by
  simp only [trace, h]

theorem trace_cons_of_neighbor?_eq_none {p : Cell n m} {δ : Dir} {σ : List Dir}
    (h : neighbor? p δ = none) : trace p (δ :: σ) = trace p σ := by
  simp only [trace, h]

theorem permOf_cons_of_neighbor? {p c' : Cell n m} {δ : Dir} {σ : List Dir}
    (h : neighbor? p δ = some c') : permOf p (δ :: σ) = Equiv.swap p c' * permOf c' σ := by
  simp only [permOf, h]

theorem permOf_cons_of_neighbor?_eq_none {p : Cell n m} {δ : Dir} {σ : List Dir}
    (h : neighbor? p δ = none) : permOf p (δ :: σ) = permOf p σ := by
  simp only [permOf, h]

/-- Acting a sequence is precomposition with the induced cell permutation. -/
theorem actSeq_eq_permOf [NeZero (n * m)] (B : Board n m) (σ : List Dir) :
    actSeq B σ = (permOf (blank B) σ).trans B := by
  induction σ generalizing B with
  | nil => rfl
  | cons δ σ ih =>
      rw [actSeq_cons, ih (act B δ)]
      cases h : neighbor? (blank B) δ with
      | none =>
          rw [act_of_neighbor?_eq_none h, permOf_cons_of_neighbor?_eq_none h]
      | some c' =>
          rw [blank_act_of_neighbor? h, act_of_neighbor? h, permOf_cons_of_neighbor? h]
          rw [← Equiv.trans_assoc]
          rfl

/-- The blank after a sequence is its trace. -/
theorem blank_actSeq [NeZero (n * m)] (B : Board n m) (σ : List Dir) :
    blank (actSeq B σ) = trace (blank B) σ := by
  induction σ generalizing B with
  | nil => rfl
  | cons δ σ ih =>
      rw [actSeq_cons, ih (act B δ)]
      cases h : neighbor? (blank B) δ with
      | none => rw [act_of_neighbor?_eq_none h, trace_cons_of_neighbor?_eq_none h]
      | some c' => rw [blank_act_of_neighbor? h, trace_cons_of_neighbor? h]

/-- The inverse of the induced permutation sends the starting cell to the trace. -/
theorem permOf_symm_apply (p : Cell n m) (σ : List Dir) :
    (permOf p σ).symm p = trace p σ := by
  induction σ generalizing p with
  | nil => rfl
  | cons δ σ ih =>
      cases h : neighbor? p δ with
      | none =>
          rw [permOf_cons_of_neighbor?_eq_none h, trace_cons_of_neighbor?_eq_none h]
          exact ih p
      | some c' =>
          rw [permOf_cons_of_neighbor? h, trace_cons_of_neighbor? h]
          have hsymm : (Equiv.swap p c' * permOf c' σ).symm p = (permOf c' σ).symm c' := by
            rw [Equiv.symm_apply_eq]
            change p = (Equiv.swap p c' * permOf c' σ) ((permOf c' σ).symm c')
            simp
          rw [hsymm]
          exact ih c'

theorem trace_append (p : Cell n m) (σ₁ σ₂ : List Dir) :
    trace p (σ₁ ++ σ₂) = trace (trace p σ₁) σ₂ := by
  induction σ₁ generalizing p with
  | nil => simp
  | cons δ σ₁ ih =>
      cases h : neighbor? p δ with
      | none => rw [List.cons_append, trace_cons_of_neighbor?_eq_none h,
                    trace_cons_of_neighbor?_eq_none h]; exact ih p
      | some c' => rw [List.cons_append, trace_cons_of_neighbor? h,
                       trace_cons_of_neighbor? h]; exact ih c'

theorem permOf_append (p : Cell n m) (σ₁ σ₂ : List Dir) :
    permOf p (σ₁ ++ σ₂) = permOf p σ₁ * permOf (trace p σ₁) σ₂ := by
  induction σ₁ generalizing p with
  | nil => simp
  | cons δ σ₁ ih =>
      cases h : neighbor? p δ with
      | none => rw [List.cons_append, permOf_cons_of_neighbor?_eq_none h,
                    trace_cons_of_neighbor?_eq_none h,
                    permOf_cons_of_neighbor?_eq_none h]; exact ih p
      | some c' =>
          rw [List.cons_append, permOf_cons_of_neighbor? h, trace_cons_of_neighbor? h,
              permOf_cons_of_neighbor? h, ih c', mul_assoc]

/-- Cell permutations induced by closed walks (sequences returning the blank to its start)
compose: this makes the closed-walk permutations a subgroup of the permutations fixing `p`. -/
theorem permOf_append_of_trace_eq (p : Cell n m) (σ₁ σ₂ : List Dir)
    (h : trace p σ₁ = p) : permOf p (σ₁ ++ σ₂) = permOf p σ₁ * permOf p σ₂ := by
  rw [permOf_append, h]

/-! ### The inverse operation sequence

The inverse `invWord σ` of an operation sequence undoes it: it reverses the order and
replaces every move by the opposite move. -/

/-- The opposite move. -/
def invDir : Dir → Dir
  | Dir.U => Dir.D
  | Dir.D => Dir.U
  | Dir.L => Dir.R
  | Dir.R => Dir.L

@[simp] theorem invDir_U : invDir Dir.U = Dir.D := rfl
@[simp] theorem invDir_D : invDir Dir.D = Dir.U := rfl
@[simp] theorem invDir_L : invDir Dir.L = Dir.R := rfl
@[simp] theorem invDir_R : invDir Dir.R = Dir.L := rfl

/-- The inverse of an operation sequence. -/
def invWord : List Dir → List Dir
  | [] => []
  | δ :: σ => invWord σ ++ [invDir δ]

@[simp] theorem invWord_nil : invWord ([] : List Dir) = [] := rfl

theorem invWord_cons (δ : Dir) (σ : List Dir) :
    invWord (δ :: σ) = invWord σ ++ [invDir δ] := rfl

/-- The inverse of a one-element sequence. -/
@[simp] theorem invWord_singleton (δ : Dir) : invWord [δ] = [invDir δ] := by
  simp [invWord]

/-- Undoing a move: the opposite move is applicable and returns the blank. -/
theorem neighbor?_invDir {c c' : Cell n m} {δ : Dir} (h : neighbor? c δ = some c') :
    neighbor? c' (invDir δ) = some c := by
  cases δ <;>
    simp only [invDir, neighbor?] at h ⊢ <;>
    split_ifs at h ⊢ <;>
    simp_all [Prod.ext_iff, Fin.ext_iff] <;>
    omega

/-- A sequence is applicable starting from the cell `p`. -/
def ApplicableFrom (p : Cell n m) : List Dir → Prop
  | [] => True
  | δ :: σ => ∃ c', neighbor? p δ = some c' ∧ ApplicableFrom c' σ

@[simp] theorem applicableFrom_nil (p : Cell n m) : ApplicableFrom p [] := trivial

theorem applicableFrom_cons_of_neighbor? {p c' : Cell n m} {δ : Dir} {σ : List Dir}
    (h : neighbor? p δ = some c') : ApplicableFrom p (δ :: σ) ↔ ApplicableFrom c' σ := by
  change (∃ d, neighbor? p δ = some d ∧ ApplicableFrom d σ) ↔ ApplicableFrom c' σ
  constructor
  · rintro ⟨d, hd, hrest⟩
    rw [h] at hd
    have hdc : d = c' := (Option.some.inj hd).symm
    subst hdc
    exact hrest
  · intro hrest; exact ⟨c', h, hrest⟩

theorem applicableFrom_cons_of_neighbor?_eq_none {p : Cell n m} {δ : Dir} {σ : List Dir}
    (h : neighbor? p δ = none) : ¬ ApplicableFrom p (δ :: σ) := by
  intro hc
  change (∃ d, neighbor? p δ = some d ∧ ApplicableFrom d σ) at hc
  obtain ⟨d, hd, _⟩ := hc
  rw [h] at hd
  exact absurd hd (by simp)

/-- Applicability is decidable (recursively on the word). -/
instance decidableApplicableFrom (p : Cell n m) : ∀ σ : List Dir, Decidable (ApplicableFrom p σ)
  | [] => isTrue trivial
  | δ :: σ =>
      match h : neighbor? p δ with
      | none => isFalse (applicableFrom_cons_of_neighbor?_eq_none h)
      | some c' =>
          haveI := decidableApplicableFrom c' σ
          decidable_of_iff' (ApplicableFrom c' σ) (applicableFrom_cons_of_neighbor? h)

/-- Applicability of a concatenation. -/
theorem applicableFrom_append (p : Cell n m) (σ₁ σ₂ : List Dir) :
    ApplicableFrom p (σ₁ ++ σ₂) ↔
      ApplicableFrom p σ₁ ∧ ApplicableFrom (trace p σ₁) σ₂ := by
  induction σ₁ generalizing p with
  | nil => simp
  | cons δ σ₁ ih =>
      cases h : neighbor? p δ with
      | none =>
          have hL : ¬ ApplicableFrom p ((δ :: σ₁) ++ σ₂) := by
            rw [List.cons_append]
            exact applicableFrom_cons_of_neighbor?_eq_none h
          have hR : ¬ (ApplicableFrom p (δ :: σ₁) ∧
              ApplicableFrom (trace p (δ :: σ₁)) σ₂) :=
            fun hx => applicableFrom_cons_of_neighbor?_eq_none h hx.1
          exact ⟨fun hx => absurd hx hL, fun hx => absurd hx hR⟩
      | some c' =>
          rw [List.cons_append]
          simp only [applicableFrom_cons_of_neighbor? h, trace_cons_of_neighbor? h]
          exact ih c'

/-- The set of cells visited by the blank along a sequence. -/
def traceSet (p : Cell n m) : List Dir → Finset (Cell n m)
  | [] => {p}
  | δ :: σ =>
      match neighbor? p δ with
      | some c' => insert p (traceSet c' σ)
      | none => insert p (traceSet p σ)

@[simp] theorem traceSet_nil (p : Cell n m) : traceSet p [] = {p} := rfl

theorem traceSet_cons_of_neighbor? {p c' : Cell n m} {δ : Dir} {σ : List Dir}
    (h : neighbor? p δ = some c') : traceSet p (δ :: σ) = insert p (traceSet c' σ) := by
  simp only [traceSet, h]

theorem traceSet_cons_of_neighbor?_eq_none {p : Cell n m} {δ : Dir} {σ : List Dir}
    (h : neighbor? p δ = none) : traceSet p (δ :: σ) = insert p (traceSet p σ) := by
  simp only [traceSet, h]

/-- The starting cell is always visited. -/
theorem mem_traceSet_self (p : Cell n m) (σ : List Dir) : p ∈ traceSet p σ := by
  induction σ generalizing p with
  | nil => simp
  | cons δ σ ih =>
      cases h : neighbor? p δ with
      | none => rw [traceSet_cons_of_neighbor?_eq_none h]; exact Finset.mem_insert_self _ _
      | some c' => rw [traceSet_cons_of_neighbor? h]; exact Finset.mem_insert_self _ _

theorem traceSet_append (p : Cell n m) (σ₁ σ₂ : List Dir) :
    traceSet p (σ₁ ++ σ₂) = traceSet p σ₁ ∪ traceSet (trace p σ₁) σ₂ := by
  induction σ₁ generalizing p with
  | nil =>
      rw [List.nil_append, trace_nil, traceSet_nil, Finset.singleton_union,
          Finset.insert_eq_self.mpr (mem_traceSet_self p σ₂)]
  | cons δ σ₁ ih =>
      cases h : neighbor? p δ with
      | none =>
          rw [List.cons_append, traceSet_cons_of_neighbor?_eq_none h,
              traceSet_cons_of_neighbor?_eq_none h, trace_cons_of_neighbor?_eq_none h,
              ih p, Finset.insert_union]
      | some c' =>
          rw [List.cons_append, traceSet_cons_of_neighbor? h, traceSet_cons_of_neighbor? h,
              trace_cons_of_neighbor? h, ih c', Finset.insert_union]

/-- The induced permutation fixes every cell that the blank never visits. -/
theorem permOf_apply_of_not_mem_traceSet {p x : Cell n m} {σ : List Dir}
    (h : x ∉ traceSet p σ) : permOf p σ x = x := by
  induction σ generalizing p with
  | nil => simpa using h
  | cons δ σ ih =>
      cases hδ : neighbor? p δ with
      | none =>
          rw [permOf_cons_of_neighbor?_eq_none hδ]
          exact ih (by rw [traceSet_cons_of_neighbor?_eq_none hδ] at h; exact fun hx => h (Finset.mem_insert_of_mem hx))
      | some c' =>
          rw [permOf_cons_of_neighbor? hδ]
          rw [traceSet_cons_of_neighbor? hδ] at h
          have hx_not : x ∉ traceSet c' σ := fun hx => h (Finset.mem_insert_of_mem hx)
          have hxp : x ≠ p := fun hx => h (hx.symm ▸ Finset.mem_insert_self p _)
          have hxc' : x ≠ c' := fun hx => hx_not (hx.symm ▸ mem_traceSet_self c' σ)
          change swap p c' (permOf c' σ x) = x
          rw [ih hx_not, Equiv.swap_apply_of_ne_of_ne hxp hxc']

/-- Following a sequence and then its inverse returns the blank to the start. -/
theorem trace_invWord {p : Cell n m} {σ : List Dir} (h : ApplicableFrom p σ) :
    trace (trace p σ) (invWord σ) = p := by
  induction σ generalizing p with
  | nil => simp
  | cons δ σ ih =>
      obtain ⟨c', hc', hσ⟩ := h
      rw [trace_cons_of_neighbor? hc', invWord_cons, trace_append, ih hσ,
          trace_cons_of_neighbor? (neighbor?_invDir hc')]
      rfl

/-- The inverse word is applicable from the endpoint of an applicable word. -/
theorem applicableFrom_invWord {p : Cell n m} {σ : List Dir} (h : ApplicableFrom p σ) :
    ApplicableFrom (trace p σ) (invWord σ) := by
  induction σ generalizing p with
  | nil => simp
  | cons δ σ ih =>
      obtain ⟨c', hc', hσ⟩ := h
      rw [trace_cons_of_neighbor? hc', invWord_cons, applicableFrom_append]
      refine ⟨?_, ?_⟩
      · exact ih hσ
      · rw [trace_invWord hσ,
          applicableFrom_cons_of_neighbor? (neighbor?_invDir hc')]
        exact trivial

/-- The inverse word induces the inverse cell permutation. -/
theorem permOf_invWord {p : Cell n m} {σ : List Dir} (h : ApplicableFrom p σ) :
    permOf (trace p σ) (invWord σ) = (permOf p σ)⁻¹ := by
  have hmain : permOf p (σ ++ invWord σ) = 1 := by
    induction σ generalizing p with
    | nil => simp
    | cons δ σ ih =>
        obtain ⟨c', hc', hσ⟩ := h
        rw [List.cons_append, invWord_cons, ← List.append_assoc, permOf_cons_of_neighbor? hc',
            permOf_append, ih hσ, trace_append, trace_invWord hσ, permOf_cons_of_neighbor?
              (neighbor?_invDir hc'), permOf_nil, one_mul, mul_one, Equiv.swap_comm c' p,
            Equiv.swap_mul_self]
  rw [permOf_append] at hmain
  exact eq_inv_of_mul_eq_one_right hmain

end Zhong
