/-
Copyright (c) 2026 The Zhong formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Zhong formalisation contributors
-/
import Zhong.Algorithm.Jump
import Zhong.Algorithm.JumpRow
import Zhong.Algorithm.Orient
import Zhong.Algorithm.Move
import Zhong.Algorithm.Shift

/-!
# Lifting operation sequences to two-row and two-column strips

The explicit words of `Algorithm/Jump.lean` and `Algorithm/JumpRow.lean` are proved on a
`2 × m` board.  The algorithm of Zhong (2023) uses them inside a two-row strip of a larger
board.  This file provides the generic transport principle:

* `swap_apply_injective` : an injective map commutes with transpositions;
* `trace_map_of_neighbor_map` / `permOf_map_apply_of_neighbor_map` : a map that carries
  applicable moves to applicable moves transports the trace and the induced permutation;
* `hStrip` / `vStrip` : the two-row / two-column embeddings;
* the lifted jump `hStrip_jumpWord`, `vStrip_transJumpWord` and the same-row jump
  `hStrip_row0Word`, each with its explicit effect and length;
* `moveToWord` : move the blank to a prescribed cell.

The hypotheses of the generic transport lemma only concern *applicable* moves, so no
"virtual wall" at the boundary of the strip is needed: the words are proved applicable in
the strip, and only the directions that stay inside the strip are ever used.
-/

namespace Zhong

open Equiv

variable {n m : ℕ}

/-! ### Generic transport along an injective map -/

/-- An injective map commutes with transpositions: `swap (ι a) (ι b) (ι z) = ι (swap a b z)`. -/
theorem swap_apply_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    {ι : α → β} (hinj : Function.Injective ι) (a b z : α) :
    Equiv.swap (ι a) (ι b) (ι z) = ι (Equiv.swap a b z) := by
  by_cases hza : z = a
  · subst hza; simp
  · by_cases hzb : z = b
    · subst hzb; simp
    · have h1 : ι z ≠ ι a := fun hh => hza (hinj hh)
      have h2 : ι z ≠ ι b := fun hh => hzb (hinj hh)
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne hza hzb]

/-- Transport of the trace along an injective map carrying applicable moves to applicable
moves. -/
theorem trace_map_of_neighbor_map {n' m' : ℕ} {ι : Cell n' m' → Cell n m} {f : Dir → Dir}
    (hstep : ∀ (c : Cell n' m') (δ : Dir) (c' : Cell n' m'),
      neighbor? c δ = some c' → neighbor? (ι c) (f δ) = some (ι c'))
    (p : Cell n' m') (σ : List Dir) (happ : ApplicableFrom p σ) :
    trace (ι p) (σ.map f) = ι (trace p σ) := by
  induction σ generalizing p with
  | nil => rfl
  | cons δ σ ih =>
      obtain ⟨c', hc', hσ⟩ := happ
      rw [List.map_cons, trace_cons_of_neighbor? hc',
          trace_cons_of_neighbor? (hstep p δ c' hc')]
      exact ih c' hσ

/-- Transport of the action of the induced permutation along an injective map carrying
applicable moves to applicable moves. -/
theorem permOf_map_apply_of_neighbor_map {n' m' : ℕ} {ι : Cell n' m' → Cell n m}
    {f : Dir → Dir} (hinj : Function.Injective ι)
    (hstep : ∀ (c : Cell n' m') (δ : Dir) (c' : Cell n' m'),
      neighbor? c δ = some c' → neighbor? (ι c) (f δ) = some (ι c'))
    (p : Cell n' m') (σ : List Dir) (happ : ApplicableFrom p σ) (x : Cell n' m') :
    permOf (ι p) (σ.map f) (ι x) = ι (permOf p σ x) := by
  induction σ generalizing p with
  | nil => simp
  | cons δ σ ih =>
      obtain ⟨c', hc', hσ⟩ := happ
      rw [List.map_cons, permOf_cons_of_neighbor? (hstep p δ c' hc'),
          permOf_cons_of_neighbor? hc', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
          ih c' hσ]
      exact swap_apply_injective hinj p c' (permOf c' σ x)

/-- The trace set of a transported word stays in the image of the map. -/
theorem traceSet_map_subset_range {n' m' : ℕ} {ι : Cell n' m' → Cell n m} {f : Dir → Dir}
    (hstep : ∀ (c : Cell n' m') (δ : Dir) (c' : Cell n' m'),
      neighbor? c δ = some c' → neighbor? (ι c) (f δ) = some (ι c'))
    (p : Cell n' m') (σ : List Dir) (happ : ApplicableFrom p σ) :
    ∀ x ∈ traceSet (ι p) (σ.map f), x ∈ Set.range ι := by
  induction σ generalizing p with
  | nil =>
      intro x hx
      rw [List.map_nil, traceSet_nil, Finset.mem_singleton] at hx
      exact ⟨p, hx.symm⟩
  | cons δ σ ih =>
      obtain ⟨c', hc', hσ⟩ := happ
      intro x hx
      rw [List.map_cons, traceSet_cons_of_neighbor? (hstep p δ c' hc')] at hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · exact ⟨p, hx.symm⟩
      · exact ih c' hσ x hx

/-- The trace set of a transported word is exactly the image of the trace set. -/
theorem traceSet_map_eq_image {n' m' : ℕ} {ι : Cell n' m' → Cell n m} {f : Dir → Dir}
    (hinj : Function.Injective ι)
    (hstep : ∀ (c : Cell n' m') (δ : Dir) (c' : Cell n' m'),
      neighbor? c δ = some c' → neighbor? (ι c) (f δ) = some (ι c'))
    (p : Cell n' m') (σ : List Dir) (happ : ApplicableFrom p σ) :
    traceSet (ι p) (σ.map f) = (traceSet p σ).image ι := by
  induction σ generalizing p with
  | nil => simp
  | cons δ σ ih =>
      obtain ⟨c', hc', hσ⟩ := happ
      rw [List.map_cons, traceSet_cons_of_neighbor? (hstep p δ c' hc'),
        traceSet_cons_of_neighbor? hc', Finset.image_insert, ih c' hσ]

/-- The transported permutation fixes every cell outside the image of the map. -/
theorem permOf_map_fixes_of_not_mem_range {n' m' : ℕ} {ι : Cell n' m' → Cell n m}
    {f : Dir → Dir}
    (hstep : ∀ (c : Cell n' m') (δ : Dir) (c' : Cell n' m'),
      neighbor? c δ = some c' → neighbor? (ι c) (f δ) = some (ι c'))
    (p : Cell n' m') (σ : List Dir) (happ : ApplicableFrom p σ)
    {y : Cell n m} (hy : y ∉ Set.range ι) :
    permOf (ι p) (σ.map f) y = y := by
  apply permOf_apply_of_not_mem_traceSet
  intro hmem
  exact hy (traceSet_map_subset_range hstep p σ happ y hmem)

/-- If the transported permutation of the strip is a single transposition, so is the
transported permutation of the larger board. -/
theorem permOf_map_eq_swap {n' m' : ℕ} {ι : Cell n' m' → Cell n m} {f : Dir → Dir}
    (hinj : Function.Injective ι)
    (hstep : ∀ (c : Cell n' m') (δ : Dir) (c' : Cell n' m'),
      neighbor? c δ = some c' → neighbor? (ι c) (f δ) = some (ι c'))
    (p : Cell n' m') (σ : List Dir) (happ : ApplicableFrom p σ)
    {a b : Cell n' m'} (hQ : permOf p σ = Equiv.swap a b) :
    permOf (ι p) (σ.map f) = Equiv.swap (ι a) (ι b) := by
  apply Equiv.ext
  intro y
  by_cases hy : ∃ x, ι x = y
  · obtain ⟨x, rfl⟩ := hy
    rw [permOf_map_apply_of_neighbor_map hinj hstep p σ happ x, hQ,
        swap_apply_injective hinj a b x]
  · push Not at hy
    have hy' : y ∉ Set.range ι := fun hmem => hy hmem.choose hmem.choose_spec
    rw [permOf_map_fixes_of_not_mem_range hstep p σ happ hy',
        Equiv.swap_apply_of_ne_of_ne (fun h => hy a h.symm) (fun h => hy b h.symm)]

/-! ### Applicability of the jump words (on a `2 × m` board) -/

/-- Applicability of the `L`-run of length two. -/
theorem applicableFrom_L2 {c : Fin m} (hc : c.val + 2 < m) :
    ApplicableFrom (top c) [Dir.L, Dir.L] := by
  simpa [top, List.replicate] using
    (applicableFrom_replicate_left (n := 2) (m := m) 0 2 c.val (by omega) (by decide))

/-- Trace of the `L`-run of length two. -/
theorem trace_L2 {c : Fin m} (hc : c.val + 2 < m) :
    trace (top c) [Dir.L, Dir.L] = top (⟨c.val + 2, hc⟩ : Fin m) := by
  have h := trace_replicate_L2 (0 : Fin 2) (c := c) 2 (by simpa using hc)
  simpa [top, List.replicate] using h

/-- Applicability of the `R`-run of length two. -/
theorem applicableFrom_R2 {c : Fin m} (hc : c.val + 2 < m) :
    ApplicableFrom (top (⟨c.val + 2, hc⟩ : Fin m)) [Dir.R, Dir.R] := by
  simpa [top, List.replicate] using
    (applicableFrom_replicate_right (n := 2) (m := m) 0 2 (c.val + 2) (by omega)
      (by decide) (by omega))

/-- Trace of the `R`-run of length two. -/
theorem trace_R2 {c : Fin m} (hc : c.val + 2 < m) :
    trace (top (⟨c.val + 2, hc⟩ : Fin m)) [Dir.R, Dir.R] = top c := by
  have h := trace_invWord (applicableFrom_L2 (c := c) hc)
  rw [trace_L2 hc] at h
  simpa [invWord] using h

/-- The loop `U R D L` is applicable from `(0,c+1)`. -/
theorem applicableFrom_jumpLoop {c : Fin m} (hc : c.val + 2 < m) :
    ApplicableFrom (top (⟨c.val + 1, by omega⟩ : Fin m)) jumpLoop := by
  have hc1 : c.val + 1 < m := by omega
  have h1 : neighbor? (top (⟨c.val + 1, hc1⟩ : Fin m)) Dir.U
      = some (bot (⟨c.val + 1, hc1⟩ : Fin m)) := by
    simpa [top, bot] using
      (neighbor?_mk_U (x := (0 : Fin 2)) (y := (⟨c.val + 1, hc1⟩ : Fin m)) (by decide))
  have h2 : neighbor? (bot (⟨c.val + 1, hc1⟩ : Fin m)) Dir.R = some (bot c) := by
    simpa [bot] using
      (neighbor?_mk_R (x := (1 : Fin 2)) (y := (⟨c.val + 1, hc1⟩ : Fin m))
        (by simp only [Fin.val_mk]; omega))
  have h3 : neighbor? (bot c) Dir.D = some (top c) := by
    simpa [top, bot] using (neighbor?_mk_D (x := (1 : Fin 2)) (y := c) (by decide))
  have h4 : neighbor? (top c) Dir.L = some (top (⟨c.val + 1, hc1⟩ : Fin m)) := by
    simpa [top] using (neighbor?_mk_L (x := (0 : Fin 2)) (y := c) hc1)
  unfold jumpLoop
  refine ⟨bot (⟨c.val + 1, hc1⟩ : Fin m), h1, ?_⟩
  rw [applicableFrom_cons_of_neighbor? h2]
  refine ⟨top c, h3, ?_⟩
  rw [applicableFrom_cons_of_neighbor? h4]
  exact trivial

/-- The gadget is applicable from its base `(0,c)`. -/
theorem applicableFrom_jumpGadget {c : Fin m} (hc : c.val + 2 < m) :
    ApplicableFrom (top c) jumpGadget := by
  unfold jumpGadget
  rw [List.append_assoc, applicableFrom_append, trace_jumpHead hc]
  refine ⟨applicableFrom_jumpHead hc, ?_⟩
  rw [applicableFrom_append, trace_jumpLoop hc]
  exact ⟨applicableFrom_jumpLoop hc,
    by simpa [trace_jumpHead hc] using applicableFrom_invWord (applicableFrom_jumpHead hc)⟩

/-- The closed part of the jump word is applicable from its base. -/
theorem applicableFrom_jumpClosed : ∀ (l : ℕ) (c : Fin m) (hc : c.val + 2 * l < m),
    ApplicableFrom (top c) (jumpClosed l) := by
  intro l
  induction l with
  | zero => intro c hc; rw [jumpClosed_zero]; exact trivial
  | succ l ih =>
      intro c hc
      have hc2 : c.val + 2 < m := by omega
      have hc2l : (⟨c.val + 2, hc2⟩ : Fin m).val + 2 * l < m := by
        simp only [Fin.val_mk]; omega
      rw [jumpClosed_succ,
        show [Dir.L, Dir.L] ++ jumpClosed l ++ [Dir.R, Dir.R] ++ jumpGadget
          = [Dir.L, Dir.L] ++ (jumpClosed l ++ ([Dir.R, Dir.R] ++ jumpGadget)) from by
          simp [List.append_assoc],
        applicableFrom_append, trace_L2 hc2]
      refine ⟨applicableFrom_L2 hc2, ?_⟩
      rw [applicableFrom_append]
      refine ⟨ih (⟨c.val + 2, hc2⟩ : Fin m) hc2l, ?_⟩
      rw [trace_jumpClosed l (⟨c.val + 2, hc2⟩ : Fin m) hc2l,
        applicableFrom_append, trace_R2 hc2]
      exact ⟨applicableFrom_R2 hc2, applicableFrom_jumpGadget hc2⟩

/-- The jump word is applicable from its base `(0,c)`. -/
theorem applicableFrom_jumpWord {c : Fin m} (l : ℕ) (hc : c.val + 2 * l < m) :
    ApplicableFrom (top c) (jumpWord l) := by
  have hU : neighbor? (top c) Dir.U = some (bot c) := by
    simpa [top, bot] using (neighbor?_mk_U (x := (0 : Fin 2)) (y := c) (by decide))
  rw [jumpWord,
    show jumpClosed l ++ [Dir.U] ++ List.replicate (2 * l) Dir.L
      = jumpClosed l ++ ([Dir.U] ++ List.replicate (2 * l) Dir.L) from by
      simp [List.append_assoc],
    applicableFrom_append, trace_jumpClosed l c hc, applicableFrom_append]
  refine ⟨applicableFrom_jumpClosed l c hc, ?_, ?_⟩
  · exact ⟨bot c, hU, trivial⟩
  · rw [show trace (top c) [Dir.U] = bot c from by
      rw [trace_cons_of_neighbor? hU, trace_nil]]
    simpa [bot] using
      (applicableFrom_replicate_left (n := 2) (m := m) 1 (2 * l) c.val hc (by decide))

/-! ### The two-row horizontal strip -/

/-- The two-row horizontal strip at rows `r, r+1`. -/
def hStrip (r : ℕ) (hr : r + 1 < n) (c : Cell 2 m) : Cell n m :=
  (⟨r + c.1.val, by have := c.1.isLt; omega⟩, c.2)

theorem hStrip_injective (r : ℕ) (hr : r + 1 < n) :
    Function.Injective (hStrip (m := m) r hr) := by
  intro c1 c2 h
  have h2 : c1.2 = c2.2 := congrArg (fun x : Cell n m => x.2) h
  have h1 : c1.1 = c2.1 := by
    have hh : r + c1.1.val = r + c2.1.val := congrArg (fun x : Cell n m => x.1.val) h
    exact Fin.ext (by omega)
  exact Prod.ext h1 h2

theorem hStrip_neighbor (r : ℕ) (hr : r + 1 < n) :
    ∀ (c : Cell 2 m) (δ : Dir) (c' : Cell 2 m),
      neighbor? c δ = some c' → neighbor? (hStrip r hr c) δ = some (hStrip r hr c') := by
  rintro ⟨a, b⟩ δ ⟨a', b'⟩ h
  fin_cases a <;> fin_cases a' <;> cases δ <;> simp_all [hStrip, neighbor?] <;> split_ifs <;> simp_all <;> omega

/-! ### The two-column vertical strip -/

/-! ### Moving the blank to a prescribed cell -/

/-- The word moving the blank from `(r,c)` to `(x,y)`: first vertically, then horizontally. -/
def moveToWord (r c x y : ℕ) : List Dir := moveXWord r x ++ moveYWord c y

theorem trace_moveToWord (r c x y : ℕ) (hx : x < n) (hy : y < m) (hr : r < n) (hc : c < m) :
    trace (((⟨r, hr⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m) (moveToWord r c x y)
      = (((⟨x, hx⟩ : Fin n), (⟨y, hy⟩ : Fin m)) : Cell n m) := by
  unfold moveToWord
  rw [trace_append, trace_moveXWord r c x hx hr hc]
  exact trace_moveYWord x c y hx hc hy

theorem applicableFrom_moveToWord (r c x y : ℕ) (hx : x < n) (hy : y < m) (hr : r < n)
    (hc : c < m) :
    ApplicableFrom (((⟨r, hr⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m)
      (moveToWord r c x y) := by
  unfold moveToWord
  rw [applicableFrom_append]
  refine ⟨applicableFrom_moveXWord r c x hx hr hc, ?_⟩
  rw [trace_moveXWord r c x hx hr hc]
  exact applicableFrom_moveYWord x c y hy hx hc

theorem length_moveToWord (r c x y : ℕ) :
    (moveToWord r c x y).length = Nat.dist r x + Nat.dist c y := by
  simp [moveToWord, length_moveXWord, length_moveYWord]

/-- Moving the blank of a board with `moveToWord`. -/
theorem blank_actSeq_moveToWord (r c x y : ℕ) (hx : x < n) (hy : y < m) (hr : r < n)
    (hc : c < m) [NeZero (n * m)] (B : Board n m)
    (hblank : blank B = (((⟨r, hr⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m)) :
    blank (actSeq B (moveToWord r c x y))
      = (((⟨x, hx⟩ : Fin n), (⟨y, hy⟩ : Fin m)) : Cell n m) := by
  rw [blank_actSeq, hblank, trace_moveToWord r c x y hx hy hr hc]

/-! ### Transport of applicability -/

/-- Transport of applicability along a map carrying applicable moves to applicable moves. -/
theorem applicableFrom_map_of_neighbor_map {n' m' : ℕ} {ι : Cell n' m' → Cell n m}
    {f : Dir → Dir}
    (hstep : ∀ (c : Cell n' m') (δ : Dir) (c' : Cell n' m'),
      neighbor? c δ = some c' → neighbor? (ι c) (f δ) = some (ι c'))
    {p : Cell n' m'} {σ : List Dir} (happ : ApplicableFrom p σ) :
    ApplicableFrom (ι p) (σ.map f) := by
  induction σ generalizing p with
  | nil => trivial
  | cons δ σ ih =>
      obtain ⟨c', hc', hσ⟩ := happ
      exact ⟨ι c', hstep p δ c' hc', ih hσ⟩

/-! ### The reflected and flipped jumps on a horizontal strip -/

/-- Applicability of the reflected jump on a `2 × m` board. -/
theorem applicableFrom_reflJumpWord {c : Fin m} (l : ℕ) (hc : 2 * l ≤ c.val) :
    ApplicableFrom (top c) (reflJumpWord l) := by
  have hcle : (c.rev).val + 2 * l < m := by rw [Fin.val_rev]; omega
  have h := applicableFrom_map_of_neighbor_map (ι := colRefl 2 m) (f := reflDir)
    (fun c δ c' hc' => by rw [neighbor?_colRefl, hc']; rfl)
    (applicableFrom_jumpWord l hcle)
  have htop : colRefl 2 m (top (c.rev)) = top c := by
    simp [top, colRefl_apply, Fin.rev_rev]
  simpa [reflJumpWord, htop] using h

/-- Applicability of the flipped jump on a `2 × m` board. -/
theorem applicableFrom_flipJumpWord {c : Fin m} (l : ℕ) (hc : c.val + 2 * l < m) :
    ApplicableFrom (bot c) (flipJumpWord l) := by
  have h := applicableFrom_map_of_neighbor_map (ι := rowSwap2 m) (f := flipDir)
    (fun c δ c' hc' => by rw [neighbor?_rowSwap2, hc']; rfl)
    (applicableFrom_jumpWord l hc)
  have htop : rowSwap2 m (top c) = bot c := by
    simp [top, bot, rowSwap2_apply, Fin.rev_zero]
  simpa [flipJumpWord, htop] using h

/-! ### The same-row jump on a horizontal strip -/

/-- The loop `D R U L` of the same-row gadget is applicable from `(1,c+2)`. -/
theorem applicableFrom_row0Loop {c : Fin m} (hc : c.val + 3 < m) :
    ApplicableFrom (bot (⟨c.val + 2, by omega⟩ : Fin m)) row0Loop := by
  have hc1 : c.val + 1 < m := by omega
  have hc2 : c.val + 2 < m := by omega
  have h1 : neighbor? (bot (⟨c.val + 2, hc2⟩ : Fin m)) Dir.D
      = some (top (⟨c.val + 2, hc2⟩ : Fin m)) := by
    simpa [top, bot] using
      (neighbor?_mk_D (x := (1 : Fin 2)) (y := (⟨c.val + 2, hc2⟩ : Fin m)) (by decide))
  have h2 : neighbor? (top (⟨c.val + 2, hc2⟩ : Fin m)) Dir.R
      = some (top (⟨c.val + 1, hc1⟩ : Fin m)) := by
    simpa [top] using (neighbor?_mk_R (x := (0 : Fin 2))
      (y := (⟨c.val + 2, hc2⟩ : Fin m)) (by simp only [Fin.val_mk]; omega))
  have h3 : neighbor? (top (⟨c.val + 1, hc1⟩ : Fin m)) Dir.U
      = some (bot (⟨c.val + 1, hc1⟩ : Fin m)) := by
    simpa [top, bot] using
      (neighbor?_mk_U (x := (0 : Fin 2)) (y := (⟨c.val + 1, hc1⟩ : Fin m)) (by decide))
  have h4 : neighbor? (bot (⟨c.val + 1, hc1⟩ : Fin m)) Dir.L
      = some (bot (⟨c.val + 2, hc2⟩ : Fin m)) := by
    simpa [bot] using (neighbor?_mk_L (x := (1 : Fin 2))
      (y := (⟨c.val + 1, hc1⟩ : Fin m)) (by simp only [Fin.val_mk]; omega))
  unfold row0Loop
  refine ⟨top (⟨c.val + 2, hc2⟩ : Fin m), h1, ?_⟩
  rw [applicableFrom_cons_of_neighbor? h2]
  refine ⟨bot (⟨c.val + 1, hc1⟩ : Fin m), h3, ?_⟩
  rw [applicableFrom_cons_of_neighbor? h4]
  exact trivial

/-- The same-row gadget is applicable from its base `(0,c)`. -/
theorem applicableFrom_row0Gadget {c : Fin m} (hc : c.val + 3 < m) :
    ApplicableFrom (top c) row0Gadget := by
  unfold row0Gadget
  rw [List.append_assoc, applicableFrom_append, trace_row0Head hc]
  refine ⟨applicableFrom_row0Head hc, ?_⟩
  rw [applicableFrom_append, trace_row0Loop hc]
  exact ⟨applicableFrom_row0Loop hc,
    by simpa [trace_row0Head hc] using applicableFrom_invWord (applicableFrom_row0Head hc)⟩

/-- The closed part of the same-row jump word is applicable from its base. -/
theorem applicableFrom_row0Closed : ∀ (l : ℕ) (c : Fin m) (hc : c.val + 2 * l + 1 < m),
    ApplicableFrom (top c) (row0Closed l) := by
  intro l
  induction l with
  | zero => intro c hc; rw [row0Closed_zero]; exact trivial
  | succ l ih =>
      intro c hc
      have hc2 : c.val + 2 < m := by omega
      have hc2l : (⟨c.val + 2, hc2⟩ : Fin m).val + 2 * l + 1 < m := by
        simp only [Fin.val_mk]; omega
      rw [row0Closed_succ,
        show [Dir.L, Dir.L] ++ row0Closed l ++ [Dir.R, Dir.R] ++ row0Gadget
          = [Dir.L, Dir.L] ++ (row0Closed l ++ ([Dir.R, Dir.R] ++ row0Gadget)) from by
          simp [List.append_assoc],
        applicableFrom_append, trace_L2 hc2]
      refine ⟨applicableFrom_L2 hc2, ?_⟩
      rw [applicableFrom_append]
      refine ⟨ih (⟨c.val + 2, hc2⟩ : Fin m) hc2l, ?_⟩
      rw [trace_row0Closed l (⟨c.val + 2, hc2⟩ : Fin m) hc2l,
        applicableFrom_append, trace_R2 hc2]
      exact ⟨applicableFrom_R2 hc2, applicableFrom_row0Gadget (c := c) (by omega)⟩

/-- The same-row jump word is applicable from its base `(0,c)`. -/
theorem applicableFrom_row0Word {c : Fin m} (l : ℕ) (hc : c.val + 2 * l + 1 < m) :
    ApplicableFrom (top c) (row0Word l) := by
  rw [row0Word, applicableFrom_append, trace_row0Closed l c hc]
  exact ⟨applicableFrom_row0Closed l c hc,
    by simpa [top, List.replicate] using
      (applicableFrom_replicate_left (n := 2) (m := m) 0 (2 * l + 1) c.val hc (by decide))⟩

/-! ### The three-row horizontal strip

Lemma 1 of Zhong (2023) is proved on a `3 × m` board in `Algorithm/Shift.lean`.  Phase I of
the algorithm applies it to a three-row strip of a larger board, so here we lift it exactly
as for the jump words: the embedding `hStrip3` carries the moves of the strip to the board,
and `applicableFrom_shiftWord` makes the transport unconditional. -/

/-- The three-row horizontal strip at rows `r, r+1, r+2`. -/
def hStrip3 (r : ℕ) (hr : r + 2 < n) (c : Cell 3 m) : Cell n m :=
  (⟨r + c.1.val, by have := c.1.isLt; omega⟩, c.2)

theorem hStrip3_injective (r : ℕ) (hr : r + 2 < n) :
    Function.Injective (hStrip3 (m := m) r hr) := by
  intro c1 c2 h
  have h2 : c1.2 = c2.2 := congrArg (fun x : Cell n m => x.2) h
  have h1 : c1.1 = c2.1 := by
    have hh : r + c1.1.val = r + c2.1.val := congrArg (fun x : Cell n m => x.1.val) h
    exact Fin.ext (by omega)
  exact Prod.ext h1 h2

theorem hStrip3_neighbor (r : ℕ) (hr : r + 2 < n) :
    ∀ (c : Cell 3 m) (δ : Dir) (c' : Cell 3 m),
      neighbor? c δ = some c' → neighbor? (hStrip3 r hr c) δ = some (hStrip3 r hr c') := by
  rintro ⟨a, b⟩ δ ⟨a', b'⟩ h
  fin_cases a <;> fin_cases a' <;> cases δ <;>
    simp_all [hStrip3, neighbor?] <;>
    (try omega) <;>
    (try (split_ifs <;> simp_all <;> omega)) <;>
    (try (rcases h with ⟨hb, hbb⟩; rw [dif_pos hb]; simp_all))

/-- **Lemma 1 (Zhong 2023), lifted to a three-row strip.**  On an `n × m` board, if the
blank is at `(r+2, 0)` with `r + 2 < n`, then the word `shiftWord m` moves the tile at
`(r, c)` down to `(r+1, c)` for every column `c`, and fixes the row `r+2`. -/
theorem hStrip3_shiftWord (r : ℕ) (hr : r + 2 < n) {m : ℕ} (hm : 1 < m) (c : Fin m) :
    permOf (hStrip3 r hr ((2 : Fin 3), (⟨0, by omega⟩ : Fin m))) (shiftWord m)
        (hStrip3 r hr ((1 : Fin 3), c))
      = hStrip3 r hr ((0 : Fin 3), c) := by
  have h := permOf_map_apply_of_neighbor_map (ι := hStrip3 (n := n) (m := m) r hr) (f := id)
    (hStrip3_injective r hr) (hStrip3_neighbor r hr)
    ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) (shiftWord m)
    (applicableFrom_shiftWord hm) (x := ((1 : Fin 3), c))
  simp only [List.map_id] at h
  rw [h, permOf_shiftWord_row1 hm c]

/-- **Lemma 1, lifted to a three-row strip, third row fixed.** -/
theorem hStrip3_shiftWord_row2 (r : ℕ) (hr : r + 2 < n) {m : ℕ} (hm : 1 < m) (c : Fin m) :
    permOf (hStrip3 r hr ((2 : Fin 3), (⟨0, by omega⟩ : Fin m))) (shiftWord m)
        (hStrip3 r hr ((2 : Fin 3), c))
      = hStrip3 r hr ((2 : Fin 3), c) := by
  have h := permOf_map_apply_of_neighbor_map (ι := hStrip3 (n := n) (m := m) r hr) (f := id)
    (hStrip3_injective r hr) (hStrip3_neighbor r hr)
    ((2 : Fin 3), (⟨0, by omega⟩ : Fin m)) (shiftWord m)
    (applicableFrom_shiftWord hm) (x := ((2 : Fin 3), c))
  simp only [List.map_id] at h
  rw [h, permOf_shiftWord_row2 hm c]

/-! ### The multi-step row translation `(θ_m U)^t`

Acting `(θ_m U)^t` moves a `1 × m` subarray down by `t` cells (Lemma 1 of Zhong 2023).
The leftmost column of the `3 × m` window is a scratch column (it is permuted by the
vertical `U` moves); the remaining `m - 1` columns move down cleanly.  The results below
isolate that clean movement, which is what Phase I uses. -/

/-- The word `(θ_m U)^t` moving a `1 × m` subarray down by `t`. -/
def downWord (m : ℕ) : ℕ → List Dir
  | 0 => []
  | t + 1 => downWord m t ++ shiftWord m ++ [Dir.U]

@[simp] theorem downWord_zero (m : ℕ) : downWord m 0 = [] := rfl

theorem downWord_succ (m t : ℕ) :
    downWord m (t + 1) = downWord m t ++ shiftWord m ++ [Dir.U] := rfl

/-- The multi-step translation word `(θ_m U)^t` has length `t (6m + 3)`. -/
theorem downWord_length {m : ℕ} (hm : 1 < m) (t : ℕ) :
    (downWord m t).length = t * (6 * m + 3) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [downWord_succ, List.length_append, List.length_append, ih, shiftWord_length hm]
      simp only [List.length_singleton]
      ring

/-- The lifted single step, with the strip written as plain board cells. -/
theorem permOf_shiftWord_window {N m : ℕ} (r : ℕ) (hr : r + 2 < N) (hm : 1 < m) (c : Fin m) :
    permOf (((⟨r + 2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m) (shiftWord m)
        (((⟨r + 1, by omega⟩ : Fin N), c) : Cell N m)
      = (((⟨r, by omega⟩ : Fin N), c) : Cell N m) := by
  have h := hStrip3_shiftWord (n := N) r hr hm c
  simpa [hStrip3] using h

/-- The lifted single step fixes the third row. -/
theorem permOf_shiftWord_window_row2 {N m : ℕ} (r : ℕ) (hr : r + 2 < N) (hm : 1 < m)
    (c : Fin m) :
    permOf (((⟨r + 2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m) (shiftWord m)
        (((⟨r + 2, by omega⟩ : Fin N), c) : Cell N m)
      = (((⟨r + 2, by omega⟩ : Fin N), c) : Cell N m) := by
  have h := hStrip3_shiftWord_row2 (n := N) r hr hm c
  simpa [hStrip3] using h

/-- The blank of the lifted shift word returns to its start. -/
theorem trace_shiftWord_window {N m : ℕ} (r : ℕ) (hr : r + 2 < N) (hm : 1 < m) :
    trace (((⟨r + 2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m) (shiftWord m)
      = (((⟨r + 2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m) := by
  rw [← permOf_symm_apply, Equiv.symm_apply_eq]
  exact (permOf_shiftWord_window_row2 r hr hm (⟨0, by omega⟩ : Fin m)).symm

/-- A single `U` fixes a cell that is neither the blank nor its neighbour. -/
theorem permOf_U_fixes {N m : ℕ} {p x : Cell N m} (hx : x ≠ p)
    (hx' : neighbor? p Dir.U ≠ some x) : permOf p [Dir.U] x = x := by
  cases h : neighbor? p Dir.U with
  | none => rw [permOf_cons_of_neighbor?_eq_none h, permOf_nil]; rfl
  | some q =>
      rw [permOf_cons_of_neighbor? h, permOf_nil, mul_one]
      exact Equiv.swap_apply_of_ne_of_ne hx (fun hq => hx' (by rw [h, hq]))

/-- The neighbour of the blank after the vertical `U` step of the translation. -/
theorem neighbor_U_window {N m : ℕ} (t : ℕ) (hN : t + 2 + 1 < N) (hm : 0 < m) :
    neighbor? (((⟨t + 2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m) Dir.U
      = some (((⟨t + 3, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m) := by
  simp only [neighbor?]
  rw [dif_pos (by omega)]

/-- The blank of `(θ_m U)^t` ends at row `t + 2`. -/
theorem trace_downWord {N m t : ℕ} (hN : t + 2 < N) (hm : 1 < m) :
    trace (((⟨2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m) (downWord m t)
      = (((⟨t + 2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m) := by
  revert hN
  induction t with
  | zero =>
      intro hN
      rw [downWord_zero, trace_nil]
  | succ t ih =>
      intro hN
      rw [downWord_succ, trace_append, trace_append, ih (by omega)]
      rw [trace_shiftWord_window t (by omega) hm,
          trace_cons_of_neighbor? (neighbor_U_window t (by omega) (by omega)), trace_nil]

/-- **Lemma 1 (Zhong 2023), multi-step translation.**  On an `N × m` board, the word
`(θ_m U)^t` moves the content of row `0` (columns `≥ 1`) down to row `t`. -/
theorem permOf_downWord {N m t : ℕ} (hN : t + 2 < N) (hm : 1 < m) (c : Fin m) :
    permOf (((⟨2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m) (downWord m t)
        (((⟨t, by omega⟩ : Fin N), c) : Cell N m)
      = (((⟨0, by omega⟩ : Fin N), c) : Cell N m) := by
  revert hN
  induction t with
  | zero =>
      intro hN
      rw [downWord_zero, permOf_nil]
      rfl
  | succ t ih =>
      intro hN
      rw [downWord_succ, permOf_append,
          trace_append, trace_downWord (by omega) hm,
          trace_shiftWord_window t (by omega) hm]
      rw [Equiv.Perm.mul_apply]
      have hfix : permOf (((⟨t + 2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m)
          [Dir.U] (((⟨t + 1, by omega⟩ : Fin N), c) : Cell N m)
          = (((⟨t + 1, by omega⟩ : Fin N), c) : Cell N m) := by
        apply permOf_U_fixes
        · intro h
          have := congrArg (fun y : Cell N m => y.1.val) h
          simp only [Prod.fst, Fin.val_mk] at this
          omega
        · rw [neighbor_U_window t (by omega) (by omega)]
          intro h
          have := congrArg (fun y : Cell N m => y.1.val) (Option.some.inj h)
          simp only [Prod.fst, Fin.val_mk] at this
          omega
      rw [hfix, permOf_append, trace_downWord (by omega) hm, Equiv.Perm.mul_apply,
          permOf_shiftWord_window t (by omega) hm c]
      exact ih (by omega)

/-- The multi-step translation word is applicable. -/
theorem applicableFrom_downWord {N m t : ℕ} (hN : t + 2 < N) (hm : 1 < m) :
    ApplicableFrom (((⟨2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m)
      (downWord m t) := by
  revert hN
  induction t with
  | zero => intro hN; rw [downWord_zero]; exact trivial
  | succ t ih =>
      intro hN
      rw [downWord_succ, applicableFrom_append]
      constructor
      · rw [applicableFrom_append]
        refine ⟨ih (by omega), ?_⟩
        rw [trace_downWord (by omega) hm]
        simpa [hStrip3] using
          applicableFrom_map_of_neighbor_map (ι := hStrip3 (n := N) t (by omega)) (f := id)
            (hStrip3_neighbor t (by omega)) (applicableFrom_shiftWord hm)
      · rw [trace_append, trace_downWord (by omega) hm,
            trace_shiftWord_window t (by omega) hm]
        exact ⟨_, neighbor_U_window t (by omega) (by omega), trivial⟩

/-- The blank never leaves the three-row window during a lifted `θ_m`. -/
theorem traceSet_shiftWord_window_rows {N m : ℕ} (r : ℕ) (hr : r + 2 < N) (hm : 1 < m) :
    ∀ x ∈ traceSet (((⟨r + 2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m)
        (shiftWord m), x.1.val ≤ r + 2 := by
  intro x hx
  have h := traceSet_map_subset_range (ι := hStrip3 (n := N) (m := m) r hr) (f := id)
    (fun c δ c' hc' => hStrip3_neighbor r hr c δ c' hc')
    (((⟨2, by omega⟩ : Fin 3), (⟨0, by omega⟩ : Fin m)) : Cell 3 m)
    (shiftWord m) (applicableFrom_shiftWord hm)
  simp only [List.map_id] at h
  have hx' : x ∈ traceSet (hStrip3 (n := N) (m := m) r hr
      (((⟨2, by omega⟩ : Fin 3), (⟨0, by omega⟩ : Fin m)) : Cell 3 m)) (shiftWord m) := hx
  obtain ⟨y, hy⟩ := h x hx'
  have hy1 : x.1.val = r + y.1.val := by rw [← hy]; rfl
  have hy2 : y.1.val ≤ 2 := by have := y.1.isLt; omega
  omega

/-- The support of the multi-step translation is contained in the window rows `≤ t + 2`. -/
theorem traceSet_downWord_subset {N m t : ℕ} (hN : t + 2 < N) (hm : 1 < m) :
    ∀ x ∈ traceSet (((⟨2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m)
        (downWord m t), x.1.val ≤ t + 2 := by
  induction t with
  | zero =>
      intro x hx
      rw [downWord_zero, traceSet_nil, Finset.mem_singleton] at hx
      subst hx
      simp
  | succ t ih =>
      intro x hx
      rw [downWord_succ,
        show downWord m t ++ shiftWord m ++ [Dir.U]
          = downWord m t ++ (shiftWord m ++ [Dir.U]) from List.append_assoc _ _ _,
        traceSet_append, trace_downWord (by omega) hm] at hx
      rcases Finset.mem_union.mp hx with hx | hx
      · have := ih (by omega) x hx
        omega
      · rw [traceSet_append, trace_shiftWord_window t (by omega) hm] at hx
        rcases Finset.mem_union.mp hx with hx | hx
        · have := traceSet_shiftWord_window_rows t (by omega) hm x hx
          omega
        · rw [traceSet_cons_of_neighbor? (neighbor_U_window t (by omega) (by omega)),
              traceSet_nil, Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with hx | hx <;> (subst hx; simp)

/-! ### The multi-step translation at an arbitrary base row

Phase I applies the translation inside the window starting at row `r` of a larger board.  The
embedding `rowStrip` carries the moves of the source strip `Cell N m` to `Cell n m`; the
transported `downWord` moves the content of row `r` down to row `r + t`. -/

/-! ### The multi-step column translation `(θ_m^T)^t`

The transpose of `downWord`, obtained by transporting along `transEquiv` exactly as the
vertical jump is obtained from the horizontal one.  On a board `Cell rows cols` (i.e. a
board with `rows` rows and `cols` columns) the word `rightWord rows t` moves the content of
column `0` (every row) to column `t`, fixing everything outside the affected rectangle. -/

/-! ### The multi-step translation on a rectangular block

Phase I step (iii) translates an `H × M` block of the board to the right.  The embedding
`blockStrip` carries the moves of the source block `Cell H M` to `Cell n n`, so that
`rightWord H t` moves the block's first column to its `(t+1)`-st column. -/

/-- The `H × M` block with upper-left corner `(ro, co)`, embedded in an `n × n` board. -/
def blockStrip {n : ℕ} (H M ro co : ℕ) (hro : ro + H ≤ n) (hco : co + M ≤ n)
    (c : Cell H M) : Cell n n :=
  (⟨ro + c.1.val, by have := c.1.isLt; omega⟩,
   ⟨co + c.2.val, by have := c.2.isLt; omega⟩)

theorem blockStrip_injective {n H M ro co : ℕ} (hro : ro + H ≤ n) (hco : co + M ≤ n) :
    Function.Injective (blockStrip (n := n) H M ro co hro hco) := by
  intro c1 c2 h
  have h1 : c1.1 = c2.1 := by
    have hh : ro + c1.1.val = ro + c2.1.val := congrArg (fun x : Cell n n => x.1.val) h
    exact Fin.ext (by omega)
  have h2 : c1.2 = c2.2 := by
    have hh : co + c1.2.val = co + c2.2.val := congrArg (fun x : Cell n n => x.2.val) h
    exact Fin.ext (by omega)
  exact Prod.ext h1 h2

/-- The row strip at rows `r, …, r + N - 1`, embedded in an `n × m` board. -/
def rowStrip {n m : ℕ} (N : ℕ) (r : ℕ) (hr : r + N ≤ n) (c : Cell N m) : Cell n m :=
  (⟨r + c.1.val, by have := c.1.isLt; omega⟩, c.2)


theorem blockStrip_neighbor {n H M ro co : ℕ} (hro : ro + H ≤ n) (hco : co + M ≤ n) :
    ∀ (c : Cell H M) (δ : Dir) (c' : Cell H M),
      neighbor? c δ = some c' →
      neighbor? (blockStrip (n := n) H M ro co hro hco c) δ
        = some (blockStrip H M ro co hro hco c') := by
  rintro ⟨x, y⟩ δ ⟨x', y'⟩ h
  cases δ with
  | U =>
      rw [neighbor?] at h
      split_ifs at h with hx
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
      have hb : (ro + x.1) + 1 < n := by
        rw [Nat.add_assoc]
        exact lt_of_lt_of_le (Nat.add_lt_add_left hx ro) hro
      rw [← h1, ← h2, blockStrip, blockStrip,
        neighbor?_mk_U (x := (⟨ro + x.1, Nat.lt_of_succ_lt hb⟩ : Fin n))
          (y := (⟨co + y.1, by omega⟩ : Fin n)) hb, Option.some.injEq]
      apply Prod.ext
      · apply Fin.ext; simp only [blockStrip]; exact Nat.add_assoc ro x.1 1
      · rfl
  | D =>
      rw [neighbor?] at h
      split_ifs at h with hx
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
      have hpos : 0 < ro + x.1 := lt_of_lt_of_le hx (Nat.le_add_left x.1 ro)
      have hb : ro + x.1 < n := lt_of_lt_of_le (Nat.add_lt_add_left x.isLt ro) hro
      rw [← h1, ← h2, blockStrip, blockStrip,
        neighbor?_mk_D (x := (⟨ro + x.1, hb⟩ : Fin n))
          (y := (⟨co + y.1, by omega⟩ : Fin n)) hpos, Option.some.injEq]
      apply Prod.ext
      · apply Fin.ext; simp only [rowStrip]
        have hx1 : 1 ≤ x.1 := hx
        omega
      · rfl
  | L =>
      rw [neighbor?] at h
      split_ifs at h with hy
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
      have hb : (co + y.1) + 1 < n := by
        rw [Nat.add_assoc]
        exact lt_of_lt_of_le (Nat.add_lt_add_left hy co) hco
      rw [← h1, ← h2, blockStrip, blockStrip,
        neighbor?_mk_L (x := (⟨ro + x.1, by omega⟩ : Fin n))
          (y := (⟨co + y.1, Nat.lt_of_succ_lt hb⟩ : Fin n)) hb, Option.some.injEq]
      rfl
  | R =>
      rw [neighbor?] at h
      split_ifs at h with hy
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
      have hpos : 0 < co + y.1 := lt_of_lt_of_le hy (Nat.le_add_left y.1 co)
      have hb : co + y.1 < n := lt_of_lt_of_le (Nat.add_lt_add_left y.isLt co) hco
      rw [← h1, ← h2, blockStrip, blockStrip,
        neighbor?_mk_R (x := (⟨ro + x.1, by omega⟩ : Fin n))
          (y := (⟨co + y.1, hb⟩ : Fin n)) hpos, Option.some.injEq]
      apply Prod.ext
      · rfl
      · apply Fin.ext; simp only [blockStrip]
        have hy1 : 1 ≤ y.1 := hy
        omega

/-! ### The block column translation (Phase I step (iii))

`rightWord H t` translates a single column.  To translate a *block* of columns to the right we
apply `rightWord H t` to the columns from right to left, routing the blank back along a scratch
row.  The scratch row (`ro`) is corrupted, but the data rows (`ro+1, …, ro+H-1`) are preserved:
the scratch-row lemmas `permOf_rightWord_fixes_of_col_add_one/_two` show that the columns just
past the target are changed only in the scratch row, so the targets already produced by the
translations to the right survive.  This is the primitive Phase I step (iii) needs. -/

/-! ### The multi-step row translation on a rectangular block

Phase I step (ii) translates the segment `B(i, k³:n)` of the board *down*.  The embedding
`blockStrip` carries the moves of the source block `Cell H M` to `Cell n n`, so that
`downWord M t` moves the block's first row to its `(t+1)`-st row while fixing every cell
outside the block (in particular every cell of the columns left of `co`). -/

/-- **Lemma 1, rectangular block.**  On an `n × n` board, `downWord M t` moves the content
of the block's first row (all columns) down to its `(t+1)`-st row. -/
theorem blockStrip_downWord {n H M t ro co : ℕ} (hro : ro + H ≤ n) (hco : co + M ≤ n)
    (hHt : t + 2 < H) (hM : 1 < M) (c : Fin M) :
    permOf (((⟨ro + 2, by omega⟩ : Fin n), (⟨co, by omega⟩ : Fin n)) : Cell n n)
        (downWord M t)
        (((⟨ro + t, by omega⟩ : Fin n), (⟨co + c.1, by omega⟩ : Fin n)) : Cell n n)
      = (((⟨ro, by omega⟩ : Fin n), (⟨co + c.1, by omega⟩ : Fin n)) : Cell n n) := by
  have h := permOf_map_apply_of_neighbor_map
    (ι := blockStrip (n := n) H M ro co hro hco) (f := id)
    (blockStrip_injective hro hco) (blockStrip_neighbor hro hco)
    (((⟨2, by omega⟩ : Fin H), (⟨0, by omega⟩ : Fin M)) : Cell H M)
    (downWord M t) (applicableFrom_downWord (N := H) (m := M) hHt hM)
    (x := ((⟨t, by omega⟩ : Fin H), c))
  simp only [List.map_id] at h
  rw [permOf_downWord (N := H) (m := M) hHt hM c] at h
  simpa [blockStrip] using h

/-- **Lemma 1, rectangular block, board form.** -/
theorem blockStrip_downWord_effect {n H M t ro co : ℕ} (hro : ro + H ≤ n)
    (hco : co + M ≤ n) (hHt : t + 2 < H) (hM : 1 < M) [NeZero (n * n)] (B : Board n n)
    (hblank : blank B = (((⟨ro + 2, by omega⟩ : Fin n), (⟨co, by omega⟩ : Fin n)) : Cell n n))
    (c : Fin M) :
    actSeq B (downWord M t)
        (((⟨ro + t, by omega⟩ : Fin n), (⟨co + c.1, by omega⟩ : Fin n)) : Cell n n)
      = B (((⟨ro, by omega⟩ : Fin n), (⟨co + c.1, by omega⟩ : Fin n)) : Cell n n) := by
  rw [actSeq_eq_permOf, hblank]
  change B (permOf (((⟨ro + 2, by omega⟩ : Fin n), (⟨co, by omega⟩ : Fin n)) : Cell n n)
      (downWord M t)
      (((⟨ro + t, by omega⟩ : Fin n), (⟨co + c.1, by omega⟩ : Fin n)) : Cell n n))
    = B (((⟨ro, by omega⟩ : Fin n), (⟨co + c.1, by omega⟩ : Fin n)) : Cell n n)
  rw [blockStrip_downWord hro hco hHt hM c]

/-- The block translation never leaves rows `≤ ro + t + 2` nor the block's columns. -/
theorem traceSet_blockStrip_downWord {n H M t ro co : ℕ} (hro : ro + H ≤ n)
    (hco : co + M ≤ n) (hHt : t + 2 < H) (hM : 1 < M) :
    ∀ x ∈ traceSet (((⟨ro + 2, by omega⟩ : Fin n), (⟨co, by omega⟩ : Fin n)) : Cell n n)
        (downWord M t), x.1.val ≤ ro + t + 2 ∧ ro ≤ x.1.val ∧ x.1.val < ro + H ∧
        co ≤ x.2.val ∧ x.2.val < co + M := by
  intro x hx
  have h := traceSet_map_eq_image (f := id) (blockStrip_injective hro hco)
    (blockStrip_neighbor hro hco)
    (((⟨2, by omega⟩ : Fin H), (⟨0, by omega⟩ : Fin M)) : Cell H M)
    (downWord M t) (applicableFrom_downWord (N := H) (m := M) hHt hM)
  simp only [List.map_id] at h
  have hx' : x ∈ traceSet (blockStrip (n := n) H M ro co hro hco
      (((⟨2, by omega⟩ : Fin H), (⟨0, by omega⟩ : Fin M)) : Cell H M)) (downWord M t) := hx
  rw [h, Finset.mem_image] at hx'
  obtain ⟨y, hy, hyx⟩ := hx'
  have hy' := traceSet_downWord_subset (N := H) (m := M) hHt hM y hy
  have hyrow : y.1.val < H := y.1.isLt
  have hycol : y.2.val < M := y.2.isLt
  rw [← hyx]
  simp only [blockStrip]
  omega

end Zhong
