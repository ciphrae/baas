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

/-- **Lemma 2 (Zhong 2023), lifted to a horizontal strip.**  On an `n × m` board, if the
blank is at `(r, c)` with `r + 1 < n`, the word `jumpWord l` swaps the blank with the tile
at `(r + 1, c + 2l)`. -/
theorem hStrip_jumpWord (r : ℕ) (hr : r + 1 < n) {c : Fin m} (l : ℕ)
    (hc : c.val + 2 * l < m) :
    permOf (hStrip r hr (top c)) (jumpWord l)
      = Equiv.swap (hStrip r hr (top c))
          (hStrip r hr (bot (⟨c.val + 2 * l, hc⟩ : Fin m))) := by
  have h := permOf_map_eq_swap (ι := hStrip r hr) (f := id) (hStrip_injective r hr)
    (hStrip_neighbor r hr) (top c) (jumpWord l) (applicableFrom_jumpWord l hc)
    (a := top c) (b := bot (⟨c.val + 2 * l, hc⟩ : Fin m)) (permOf_jumpWord l hc)
  simpa using h

/-- **Lemma 2, horizontal strip, board form.** -/
theorem hStrip_jumpWord_effect (r : ℕ) (hr : r + 1 < n) {c : Fin m} (l : ℕ)
    (hc : c.val + 2 * l < m) [NeZero (n * m)] (B : Board n m)
    (hblank : blank B = hStrip r hr (top c)) :
    actSeq B (jumpWord l)
      = (Equiv.swap (hStrip r hr (top c))
          (hStrip r hr (bot (⟨c.val + 2 * l, hc⟩ : Fin m)))).trans B := by
  rw [actSeq_eq_permOf, hblank, hStrip_jumpWord r hr l hc]

/-- The `jumpWord` has length `20 l + 1` also in a horizontal strip. -/
theorem hStrip_jumpWord_length (l : ℕ) : (jumpWord l).length = 20 * l + 1 :=
  jumpWord_length l

/-! ### The two-column vertical strip -/

/-- The two-column vertical strip at columns `r, r+1`.  The domain is `Cell 2 n`, so that
`transDir` turns the horizontal jump into the vertical one. -/
def vStrip (r : ℕ) (hr : r + 1 < m) (c : Cell 2 n) : Cell n m :=
  (c.2, ⟨r + c.1.val, by have := c.1.isLt; omega⟩)

theorem vStrip_injective (r : ℕ) (hr : r + 1 < m) :
    Function.Injective (vStrip (n := n) r hr) := by
  intro c1 c2 h
  have h2 : c1.2 = c2.2 := congrArg (fun x : Cell n m => x.1) h
  have h1 : c1.1 = c2.1 := by
    have hh : r + c1.1.val = r + c2.1.val := congrArg (fun x : Cell n m => x.2.val) h
    exact Fin.ext (by omega)
  exact Prod.ext h1 h2

theorem vStrip_neighbor (r : ℕ) (hr : r + 1 < m) :
    ∀ (c : Cell 2 n) (δ : Dir) (c' : Cell 2 n),
      neighbor? c δ = some c' → neighbor? (vStrip r hr c) (transDir δ) = some (vStrip r hr c') := by
  rintro ⟨a, b⟩ δ ⟨a', b'⟩ h
  fin_cases a <;> fin_cases a' <;> cases δ <;> simp_all [vStrip, transDir, neighbor?] <;> split_ifs <;> simp_all <;> omega

/-- **Lemma 2 (Zhong 2023), lifted to a vertical strip.**  On an `n × m` board, if the
blank is at `(c, r)` with `r + 1 < m`, the word `transJumpWord l` swaps the blank with the
tile at `(c + 2l, r + 1)`. -/
theorem vStrip_transJumpWord (r : ℕ) (hr : r + 1 < m) {c : Fin n} (l : ℕ)
    (hc : c.val + 2 * l < n) :
    permOf (vStrip r hr (top c)) (transJumpWord l)
      = Equiv.swap (vStrip r hr (top c))
          (vStrip r hr (bot (⟨c.val + 2 * l, hc⟩ : Fin n))) := by
  have h := permOf_map_eq_swap (ι := vStrip r hr) (f := transDir) (vStrip_injective r hr)
    (vStrip_neighbor r hr) (top c) (jumpWord l)
    (applicableFrom_jumpWord (m := n) l hc)
    (a := top c) (b := bot (⟨c.val + 2 * l, hc⟩ : Fin n)) (permOf_jumpWord (m := n) l hc)
  simpa [transJumpWord] using h

/-- **Lemma 2, vertical strip, board form.** -/
theorem vStrip_transJumpWord_effect (r : ℕ) (hr : r + 1 < m) {c : Fin n} (l : ℕ)
    (hc : c.val + 2 * l < n) [NeZero (n * m)] (B : Board n m)
    (hblank : blank B = vStrip r hr (top c)) :
    actSeq B (transJumpWord l)
      = (Equiv.swap (vStrip r hr (top c))
          (vStrip r hr (bot (⟨c.val + 2 * l, hc⟩ : Fin n)))).trans B := by
  rw [actSeq_eq_permOf, hblank, vStrip_transJumpWord r hr l hc]

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

/-- **Lemma 2, target to the left, lifted to a horizontal strip.** -/
theorem hStrip_reflJumpWord (r : ℕ) (hr : r + 1 < n) {c : Fin m} (l : ℕ)
    (hc : 2 * l ≤ c.val) :
    permOf (hStrip r hr (top c)) (reflJumpWord l)
      = Equiv.swap (hStrip r hr (top c))
          (hStrip r hr (bot (⟨c.val - 2 * l, by omega⟩ : Fin m))) := by
  have h := permOf_map_eq_swap (ι := hStrip r hr) (f := id) (hStrip_injective r hr)
    (hStrip_neighbor r hr) (top c) (reflJumpWord l) (applicableFrom_reflJumpWord l hc)
    (a := top c) (b := bot (⟨c.val - 2 * l, by omega⟩ : Fin m)) (permOf_reflJumpWord l hc)
  simpa using h

/-- **Lemma 2, blank in the lower row, lifted to a horizontal strip.** -/
theorem hStrip_flipJumpWord (r : ℕ) (hr : r + 1 < n) {c : Fin m} (l : ℕ)
    (hc : c.val + 2 * l < m) :
    permOf (hStrip r hr (bot c)) (flipJumpWord l)
      = Equiv.swap (hStrip r hr (bot c))
          (hStrip r hr (top (⟨c.val + 2 * l, hc⟩ : Fin m))) := by
  have h := permOf_map_eq_swap (ι := hStrip r hr) (f := id) (hStrip_injective r hr)
    (hStrip_neighbor r hr) (bot c) (flipJumpWord l) (applicableFrom_flipJumpWord l hc)
    (a := bot c) (b := top (⟨c.val + 2 * l, hc⟩ : Fin m)) (permOf_flipJumpWord l hc)
  simpa using h

/-- **Lemma 2, target to the left, horizontal strip, board form.** -/
theorem hStrip_reflJumpWord_effect (r : ℕ) (hr : r + 1 < n) {c : Fin m} (l : ℕ)
    (hc : 2 * l ≤ c.val) [NeZero (n * m)] (B : Board n m)
    (hblank : blank B = hStrip r hr (top c)) :
    actSeq B (reflJumpWord l)
      = (Equiv.swap (hStrip r hr (top c))
          (hStrip r hr (bot (⟨c.val - 2 * l, by omega⟩ : Fin m)))).trans B := by
  rw [actSeq_eq_permOf, hblank, hStrip_reflJumpWord r hr l hc]

/-- **Lemma 2, blank in the lower row, horizontal strip, board form.** -/
theorem hStrip_flipJumpWord_effect (r : ℕ) (hr : r + 1 < n) {c : Fin m} (l : ℕ)
    (hc : c.val + 2 * l < m) [NeZero (n * m)] (B : Board n m)
    (hblank : blank B = hStrip r hr (bot c)) :
    actSeq B (flipJumpWord l)
      = (Equiv.swap (hStrip r hr (bot c))
          (hStrip r hr (top (⟨c.val + 2 * l, hc⟩ : Fin m)))).trans B := by
  rw [actSeq_eq_permOf, hblank, hStrip_flipJumpWord r hr l hc]

/-- The lifted canonical jump is applicable on the whole board. -/
theorem applicableFrom_hStrip_jumpWord (r : ℕ) (hr : r + 1 < n) {c : Fin m} (l : ℕ)
    (hc : c.val + 2 * l < m) :
    ApplicableFrom (hStrip r hr (top c)) (jumpWord l) := by
  have h := applicableFrom_map_of_neighbor_map (ι := hStrip r hr) (f := id)
    (hStrip_neighbor r hr) (applicableFrom_jumpWord l hc)
  simpa using h

/-- The lifted vertical jump is applicable on the whole board. -/
theorem applicableFrom_vStrip_transJumpWord (r : ℕ) (hr : r + 1 < m) {c : Fin n} (l : ℕ)
    (hc : c.val + 2 * l < n) :
    ApplicableFrom (vStrip r hr (top c)) (transJumpWord l) := by
  have h := applicableFrom_map_of_neighbor_map (ι := vStrip r hr) (f := transDir)
    (vStrip_neighbor r hr) (applicableFrom_jumpWord (m := n) l hc)
  simpa [transJumpWord] using h

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

/-- **Lemma 2, same row, lifted to a horizontal strip.**  On an `n × m` board, if the blank
is at `(r, c)` with `r + 1 < n`, the word `row0Word l` swaps the blank with the tile at
`(r, c + 2l + 1)`. -/
theorem hStrip_row0Word (r : ℕ) (hr : r + 1 < n) {c : Fin m} (l : ℕ)
    (hc : c.val + 2 * l + 1 < m) :
    permOf (hStrip r hr (top c)) (row0Word l)
      = Equiv.swap (hStrip r hr (top c))
          (hStrip r hr (top (⟨c.val + 2 * l + 1, hc⟩ : Fin m))) := by
  have h := permOf_map_eq_swap (ι := hStrip r hr) (f := id) (hStrip_injective r hr)
    (hStrip_neighbor r hr) (top c) (row0Word l) (applicableFrom_row0Word l hc)
    (a := top c) (b := top (⟨c.val + 2 * l + 1, hc⟩ : Fin m)) (permOf_row0Word l hc)
  simpa using h

/-- **Lemma 2, same row, horizontal strip, board form.** -/
theorem hStrip_row0Word_effect (r : ℕ) (hr : r + 1 < n) {c : Fin m} (l : ℕ)
    (hc : c.val + 2 * l + 1 < m) [NeZero (n * m)] (B : Board n m)
    (hblank : blank B = hStrip r hr (top c)) :
    actSeq B (row0Word l)
      = (Equiv.swap (hStrip r hr (top c))
          (hStrip r hr (top (⟨c.val + 2 * l + 1, hc⟩ : Fin m)))).trans B := by
  rw [actSeq_eq_permOf, hblank, hStrip_row0Word r hr l hc]

/-- The transposed same-row word: the same-column jump. -/
def transRow0Word (l : ℕ) : List Dir := (row0Word l).map transDir

/-- **Lemma 2, same column, lifted to a vertical strip.**  On an `n × m` board, if the blank
is at `(c, r)` with `r + 1 < m`, the word `transRow0Word l` swaps the blank with the tile
at `(c + 2l + 1, r)`. -/
theorem vStrip_transRow0Word (r : ℕ) (hr : r + 1 < m) {c : Fin n} (l : ℕ)
    (hc : c.val + 2 * l + 1 < n) :
    permOf (vStrip r hr (top c)) (transRow0Word l)
      = Equiv.swap (vStrip r hr (top c))
          (vStrip r hr (top (⟨c.val + 2 * l + 1, hc⟩ : Fin n))) := by
  have h := permOf_map_eq_swap (ι := vStrip r hr) (f := transDir) (vStrip_injective r hr)
    (vStrip_neighbor r hr) (top c) (row0Word l)
    (applicableFrom_row0Word (m := n) l hc)
    (a := top c) (b := top (⟨c.val + 2 * l + 1, hc⟩ : Fin n))
    (permOf_row0Word (m := n) l hc)
  simpa [transRow0Word] using h

/-- **Lemma 2, same column, vertical strip, board form.** -/
theorem vStrip_transRow0Word_effect (r : ℕ) (hr : r + 1 < m) {c : Fin n} (l : ℕ)
    (hc : c.val + 2 * l + 1 < n) [NeZero (n * m)] (B : Board n m)
    (hblank : blank B = vStrip r hr (top c)) :
    actSeq B (transRow0Word l)
      = (Equiv.swap (vStrip r hr (top c))
          (vStrip r hr (top (⟨c.val + 2 * l + 1, hc⟩ : Fin n)))).trans B := by
  rw [actSeq_eq_permOf, hblank, vStrip_transRow0Word r hr l hc]

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

/-- **Lemma 1, three-row strip, board form.**  Acting `θ_m` on a board whose blank is at
`(r+2, 0)` moves the content of row `r` down to row `r+1` and fixes row `r+2`. -/
theorem hStrip3_shiftWord_effect (r : ℕ) (hr : r + 2 < n) {m : ℕ} (hm : 1 < m)
    [NeZero (n * m)] (B : Board n m)
    (hblank : blank B = hStrip3 r hr ((2 : Fin 3), (⟨0, by omega⟩ : Fin m))) :
    (∀ c : Fin m, actSeq B (shiftWord m) (hStrip3 r hr ((1 : Fin 3), c))
        = B (hStrip3 r hr ((0 : Fin 3), c))) ∧
    (∀ c : Fin m, actSeq B (shiftWord m) (hStrip3 r hr ((2 : Fin 3), c))
        = B (hStrip3 r hr ((2 : Fin 3), c))) := by
  constructor
  · intro c
    rw [actSeq_eq_permOf, hblank]
    change B (permOf (hStrip3 r hr ((2 : Fin 3), (⟨0, by omega⟩ : Fin m))) (shiftWord m)
        (hStrip3 r hr ((1 : Fin 3), c))) = B (hStrip3 r hr ((0 : Fin 3), c))
    rw [hStrip3_shiftWord r hr hm c]
  · intro c
    rw [actSeq_eq_permOf, hblank]
    change B (permOf (hStrip3 r hr ((2 : Fin 3), (⟨0, by omega⟩ : Fin m))) (shiftWord m)
        (hStrip3 r hr ((2 : Fin 3), c))) = B (hStrip3 r hr ((2 : Fin 3), c))
    rw [hStrip3_shiftWord_row2 r hr hm c]

/-- The shift word has length `6m + 2` also on a three-row strip. -/
theorem hStrip3_shiftWord_length {m : ℕ} (hm : 1 < m) :
    (shiftWord m).length = 6 * m + 2 := shiftWord_length hm

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

/-- **Lemma 1, multi-step translation, board form.** -/
theorem downWord_effect {N m t : ℕ} (hN : t + 2 < N) (hm : 1 < m) [NeZero (N * m)]
    (B : Board N m)
    (hblank : blank B
      = (((⟨2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m))
    (c : Fin m) :
    actSeq B (downWord m t) (((⟨t, by omega⟩ : Fin N), c) : Cell N m)
      = B (((⟨0, by omega⟩ : Fin N), c) : Cell N m) := by
  rw [actSeq_eq_permOf, hblank]
  change B (permOf (((⟨2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m)
      (downWord m t) (((⟨t, by omega⟩ : Fin N), c) : Cell N m))
    = B (((⟨0, by omega⟩ : Fin N), c) : Cell N m)
  rw [permOf_downWord hN hm c]

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

/-- The multi-step translation fixes every cell below the window. -/
theorem permOf_downWord_fixes_of_row_gt {N m t : ℕ} (hN : t + 2 < N) (hm : 1 < m)
    {x : Cell N m} (hx : t + 2 < x.1.val) :
    permOf (((⟨2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m)
        (downWord m t) x = x :=
  permOf_apply_of_not_mem_traceSet (fun hmem => by
    have := traceSet_downWord_subset hN hm x hmem
    omega)

/-- **The scratch-column bound.**  The multi-step translation fixes row `t+2` in every
column except the scratch column `0`; this is the precise "corruption below the window" used
by the corrected Phase I schedule (rows `t+1, t+2` differ from the identity only at column
`0`). -/
theorem permOf_downWord_row_add_two {N m t : ℕ} (hN : t + 2 < N) (hm : 1 < m)
    (c : Fin m) (hc : 0 < c.val) :
    permOf (((⟨2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m) (downWord m t)
        (((⟨t + 2, by omega⟩ : Fin N), c) : Cell N m)
      = (((⟨t + 2, by omega⟩ : Fin N), c) : Cell N m) := by
  revert hN
  induction t with
  | zero =>
      intro hN
      rw [downWord_zero, permOf_nil]
      rfl
  | succ t ih =>
      intro hN
      have hNt : t + 2 < N := by omega
      rw [downWord_succ, permOf_append, trace_append, trace_downWord hNt hm,
        trace_shiftWord_window t (by omega) hm]
      rw [Equiv.Perm.mul_apply]
      have hU : permOf (((⟨t + 2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m)
          [Dir.U] (((⟨t + 3, by omega⟩ : Fin N), c) : Cell N m)
          = (((⟨t + 3, by omega⟩ : Fin N), c) : Cell N m) := by
        apply permOf_U_fixes
        · intro h
          have h2 : t + 3 = t + 2 := congrArg (fun y : Cell N m => y.1.val) h
          omega
        · rw [neighbor_U_window t (by omega) (by omega)]
          intro h
          have h2 : (0 : ℕ) = c.val := by
            simpa using congrArg (fun y : Cell N m => y.2.val) (Option.some.inj h)
          omega
      have hshift : permOf (((⟨t + 2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m)
          (shiftWord m) (((⟨t + 3, by omega⟩ : Fin N), c) : Cell N m)
          = (((⟨t + 3, by omega⟩ : Fin N), c) : Cell N m) := by
        apply permOf_apply_of_not_mem_traceSet
        intro hmem
        have := traceSet_shiftWord_window_rows t (by omega) hm _ hmem
        simp only [Prod.fst, Fin.val_mk] at this
        omega
      rw [hU, permOf_append, trace_downWord hNt hm, Equiv.Perm.mul_apply, hshift]
      exact permOf_downWord_fixes_of_row_gt hNt hm (by simp only [Prod.fst, Fin.val_mk]; omega)

/-- **The scratch-column bound, one row up.**  The multi-step translation fixes row `t+1` in
every column except the scratch column `0`. -/
theorem permOf_downWord_row_add_one {N m t : ℕ} (hN : t + 2 < N) (hm : 1 < m)
    (c : Fin m) (hc : 0 < c.val) :
    permOf (((⟨2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m) (downWord m t)
        (((⟨t + 1, by omega⟩ : Fin N), c) : Cell N m)
      = (((⟨t + 1, by omega⟩ : Fin N), c) : Cell N m) := by
  revert hN
  induction t with
  | zero =>
      intro hN
      rw [downWord_zero, permOf_nil]
      rfl
  | succ t _ =>
      intro hN
      have hNt : t + 2 < N := by omega
      rw [downWord_succ, permOf_append, trace_append, trace_downWord hNt hm,
        trace_shiftWord_window t (by omega) hm]
      rw [Equiv.Perm.mul_apply]
      have hU : permOf (((⟨t + 2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m)
          [Dir.U] (((⟨t + 2, by omega⟩ : Fin N), c) : Cell N m)
          = (((⟨t + 2, by omega⟩ : Fin N), c) : Cell N m) := by
        apply permOf_U_fixes
        · intro h
          have h2 : c.val = 0 := congrArg (fun y : Cell N m => y.2.val) h
          omega
        · rw [neighbor_U_window t (by omega) (by omega)]
          intro h
          have h2 : (0 : ℕ) = c.val := by
            simpa using congrArg (fun y : Cell N m => y.2.val) (Option.some.inj h)
          omega
      rw [hU, permOf_append, trace_downWord hNt hm, Equiv.Perm.mul_apply,
        permOf_shiftWord_window_row2 t (by omega) hm c]
      exact permOf_downWord_row_add_two hNt hm c hc

/-! ### The multi-step translation at an arbitrary base row

Phase I applies the translation inside the window starting at row `r` of a larger board.  The
embedding `rowStrip` carries the moves of the source strip `Cell N m` to `Cell n m`; the
transported `downWord` moves the content of row `r` down to row `r + t`. -/

/-- The row strip at rows `r, …, r + N - 1`, embedded in an `n × m` board. -/
def rowStrip {n m : ℕ} (N : ℕ) (r : ℕ) (hr : r + N ≤ n) (c : Cell N m) : Cell n m :=
  (⟨r + c.1.val, by have := c.1.isLt; omega⟩, c.2)

theorem rowStrip_injective {n m N : ℕ} (r : ℕ) (hr : r + N ≤ n) :
    Function.Injective (rowStrip (n := n) (m := m) N r hr) := by
  intro c1 c2 h
  have h2 : c1.2 = c2.2 := congrArg (fun x : Cell n m => x.2) h
  have h1 : c1.1 = c2.1 := by
    have hh : r + c1.1.val = r + c2.1.val := congrArg (fun x : Cell n m => x.1.val) h
    exact Fin.ext (by omega)
  exact Prod.ext h1 h2

theorem rowStrip_neighbor {n m N : ℕ} (r : ℕ) (hr : r + N ≤ n) :
    ∀ (c : Cell N m) (δ : Dir) (c' : Cell N m),
      neighbor? c δ = some c' →
      neighbor? (rowStrip (n := n) (m := m) N r hr c) δ
        = some (rowStrip N r hr c') := by
  rintro ⟨x, y⟩ δ ⟨x', y'⟩ h
  cases δ with
  | U =>
      rw [neighbor?] at h
      split_ifs at h with hx
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
      have hb : (r + x.1) + 1 < n := by
        rw [Nat.add_assoc]
        exact lt_of_lt_of_le (Nat.add_lt_add_left hx r) hr
      rw [← h1, ← h2, rowStrip, rowStrip,
        neighbor?_mk_U (x := (⟨r + x.1, Nat.lt_of_succ_lt hb⟩ : Fin n)) (y := y) hb,
        Option.some.injEq]
      apply Prod.ext
      · apply Fin.ext; simp only [rowStrip]; exact Nat.add_assoc r x.1 1
      · rfl
  | D =>
      rw [neighbor?] at h
      split_ifs at h with hx
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
      have hpos : 0 < r + x.1 := lt_of_lt_of_le hx (Nat.le_add_left x.1 r)
      have hb : r + x.1 < n := lt_of_lt_of_le (Nat.add_lt_add_left x.isLt r) hr
      rw [← h1, ← h2, rowStrip, rowStrip,
        neighbor?_mk_D (x := (⟨r + x.1, hb⟩ : Fin n)) (y := y) hpos,
        Option.some.injEq]
      apply Prod.ext
      · apply Fin.ext; simp only [rowStrip]
        have hx1 : 1 ≤ x.1 := hx
        omega
      · rfl
  | L =>
      rw [neighbor?] at h
      split_ifs at h with hy
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
      have hb : r + x.1 < n := lt_of_lt_of_le (Nat.add_lt_add_left x.isLt r) hr
      rw [← h1, ← h2, rowStrip, rowStrip,
        neighbor?_mk_L (x := (⟨r + x.1, hb⟩ : Fin n)) (y := y) hy,
        Option.some.injEq]
  | R =>
      rw [neighbor?] at h
      split_ifs at h with hy
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
      have hb : r + x.1 < n := lt_of_lt_of_le (Nat.add_lt_add_left x.isLt r) hr
      rw [← h1, ← h2, rowStrip, rowStrip,
        neighbor?_mk_R (x := (⟨r + x.1, hb⟩ : Fin n)) (y := y) hy,
        Option.some.injEq]

/-- **Lemma 1 (transposed), arbitrary base row.**  On an `n × m` board with `r + t + 2 < n`,
the word `downWord m t` moves the content of row `r` down to row `r + t`. -/
theorem rowStrip_downWord {n m N t r : ℕ} (hr : r + N ≤ n) (hN : t + 2 < N) (hm : 1 < m)
    (c : Fin m) :
    permOf (((⟨r + 2, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) : Cell n m) (downWord m t)
        (((⟨r + t, by omega⟩ : Fin n), c) : Cell n m)
      = (((⟨r, by omega⟩ : Fin n), c) : Cell n m) := by
  have h := permOf_map_apply_of_neighbor_map (ι := rowStrip (n := n) (m := m) N r hr) (f := id)
    (rowStrip_injective r hr) (rowStrip_neighbor r hr)
    (((⟨2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m)
    (downWord m t) (applicableFrom_downWord hN hm) (x := ((⟨t, by omega⟩ : Fin N), c))
  simp only [List.map_id] at h
  rw [permOf_downWord hN hm c] at h
  simpa [rowStrip] using h

/-- **Lemma 1, arbitrary base row, board form.** -/
theorem rowStrip_downWord_effect {n m N t r : ℕ} (hr : r + N ≤ n) (hN : t + 2 < N)
    (hm : 1 < m) [NeZero (n * m)] (B : Board n m)
    (hblank : blank B = (((⟨r + 2, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) : Cell n m))
    (c : Fin m) :
    actSeq B (downWord m t) (((⟨r + t, by omega⟩ : Fin n), c) : Cell n m)
      = B (((⟨r, by omega⟩ : Fin n), c) : Cell n m) := by
  rw [actSeq_eq_permOf, hblank]
  change B (permOf (((⟨r + 2, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) : Cell n m)
      (downWord m t) (((⟨r + t, by omega⟩ : Fin n), c) : Cell n m))
    = B (((⟨r, by omega⟩ : Fin n), c) : Cell n m)
  rw [rowStrip_downWord hr hN hm c]

/-- The window starting at row `r` is not left below row `r + t + 2`. -/
theorem traceSet_rowStrip_downWord {n m N t r : ℕ} (hr : r + N ≤ n) (hN : t + 2 < N)
    (hm : 1 < m) :
    ∀ x ∈ traceSet (((⟨r + 2, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) : Cell n m)
        (downWord m t), x.1.val ≤ r + t + 2 := by
  intro x hx
  have h := traceSet_map_eq_image (f := id)
    (rowStrip_injective (n := n) (m := m) (N := N) r hr)
    (rowStrip_neighbor (n := n) (m := m) (N := N) r hr)
    (((⟨2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m)
    (downWord m t) (applicableFrom_downWord hN hm)
  simp only [List.map_id] at h
  have hx' : x ∈ traceSet (rowStrip (n := n) (m := m) N r hr
      (((⟨2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m)) (downWord m t) := hx
  rw [h, Finset.mem_image] at hx'
  obtain ⟨y, hy, hyx⟩ := hx'
  have hy' := traceSet_downWord_subset hN hm y hy
  rw [← hyx]
  simp only [rowStrip]
  omega

/-- The blank of the lifted multi-step translation ends at `(r + t + 2, 0)`. -/
theorem trace_rowStrip_downWord {n m N t r : ℕ} (hr : r + N ≤ n) (hN : t + 2 < N)
    (hm : 1 < m) :
    trace (((⟨r + 2, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) : Cell n m) (downWord m t)
      = (((⟨r + t + 2, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) : Cell n m) := by
  have h := trace_map_of_neighbor_map (ι := rowStrip (n := n) (m := m) N r hr) (f := id)
    (rowStrip_neighbor r hr)
    (((⟨2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m)
    (downWord m t) (applicableFrom_downWord hN hm)
  simp only [List.map_id] at h
  rw [trace_downWord hN hm] at h
  simpa only [rowStrip, Nat.add_assoc] using h

/-- The lifted multi-step translation never visits a cell above its window. -/
theorem traceSet_rowStrip_downWord_ge {n m N t r : ℕ} (hr : r + N ≤ n) (hN : t + 2 < N)
    (hm : 1 < m) :
    ∀ x ∈ traceSet (((⟨r + 2, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) : Cell n m)
        (downWord m t), r ≤ x.1.val := by
  intro x hx
  have h := traceSet_map_eq_image (f := id)
    (rowStrip_injective (n := n) (m := m) (N := N) r hr)
    (rowStrip_neighbor (n := n) (m := m) (N := N) r hr)
    (((⟨2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m)
    (downWord m t) (applicableFrom_downWord hN hm)
  simp only [List.map_id] at h
  have hx' : x ∈ traceSet (rowStrip (n := n) (m := m) N r hr
      (((⟨2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m)) (downWord m t) := hx
  rw [h, Finset.mem_image] at hx'
  obtain ⟨y, hy, hyx⟩ := hx'
  rw [← hyx]
  simp only [rowStrip]
  omega

/-- **The scratch-column bound, arbitrary base row.**  The lifted multi-step translation
fixes every cell strictly below the window (row `> r + t + 2`). -/
theorem permOf_rowStrip_downWord_fixes_of_row_gt {n m N t r : ℕ} (hr : r + N ≤ n)
    (hN : t + 2 < N) (hm : 1 < m) {x : Cell n m} (hx : r + t + 2 < x.1.val) :
    permOf (((⟨r + 2, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) : Cell n m)
        (downWord m t) x = x :=
  permOf_apply_of_not_mem_traceSet (fun hmem => by
    have := traceSet_rowStrip_downWord hr hN hm x hmem
    omega)

/-- The lifted multi-step translation fixes every cell above its window. -/
theorem permOf_rowStrip_downWord_fixes_of_row_lt {n m N t r : ℕ} (hr : r + N ≤ n)
    (hN : t + 2 < N) (hm : 1 < m) {x : Cell n m} (hx : x.1.val < r) :
    permOf (((⟨r + 2, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) : Cell n m)
        (downWord m t) x = x :=
  permOf_apply_of_not_mem_traceSet (fun hmem => by
    have := traceSet_rowStrip_downWord_ge hr hN hm x hmem
    omega)

/-- **The scratch-column bound, arbitrary base row, row `r + t + 2`.**  The lifted
multi-step translation fixes row `r + t + 2` in every column except the scratch column `0`. -/
theorem permOf_rowStrip_downWord_row_add_two {n m N t r : ℕ} (hr : r + N ≤ n)
    (hN : t + 2 < N) (hm : 1 < m) (c : Fin m) (hc : 0 < c.val) :
    permOf (((⟨r + 2, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) : Cell n m)
        (downWord m t) (((⟨r + t + 2, by omega⟩ : Fin n), c) : Cell n m)
      = (((⟨r + t + 2, by omega⟩ : Fin n), c) : Cell n m) := by
  have h := permOf_map_apply_of_neighbor_map (ι := rowStrip (n := n) (m := m) N r hr) (f := id)
    (rowStrip_injective r hr) (rowStrip_neighbor r hr)
    (((⟨2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m)
    (downWord m t) (applicableFrom_downWord hN hm) (x := ((⟨t + 2, by omega⟩ : Fin N), c))
  simp only [List.map_id] at h
  rw [permOf_downWord_row_add_two hN hm c hc] at h
  simpa only [rowStrip, Nat.add_assoc] using h

/-- **The scratch-column bound, arbitrary base row, row `r + t + 1`.**  The lifted
multi-step translation fixes row `r + t + 1` in every column except the scratch column `0`. -/
theorem permOf_rowStrip_downWord_row_add_one {n m N t r : ℕ} (hr : r + N ≤ n)
    (hN : t + 2 < N) (hm : 1 < m) (c : Fin m) (hc : 0 < c.val) :
    permOf (((⟨r + 2, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) : Cell n m)
        (downWord m t) (((⟨r + t + 1, by omega⟩ : Fin n), c) : Cell n m)
      = (((⟨r + t + 1, by omega⟩ : Fin n), c) : Cell n m) := by
  have h := permOf_map_apply_of_neighbor_map (ι := rowStrip (n := n) (m := m) N r hr) (f := id)
    (rowStrip_injective r hr) (rowStrip_neighbor r hr)
    (((⟨2, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin m)) : Cell N m)
    (downWord m t) (applicableFrom_downWord hN hm) (x := ((⟨t + 1, by omega⟩ : Fin N), c))
  simp only [List.map_id] at h
  rw [permOf_downWord_row_add_one hN hm c hc] at h
  simpa only [rowStrip, Nat.add_assoc] using h

/-! ### The multi-step column translation `(θ_m^T)^t`

The transpose of `downWord`, obtained by transporting along `transEquiv` exactly as the
vertical jump is obtained from the horizontal one.  On a board `Cell rows cols` (i.e. a
board with `rows` rows and `cols` columns) the word `rightWord rows t` moves the content of
column `0` (every row) to column `t`, fixing everything outside the affected rectangle. -/

/-- The transpose of `downWord`: the multi-step column translation word. -/
def rightWord (rows : ℕ) (t : ℕ) : List Dir := (downWord rows t).map transDir

/-- The column translation word has length `t (6 · rows + 3)`. -/
theorem rightWord_length {rows : ℕ} (hm : 1 < rows) (t : ℕ) :
    (rightWord rows t).length = t * (6 * rows + 3) := by
  rw [rightWord, List.length_map, downWord_length hm t]

/-- The blank of the column translation word ends at column `t + 2`. -/
theorem trace_rightWord {rows cols t : ℕ} (hN : t + 2 < cols) (hm : 1 < rows) :
    trace (((⟨0, by omega⟩ : Fin rows), (⟨2, by omega⟩ : Fin cols)) : Cell rows cols)
        (rightWord rows t)
      = (((⟨0, by omega⟩ : Fin rows), (⟨t + 2, by omega⟩ : Fin cols)) : Cell rows cols) := by
  have h := trace_map_of_neighbor_map (ι := transEquiv cols rows) (f := transDir)
    (fun c δ c' hc' => by rw [neighbor?_transEquiv, hc']; rfl)
    (((⟨2, by omega⟩ : Fin cols), (⟨0, by omega⟩ : Fin rows)) : Cell cols rows)
    (downWord rows t) (applicableFrom_downWord hN hm)
  rw [trace_downWord hN hm] at h
  simpa [rightWord, transEquiv_apply] using h

/-- **Lemma 1 (transposed), multi-step translation.**  On a `rows × cols` board, the word
`rightWord rows t` moves the content of column `0` (every row) to column `t`. -/
theorem permOf_rightWord {rows cols t : ℕ} (hN : t + 2 < cols) (hm : 1 < rows)
    (r : Fin rows) :
    permOf (((⟨0, by omega⟩ : Fin rows), (⟨2, by omega⟩ : Fin cols)) : Cell rows cols)
        (rightWord rows t)
        (((r, (⟨t, by omega⟩ : Fin cols))) : Cell rows cols)
      = (((r, (⟨0, by omega⟩ : Fin cols))) : Cell rows cols) := by
  have h := permOf_map (transEquiv cols rows) transDir (neighbor?_transEquiv)
    (((⟨2, by omega⟩ : Fin cols), (⟨0, by omega⟩ : Fin rows)) : Cell cols rows)
    (downWord rows t)
  rw [transEquiv_apply] at h
  have h2 := congrArg (fun e : Equiv.Perm (Cell rows cols) =>
    e (transEquiv cols rows (((⟨t, by omega⟩ : Fin cols), r) : Cell cols rows))) h
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply] at h2
  rw [permOf_downWord (N := cols) (m := rows) hN hm r] at h2
  simpa [rightWord, transEquiv_apply] using h2

/-- **Lemma 1 (transposed), board form.** -/
theorem rightWord_effect {rows cols t : ℕ} (hN : t + 2 < cols) (hm : 1 < rows)
    [NeZero (rows * cols)] (B : Board rows cols)
    (hblank : blank B = (((⟨0, by omega⟩ : Fin rows), (⟨2, by omega⟩ : Fin cols)) : Cell rows cols))
    (r : Fin rows) :
    actSeq B (rightWord rows t) (((r, (⟨t, by omega⟩ : Fin cols))) : Cell rows cols)
      = B (((r, (⟨0, by omega⟩ : Fin cols))) : Cell rows cols) := by
  rw [actSeq_eq_permOf, hblank]
  change B (permOf (((⟨0, by omega⟩ : Fin rows), (⟨2, by omega⟩ : Fin cols)) : Cell rows cols)
      (rightWord rows t) (((r, (⟨t, by omega⟩ : Fin cols))) : Cell rows cols))
    = B (((r, (⟨0, by omega⟩ : Fin cols))) : Cell rows cols)
  rw [permOf_rightWord hN hm r]

/-- The column translation word is applicable. -/
theorem applicableFrom_rightWord {rows cols t : ℕ} (hN : t + 2 < cols) (hm : 1 < rows) :
    ApplicableFrom (((⟨0, by omega⟩ : Fin rows), (⟨2, by omega⟩ : Fin cols)) : Cell rows cols)
      (rightWord rows t) := by
  have h := applicableFrom_map_of_neighbor_map (ι := transEquiv cols rows) (f := transDir)
    (fun c δ c' hc' => by rw [neighbor?_transEquiv, hc']; rfl)
    (applicableFrom_downWord (N := cols) (m := rows) hN hm)
  simpa [rightWord, transEquiv_apply] using h

/-- The support of the column translation is contained in the window columns `≤ t + 2`. -/
theorem traceSet_rightWord_subset {rows cols t : ℕ} (hN : t + 2 < cols) (hm : 1 < rows) :
    ∀ x ∈ traceSet (((⟨0, by omega⟩ : Fin rows), (⟨2, by omega⟩ : Fin cols)) : Cell rows cols)
        (rightWord rows t), x.2.val ≤ t + 2 := by
  intro x hx
  have h := traceSet_map_eq_image (transEquiv cols rows).injective
    (fun c δ c' hc' => by rw [neighbor?_transEquiv, hc']; rfl)
    (((⟨2, by omega⟩ : Fin cols), (⟨0, by omega⟩ : Fin rows)) : Cell cols rows)
    (downWord rows t) (applicableFrom_downWord hN hm)
  rw [transEquiv_apply] at h
  rw [rightWord, h, Finset.mem_image] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hy' := traceSet_downWord_subset hN hm y hy
  rw [← hyx]
  simpa [transEquiv_apply] using hy'

/-- The column translation fixes every cell right of the window. -/
theorem permOf_rightWord_fixes_of_col_gt {rows cols t : ℕ} (hN : t + 2 < cols)
    (hm : 1 < rows) {x : Cell rows cols} (hx : t + 2 < x.2.val) :
    permOf (((⟨0, by omega⟩ : Fin rows), (⟨2, by omega⟩ : Fin cols)) : Cell rows cols)
        (rightWord rows t) x = x :=
  permOf_apply_of_not_mem_traceSet (fun hmem => by
    have := traceSet_rightWord_subset hN hm x hmem
    omega)

/-- **The scratch-row bound (transposed).**  The column translation fixes column `t + 1` — the
one immediately past the target — in every row except the scratch row `0`.  This is the
transpose of `permOf_downWord_row_add_one`; together with `permOf_rightWord` it gives the
precise corruption of a single-column translation: columns `0, …, t` are permuted, columns
`t + 1, t + 2` change only in row `0`, and the columns beyond are fixed. -/
theorem permOf_rightWord_fixes_of_col_add_one {rows cols t : ℕ} (hN : t + 2 < cols)
    (hm : 1 < rows) (r : Fin rows) (hr : 0 < r.val) :
    permOf (((⟨0, by omega⟩ : Fin rows), (⟨2, by omega⟩ : Fin cols)) : Cell rows cols)
        (rightWord rows t)
        (((r, (⟨t + 1, by omega⟩ : Fin cols))) : Cell rows cols)
      = (((r, (⟨t + 1, by omega⟩ : Fin cols))) : Cell rows cols) := by
  have h := permOf_map (transEquiv cols rows) transDir (neighbor?_transEquiv)
    (((⟨2, by omega⟩ : Fin cols), (⟨0, by omega⟩ : Fin rows)) : Cell cols rows)
    (downWord rows t)
  rw [transEquiv_apply] at h
  have h2 := congrArg (fun e : Equiv.Perm (Cell rows cols) =>
    e (transEquiv cols rows (((⟨t + 1, by omega⟩ : Fin cols), r) : Cell cols rows))) h
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply] at h2
  rw [permOf_downWord_row_add_one (N := cols) (m := rows) hN hm r hr] at h2
  simpa [rightWord, transEquiv_apply] using h2

/-- **The scratch-row bound (transposed), one column further.**  The column translation fixes
column `t + 2` in every row except the scratch row `0`. -/
theorem permOf_rightWord_fixes_of_col_add_two {rows cols t : ℕ} (hN : t + 2 < cols)
    (hm : 1 < rows) (r : Fin rows) (hr : 0 < r.val) :
    permOf (((⟨0, by omega⟩ : Fin rows), (⟨2, by omega⟩ : Fin cols)) : Cell rows cols)
        (rightWord rows t)
        (((r, (⟨t + 2, by omega⟩ : Fin cols))) : Cell rows cols)
      = (((r, (⟨t + 2, by omega⟩ : Fin cols))) : Cell rows cols) := by
  have h := permOf_map (transEquiv cols rows) transDir (neighbor?_transEquiv)
    (((⟨2, by omega⟩ : Fin cols), (⟨0, by omega⟩ : Fin rows)) : Cell cols rows)
    (downWord rows t)
  rw [transEquiv_apply] at h
  have h2 := congrArg (fun e : Equiv.Perm (Cell rows cols) =>
    e (transEquiv cols rows (((⟨t + 2, by omega⟩ : Fin cols), r) : Cell cols rows))) h
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply] at h2
  rw [permOf_downWord_row_add_two (N := cols) (m := rows) hN hm r hr] at h2
  simpa [rightWord, transEquiv_apply] using h2

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

/-- **Lemma 1 (transposed), rectangular block.**  On an `n × n` board, `rightWord H t` moves
the content of the block's first column to its `(t+1)`-st column. -/
theorem blockStrip_rightWord {n H M t ro co : ℕ} (hro : ro + H ≤ n) (hco : co + M ≤ n)
    (hM : t + 2 < M) (hH : 1 < H) (r : Fin H) :
    permOf (((⟨ro, by omega⟩ : Fin n), (⟨co + 2, by omega⟩ : Fin n)) : Cell n n)
        (rightWord H t)
        (((⟨ro + r.1, by omega⟩ : Fin n), (⟨co + t, by omega⟩ : Fin n)) : Cell n n)
      = (((⟨ro + r.1, by omega⟩ : Fin n), (⟨co, by omega⟩ : Fin n)) : Cell n n) := by
  have h := permOf_map_apply_of_neighbor_map
    (ι := blockStrip (n := n) H M ro co hro hco) (f := id)
    (blockStrip_injective hro hco) (blockStrip_neighbor hro hco)
    (((⟨0, by omega⟩ : Fin H), (⟨2, by omega⟩ : Fin M)) : Cell H M)
    (rightWord H t) (applicableFrom_rightWord hM hH)
    (x := ((r, (⟨t, by omega⟩ : Fin M))))
  simp only [List.map_id] at h
  rw [permOf_rightWord hM hH r] at h
  simpa [blockStrip] using h

/-- **Lemma 1 (transposed), rectangular block, board form.** -/
theorem blockStrip_rightWord_effect {n H M t ro co : ℕ} (hro : ro + H ≤ n)
    (hco : co + M ≤ n) (hM : t + 2 < M) (hH : 1 < H) [NeZero (n * n)] (B : Board n n)
    (hblank : blank B = (((⟨ro, by omega⟩ : Fin n), (⟨co + 2, by omega⟩ : Fin n)) : Cell n n))
    (r : Fin H) :
    actSeq B (rightWord H t)
        (((⟨ro + r.1, by omega⟩ : Fin n), (⟨co + t, by omega⟩ : Fin n)) : Cell n n)
      = B (((⟨ro + r.1, by omega⟩ : Fin n), (⟨co, by omega⟩ : Fin n)) : Cell n n) := by
  rw [actSeq_eq_permOf, hblank]
  change B (permOf (((⟨ro, by omega⟩ : Fin n), (⟨co + 2, by omega⟩ : Fin n)) : Cell n n)
      (rightWord H t)
      (((⟨ro + r.1, by omega⟩ : Fin n), (⟨co + t, by omega⟩ : Fin n)) : Cell n n))
    = B (((⟨ro + r.1, by omega⟩ : Fin n), (⟨co, by omega⟩ : Fin n)) : Cell n n)
  rw [blockStrip_rightWord hro hco hM hH r]

/-- The block translation never leaves columns `≤ co + t + 2` nor rows `[ro, ro+H)`. -/
theorem traceSet_blockStrip_rightWord {n H M t ro co : ℕ} (hro : ro + H ≤ n)
    (hco : co + M ≤ n) (hM : t + 2 < M) (hH : 1 < H) :
    ∀ x ∈ traceSet (((⟨ro, by omega⟩ : Fin n), (⟨co + 2, by omega⟩ : Fin n)) : Cell n n)
        (rightWord H t), x.2.val ≤ co + t + 2 ∧ ro ≤ x.1.val ∧ x.1.val < ro + H := by
  intro x hx
  have h := traceSet_map_eq_image (f := id) (blockStrip_injective hro hco)
    (blockStrip_neighbor hro hco)
    (((⟨0, by omega⟩ : Fin H), (⟨2, by omega⟩ : Fin M)) : Cell H M)
    (rightWord H t) (applicableFrom_rightWord hM hH)
  simp only [List.map_id] at h
  have hx' : x ∈ traceSet (blockStrip (n := n) H M ro co hro hco
      (((⟨0, by omega⟩ : Fin H), (⟨2, by omega⟩ : Fin M)) : Cell H M)) (rightWord H t) := hx
  rw [h, Finset.mem_image] at hx'
  obtain ⟨y, hy, hyx⟩ := hx'
  have hy' := traceSet_rightWord_subset hM hH y hy
  have hyrow : y.1.val < H := y.1.isLt
  rw [← hyx]
  simp only [blockStrip]
  omega

/-! ### The block column translation (Phase I step (iii))

`rightWord H t` translates a single column.  To translate a *block* of columns to the right we
apply `rightWord H t` to the columns from right to left, routing the blank back along a scratch
row.  The scratch row (`ro`) is corrupted, but the data rows (`ro+1, …, ro+H-1`) are preserved:
the scratch-row lemmas `permOf_rightWord_fixes_of_col_add_one/_two` show that the columns just
past the target are changed only in the scratch row, so the targets already produced by the
translations to the right survive.  This is the primitive Phase I step (iii) needs. -/

/-- **Single-column translation with a scratch row.**  Let `ro` be the scratch row and
`ro + 1, …, ro + H - 1` the data rows of a block starting at column `co`.  With the blank at
`(ro, co + 2)`, `rightWord H t` sends the content of column `co` to column `co + t`, changes
only the data-row cells of columns `co, …, co + t`, parks the blank at `(ro, co + t + 2)`, and
leaves the data-row cells of the two columns `co + t + 1`, `co + t + 2` (and of every column
`< co` or `> co + t + 2`) unchanged. -/
theorem blockRightWord_spec {n H t ro co : ℕ} (hro : ro + H ≤ n)
    (hco : co + t + 3 ≤ n) (hH : 1 < H)
    (B : Board n n) [NeZero (n * n)]
    (hblank : blank B = (((⟨ro, by omega⟩ : Fin n), (⟨co + 2, by omega⟩ : Fin n)) : Cell n n)) :
    (∀ (r : Fin n), ro ≤ r.val → r.val < ro + H →
        (actSeq B (rightWord H t)) (((r, (⟨co + t, by omega⟩ : Fin n))) : Cell n n)
          = B (((r, (⟨co, by omega⟩ : Fin n))) : Cell n n)) ∧
    (∀ z : Cell n n, ro + 1 ≤ z.1.val → z.1.val < ro + H →
        (z.2.val < co ∨ co + t < z.2.val) →
        (actSeq B (rightWord H t)) z = B z) ∧
    (blank (actSeq B (rightWord H t))
      = (((⟨ro, by omega⟩ : Fin n), (⟨co + t + 2, by omega⟩ : Fin n)) : Cell n n)) := by
  have hM : t + 2 < t + 3 := by omega
  have hco3 : co + (t + 3) ≤ n := hco
  have hinj : Function.Injective (blockStrip (n := n) H (t + 3) ro co hro hco3) :=
    blockStrip_injective hro hco3
  have hnb : ∀ (c : Cell H (t + 3)) (δ : Dir) (c' : Cell H (t + 3)),
      neighbor? c δ = some c' →
      neighbor? (blockStrip (n := n) H (t + 3) ro co hro hco3 c) δ
        = some (blockStrip H (t + 3) ro co hro hco3 c') :=
    blockStrip_neighbor hro hco3
  have hstart : blockStrip (n := n) H (t + 3) ro co hro hco3
      (((⟨0, by omega⟩ : Fin H), (⟨2, by omega⟩ : Fin (t + 3))) : Cell H (t + 3))
      = (((⟨ro, by omega⟩ : Fin n), (⟨co + 2, by omega⟩ : Fin n)) : Cell n n) := by
    apply Prod.ext <;> (apply Fin.ext <;> simp only [blockStrip, Fin.val_mk] <;> omega)
  have hred : ∀ (y : Cell H (t + 3)),
      permOf (((⟨ro, by omega⟩ : Fin n), (⟨co + 2, by omega⟩ : Fin n)) : Cell n n)
          (rightWord H t) (blockStrip (n := n) H (t + 3) ro co hro hco3 y)
        = blockStrip (n := n) H (t + 3) ro co hro hco3
            (permOf (((⟨0, by omega⟩ : Fin H), (⟨2, by omega⟩ : Fin (t + 3))) : Cell H (t + 3))
              (rightWord H t) y) := by
    intro y
    have h := permOf_map_apply_of_neighbor_map (ι := blockStrip (n := n) H (t + 3) ro co hro hco3)
      (f := id) hinj hnb
      (((⟨0, by omega⟩ : Fin H), (⟨2, by omega⟩ : Fin (t + 3))) : Cell H (t + 3))
      (rightWord H t) (applicableFrom_rightWord hM hH) (x := y)
    simp only [List.map_id, hstart] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · intro r hr1 hr2
    have hrH : r.val - ro < H := by omega
    have hloc : (((r, (⟨co + t, by omega⟩ : Fin n))) : Cell n n)
        = blockStrip (n := n) H (t + 3) ro co hro hco3
            ((⟨r.val - ro, hrH⟩ : Fin H), (⟨t, by omega⟩ : Fin (t + 3))) := by
      apply Prod.ext <;> (apply Fin.ext <;> simp only [blockStrip, Fin.val_mk] <;> omega)
    have hloc2 : blockStrip (n := n) H (t + 3) ro co hro hco3
        ((⟨r.val - ro, hrH⟩ : Fin H), (⟨0, by omega⟩ : Fin (t + 3)))
        = (((r, (⟨co, by omega⟩ : Fin n))) : Cell n n) := by
      apply Prod.ext <;> (apply Fin.ext <;> simp only [blockStrip, Fin.val_mk] <;> omega)
    rw [actSeq_eq_permOf, hblank, Equiv.trans_apply, hloc, hred,
      permOf_rightWord hM hH (⟨r.val - ro, hrH⟩ : Fin H), hloc2]
  · intro z hz1 hz2 hcond
    rw [actSeq_eq_permOf, hblank, Equiv.trans_apply]
    rcases hcond with hlt | hgt
    · -- column `< co`: outside the block
      have hnot : z ∉ Set.range (blockStrip (n := n) H (t + 3) ro co hro hco3) := by
        rintro ⟨y, hy⟩
        have hyc : z.2.val = co + y.2.val := by rw [← hy]; rfl
        omega
      have h := permOf_map_fixes_of_not_mem_range (f := id) hnb
        (((⟨0, by omega⟩ : Fin H), (⟨2, by omega⟩ : Fin (t + 3))) : Cell H (t + 3))
        (rightWord H t) (applicableFrom_rightWord hM hH) hnot
      rw [List.map_id, hstart] at h
      rw [h]
    · by_cases hzcol : z.2.val < co + (t + 3)
      · -- inside the block, local column `t+1` or `t+2`
        have hzH : z.1.val - ro < H := by omega
        have hzc : z.2.val - co < t + 3 := by omega
        have hloc : z = blockStrip (n := n) H (t + 3) ro co hro hco3
            ((⟨z.1.val - ro, hzH⟩ : Fin H), (⟨z.2.val - co, hzc⟩ : Fin (t + 3))) := by
          apply Prod.ext <;> (apply Fin.ext <;> simp only [blockStrip, Fin.val_mk] <;> omega)
        have hzr : 0 < z.1.val - ro := by omega
        have hfix : permOf (((⟨0, by omega⟩ : Fin H), (⟨2, by omega⟩ : Fin (t + 3))) :
            Cell H (t + 3)) (rightWord H t)
            ((⟨z.1.val - ro, hzH⟩ : Fin H), (⟨z.2.val - co, hzc⟩ : Fin (t + 3)))
          = ((⟨z.1.val - ro, hzH⟩ : Fin H), (⟨z.2.val - co, hzc⟩ : Fin (t + 3))) := by
          rcases (by omega : z.2.val - co = t + 1 ∨ z.2.val - co = t + 2) with hc | hc
          · have hthis : (⟨z.2.val - co, hzc⟩ : Fin (t + 3)) = (⟨t + 1, by omega⟩ : Fin (t + 3)) :=
              Fin.ext hc
            rw [hthis]
            exact permOf_rightWord_fixes_of_col_add_one hM hH
              (⟨z.1.val - ro, hzH⟩ : Fin H) hzr
          · have hthis : (⟨z.2.val - co, hzc⟩ : Fin (t + 3)) = (⟨t + 2, by omega⟩ : Fin (t + 3)) :=
              Fin.ext hc
            rw [hthis]
            exact permOf_rightWord_fixes_of_col_add_two hM hH
              (⟨z.1.val - ro, hzH⟩ : Fin H) hzr
        rw [hloc, hred, hfix]
      · -- column `> co + t + 2`: outside the block
        have hnot : z ∉ Set.range (blockStrip (n := n) H (t + 3) ro co hro hco3) := by
          rintro ⟨y, hy⟩
          have hyc : z.2.val = co + y.2.val := by rw [← hy]; rfl
          have := y.2.isLt
          omega
        have h := permOf_map_fixes_of_not_mem_range (f := id) hnb
          (((⟨0, by omega⟩ : Fin H), (⟨2, by omega⟩ : Fin (t + 3))) : Cell H (t + 3))
          (rightWord H t) (applicableFrom_rightWord hM hH) hnot
        rw [List.map_id, hstart] at h
        rw [h]
  · have htr := trace_map_of_neighbor_map (ι := blockStrip (n := n) H (t + 3) ro co hro hco3)
      (f := id) hnb
      (((⟨0, by omega⟩ : Fin H), (⟨2, by omega⟩ : Fin (t + 3))) : Cell H (t + 3))
      (rightWord H t) (applicableFrom_rightWord hM hH)
    simp only [List.map_id] at htr
    rw [hstart] at htr
    rw [trace_rightWord (rows := H) (cols := t + 3) (t := t) hM hH] at htr
    have hend : blockStrip (n := n) H (t + 3) ro co hro hco3
        (((⟨0, by omega⟩ : Fin H), (⟨t + 2, by omega⟩ : Fin (t + 3))) : Cell H (t + 3))
        = (((⟨ro, by omega⟩ : Fin n), (⟨co + t + 2, by omega⟩ : Fin n)) : Cell n n) := by
      apply Prod.ext <;> (apply Fin.ext <;> simp only [blockStrip, Fin.val_mk] <;> omega)
    rw [hend] at htr
    rw [blank_actSeq, hblank, htr]

/-- A horizontal run `R^i` fixes every cell outside its row. -/
theorem permOf_replicate_R_fixes {n m : ℕ} (r : Fin n) (i : ℕ) (j : Fin m) :
    ∀ z : Cell n m, z.1 ≠ r → permOf (r, j) (List.replicate i Dir.R) z = z := by
  induction i generalizing j with
  | zero => intro z _; simp
  | succ i ih =>
      intro z hz
      rw [List.replicate_succ]
      by_cases hj : 0 < j.val
      · have hstep : neighbor? (r, j) Dir.R = some (r, ⟨j.val - 1, by omega⟩) := by
          simp only [neighbor?]; rw [if_pos hj]
        rw [permOf_cons_of_neighbor? hstep, Equiv.Perm.mul_apply,
          ih (⟨j.val - 1, by omega⟩) z hz]
        have hz1 : z ≠ (r, j) := fun h => hz (by rw [h])
        have hz2 : z ≠ (r, ⟨j.val - 1, by omega⟩) := fun h => hz (by rw [h])
        exact Equiv.swap_apply_of_ne_of_ne hz1 hz2
      · have hnone : neighbor? (r, j) Dir.R = none := by
          simp only [neighbor?]; rw [if_neg hj]
        rw [permOf_cons_of_neighbor?_eq_none hnone]
        exact ih j z hz

/-- The word translating a block of `K` columns to the right by `t`.  The columns are processed
from right to left and the blank is routed back along the scratch row. -/
def blockColWord (H t : ℕ) : ℕ → List Dir
  | 0 => []
  | K + 1 => rightWord H t ++ List.replicate (t + 1) Dir.R ++ blockColWord H t K

/-- The trace of the transported single-column translation. -/
theorem trace_blockRightWord {n H t ro co : ℕ} (hro : ro + H ≤ n)
    (hco : co + t + 3 ≤ n) (hH : 1 < H) :
    trace (((⟨ro, by omega⟩ : Fin n), (⟨co + 2, by omega⟩ : Fin n)) : Cell n n)
        (rightWord H t)
      = (((⟨ro, by omega⟩ : Fin n), (⟨co + t + 2, by omega⟩ : Fin n)) : Cell n n) := by
  have hM : t + 2 < t + 3 := by omega
  have h := trace_map_of_neighbor_map
    (ι := blockStrip (n := n) H (t + 3) ro co hro (by omega))
    (f := id) (blockStrip_neighbor hro (by omega))
    (((⟨0, by omega⟩ : Fin H), (⟨2, by omega⟩ : Fin (t + 3))) : Cell H (t + 3))
    (rightWord H t) (applicableFrom_rightWord hM hH)
  simp only [List.map_id] at h
  rw [trace_rightWord (rows := H) (cols := t + 3) (t := t) hM hH] at h
  have hstart : blockStrip (n := n) H (t + 3) ro co hro (by omega)
      (((⟨0, by omega⟩ : Fin H), (⟨2, by omega⟩ : Fin (t + 3))) : Cell H (t + 3))
      = (((⟨ro, by omega⟩ : Fin n), (⟨co + 2, by omega⟩ : Fin n)) : Cell n n) := by
    apply Prod.ext <;> (apply Fin.ext <;> simp only [blockStrip, Fin.val_mk] <;> omega)
  have hend : blockStrip (n := n) H (t + 3) ro co hro (by omega)
      (((⟨0, by omega⟩ : Fin H), (⟨t + 2, by omega⟩ : Fin (t + 3))) : Cell H (t + 3))
      = (((⟨ro, by omega⟩ : Fin n), (⟨co + t + 2, by omega⟩ : Fin n)) : Cell n n) := by
    apply Prod.ext <;> (apply Fin.ext <;> simp only [blockStrip, Fin.val_mk] <;> omega)
  rw [hstart, hend] at h
  exact h

/-- The block column translation parks the blank at `(ro, co + 1)`, which is exactly the
starting position of the translation of the next block to the left. -/
theorem trace_blockColWord {n H K t ro co : ℕ} (hro : ro + H ≤ n) (hH : 1 < H)
    (hco : co + K + t + 3 ≤ n) :
    trace (((⟨ro, by omega⟩ : Fin n), (⟨co + K + 1, by omega⟩ : Fin n)) : Cell n n)
        (blockColWord H t K)
      = (((⟨ro, by omega⟩ : Fin n), (⟨co + 1, by omega⟩ : Fin n)) : Cell n n) := by
  induction K with
  | zero => rw [blockColWord, trace_nil]
  | succ K ih =>
      have hcoK : co + K + t + 3 ≤ n := by omega
      rw [show blockColWord H t (K + 1)
          = rightWord H t ++ List.replicate (t + 1) Dir.R ++ blockColWord H t K from rfl,
        List.append_assoc, trace_append, trace_append]
      rw [show (⟨co + (K + 1) + 1, by omega⟩ : Fin n)
          = (⟨co + K + 2, by omega⟩ : Fin n) from Fin.ext (by simp only [Fin.val_mk]; omega)]
      rw [trace_blockRightWord (ro := ro) (co := co + K) hro (by omega) hH,
        trace_replicate_right ro (t + 1) (co + K + t + 2) (by omega) (by omega) (by omega)]
      rw [show (⟨co + K + t + 2 - (t + 1), by omega⟩ : Fin n)
          = (⟨co + K + 1, by omega⟩ : Fin n) from Fin.ext (by simp only [Fin.val_mk]; omega)]
      exact ih hcoK

/-- **Block column translation (Phase I step (iii)).**  Let `ro` be the scratch row and
`ro + 1, …, ro + H - 1` the data rows.  With the blank at `(ro, co + K + 1)`, the word
`blockColWord H t K` sends the content of the source column `co + j` (data rows) to the target
column `co + t + j` for every `j < K`, and fixes every data-row cell outside the columns
`[co, co + t + K)`.  The scratch row `ro` is corrupted. -/
theorem blockColWord_spec {n H K t ro co : ℕ} (hro : ro + H ≤ n)
    (hH : 1 < H) (hco : co + K + t + 3 ≤ n) :
    ∀ (B : Board n n) [NeZero (n * n)]
      (hblank : blank B
        = (((⟨ro, by omega⟩ : Fin n), (⟨co + K + 1, by omega⟩ : Fin n)) : Cell n n)),
    (∀ (j : ℕ) (hj : j < K) (r : Fin n), ro + 1 ≤ r.val → r.val < ro + H →
        (actSeq B (blockColWord H t K)) (((r, (⟨co + t + j, by omega⟩ : Fin n))) : Cell n n)
          = B (((r, (⟨co + j, by omega⟩ : Fin n))) : Cell n n)) ∧
    (∀ z : Cell n n, ro + 1 ≤ z.1.val → z.1.val < ro + H →
        (z.2.val < co ∨ co + t + K ≤ z.2.val) →
        (actSeq B (blockColWord H t K)) z = B z) := by
  induction K with
  | zero =>
      intro B _ hblank
      refine ⟨?_, ?_⟩
      · intro j hj; omega
      · intro z _ _ _; rw [blockColWord, actSeq_nil]
  | succ K ih =>
      intro B _ hblank
      have hcoK : co + K + t + 3 ≤ n := by omega
      have hblankB : blank B
          = (((⟨ro, by omega⟩ : Fin n), (⟨co + K + 2, by omega⟩ : Fin n)) : Cell n n) := by
        rw [hblank]
        apply Prod.ext
        · rfl
        · apply Fin.ext; simp only [Fin.val_mk]; omega
      obtain ⟨hmove, hfix, hblank1⟩ :=
        blockRightWord_spec (n := n) (H := H) (t := t) (ro := ro) (co := co + K)
          hro (by omega) hH B hblankB
      set B₁ : Board n n := actSeq B (rightWord H t) with hB₁
      have hblank2 : blank (actSeq B₁ (List.replicate (t + 1) Dir.R))
          = (((⟨ro, by omega⟩ : Fin n), (⟨co + K + 1, by omega⟩ : Fin n)) : Cell n n) := by
        rw [blank_actSeq, hblank1,
          trace_replicate_right ro (t + 1) (co + K + t + 2) (by omega) (by omega) (by omega)]
        apply Prod.ext
        · rfl
        · apply Fin.ext; simp only [Fin.val_mk]; omega
      set B₂ : Board n n := actSeq B₁ (List.replicate (t + 1) Dir.R) with hB₂
      obtain ⟨ihmove, ihfix⟩ := ih hcoK B₂ hblank2
      have hρfix : ∀ z : Cell n n, z.1 ≠ (⟨ro, by omega⟩ : Fin n) →
          (actSeq B₁ (List.replicate (t + 1) Dir.R)) z = B₁ z := by
        intro z hz
        rw [actSeq_eq_permOf, hblank1, Equiv.trans_apply,
          permOf_replicate_R_fixes (⟨ro, by omega⟩ : Fin n) (t + 1)
            (⟨co + K + t + 2, by omega⟩ : Fin n) z hz]
      have hword : blockColWord H t (K + 1)
          = rightWord H t ++ List.replicate (t + 1) Dir.R ++ blockColWord H t K := rfl
      have hcomp : ∀ z : Cell n n,
          (actSeq B (blockColWord H t (K + 1))) z = (actSeq B₂ (blockColWord H t K)) z := by
        intro z
        rw [hword, List.append_assoc, actSeq_append, actSeq_append]
      have hne : ∀ z : Cell n n, ro + 1 ≤ z.1.val → z.1 ≠ (⟨ro, by omega⟩ : Fin n) := by
        intro z hz h
        have hv := congrArg Fin.val h
        simp only [Fin.val_mk] at hv
        omega
      refine ⟨?_, ?_⟩
      · intro j hj r hr1 hr2
        rw [hcomp]
        by_cases hjK : j < K
        · have hmv := ihmove j hjK r hr1 hr2
          have hρz := hρfix (((r, (⟨co + j, by omega⟩ : Fin n))) : Cell n n)
            (hne _ hr1)
          rw [hmv, hB₂, hρz, hB₁]
          exact hfix _ hr1 hr2 (Or.inl (by simp only [Prod.snd, Fin.val_mk]; omega))
        · have hjK' : j = K := by omega
          subst j
          have hfix2 := ihfix (((r, (⟨co + t + K, by omega⟩ : Fin n))) : Cell n n) hr1 hr2
            (Or.inr (by simp only [Prod.snd, Fin.val_mk]; omega))
          have hmv := hmove r (by omega) hr2
          have hρz := hρfix (((r, (⟨co + t + K, by omega⟩ : Fin n))) : Cell n n)
            (hne _ hr1)
          rw [hfix2, hB₂, hρz, hB₁]
          convert hmv using 2 <;>
            (apply Prod.ext <;> (apply Fin.ext <;> simp only [Fin.val_mk] <;> omega))
      · intro z hz1 hz2 hcond
        rw [hcomp]
        have hρz := hρfix z (hne z hz1)
        rcases hcond with hlt | hge
        · have hfix2 := ihfix z hz1 hz2 (Or.inl hlt)
          rw [hfix2, hB₂, hρz, hB₁]
          exact hfix z hz1 hz2 (Or.inl (by omega))
        · have hfix2 := ihfix z hz1 hz2 (Or.inr (by omega))
          rw [hfix2, hB₂, hρz, hB₁]
          exact hfix z hz1 hz2 (Or.inr (by omega))

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

/-- The block translation is applicable from the block's `(2,0)` corner. -/
theorem applicableFrom_blockStrip_downWord {n H M t ro co : ℕ} (hro : ro + H ≤ n)
    (hco : co + M ≤ n) (hHt : t + 2 < H) (hM : 1 < M) :
    ApplicableFrom (((⟨ro + 2, by omega⟩ : Fin n), (⟨co, by omega⟩ : Fin n)) : Cell n n)
      (downWord M t) := by
  have h := applicableFrom_map_of_neighbor_map (ι := blockStrip (n := n) H M ro co hro hco)
    (f := id) (blockStrip_neighbor hro hco)
    (applicableFrom_downWord (N := H) (m := M) hHt hM)
  simpa [blockStrip] using h

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

/-- The block translation fixes every cell below the window. -/
theorem blockStrip_downWord_fixes_of_row_gt {n H M t ro co : ℕ} (hro : ro + H ≤ n)
    (hco : co + M ≤ n) (hHt : t + 2 < H) (hM : 1 < M)
    {x : Cell n n} (hx : ro + t + 2 < x.1.val) :
    permOf (((⟨ro + 2, by omega⟩ : Fin n), (⟨co, by omega⟩ : Fin n)) : Cell n n)
        (downWord M t) x = x :=
  permOf_apply_of_not_mem_traceSet (fun hmem => by
    have := (traceSet_blockStrip_downWord hro hco hHt hM x hmem).1
    omega)

end Zhong
