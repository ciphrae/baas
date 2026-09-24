/-
Copyright (c) 2026 The Zhong formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Zhong formalisation contributors
-/
import Zhong.Algorithm.Lift

/-!
# All orientations of the jump on a `2 × m` strip

`Algorithm/Jump.lean`, `Algorithm/Orient.lean` and `Algorithm/JumpRow.lean` give the jump
(Lemma 2 of Zhong 2023) in the following orientations of a `2 × m` board, where the blank
is at `top c` (row `0`, column `c`) or `bot c` (row `1`, column `c`):

* `jumpWord l`      : `top c → bot (c + 2l)`            (adjacent row, right, even offset)
* `reflJumpWord l`  : `top c → bot (c - 2l)`            (adjacent row, left, even offset)
* `flipJumpWord l`  : `bot c → top (c + 2l)`            (adjacent row, right, even offset)
* `row0Word l`      : `top c → top (c + 2l + 1)`        (same row, right, odd offset)

This file supplies the remaining four orientations by transporting along the board
symmetries of `Algorithm/Orient.lean`:

* `flipReflJumpWord l` : `bot c → top (c - 2l)`         (adjacent row, left, even offset)
* `reflRow0Word l`     : `top c → top (c - 2l - 1)`     (same row, left, odd offset)
* `flipRow0Word l`     : `bot c → bot (c + 2l + 1)`     (same row, right, odd offset)
* `flipReflRow0Word l` : `bot c → bot (c - 2l - 1)`     (same row, left, odd offset)

Together they show that, inside a `2 × m` strip, the blank can jump to *any* cell of the
opposite colour of the checkerboard (`strip_jump`), which is the primitive used by the
tile-by-tile placement routine of Parberry's algorithm.
-/

namespace Zhong

open Equiv

variable {m : ℕ}

/-! ### The reflected/flipped words -/

/-- The row-swapped, column-reflected jump word. -/
def flipReflJumpWord (l : ℕ) : List Dir := (reflJumpWord l).map flipDir

/-- The column-reflected same-row jump word. -/
def reflRow0Word (l : ℕ) : List Dir := (row0Word l).map reflDir

/-- The row-swapped same-row jump word. -/
def flipRow0Word (l : ℕ) : List Dir := (row0Word l).map flipDir

/-- The row-swapped, column-reflected same-row jump word. -/
def flipReflRow0Word (l : ℕ) : List Dir := (reflRow0Word l).map flipDir

/-! ### Their effects -/

/-- **Lemma 2, blank in row `1`, target to the left.**  On a `2 × m` board with the blank
at `(1, c)`, the word `flipReflJumpWord l` swaps the blank with the tile at `(0, c - 2l)`. -/
theorem permOf_flipReflJumpWord {c : Fin m} (l : ℕ) (hc : 2 * l ≤ c.val) :
    permOf (bot c) (flipReflJumpWord l)
      = Equiv.swap (bot c) (top (⟨c.val - 2 * l, by omega⟩ : Fin m)) := by
  have h := permOf_map (rowSwap2 m) flipDir (neighbor?_rowSwap2) (top c) (reflJumpWord l)
  rw [permOf_reflJumpWord l hc] at h
  have htop : rowSwap2 m (top c) = bot c := by
    simp [top, bot, rowSwap2_apply, Fin.rev_zero, Fin.last]
  have hbot : rowSwap2 m (bot (⟨c.val - 2 * l, by omega⟩ : Fin m))
      = top (⟨c.val - 2 * l, by omega⟩ : Fin m) := by
    have h1 : (1 : Fin 2).rev = 0 := by decide
    simp [top, bot, rowSwap2_apply, h1]
  rw [permCongr_swap, htop, hbot] at h
  simpa [flipReflJumpWord] using h

/-- **Lemma 2, same row, target to the left.**  On a `2 × m` board with the blank at
`(0, c)`, the word `reflRow0Word l` swaps the blank with the tile at `(0, c - (2l+1))`. -/
theorem permOf_reflRow0Word {c : Fin m} (l : ℕ) (hc : 2 * l + 1 ≤ c.val) :
    permOf (top c) (reflRow0Word l)
      = Equiv.swap (top c) (top (⟨c.val - (2 * l + 1), by omega⟩ : Fin m)) := by
  have hcle : (c.rev).val + 2 * l + 1 < m := by rw [Fin.val_rev]; omega
  have h := permOf_map (colRefl 2 m) reflDir (neighbor?_colRefl) (top c.rev) (row0Word l)
  rw [permOf_row0Word l hcle] at h
  have htop : colRefl 2 m (top c.rev) = top c := by
    simp [top, colRefl_apply, Fin.rev_rev]
  have hbot : colRefl 2 m (top (⟨(c.rev).val + 2 * l + 1, hcle⟩ : Fin m))
      = top (⟨c.val - (2 * l + 1), by omega⟩ : Fin m) := by
    simp only [colRefl_apply, top, Prod.mk.injEq, true_and]
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  rw [permCongr_swap, htop, hbot] at h
  simpa [reflRow0Word] using h

/-- **Lemma 2, same row of the lower row, to the right.**  On a `2 × m` board with the
blank at `(1, c)`, the word `flipRow0Word l` swaps the blank with the tile at
`(1, c + (2l+1))`. -/
theorem permOf_flipRow0Word {c : Fin m} (l : ℕ) (hc : c.val + 2 * l + 1 < m) :
    permOf (bot c) (flipRow0Word l)
      = Equiv.swap (bot c) (bot (⟨c.val + 2 * l + 1, hc⟩ : Fin m)) := by
  have h := permOf_map (rowSwap2 m) flipDir (neighbor?_rowSwap2) (top c) (row0Word l)
  rw [permOf_row0Word l hc] at h
  have htop : rowSwap2 m (top c) = bot c := by
    simp [top, bot, rowSwap2_apply, Fin.rev_zero, Fin.last]
  have hbot : rowSwap2 m (top (⟨c.val + 2 * l + 1, hc⟩ : Fin m))
      = bot (⟨c.val + 2 * l + 1, hc⟩ : Fin m) := by
    simp [top, bot, rowSwap2_apply]
  rw [permCongr_swap, htop, hbot] at h
  simpa [flipRow0Word] using h

/-- **Lemma 2, same row of the lower row, to the left.**  On a `2 × m` board with the blank
at `(1, c)`, the word `flipReflRow0Word l` swaps the blank with the tile at
`(1, c - (2l+1))`. -/
theorem permOf_flipReflRow0Word {c : Fin m} (l : ℕ) (hc : 2 * l + 1 ≤ c.val) :
    permOf (bot c) (flipReflRow0Word l)
      = Equiv.swap (bot c) (bot (⟨c.val - (2 * l + 1), by omega⟩ : Fin m)) := by
  have h := permOf_map (rowSwap2 m) flipDir (neighbor?_rowSwap2) (top c) (reflRow0Word l)
  rw [permOf_reflRow0Word l hc] at h
  have htop : rowSwap2 m (top c) = bot c := by
    simp [top, bot, rowSwap2_apply, Fin.rev_zero, Fin.last]
  have hbot : rowSwap2 m (top (⟨c.val - (2 * l + 1), by omega⟩ : Fin m))
      = bot (⟨c.val - (2 * l + 1), by omega⟩ : Fin m) := by
    simp [top, bot, rowSwap2_apply]
  rw [permCongr_swap, htop, hbot] at h
  simpa [flipReflRow0Word] using h

/-! ### Applicability -/

/-- Applicability of the row-swapped, column-reflected jump. -/
theorem applicableFrom_flipReflJumpWord {c : Fin m} (l : ℕ) (hc : 2 * l ≤ c.val) :
    ApplicableFrom (bot c) (flipReflJumpWord l) := by
  have h := applicableFrom_map_of_neighbor_map (ι := rowSwap2 m) (f := flipDir)
    (fun c δ c' hc' => by rw [neighbor?_rowSwap2, hc']; rfl)
    (applicableFrom_reflJumpWord (m := m) l hc)
  have htop : rowSwap2 m (top c) = bot c := by
    simp [top, bot, rowSwap2_apply, Fin.rev_zero, Fin.last]
  simpa [flipReflJumpWord, htop] using h

/-- Applicability of the column-reflected same-row jump. -/
theorem applicableFrom_reflRow0Word {c : Fin m} (l : ℕ) (hc : 2 * l + 1 ≤ c.val) :
    ApplicableFrom (top c) (reflRow0Word l) := by
  have hcle : (c.rev).val + 2 * l + 1 < m := by rw [Fin.val_rev]; omega
  have h := applicableFrom_map_of_neighbor_map (ι := colRefl 2 m) (f := reflDir)
    (fun c δ c' hc' => by rw [neighbor?_colRefl, hc']; rfl)
    (applicableFrom_row0Word (m := m) l hcle)
  have htop : colRefl 2 m (top c.rev) = top c := by
    simp [top, colRefl_apply, Fin.rev_rev]
  simpa [reflRow0Word, htop] using h

/-- Applicability of the row-swapped same-row jump. -/
theorem applicableFrom_flipRow0Word {c : Fin m} (l : ℕ) (hc : c.val + 2 * l + 1 < m) :
    ApplicableFrom (bot c) (flipRow0Word l) := by
  have h := applicableFrom_map_of_neighbor_map (ι := rowSwap2 m) (f := flipDir)
    (fun c δ c' hc' => by rw [neighbor?_rowSwap2, hc']; rfl)
    (applicableFrom_row0Word (m := m) l hc)
  have htop : rowSwap2 m (top c) = bot c := by
    simp [top, bot, rowSwap2_apply, Fin.rev_zero, Fin.last]
  simpa [flipRow0Word, htop] using h

/-- Applicability of the row-swapped, column-reflected same-row jump. -/
theorem applicableFrom_flipReflRow0Word {c : Fin m} (l : ℕ) (hc : 2 * l + 1 ≤ c.val) :
    ApplicableFrom (bot c) (flipReflRow0Word l) := by
  have h := applicableFrom_map_of_neighbor_map (ι := rowSwap2 m) (f := flipDir)
    (fun c δ c' hc' => by rw [neighbor?_rowSwap2, hc']; rfl)
    (applicableFrom_reflRow0Word (m := m) l hc)
  have htop : rowSwap2 m (top c) = bot c := by
    simp [top, bot, rowSwap2_apply, Fin.rev_zero, Fin.last]
  simpa [flipReflRow0Word, htop] using h

/-! ### Board forms -/

/-- **Lemma 2, blank in row `1`, target to the left, board form.** -/
theorem flipReflJumpWord_effect {c : Fin m} (l : ℕ) (hc : 2 * l ≤ c.val)
    [NeZero (2 * m)] (B : Board 2 m) (hblank : blank B = bot c) :
    actSeq B (flipReflJumpWord l)
      = (Equiv.swap (bot c) (top (⟨c.val - 2 * l, by omega⟩ : Fin m))).trans B := by
  rw [actSeq_eq_permOf, hblank, permOf_flipReflJumpWord l hc]

/-- **Lemma 2, same row, target to the left, board form.** -/
theorem reflRow0Word_effect {c : Fin m} (l : ℕ) (hc : 2 * l + 1 ≤ c.val)
    [NeZero (2 * m)] (B : Board 2 m) (hblank : blank B = top c) :
    actSeq B (reflRow0Word l)
      = (Equiv.swap (top c) (top (⟨c.val - (2 * l + 1), by omega⟩ : Fin m))).trans B := by
  rw [actSeq_eq_permOf, hblank, permOf_reflRow0Word l hc]

/-- **Lemma 2, lower row, to the right, board form.** -/
theorem flipRow0Word_effect {c : Fin m} (l : ℕ) (hc : c.val + 2 * l + 1 < m)
    [NeZero (2 * m)] (B : Board 2 m) (hblank : blank B = bot c) :
    actSeq B (flipRow0Word l)
      = (Equiv.swap (bot c) (bot (⟨c.val + 2 * l + 1, hc⟩ : Fin m))).trans B := by
  rw [actSeq_eq_permOf, hblank, permOf_flipRow0Word l hc]

/-- **Lemma 2, lower row, to the left, board form.** -/
theorem flipReflRow0Word_effect {c : Fin m} (l : ℕ) (hc : 2 * l + 1 ≤ c.val)
    [NeZero (2 * m)] (B : Board 2 m) (hblank : blank B = bot c) :
    actSeq B (flipReflRow0Word l)
      = (Equiv.swap (bot c) (bot (⟨c.val - (2 * l + 1), by omega⟩ : Fin m))).trans B := by
  rw [actSeq_eq_permOf, hblank, permOf_flipReflRow0Word l hc]

/-! ### Lengths -/

@[simp] theorem flipReflJumpWord_length (l : ℕ) :
    (flipReflJumpWord l).length = 20 * l + 1 := by
  simp [flipReflJumpWord, reflJumpWord_length]

@[simp] theorem reflRow0Word_length (l : ℕ) : (reflRow0Word l).length = 24 * l + 1 := by
  simp [reflRow0Word, row0Word_length]

@[simp] theorem flipRow0Word_length (l : ℕ) : (flipRow0Word l).length = 24 * l + 1 := by
  simp [flipRow0Word, row0Word_length]

@[simp] theorem flipReflRow0Word_length (l : ℕ) :
    (flipReflRow0Word l).length = 24 * l + 1 := by
  simp [flipReflRow0Word, reflRow0Word_length]

/-! ### Jumping to any cell of the opposite colour -/

/-- **Jumping anywhere in a strip.**  On a `2 × m` board, if the blank at `p` and the target
`q` lie on opposite colours of the checkerboard, there is an `O(m)`-move word that swaps the
blank with the tile at `q`. -/
theorem strip_jump {p q : Cell 2 m}
    (h : (p.1.val + p.2.val + q.1.val + q.2.val) % 2 = 1) :
    ∃ σ : List Dir, ApplicableFrom p σ ∧ permOf p σ = Equiv.swap p q
      ∧ σ.length ≤ 12 * m + 1 := by
  obtain ⟨pr, pc⟩ := p
  obtain ⟨qr, qc⟩ := q
  have hpr : pr = 0 ∨ pr = 1 := by fin_cases pr <;> simp
  have hqr : qr = 0 ∨ qr = 1 := by fin_cases qr <;> simp
  rcases hpr with rfl | rfl <;> rcases hqr with rfl | rfl
  · -- top pc → top qc: same row, odd offset
    simp only [Fin.val_zero, Nat.zero_add] at h
    have hne : pc.val ≠ qc.val := by omega
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hb : pc.val + 2 * ((qc.val - pc.val - 1) / 2) + 1 < m := by omega
      have hq : pc.val + 2 * ((qc.val - pc.val - 1) / 2) + 1 = qc.val := by omega
      refine ⟨row0Word ((qc.val - pc.val - 1) / 2),
        applicableFrom_row0Word _ hb, ?_, ?_⟩
      · rw [permOf_row0Word _ hb]; congr 1
        exact Prod.ext rfl (Fin.ext hq)
      · rw [row0Word_length]; omega
    · have hb : 2 * ((pc.val - qc.val - 1) / 2) + 1 ≤ pc.val := by omega
      have hq : pc.val - (2 * ((pc.val - qc.val - 1) / 2) + 1) = qc.val := by omega
      refine ⟨reflRow0Word ((pc.val - qc.val - 1) / 2),
        applicableFrom_reflRow0Word _ hb, ?_, ?_⟩
      · rw [permOf_reflRow0Word _ hb]; congr 1
        exact Prod.ext rfl (Fin.ext hq)
      · rw [reflRow0Word_length]; omega
  · -- top pc → bot qc: adjacent row, even offset
    simp only [Fin.val_zero, Fin.val_one, Nat.zero_add] at h
    rcases le_or_gt pc.val qc.val with hle | hlt
    · have hb : pc.val + 2 * ((qc.val - pc.val) / 2) < m := by omega
      have hq : pc.val + 2 * ((qc.val - pc.val) / 2) = qc.val := by omega
      refine ⟨jumpWord ((qc.val - pc.val) / 2),
        applicableFrom_jumpWord _ hb, ?_, ?_⟩
      · rw [permOf_jumpWord _ hb]; congr 1
        exact Prod.ext rfl (Fin.ext hq)
      · rw [jumpWord_length]; omega
    · have hb : 2 * ((pc.val - qc.val) / 2) ≤ pc.val := by omega
      have hq : pc.val - 2 * ((pc.val - qc.val) / 2) = qc.val := by omega
      refine ⟨reflJumpWord ((pc.val - qc.val) / 2),
        applicableFrom_reflJumpWord _ hb, ?_, ?_⟩
      · rw [permOf_reflJumpWord _ hb]; congr 1
        exact Prod.ext rfl (Fin.ext hq)
      · rw [reflJumpWord_length]; omega
  · -- bot pc → top qc: adjacent row, even offset
    simp only [Fin.val_zero, Fin.val_one] at h
    rcases le_or_gt pc.val qc.val with hle | hlt
    · have hb : pc.val + 2 * ((qc.val - pc.val) / 2) < m := by omega
      have hq : pc.val + 2 * ((qc.val - pc.val) / 2) = qc.val := by omega
      refine ⟨flipJumpWord ((qc.val - pc.val) / 2),
        applicableFrom_flipJumpWord _ hb, ?_, ?_⟩
      · rw [permOf_flipJumpWord _ hb]; congr 1
        exact Prod.ext rfl (Fin.ext hq)
      · rw [flipJumpWord_length]; omega
    · have hb : 2 * ((pc.val - qc.val) / 2) ≤ pc.val := by omega
      have hq : pc.val - 2 * ((pc.val - qc.val) / 2) = qc.val := by omega
      refine ⟨flipReflJumpWord ((pc.val - qc.val) / 2),
        applicableFrom_flipReflJumpWord _ hb, ?_, ?_⟩
      · rw [permOf_flipReflJumpWord _ hb]; congr 1
        exact Prod.ext rfl (Fin.ext hq)
      · rw [flipReflJumpWord_length]; omega
  · -- bot pc → bot qc: same row, odd offset
    simp only [Fin.val_one] at h
    have hne : pc.val ≠ qc.val := by omega
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hb : pc.val + 2 * ((qc.val - pc.val - 1) / 2) + 1 < m := by omega
      have hq : pc.val + 2 * ((qc.val - pc.val - 1) / 2) + 1 = qc.val := by omega
      refine ⟨flipRow0Word ((qc.val - pc.val - 1) / 2),
        applicableFrom_flipRow0Word _ hb, ?_, ?_⟩
      · rw [permOf_flipRow0Word _ hb]; congr 1
        exact Prod.ext rfl (Fin.ext hq)
      · rw [flipRow0Word_length]; omega
    · have hb : 2 * ((pc.val - qc.val - 1) / 2) + 1 ≤ pc.val := by omega
      have hq : pc.val - (2 * ((pc.val - qc.val - 1) / 2) + 1) = qc.val := by omega
      refine ⟨flipReflRow0Word ((pc.val - qc.val - 1) / 2),
        applicableFrom_flipReflRow0Word _ hb, ?_, ?_⟩
      · rw [permOf_flipReflRow0Word _ hb]; congr 1
        exact Prod.ext rfl (Fin.ext hq)
      · rw [flipReflRow0Word_length]; omega

/-! ### Composing jumps into chains

A chain of jumps `p → x → y` composes to the three-cycle `p → y → x` of *positions*; a
chain `p → u → v → w → p` composes to the three-cycle `u → w → v` of positions.  Since the
content of a cell moves to its image under the induced permutation, the four-chain moves
the content `u → w`, `w → v`, `v → u`. -/

/-- Two consecutive jumps compose to a three-cycle of positions. -/
theorem permOf_two_jumps {p x y : Cell 2 m} (σ₁ σ₂ : List Dir)
    (h₁ : permOf p σ₁ = Equiv.swap p x) (t₁ : trace p σ₁ = x)
    (h₂ : permOf x σ₂ = Equiv.swap x y) :
    permOf p (σ₁ ++ σ₂) = Equiv.swap p x * Equiv.swap x y := by
  rw [permOf_append, h₁, t₁, h₂]

/-- Four consecutive jumps composing to a closed chain `p → u → v → w → p` give the
three-cycle `u → w → v` of positions. -/
theorem permOf_four_jumps {p u v w : Cell 2 m} (σ₁ σ₂ σ₃ σ₄ : List Dir)
    (h₁ : permOf p σ₁ = Equiv.swap p u) (t₁ : trace p σ₁ = u)
    (h₂ : permOf u σ₂ = Equiv.swap u v) (t₂ : trace u σ₂ = v)
    (h₃ : permOf v σ₃ = Equiv.swap v w) (t₃ : trace v σ₃ = w)
    (h₄ : permOf w σ₄ = Equiv.swap w p) :
    permOf p (((σ₁ ++ σ₂) ++ σ₃) ++ σ₄)
      = Equiv.swap p u * Equiv.swap u v * Equiv.swap v w * Equiv.swap w p := by
  simp only [permOf_append, trace_append, h₁, t₁, h₂, t₂, h₃, t₃, h₄]

/-- The trace of a jump word is its target. -/
theorem trace_eq_of_permOf_swap {p q : Cell 2 m} {σ : List Dir}
    (h : permOf p σ = Equiv.swap p q) : trace p σ = q := by
  rw [← permOf_symm_apply p σ, h]
  simp

/-! ### The two-jump placement (case `A = P ≠ C`) -/

/-- If the blank at `p` can jump to `c` and `c` can jump to `a`, then the chain `p → c → a`
moves the content of `a` to `c`. -/
theorem strip_place_two {p c a : Cell 2 m}
    (hpc : (p.1.val + p.2.val + c.1.val + c.2.val) % 2 = 1)
    (hca : (c.1.val + c.2.val + a.1.val + a.2.val) % 2 = 1) :
    ∃ σ : List Dir, ApplicableFrom p σ
      ∧ permOf p σ = Equiv.swap p c * Equiv.swap c a
      ∧ σ.length ≤ 24 * m + 2 := by
  obtain ⟨σ₁, hap₁, hp₁, hl₁⟩ := strip_jump (p := p) (q := c) hpc
  obtain ⟨σ₂, hap₂, hp₂, hl₂⟩ := strip_jump (p := c) (q := a) hca
  have ht₁ : trace p σ₁ = c := trace_eq_of_permOf_swap hp₁
  refine ⟨σ₁ ++ σ₂, ?_, permOf_two_jumps σ₁ σ₂ hp₁ ht₁ hp₂, ?_⟩
  · rw [applicableFrom_append, ht₁]; exact ⟨hap₁, hap₂⟩
  · rw [List.length_append]; omega

/-! ### The four-jump placement (cases `A ≠ P = C` and `A = C ≠ P`) -/

/-- A closed four-jump chain `p → u → v → w → p` moves the content of `u` to `v`, the
content of `v` to `w` and the content of `w` to `u`, returning the blank to `p`. -/
theorem strip_place_four {p u v w : Cell 2 m}
    (hpu : (p.1.val + p.2.val + u.1.val + u.2.val) % 2 = 1)
    (huv : (u.1.val + u.2.val + v.1.val + v.2.val) % 2 = 1)
    (hvw : (v.1.val + v.2.val + w.1.val + w.2.val) % 2 = 1)
    (hwp : (w.1.val + w.2.val + p.1.val + p.2.val) % 2 = 1) :
    ∃ σ : List Dir, ApplicableFrom p σ
      ∧ permOf p σ = Equiv.swap p u * Equiv.swap u v * Equiv.swap v w * Equiv.swap w p
      ∧ σ.length ≤ 48 * m + 4 := by
  obtain ⟨σ₁, hap₁, hp₁, hl₁⟩ := strip_jump (p := p) (q := u) hpu
  obtain ⟨σ₂, hap₂, hp₂, hl₂⟩ := strip_jump (p := u) (q := v) huv
  obtain ⟨σ₃, hap₃, hp₃, hl₃⟩ := strip_jump (p := v) (q := w) hvw
  obtain ⟨σ₄, hap₄, hp₄, hl₄⟩ := strip_jump (p := w) (q := p) hwp
  have ht₁ : trace p σ₁ = u := trace_eq_of_permOf_swap hp₁
  have ht₂ : trace u σ₂ = v := trace_eq_of_permOf_swap hp₂
  have ht₃ : trace v σ₃ = w := trace_eq_of_permOf_swap hp₃
  refine ⟨((σ₁ ++ σ₂) ++ σ₃) ++ σ₄, ?_,
    permOf_four_jumps σ₁ σ₂ σ₃ σ₄ hp₁ ht₁ hp₂ ht₂ hp₃ ht₃ hp₄, ?_⟩
  · rw [applicableFrom_append, applicableFrom_append, applicableFrom_append]
    simp only [trace_append, ht₁, ht₂, ht₃]
    exact ⟨⟨⟨hap₁, hap₂⟩, hap₃⟩, hap₄⟩
  · rw [List.length_append, List.length_append, List.length_append]; omega

/-! ### The content effects of the placement chains -/

/-- The two-jump chain `p → c → a` moves the content of `a` to `c`. -/
theorem strip_place_two_content {p c a : Cell 2 m}
    (hpc : (p.1.val + p.2.val + c.1.val + c.2.val) % 2 = 1)
    (hca : (c.1.val + c.2.val + a.1.val + a.2.val) % 2 = 1)
    (hap : a ≠ p) (hac : a ≠ c) :
    ∃ σ : List Dir, ApplicableFrom p σ ∧ permOf p σ c = a ∧ σ.length ≤ 24 * m + 2 := by
  obtain ⟨σ, hapσ, hperm, hlen⟩ := strip_place_two hpc hca
  refine ⟨σ, hapσ, ?_, hlen⟩
  rw [hperm, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hap hac]

/-- The closed four-jump chain `p → u → v → w → p` moves the content of `w` to `u`. -/
theorem strip_place_four_content {p u v w : Cell 2 m}
    (hpu : (p.1.val + p.2.val + u.1.val + u.2.val) % 2 = 1)
    (huv : (u.1.val + u.2.val + v.1.val + v.2.val) % 2 = 1)
    (hvw : (v.1.val + v.2.val + w.1.val + w.2.val) % 2 = 1)
    (hwp : (w.1.val + w.2.val + p.1.val + p.2.val) % 2 = 1)
    (hpv : p ≠ v) (hpw : p ≠ w) (hpu' : p ≠ u) :
    ∃ σ : List Dir, ApplicableFrom p σ ∧ permOf p σ w = u ∧ σ.length ≤ 48 * m + 4 := by
  obtain ⟨σ, hapσ, hperm, hlen⟩ := strip_place_four hpu huv hvw hwp
  refine ⟨σ, hapσ, ?_, hlen⟩
  rw [hperm, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hpv hpw,
      Equiv.swap_apply_of_ne_of_ne hpu' hpv, Equiv.swap_apply_left]

end Zhong
