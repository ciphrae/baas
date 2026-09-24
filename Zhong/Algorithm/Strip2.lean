/-
Copyright (c) 2026 The Zhong formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhong formalisation contributors
-/
import Zhong.Algorithm.Assembly
import Zhong.Algorithm.TwoByTwo
import Zhong.Reachable

/-!
# The two-row solver

This file finishes milestone M7.  After `solveRows` has placed rows `0, …, n-3`, the
remaining `2 × m` strip is solved column by column down to the trailing `2 × 2` block,
which is closed by the exhaustive `2 × 2` solver of `Algorithm/TwoByTwo.lean`.

* `blk` is the embedding of the trailing `2 × 2` block into the board;
* `solveBlock22` solves a board whose only incorrect cells lie in that block;
* `solveStrip2` places the last two rows column by column.
-/

namespace Zhong

open Equiv

variable {n m : ℕ}

local notation "c(" a "," b ")" => ((⟨a, by omega⟩ : Fin n), (⟨b, by omega⟩ : Fin m))
local notation "d(" a "," b ")" => ((⟨a, by omega⟩ : Fin 2), (⟨b, by omega⟩ : Fin m))

/-! ### The trailing `2 × 2` block -/

/-- The trailing `2 × 2` block of an `n × m` board: rows `n-2, n-1`, columns `m-2, m-1`. -/
def blk (hn : 2 ≤ n) (hm : 2 ≤ m) (c : Cell 2 2) : Cell n m :=
  (⟨n - 2 + c.1.val, by have := c.1.isLt; omega⟩,
   ⟨m - 2 + c.2.val, by have := c.2.isLt; omega⟩)

theorem blk_injective (hn : 2 ≤ n) (hm : 2 ≤ m) : Function.Injective (blk (n := n) (m := m) hn hm) := by
  intro c1 c2 h
  have h1 : c1.1.val = c2.1.val := by
    have := congrArg (fun w : Cell n m => w.1.val) h
    simp only [blk, Fin.val_mk] at this
    omega
  have h2 : c1.2.val = c2.2.val := by
    have := congrArg (fun w : Cell n m => w.2.val) h
    simp only [blk, Fin.val_mk] at this
    omega
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)

theorem blk_neighbor (hn : 2 ≤ n) (hm : 2 ≤ m) :
    ∀ (c : Cell 2 2) (δ : Dir) (c' : Cell 2 2),
      neighbor? c δ = some c' → neighbor? (blk hn hm c) δ = some (blk hn hm c') := by
  rintro ⟨a, b⟩ δ ⟨a', b'⟩ h
  fin_cases a <;> fin_cases a' <;> fin_cases b <;> fin_cases b' <;>
    cases δ <;> simp_all [blk, neighbor?] <;> omega

/-- A cell of the trailing block is characterised by its coordinates. -/
theorem mem_range_blk (hn : 2 ≤ n) (hm : 2 ≤ m) {z : Cell n m} :
    z ∈ Set.range (blk (n := n) (m := m) hn hm) ↔ n - 2 ≤ z.1.val ∧ m - 2 ≤ z.2.val := by
  constructor
  · rintro ⟨c, rfl⟩
    simp only [blk, Fin.val_mk]
    constructor <;> omega
  · intro hz
    refine ⟨((⟨z.1.val - (n - 2), by omega⟩ : Fin 2),
      (⟨z.2.val - (m - 2), by omega⟩ : Fin 2)), ?_⟩
    apply Prod.ext
    · apply Fin.ext; simp only [blk, Fin.val_mk]; omega
    · apply Fin.ext; simp only [blk, Fin.val_mk]; omega

/-! ### Horizontal-first navigation -/

/-- Move the blank to `(x,y)`, moving horizontally first.  This is the variant used when the
vertical run would pass through a cell that must not be disturbed. -/
def moveToWordHV (r c x y : ℕ) : List Dir := moveYWord c y ++ moveXWord r x

theorem trace_moveToWordHV (r c x y : ℕ) (hx : x < n) (hy : y < m) (hr : r < n) (hc : c < m) :
    trace (((⟨r, hr⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m) (moveToWordHV r c x y)
      = (((⟨x, hx⟩ : Fin n), (⟨y, hy⟩ : Fin m)) : Cell n m) := by
  unfold moveToWordHV
  rw [trace_append, trace_moveYWord r c y hr hc hy]
  exact trace_moveXWord r y x hx (by omega) hy

theorem applicableFrom_moveToWordHV (r c x y : ℕ) (hx : x < n) (hy : y < m) (hr : r < n)
    (hc : c < m) :
    ApplicableFrom (((⟨r, hr⟩ : Fin n), (⟨c, hc⟩ : Fin m)) : Cell n m) (moveToWordHV r c x y) := by
  unfold moveToWordHV
  rw [applicableFrom_append]
  refine ⟨applicableFrom_moveYWord r c y hy hr hc, ?_⟩
  rw [trace_moveYWord r c y hr hc hy]
  exact applicableFrom_moveXWord r y x hx (by omega) hy

theorem length_moveToWordHV (r c x y : ℕ) :
    (moveToWordHV r c x y).length = Nat.dist c y + Nat.dist r x := by
  unfold moveToWordHV
  rw [List.length_append, length_moveYWord, length_moveXWord]

/-- A cell of the strip is the image of its strip coordinates. -/
theorem hStrip_sCell (r : ℕ) (hr : r + 1 < n) {z : Cell n m} (h1 : r ≤ z.1.val)
    (h2 : z.1.val ≤ r + 1) :
    hStrip r hr ((⟨z.1.val - r, by omega⟩ : Fin 2), z.2) = z := by
  apply Prod.ext
  · apply Fin.ext; simp only [hStrip, Fin.val_mk]; omega
  · rfl

/-! ### The trailing `2 × 2` block solver -/

/-- **The trailing `2 × 2` block solver.**  If every cell outside the trailing block already
agrees with the target, then a reachable board can be solved in at most `6` moves. -/
theorem solveBlock22 (B : Board n m) [NeZero (n * m)] (hn : 2 ≤ n) (hm : 4 ≤ m)
    (hout : ∀ z : Cell n m, z ∉ Set.range (blk (n := n) (m := m) hn (by omega)) →
      B z = target n m z)
    (hreach : Reachable B (target n m)) :
    ∃ σ : List Dir, actSeq B σ = target n m ∧ σ.length ≤ 6 := by
  classical
  have hm2 : 2 ≤ m := by omega
  set b : Cell 2 2 → Cell n m := blk hn hm2 with hb
  have hbinj : Function.Injective b := blk_injective hn hm2
  have hbneigh : ∀ (c : Cell 2 2) (δ : Dir) (c' : Cell 2 2),
      neighbor? c δ = some c' → neighbor? (b c) δ = some (b c') := blk_neighbor hn hm2
  have hout' : ∀ z : Cell n m, z ∉ Set.range b → B z = target n m z := hout
  set ρfun : Fin 4 → Fin (n * m) := fun k => target n m (b ((target 2 2).symm k)) with hρ
  have hρinj : Function.Injective ρfun := by
    intro k1 k2 h
    have h1 : b ((target 2 2).symm k1) = b ((target 2 2).symm k2) := (target n m).injective h
    exact (target 2 2).symm.injective (hbinj h1)
  let ρe : Fin 4 ≃ Set.range ρfun := Equiv.ofInjective ρfun hρinj
  -- every label of the block is a target label
  have hmem : ∀ c : Cell 2 2, B (b c) ∈ Set.range ρfun := by
    intro c
    set w : Cell n m := (target n m).symm (B (b c)) with hw
    by_cases hwr : w ∈ Set.range b
    · obtain ⟨c', hc'⟩ := hwr
      refine ⟨target 2 2 c', ?_⟩
      show ρfun (target 2 2 c') = B (b c)
      rw [show ρfun (target 2 2 c') = target n m (b c') by simp only [ρfun, Equiv.symm_apply_apply],
        hc', hw, Equiv.apply_symm_apply]
    · have hBw : B w = target n m w := hout' w hwr
      have htw : target n m w = B (b c) := by rw [hw, Equiv.apply_symm_apply]
      have hwb : w = b c := B.injective (hBw.trans htw)
      exact absurd ⟨c, hwb.symm⟩ hwr
  let f : Cell 2 2 → Set.range ρfun := fun c => ⟨B (b c), hmem c⟩
  have hf_inj : Function.Injective f := by
    intro c1 c2 h
    exact hbinj (B.injective (Subtype.ext_iff.mp h))
  have hf_surj : Function.Surjective f := by
    intro t
    obtain ⟨k, hk⟩ := t.2
    set z : Cell n m := B.symm t.1 with hz
    by_cases hzr : z ∈ Set.range b
    · obtain ⟨c', hc'⟩ := hzr
      refine ⟨c', Subtype.ext ?_⟩
      show B (b c') = t.1
      rw [hc', hz, Equiv.apply_symm_apply]
    · have hBz : B z = target n m z := hout' z hzr
      have hzt : t.1 = target n m z := by rw [← hBz, hz, Equiv.apply_symm_apply]
      have hkw : t.1 = target n m (b ((target 2 2).symm k)) := hk.symm
      have hzb : z = b ((target 2 2).symm k) := (target n m).injective (hzt.symm.trans hkw)
      exact absurd ⟨_, hzb.symm⟩ hzr
  let fE : Cell 2 2 ≃ Set.range ρfun := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  let B22 : Board 2 2 := fE.trans ρe.symm
  have hB22 : ∀ c : Cell 2 2, ρfun (B22 c) = B (b c) := by
    intro c
    change ρfun (ρe.symm (fE c)) = B (b c)
    rw [Equiv.apply_ofInjective_symm hρinj (fE c)]
    rfl
  -- the sign relation
  have hcomp : ∀ x : Fin 4,
      ρfun (relPerm B22 (target 2 2) x) = relPerm B (target n m) (ρfun x) := by
    intro x
    change ρfun ((target 2 2) (B22.symm x)) = (target n m) (B.symm (ρfun x))
    have hx1 : ρfun x = B (b (B22.symm x)) := by
      rw [← hB22 (B22.symm x), Equiv.apply_symm_apply]
    rw [hx1, Equiv.symm_apply_apply]
    simp only [ρfun, Equiv.symm_apply_apply]
  have hsign : Equiv.Perm.sign (relPerm B22 (target 2 2))
      = Equiv.Perm.sign (relPerm B (target n m)) := by
    apply Equiv.Perm.sign_bij (fun x (_ : relPerm B22 (target 2 2) x ≠ x) => ρfun x)
    · intro x hx hx'
      exact hcomp x
    · intro x1 x2 _ _ h
      exact hρinj h
    · intro y hy
      by_contra hcon
      have hzr : B.symm y ∉ Set.range b := by
        intro hzr
        obtain ⟨c, hc⟩ := hzr
        refine hcon ⟨B22 c, ?_, ?_⟩
        · intro heq
          apply hy
          have h := hcomp (B22 c)
          rw [heq] at h
          rw [hB22 c, hc, Equiv.apply_symm_apply] at h
          exact h.symm
        · rw [hB22 c, hc, Equiv.apply_symm_apply]
      have hyy : relPerm B (target n m) y = y := by
        rw [relPerm, Equiv.trans_apply]
        have hBw : B (B.symm y) = target n m (B.symm y) := hout' _ hzr
        rw [Equiv.apply_symm_apply] at hBw
        exact hBw.symm
      exact hy hyy
  -- parity of the block agrees with the target
  have hb0 : b (blank (target 2 2))
      = (((⟨n - 1, by omega⟩ : Fin n), (⟨m - 1, by omega⟩ : Fin m)) : Cell n m) := by
    have h0 : blank (target 2 2) = ((1, 1) : Cell 2 2) := by
      apply (target 2 2).injective
      rw [blank, Equiv.apply_symm_apply]
      exact (target_last (n := 2) (m := 2) (by norm_num) (by norm_num) (by norm_num)).symm
    rw [h0]
    apply Prod.ext <;> apply Fin.ext <;>
      simp only [b, blk, Fin.val_mk] <;> omega
  have hρ0 : ρfun 0 = 0 := by
    simp only [ρfun]
    rw [show (target 2 2).symm (0 : Fin 4) = blank (target 2 2) from rfl, hb0]
    exact target_last (n := n) (m := m) (by omega) (by omega) (by nlinarith)
  have hblank : blank B = b (blank B22) := by
    apply B.injective
    show B (B.symm 0) = B (b (B22.symm 0))
    rw [Equiv.apply_symm_apply]
    rw [← hB22 (B22.symm 0), Equiv.apply_symm_apply]
    exact hρ0.symm
  have hblankT : blank (target n m) = b (blank (target 2 2)) := by
    rw [hb0]
    apply (target n m).injective
    rw [blank, Equiv.apply_symm_apply]
    exact (target_last (n := n) (m := m) (by omega) (by omega) (by nlinarith)).symm
  have hcp : ∀ c : Cell 2 2,
      cellParity (b c) = (-1 : ℤˣ) ^ (n + m - 4) * cellParity c := by
    intro c
    unfold cellParity
    have hsum : (b c).1.1 + (b c).2.1 = (n + m - 4) + (c.1.1 + c.2.1) := by
      simp only [b, blk, Fin.val_mk]; omega
    rw [hsum, pow_add]
  have hpar : Equiv.Perm.sign (relPerm B22 (target 2 2))
      = cellParity (blank B22) * cellParity (blank (target 2 2)) := by
    rw [hsign, reachable_sign_relPerm hreach, hblank, hblankT,
      hcp (blank B22), hcp (blank (target 2 2))]
    calc ((-1 : ℤˣ) ^ (n + m - 4) * cellParity (blank B22))
          * ((-1 : ℤˣ) ^ (n + m - 4) * cellParity (blank (target 2 2)))
        = (((-1 : ℤˣ) ^ (n + m - 4) * (-1 : ℤˣ) ^ (n + m - 4))
            * (cellParity (blank B22) * cellParity (blank (target 2 2)))) := by ac_rfl
      _ = 1 * (cellParity (blank B22) * cellParity (blank (target 2 2))) := by
            rw [units_mul_self]
      _ = cellParity (blank B22) * cellParity (blank (target 2 2)) := by rw [one_mul]
  let σ : List Dir := solve22 B22
  have hσ22 : actSeq B22 σ = target 2 2 := solve22_correct B22 hpar
  have happ22 : ApplicableFrom (blank B22) σ := solve22_applicable B22
  have hperm22 : permOf (blank B22) σ = (target 2 2).trans B22.symm := by
    have h := congrArg (fun e => e.trans B22.symm) hσ22
    simpa [σ, actSeq_eq_permOf, Equiv.trans_assoc] using h
  have hperm : ∀ x : Cell 2 2, permOf (blank B) σ (b x) = b (permOf (blank B22) σ x) := by
    intro x
    have h := permOf_map_apply_of_neighbor_map (ι := b) (f := id) hbinj hbneigh
      (blank B22) σ happ22 x
    simpa [← hblank] using h
  have hfix : ∀ z : Cell n m, z ∉ Set.range b → permOf (blank B) σ z = z := by
    intro z hz
    have h := permOf_map_fixes_of_not_mem_range (ι := b) (f := id) hbneigh
      (blank B22) σ happ22 hz
    simpa [← hblank] using h
  refine ⟨σ, ?_, solve22_length B22⟩
  apply Equiv.ext
  intro z
  rw [actSeq_eq_permOf, Equiv.trans_apply]
  by_cases hz : z ∈ Set.range b
  · obtain ⟨x, rfl⟩ := hz
    rw [hperm x]
    rw [show permOf (blank B22) σ x = B22.symm ((target 2 2) x) from by rw [hperm22]; rfl]
    rw [← hB22 (B22.symm ((target 2 2) x)), Equiv.apply_symm_apply]
    simp only [ρfun, Equiv.symm_apply_apply]
  · rw [hfix z hz]
    exact hout' z hz

/-! ### The two-row column step -/

/-- If a word fixes the rows above `r` and the columns left of `lo`, then the blank after it
stays in the region `row ≥ r`, `column ≥ lo`. -/
lemma blank_bounds_of_fixes {r lo : ℕ} {B : Board n m} [NeZero (n * m)] {σ : List Dir}
    (hfixr : ∀ z : Cell n m, z.1.val < r → permOf (blank B) σ z = z)
    (hfixc : ∀ z : Cell n m, z.2.val < lo → permOf (blank B) σ z = z)
    (hrow : r ≤ (blank B).1.val) (hcol : lo ≤ (blank B).2.val) :
    r ≤ (blank (actSeq B σ)).1.val ∧ lo ≤ (blank (actSeq B σ)).2.val := by
  have htr : blank (actSeq B σ) = (permOf (blank B) σ).symm (blank B) := by
    rw [blank_actSeq, permOf_symm_apply]
  constructor
  · by_contra h
    have hperm : permOf (blank B) σ (blank (actSeq B σ)) = blank B := by
      rw [htr, Equiv.apply_symm_apply]
    rw [hfixr _ (by omega)] at hperm
    have := congrArg (fun z : Cell n m => z.1.val) hperm
    omega
  · by_contra h
    have hperm : permOf (blank B) σ (blank (actSeq B σ)) = blank B := by
      rw [htr, Equiv.apply_symm_apply]
    rw [hfixc _ (by omega)] at hperm
    have := congrArg (fun z : Cell n m => z.2.val) hperm
    omega

/-- Convert a board-level fix property to the induced permutation. -/
lemma board_fix_to_perm {B : Board n m} [NeZero (n * m)] {σ : List Dir} {z : Cell n m}
    (h : (actSeq B σ) z = B z) : permOf (blank B) σ z = z := by
  rw [actSeq_eq_permOf, Equiv.trans_apply] at h
  exact B.injective h

/-- **One column of the two-row solver.**  With rows `< r` and columns `< j` already correct,
place both cells of column `j` in `O(n + m)` moves, leaving rows `< r` and columns `< j+1`
correct.  The strip must be the last two rows (`r + 2 = n`). -/
theorem placeColumn2 (r : ℕ) (hr : r + 1 < n) (hr2 : r + 2 = n) (hm : 4 ≤ m)
    (j : ℕ) (hj : j + 3 ≤ m)
    (B : Board n m) [NeZero (n * m)]
    (habove : ∀ (x : Fin n) (y : Fin m), x.val < r → B (x,y) = target n m (x,y))
    (hcol : ∀ (x : Fin n) (y : Fin m), y.val < j → B (x,y) = target n m (x,y)) :
    ∃ σ : List Dir,
      (∀ (x : Fin n) (y : Fin m), x.val < r → (actSeq B σ) (x,y) = target n m (x,y)) ∧
      (∀ (x : Fin n) (y : Fin m), y.val < j + 1 → (actSeq B σ) (x,y) = target n m (x,y)) ∧
      σ.length ≤ 600 * (n + m) := by
  classical
  have hjlt : j < m := by omega
  have hj1lt : j + 1 < m := by omega
  have hstrip_top : hStrip (m := m) r hr (d(0,j)) = c(r,j) := by
    apply Prod.ext <;> apply Fin.ext <;> simp only [hStrip, Fin.val_mk]; omega
  have hstrip_bot : hStrip (m := m) r hr (d(1,j)) = c(r+1,j) := by
    apply Prod.ext <;> apply Fin.ext <;> simp only [hStrip, Fin.val_mk]
  have hstrip_p : hStrip (m := m) r hr (d(0,j+1)) = c(r,j+1) := by
    apply Prod.ext <;> apply Fin.ext <;> simp only [hStrip, Fin.val_mk]; omega
  -- ### blank facts
  set p0 : Cell n m := blank B with hp0
  have hp0row : r ≤ p0.1.val := by
    by_contra h
    have h1 : B p0 = target n m p0 := habove p0.1 p0.2 (by omega)
    have h2 : B p0 = 0 := by rw [hp0]; exact Equiv.apply_symm_apply B 0
    rw [h1] at h2
    exact target_ne_zero p0.1.val p0.2.val p0.2.isLt (by omega) h2
  have hp0row2 : p0.1.val ≤ r + 1 := by have := p0.1.isLt; omega
  have hp0col : j ≤ p0.2.val := by
    by_contra h
    have h1 : B p0 = target n m p0 := hcol p0.1 p0.2 (by omega)
    have h2 : B p0 = 0 := by rw [hp0]; exact Equiv.apply_symm_apply B 0
    have h3 : target n m p0 = 0 := by rw [← h1, h2]
    have hlast := target_last (n := n) (m := m) (by omega) (by omega) (by nlinarith)
    have hcell : p0 = (((⟨n-1, by omega⟩ : Fin n), (⟨m-1, by omega⟩ : Fin m)) : Cell n m) :=
      (target n m).injective (h3.trans hlast.symm)
    have := congrArg (fun w : Cell n m => w.2.val) hcell
    simp only at this
    omega
  -- ### step 1: normalise the blank to `(r+1,j)`
  set σ0 : List Dir := moveToWord p0.1.val p0.2.val (r+1) j with hσ0
  have happ0 : ApplicableFrom p0 σ0 := by
    rw [hσ0]
    exact applicableFrom_moveToWord p0.1.val p0.2.val (r+1) j (by omega) (by omega)
      p0.1.isLt p0.2.isLt
  have htr0 : trace p0 σ0 = c(r+1,j) := by
    rw [hσ0]
    have := trace_moveToWord p0.1.val p0.2.val (r+1) j (by omega) (by omega) p0.1.isLt p0.2.isLt
    simpa using this
  have hbound0 : ∀ z ∈ traceSet p0 σ0, j ≤ z.2.val ∧ r ≤ z.1.val ∧ z.1.val ≤ r + 1 := by
    intro z hz
    rw [hσ0, show moveToWord p0.1.val p0.2.val (r+1) j
        = moveXWord p0.1.val (r+1) ++ moveYWord p0.2.val j from rfl, traceSet_append] at hz
    rcases Finset.mem_union.mp hz with hz | hz
    · have hres :=
        moveXWord_traceSet p0.1.val p0.2.val (r+1) (by omega) p0.1.isLt p0.2.isLt z hz
      have h2v : z.2.val = p0.2.val := congrArg Fin.val hres.1
      exact ⟨by omega, by omega, by omega⟩
    · rw [trace_moveXWord p0.1.val p0.2.val (r+1) (by omega) p0.1.isLt p0.2.isLt] at hz
      have hrow := moveYWord_traceSet (r+1) p0.2.val j (by omega) (by omega) p0.2.isLt z hz
      have hcol := moveYWord_traceSet_col (r+1) p0.2.val j (by omega) (by omega) p0.2.isLt z hz
      have h1v : z.1.val = r + 1 := congrArg Fin.val hrow
      exact ⟨by omega, by omega, by omega⟩
  have hfix0r : ∀ z : Cell n m, z.1.val < r → permOf p0 σ0 z = z := by
    intro z hz
    apply permOf_apply_of_not_mem_traceSet
    intro hmem
    obtain ⟨_, hmin, _⟩ := hbound0 z hmem
    omega
  have hfix0c : ∀ z : Cell n m, z.2.val < j → permOf p0 σ0 z = z := by
    intro z hz
    apply permOf_apply_of_not_mem_traceSet
    intro hmem
    obtain ⟨hmin, _, _⟩ := hbound0 z hmem
    omega
  set B0 : Board n m := actSeq B σ0 with hB0
  have hblank0 : blank B0 = c(r+1,j) := by rw [hB0, blank_actSeq, ← hp0, htr0]
  have habove0 : ∀ (x : Fin n) (y : Fin m), x.val < r → B0 (x,y) = target n m (x,y) := by
    intro x y hx
    rw [hB0, actSeq_eq_permOf, Equiv.trans_apply, ← hp0, hfix0r (x,y) hx]
    exact habove x y hx
  have hcol0 : ∀ (x : Fin n) (y : Fin m), y.val < j → B0 (x,y) = target n m (x,y) := by
    intro x y hy
    rw [hB0, actSeq_eq_permOf, Equiv.trans_apply, ← hp0, hfix0c (x,y) hy]
    exact hcol x y hy
  -- ### step 2: place the upper tile `T1` at `(r,j)`
  set T1 : Fin (n * m) := target n m c(r,j) with hT1
  have hT1ne : T1 ≠ 0 := by rw [hT1]; exact target_ne_zero r j hjlt (by omega)
  set a1 : Cell n m := B0.symm T1 with ha1
  have hB0a1 : B0 a1 = T1 := Equiv.apply_symm_apply B0 T1
  have ha1row : r ≤ a1.1.val := by
    by_contra h
    have h1 : B0 a1 = target n m a1 := habove0 a1.1 a1.2 (by omega)
    have h2 : a1 = c(r,j) := (target n m).injective (h1.symm.trans hB0a1)
    have := congrArg (fun w : Cell n m => w.1.val) h2
    simp only at this; omega
  have ha1row2 : a1.1.val ≤ r + 1 := by have := a1.1.isLt; omega
  have ha1col : j ≤ a1.2.val := by
    by_contra h
    have h1 : B0 a1 = target n m a1 := hcol0 a1.1 a1.2 (by omega)
    have h2 : a1 = c(r,j) := (target n m).injective (h1.symm.trans hB0a1)
    have := congrArg (fun w : Cell n m => w.2.val) h2
    simp only at this; omega
  set a1s : Cell 2 m := ((⟨a1.1.val - r, by omega⟩ : Fin 2), a1.2) with ha1s
  have hstrip_a1s : hStrip (m := m) r hr a1s = a1 := by
    rw [ha1s]; exact hStrip_sCell r hr ha1row ha1row2
  have ha1scol : a1s.2.val = a1.2.val := rfl
  have ha1srow : a1s.1.val = a1.1.val - r := rfl
  have ha1s_ge : j ≤ a1s.2.val := by rw [ha1scol]; exact ha1col
  -- perform the placement (or detect that the tile is already in place)
  have hplace1 : ∃ σ1 : List Dir,
      (actSeq B0 σ1) c(r,j) = T1 ∧
      (∀ (x : Fin n) (y : Fin m), x.val < r → (actSeq B0 σ1) (x,y) = B0 (x,y)) ∧
      (∀ (x : Fin n) (y : Fin m), y.val < j → (actSeq B0 σ1) (x,y) = B0 (x,y)) ∧
      σ1.length ≤ 96 * m + 8 := by
    by_cases hsame : a1 = c(r,j)
    · refine ⟨[], ?_, ?_, ?_, by simp⟩
      · rw [actSeq_nil, ← hsame, hB0a1]
      · intro x y hx; rw [actSeq_nil]
      · intro x y hy; rw [actSeq_nil]
    · have hac : a1s ≠ d(0,j) := by
        intro h
        apply hsame
        rw [← hstrip_a1s, h, hstrip_top]
      have hpa : d(1,j) ≠ a1s := by
        intro h
        have h' : c(r+1,j) = a1 := by rw [← hstrip_bot, h, hstrip_a1s]
        have h0 : B0 c(r+1,j) = 0 := by rw [← hblank0]; exact Equiv.apply_symm_apply B0 0
        rw [h', hB0a1] at h0
        exact hT1ne h0
      obtain ⟨σ1, happ1, heff1, hfix1r, hfix1left, hfix1c, hlen1⟩ :=
        stripPlace2Board (r := r) hr hm j hj (J := d(0,0)) (p := d(1,j)) (a := a1s)
          (c := d(0,j)) (T := T1) (by rfl) (by rw [hblank0, hstrip_bot]) (by rw [hstrip_a1s]; exact hB0a1)
          (by rfl) (by rfl) hpa hac (fun _ => ha1s_ge)
          (by simp) ha1s_ge (by simp)
      refine ⟨σ1, ?_, ?_, ?_, hlen1⟩
      · rw [← hstrip_top]; exact heff1
      · intro x y hx; exact hfix1r (x,y) hx
      · intro x y hy; exact hfix1c (x,y) hy
  obtain ⟨σ1, heff1, hfix1r, hfix1c, hlen1⟩ := hplace1
  set B1 : Board n m := actSeq B0 σ1 with hB1
  have habove1 : ∀ (x : Fin n) (y : Fin m), x.val < r → B1 (x,y) = target n m (x,y) := by
    intro x y hx; rw [hB1, hfix1r x y hx]; exact habove0 x y hx
  have hcol1 : ∀ (x : Fin n) (y : Fin m), y.val < j → B1 (x,y) = target n m (x,y) := by
    intro x y hy; rw [hB1, hfix1c x y hy]; exact hcol0 x y hy
  have hcell1 : B1 c(r,j) = target n m c(r,j) := by rw [hB1, heff1, hT1]
  have hblank1_ne : blank B1 ≠ c(r,j) := by
    intro h
    have h0 : B1 (blank B1) = 0 := Equiv.apply_symm_apply B1 0
    rw [h, hcell1] at h0
    exact hT1ne h0
  have hfix1r' : ∀ z : Cell n m, z.1.val < r → permOf (blank B0) σ1 z = z :=
    fun z hz => board_fix_to_perm (hfix1r z.1 z.2 hz)
  have hfix1c' : ∀ z : Cell n m, z.2.val < j → permOf (blank B0) σ1 z = z :=
    fun z hz => board_fix_to_perm (hfix1c z.1 z.2 hz)
  have hb0row : (blank B0).1.val = r + 1 := by rw [hblank0]
  have hb0col : (blank B0).2.val = j := by rw [hblank0]
  have hb1 := blank_bounds_of_fixes hfix1r' hfix1c' (show r ≤ (blank B0).1.val by omega)
    (show j ≤ (blank B0).2.val by omega)
  have hblank1row : r ≤ (blank B1).1.val := hb1.1
  have hblank1col : j ≤ (blank B1).2.val := hb1.2
  -- ### step 3: normalise the blank to `(r,j+1)` (horizontal first, avoiding `(r,j)`)
  set σ2 : List Dir := moveToWordHV (blank B1).1.val (blank B1).2.val r (j+1) with hσ2
  have happ2 : ApplicableFrom (blank B1) σ2 := by
    rw [hσ2]
    exact applicableFrom_moveToWordHV (blank B1).1.val (blank B1).2.val r (j+1)
      (by omega) (by omega) (blank B1).1.isLt (blank B1).2.isLt
  have htr2 : trace (blank B1) σ2 = c(r,j+1) := by
    rw [hσ2]
    have := trace_moveToWordHV (blank B1).1.val (blank B1).2.val r (j+1)
      (by omega) (by omega) (blank B1).1.isLt (blank B1).2.isLt
    simpa using this
  have hbound2 : ∀ z ∈ traceSet (blank B1) σ2, r ≤ z.1.val ∧ z.1.val ≤ r + 1 ∧ j ≤ z.2.val := by
    intro z hz
    rw [hσ2, show moveToWordHV (blank B1).1.val (blank B1).2.val r (j+1)
        = moveYWord (blank B1).2.val (j+1) ++ moveXWord (blank B1).1.val r from rfl,
      traceSet_append] at hz
    rcases Finset.mem_union.mp hz with hz | hz
    · have hrow := moveYWord_traceSet (blank B1).1.val (blank B1).2.val (j+1)
        (by omega) (by omega) (blank B1).2.isLt z hz
      have hcol := moveYWord_traceSet_col (blank B1).1.val (blank B1).2.val (j+1)
        (by omega) (by omega) (blank B1).2.isLt z hz
      have h1v : z.1.val = (blank B1).1.val := congrArg Fin.val hrow
      exact ⟨by omega, by omega, by omega⟩
    · rw [trace_moveYWord (blank B1).1.val (blank B1).2.val (j+1) (by omega)
        (blank B1).2.isLt (by omega)] at hz
      have hres := moveXWord_traceSet (blank B1).1.val (j+1) r (by omega) (by omega)
        (by omega) z hz
      have h2v : z.2.val = j + 1 := congrArg Fin.val hres.1
      exact ⟨by omega, by omega, by omega⟩
  have hnotmem2 : c(r,j) ∉ traceSet (blank B1) σ2 := by
    intro hmem
    rw [hσ2, show moveToWordHV (blank B1).1.val (blank B1).2.val r (j+1)
        = moveYWord (blank B1).2.val (j+1) ++ moveXWord (blank B1).1.val r from rfl,
      traceSet_append] at hmem
    rcases Finset.mem_union.mp hmem with hmem | hmem
    · have hrow := moveYWord_traceSet (blank B1).1.val (blank B1).2.val (j+1)
        (by omega) (by omega) (blank B1).2.isLt c(r,j) hmem
      have hcol := moveYWord_traceSet_col (blank B1).1.val (blank B1).2.val (j+1)
        (by omega) (by omega) (blank B1).2.isLt c(r,j) hmem
      have h1v : r = (blank B1).1.val := by
        have := congrArg Fin.val hrow; simp only at this; omega
      have hbcj : (blank B1).2.val = j := by
        have := hcol.1; simp only at this; omega
      refine hblank1_ne ?_
      apply Prod.ext
      · apply Fin.ext; exact h1v.symm
      · apply Fin.ext; exact hbcj
    · rw [trace_moveYWord (blank B1).1.val (blank B1).2.val (j+1) (by omega)
        (blank B1).2.isLt (by omega)] at hmem
      have hres := moveXWord_traceSet (blank B1).1.val (j+1) r (by omega) (by omega)
        (by omega) c(r,j) hmem
      have h2v : j = j + 1 := by
        have := congrArg Fin.val hres.1; simp only at this; omega
      exact absurd h2v (by omega)
  set B2 : Board n m := actSeq B1 σ2 with hB2
  have hblank2 : blank B2 = c(r,j+1) := by rw [hB2, blank_actSeq, htr2]
  have hfix2r : ∀ z : Cell n m, z.1.val < r → permOf (blank B1) σ2 z = z := by
    intro z hz
    apply permOf_apply_of_not_mem_traceSet
    intro hmem
    obtain ⟨hmin, _, _⟩ := hbound2 z hmem
    omega
  have hfix2lt : ∀ z : Cell n m, z.2.val < j → permOf (blank B1) σ2 z = z := by
    intro z hz
    apply permOf_apply_of_not_mem_traceSet
    intro hmem
    obtain ⟨_, _, hcol⟩ := hbound2 z hmem
    omega
  have hfix2cell : permOf (blank B1) σ2 c(r,j) = c(r,j) :=
    permOf_apply_of_not_mem_traceSet hnotmem2
  have habove2 : ∀ (x : Fin n) (y : Fin m), x.val < r → B2 (x,y) = target n m (x,y) := by
    intro x y hx
    rw [hB2, actSeq_eq_permOf, Equiv.trans_apply, hfix2r (x,y) hx]
    exact habove1 x y hx
  have hcol2 : ∀ (x : Fin n) (y : Fin m), y.val < j → B2 (x,y) = target n m (x,y) := by
    intro x y hy
    rw [hB2, actSeq_eq_permOf, Equiv.trans_apply, hfix2lt (x,y) hy]
    exact hcol1 x y hy
  have hcell2 : B2 c(r,j) = target n m c(r,j) := by
    rw [hB2, actSeq_eq_permOf, Equiv.trans_apply, hfix2cell, hcell1]
  -- ### step 4: place the lower tile `T2` at `(r+1,j)`
  set T2 : Fin (n * m) := target n m c(r+1,j) with hT2
  have hT2ne : T2 ≠ 0 := by
    rw [hT2]
    intro h0
    have hlast := target_last (n := n) (m := m) (by omega) (by omega) (by nlinarith)
    have hcell : c(r+1,j)
        = (((⟨n-1, by omega⟩ : Fin n), (⟨m-1, by omega⟩ : Fin m)) : Cell n m) :=
      (target n m).injective (h0.trans hlast.symm)
    have := congrArg (fun w : Cell n m => w.2.val) hcell
    simp only at this
    omega
  set a2 : Cell n m := B2.symm T2 with ha2
  have hB2a2 : B2 a2 = T2 := Equiv.apply_symm_apply B2 T2
  have ha2row : r ≤ a2.1.val := by
    by_contra h
    have h1 : B2 a2 = target n m a2 := habove2 a2.1 a2.2 (by omega)
    have h2 : a2 = c(r+1,j) := (target n m).injective (h1.symm.trans hB2a2)
    have := congrArg (fun w : Cell n m => w.1.val) h2
    simp only at this; omega
  have ha2row2 : a2.1.val ≤ r + 1 := by have := a2.1.isLt; omega
  have ha2col : j ≤ a2.2.val := by
    by_contra h
    have h1 : B2 a2 = target n m a2 := hcol2 a2.1 a2.2 (by omega)
    have h2 : a2 = c(r+1,j) := (target n m).injective (h1.symm.trans hB2a2)
    have := congrArg (fun w : Cell n m => w.2.val) h2
    simp only at this; omega
  set a2s : Cell 2 m := ((⟨a2.1.val - r, by omega⟩ : Fin 2), a2.2) with ha2s
  have hstrip_a2s : hStrip (m := m) r hr a2s = a2 := by
    rw [ha2s]; exact hStrip_sCell r hr ha2row ha2row2
  have ha2scol : a2s.2.val = a2.2.val := rfl
  have ha2s_ge : j ≤ a2s.2.val := by rw [ha2scol]; exact ha2col
  have hplace2 : ∃ σ3 : List Dir,
      (actSeq B2 σ3) c(r+1,j) = T2 ∧
      (∀ (x : Fin n) (y : Fin m), x.val < r → (actSeq B2 σ3) (x,y) = B2 (x,y)) ∧
      (∀ (x : Fin n) (y : Fin m), y.val < j → (actSeq B2 σ3) (x,y) = B2 (x,y)) ∧
      (actSeq B2 σ3) c(r,j) = B2 c(r,j) ∧
      σ3.length ≤ 96 * m + 8 := by
    by_cases hsame : a2 = c(r+1,j)
    · refine ⟨[], ?_, ?_, ?_, ?_, by simp⟩
      · rw [actSeq_nil, ← hsame, hB2a2]
      · intro x y hx; rw [actSeq_nil]
      · intro x y hy; rw [actSeq_nil]
      · rw [actSeq_nil]
    · have hac : a2s ≠ d(1,j) := by
        intro h
        apply hsame
        rw [← hstrip_a2s, h, hstrip_bot]
      have hpa : d(0,j+1) ≠ a2s := by
        intro h
        have h' : c(r,j+1) = a2 := by rw [← hstrip_p, h, hstrip_a2s]
        have h0 : B2 c(r,j+1) = 0 := by rw [← hblank2]; exact Equiv.apply_symm_apply B2 0
        rw [h', hB2a2] at h0
        exact hT2ne h0
      have hJp : d(0,j) ≠ d(0,j+1) := by
        intro h; have := congrArg (fun w : Cell 2 m => w.2.val) h
        simp only at this; omega
      have hJa : d(0,j) ≠ a2s := by
        intro h
        have h' : c(r,j) = a2 := by rw [← hstrip_top, h, hstrip_a2s]
        have h2 : c(r+1,j) = c(r,j) := (target n m).injective (by
          rw [← hT2, ← hT1, ← hB2a2, ← h', hcell2, ← hT1])
        have := congrArg (fun w : Cell n m => w.1.val) h2
        simp only at this; omega
      have hJc : d(0,j) ≠ d(1,j) := by
        intro h; have := congrArg (fun w : Cell 2 m => w.1.val) h
        simp only at this; omega
      obtain ⟨σ3, happ3, heff3, hfix3r, hfix3low, hfix3c, hfix3J, hlen3⟩ :=
        stripPlaceFlip2Board (r := r) hr hm j hj (J := d(0,j)) (p := d(0,j+1)) (a := a2s)
          (c := d(1,j)) (T := T2) (by rfl) (by rw [hblank2, hstrip_p])
          (by rw [hstrip_a2s]; exact hB2a2) (by rfl) (by rfl) hpa hac (fun _ => ha2s_ge)
          (by simp) ha2s_ge (by simp) hJp hJa hJc
      refine ⟨σ3, ?_, ?_, ?_, ?_, hlen3⟩
      · rw [← hstrip_bot]; exact heff3
      · intro x y hx; exact hfix3r (x,y) hx
      · intro x y hy; exact hfix3c (x,y) hy
      · rw [← hstrip_top]; exact hfix3J
  obtain ⟨σ3, heff3, hfix3r, hfix3c, hfix3J, hlen3⟩ := hplace2
  -- ### assembly
  refine ⟨σ0 ++ σ1 ++ σ2 ++ σ3, ?_, ?_, ?_⟩
  · intro x y hx
    have h3 : (actSeq B2 σ3) (x,y) = B2 (x,y) := hfix3r x y hx
    have h2 : B2 (x,y) = B1 (x,y) := by
      rw [hB2, actSeq_eq_permOf, Equiv.trans_apply, hfix2r (x,y) hx]
    have h1 : B1 (x,y) = B0 (x,y) := by
      rw [hB1, actSeq_eq_permOf, Equiv.trans_apply, hfix1r' (x,y) hx]
    rw [actSeq_append, actSeq_append, actSeq_append, ← hB0, ← hB1, ← hB2, h3, h2, h1]
    exact habove0 x y hx
  · intro x y hy
    rcases (by omega : y.val < j ∨ y.val = j) with h | h
    · have h3 : (actSeq B2 σ3) (x,y) = B2 (x,y) := hfix3c x y h
      have h2 : B2 (x,y) = B1 (x,y) := by
        rw [hB2, actSeq_eq_permOf, Equiv.trans_apply, hfix2lt (x,y) (by omega)]
      have h1 : B1 (x,y) = B0 (x,y) := by
        rw [hB1, actSeq_eq_permOf, Equiv.trans_apply, hfix1c' (x,y) h]
      rw [actSeq_append, actSeq_append, actSeq_append, ← hB0, ← hB1, ← hB2, h3, h2, h1]
      exact hcol0 x y h
    · have hy' : y = (⟨j, hjlt⟩ : Fin m) := Fin.ext h
      rcases (by omega : x.val < r ∨ x.val = r ∨ x.val = r + 1) with hx | hx | hx
      · have h3 : (actSeq B2 σ3) (x,y) = B2 (x,y) := hfix3r x y hx
        have h2 : B2 (x,y) = B1 (x,y) := by
          rw [hB2, actSeq_eq_permOf, Equiv.trans_apply, hfix2r (x,y) hx]
        have h1 : B1 (x,y) = B0 (x,y) := by
          rw [hB1, actSeq_eq_permOf, Equiv.trans_apply, hfix1r' (x,y) hx]
        rw [actSeq_append, actSeq_append, actSeq_append, ← hB0, ← hB1, ← hB2, h3, h2, h1]
        exact habove0 x y hx
      · have hx' : x = (⟨r, by omega⟩ : Fin n) := Fin.ext hx
        have h3 : (actSeq B2 σ3) c(r,j) = B2 c(r,j) := hfix3J
        have h2 : B2 c(r,j) = B1 c(r,j) := by
          rw [hB2, actSeq_eq_permOf, Equiv.trans_apply, hfix2cell]
        rw [hx', hy', actSeq_append, actSeq_append, actSeq_append, ← hB0, ← hB1, ← hB2,
          h3, h2, hB1, heff1, hT1]
      · have hx' : x = (⟨r+1, by omega⟩ : Fin n) := Fin.ext hx
        rw [hx', hy', actSeq_append, actSeq_append, actSeq_append, ← hB0, ← hB1, ← hB2,
          heff3, hT2]
  · rw [List.length_append, List.length_append, List.length_append]
    have hlen0 : σ0.length ≤ n + m := by
      rw [hσ0, length_moveToWord]
      have h1 : Nat.dist p0.1.val (r+1) ≤ n := by rw [Nat.dist_eq_max_sub_min]; omega
      have h2 : Nat.dist p0.2.val j ≤ m := by rw [Nat.dist_eq_max_sub_min]; omega
      omega
    have hlen2 : σ2.length ≤ n + m := by
      rw [hσ2, length_moveToWordHV]
      have h1 : Nat.dist (blank B1).2.val (j+1) ≤ m := by rw [Nat.dist_eq_max_sub_min]; omega
      have h2 : Nat.dist (blank B1).1.val r ≤ n := by rw [Nat.dist_eq_max_sub_min]; omega
      omega
    omega

/-! ### The two-row solver -/

/-- **The two-row solver.**  With rows `< r` already correct and `r + 2 = n`, solve the last
two rows in `O(m²)` moves. -/
theorem solveStrip2Aux (r : ℕ) (hr : r + 1 < n) (hr2 : r + 2 = n) (hm : 4 ≤ m) :
    ∀ (k : ℕ), ∀ (j : ℕ), m - j = k → j ≤ m →
      ∀ (B : Board n m) [NeZero (n * m)],
        (∀ (x : Fin n) (y : Fin m), x.val < r → B (x,y) = target n m (x,y)) →
        (∀ (x : Fin n) (y : Fin m), y.val < j → B (x,y) = target n m (x,y)) →
        Reachable B (target n m) →
        ∃ σ : List Dir, actSeq B σ = target n m ∧
          σ.length ≤ (m - j) * (600 * (n + m)) + 6 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro j hk hj B _ habove hcol hreach
    by_cases hj3 : j + 3 ≤ m
    · obtain ⟨σ1, habove1, hcol1, hlen1⟩ :=
        placeColumn2 r hr hr2 hm j hj3 B habove hcol
      have hreach1 : Reachable (actSeq B σ1) (target n m) :=
        reachable_trans (reachable_symm (by omega) (by omega) ⟨σ1, rfl⟩) hreach
      obtain ⟨σ2, heff2, hlen2⟩ :=
        ih (m - (j+1)) (by omega) (j+1) (by omega) (by omega) (actSeq B σ1) habove1 hcol1
          hreach1
      refine ⟨σ1 ++ σ2, ?_, ?_⟩
      · rw [actSeq_append]; exact heff2
      · rw [List.length_append]
        have hmj : m - j = m - (j+1) + 1 := by omega
        calc σ1.length + σ2.length
            ≤ 600 * (n + m) + ((m - (j+1)) * (600 * (n + m)) + 6) := add_le_add hlen1 hlen2
          _ = (m - j) * (600 * (n + m)) + 6 := by rw [hmj]; ring
    · have hjm : m - 2 ≤ j := by omega
      have hout : ∀ z : Cell n m,
          z ∉ Set.range (blk (n := n) (m := m) (by omega) (by omega)) → B z = target n m z := by
        intro z hz
        rw [mem_range_blk] at hz
        push Not at hz
        rcases (by omega : z.1.val < r ∨ z.2.val < j) with h | h
        · exact habove z.1 z.2 h
        · exact hcol z.1 z.2 h
      obtain ⟨σ, heff, hlen⟩ := solveBlock22 B (by omega) hm hout hreach
      exact ⟨σ, heff, by omega⟩

/-- **The two-row solver**, `j = 0` case. -/
theorem solveStrip2 (r : ℕ) (hr : r + 1 < n) (hr2 : r + 2 = n) (hm : 4 ≤ m)
    (B : Board n m) [NeZero (n * m)]
    (habove : ∀ (x : Fin n) (y : Fin m), x.val < r → B (x,y) = target n m (x,y))
    (hreach : Reachable B (target n m)) :
    ∃ σ : List Dir, actSeq B σ = target n m ∧
      σ.length ≤ m * (600 * (n + m)) + 6 := by
  obtain ⟨σ, h1, h2⟩ :=
    solveStrip2Aux r hr hr2 hm (m - 0) 0 rfl (by omega) B habove (fun x y hy => by omega) hreach
  exact ⟨σ, h1, by simpa using h2⟩

/-- **Parberry's reduction-of-order algorithm.**  A reachable `n × m` board with `n ≥ 3` and
`m ≥ 4` is solved in `O(n³)` moves. -/
theorem solveBoard (B : Board n m) [NeZero (n * m)] (hn : 3 ≤ n) (hm : 4 ≤ m)
    (hreach : Reachable B (target n m)) :
    ∃ σ : List Dir, actSeq B σ = target n m ∧
      σ.length ≤ (n - 2) * (m * (251 * (n + m))) + (m * (600 * (n + m)) + 6) := by
  obtain ⟨σ1, h1, hlen1⟩ := solveRows B hn hm
  have hB : ∀ (x : Fin n) (y : Fin m), x.val < n - 2 →
      (actSeq B σ1) (x,y) = target n m (x,y) := fun x y hx => h1 x y (by omega)
  have hreach1 : Reachable (actSeq B σ1) (target n m) :=
    reachable_trans (reachable_symm (by omega) (by omega) ⟨σ1, rfl⟩) hreach
  obtain ⟨σ2, h2, hlen2⟩ :=
    solveStrip2 (n - 2) (by omega) (by omega) hm (actSeq B σ1) hB hreach1
  refine ⟨σ1 ++ σ2, ?_, ?_⟩
  · rw [actSeq_append]; exact h2
  · rw [List.length_append]; exact add_le_add hlen1 hlen2

end Zhong
