import SlidingPuzzle.Hub.PrimRes

/-! # Insertion by a jump and a three-cycle

The blank sits on a corridor cell `v` inside the square box of `Q`. It jumps
into the reservoir of `Q` (cell `w`), and a three-cycle in the box of `Q`
brings a tile of class `y` from the region of `Q` to `v`. Only `v` and cells of
the region of `Q` change, and only the inserted tile changes its key. The
three-cycle is staged from a corner of the box near `v`, `w` and the spare
reservoir cell (`exists_box_three_cycle_near`), so it costs `10 s + O(k)`. -/
namespace SlidingPuzzle.Hub
open Classical

variable {n k s : ℕ} [NeZero n]

theorem insert_by_cycle (hd : HDims n k s) (B : Board n) {Q y : Sq k} {v w : Cell n}
    (hbv : blank B = v) (hv : keyOf hd v = none) (hw : reservoir k s Q w)
    (hvbox : InBox (Q.1.val * s) (Q.2.val * s) s v)
    (hT : 1 ≤ regionCount hd B Q y) (cj : ℕ)
    (hjump : ∃ p : Path B (swapCells B (blank B) w), p.inefficientMoves ≤ cj)
    (fr fc : Bool) {ro co : ℕ} (hro : k ≤ ro) (hro' : ro < s) (hco : k ≤ co) (hco' : co + 2 < s)
    (hD : ∀ j, j ≤ 2 → cornerDist (Q.1.val * s) (Q.2.val * s) s fr fc w v
      (mkCell n (Q.1.val * s + ro) (Q.2.val * s + co + j)) ≤ 6 * k + 7) :
    ∃ C : Board n, ∃ p : Path B C, ∃ T : Tile n, T.val ≠ 0 ∧ classOf hd T = y ∧
      keyOf hd (position B T) = some Q ∧ C v = T ∧ blank C = w ∧
      (∀ x, x ≠ v → keyOf hd x ≠ some Q → C x = B x) ∧ KeepKey hd B C {T} ∧
      p.inefficientMoves ≤ cj + 10 * s + 492 * k + 1010 := by
  obtain ⟨t, htQ, htT, htc⟩ := exists_of_regionCount hd B hT
  obtain ⟨p1, hp1⟩ := hjump
  have hkw : keyOf hd w = some Q := keyOf_reservoir hd hw
  have hkt : keyOf hd t = some Q := (keyOf_eq_some hd).mpr htQ
  have hvw : v ≠ w := ne_of_keyOf (by rw [hv, hkw]; simp)
  have hvt : v ≠ t := ne_of_keyOf (by rw [hv, hkt]; simp)
  let B4 := swapCells B (blank B) w
  have hB4v : B4 v = B w := by simp only [B4, ← hbv, swapCells_at_left]
  have hB4w : B4 w = 0 := by simp only [B4, swapCells_at_right, apply_blank]
  have hB4x : ∀ x, x ≠ v → x ≠ w → B4 x = B x := fun x h1 h2 =>
    swapCells_preserves B (by rw [hbv]; exact h1) h2
  have hW0 : (B w).val ≠ 0 := val_ne_zero_of_ne_blank (by rw [hbv]; exact hvw.symm)
  have K1 : KeepKey hd B B4 {0, B w} := by
    have := keepKey_of_agree_outside hd (B := B) (C := B4) {v, w}
      (fun x hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        exact hB4x x hx.1 hx.2)
    rwa [Finset.image_insert, Finset.image_singleton, ← hbv, apply_blank] at this
  have hposT : position B (B t) = t := by simp [position]
  by_cases htw : t = w
  · subst htw
    refine ⟨B4, p1, B t, htT, htc, by rw [hposT]; exact hkt, hB4v, blank_eq_of_apply hB4w,
      fun x h1 h2 => hB4x x h1 (fun e => h2 (by rw [e]; exact hkw)), ?_, by omega⟩
    intro t' h0 ht'
    exact K1 t' h0 (by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht' ⊢
      rintro (e | e)
      · exact h0 (by rw [e]; rfl)
      · exact ht' e)
  · obtain ⟨j, hj, hu, hut, huw⟩ := exists_reservoir_near hd Q hro hro' hco hco' t w
    set u := mkCell n (Q.1.val * s + ro) (Q.2.val * s + co + j) with hudef
    have hku : keyOf hd u = some Q := keyOf_reservoir hd hu
    have hvu : v ≠ u := ne_of_keyOf (by rw [hv, hku]; simp)
    have hB4t : B4 t = B t := hB4x t (Ne.symm hvt) htw
    have hB4u : B4 u = B u := hB4x u (Ne.symm hvu) huw
    have hU0 : (B u).val ≠ 0 := val_ne_zero_of_ne_blank (by rw [hbv]; exact hvu.symm)
    have hbl4 : blank B4 = w := blank_swapCells B w
    obtain ⟨C, p2, hp2, hCv, hCt, hCu, hCx⟩ := exists_box_three_cycle_near B4 (Q.1.val * s)
      (Q.2.val * s) s fr fc (by have := hd.room; have := hd.two_le; omega) (hd.band_le Q.1.isLt)
      (hd.band_le Q.2.isLt)
      (by rw [hbl4]; exact inBox_of_reservoir hd hw) v t u hvbox (inBox_of_region hd htQ)
      (inBox_of_reservoir hd hu) hvt hvu (Ne.symm hut)
      (by rw [hB4v]; exact fun e => hW0 (by rw [e]; rfl))
      (by rw [hB4t]; exact fun e => htT (by rw [e]; rfl))
      (by rw [hB4u]; exact fun e => hU0 (by rw [e]; rfl))
    have hCw : C w = 0 := by
      rw [hCx w hvw.symm (fun e => htw e.symm) huw.symm, hB4w]
    have K2 : KeepKey hd B4 C {B w, B t, B u} := by
      have := keepKey_of_agree_outside hd (B := B4) (C := C) {v, t, u}
        (fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
          exact hCx x hx.1 hx.2.1 hx.2.2)
      rwa [Finset.image_insert, Finset.image_insert, Finset.image_singleton, hB4v, hB4t,
        hB4u] at this
    have K := K1.trans K2
    refine ⟨C, p1.append p2, B t, htT, htc, by rw [hposT]; exact hkt, by rw [hCv, hB4t],
      blank_eq_of_apply hCw, ?_, ?_, ?_⟩
    · intro x h1 h2
      have hxt : x ≠ t := fun e => h2 (by rw [e]; exact hkt)
      have hxu : x ≠ u := fun e => h2 (by rw [e]; exact hku)
      have hxw : x ≠ w := fun e => h2 (by rw [e]; exact hkw)
      rw [hCx x h1 hxt hxu, hB4x x h1 hxw]
    · intro t' h0 ht'
      rw [Finset.mem_singleton] at ht'
      by_cases e1 : t' = B w
      · subst e1
        have : position C (B w) = u := position_eq_of_apply (by rw [hCu, hB4v])
        rw [this, show position B (B w) = w by simp [position], hku, hkw]
      by_cases e2 : t' = B u
      · subst e2
        have : position C (B u) = t := position_eq_of_apply (by rw [hCt, hB4u])
        rw [this, show position B (B u) = u by simp [position], hku, hkt]
      apply K t' h0
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨⟨fun e => h0 (by rw [e]; rfl), e1⟩, e1, ht', e2⟩
    · rw [Path.inefficientMoves_append]
      rw [hbl4] at hp2
      have h1 : cornerDist (Q.1.val * s) (Q.2.val * s) s fr fc w v u ≤ 6 * k + 7 := hD j hj
      omega

end SlidingPuzzle.Hub
