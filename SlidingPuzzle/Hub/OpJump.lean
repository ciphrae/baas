import SlidingPuzzle.Hub.GeomJump

/-! # jump: relocation between aligned squares

The blank walks inside `E`'s reservoir to a cell aligned with a reservoir cell
`z` of `Z` and jumps there (the tile at `z` goes to `E`). If the class-`y` tile
of `Z` is not that tile, a three-cycle in a box covering both squares swaps it
into `E` and returns the tile from `z` to `Z`. -/
namespace SlidingPuzzle.Hub
open Classical

variable {n k s : ℕ} [NeZero n]

/-- jump realized on the board: jump into `Z`, line up a class-`y` tile by a
three-cycle inside `Z`'s box, jump back, and jump that tile across. -/
theorem simulate_jump (hd : HDims n k s) {B : Board n} {σ : IState k} (hR : Rel hd B σ)
    {E Z y : Sq k} (hpre : σ.Pre (.jump E Z y)) :
    ∃ C : Board n, ∃ p : Path B C, Rel hd C (σ.step s (.jump E Z y)) ∧
      p.inefficientMoves ≤ σ.cost s (.jump E Z y) := by
  obtain ⟨hbl, hEZ, hal, hcnt⟩ := hpre
  obtain ⟨hRrow, hRcol, hRcnt, hRbl⟩ := hR
  rw [hbl] at hRbl
  obtain ⟨e0, z, z', he0, hz, hz', hzz', hzrow, hz'row, hjump, hback, hjump'⟩ := jump_ends2 hd hal
  have hke0 : keyOf hd e0 = some E := keyOf_reservoir hd he0
  have hkz : keyOf hd z = some Z := keyOf_reservoir hd hz
  have hkz' : keyOf hd z' = some Z := keyOf_reservoir hd hz'
  have hZE : Z ≠ E := Ne.symm hEZ
  have he0z : e0 ≠ z := ne_of_keyOf (by rw [hke0, hkz]; exact fun e => hEZ (Option.some.inj e))
  have he0z' : e0 ≠ z' := ne_of_keyOf (by rw [hke0, hkz']; exact fun e => hEZ (Option.some.inj e))
  -- walk and jump
  obtain ⟨B1, p1, hbB1, hl1, hf1⟩ := exists_reservoir_walk hd B hRbl he0
  obtain ⟨p2, hp2⟩ := hjump B1 hbB1
  let B2 := swapCells B1 (blank B1) z
  have hbB2 : blank B2 = z := blank_swapCells B1 _
  have hzE : ¬ reservoir k s E z := fun hr => by
    rw [keyOf_reservoir hd hr] at hkz; exact hEZ (Option.some.inj hkz)
  have hB2e0 : B2 e0 = B z := by
    change swapCells B1 (blank B1) z e0 = B z
    rw [← hbB1, swapCells_at_left, hf1 z hzE]
  have hB2 : ∀ x, ¬ reservoir k s E x → x ≠ z → B2 x = B x := by
    intro x h1 h2
    change swapCells B1 (blank B1) z x = B x
    rw [swapCells_preserves B1 (by rw [hbB1]; exact fun e => h1 (e ▸ he0)) h2, hf1 x h1]
  have hB2z : B2 z = 0 := by rw [← hbB2]; exact apply_blank B2
  have hZt0 : (B z).val ≠ 0 := val_ne_zero_of_ne_blank (fun e => hzE (e ▸ hRbl))
  have K1 : KeepKey hd B B1 ∅ := keepKey_of_agree hd (reservoir k s E)
    (fun x y hx hy => by rw [keyOf_reservoir hd hx, keyOf_reservoir hd hy]) hf1
  have K2 : KeepKey hd B1 B2 {0, B z} := by
    have := keepKey_of_agree_outside hd (B := B1) (C := B2) {e0, z}
      (fun x hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        exact swapCells_preserves B1 (by rw [hbB1]; exact hx.1) hx.2)
    rwa [Finset.image_insert, Finset.image_singleton, ← hbB1, apply_blank,
      hf1 z hzE] at this
  -- the class-y tile of Z
  obtain ⟨t, htZ, htT, htc⟩ := exists_of_regionCount hd B (by rw [hRcnt]; exact hcnt)
  have hkt : keyOf hd t = some Z := (keyOf_eq_some hd).mpr htZ
  have htE : ¬ reservoir k s E t := fun hr => by
    rw [keyOf_reservoir hd hr] at hkt; exact hEZ (Option.some.inj hkt)
  -- the final board: general facts needed for `Rel`
  suffices H : ∃ C : Board n, ∃ p : Path B2 C, reservoir k s Z (blank C) ∧
      (∀ x, keyOf hd x = none → C x = B2 x) ∧ KeepKey hd B C {B t} ∧
      keyOf hd (position C (B t)) = some E ∧
      p.inefficientMoves ≤ 52 * s + 13 * (sqDist E Z * s + 2) + 13 * (sqDist E Z * s + 6) by
    obtain ⟨C, p3, hCbl, hCc, K, hkC, hi3⟩ := H
    have hcor : ∀ x, keyOf hd x = none → C x = B x := by
      intro x hx
      rw [hCc x hx]
      apply hB2
      · exact fun hr => by rw [keyOf_reservoir hd hr] at hx; cases hx
      · exact ne_of_keyOf (by rw [hx, hkz]; simp)
    refine ⟨C, (p1.append p2).append p3, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro H q hq
      simp only [IState.step]
      rw [hcor _ (keyOf_rowCell hd H q hq)]
      exact hRrow H q hq
    · intro V q hq
      simp only [IState.step]
      rw [hcor _ (keyOf_colCell hd V q hq)]
      exact hRcol V q hq
    · intro Q y'
      simp only [IState.step]
      have hkB : keyOf hd (position B (B t)) = some Z := by
        rw [show position B (B t) = t by simp [position]]; exact hkt
      rw [regionCount_move1 hd K htT hZE hkB hkC Q y', htc]
      have hc : regionCount hd B = σ.cnt := funext fun Q => funext fun y => hRcnt Q y
      rw [hc]
    · simp only [IState.step]
      exact hCbl
    · simp only [IState.cost, Path.inefficientMoves_append]
      have c1 := p1.inefficientMoves_le_length
      have e1 : (s + 3) * (54 + 39 * sqDist E Z) =
          54 * s + 39 * (sqDist E Z * s) + 162 + 117 * sqDist E Z := by ring
      have e2 : 13 * (sqDist E Z * s + 2) = 13 * (sqDist E Z * s) + 26 := by ring
      have e3 : 13 * (sqDist E Z * s + 6) = 13 * (sqDist E Z * s) + 78 := by ring
      omega
  by_cases htz : t = z
  · subst htz
    refine ⟨B2, .nil B2, by rw [hbB2]; exact hz, fun _ _ => rfl, ?_, ?_,
      by simp [Path.inefficientMoves]⟩
    · intro t' h0 ht'
      rw [Finset.mem_singleton] at ht'
      apply (K1.trans K2) t' h0
      simp only [Finset.empty_union, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun e => h0 (by rw [e]; rfl), ht'⟩
    · rw [position_eq_of_apply hB2e0]; exact hke0
  have hB2t : B2 t = B t := hB2 t htE htz
  have hz'E : ¬ reservoir k s E z' := fun hr => by
    rw [keyOf_reservoir hd hr] at hkz'; exact hEZ (Option.some.inj hkz')
  have hB2z' : B2 z' = B z' := hB2 z' hz'E (Ne.symm hzz')
  -- a class-y tile at `z'`, by a three-cycle inside `Z`'s box unless it is there
  obtain ⟨C3, p3, hp3, hbC3, hC3z', hC3out, K3⟩ : ∃ C3 : Board n, ∃ p : Path B2 C3,
      p.inefficientMoves ≤ 52 * s ∧ blank C3 = z ∧ C3 z' = B t ∧
      (∀ x, keyOf hd x ≠ some Z → C3 x = B2 x) ∧ KeepKey hd B2 C3 ∅ := by
    by_cases htz' : t = z'
    · subst htz'
      exact ⟨B2, .nil B2, by simp [Path.inefficientMoves], hbB2, hB2t, fun _ _ => rfl,
        KeepKey.refl hd B2 ∅⟩
    obtain ⟨u, hu, hurow, hut⟩ := exists_reservoir_other hd Z t
    have hku : keyOf hd u = some Z := keyOf_reservoir hd hu
    have huz : u ≠ z := cell_ne_of_fst (by rw [hurow]; exact fun e => hzrow e.symm)
    have huz' : u ≠ z' := cell_ne_of_fst (by rw [hurow]; exact fun e => hz'row e.symm)
    have huE : ¬ reservoir k s E u := fun hr => by
      rw [keyOf_reservoir hd hr] at hku; exact hEZ (Option.some.inj hku)
    have hB2u : B2 u = B u := hB2 u huE huz
    have hU0 : (B2 u).val ≠ 0 := val_ne_zero_of_ne_blank (by rw [hbB2]; exact huz)
    have hZ'0 : (B2 z').val ≠ 0 := val_ne_zero_of_ne_blank (by rw [hbB2]; exact Ne.symm hzz')
    obtain ⟨C, p, hp, hCa, hCb, hCc, hCx⟩ := exists_box_three_cycle B2 (Z.1.val * s)
      (Z.2.val * s) s (by have := hd.room; have := hd.two_le; omega) (hd.band_le Z.1.isLt)
      (hd.band_le Z.2.isLt) (by rw [hbB2]; exact inBox_of_reservoir hd hz) z' t u
      (inBox_of_reservoir hd hz') (inBox_of_region hd htZ) (inBox_of_reservoir hd hu)
      (Ne.symm htz') (Ne.symm huz') (Ne.symm hut)
      (fun e => hZ'0 (by rw [e]; rfl))
      (by rw [hB2t]; exact fun e => htT (by rw [e]; rfl))
      (fun e => hU0 (by rw [e]; rfl))
    have hout : ∀ x, keyOf hd x ≠ some Z → C x = B2 x := by
      intro x hx
      apply hCx
      · rintro rfl; exact hx hkz'
      · rintro rfl; exact hx hkt
      · rintro rfl; exact hx hku
    refine ⟨C, p, hp.trans' p.inefficientMoves_le_length, ?_, by rw [hCa, hB2t], hout, ?_⟩
    · apply blank_eq_of_apply
      rw [hCx z hzz' (fun e => htz e.symm) (Ne.symm huz), hB2z]
    · exact keepKey_of_agree hd (fun x => keyOf hd x = some Z)
        (fun x y hx hy => by rw [hx, hy]) (fun x hx => hout x hx)
  have hC3e0 : C3 e0 = B z := by rw [hC3out e0 (by rw [hke0]; exact fun e => hEZ (Option.some.inj e)), hB2e0]
  -- jump back to `E`, then jump the tile at `z'` across
  obtain ⟨p4, hp4⟩ := hback C3 hbC3
  let B4 := swapCells C3 (blank C3) e0
  have hbB4 : blank B4 = e0 := blank_swapCells C3 _
  have hB4z : B4 z = B z := by
    change swapCells C3 (blank C3) e0 z = B z
    have h := swapCells_at_left C3 (blank C3) e0
    conv at h => lhs; arg 2; rw [hbC3]
    rw [h, hC3e0]
  have hB4z' : B4 z' = B t := by
    change swapCells C3 (blank C3) e0 z' = B t
    rw [swapCells_preserves C3 (by rw [hbC3]; exact Ne.symm hzz') (Ne.symm he0z'), hC3z']
  obtain ⟨p5, hp5⟩ := hjump' B4 hbB4
  let B5 := swapCells B4 (blank B4) z'
  have hbB5 : blank B5 = z' := blank_swapCells B4 _
  have hB5e0 : B5 e0 = B t := by
    change swapCells B4 (blank B4) z' e0 = B t
    rw [← hbB4, swapCells_at_left, hB4z']
  have hB5z : B5 z = B z := by
    change swapCells B4 (blank B4) z' z = B z
    rw [swapCells_preserves B4 (by rw [hbB4]; exact Ne.symm he0z) hzz', hB4z]
  have hB5x : ∀ x, x ≠ e0 → x ≠ z → x ≠ z' → B5 x = C3 x := by
    intro x h1 h2 h3
    change swapCells B4 (blank B4) z' x = C3 x
    rw [swapCells_preserves B4 (by rw [hbB4]; exact h1) h3]
    change swapCells C3 (blank C3) e0 x = C3 x
    exact swapCells_preserves C3 (by rw [hbC3]; exact h2) h1
  have K4 : KeepKey hd C3 B4 {0, B z} := by
    have := keepKey_of_agree_outside hd (B := C3) (C := B4) {z, e0}
      (fun x hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        exact swapCells_preserves C3 (by rw [hbC3]; exact hx.1) hx.2)
    rwa [Finset.image_insert, Finset.image_singleton, ← hbC3, apply_blank, hC3e0] at this
  have K5 : KeepKey hd B4 B5 {0, B t} := by
    have := keepKey_of_agree_outside hd (B := B4) (C := B5) {e0, z'}
      (fun x hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        exact swapCells_preserves B4 (by rw [hbB4]; exact hx.1) hx.2)
    rwa [Finset.image_insert, Finset.image_singleton, ← hbB4, apply_blank, hB4z'] at this
  have K := (((K1.trans K2).trans K3).trans K4).trans K5
  refine ⟨B5, (p3.append p4).append p5, by rw [hbB5]; exact hz', ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hB5x x (fun e => by rw [e, hke0] at hx; cases hx) (fun e => by rw [e, hkz] at hx; cases hx)
      (fun e => by rw [e, hkz'] at hx; cases hx)]
    exact hC3out x (by rw [hx]; simp)
  · intro t' h0 ht'
    rw [Finset.mem_singleton] at ht'
    by_cases e1 : t' = B z
    · subst e1
      rw [position_eq_of_apply hB5z, show position B (B z) = z by simp [position]]
    have h0' : t' ≠ 0 := fun e => h0 (by rw [e]; rfl)
    apply K t' h0
    simp [h0', e1, ht']
  · rw [position_eq_of_apply hB5e0]; exact hke0
  · simp only [Path.inefficientMoves_append]
    omega

end SlidingPuzzle.Hub
