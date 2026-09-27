import SlidingPuzzle.Hub.GeomJump

/-! # jump: relocation between aligned squares

The blank walks inside `E`'s reservoir to a cell aligned with a reservoir cell
`z` of `Z` and jumps there (the tile at `z` goes to `E`). If the class-`y` tile
of `Z` is not that tile, a three-cycle in a box covering both squares swaps it
into `E` and returns the tile from `z` to `Z`. -/
namespace SlidingPuzzle.Hub
open Classical

variable {n k s : ℕ} [NeZero n]

/-- jump realized on the board. -/
theorem simulate_jump (hd : HDims n k s) {B : Board n} {σ : IState k} (hR : Rel hd B σ)
    {E Z y : Sq k} (hpre : σ.Pre (.jump E Z y)) :
    ∃ C : Board n, ∃ p : Path B C, Rel hd C (σ.step s (.jump E Z y)) ∧
      p.inefficientMoves ≤ σ.cost s (.jump E Z y) := by
  obtain ⟨hbl, hEZ, hal, hcnt⟩ := hpre
  obtain ⟨hRrow, hRcol, hRcnt, hRbl⟩ := hR
  rw [hbl] at hRbl
  obtain ⟨e0, z, he0, hz, hzrow, hjump⟩ := jump_ends hd hal
  obtain ⟨r0, c0, hr0, hc0, hbox⟩ := jump_box (n := n) hd hal
  have hke0 : keyOf hd e0 = some E := keyOf_reservoir hd he0
  have hkz : keyOf hd z = some Z := keyOf_reservoir hd hz
  have hZE : Z ≠ E := Ne.symm hEZ
  have he0z : e0 ≠ z := ne_of_keyOf (by rw [hke0, hkz]; exact fun e => hEZ (Option.some.inj e))
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
  suffices H : ∃ C : Board n, ∃ p : Path B2 C, blank C = z ∧
      (∀ x, keyOf hd x = none → C x = B2 x) ∧ KeepKey hd B C {B t} ∧
      keyOf hd (position C (B t)) = some E ∧ p.inefficientMoves ≤ 52 * ((sqDist E Z + 1) * s) by
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
      rw [hCbl]; exact hz
    · simp only [IState.cost, Path.inefficientMoves_append]
      have c1 := p1.inefficientMoves_le_length
      have e1 : 52 * ((sqDist E Z + 1) * s) = 52 * (sqDist E Z * s) + 52 * s := by ring
      have e2 : 65 * s * (1 + sqDist E Z) = 65 * (sqDist E Z * s) + 65 * s := by ring
      have := hd.room
      omega
  by_cases htz : t = z
  · subst htz
    refine ⟨B2, .nil B2, hbB2, fun _ _ => rfl, ?_, ?_, by simp [Path.inefficientMoves]⟩
    · intro t' h0 ht'
      rw [Finset.mem_singleton] at ht'
      apply (K1.trans K2) t' h0
      simp only [Finset.empty_union, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun e => h0 (by rw [e]; rfl), ht'⟩
    · rw [position_eq_of_apply hB2e0]; exact hke0
  · obtain ⟨u, hu, hurow, hut⟩ := exists_reservoir_other hd Z t
    have hku : keyOf hd u = some Z := keyOf_reservoir hd hu
    have huz : u ≠ z := cell_ne_of_fst (by rw [hurow]; exact fun e => hzrow e.symm)
    have huE : ¬ reservoir k s E u := fun hr => by
      rw [keyOf_reservoir hd hr] at hku; exact hEZ (Option.some.inj hku)
    have he0t : e0 ≠ t := ne_of_keyOf (by rw [hke0, hkt]; exact fun e => hEZ (Option.some.inj e))
    have he0u : e0 ≠ u := ne_of_keyOf (by rw [hke0, hku]; exact fun e => hEZ (Option.some.inj e))
    have hB2t : B2 t = B t := hB2 t htE htz
    have hB2u : B2 u = B u := hB2 u huE huz
    have hU0 : (B2 u).val ≠ 0 := val_ne_zero_of_ne_blank (by rw [hbB2]; exact huz)
    have inE := hbox E (Or.inl rfl)
    have inZ := hbox Z (Or.inr rfl)
    obtain ⟨C, p3, hp3, hCe, hCt, hCu, hCx⟩ := exists_box_three_cycle B2 r0 c0
      ((sqDist E Z + 1) * s) (by have := hd.room; have := hd.two_le; nlinarith) hr0 hc0
      (by rw [hbB2]; exact inZ z (inBox_of_reservoir hd hz)) e0 t u
      (inE e0 (inBox_of_reservoir hd he0)) (inZ t (inBox_of_region hd htZ))
      (inZ u (inBox_of_reservoir hd hu)) he0t he0u (Ne.symm hut)
      (by rw [hB2e0]; exact fun e => hZt0 (by rw [e]; rfl))
      (by rw [hB2t]; exact fun e => htT (by rw [e]; rfl))
      (fun e => hU0 (by rw [e]; rfl))
    have K3 : KeepKey hd B2 C {B z, B t, B u} := by
      have := keepKey_of_agree_outside hd (B := B2) (C := C) {e0, t, u}
        (fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
          exact hCx x hx.1 hx.2.1 hx.2.2)
      rwa [Finset.image_insert, Finset.image_insert, Finset.image_singleton, hB2e0, hB2t,
        hB2u] at this
    have K := (K1.trans K2).trans K3
    refine ⟨C, p3, ?_, ?_, ?_, ?_, hp3.trans' p3.inefficientMoves_le_length⟩
    · apply blank_eq_of_apply
      rw [hCx z (Ne.symm he0z) (fun e => htz e.symm) (Ne.symm huz), hB2z]
    · intro x hx
      apply hCx
      · exact ne_of_keyOf (by rw [hx, hke0]; simp)
      · exact ne_of_keyOf (by rw [hx, hkt]; simp)
      · exact ne_of_keyOf (by rw [hx, hku]; simp)
    · intro t' h0 ht'
      rw [Finset.mem_singleton] at ht'
      by_cases e1 : t' = B z
      · subst e1
        have : position C (B z) = u := position_eq_of_apply (by rw [hCu, hB2e0])
        rw [this, show position B (B z) = z by simp [position], hku, hkz]
      by_cases e2 : t' = B u
      · subst e2
        have : position C (B u) = t := position_eq_of_apply (by rw [hCt, hB2u])
        rw [this, show position B (B u) = u by simp [position], hku, hkt]
      apply K t' h0
      simp only [Finset.empty_union, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      exact ⟨⟨fun e => h0 (by rw [e]; rfl), e1⟩, e1, ht', e2⟩
    · rw [position_eq_of_apply (show C e0 = B t by rw [hCe, hB2t])]; exact hke0

end SlidingPuzzle.Hub
