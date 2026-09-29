import SlidingPuzzle.Port.Prim

/-! # Landing from a port

The blank walks inside a port box to a cell `w0`, jumps to the drop cell `d` of
the port's line (the tile there goes to `w0`), steps or jumps into position `0`
of the lane (the lane's head drops onto `d`) and walks along the lane to the
insertion position. Only the head changes its refined key. -/
namespace SlidingPuzzle.Port
open Classical
open SlidingPuzzle.Hub (Sq HDims sqOf classOf mkCell mkCell_fst mkCell_snd cell_ext
  div_eq_iff_bounds moveCost moveCost_le_one exists_move_step exists_vjump_step exists_hjump_step
  exists_swap_walk apply_blank blank_eq_of_apply val_ne_zero_of_ne_blank)
open SlidingPuzzle.Hub.LayoutAux
open SlidingPuzzle.Tree

variable {n k s q σ : ℕ} [NeZero n] (L : LaneSys k q)

theorem KeepK.erase_zero {β : Type*} {κ : Cell n → β} {B C : Board n} {t : Tile n}
    (h : KeepK κ B C {0, t}) : KeepK κ B C {t} := by
  intro t' h0 ht'
  apply h t' h0
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht' ⊢
  exact ⟨fun e => h0 (by rw [e]; rfl), ht'⟩

/-- The landing, generically: box walk, jump to the drop cell, into the lane, lane walk. -/
theorem land_core (pd : PDims n k s q σ) (h3 : 3 ≤ σ) (B : Board n) {Q : Sq k} {pt : Pt}
    (hbl : InBoxOf s σ Q pt (blank B)) {w0 d : Cell n} (hw0 : InBoxOf s σ Q pt w0)
    (hd : rkey L s σ pd.hd d = some (Q, some pt)) (hdbox : ¬ InBoxOf s σ Q pt d)
    (c1 : ℕ) (hj1 : ∀ B' : Board n, blank B' = w0 →
      ∃ p : Path B' (swapCells B' (blank B') d), p.inefficientMoves ≤ c1)
    (P : ℕ) (f : ℕ → Cell n) (hf : ∀ t, t ≤ P → rkey L s σ pd.hd (f t) = none)
    (hinj : ∀ t t', t ≤ P → t' ≤ P → f t = f t' → t = t')
    (c2 : ℕ) (hj2 : ∀ B' : Board n, blank B' = d →
      ∃ p : Path B' (swapCells B' (blank B') (f 0)), p.inefficientMoves ≤ c2)
    (cost : ℕ → Tile n → ℕ)
    (hstep : ∀ t, t < P → ∀ B' : Board n, blank B' = f t →
      ∃ p : Path B' (swapCells B' (blank B') (f (t+1))),
        p.inefficientMoves ≤ cost t (B' (f (t+1)))) :
    ∃ C : Board n, ∃ p : Path B C, blank C = f P ∧
      (∀ t, t < P → C (f t) = B (f (t+1))) ∧
      C d = B (f 0) ∧
      (∀ x, ¬ InBoxOf s σ Q pt x → x ≠ d → (∀ t, t ≤ P → x ≠ f t) → C x = B x) ∧
      KeepK (rkey L s σ pd.hd) B C {B (f 0)} ∧
      p.inefficientMoves ≤ 2 * σ + c1 + c2 + ∑ t ∈ Finset.range P, cost t (B (f (t+1))) := by
  have hfbox : ∀ t, t ≤ P → ¬ InBoxOf s σ Q pt (f t) := fun t ht hb => by
    have := rkey_inBoxOf L pd hb; rw [hf t ht] at this; cases this
  have hfd : ∀ t, t ≤ P → f t ≠ d := fun t ht e => by
    have := hf t ht; rw [e, hd] at this; cases this
  have hw0d : w0 ≠ d := fun e => hdbox (by rw [← e]; exact hw0)
  -- A: walk inside the box
  obtain ⟨B1, p1, hbB1, hi1, hf1, K1⟩ := exists_box_walk L pd h3 B hbl hw0
  -- B: jump onto the drop cell
  set B2 := swapCells B1 (blank B1) d with hB2def
  obtain ⟨p2, hp2⟩ : ∃ p : Path B1 B2, p.inefficientMoves ≤ c1 := hj1 B1 hbB1
  have hbB2 : blank B2 = d := blank_swapCells B1 _
  have hB2x : ∀ x, x ≠ w0 → x ≠ d → B2 x = B1 x := fun x h1 h2 =>
    swapCells_preserves B1 (by rw [hbB1]; exact h1) h2
  have hB2w0 : B2 w0 = B d := by
    rw [hB2def, ← hbB1, swapCells_at_left, hf1 d hdbox]
  have K2 : KeepK (rkey L s σ pd.hd) B1 B2 ∅ := keepK_of_agree (rkey L s σ pd.hd)
    (fun x => x = w0 ∨ x = d)
    (fun x y hx hy => by
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
        simp only [rkey_inBoxOf L pd hw0, hd])
    (fun x hx => by simp only [not_or] at hx; exact hB2x x hx.1 hx.2)
  -- C: into position `0` of the lane
  set B3 := swapCells B2 (blank B2) (f 0) with hB3def
  obtain ⟨p3, hp3⟩ : ∃ p : Path B2 B3, p.inefficientMoves ≤ c2 := hj2 B2 hbB2
  have hbB3 : blank B3 = f 0 := blank_swapCells B2 _
  have hf0d : f 0 ≠ d := hfd 0 (Nat.zero_le _)
  have hf0w : f 0 ≠ w0 := fun e => hfbox 0 (Nat.zero_le _) (by rw [e]; exact hw0)
  have hB3x : ∀ x, x ≠ d → x ≠ f 0 → B3 x = B2 x := fun x h1 h2 =>
    swapCells_preserves B2 (by rw [hbB2]; exact h1) h2
  have hB2f : ∀ t, t ≤ P → B2 (f t) = B (f t) := fun t ht => by
    rw [hB2x _ (fun e => hfbox t ht (by rw [e]; exact hw0)) (hfd t ht), hf1 _ (hfbox t ht)]
  have hB3d : B3 d = B (f 0) := by
    rw [hB3def, ← hbB2, swapCells_at_left, hB2f 0 (Nat.zero_le _)]
  have K3 : KeepK (rkey L s σ pd.hd) B2 B3 {0, B (f 0)} := by
    have := keepK_of_agree_outside (rkey L s σ pd.hd) (B := B2) (C := B3) {d, f 0}
      (fun x hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        exact hB3x x hx.1 hx.2)
    rwa [Finset.image_insert, Finset.image_singleton, ← hbB2, apply_blank,
      hB2f 0 (Nat.zero_le _)] at this
  -- D: the lane walk
  obtain ⟨C, p4, hbC, hC4, hfix4, hi4⟩ := exists_swap_walk P f cost hinj hstep B3 hbB3
  have hB3f : ∀ t, 1 ≤ t → t ≤ P → B3 (f t) = B (f t) := fun t h1 h2 => by
    rw [hB3x _ (hfd t h2) (fun e => by have := hinj t 0 h2 (Nat.zero_le _) e; omega), hB2f t h2]
  have K4 : KeepK (rkey L s σ pd.hd) B3 C ∅ := keepK_of_agree (rkey L s σ pd.hd)
    (fun x => ∃ t, t ≤ P ∧ x = f t)
    (fun x y hx hy => by
      obtain ⟨t, ht, rfl⟩ := hx; obtain ⟨t', ht', rfl⟩ := hy; rw [hf t ht, hf t' ht'])
    (fun x hx => hfix4 x (fun t ht e => hx ⟨t, ht, e⟩))
  have hCd : C d = B (f 0) := by
    rw [hfix4 d (fun t ht e => hfd t ht e.symm), hB3d]
  refine ⟨C, ((p1.append p2).append p3).append p4, hbC, ?_, hCd, ?_, ?_, ?_⟩
  · intro t ht
    rw [hC4 t ht, hB3f (t + 1) (by omega) (by omega)]
  · intro x h1 h2 h3
    rw [hfix4 x h3, hB3x x h2 (h3 0 (Nat.zero_le _)),
      hB2x x (fun e => h1 (by rw [e]; exact hw0)) h2, hf1 x h1]
  · have := ((K1.trans K2).trans K3).trans K4
    simp only [Finset.empty_union, Finset.union_empty] at this
    exact KeepK.erase_zero this
  · simp only [Path.inefficientMoves_append]
    have hs : ∑ t ∈ Finset.range P, cost t (B3 (f (t + 1))) =
        ∑ t ∈ Finset.range P, cost t (B (f (t + 1))) :=
      Finset.sum_congr rfl fun t ht => by
        rw [Finset.mem_range] at ht; rw [hB3f (t + 1) (by omega) (by omega)]
    omega

end SlidingPuzzle.Port
