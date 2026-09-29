import SlidingPuzzle.Port.SimHop

/-! # Carrying a tile by jumps

The blank sits on `a0`. It jumps to `z0` (the tile there goes to `a0`), a local
operation around `z0` puts the tile to carry on `z'`, it jumps back to `a0` (the
tile of `z0` returns) and jumps to `z'`: the carried tile lands on `a0`. -/
namespace SlidingPuzzle.Port
open Classical
open SlidingPuzzle.Hub (Sq HDims sqOf classOf apply_blank blank_eq_of_apply val_ne_zero_of_ne_blank
  exists_vjump_step exists_hjump_step exists_box_three_cycle_near cornerDist InBox)
open SlidingPuzzle.Tree

variable {n : ℕ} [NeZero n]

/-- The jump dance, with a local operation (from `B1` to `M`) while the blank is at `z0`. -/
theorem dance (B : Board n) {a0 z0 z' : Cell n} (hb : blank B = a0) (h1 : a0 ≠ z0) (h2 : z0 ≠ z')
    (h3 : a0 ≠ z') (U : Cell n → Prop) (hUa : ¬ U a0)
    (cJ cM : ℕ)
    (j1 : ∃ p : Path B (swapCells B (blank B) z0), p.inefficientMoves ≤ cJ)
    (j2 : ∀ B' : Board n, blank B' = z0 →
      ∃ p : Path B' (swapCells B' (blank B') a0), p.inefficientMoves ≤ cJ)
    (j3 : ∀ B' : Board n, blank B' = a0 →
      ∃ p : Path B' (swapCells B' (blank B') z'), p.inefficientMoves ≤ cJ)
    (M : Board n) (pm : Path (swapCells B (blank B) z0) M) (hbM : blank M = z0)
    (hpm : pm.inefficientMoves ≤ cM) (hMx : ∀ x, ¬ U x → M x = swapCells B (blank B) z0 x) :
    ∃ C : Board n, ∃ p : Path B C,
      C a0 = M z' ∧ blank C = z' ∧ C z0 = B z0 ∧
      (∀ x, x ≠ a0 → x ≠ z0 → x ≠ z' → C x = M x) ∧
      p.inefficientMoves ≤ 3 * cJ + cM := by
  obtain ⟨pj1, hj1⟩ := j1
  have hMa : M a0 = B z0 := by
    rw [hMx a0 hUa, hb, swapCells_at_left]
  set B2 := swapCells M (blank M) a0 with hB2
  obtain ⟨pj2, hj2⟩ : ∃ p : Path M B2, p.inefficientMoves ≤ cJ := j2 M hbM
  have hbB2 : blank B2 = a0 := blank_swapCells M _
  have hB2z0 : B2 z0 = B z0 := by rw [hB2, ← hbM, swapCells_at_left, hbM, hMa]
  have hB2x : ∀ x, x ≠ z0 → x ≠ a0 → B2 x = M x := fun x h h' =>
    swapCells_preserves M (by rw [hbM]; exact h) h'
  set C := swapCells B2 (blank B2) z' with hC
  obtain ⟨pj3, hj3⟩ : ∃ p : Path B2 C, p.inefficientMoves ≤ cJ := j3 B2 hbB2
  have hCa : C a0 = M z' := by
    rw [hC, ← hbB2, swapCells_at_left, hB2x z' (Ne.symm h2) (Ne.symm h3)]
  have hCx : ∀ x, x ≠ a0 → x ≠ z' → C x = B2 x := fun x h h' =>
    swapCells_preserves B2 (by rw [hbB2]; exact h) h'
  refine ⟨C, ((pj1.append pm).append pj2).append pj3, hCa, blank_swapCells B2 _,
    by rw [hCx z0 (Ne.symm h1) h2, hB2z0], fun x ha hz hz' => by rw [hCx x ha hz', hB2x x hz ha], ?_⟩
  simp only [Path.inefficientMoves_append]
  omega

end SlidingPuzzle.Port
