import SlidingPuzzle.Tree.OpJump

/-! # Realizing resolved operations on boards -/
namespace SlidingPuzzle.Tree

variable {n k s q : ℕ} [NeZero n] (L : LaneSys k q)

theorem simulate_step (td : TDims n k s q) {B : Board n} {σ : IState k q}
    (hR : Rel L td.hd B σ) {e : REvent k q} (he : σ.Pre L e) :
    ∃ C : Board n, ∃ p : Path B C, Rel L td.hd C (σ.step s e) ∧
      p.inefficientMoves ≤ σ.cost s e := by
  cases e with
  | hopR H J y => exact simulate_hopR L td hR he
  | hopC V I y => exact simulate_hopC L td hR he
  | jump E Z y => exact simulate_jump L td hR he

theorem simulate_run (td : TDims n k s q) {B : Board n} {σ : IState k q}
    (hR : Rel L td.hd B σ) {es : List (REvent k q)} (hv : σ.Valid L s es) :
    ∃ C : Board n, ∃ p : Path B C,
      Rel L td.hd C (σ.run s es) ∧ p.inefficientMoves ≤ σ.totalCost s es := by
  induction es generalizing B σ with
  | nil => exact ⟨B, .nil B, hR, by simp [Path.inefficientMoves, IState.totalCost]⟩
  | cons e es ih =>
    obtain ⟨hpre, hrest⟩ := hv
    obtain ⟨C, p, hC, hp⟩ := simulate_step L td hR hpre
    obtain ⟨D, q, hD, hq⟩ := ih hC hrest
    refine ⟨D, p.append q, hD, ?_⟩
    rw [Path.inefficientMoves_append]
    simp only [IState.totalCost]
    omega

end SlidingPuzzle.Tree
