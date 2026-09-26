import SlidingPuzzle.Hub.Layout

/-! # Realizing resolved operations on boards

`simulate_step` realizes one `REvent` by a legal path whose inefficient moves
are bounded by `IState.cost`; `simulate_run` chains them. -/
namespace SlidingPuzzle.Hub

variable {n k s : ℕ}

/-- One operation. -/
theorem simulate_step (hd : HDims n k s) [NeZero n] {B : Board n} {σ : IState k}
    (hR : Rel hd B σ) {e : REvent k} (he : σ.Pre e) :
    ∃ C : Board n, ∃ p : Path B C, Rel hd C (σ.step s e) ∧ p.inefficientMoves ≤ σ.cost s e := by
  sorry

/-- A valid list of operations. -/
theorem simulate_run (hd : HDims n k s) [NeZero n] {B : Board n} {σ : IState k}
    (hR : Rel hd B σ) {es : List (REvent k)} (hv : σ.Valid s es) :
    ∃ C : Board n, ∃ p : Path B C,
      Rel hd C (σ.run s es) ∧ p.inefficientMoves ≤ σ.totalCost s es := by
  induction es generalizing B σ with
  | nil => exact ⟨B, .nil B, hR, by simp [Path.inefficientMoves, IState.totalCost]⟩
  | cons e es ih =>
    obtain ⟨hpre, hrest⟩ := hv
    obtain ⟨C, p, hC, hp⟩ := simulate_step hd hR hpre
    obtain ⟨D, q, hD, hq⟩ := ih hC hrest
    refine ⟨D, p.append q, hD, ?_⟩
    rw [Path.inefficientMoves_append]
    simp only [IState.totalCost]
    omega

end SlidingPuzzle.Hub
