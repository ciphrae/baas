import SlidingPuzzle.Hub.Layout
import SlidingPuzzle.Algorithm.Finish

/-! # Finish on the hub layout

The formalized Finish (`Algorithm/Finish.lean`) solves each square with a local
solver once every tile lies in its own square. It was stated for `Dims`
(`k³ ≤ s`), but only uses `8 ≤ s`; here it is applied with `HDims`. -/
namespace SlidingPuzzle.Hub

variable {n k s : ℕ}

/-- Finish for a board whose tiles all lie in their own squares. -/
theorem exists_finish (hd : HDims n k s) [NeZero n] {cost ineff : ℕ → ℕ}
    (hsolver : SolverBound cost ineff) (B : Board n) (hB : Reachable B)
    (hsorted : ∀ x, (B x).val ≠ 0 → classOf hd (B x) = sqOf hd x)
    (hblank : IsLast (sqOf hd (blank B))) :
    ∃ p : Path B (target n), p.inefficientMoves ≤ k ^ 2 * ineff s + 9354 * k ^ 2 * n := by
  sorry

end SlidingPuzzle.Hub
