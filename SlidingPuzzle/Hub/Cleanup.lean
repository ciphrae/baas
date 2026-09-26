import SlidingPuzzle.Hub.Layout

/-! # Cleanup

Bring the blank into the last square, then fix misplaced tiles two at a time
with double swaps (`exists_double_swap`, `O(n)` each): a misplaced tile of
class `Q` is exchanged with a wrong tile inside square `Q`, together with a
harmless exchange inside one square, which keeps the permutation even. -/
namespace SlidingPuzzle.Hub

variable {n k s : ℕ}

/-- Sort every tile into its own square. -/
theorem exists_cleanup (hd : HDims n k s) [NeZero n] (B : Board n) :
    ∃ C : Board n, ∃ p : Path B C,
      (∀ x, (C x).val ≠ 0 → classOf hd (C x) = sqOf hd x) ∧ IsLast (sqOf hd (blank C)) ∧
      p.inefficientMoves ≤ 7000 * n * (misplaced hd B + 2 * n + 1) := by
  sorry

end SlidingPuzzle.Hub
