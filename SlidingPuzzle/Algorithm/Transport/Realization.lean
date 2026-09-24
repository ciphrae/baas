import SlidingPuzzle.Algorithm.PhaseStates
import SlidingPuzzle.Algorithm.Accounting

/-! Lifting Algorithm 4's count run to legal board paths. The local construction
is an explicit parameter, instantiated in `Transport.lean`: it restores Clear,
implements the exact matrix update, moves the blank to the source reservoir,
and pays for its moves. It need not realize a transposition of two specific cells. -/
namespace SlidingPuzzle.Partition
noncomputable section

/-- The one-iteration specification. A uniform construction of these
paths with budget `C*k³` is sufficient for the full Transport contract. -/
def TransportStepBound {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (E : ℕ) : Prop :=
  ∀ B : Board n, Clear (k := k) B → ∀ i j : Fin (k*k-1+1),
    reservoir (transportIndex k hk i) (blank B) →
    TransportCounts.Chooses (boardMatrix hk B) i j →
    ∃ D : Board n, ∃ p : Path B D,
      Clear (k := k) D ∧ reservoir (transportIndex k hk j) (blank D) ∧
      boardMatrix hk D = TransportCounts.move (boardMatrix hk B) i j ∧
      p.inefficientMoves ≤ E

/-- Realize every step of a count run on the evolving board. In particular,
the terminal matrix is the matrix of the actual endpoint, and the costs add. -/
theorem exists_path_of_count_run {n k E : ℕ} [NeZero n] (hk : 2 ≤ k)
    (hstep : TransportStepBound (n := n) hk E)
    {M N : TransportCounts.CountMatrix (k*k-1)} {i j : Fin (k*k-1+1)} {t : ℕ}
    (hrun : TransportCounts.Run M i N j t)
    (B : Board n) (hclear : Clear (k := k) B) (hmatrix : boardMatrix hk B = M)
    (hblank : reservoir (transportIndex k hk i) (blank B)) :
    ∃ D : Board n, ∃ p : Path B D,
      Clear (k := k) D ∧ reservoir (transportIndex k hk j) (blank D) ∧
      boardMatrix hk D = N ∧ p.inefficientMoves ≤ t*E := by
  induction hrun generalizing B with
  | nil =>
    exact ⟨B, .nil B, hclear, hblank, hmatrix, by simp [Path.inefficientMoves]⟩
  | @cons M N i j l t hchoice hrun ih =>
    obtain ⟨D, p, hD, hbD, hmD, hp⟩ := hstep B hclear i j hblank (by
      simpa only [hmatrix] using hchoice)
    rw [hmatrix] at hmD
    obtain ⟨F, q, hF, hbF, hmF, hq⟩ := ih D hD hmD hbD
    refine ⟨F, p.append q, hF, hbF, hmF, ?_⟩
    rw [Path.inefficientMoves_append, Nat.add_mul, Nat.one_mul]
    omega

/-- A local step construction lifts the already proved `n²`-transfer run to
a legal path satisfying the original Transport postcondition. -/
theorem exists_transport_path_of_step_bound {n k E : ℕ} [NeZero n]
    (hk : 2 ≤ k) (hn : n = k^4) (hstep : TransportStepBound (n := n) hk E)
    (B : Board n) (hB : Prepared hk B) :
    ∃ D : Board n, ∃ p : Path B D, Transported hk D ∧ p.inefficientMoves ≤ n^2*E := by
  obtain ⟨i, N, j, t, hi, hrun, ht, _hj, hN⟩ :=
    clear_board_count_run_quadratic hk hn B hB.clear hB.representatives
  obtain ⟨D, p, hD, _hbD, hmD, hp⟩ :=
    exists_path_of_count_run hk hstep hrun B hB.clear rfl hi
  refine ⟨D, p, Transported.of_count_endpoint hn hB p hD ?_,
    hp.trans (Nat.mul_le_mul_right E ht)⟩
  rwa [hmD]

end
end SlidingPuzzle.Partition

namespace SlidingPuzzle.Algorithm
open SlidingPuzzle.Partition

end SlidingPuzzle.Algorithm
