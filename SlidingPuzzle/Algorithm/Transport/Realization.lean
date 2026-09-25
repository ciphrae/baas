import SlidingPuzzle.Algorithm.PhaseStates
import SlidingPuzzle.Algorithm.Accounting

/-! Lifting Algorithm 4's count run to legal board paths. The local construction
is an explicit parameter (`TransportStepBound`), instantiated in `Step.lean`: it restores Clear,
implements the exact matrix update, moves the blank to the source reservoir,
and pays for its moves. It need not realize a transposition of two specific cells. -/
namespace SlidingPuzzle.Partition
noncomputable section

/-- One transfer of the count algorithm, realized by a legal path with at most
`E j` inefficient moves, where `j` is the source reservoir. -/
def TransportStepBound {n k : ℕ} [NeZero n] (hk : Dims n k) (E : Fin (k*k-1+1) → ℕ) : Prop :=
  ∀ B : Board n, Clear (k := k) B → ∀ i j : Fin (k*k-1+1),
    reservoir (transportIndex k hk i) (blank B) →
    TransportCounts.Chooses (boardMatrix hk B) i j →
    ∃ D : Board n, ∃ p : Path B D,
      Clear (k := k) D ∧ reservoir (transportIndex k hk j) (blank D) ∧
      boardMatrix hk D = TransportCounts.move (boardMatrix hk B) i j ∧
      p.inefficientMoves ≤ E j

/-- Realize every step of a count run on the evolving board. In particular,
the terminal matrix is the matrix of the actual endpoint, and each step is paid
by one unit of its source row's off-diagonal mass. -/
theorem exists_path_of_count_run {n k : ℕ} {E : Fin (k*k-1+1) → ℕ} [NeZero n] (hk : Dims n k)
    (hstep : TransportStepBound (n := n) hk E)
    {M N : TransportCounts.CountMatrix (k*k-1)} {i j : Fin (k*k-1+1)} {t : ℕ}
    (hrun : TransportCounts.Run M i N j t)
    (B : Board n) (hclear : Clear (k := k) B) (hmatrix : boardMatrix hk B = M)
    (hblank : reservoir (transportIndex k hk i) (blank B)) :
    ∃ D : Board n, ∃ p : Path B D,
      Clear (k := k) D ∧ reservoir (transportIndex k hk j) (blank D) ∧
      boardMatrix hk D = N ∧ p.inefficientMoves + ∑ r, TransportCounts.rowOff N r * E r ≤
        ∑ r, TransportCounts.rowOff M r * E r := by
  induction hrun generalizing B with
  | nil =>
    exact ⟨B, .nil B, hclear, hblank, hmatrix, by simp [Path.inefficientMoves]⟩
  | @cons M N i j l t hchoice hrun ih =>
    obtain ⟨D, p, hD, hbD, hmD, hp⟩ := hstep B hclear i j hblank (by
      simpa only [hmatrix] using hchoice)
    rw [hmatrix] at hmD
    obtain ⟨F, q, hF, hbF, hmF, hq⟩ := ih D hD hmD hbD
    refine ⟨F, p.append q, hF, hbF, hmF, ?_⟩
    have hw := TransportCounts.weighted_rowOff_move _ E hchoice.1 hchoice.2.1
    rw [Path.inefficientMoves_append]
    omega

/-- A local step construction lifts the count run to a legal path satisfying
the original Transport postcondition. Each reservoir pays for at most as many
transfers as it initially holds off-diagonal units. -/
theorem exists_transport_path_of_step_bound {n k : ℕ} {E : Fin (k*k-1+1) → ℕ} [NeZero n]
    (hk : Dims n k) (hstep : TransportStepBound (n := n) hk E)
    (B : Board n) (hB : Prepared hk B) :
    ∃ D : Board n, ∃ p : Path B D, Transported hk D ∧
      p.inefficientMoves ≤ ∑ r, TransportCounts.rowOff (boardMatrix hk B) r * E r := by
  obtain ⟨i, N, j, t, hi, hrun, ht, _hj, hN⟩ :=
    clear_board_count_run_quadratic hk B hB.clear hB.representatives
  obtain ⟨D, p, hD, _hbD, hmD, hp⟩ :=
    exists_path_of_count_run hk hstep hrun B hB.clear rfl hi
  refine ⟨D, p, Transported.of_count_endpoint hB p hD ?_, by omega⟩
  rwa [hmD]

end
end SlidingPuzzle.Partition

