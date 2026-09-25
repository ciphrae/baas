import SlidingPuzzle.Algorithm.PhaseStates
import SlidingPuzzle.Algorithm.Accounting

/-! Lifting Algorithm 4's count run to legal board paths. The local construction
is an explicit parameter (`TransportStepBoundAmortized`), instantiated in `Step.lean`: it
restores Clear, implements the exact matrix update, moves the blank to the source
reservoir, and pays for its moves up to a potential that telescopes along the run.
It need not realize a transposition of two specific cells. -/
namespace SlidingPuzzle.Partition
noncomputable section

/-- A transfer amortized by a board potential `Pot`: its doubled inefficiency
plus the potential after it is at most `E j` plus the potential before it. -/
def TransportStepBoundAmortized {n k : ℕ} [NeZero n] (hk : Dims n k)
    (E : Fin (k*k-1+1) → ℕ) (Pot : Board n → ℕ) : Prop :=
  ∀ B : Board n, Clear (k := k) B → ∀ i j : Fin (k*k-1+1),
    reservoir (transportIndex k hk i) (blank B) →
    TransportCounts.Chooses (boardMatrix hk B) i j →
    ∃ D : Board n, ∃ p : Path B D,
      Clear (k := k) D ∧ reservoir (transportIndex k hk j) (blank D) ∧
      boardMatrix hk D = TransportCounts.move (boardMatrix hk B) i j ∧
      2*p.inefficientMoves+Pot D ≤ E j+Pot B

/-- Realize a count run with an amortized step: the potentials telescope. -/
theorem exists_path_of_count_run_amortized {n k : ℕ} {E : Fin (k*k-1+1) → ℕ}
    {Pot : Board n → ℕ} [NeZero n]
    (hk : Dims n k) (hstep : TransportStepBoundAmortized (n := n) hk E Pot)
    {M N : TransportCounts.CountMatrix (k*k-1)} {i j : Fin (k*k-1+1)} {t : ℕ}
    (hrun : TransportCounts.Run M i N j t)
    (B : Board n) (hclear : Clear (k := k) B) (hmatrix : boardMatrix hk B = M)
    (hblank : reservoir (transportIndex k hk i) (blank B)) :
    ∃ D : Board n, ∃ p : Path B D,
      Clear (k := k) D ∧ reservoir (transportIndex k hk j) (blank D) ∧
      boardMatrix hk D = N ∧ 2*p.inefficientMoves + ∑ r, TransportCounts.rowOff N r * E r ≤
        ∑ r, TransportCounts.rowOff M r * E r + Pot B := by
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

/-- The amortized realization of the transport phase. -/
theorem exists_transport_path_of_step_bound_amortized {n k : ℕ} {E : Fin (k*k-1+1) → ℕ}
    {Pot : Board n → ℕ} [NeZero n] (hk : Dims n k)
    (hstep : TransportStepBoundAmortized (n := n) hk E Pot)
    (B : Board n) (hB : Prepared hk B) :
    ∃ D : Board n, ∃ p : Path B D, Transported hk D ∧
      2*p.inefficientMoves ≤ ∑ r, TransportCounts.rowOff (boardMatrix hk B) r * E r + Pot B := by
  obtain ⟨N, j, t, hi, hrun, ht, _hj, hN⟩ :=
    Classical.choose_spec (clear_board_count_run_quadratic hk B hB.clear hB.representatives)
  obtain ⟨D, p, hD, _hbD, hmD, hp⟩ :=
    exists_path_of_count_run_amortized hk hstep hrun B hB.clear rfl hi
  refine ⟨D, p, Transported.of_count_endpoint hB p hD ?_, by omega⟩
  rwa [hmD]

end
end SlidingPuzzle.Partition

