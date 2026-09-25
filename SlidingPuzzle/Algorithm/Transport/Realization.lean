import SlidingPuzzle.Algorithm.PhaseStates
import SlidingPuzzle.Algorithm.Accounting

/-! Lifting Algorithm 4's count run to legal board paths. The local construction
is an explicit parameter (`TransportStepBoundAmortized`), instantiated in `Step.lean`: it
restores Clear, implements the exact matrix update, moves the blank to the source
reservoir, and pays for its moves up to a potential that telescopes along the run.
It need not realize a transposition of two specific cells. -/
namespace SlidingPuzzle.Partition
noncomputable section

/-- The potential of a transfer from the blank's reservoir `X` to the source
`Y`, with the blank in column `c`: twice the horizontal distance to the edge of
`X`'s square facing `Y`, or one side length if `Y` lies in the same column of
squares. It bounds the inefficiency of the transfer's horizontal travel, and the
exit side of the previous transfer is chosen with it in mind. -/
def transferPotential {n k : ℕ} (c : ℕ) (X Y : GroupIndex k) : ℕ :=
  if (groupCol X).val < (groupCol Y).val then
    2*((groupCol X).val*side n k+side n k+1-c)
  else if (groupCol Y).val < (groupCol X).val then 2*(c+1-(groupCol X).val*side n k)
  else side n k

/-- The potential of a state of the count run: that of its next transfer, if any. -/
def statePotential {n k : ℕ} [NeZero n] (hk : Dims n k) (B : Board n)
    (M : TransportCounts.CountMatrix (k*k-1)) (i : Fin (k*k-1+1)) : ℕ :=
  haveI := Classical.propDecidable
  if h : ∃ j, TransportCounts.Chooses M i j then
    transferPotential (n := n) (blank B).2.val (transportIndex k hk i) (transportIndex k hk h.choose)
  else 0

theorem statePotential_of_chooses {n k : ℕ} [NeZero n] (hk : Dims n k) (B : Board n)
    {M : TransportCounts.CountMatrix (k*k-1)} {i j : Fin (k*k-1+1)}
    (h : TransportCounts.Chooses M i j) :
    statePotential hk B M i =
      transferPotential (n := n) (blank B).2.val (transportIndex k hk i) (transportIndex k hk j) := by
  have hex : ∃ j, TransportCounts.Chooses M i j := ⟨j, h⟩
  unfold statePotential
  rw [dif_pos hex, TransportCounts.Chooses.unique hex.choose_spec h]

/-- A state potential from a reservoir position is at most `2s+2`. -/
theorem statePotential_le {n k : ℕ} [NeZero n] (hk : Dims n k) (B : Board n)
    (M : TransportCounts.CountMatrix (k*k-1)) (i : Fin (k*k-1+1))
    (hi : reservoir (transportIndex k hk i) (blank B)) :
    statePotential hk B M i ≤ 2*side n k+2 := by
  classical
  unfold statePotential
  split_ifs with h
  · have h1 := hi.2.2.1; have h2 := hi.2.2.2
    simp only [Nat.add_mul, Nat.one_mul] at h2
    unfold transferPotential
    split_ifs <;> omega
  · omega

/-- A transfer amortized by the state potential: its doubled inefficiency plus
the potential of the next state is at most `2*E j` plus the potential of this
transfer. -/
def TransportStepBoundAmortized {n k : ℕ} [NeZero n] (hk : Dims n k)
    (E : Fin (k*k-1+1) → ℕ) : Prop :=
  ∀ B : Board n, Clear (k := k) B → ∀ i j : Fin (k*k-1+1),
    reservoir (transportIndex k hk i) (blank B) →
    TransportCounts.Chooses (boardMatrix hk B) i j →
    ∃ D : Board n, ∃ p : Path B D,
      Clear (k := k) D ∧ reservoir (transportIndex k hk j) (blank D) ∧
      boardMatrix hk D = TransportCounts.move (boardMatrix hk B) i j ∧
      2*p.inefficientMoves+statePotential hk D (boardMatrix hk D) j ≤
        2*E j+transferPotential (n := n) (blank B).2.val (transportIndex k hk i)
          (transportIndex k hk j)

/-- Realize a count run with an amortized step: the potentials telescope. -/
theorem exists_path_of_count_run_amortized {n k : ℕ} {E : Fin (k*k-1+1) → ℕ} [NeZero n]
    (hk : Dims n k) (hstep : TransportStepBoundAmortized (n := n) hk E)
    {M N : TransportCounts.CountMatrix (k*k-1)} {i j : Fin (k*k-1+1)} {t : ℕ}
    (hrun : TransportCounts.Run M i N j t)
    (B : Board n) (hclear : Clear (k := k) B) (hmatrix : boardMatrix hk B = M)
    (hblank : reservoir (transportIndex k hk i) (blank B)) :
    ∃ D : Board n, ∃ p : Path B D,
      Clear (k := k) D ∧ reservoir (transportIndex k hk j) (blank D) ∧
      boardMatrix hk D = N ∧ 2*p.inefficientMoves + 2*∑ r, TransportCounts.rowOff N r * E r ≤
        2*∑ r, TransportCounts.rowOff M r * E r + statePotential hk B M i := by
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
    rw [statePotential_of_chooses hk B hchoice]
    rw [hmD] at hp
    rw [Path.inefficientMoves_append]
    omega

/-- The amortized realization of the transport phase. -/
theorem exists_transport_path_of_step_bound_amortized {n k : ℕ} {E : Fin (k*k-1+1) → ℕ}
    [NeZero n] (hk : Dims n k) (hstep : TransportStepBoundAmortized (n := n) hk E)
    (B : Board n) (hB : Prepared hk B) :
    ∃ D : Board n, ∃ p : Path B D, Transported hk D ∧
      2*p.inefficientMoves ≤ 2*∑ r, TransportCounts.rowOff (boardMatrix hk B) r * E r +
        statePotential hk B (boardMatrix hk B) (Classical.choose
          (clear_board_count_run_quadratic hk B hB.clear hB.representatives)) := by
  obtain ⟨N, j, t, hi, hrun, ht, _hj, hN⟩ :=
    Classical.choose_spec (clear_board_count_run_quadratic hk B hB.clear hB.representatives)
  obtain ⟨D, p, hD, _hbD, hmD, hp⟩ :=
    exists_path_of_count_run_amortized hk hstep hrun B hB.clear rfl hi
  refine ⟨D, p, Transported.of_count_endpoint hB p hD ?_, by omega⟩
  rwa [hmD]

end
end SlidingPuzzle.Partition

