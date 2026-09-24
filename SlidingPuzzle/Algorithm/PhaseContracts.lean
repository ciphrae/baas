import SlidingPuzzle.Algorithm.PhaseStates
import SlidingPuzzle.Algorithm.Accounting
import SlidingPuzzle.Algorithm.GeneralSize

/-! Uniform contracts for the four phases of the fourth-power algorithm.

These are specifications, not constructions of the phases. Their inhabitants must
supply actual legal paths with uniform inefficient-move bounds. The composition
theorems below take those inhabitants as explicit hypotheses.

Finish accepts global reachability, correct nonblank square membership, and a blank
in the last square. It must construct and pay for all blank access and parity
adjustments; independent reachability of each square is not an input assumption.
-/
namespace SlidingPuzzle
namespace Algorithm

open SlidingPuzzle.Partition

/-- A phase with concrete board predicates, a legal path, and a uniform error budget.
Only endpoint invariants are required; a construction may temporarily disturb them. -/
def BoundedPhase {n : ℕ} [NeZero n] (k C : ℕ)
    (pre post : Board n → Prop) : Prop :=
  ∀ B : Board n, pre B → ∃ D : Board n, ∃ p : Path B D,
    post D ∧ p.inefficientMoves ≤ C*k^11

/-- Matching endpoint predicates suffice to concatenate two bounded phases. -/
theorem BoundedPhase.comp {n : ℕ} [NeZero n] {k C D : ℕ}
    {pre middle post : Board n → Prop}
    (h₁ : BoundedPhase k C pre middle) (h₂ : BoundedPhase k D middle post) :
    BoundedPhase k (C+D) pre post := by
  intro B hB
  obtain ⟨M,p,hM,hp⟩ := h₁ B hB
  obtain ⟨E,q,hE,hq⟩ := h₂ M hM
  refine ⟨E,p.append q,hE,?_⟩
  rw [Path.inefficientMoves_append, Nat.add_mul]
  exact Nat.add_le_add hp hq

/-- An all-moves bound is sufficient where a phase does not need finer
efficient/inefficient accounting. This does not assert such a bound exists. -/
theorem BoundedPhase.of_length_bound {n : ℕ} [NeZero n] {k C : ℕ}
    {pre post : Board n → Prop}
    (h : ∀ B : Board n, pre B → ∃ D : Board n, ∃ p : Path B D,
      post D ∧ p.length ≤ C*k^11) : BoundedPhase k C pre post := by
  intro B hB
  obtain ⟨D,p,hD,hp⟩ := h B hB
  exact ⟨D,p,hD,p.inefficientMoves_le_length.trans hp⟩

/-- Charge an entire solving suffix at half its length. Keeping its phases
together avoids charging potential increases that later phases undo. -/
theorem BoundedPhase.exists_solution {n : ℕ} [NeZero n] {k C D : ℕ}
    {pre post : Board n → Prop} (h : BoundedPhase k C pre post)
    (hfinish : ∀ M : Board n, post M →
      ∃ q : Path M (target n), q.length ≤ 2*D*k^11)
    (B : Board n) (hB : pre B) :
    ∃ p : Path B (target n), p.inefficientMoves ≤ (C+D)*k^11 ∧
      p.length ≤ manhattan B + 2*(C+D)*k^11 := by
  obtain ⟨M,p,hM,hp⟩ := h B hB
  obtain ⟨q,hq⟩ := hfinish M hM
  have hqi : q.inefficientMoves ≤ D*k^11 := by
    have hh := q.inefficientMoves_le_half_length
    nlinarith
  have hi : (p.append q).inefficientMoves ≤ (C+D)*k^11 := by
    rw [Path.inefficientMoves_append, Nat.add_mul]
    exact Nat.add_le_add hp hqi
  refine ⟨p.append q,hi,?_⟩
  rw [Path.solution_length]
  nlinarith

/-- Build clear corridors and last-reservoir representatives from a reachable board. -/
def PreparationContract (C : ℕ) : Prop :=
  ∀ k : ℕ, ∀ hk : 2 ≤ k,
    letI : NeZero (k^4) := ⟨by positivity⟩
    BoundedPhase (n := k^4) k C Reachable (Prepared hk)

/-- Sort the reservoirs, retaining clear corridors and returning the blank to
the last reservoir. The representative condition need not survive transport. -/
def TransportContract (C : ℕ) : Prop :=
  ∀ k : ℕ, ∀ hk : 2 ≤ k,
    letI : NeZero (k^4) := ⟨by positivity⟩
    BoundedPhase (n := k^4) k C (Prepared hk) (Transported hk)

/-- Put each nonblank tile in its target square. Clear corridors need not survive
arrangement; the next phase needs square membership and global reachability. -/
def ArrangeContract (C : ℕ) : Prop :=
  ∀ k : ℕ, ∀ hk : 2 ≤ k,
    letI : NeZero (k^4) := ⟨by positivity⟩
    BoundedPhase (n := k^4) k C (Transported hk) (Arranged hk)

/-- Solve the arranged board, including any access moves and block parity repairs
inside this phase's budget. No blockwise solvability assumption is permitted. -/
def FinishContract (C : ℕ) : Prop :=
  ∀ k : ℕ, ∀ hk : 2 ≤ k,
    letI : NeZero (k^4) := ⟨by positivity⟩
    BoundedPhase (n := k^4) k C (Arranged hk) (fun D => D=target (k^4))

/-- Constants are chosen once for all dimensions and all input boards. -/
structure PhaseBudgets where
  preparation : ℕ
  transport : ℕ
  arrange : ℕ
  finish : ℕ

/-- Each inefficient move contributes two moves to the additive overhead. -/
def PhaseBudgets.overhead (c : PhaseBudgets) : ℕ :=
  2*(c.preparation+c.transport+c.arrange+c.finish)

/-- The four constructive obligations, with exactly matching boundaries.
`Preparation.lean` supplies the preparation field with constant `1033`. -/
structure FourPhaseContracts (c : PhaseBudgets) : Prop where
  preparation : PreparationContract c.preparation
  transport : TransportContract c.transport
  arrange : ArrangeContract c.arrange
  finish : FinishContract c.finish

/-- Composition supplies a legal solution and its additive bound. All phase
preconditions come from the preceding endpoint, starting with global reachability. -/
theorem FourPhaseContracts.exists_solution {c : PhaseBudgets}
    (h : FourPhaseContracts c) (k : ℕ) (hk : 2 ≤ k)
    [NeZero (k^4)] (B : Board (k^4)) (hB : Reachable B) :
    ∃ p : Path B (target (k^4)), p.length ≤ manhattan B + c.overhead*k^11 := by
  obtain ⟨D,p,hD,hp⟩ := (((h.preparation k hk).comp (h.transport k hk)).comp
    (h.arrange k hk)).comp (h.finish k hk) B hB
  change D = target (k^4) at hD
  subst D
  refine ⟨p,?_⟩
  rw [p.solution_length]
  dsimp [PhaseBudgets.overhead]
  nlinarith [hp]

/-- Completing these concrete phase contracts discharges the fourth-power bound. -/
theorem fourthPowerApproximation_of_phaseContracts {c : PhaseBudgets}
    (h : FourPhaseContracts c) : FourthPowerApproximation := by
  refine ⟨c.overhead,?_⟩
  intro k hk
  let : NeZero (k^4) := ⟨by positivity⟩
  intro B
  obtain ⟨p,hp⟩ := h.exists_solution k hk B.val B.property
  exact (optimalLength_le_path_length B p).trans hp

theorem uniformApproximation_of_phaseContracts {c : PhaseBudgets}
    (h : FourPhaseContracts c) : UniformApproximation :=
  uniformApproximation_of_fourthPowerApproximation
    (fourthPowerApproximation_of_phaseContracts h)

open Filter Asymptotics in
/-- The final conclusions remain conditional on constructing all four phases. -/
theorem proposition9_of_phaseContracts {c : PhaseBudgets} (h : FourPhaseContracts c) :
    ((fun n : ℕ => averageOptimalLength n - (2 / 3 : ℝ)*(n : ℝ)^3)
      =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) (11 / 4 : ℝ))) ∧
    ((fun n : ℕ => godsNumber n - (n : ℝ)^3)
      =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) (11 / 4 : ℝ))) :=
  proposition9_of_fourthPowerApproximation (fourthPowerApproximation_of_phaseContracts h)

end Algorithm
end SlidingPuzzle
