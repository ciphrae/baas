import SlidingPuzzle.Hub.Plan

/-! # The walk of one round

In a round every square with a real in-edge is served once, by its sender, and
the blank follows the tiles backwards: serving `D` from `S = perm⁻¹ D` moves the
blank from `D` to `S`. The components of the round are cut at dummy edges into
paths (each started by one relocation) and dummy-free cycles, which are started
at their snake-minimal square in snake order, so that the relocations between
consecutive cycles telescope. -/
namespace SlidingPuzzle.Hub

/-- High-level events: `serve S D` (blank at `D`, ends at `S`) and a relocation
of the blank from `E` to `Z`. -/
inductive HEvent (k : ℕ) where
  | serve (S D : Sq k)
  | reloc (E Z : Sq k)
  deriving DecidableEq

/-- Blank consistency of a list of events started with the blank in `b`. -/
def HChain {k : ℕ} : Sq k → List (HEvent k) → Prop
  | _, [] => True
  | b, .serve S D :: es => b = D ∧ HChain S es
  | b, .reloc E Z :: es => b = E ∧ E ≠ Z ∧ HChain Z es

/-- The square holding the blank after a list of events. -/
def hEnd {k : ℕ} : Sq k → List (HEvent k) → Sq k
  | b, [] => b
  | _, .serve S _ :: es => hEnd S es
  | _, .reloc _ Z :: es => hEnd Z es

/-- Weight of a relocation (`1 + ` its square distance); serves weigh nothing. -/
def relocWeight {k : ℕ} : HEvent k → ℕ
  | .serve _ _ => 0
  | .reloc E Z => 1 + sqDist E Z

/-- The events of one round, started with the blank in `cur`. -/
theorem exists_round_events {k : ℕ} (r : Round k) (cur : Sq k) :
    ∃ es : List (HEvent k),
      HChain cur es ∧
      (∀ S D, es.count (.serve S D) = if r.perm S = D ∧ r.real S then 1 else 0) ∧
      (es.map relocWeight).sum ≤
        4 * k ^ 2 + 4 * k * (1 + (Finset.univ.filter fun S => r.isDummy S).card) := by
  sorry

end SlidingPuzzle.Hub
