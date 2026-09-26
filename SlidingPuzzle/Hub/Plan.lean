import SlidingPuzzle.Hub.Basic

/-! # The plan: rounds from a regular bipartite multigraph

`T S D` counts the reservoir tiles of `S` with class `D ≠ S`. Padding with
dummy edges (from squares that receive more than they send to squares that
send more than they receive) and loops gives a `Δ0`-regular bipartite
multigraph, which splits into `Δ0` perfect matchings (Hall/König). A round is
one of them: a permutation `perm` of the squares (`S ↦` the square `S` sends
to) with a flag marking dummy edges. -/
namespace SlidingPuzzle.Hub

/-- One perfect matching of the padded multigraph. -/
structure Round (k : ℕ) where
  perm : Equiv.Perm (Sq k)
  dummy : Sq k → Bool

namespace Round
variable {k : ℕ}

/-- `S` sends a real tile in this round (to `perm S`). -/
def real (r : Round k) (S : Sq k) : Prop := r.perm S ≠ S ∧ r.dummy S = false

/-- `S`'s edge is a dummy edge (to `perm S ≠ S`). -/
def isDummy (r : Round k) (S : Sq k) : Prop := r.perm S ≠ S ∧ r.dummy S = true

instance (r : Round k) (S : Sq k) : Decidable (r.real S) := by unfold real; infer_instance
instance (r : Round k) (S : Sq k) : Decidable (r.isDummy S) := by unfold isDummy; infer_instance

end Round

/-- Tiles a square sends. -/
def sends {k : ℕ} (T : Sq k → Sq k → ℕ) (S : Sq k) : ℕ := ∑ D, T S D

/-- Tiles a square receives. -/
def recv {k : ℕ} (T : Sq k → Sq k → ℕ) (D : Sq k) : ℕ := ∑ S, T S D

/-- König decomposition of the padded demand multigraph. -/
theorem exists_rounds {k : ℕ} (T : Sq k → Sq k → ℕ) (hT : ∀ S, T S S = 0) :
    ∃ (Δ0 : ℕ) (rs : Fin Δ0 → Round k),
      (∀ S D, (Finset.univ.filter fun i => (rs i).perm S = D ∧ (rs i).real S).card = T S D) ∧
      (∀ S, (Finset.univ.filter fun i => (rs i).isDummy S).card = recv T S - sends T S) ∧
      (∀ S, (Finset.univ.filter fun i => (rs i).perm S = S).card =
        Δ0 - max (sends T S) (recv T S)) ∧
      (∀ S, max (sends T S) (recv T S) ≤ Δ0) ∧
      (∀ M, (∀ S, sends T S ≤ M ∧ recv T S ≤ M) → Δ0 ≤ M) := by
  sorry

end SlidingPuzzle.Hub
