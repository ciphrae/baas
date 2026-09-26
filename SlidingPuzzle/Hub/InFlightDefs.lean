import SlidingPuzzle.Hub.Plan

/-! # Tiles in flight in the row halves: definitions

Insertion records, the ghost contents of the row halves, the insertions of a
round, and consistency of an insertion list with an order of the rounds. The
bound itself is `exists_good_order` in `Hub/InFlight.lean`. -/
namespace SlidingPuzzle.Hub

/-- An insertion into a row half: plan-order time `τ` (the round), half, block
distance and class. -/
structure InsRec (k : ℕ) where
  τ : ℕ
  H : RowH k
  d : ℕ
  x : Sq k

/-- Ghost contents of the row halves: `none` for tiles present from the start,
`some (x, d)` for a tile of class `x` inserted from block distance `d`. -/
abbrev Ghost (k : ℕ) := RowH k → ℕ → Option (Sq k × ℕ)

/-- One insertion. -/
def ghostStep {k : ℕ} (s : ℕ) (g : Ghost k) (r : InsRec k) : Ghost k :=
  Function.update g r.H (shiftIn (g r.H) (insPos k s r.H r.d) (some (r.x, r.d)))

/-- A list of insertions. -/
def ghostRun {k : ℕ} (s : ℕ) (g : Ghost k) (L : List (InsRec k)) : Ghost k :=
  L.foldl (ghostStep s) g

/-- Inserted class-`x` tiles present in the two halves of `R(h)`. -/
def newCnt {k : ℕ} (s : ℕ) (g : Ghost k) (h x : Sq k) : ℕ :=
  ∑ side : Bool, ((Finset.range (rowLen k s (h.1, h.2, side))).filter
    fun q => (g (h.1, h.2, side) q).map Prod.fst = some x).card

/-- The row insertions of a round: every real edge `S → D` with `S.2 ≠ D.2`
inserts a class-`D` tile into `R(S.1, D.2)` from block distance
`|S.2 - D.2| - 1`. -/
noncomputable def roundIns {k : ℕ} (r : Round k) : List (RowH k × ℕ × Sq k) :=
  ((Finset.univ.filter fun S => r.real S ∧ S.2 ≠ (r.perm S).2).toList).map fun S =>
    (hop1Half S (S.1, (r.perm S).2), hop1Dist S (S.1, (r.perm S).2), r.perm S)

/-- An insertion list executes the rounds in the order `σ` (plan round `σ τ`
at time `τ`), in any order within a round. -/
def Consistent {k Δ : ℕ} (rs : Fin Δ → Round k) (σ : Equiv.Perm (Fin Δ))
    (L : List (InsRec k)) : Prop :=
  L.Pairwise (fun a b => a.τ ≤ b.τ) ∧ (∀ r ∈ L, r.τ < Δ) ∧
    ∀ τ (hτ : τ < Δ), ((L.filter fun r => r.τ = τ).map fun r => (r.H, r.d, r.x)).Perm
      (roundIns (rs (σ ⟨τ, hτ⟩)))

end SlidingPuzzle.Hub
