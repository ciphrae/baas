import SlidingPuzzle.Hub.InFlightPush

/-! # Window bookkeeping for the in-flight bound

The insertion list `L` is sorted by time and, at each time `τ`, performs exactly
the insertions `R τ` (in any order). Counting list entries by time and by
insertion (`card_time_filter`, `sum_card_fiber`) turns window sums over `R`
into counts of list indices; `Hub/InFlightSegment.lean` uses this to bound the
tiles in flight. -/
namespace SlidingPuzzle.Hub

open Finset

variable {k : ℕ} (s : ℕ)

/-- The row insertion of a record. -/
def proj (r : InsRec k) : RowH k × ℕ × Sq k := (r.H, r.d, r.x)

theorem card_range_filter_getD {α : Type*} (r0 : α) (Q : α → Prop) [DecidablePred Q] :
    ∀ L : List α, ((range L.length).filter fun i => Q (L.getD i r0)).card =
      L.countP (fun a => decide (Q a))
  | [] => by simp
  | a :: L => by
    rw [card_filter, List.length_cons, sum_range_succ', List.countP_cons,
      ← card_range_filter_getD r0 Q L, card_filter]
    simp

/-- Sums of fibre counts over a set of times. -/
theorem sum_card_fiber {ι : Type*} (S : Finset ι) (f : ι → ℕ) (U : Finset ℕ) (P : ι → Prop)
    [DecidablePred P] :
    ∑ τ ∈ U, (S.filter fun i => f i = τ ∧ P i).card = (S.filter fun i => f i ∈ U ∧ P i).card := by
  rw [card_eq_sum_card_fiberwise (f := f) (t := U) (fun i hi => (mem_filter.mp hi).2.1)]
  refine sum_congr rfl fun τ hτ => ?_
  rw [filter_filter]
  apply congrArg; apply filter_congr
  intro i _
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1 ▸ hτ, h2⟩, h1⟩
  · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩

section list

variable {L : List (InsRec k)} (r0 : InsRec k) {R : ℕ → List (RowH k × ℕ × Sq k)}

/-- Counting the records of time `τ` with a property of their insertion. -/
theorem card_time_filter (hperm : ∀ τ, ((L.filter fun r => r.τ = τ).map proj).Perm (R τ))
    (τ : ℕ) (P : RowH k × ℕ × Sq k → Prop) [DecidablePred P] :
    ((range L.length).filter fun i => (L.getD i r0).τ = τ ∧ P (proj (L.getD i r0))).card =
      (R τ).countP (fun p => decide (P p)) := by
  rw [card_range_filter_getD r0 (fun r => r.τ = τ ∧ P (proj r)), ← (hperm τ).countP_eq,
    List.countP_map, List.countP_filter]
  apply List.countP_congr
  intro a _; simp [and_comm]

theorem tau_mono (hsort : L.Pairwise fun a b => a.τ ≤ b.τ) {j j' : ℕ} (h : j ≤ j')
    (hj' : j' < L.length) : (L.getD j r0).τ ≤ (L.getD j' r0).τ := by
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  · rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hj']
    exact List.pairwise_iff_getElem.mp hsort j j' (by omega) hj' h

theorem proj_mem (hperm : ∀ τ, ((L.filter fun r => r.τ = τ).map proj).Perm (R τ)) {i : ℕ}
    (hi : i < L.length) : proj (L.getD i r0) ∈ R (L.getD i r0).τ := by
  rw [← (hperm _).mem_iff]
  apply List.mem_map_of_mem
  rw [List.mem_filter]
  refine ⟨?_, by simp⟩
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

end list

end SlidingPuzzle.Hub
