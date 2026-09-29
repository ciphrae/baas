import SlidingPuzzle.Port.Ghost

/-! # Algebra of port counts -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle.Hub (Sq)

variable {k q : ℕ}

theorem incP_apply (f : Sq k → Pt → Sq k → ℕ) (Q : Sq k) (pt : Pt) (z Q' : Sq k) (pt' : Pt)
    (z' : Sq k) : incP f Q pt z Q' pt' z' = f Q' pt' z' + (if Q' = Q ∧ pt' = pt ∧ z' = z then 1 else 0) :=
  rfl

theorem decP_apply (f : Sq k → Pt → Sq k → ℕ) (Q : Sq k) (pt : Pt) (z Q' : Sq k) (pt' : Pt)
    (z' : Sq k) : decP f Q pt z Q' pt' z' = f Q' pt' z' - (if Q' = Q ∧ pt' = pt ∧ z' = z then 1 else 0) :=
  rfl

theorem sumPt_ind (Q Q' z z' : Sq k) (pt : Pt) :
    ∑ pt' : Pt, (if Q' = Q ∧ pt' = pt ∧ z' = z then 1 else 0) = if Q' = Q ∧ z' = z then 1 else 0 := by
  by_cases h : Q' = Q ∧ z' = z
  · rw [if_pos h, Finset.sum_eq_single pt]
    · simp [h]
    · intro b _ hb; simp [hb]
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg (fun h' => h ⟨h'.1, h'.2.2⟩)]

theorem sumZ_ind (Q Q' z : Sq k) (pt pt' : Pt) :
    ∑ z' : Sq k, (if Q' = Q ∧ pt' = pt ∧ z' = z then 1 else 0) = if Q' = Q ∧ pt' = pt then 1 else 0 := by
  by_cases h : Q' = Q ∧ pt' = pt
  · rw [if_pos h, Finset.sum_eq_single z]
    · simp [h]
    · intro b _ hb; simp [hb]
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg (fun h' => h ⟨h'.1, h'.2.1⟩)]

theorem sumPt_incP (f : Sq k → Pt → Sq k → ℕ) (Q : Sq k) (pt : Pt) (z Q' z' : Sq k) :
    ∑ pt', incP f Q pt z Q' pt' z' = (∑ pt', f Q' pt' z') + if Q' = Q ∧ z' = z then 1 else 0 := by
  simp only [incP_apply, sum_add_distrib, sumPt_ind]

theorem sumPt_decP (f : Sq k → Pt → Sq k → ℕ) (Q : Sq k) (pt : Pt) (z Q' z' : Sq k)
    (h : 1 ≤ f Q pt z) :
    (∑ pt', decP f Q pt z Q' pt' z') + (if Q' = Q ∧ z' = z then 1 else 0) = ∑ pt', f Q' pt' z' := by
  rw [← sumPt_ind Q Q' z z' pt, ← sum_add_distrib]
  refine Finset.sum_congr rfl fun pt' _ => ?_
  rw [decP_apply]
  split_ifs with h1
  · obtain ⟨rfl, rfl, rfl⟩ := h1; omega
  · rfl

theorem sumZ_incP (f : Sq k → Pt → Sq k → ℕ) (Q : Sq k) (pt : Pt) (z Q' : Sq k) (pt' : Pt) :
    ∑ z', incP f Q pt z Q' pt' z' = (∑ z', f Q' pt' z') + if Q' = Q ∧ pt' = pt then 1 else 0 := by
  simp only [incP_apply, sum_add_distrib, sumZ_ind]

theorem sumZ_decP (f : Sq k → Pt → Sq k → ℕ) (Q : Sq k) (pt : Pt) (z Q' : Sq k) (pt' : Pt)
    (h : 1 ≤ f Q pt z) :
    (∑ z', decP f Q pt z Q' pt' z') + (if Q' = Q ∧ pt' = pt then 1 else 0) = ∑ z', f Q' pt' z' := by
  rw [← sumZ_ind Q Q' z pt pt', ← sum_add_distrib]
  refine Finset.sum_congr rfl fun z' _ => ?_
  rw [decP_apply]
  split_ifs with h1
  · obtain ⟨rfl, rfl, rfl⟩ := h1; omega
  · rfl

end SlidingPuzzle.Port
