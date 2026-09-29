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

namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle.Hub (Sq)

variable {k q : ℕ}

/-- The class leaving the ports of the source through the insertion. -/
def Mode.out (y : Sq k) : Mode k → Sq k
  | .cheap => y
  | .imp none z => z
  | .imp (some _) _ => y

/-- The conditions under which `srcPc` removes tiles that are there. -/
def SrcOK (f : Sq k → Pt → Sq k → ℕ) (S : Sq k) (P : Pt) (y : Sq k) : Mode k → Prop
  | .cheap => 1 ≤ f S P y
  | .imp none z => 1 ≤ f S P z
  | .imp (some p) z => p ≠ P ∧ 1 ≤ f S p y ∧ 1 ≤ f S P z

theorem srcPc_ne (f : Sq k → Pt → Sq k → ℕ) (S : Sq k) (P : Pt) (y : Sq k) (m : Mode k)
    {Q : Sq k} (hQ : Q ≠ S) (pt : Pt) (z : Sq k) : PState.srcPc f S P y m Q pt z = f Q pt z := by
  rcases m with _ | ⟨_ | p, z0⟩ <;> simp [PState.srcPc, decP, incP, hQ]

theorem srcPc_sumPt (f : Sq k → Pt → Sq k → ℕ) (S : Sq k) (P : Pt) (y : Sq k) (m : Mode k)
    (h : SrcOK f S P y m) (Q z : Sq k) :
    (∑ pt, PState.srcPc f S P y m Q pt z) + (if Q = S ∧ z = m.out y then 1 else 0) =
      ∑ pt, f Q pt z := by
  rcases m with _ | ⟨_ | p, z0⟩
  · exact sumPt_decP f S P y Q z h
  · exact sumPt_decP f S P z0 Q z h
  · obtain ⟨hp, h1, h2⟩ := h
    show (∑ pt, decP (incP (decP f S p y) S p z0) S P z0 Q pt z) + _ = _
    have g2 : 1 ≤ incP (decP f S p y) S p z0 S P z0 := by
      rw [incP_apply, decP_apply, if_neg (fun h' => hp h'.2.1.symm)]; omega
    have e1 := sumPt_decP (incP (decP f S p y) S p z0) S P z0 Q z g2
    have e2 := sumPt_incP (decP f S p y) S p z0 Q z
    have e3 := sumPt_decP f S p y Q z h1
    rw [show Mode.out y (Mode.imp (some p) z0) = y from rfl]
    omega

theorem srcPc_sumZ (f : Sq k → Pt → Sq k → ℕ) (S : Sq k) (P : Pt) (y : Sq k) (m : Mode k)
    (h : SrcOK f S P y m) (Q : Sq k) (pt : Pt) :
    (∑ z, PState.srcPc f S P y m Q pt z) + (if Q = S ∧ pt = P then 1 else 0) = ∑ z, f Q pt z := by
  rcases m with _ | ⟨_ | p, z0⟩
  · exact sumZ_decP f S P y Q pt h
  · exact sumZ_decP f S P z0 Q pt h
  · obtain ⟨hp, h1, h2⟩ := h
    show (∑ z, decP (incP (decP f S p y) S p z0) S P z0 Q pt z) + _ = _
    have g2 : 1 ≤ incP (decP f S p y) S p z0 S P z0 := by
      rw [incP_apply, decP_apply, if_neg (fun h' => hp h'.2.1.symm)]; omega
    have e1 := sumZ_decP (incP (decP f S p y) S p z0) S P z0 Q pt g2
    have e2 := sumZ_incP (decP f S p y) S p z0 Q pt
    have e3 := sumZ_decP f S p y Q pt h1
    omega

end SlidingPuzzle.Port
