import SlidingPuzzle.Hub.InFlightSum
import SlidingPuzzle.Hub.InFlightOrder
import SlidingPuzzle.Hub.InFlightSegment

/-!
Generic pipe residence, extracted from Hub/InFlight{Push,Window,Segment}.
The lane and class types and insertion offsets are independent of the board
layout. This is research code, not wired into the certified puzzle solver.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace SlidingPuzzle.GroupedPipe
open Finset SlidingPuzzle.Hub

variable {Lane Class : Type*} [DecidableEq Lane] [DecidableEq Class]

structure InsRec (Lane Class : Type*) where
  τ : ℕ
  H : Lane
  d : ℕ
  x : Class

abbrev Ghost (Lane Class : Type*) := Lane → ℕ → Option (Class × ℕ)

def insPos (s : ℕ) (offset : Lane → ℕ) (H : Lane) (d : ℕ) : ℕ := d * s + offset H

def ghostStep (s : ℕ) (offset : Lane → ℕ) (g : Ghost Lane Class)
    (r : InsRec Lane Class) : Ghost Lane Class :=
  Function.update g r.H (shiftIn (g r.H) (insPos s offset r.H r.d) (some (r.x, r.d)))

def ghostRun (s : ℕ) (offset : Lane → ℕ) (g : Ghost Lane Class)
    (L : List (InsRec Lane Class)) : Ghost Lane Class := L.foldl (ghostStep s offset) g


open Finset

variable {k : ℕ} (s : ℕ) (offset : Lane → ℕ)

/-- Ghost rows holding insertion indices. -/
abbrev IGhost (Lane : Type*) := Lane → ℕ → Option ℕ

/-- Insertion number `m` of the sequence `e`. -/
def istep (e : ℕ → InsRec Lane Class) (g : IGhost Lane) (m : ℕ) : IGhost Lane :=
  Function.update g (e m).H (shiftIn (g (e m).H) (insPos s offset (e m).H (e m).d) (some m))

/-- The first `m` insertions of `e`, with indices. -/
def irun (e : ℕ → InsRec Lane Class) : ℕ → IGhost Lane
  | 0 => fun _ _ => none
  | m + 1 => istep s offset e (irun e m) m

/-- Insertions after `i` and before `m` into the same half from a distance `≥`. -/
def pushes (e : ℕ → InsRec Lane Class) (i m : ℕ) : ℕ :=
  ((range m).filter fun j => i < j ∧ (e j).H = (e i).H ∧ (e i).d ≤ (e j).d).card

theorem insPos_mono (H : Lane) {d d' : ℕ} (h : d ≤ d') : insPos s offset H d ≤ insPos s offset H d' := by
  unfold insPos
  exact Nat.add_le_add_right (Nat.mul_le_mul_right s h) _

theorem pushes_succ (e : ℕ → InsRec Lane Class) (i m : ℕ) :
    pushes e i (m + 1) = pushes e i m +
      if i < m ∧ (e m).H = (e i).H ∧ (e i).d ≤ (e m).d then 1 else 0 := by
  unfold pushes
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

theorem pushes_self (e : ℕ → InsRec Lane Class) (m : ℕ) : pushes e m (m + 1) = 0 := by
  unfold pushes
  rw [card_eq_zero, filter_eq_empty_iff]
  intro j hj; simp at hj; omega

/-- Injectivity of an index row survives an insertion of a fresh index. -/
theorem shiftIn_inj {f : ℕ → Option ℕ} {p m : ℕ}
    (hf : ∀ q q' i, f q = some i → f q' = some i → q = q')
    (hlt : ∀ q i, f q = some i → i < m) :
    ∀ q q' i, shiftIn f p (some m) q = some i → shiftIn f p (some m) q' = some i → q = q' := by
  intro q q' i h h'
  unfold shiftIn at h h'
  split_ifs at h h' with h1 h2 h3 h4 h5 h6 h7 h8
  all_goals first
    | omega
    | (have := hf _ _ _ h h'; omega)
    | (cases h; have := hlt _ _ h'; omega)
    | (cases h'; have := hlt _ _ h; omega)

/-- The invariant of the indexed run. -/
structure IInv (e : ℕ → InsRec Lane Class) (m : ℕ) : Prop where
  val : ∀ H q i, irun s offset e m H q = some i →
    i < m ∧ (e i).H = H ∧ q + pushes e i m ≤ insPos s offset H (e i).d
  inj : ∀ H q q' i, irun s offset e m H q = some i → irun s offset e m H q' = some i → q = q'

theorem iinv_zero (e : ℕ → InsRec Lane Class) : IInv s offset e 0 :=
  ⟨fun _ _ _ h => by simp [irun] at h, fun _ _ _ _ h => by simp [irun] at h⟩

theorem iinv_succ (e : ℕ → InsRec Lane Class) (m : ℕ) (hI : IInv s offset e m) : IInv s offset e (m + 1) := by
  constructor
  · intro H q i h
    simp only [irun, istep] at h
    by_cases hH : H = (e m).H
    · subst hH
      rw [Function.update_self] at h
      unfold shiftIn at h
      split_ifs at h with h1 h2
      · obtain ⟨hi, hHi, hb⟩ := hI.val _ _ _ h
        have := pushes_succ e i m
        refine ⟨by omega, hHi, ?_⟩
        split_ifs at this <;> omega
      · cases h
        rw [pushes_self]
        exact ⟨by omega, rfl, by omega⟩
      · obtain ⟨hi, hHi, hb⟩ := hI.val _ _ _ h
        have hp := pushes_succ e i m
        refine ⟨by omega, hHi, ?_⟩
        split_ifs at hp with hc
        · have := insPos_mono s offset (e m).H hc.2.2
          omega
        · omega
    · rw [Function.update_of_ne hH] at h
      obtain ⟨hi, hHi, hb⟩ := hI.val _ _ _ h
      have hp := pushes_succ e i m
      refine ⟨by omega, hHi, ?_⟩
      split_ifs at hp with hc
      · exact absurd (hc.2.1.trans hHi).symm hH
      · omega
  · intro H q q' i h h'
    simp only [irun, istep] at h h'
    by_cases hH : H = (e m).H
    · subst hH
      rw [Function.update_self] at h h'
      exact shiftIn_inj (hI.inj _) (fun q i hq => (hI.val _ _ _ hq).1) q q' i h h'
    · rw [Function.update_of_ne hH] at h h'
      exact hI.inj _ _ _ _ h h'

theorem iinv (e : ℕ → InsRec Lane Class) : ∀ m, IInv s offset e m
  | 0 => iinv_zero s offset e
  | m + 1 => iinv_succ s offset e m (iinv e m)

/-- `ghostRun` on a prefix is the indexed run with the tags read off. -/
theorem ghostRun_take (L : List (InsRec Lane Class)) (r0 : InsRec Lane Class) :
    ∀ m, m ≤ L.length → ghostRun s offset (fun _ _ => none) (L.take m) =
      fun H q => (irun s offset (fun i => L.getD i r0) m H q).map
        fun i => ((L.getD i r0).x, (L.getD i r0).d)
  | 0, _ => by funext H q; simp [ghostRun, irun]
  | m + 1, hm => by
    have ih := ghostRun_take L r0 m (by omega)
    have hget : L[m]? = some (L.getD m r0) := by
      rw [List.getElem?_eq_getElem (by omega), List.getD_eq_getElem _ _ (by omega)]
    have happ : ∀ (A : List (InsRec Lane Class)) (r : InsRec Lane Class), ghostRun s offset (fun _ _ => none) (A ++ [r]) =
        ghostStep s offset (ghostRun s offset (fun _ _ => none) A) r := fun A r => by simp [ghostRun]
    rw [List.take_add_one, hget, Option.toList_some, happ, ih]
    funext H q
    simp only [ghostStep, irun, istep]
    by_cases hH : H = (L.getD m r0).H
    · subst hH
      simp only [Function.update_self]
      unfold shiftIn
      split_ifs <;> simp
    · simp only [Function.update_of_ne hH]



open Finset

variable {k : ℕ} (s : ℕ) (offset : Lane → ℕ)

/-- The row insertion of a record. -/
def proj (r : InsRec Lane Class) : Lane × ℕ × Class := (r.H, r.d, r.x)

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

variable {L : List (InsRec Lane Class)} (r0 : InsRec Lane Class) {R : ℕ → List (Lane × ℕ × Class)}

/-- Counting the records of time `τ` with a property of their insertion. -/
theorem card_time_filter (hperm : ∀ τ, ((L.filter fun r => r.τ = τ).map proj).Perm (R τ))
    (τ : ℕ) (P : Lane × ℕ × Class → Prop) [DecidablePred P] :
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



open Finset

variable {k : ℕ} (s : ℕ) (offset : Lane → ℕ)

/-- Insertions with index in `[t, m)` into `H` at a position `≥ B`. -/
def pushesAbove (e : ℕ → InsRec Lane Class) (H : Lane) (B t m : ℕ) : ℕ :=
  ((Ico t m).filter fun l => (e l).H = H ∧ B ≤ insPos s offset (e l).H (e l).d).card

theorem pushesAbove_succ (e : ℕ → InsRec Lane Class) (H : Lane) (B t m : ℕ) (htm : t ≤ m) :
    pushesAbove s offset e H B t (m + 1) = pushesAbove s offset e H B t m +
      if (e m).H = H ∧ B ≤ insPos s offset (e m).H (e m).d then 1 else 0 := by
  unfold pushesAbove
  rw [show m + 1 = m.succ from rfl, Nat.Ico_succ_right_eq_insert_Ico htm, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

theorem pushesAbove_mono (e : ℕ → InsRec Lane Class) (H : Lane) (B t : ℕ) {m m' : ℕ} (h : m ≤ m') :
    pushesAbove s offset e H B t m ≤ pushesAbove s offset e H B t m' := by
  unfold pushesAbove
  apply card_le_card
  intro l; simp only [mem_filter, mem_Ico]; intro h'; exact ⟨⟨h'.1.1, by omega⟩, h'.2⟩

/-- **Segment lemma**: a tile at position `≤ B` at step `t` is moved toward the
head by each later insertion into its half at a position `≥ B`. -/
theorem seg_bound (e : ℕ → InsRec Lane Class) (H : Lane) {i B t : ℕ} (hit : i < t)
    (h0 : ∀ q, irun s offset e t H q = some i → q ≤ B) :
    ∀ m, t ≤ m → ∀ q, irun s offset e m H q = some i → q + pushesAbove s offset e H B t m ≤ B := by
  intro m htm
  induction m, htm using Nat.le_induction with
  | base =>
    intro q hq
    have : pushesAbove s offset e H B t t = 0 := by simp [pushesAbove]
    rw [this]; simpa using h0 q hq
  | succ m htm ih =>
    intro q hq
    rw [pushesAbove_succ s offset e H B t m htm]
    simp only [irun, istep] at hq
    by_cases hH : H = (e m).H
    · subst hH
      rw [Function.update_self] at hq
      have hc : ∀ q', irun s offset e m (e m).H q' = some i → q' + pushesAbove s offset e (e m).H B t m ≤ B := ih
      by_cases hP : B ≤ insPos s offset (e m).H (e m).d
      · rw [if_pos ⟨rfl, hP⟩]
        unfold shiftIn at hq
        by_cases h1 : q < insPos s offset (e m).H (e m).d
        · rw [if_pos h1] at hq; have := hc _ hq; omega
        · rw [if_neg h1] at hq
          by_cases h2 : q = insPos s offset (e m).H (e m).d
          · rw [if_pos h2] at hq; cases hq; omega
          · rw [if_neg h2] at hq; have := hc _ hq; omega
      · rw [if_neg (fun h => hP h.2)]
        unfold shiftIn at hq
        by_cases h1 : q < insPos s offset (e m).H (e m).d
        · rw [if_pos h1] at hq; have := hc _ hq; omega
        · rw [if_neg h1] at hq
          by_cases h2 : q = insPos s offset (e m).H (e m).d
          · rw [if_pos h2] at hq; cases hq; omega
          · rw [if_neg h2] at hq; have := hc _ hq; omega
    · rw [Function.update_of_ne hH] at hq
      have := ih _ hq
      rw [if_neg (fun h => hH h.1.symm)]
      omega

/-- The prefix of a sorted list up to the end of time `T`. -/
def upto (L : List (InsRec Lane Class)) (r0 : InsRec Lane Class) (T : ℕ) : ℕ :=
  ((range L.length).filter fun l => (L.getD l r0).τ ≤ T).card

section list

variable {L : List (InsRec Lane Class)} (r0 : InsRec Lane Class)

theorem lt_upto_iff (hsort : L.Pairwise fun a b => a.τ ≤ b.τ) (T : ℕ) {l : ℕ}
    (hl : l < L.length) : l < upto L r0 T ↔ (L.getD l r0).τ ≤ T := by
  unfold upto
  constructor
  · intro h
    by_contra hc
    have hsub : (range L.length).filter (fun l' => (L.getD l' r0).τ ≤ T) ⊆ range l := by
      intro l' hl'
      simp only [mem_filter, mem_range] at hl' ⊢
      by_contra hc'
      have := tau_mono r0 hsort (not_lt.mp hc') hl'.1
      omega
    have := card_le_card hsub
    rw [card_range] at this; omega
  · intro h
    have hsub : range (l + 1) ⊆ (range L.length).filter (fun l' => (L.getD l' r0).τ ≤ T) := by
      intro l' hl'
      simp only [mem_filter, mem_range] at hl' ⊢
      exact ⟨by omega, (tau_mono r0 hsort (by omega) hl).trans h⟩
    have := card_le_card hsub
    rw [card_range] at this; omega

theorem upto_le_length (T : ℕ) : upto L r0 T ≤ L.length := by
  unfold upto
  exact (card_filter_le _ _).trans (by simp)

/-- The insertions of the times `(T, T + w]` are pushes between `upto T` and
`upto (T + w)`. -/
theorem sum_window_le_pushesAbove (hsort : L.Pairwise fun a b => a.τ ≤ b.τ)
    {R : ℕ → List (Lane × ℕ × Class)}
    (hperm : ∀ τ, ((L.filter fun r => r.τ = τ).map proj).Perm (R τ))
    (H : Lane) (j T w : ℕ) :
    ∑ τ ∈ Ioc T (T + w), (R τ).countP (fun p => decide (p.1 = H ∧ j ≤ p.2.1)) ≤
      pushesAbove s offset (fun l => L.getD l r0) H (insPos s offset H j) (upto L r0 T)
        (upto L r0 (T + w)) := by
  simp_rw [← card_time_filter r0 hperm]
  rw [sum_card_fiber]
  apply card_le_card
  intro l hl
  simp only [mem_filter, mem_range, mem_Ioc, proj] at hl
  obtain ⟨hlen, ⟨h1, h2⟩, hH, hd⟩ := hl
  simp only [mem_filter, mem_Ico]
  refine ⟨⟨?_, ?_⟩, hH, ?_⟩
  · by_contra hc
    have := (lt_upto_iff r0 hsort T hlen).mp (not_le.mp hc)
    omega
  · exact (lt_upto_iff r0 hsort (T + w) hlen).mpr h2
  · rw [hH]; exact insPos_mono s offset H hd

/-- **Residence lemma**: with the window property for every band `j ≤ d`, a
present tile inserted from distance `d` was inserted at most `∑_{j ≤ d} w j`
times before the last time of the prefix. -/
theorem last_le_of_segments {R : ℕ → List (Lane × ℕ × Class)} {T : ℕ}
    (hsort : L.Pairwise fun a b => a.τ ≤ b.τ) (hlt : ∀ r ∈ L, r.τ < T)
    (hperm : ∀ τ, ((L.filter fun r => r.τ = τ).map proj).Perm (R τ))
    (w : ℕ → ℕ) (H : Lane) (d : ℕ)
    (hgap : ∀ j, 0 < j → insPos s offset H j = insPos s offset H (j - 1) + s)
    (hzero : insPos s offset H 0 < s)
    (hA : ∀ j ≤ d, ∀ τ0, τ0 + w j < T → s ≤
      ∑ τ ∈ Ioc τ0 (τ0 + w j), (R τ).countP (fun p => decide (p.1 = H ∧ j ≤ p.2.1)))
    {m i q : ℕ} (hm : m ≤ L.length) (him : i < m) (hd : (L.getD i r0).d = d)
    (hq : irun s offset (fun l => L.getD l r0) m H q = some i) :
    (L.getD (m - 1) r0).τ ≤ (L.getD i r0).τ + ∑ j ∈ range (d + 1), w j := by
  set e := fun l => L.getD l r0 with he
  set τi := (L.getD i r0).τ
  by_contra hc
  push Not at hc
  have hlast : (L.getD (m - 1) r0).τ < T := by
    have hmem : L.getD (m - 1) r0 ∈ L := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    exact hlt _ hmem
  -- stage starts: `S j = τi + ∑_{j < j' ≤ d} w j'`
  set S : ℕ → ℕ := fun j => τi + ∑ j' ∈ Ioc j d, w j' with hS
  have hSd : S d = τi := by simp [hS]
  have hSge : ∀ j, τi ≤ S j := fun j => by simp only [hS]; exact Nat.le_add_right _ _
  have hSstep : ∀ j, 0 < j → j ≤ d → S (j - 1) = S j + w j := by
    intro j hj hjd
    simp only [hS]
    have : Ioc (j - 1) d = insert j (Ioc j d) := by
      ext x; simp only [mem_Ioc, mem_insert]; omega
    rw [this, sum_insert (by simp)]; ring
  have hS0 : S 0 + w 0 = τi + ∑ j ∈ range (d + 1), w j := by
    simp only [hS]
    have e : Ioc 0 d = Ico 1 (d + 1) := by ext x; simp only [mem_Ioc, mem_Ico]; omega
    rw [e, sum_Ico_eq_sum_range, sum_range_succ']
    simp only [Nat.add_sub_cancel]
    have : ∀ x ∈ range d, w (1 + x) = w (x + 1) := fun x _ => by rw [add_comm]
    rw [sum_congr rfl this]; ring
  have hSle : ∀ j ≤ d, S j + w j ≤ τi + ∑ j ∈ range (d + 1), w j := by
    intro j hjd
    rw [← hS0]
    simp only [hS]
    have : ∑ j' ∈ Ioc j d, w j' + w j ≤ ∑ j' ∈ Ioc 0 d, w j' + w 0 := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rfl
      · have e1 : Ioc 0 d = Ioc 0 (j - 1) ∪ insert j (Ioc j d) := by
          ext x; simp only [mem_Ioc, mem_union, mem_insert]; omega
        have hdisj : Disjoint (Ioc 0 (j - 1)) (insert j (Ioc j d)) := by
          rw [disjoint_left]; intro x hx hx'
          simp only [mem_Ioc, mem_insert] at hx hx'; omega
        rw [e1, sum_union hdisj, sum_insert (by simp)]
        omega
    omega
  -- the stages fit before the last time
  have hfit : ∀ j ≤ d, S j + w j < T := fun j hj => by have := hSle j hj; omega
  have hup_m : ∀ j ≤ d, upto L r0 (S j + w j) < m := by
    intro j hj
    by_contra hc'
    have h1 := (lt_upto_iff r0 hsort (S j + w j) (l := m - 1) (by omega)).mp (by omega)
    have := hSle j hj
    omega
  have hup_i : i < upto L r0 (S d) := by
    rw [lt_upto_iff r0 hsort _ (by omega), hSd]
  -- the claim at every stage
  have hpush : ∀ j ≤ d, s ≤ pushesAbove s offset e H (insPos s offset H j) (upto L r0 (S j))
      (upto L r0 (S j + w j)) :=
    fun j hj => (hA j hj (S j) (hfit j hj)).trans (sum_window_le_pushesAbove s offset r0 hsort hperm H j _ _)
  have hI := iinv s offset e (i + 1)
  have hstart : ∀ q', irun s offset e (i + 1) H q' = some i → q' ≤ insPos s offset H d := by
    intro q' hq'
    obtain ⟨-, -, hb⟩ := hI.val _ _ _ hq'
    simp only [he] at hb
    rw [hd] at hb
    omega
  have hstage : ∀ r ≤ d, ∀ q', irun s offset e (upto L r0 (S (d - r))) H q' = some i →
      q' ≤ insPos s offset H (d - r) := by
    intro r
    induction r with
    | zero =>
      intro _ q' hq'
      have := seg_bound s offset e H (by omega) hstart (upto L r0 (S d)) (by omega) q' hq'
      simp only [Nat.sub_zero]; omega
    | succ r ih =>
      intro hr q' hq'
      have hj : 0 < d - r := by omega
      have hstep := hSstep (d - r) hj (by omega)
      rw [show d - (r + 1) = d - r - 1 by omega] at hq' ⊢
      rw [hstep] at hq'
      have hlo : i < upto L r0 (S (d - r)) := by
        refine lt_of_lt_of_le hup_i ?_
        unfold upto
        apply card_le_card
        intro l; simp only [mem_filter, mem_range]
        intro hl; refine ⟨hl.1, hl.2.trans ?_⟩
        rw [hSd]; exact hSge _
      have hmono : upto L r0 (S (d - r)) ≤ upto L r0 (S (d - r) + w (d - r)) := by
        unfold upto
        apply card_le_card
        intro l; simp only [mem_filter, mem_range]; omega
      have := seg_bound s offset e H hlo (ih (by omega)) _ hmono q' hq'
      have hp := hpush (d - r) (by omega)
      have hg := hgap (d - r) hj
      omega
  -- the last stage evicts the tile
  have h0 := hstage d le_rfl
  rw [Nat.sub_self] at h0
  have hlo : i < upto L r0 (S 0) := by
    refine lt_of_lt_of_le hup_i ?_
    unfold upto
    apply card_le_card
    intro l; simp only [mem_filter, mem_range]
    intro hl; refine ⟨hl.1, hl.2.trans ?_⟩
    rw [hSd]; exact hSge _
  have hmono : upto L r0 (S 0) ≤ m := by
    have := hup_m 0 (by omega)
    have : upto L r0 (S 0) ≤ upto L r0 (S 0 + w 0) := by
      unfold upto; apply card_le_card; intro l; simp only [mem_filter, mem_range]; omega
    omega
  have hfinal := seg_bound s offset e H hlo h0 m hmono q hq
  have hp := hpush 0 (by omega)
  have hpm := pushesAbove_mono s offset e H (insPos s offset H 0) (upto L r0 (S 0))
    (le_of_lt (hup_m 0 (by omega)))
  omega

end list

section main

variable {L : List (InsRec Lane Class)} (r0 : InsRec Lane Class) {R : ℕ → List (Lane × ℕ × Class)} {T : ℕ}
  (w : Lane → ℕ → ℕ) (Nb : Lane → Class → ℕ)

/-- Present class-`x` tiles of one half, for a prefix of length `m ≤ |L|`, with
the segmented residence windows `∑_{j ≤ d} w H j`. -/
theorem count_tagged_le_seg
    (hsort : L.Pairwise fun a b => a.τ ≤ b.τ) (hlt : ∀ r ∈ L, r.τ < T)
    (hperm : ∀ τ, ((L.filter fun r => r.τ = τ).map proj).Perm (R τ))
    (hdk : ∀ τ, ∀ p ∈ R τ, p.2.1 < k)
    (hgap : ∀ H j, 0 < j → insPos s offset H j = insPos s offset H (j - 1) + s)
    (hzero : ∀ H, insPos s offset H 0 < s)
    (hA : ∀ H j, j < k → ∀ τ0, τ0 + w H j < T → s ≤
      ∑ τ ∈ Ioc τ0 (τ0 + w H j), (R τ).countP (fun p => decide (p.1 = H ∧ j ≤ p.2.1)))
    (hB : ∀ H x τl, τl < T → ∑ d ∈ range k,
      ∑ τ ∈ Icc (τl - ∑ j ∈ range (d + 1), w H j) τl,
        (R τ).countP (fun p => decide (p = (H, d, x))) ≤ Nb H x)
    {m : ℕ} (hm : m ≤ L.length) (H : Lane) (x : Class) (len : ℕ) :
    ((range len).filter fun q =>
        (irun s offset (fun i => L.getD i r0) m H q).map (fun i => (L.getD i r0).x) = some x).card ≤
      Nb H x := by
  set e := fun i => L.getD i r0 with he
  have hI := iinv s offset e m
  -- present tiles inject into their insertions
  have hinj : ((range len).filter fun q => (irun s offset e m H q).map (fun i => (e i).x) = some x).card ≤
      ((range m).filter fun i => (e i).H = H ∧ (e i).x = x ∧
        ∃ q ∈ range len, irun s offset e m H q = some i).card := by
    refine card_le_card_of_injOn (fun q => (irun s offset e m H q).getD 0) ?_ ?_
    · intro q hq
      simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at hq
      obtain ⟨i, hi, hfi⟩ := Option.map_eq_some_iff.mp hq.2
      obtain ⟨him, hH, -⟩ := hI.val _ _ _ hi
      simp only [coe_filter, Set.mem_ofPred_eq, mem_range, hi, Option.getD_some]
      exact ⟨him, hH, hfi, q, hq.1, hi⟩
    · intro q hq q' hq' heq
      simp only [coe_filter, Set.mem_ofPred_eq] at hq hq'
      obtain ⟨i, hi, -⟩ := Option.map_eq_some_iff.mp hq.2
      obtain ⟨i', hi', -⟩ := Option.map_eq_some_iff.mp hq'.2
      simp only [hi, hi', Option.getD_some] at heq
      subst heq
      exact hI.inj _ _ _ _ hi hi'
  refine hinj.trans ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp
  have hmaps : ∀ i ∈ (range m).filter (fun i => (e i).H = H ∧ (e i).x = x ∧
      ∃ q ∈ range len, irun s offset e m H q = some i), (e i).d ∈ range k := by
    intro i hi
    simp only [mem_filter, mem_range] at hi
    exact mem_range.mpr (hdk _ _ (proj_mem r0 hperm (i := i) (by omega)))
  rw [card_eq_sum_card_fiberwise hmaps]
  set τl := (L.getD (m - 1) r0).τ
  have hτl : τl < T := by
    have hmem : L.getD (m - 1) r0 ∈ L := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    exact hlt _ hmem
  refine le_trans (sum_le_sum fun d hd => ?_) (hB H x τl hτl)
  have hdk' := mem_range.mp hd
  set W := ∑ j ∈ range (d + 1), w H j
  calc _ ≤ ((range L.length).filter fun i => (L.getD i r0).τ ∈ Icc (τl - W) τl ∧
        proj (L.getD i r0) = (H, d, x)).card := by
        apply card_le_card
        intro i hi
        simp only [mem_filter, mem_range] at hi
        obtain ⟨⟨him, hH, hx, q, -, hq⟩, hdi⟩ := hi
        have h1 := last_le_of_segments s offset r0 hsort hlt hperm (w H) H d (hgap H) (hzero H)
          (fun j hj => hA H j (by omega)) hm him hdi hq
        have h2 := tau_mono r0 hsort (j := i) (j' := m - 1) (by omega) (by omega)
        simp only [mem_filter, mem_range, mem_Icc, proj]
        refine ⟨by omega, ⟨by omega, by omega⟩, ?_⟩
        simp only [he] at hH hx hdi
        rw [hH, hdi, hx]
    _ = ∑ τ ∈ Icc (τl - W) τl, ((range L.length).filter fun i =>
          (L.getD i r0).τ = τ ∧ proj (L.getD i r0) = (H, d, x)).card :=
        (sum_card_fiber _ _ _ _).symm
    _ = ∑ τ ∈ Icc (τl - W) τl, (R τ).countP (fun p => decide (p = (H, d, x))) :=
        sum_congr rfl fun τ _ => card_time_filter r0 hperm τ (fun p => p = (H, d, x))


end main

/-- A layout-independent form for actual tagged pipe contents. The lower and
upper window hypotheses are statistical obligations, not assumed conclusions
about pipe contents. Any number of lanes/classes and any within-round order
are allowed. -/
theorem ghost_count_le {k : ℕ} (s : ℕ) (offset : Lane → ℕ)
    (hoff : ∀ H, offset H < s)
    {L : List (InsRec Lane Class)} (r0 : InsRec Lane Class)
    {R : ℕ → List (Lane × ℕ × Class)} {T : ℕ}
    (w : Lane → ℕ → ℕ) (Nb : Lane → Class → ℕ)
    (hsort : L.Pairwise fun a b => a.τ ≤ b.τ) (hlt : ∀ r ∈ L, r.τ < T)
    (hperm : ∀ τ, ((L.filter fun r => r.τ = τ).map proj).Perm (R τ))
    (hdk : ∀ τ, ∀ p ∈ R τ, p.2.1 < k)
    (hA : ∀ H j, j < k → ∀ τ0, τ0 + w H j < T → s ≤
      ∑ τ ∈ Ioc τ0 (τ0 + w H j), (R τ).countP (fun p => decide (p.1 = H ∧ j ≤ p.2.1)))
    (hB : ∀ H x τl, τl < T → ∑ d ∈ range k,
      ∑ τ ∈ Icc (τl - ∑ j ∈ range (d + 1), w H j) τl,
        (R τ).countP (fun p => decide (p = (H, d, x))) ≤ Nb H x)
    {m : ℕ} (hm : m ≤ L.length) (H : Lane) (x : Class) (len : ℕ) :
    ((range len).filter fun q =>
      (ghostRun s offset (fun _ _ => none) (L.take m) H q).map Prod.fst = some x).card ≤ Nb H x := by
  rw [ghostRun_take s offset L r0 m hm]
  simp only [Option.map_map, Function.comp_def]
  apply count_tagged_le_seg s offset r0 w Nb hsort hlt hperm hdk ?_ ?_ hA hB hm
  · intro H j hj
    have he : j = j - 1 + 1 := by omega
    simp only [insPos]
    conv_lhs => lhs; lhs; rw [he]
    ring
  · intro H
    simpa [insPos] using hoff H

end SlidingPuzzle.GroupedPipe


/-! A common good permutation for an arbitrary finite family of tagged lanes.
Extracted from Hub/InFlightOrder: the old board geometry is replaced by two
explicit matching-traffic bounds. No assumption about pipe occupancy is made.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace SlidingPuzzle.GroupedOrder
open Finset SlidingPuzzle.Hub
variable {Lane Class : Type*} [Fintype Lane] [DecidableEq Lane]
  [Fintype Class] [DecidableEq Class]
variable {Δ : ℕ} (k s : ℕ) (rs : Fin Δ → List (Lane × ℕ × Class))
/-- Insertions into `H` from distances `≥ d` in plan round `j`. -/
noncomputable def gcnt (H : Lane) (d : ℕ) (j : Fin Δ) : ℕ :=
  (rs j).countP fun p => decide (p.1 = H ∧ d ≤ p.2.1)

/-- Insertions into `H` from distance exactly `d` in plan round `j`. -/
noncomputable def gdist (H : Lane) (d : ℕ) (j : Fin Δ) : ℕ :=
  (rs j).countP fun p => decide (p.1 = H ∧ p.2.1 = d)

/-- Insertions of `(H, d, x)` in plan round `j` (`0` or `1`). -/
noncomputable def acnt (H : Lane) (d : ℕ) (x : Class) (j : Fin Δ) : ℕ :=
  (rs j).countP fun p => decide (p = (H, d, x))

/-- `B_d`: all insertions into `H` from distances `≥ d`. -/
noncomputable def Btot (H : Lane) (d : ℕ) : ℕ := ∑ j, gcnt rs H d j

/-- `A_{x,d}`: all insertions of `(H, d, x)`. -/
noncomputable def Atot (H : Lane) (d : ℕ) (x : Class) : ℕ := ∑ j, acnt rs H d x j

/-- The window of band `d`: `w_d = min Δ (⌊4 s Δ / (3 B_d)⌋ + 1)` (`Δ` if `B_d = 0`),
long enough for `s` insertions from distances `≥ d`. -/
noncomputable def win (H : Lane) (d : ℕ) : ℕ :=
  if Btot rs H d = 0 then Δ else min Δ (4 * s * Δ / (3 * Btot rs H d) + 1)

/-- The residence window of a tile inserted from distance `d`: `∑_{j ≤ d} w_j`. -/
noncomputable def wsum (H : Lane) (d : ℕ) : ℕ := ∑ j ∈ Finset.range (d + 1), win s rs H j

/-- The additive slack of the upper tail, `λ = 3 (log₂ n + 1)`. -/
def lamN (n : ℕ) : ℕ := 3 * (Nat.log 2 n + 1)

/-- The additive slack of the lower tail, `λ_A = log₂ (k³ s²) + 4`: there are
fewer lower-tail events than upper-tail ones. -/
def lamA (k s : ℕ) : ℕ := Nat.log 2 (k ^ 3 * s ^ 2) + 4

/-- `Δ` times the mean number of present class-`x` tiles of `H`:
`∑_d A_{x,d} (W_d + 1)`. -/
noncomputable def Mtot (H : Lane) (x : Class) : ℕ :=
  ∑ d ∈ Finset.range k, Atot rs H d x * (wsum s rs H d + 1)

/-- The bound on present class-`x` tiles of `H`, all distances together. -/
noncomputable def Nbx (n : ℕ) (H : Lane) (x : Class) : ℕ :=
  if Mtot k s rs H x = 0 then 0 else 41 * Mtot k s rs H x / (40 * Δ) + 15 * lamN n

/-- The row insertions at time `τ` of the order `σ` (none after the end). -/
noncomputable def rnd (σ : Equiv.Perm (Fin Δ)) (τ : ℕ) : List (Lane × ℕ × Class) :=
  if h : τ < Δ then rs (σ ⟨τ, h⟩) else []

/-- Sums over times of a function of `rnd` are sums over plan rounds. -/
theorem sum_rnd (σ : Equiv.Perm (Fin Δ)) (U : Finset ℕ) (F : List (Lane × ℕ × Class) → ℕ)
    (hF : F [] = 0) :
    ∑ τ ∈ U, F (rnd rs σ τ) =
      ∑ τ ∈ univ.filter (fun τ : Fin Δ => τ.val ∈ U), F (rs (σ τ)) := by
  have h1 : ∑ τ ∈ univ.filter (fun τ : Fin Δ => τ.val ∈ U), F (rs (σ τ)) =
      ∑ τ ∈ (univ.filter (fun τ : Fin Δ => τ.val ∈ U)).map Fin.valEmbedding, F (rnd rs σ τ) := by
    rw [sum_map]
    refine sum_congr rfl fun τ _ => ?_
    simp [rnd, τ.isLt]
  have h2 : (univ.filter (fun τ : Fin Δ => τ.val ∈ U)).map Fin.valEmbedding =
      U.filter (· < Δ) := by
    ext i
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨ha, a.isLt⟩
    · rintro ⟨hi, hlt⟩; exact ⟨⟨i, hlt⟩, hi, rfl⟩
  rw [h1, h2, sum_filter]
  refine sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rfl
  · simp [rnd, h, hF]

theorem card_fin_filter_mem {Δ : ℕ} (U : Finset ℕ) :
    (univ.filter (fun τ : Fin Δ => τ.val ∈ U)).card = (U.filter (· < Δ)).card := by
  rw [← card_map Fin.valEmbedding]
  congr 1
  ext i
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨ha, a.isLt⟩
  · rintro ⟨hi, hlt⟩; exact ⟨⟨i, hlt⟩, hi, rfl⟩

theorem mem_rnd {σ : Equiv.Perm (Fin Δ)} {τ : ℕ} {p : Lane × ℕ × Class} (hp : p ∈ rnd rs σ τ) :
    ∃ j, p ∈ rs j := by
  unfold rnd at hp
  split_ifs at hp
  · exact ⟨_, hp⟩
  · simp at hp


/-- The times `(τ0, τ0 + w]`. -/
def winA (Δ τ0 w : ℕ) : Finset (Fin Δ) := univ.filter fun τ => τ.val ∈ Ioc τ0 (τ0 + w)

theorem card_winA {τ0 w : ℕ} (h : τ0 + w < Δ) : (winA Δ τ0 w).card = w := by
  rw [winA, card_fin_filter_mem, filter_true_of_mem (fun i hi => by rw [mem_Ioc] at hi; omega),
    Nat.card_Ioc]
  omega

/-- Orders violating (A) at `(H, d, τ0)`. -/
noncomputable def badA (H : Lane) (d : ℕ) (τ0 : Fin Δ) : Finset (Equiv.Perm (Fin Δ)) :=
  univ.filter fun σ => τ0.val + win s rs H d < Δ ∧
    ∑ τ ∈ winA Δ τ0.val (win s rs H d), gcnt rs H d (σ τ) < s

/-- Rounds that insert class `x` into `H` from a distance `d` whose window
`[τl - W_d, τl]` contains the position `τ`. Since the windows end at `τl`,
these sets grow with `τ` up to `τl` and are empty after it: a chain. -/
noncomputable def chainSet (H : Lane) (x : Class) (τl : ℕ) (τ : Fin Δ) : Finset (Fin Δ) :=
  univ.filter fun j => ∃ d ∈ range k, τl - wsum s rs H d ≤ τ.val ∧ τ.val ≤ τl ∧
    acnt rs H d x j ≠ 0

/-- Class-`x` insertions into `H` from distance `d` in the window `[τl - W_d, τl]`,
summed over `d`. -/
noncomputable def mcnt (H : Lane) (x : Class) (τl : ℕ) (σ : Equiv.Perm (Fin Δ)) : ℕ :=
  ∑ d ∈ range k, ∑ τ ∈ univ.filter (fun τ : Fin Δ => τ.val ∈ Icc (τl - wsum s rs H d) τl),
    acnt rs H d x (σ τ)

/-- Orders violating (B) at `(H, x, τl)`. -/
noncomputable def badB (n : ℕ) (H : Lane) (x : Class) (τl : Fin Δ) :
    Finset (Equiv.Perm (Fin Δ)) :=
  univ.filter fun σ => Nbx k s rs n H x < mcnt k s rs H x τl.val σ

/-- `x < (x / b + 1) * b` as reals. -/
theorem nat_div_add_one_gt (x b : ℕ) (hb : 0 < b) : (x : ℝ) / b < ((x / b : ℕ) : ℝ) + 1 := by
  have h := Nat.lt_div_mul_add (a := x) hb
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_lt_iff₀ hbR]
  have : (x : ℝ) < ((x / b : ℕ) : ℝ) * b + b := by exact_mod_cast h
  linarith

theorem card_badA
    (hbatch : ∀ j H (Q : Lane × ℕ × Class → Prop) [DecidablePred Q],
      (rs j).countP (fun p => decide (p.1 = H ∧ Q p)) ≤ k) {lam : ℕ} (hk : 0 < k) (hlam : 76 * k * lam ≤ 5 * s) (H : Lane) (d : ℕ)
    (τ0 : Fin Δ) : (badA s rs H d τ0).card * 2 ^ lam ≤ Δ.factorial := by
  set w := win s rs H d with hw
  set B := Btot rs H d with hB
  -- trivial cases: the window does not fit
  by_cases hfit : τ0.val + w < Δ
  swap
  · have : badA s rs H d τ0 = ∅ := by
      rw [badA, filter_eq_empty_iff]; intro σ _ h; exact hfit h.1
    rw [this]; simp
  have hB0 : B ≠ 0 := by
    intro h0
    have : w = Δ := by rw [hw, win, if_pos h0]
    omega
  have hwdef : w = 4 * s * Δ / (3 * B) + 1 := by
    have : w = min Δ (4 * s * Δ / (3 * B) + 1) := by rw [hw, win, if_neg hB0]
    rw [this] at hfit ⊢
    rcases min_choice Δ (4 * s * Δ / (3 * B) + 1) with h | h
    · rw [h] at hfit; omega
    · exact h
  have hΔ : 0 < Δ := Nat.lt_of_le_of_lt (Nat.zero_le _) τ0.isLt
  have hBpos : 0 < B := Nat.pos_of_ne_zero hB0
  have hkey : 4 * s * Δ < w * (3 * B) := by
    rw [hwdef, add_mul, one_mul]; exact Nat.lt_div_mul_add (by omega)
  -- Chernoff
  set g : Fin Δ → ℝ := fun j => (gcnt rs H d j : ℝ) with hg
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hg0 : ∀ j, 0 ≤ g j := fun j => Nat.cast_nonneg _
  have hgK : ∀ j, g j ≤ k := fun j => by
    simp only [hg]; exact_mod_cast hbatch j H (fun p => d ≤ p.2.1)
  have hcard : (Fintype.card (Fin Δ)) = Δ := Fintype.card_fin Δ
  have hT := card_winA (Δ := Δ) hfit
  have hsumg : ∑ j, g j = B := by simp only [hg, hB, Btot]; push_cast; rfl
  have hch := card_lower_tail_log (winA Δ τ0.val w) g hkR hg0 hgK (by rw [hcard]; exact hΔ)
  rw [hT, hsumg, hcard] at hch
  set μ : ℝ := (w : ℝ) * B / Δ with hμ
  have hΔR : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  have hμgt : 4 * (s : ℝ) < 3 * μ := by
    rw [hμ, mul_div_assoc', lt_div_iff₀ hΔR]
    have : ((4 * s * Δ : ℕ) : ℝ) < ((w * (3 * B) : ℕ) : ℝ) := by exact_mod_cast hkey
    push_cast at this; linarith
  have hsub : badA s rs H d τ0 ⊆ univ.filter fun σ : Equiv.Perm (Fin Δ) =>
      ∑ τ ∈ winA Δ τ0.val w, g (σ τ) ≤ 3 / 4 * μ := by
    intro σ hσ
    simp only [badA, mem_filter, mem_univ, true_and] at hσ ⊢
    have h1 : ∑ τ ∈ winA Δ τ0.val w, g (σ τ) + 1 ≤ s := by
      simp only [hg]; exact_mod_cast hσ.2
    linarith
  have hc1 : ((badA s rs H d τ0).card : ℝ) ≤ Δ.factorial * Real.exp (-(3423 * μ) / (100000 * k)) :=
    (Nat.cast_le.mpr (card_le_card hsub)).trans hch
  -- `2^λ ≤ exp(3423μ / (100000 k))`
  have hlamR : 76 * (k : ℝ) * lam ≤ 5 * s := by exact_mod_cast hlam
  have h2lam : (2 : ℝ) ^ lam ≤ Real.exp (3423 * μ / (100000 * k)) := by
    have hlog : Real.log 2 ≤ 6931471808 / 10000000000 := by linarith [Real.log_two_lt_d9]
    calc (2 : ℝ) ^ lam = Real.exp (lam * Real.log 2) := by
          rw [Real.exp_nat_mul, Real.exp_log two_pos]
      _ ≤ Real.exp (3423 * μ / (100000 * k)) := by
          apply Real.exp_le_exp.mpr
          rw [le_div_iff₀ (by positivity)]
          have : (lam : ℝ) * Real.log 2 ≤ 6931471808 / 10000000000 * lam := by
            have := Nat.cast_nonneg (α := ℝ) lam
            nlinarith
          nlinarith
  have hfin : ((badA s rs H d τ0).card : ℝ) * 2 ^ lam ≤ Δ.factorial := by
    calc ((badA s rs H d τ0).card : ℝ) * 2 ^ lam
        ≤ Δ.factorial * Real.exp (-(3423 * μ) / (100000 * k)) *
            Real.exp (3423 * μ / (100000 * k)) := by
          gcongr
      _ = Δ.factorial := by
          rw [mul_assoc, ← Real.exp_add]; simp [neg_div]
  exact_mod_cast hfin

omit k s rs in
theorem sum_ite_le_ite_exists {K : ℕ} (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℕ)
    (hf : ∑ d ∈ range K, f d ≤ 1) :
    ∑ d ∈ range K, (if P d then f d else 0) ≤ if ∃ d ∈ range K, P d ∧ f d ≠ 0 then 1 else 0 := by
  split_ifs with h
  · exact (sum_le_sum fun d _ => by split_ifs <;> simp).trans hf
  · push Not at h
    apply le_of_eq
    refine sum_eq_zero fun d hd => ?_
    split_ifs with hP
    · exact h d hd hP
    · rfl

omit k s rs in
theorem ite_exists_le_sum_ite {K : ℕ} (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℕ) :
    (if ∃ d ∈ range K, P d ∧ f d ≠ 0 then 1 else 0) ≤ ∑ d ∈ range K, (if P d then f d else 0) := by
  split_ifs with h
  · obtain ⟨d, hd, hP, hf⟩ := h
    calc 1 ≤ (if P d then f d else 0) := by rw [if_pos hP]; omega
      _ ≤ _ := single_le_sum (f := fun d => if P d then f d else 0) (fun _ _ => Nat.zero_le _) hd
  · exact Nat.zero_le _

theorem chainSet_chain (H : Lane) (x : Class) (τl : ℕ) (τ τ' : Fin Δ) :
    chainSet k s rs H x τl τ ⊆ chainSet k s rs H x τl τ' ∨
      chainSet k s rs H x τl τ' ⊆ chainSet k s rs H x τl τ := by
  have key : ∀ a b : Fin Δ, a.val ≤ b.val →
      chainSet k s rs H x τl a ⊆ chainSet k s rs H x τl b ∨
        chainSet k s rs H x τl b ⊆ chainSet k s rs H x τl a := by
    intro a b hab
    by_cases hb : b.val ≤ τl
    · left
      intro j hj
      simp only [chainSet, mem_filter, mem_univ, true_and] at hj ⊢
      obtain ⟨d, hd, h1, h2, h3⟩ := hj
      exact ⟨d, hd, by omega, hb, h3⟩
    · right
      intro j hj
      simp only [chainSet, mem_filter, mem_univ, true_and] at hj
      obtain ⟨d, -, -, h2, -⟩ := hj
      omega
  rcases le_total τ.val τ'.val with h | h
  · exact key τ τ' h
  · exact (key τ' τ h).symm

/-- The merged count is at most the number of positions in their chain sets. -/
theorem mcnt_le_card
    (hclass : ∀ j H x, ∑ d ∈ range k,
      (rs j).countP (fun p => decide (p = (H, d, x))) ≤ 1) (H : Lane) (x : Class) (τl : ℕ) (σ : Equiv.Perm (Fin Δ)) :
    mcnt k s rs H x τl σ ≤ (univ.filter fun τ => σ τ ∈ chainSet k s rs H x τl τ).card := by
  unfold mcnt
  simp_rw [sum_filter]
  rw [sum_comm, card_filter]
  refine sum_le_sum fun τ _ => ?_
  have h := sum_ite_le_ite_exists (K := k) (fun d => τ.val ∈ Icc (τl - wsum s rs H d) τl)
    (fun d => acnt rs H d x (σ τ)) (hclass (σ τ) H x)
  refine h.trans (le_of_eq ?_)
  congr 1
  simp only [chainSet, mem_filter, mem_univ, true_and, mem_Icc]
  apply propext
  constructor
  · rintro ⟨d, hd, ⟨h1, h2⟩, h3⟩; exact ⟨d, hd, h1, h2, h3⟩
  · rintro ⟨d, hd, h1, h2, h3⟩; exact ⟨d, hd, ⟨h1, h2⟩, h3⟩

/-- The chain sets have total size at most `Mtot`. -/
theorem sum_card_chainSet_le (H : Lane) (x : Class) (τl : ℕ) :
    ∑ τ, (chainSet k s rs H x τl τ).card ≤ Mtot k s rs H x := by
  have h1 : ∀ τ : Fin Δ, (chainSet k s rs H x τl τ).card ≤
      ∑ j, ∑ d ∈ range k, (if τ.val ∈ Icc (τl - wsum s rs H d) τl then acnt rs H d x j else 0) := by
    intro τ
    rw [chainSet, card_filter]
    refine sum_le_sum fun j _ => ?_
    refine le_trans (le_of_eq ?_) (ite_exists_le_sum_ite (K := k)
      (fun d => τ.val ∈ Icc (τl - wsum s rs H d) τl) (fun d => acnt rs H d x j))
    congr 1
    simp only [mem_Icc]
    apply propext
    constructor
    · rintro ⟨d, hd, h1, h2, h3⟩; exact ⟨d, hd, ⟨h1, h2⟩, h3⟩
    · rintro ⟨d, hd, ⟨h1, h2⟩, h3⟩; exact ⟨d, hd, h1, h2, h3⟩
  have h2 : ∑ τ : Fin Δ, ∑ j, ∑ d ∈ range k,
      (if τ.val ∈ Icc (τl - wsum s rs H d) τl then acnt rs H d x j else 0) =
      ∑ d ∈ range k, ∑ τ : Fin Δ,
        (if τ.val ∈ Icc (τl - wsum s rs H d) τl then Atot rs H d x else 0) := by
    rw [sum_congr rfl fun τ _ => sum_comm, sum_comm]
    refine sum_congr rfl fun d _ => sum_congr rfl fun τ _ => ?_
    split_ifs <;> simp [Atot]
  refine (sum_le_sum fun τ _ => h1 τ).trans (h2.trans_le (sum_le_sum fun d _ => ?_))
  rw [← sum_filter, sum_const, smul_eq_mul, mul_comm]
  have hw : (univ.filter fun τ : Fin Δ => τ.val ∈ Icc (τl - wsum s rs H d) τl).card ≤
      wsum s rs H d + 1 := by
    rw [card_fin_filter_mem]
    exact (card_filter_le _ _).trans (by rw [Nat.card_Icc]; omega)
  exact Nat.mul_le_mul_left _ hw

theorem card_badB
    (hclass : ∀ j H x, ∑ d ∈ range k,
      (rs j).countP (fun p => decide (p = (H, d, x))) ≤ 1) (n : ℕ) (H : Lane) (x : Class) (τl : Fin Δ) :
    (badB k s rs n H x τl).card * 2 ^ lamN n ≤ Δ.factorial := by
  have hΔ : 0 < Δ := Nat.lt_of_le_of_lt (Nat.zero_le _) τl.isLt
  have hΔR : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  have hcard : Fintype.card (Fin Δ) = Δ := Fintype.card_fin Δ
  obtain ⟨A, hA⟩ : ∃ A, A = chainSet k s rs H x τl.val := ⟨_, rfl⟩
  have hch := card_upper_tail_chain (univ : Finset (Fin Δ)) A
    (hA ▸ chainSet_chain k s rs H x τl.val) (15 * lamN n) (by rw [hcard]; exact hΔ)
  rw [hcard] at hch
  have hμN : ∑ τ, (A τ).card ≤ Mtot k s rs H x := hA ▸ sum_card_chainSet_le k s rs H x τl.val
  have hμ : (∑ τ, ((A τ).card : ℝ)) ≤ Mtot k s rs H x := by exact_mod_cast hμN
  have hsub : badB k s rs n H x τl ⊆ univ.filter fun σ : Equiv.Perm (Fin Δ) =>
      41 / 40 * ((∑ τ, ((A τ).card : ℝ)) / Δ) + ((15 * lamN n : ℕ) : ℝ) ≤
        ((univ.filter fun τ => σ τ ∈ A τ).card : ℝ) := by
    intro σ hσ
    simp only [badB, mem_filter, mem_univ, true_and] at hσ ⊢
    have hm : mcnt k s rs H x τl.val σ ≤ (univ.filter fun τ => σ τ ∈ A τ).card :=
      hA ▸ mcnt_le_card k s rs hclass H x τl.val σ
    by_cases hM : Mtot k s rs H x = 0
    · rw [Nbx, if_pos hM] at hσ
      have h0 : ∑ τ, (A τ).card = 0 := by omega
      have : (univ.filter fun τ => σ τ ∈ A τ).card = 0 := by
        rw [card_eq_zero, filter_eq_empty_iff]
        intro τ _ hτ
        have := (sum_eq_zero_iff.mp h0) τ (mem_univ _)
        rw [card_eq_zero] at this
        rw [this] at hτ; simp at hτ
      omega
    · rw [Nbx, if_neg hM] at hσ
      have h1 : ((41 * Mtot k s rs H x / (40 * Δ) : ℕ) : ℝ) + ((15 * lamN n : ℕ) : ℝ) + 1 ≤
          ((univ.filter fun τ => σ τ ∈ A τ).card : ℝ) := by exact_mod_cast (by omega :
            41 * Mtot k s rs H x / (40 * Δ) + 15 * lamN n + 1 ≤
              (univ.filter fun τ => σ τ ∈ A τ).card)
      have h2 := nat_div_add_one_gt (41 * Mtot k s rs H x) (40 * Δ) (by omega)
      have h3 : 41 / 40 * ((∑ τ, ((A τ).card : ℝ)) / Δ) ≤
          ((41 * Mtot k s rs H x : ℕ) : ℝ) / ((40 * Δ : ℕ) : ℝ) := by
        push_cast
        rw [show (41 : ℝ) / 40 * ((∑ τ, ((A τ).card : ℝ)) / Δ) =
          41 * (∑ τ, ((A τ).card : ℝ)) / (40 * Δ) by field_simp]
        rw [div_le_div_iff_of_pos_right (by positivity)]
        linarith
      linarith
  have h2 : (2 : ℝ) ^ lamN n ≤ (21 / 20) ^ (15 * lamN n) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hfin : ((badB k s rs n H x τl).card : ℝ) * 2 ^ lamN n ≤ Δ.factorial :=
    (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)).trans
      ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card hsub)) (by positivity)).trans
        hch)
  exact_mod_cast hfin

/-- The window properties (A) and (B), for times as natural numbers. -/
structure GoodOrder (n : ℕ) (σ : Equiv.Perm (Fin Δ)) : Prop where
  A : ∀ H d, d < k → ∀ τ0, τ0 + win s rs H d < Δ → s ≤
    ∑ τ ∈ Ioc τ0 (τ0 + win s rs H d),
      (rnd rs σ τ).countP (fun p => decide (p.1 = H ∧ d ≤ p.2.1))
  B : ∀ H x τl, τl < Δ →
    ∑ d ∈ range k, ∑ τ ∈ Icc (τl - wsum s rs H d) τl,
      (rnd rs σ τ).countP (fun p => decide (p = (H, d, x))) ≤ Nbx k s rs n H x

theorem goodOrder_of_not_bad (n : ℕ) (σ : Equiv.Perm (Fin Δ))
    (hA : ∀ H (d : Fin k) τ0, σ ∉ badA s rs H d τ0)
    (hB : ∀ H x τl, σ ∉ badB k s rs n H x τl) : GoodOrder k s rs n σ := by
  constructor
  · intro H d hd τ0 hfit
    rw [sum_rnd rs σ _ (fun l => l.countP (fun p => decide (p.1 = H ∧ d ≤ p.2.1))) rfl]
    have := hA H ⟨d, hd⟩ ⟨τ0, by omega⟩
    simp only [badA, mem_filter, mem_univ, true_and, not_and, not_lt] at this
    exact this hfit
  · intro H x τl hτl
    have e : ∀ d, ∑ τ ∈ Icc (τl - wsum s rs H d) τl,
        (rnd rs σ τ).countP (fun p => decide (p = (H, d, x))) =
          ∑ τ ∈ univ.filter (fun τ : Fin Δ => τ.val ∈ Icc (τl - wsum s rs H d) τl),
            acnt rs H d x (σ τ) := fun d =>
      sum_rnd rs σ _ (fun l => l.countP (fun p => decide (p = (H, d, x)))) rfl
    simp_rw [e]
    have := hB H x ⟨τl, hτl⟩
    simp only [badB, mem_filter, mem_univ, true_and, not_lt] at this
    exact this

/-- Union bound: some order avoids every bad event. -/
theorem exists_goodOrder
    (hbatch : ∀ j H (Q : Lane × ℕ × Class → Prop) [DecidablePred Q],
      (rs j).countP (fun p => decide (p.1 = H ∧ Q p)) ≤ k)
    (hclass : ∀ j H x, ∑ d ∈ range k,
      (rs j).countP (fun p => decide (p = (H, d, x))) ≤ 1) (n : ℕ) (hk : 0 < k) {la : ℕ} (hlam : 76 * k * la ≤ 5 * s)
    (hcA : 2 * Fintype.card (Lane × Fin k × Fin Δ) ≤ 2 ^ la)
    (hcB : 2 * Fintype.card (Lane × Class × Fin Δ) < 2 ^ lamN n) :
    ∃ σ, GoodOrder k s rs n σ := by
  set BadA : Finset (Equiv.Perm (Fin Δ)) :=
    (univ : Finset (Lane × Fin k × Fin Δ)).biUnion (fun e => badA s rs e.1 e.2.1 e.2.2)
  set BadB : Finset (Equiv.Perm (Fin Δ)) :=
    (univ : Finset (Lane × Class × Fin Δ)).biUnion (fun e => badB k s rs n e.1 e.2.1 e.2.2)
  have hf : 0 < Δ.factorial := Nat.factorial_pos Δ
  have hA : 2 * BadA.card ≤ Δ.factorial := by
    have h1 : BadA.card * 2 ^ la ≤ Fintype.card (Lane × Fin k × Fin Δ) * Δ.factorial := by
      calc BadA.card * 2 ^ la
          ≤ (∑ e : Lane × Fin k × Fin Δ, (badA s rs e.1 e.2.1 e.2.2).card) * 2 ^ la :=
            Nat.mul_le_mul_right _ card_biUnion_le
        _ = ∑ e : Lane × Fin k × Fin Δ, (badA s rs e.1 e.2.1 e.2.2).card * 2 ^ la := sum_mul ..
        _ ≤ ∑ _e : Lane × Fin k × Fin Δ, Δ.factorial :=
            sum_le_sum fun e _ => card_badA k s rs hbatch hk hlam _ _ _
        _ = _ := by simp
    have h2 := Nat.mul_le_mul_right Δ.factorial hcA
    have h3 : 2 * BadA.card * 2 ^ la ≤ 2 ^ la * Δ.factorial := by nlinarith
    rw [mul_comm (2 ^ la)] at h3
    exact Nat.le_of_mul_le_mul_right h3 (by positivity)
  have hB : 2 * BadB.card < Δ.factorial := by
    have h1 : BadB.card * 2 ^ lamN n ≤ Fintype.card (Lane × Class × Fin Δ) * Δ.factorial := by
      calc BadB.card * 2 ^ lamN n
          ≤ (∑ e : Lane × Class × Fin Δ, (badB k s rs n e.1 e.2.1 e.2.2).card) * 2 ^ lamN n :=
            Nat.mul_le_mul_right _ card_biUnion_le
        _ = ∑ e : Lane × Class × Fin Δ, (badB k s rs n e.1 e.2.1 e.2.2).card * 2 ^ lamN n :=
            sum_mul ..
        _ ≤ ∑ _e : Lane × Class × Fin Δ, Δ.factorial :=
            sum_le_sum fun e _ => card_badB k s rs hclass n _ _ _
        _ = _ := by simp
    have h2 := Nat.mul_lt_mul_of_pos_right hcB hf
    have h3 : 2 * BadB.card * 2 ^ lamN n < 2 ^ lamN n * Δ.factorial := by nlinarith
    rw [mul_comm (2 ^ lamN n)] at h3
    exact Nat.lt_of_mul_lt_mul_right h3
  have hlt : (BadA ∪ BadB).card < (univ : Finset (Equiv.Perm (Fin Δ))).card := by
    rw [card_univ, Fintype.card_perm, Fintype.card_fin]
    have := card_union_le BadA BadB
    omega
  obtain ⟨σ, -, hσ⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨σ, goodOrder_of_not_bad k s rs n σ ?_ ?_⟩
  · intro H d τ0 h
    exact hσ (mem_union_left _ (mem_biUnion.mpr ⟨(H, d, τ0), mem_univ _, h⟩))
  · intro H x τl h
    exact hσ (mem_union_right _ (mem_biUnion.mpr ⟨(H, x, τl), mem_univ _, h⟩))


end SlidingPuzzle.GroupedOrder

namespace SlidingPuzzle.GroupedOrder
open Finset SlidingPuzzle.Hub
variable {Lane Class : Type*} [Fintype Lane] [DecidableEq Lane]
  [Fintype Class] [DecidableEq Class]


variable {Δ : ℕ} (k s : ℕ) (rs : Fin Δ → List (Lane × ℕ × Class))

/-- `G_d`: all insertions into `H` from distance `d`. -/
noncomputable def Gtot (H : Lane) (d : ℕ) : ℕ := ∑ j, gdist rs H d j

theorem Btot_eq_sum
    (htail : ∀ j H d, (rs j).countP (fun p => decide (p.1 = H ∧ d ≤ p.2.1)) =
      ∑ d' ∈ Ico d k, (rs j).countP (fun p => decide (p.1 = H ∧ p.2.1 = d'))) (H : Lane) (d : ℕ) : Btot rs H d = ∑ d' ∈ Ico d k, Gtot rs H d' := by
  unfold Btot Gtot gcnt gdist
  simp_rw [htail]
  exact sum_comm

theorem Gtot_le_Btot (H : Lane) (d : ℕ) : Gtot rs H d ≤ Btot rs H d := by
  unfold Btot Gtot gcnt gdist
  apply sum_le_sum; intro j _
  apply List.countP_mono_left
  intro p _ hp
  simp only [decide_eq_true_eq] at hp ⊢
  exact ⟨hp.1, hp.2.ge⟩

theorem Btot_le
    (hbatch : ∀ j H (Q : Lane × ℕ × Class → Prop) [DecidablePred Q],
      (rs j).countP (fun p => decide (p.1 = H ∧ Q p)) ≤ k) (H : Lane) (d : ℕ) : Btot rs H d ≤ k * Δ := by
  unfold Btot
  calc ∑ j, gcnt rs H d j ≤ ∑ _j : Fin Δ, k := sum_le_sum fun j _ =>
        hbatch j H (fun p => d ≤ p.2.1)
    _ = k * Δ := by simp [mul_comm]

theorem sum_Atot
    (hclasssum : ∀ j H d, ∑ x : Class, (rs j).countP (fun p => decide (p = (H, d, x))) =
      (rs j).countP (fun p => decide (p.1 = H ∧ p.2.1 = d))) (H : Lane) (d : ℕ) : ∑ x, Atot rs H d x = Gtot rs H d := by
  unfold Atot Gtot acnt gdist
  rw [sum_comm]
  exact sum_congr rfl fun j _ => hclasssum j H d

theorem sum_x_Nbx_le
    (hclasssum : ∀ j H d, ∑ x : Class, (rs j).countP (fun p => decide (p = (H, d, x))) =
      (rs j).countP (fun p => decide (p.1 = H ∧ p.2.1 = d)))
    (n : ℕ) (H : Lane) (C : ℕ)
    (hclasses : (univ.filter fun x => Mtot k s rs H x ≠ 0).card ≤ C) :
    ∑ x, (Nbx k s rs n H x : ℝ) ≤
      ∑ d ∈ range k, 41 * (Gtot rs H d : ℝ) * (wsum s rs H d + 1) / (40 * Δ) +
        C * (15 * lamN n) := by
  have h1 : ∀ x, (Nbx k s rs n H x : ℝ) ≤ 41 * (Mtot k s rs H x : ℝ) / (40 * Δ) +
      (if Mtot k s rs H x ≠ 0 then ((15 * lamN n : ℕ) : ℝ) else 0) := by
    intro x
    unfold Nbx
    by_cases h : Mtot k s rs H x = 0
    · rw [if_pos h, if_neg (not_not.mpr h)]; simp only [Nat.cast_zero, add_zero]; positivity
    · rw [if_neg h, if_pos h]
      have := Nat.cast_div_le (α := ℝ) (m := 41 * Mtot k s rs H x) (n := 40 * Δ)
      push_cast at this ⊢
      linarith
  have h2 : ∑ x : Class, (if Mtot k s rs H x ≠ 0 then ((15 * lamN n : ℕ) : ℝ) else 0) ≤
      C * ((15 * lamN n : ℕ) : ℝ) := by
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast hclasses
  have h3 : ∑ x, 41 * (Mtot k s rs H x : ℝ) / (40 * Δ) =
      ∑ d ∈ range k, 41 * (Gtot rs H d : ℝ) * (wsum s rs H d + 1) / (40 * Δ) := by
    rw [← sum_div, ← sum_div, ← mul_sum]
    congr 1
    simp only [Mtot]
    push_cast
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun d _ => ?_
    rw [← sum_mul, ← mul_assoc]
    congr 2
    rw [← sum_Atot rs hclasssum]; push_cast; rfl
  calc ∑ x, (Nbx k s rs n H x : ℝ)
      ≤ ∑ x, (41 * (Mtot k s rs H x : ℝ) / (40 * Δ) +
          (if Mtot k s rs H x ≠ 0 then ((15 * lamN n : ℕ) : ℝ) else 0)) := sum_le_sum fun x _ => h1 x
    _ ≤ _ := by rw [sum_add_distrib, h3]; push_cast at h2 ⊢; linarith

/-- The residence window against the tail rates: `G_d (W_d + 1) ≤
(4sΔ/3) G_d ∑_{j ≤ d} 1/B_j + (d + 2) G_d`. -/
theorem Gtot_mul_wsum_le
    (hdk : ∀ j, ∀ p ∈ rs j, p.2.1 < k)
    (htail : ∀ j H d, (rs j).countP (fun p => decide (p.1 = H ∧ d ≤ p.2.1)) =
      ∑ d' ∈ Ico d k, (rs j).countP (fun p => decide (p.1 = H ∧ p.2.1 = d'))) (H : Lane) (d : ℕ) :
    (Gtot rs H d : ℝ) * (wsum s rs H d + 1) ≤
      4 * s * Δ / 3 * ((Gtot rs H d : ℝ) *
        ∑ j ∈ range (d + 1), ((∑ d' ∈ Ico j k, Gtot rs H d' : ℕ) : ℝ)⁻¹) +
      (d + 2) * (Gtot rs H d : ℝ) := by
  by_cases hG0 : Gtot rs H d = 0
  · rw [hG0]; simp
  obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero hG0
  obtain ⟨p, hp, hpH⟩ := List.countP_pos_iff.mp (Nat.pos_of_ne_zero hi)
  simp only [decide_eq_true_eq] at hpH
  have hdk : d < k := hpH.2 ▸ hdk i p hp
  have hΔ : 0 < Δ := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hΔR : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  have hGR : (0 : ℝ) ≤ Gtot rs H d := Nat.cast_nonneg _
  -- every band `j ≤ d` has positive tail rate
  have hwin : ∀ j ∈ range (d + 1), (win s rs H j : ℝ) ≤
      4 * s * Δ / 3 * ((∑ d' ∈ Ico j k, Gtot rs H d' : ℕ) : ℝ)⁻¹ + 1 := by
    intro j hj
    have hjd := mem_range.mp hj
    have hGB : Gtot rs H d ≤ Btot rs H j := by
      rw [Btot_eq_sum k rs htail]
      exact single_le_sum (f := Gtot rs H) (fun _ _ => Nat.zero_le _)
        (mem_Ico.mpr ⟨by omega, hdk⟩)
    have hB0 : Btot rs H j ≠ 0 := by omega
    have hBR : (0 : ℝ) < Btot rs H j := by exact_mod_cast Nat.pos_of_ne_zero hB0
    have hle : win s rs H j ≤ 4 * s * Δ / (3 * Btot rs H j) + 1 := by
      rw [win, if_neg hB0]; exact min_le_right _ _
    have e2 := Nat.cast_div_le (α := ℝ) (m := 4 * s * Δ) (n := 3 * Btot rs H j)
    rw [← Btot_eq_sum k rs htail]
    have : (win s rs H j : ℝ) ≤ ((4 * s * Δ / (3 * Btot rs H j) : ℕ) : ℝ) + 1 := by
      exact_mod_cast hle
    have e3 : ((4 * s * Δ : ℕ) : ℝ) / ((3 * Btot rs H j : ℕ) : ℝ) =
        4 * s * Δ / 3 * ((Btot rs H j : ℕ) : ℝ)⁻¹ := by
      push_cast; field_simp
    linarith
  have hsum : (wsum s rs H d : ℝ) ≤ 4 * s * Δ / 3 *
      ∑ j ∈ range (d + 1), ((∑ d' ∈ Ico j k, Gtot rs H d' : ℕ) : ℝ)⁻¹ + (d + 1) := by
    unfold wsum
    push_cast
    calc ∑ j ∈ range (d + 1), (win s rs H j : ℝ)
        ≤ ∑ j ∈ range (d + 1), (4 * s * Δ / 3 * ((∑ d' ∈ Ico j k, Gtot rs H d' : ℕ) : ℝ)⁻¹ + 1) :=
          sum_le_sum hwin
      _ = _ := by rw [sum_add_distrib, ← mul_sum]; simp
  have := mul_le_mul_of_nonneg_left (add_le_add_right hsum 1) hGR
  nlinarith

theorem sum_lane_le
    (hdk : ∀ j, ∀ p ∈ rs j, p.2.1 < k)
    (htail : ∀ j H d, (rs j).countP (fun p => decide (p.1 = H ∧ d ≤ p.2.1)) =
      ∑ d' ∈ Ico d k, (rs j).countP (fun p => decide (p.1 = H ∧ p.2.1 = d')))
    (hbatch : ∀ j H (Q : Lane × ℕ × Class → Prop) [DecidablePred Q],
      (rs j).countP (fun p => decide (p.1 = H ∧ Q p)) ≤ k)
    (hclasssum : ∀ j H d, ∑ x : Class, (rs j).countP (fun p => decide (p = (H, d, x))) =
      (rs j).countP (fun p => decide (p.1 = H ∧ p.2.1 = d)))
    (n : ℕ) (H : Lane) (r C : ℕ)
    (hclasses : (univ.filter fun x => Mtot k s rs H x ≠ 0).card ≤ C)
    (hbands : ((range k).filter fun j => Btot rs H j ≠ 0).card ≤ r)
    (hsupport : ∀ d, Gtot rs H d ≠ 0 → d < r) :
    ∑ x, (Nbx k s rs n H x : ℝ) ≤
      41 / 30 * (r * s) + 41 / 40 * (k * (r + 1)) + C * (15 * lamN n) := by
  refine (sum_x_Nbx_le k s rs hclasssum n H C hclasses).trans ?_
  rcases Nat.eq_zero_or_pos Δ with hΔ0 | hΔ
  · subst hΔ0
    simp only [Nat.cast_zero, mul_zero, div_zero, sum_const_zero, zero_add]
    have : (0 : ℝ) ≤ 41 / 30 * (r * s) + 41 / 40 * (k * (r + 1)) := by positivity
    linarith
  have hΔR : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  
  -- the telescoping sum
  have htel := sum_mul_sum_inv_le k (Gtot rs H)
  have hband := Nat.mul_le_mul_right s hbands
  simp_rw [← Btot_eq_sum k rs htail] at htel
  have hbandR : ((((range k).filter fun j => Btot rs H j ≠ 0).card : ℕ) : ℝ) * s ≤
      r * s := by exact_mod_cast hband
  have hGsum : ∑ d ∈ range k, (Gtot rs H d : ℝ) ≤ k * Δ := by
    have := Btot_le k rs hbatch H 0
    rw [Btot_eq_sum k rs htail, ← range_eq_Ico] at this; exact_mod_cast this
  have hterm : ∀ d ∈ range k, 41 * (Gtot rs H d : ℝ) * (wsum s rs H d + 1) / (40 * Δ) ≤
      41 / 40 * (4 * s / 3 * ((Gtot rs H d : ℝ) *
        ∑ j ∈ range (d + 1), ((Btot rs H j : ℕ) : ℝ)⁻¹)) +
      41 / 40 * ((r + 1) * (Gtot rs H d : ℝ) / Δ) := by
    intro d hd
    by_cases hzero : Gtot rs H d = 0
    · simp [hzero]
    have hdr := hsupport d hzero
    have hdist := mem_range.mp hd
    have h := Gtot_mul_wsum_le k s rs hdk htail H d
    simp_rw [← Btot_eq_sum k rs htail] at h
    have hGR : (0 : ℝ) ≤ Gtot rs H d := Nat.cast_nonneg _
    have hd2 : ((d : ℝ) + 2) * (Gtot rs H d : ℝ) ≤ ((r : ℝ) + 1) * (Gtot rs H d) := by
      have : (d : ℝ) + 2 ≤ r + 1 := by
        have : (d : ℝ) + 1 ≤ r := by exact_mod_cast hdr
        linarith
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    have e : (41 / 40 * (4 * (s : ℝ) / 3 * ((Gtot rs H d : ℝ) *
        ∑ j ∈ range (d + 1), ((Btot rs H j : ℕ) : ℝ)⁻¹)) +
        41 / 40 * ((r + 1) * (Gtot rs H d : ℝ) / Δ)) * (40 * Δ) =
        41 * (4 * s * Δ / 3 * ((Gtot rs H d : ℝ) *
          ∑ j ∈ range (d + 1), ((Btot rs H j : ℕ) : ℝ)⁻¹) + ((r : ℝ) + 1) * Gtot rs H d) := by
      field_simp
    rw [e]
    nlinarith
  refine (add_le_add (sum_le_sum hterm) le_rfl).trans ?_
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
  have h1 : 4 * (s : ℝ) / 3 * ∑ d ∈ range k, ((Gtot rs H d : ℝ) *
      ∑ j ∈ range (d + 1), ((Btot rs H j : ℕ) : ℝ)⁻¹) ≤ 4 / 3 * (r * s) := by
    have := mul_le_mul_of_nonneg_left htel (show (0 : ℝ) ≤ 4 * s / 3 by positivity)
    nlinarith
  have h2 : ∑ d ∈ range k, ((r : ℝ) + 1) * (Gtot rs H d : ℝ) / Δ ≤ k * (r + 1) := by
    rw [← sum_div, ← mul_sum, div_le_iff₀ hΔR]
    have : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    nlinarith
  nlinarith


end SlidingPuzzle.GroupedOrder

namespace SlidingPuzzle.GroupedOrder
open Finset SlidingPuzzle.Hub
variable {Lane Class : Type*} [Fintype Lane] [DecidableEq Lane]
  [Fintype Class] [DecidableEq Class]

/-- Summing disjoint exact class counts recovers the lane/distance count. -/
theorem list_count_class (L : List (Lane × ℕ × Class)) (H : Lane) (d : ℕ) :
    ∑ x : Class, L.countP (fun p => decide (p = (H, d, x))) =
      L.countP (fun p => decide (p.1 = H ∧ p.2.1 = d)) := by
  induction L with
  | nil => simp
  | cons p L ih =>
    rcases p with ⟨H', d', x'⟩
    simp [Prod.ext_iff] at ih
    by_cases hH : H' = H <;> by_cases hd : d' = d
    all_goals simp [List.countP_cons, Prod.ext_iff, hH, hd, sum_add_distrib, ih]

/-- Splitting a tail count over its distance bands. -/
theorem list_count_tail (k : ℕ) (L : List (Lane × ℕ × Class))
    (hdk : ∀ p ∈ L, p.2.1 < k) (H : Lane) (d : ℕ) :
    L.countP (fun p => decide (p.1 = H ∧ d ≤ p.2.1)) =
      ∑ d' ∈ Ico d k, L.countP (fun p => decide (p.1 = H ∧ p.2.1 = d')) := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have hp := hdk p (by simp)
    have ht : ∀ p ∈ L, p.2.1 < k := fun p h => hdk p (by simp [h])
    rw [List.countP_cons]
    simp_rw [List.countP_cons]
    rw [sum_add_distrib, ih ht]
    rcases p with ⟨H', d', x'⟩
    by_cases hH : H' = H
    · simp only [hH, true_and]
      simp [eq_comm, mem_Ico, hp]
    · simp [hH]

end SlidingPuzzle.GroupedOrder

namespace SlidingPuzzle.GroupedOrder
open Finset SlidingPuzzle.Hub
variable {Lane Class : Type*} [Fintype Lane] [DecidableEq Lane]
  [Fintype Class] [DecidableEq Class]
variable {Δ : ℕ} (k s : ℕ) (rs : Fin Δ → List (Lane × ℕ × Class))

/-- Local geometric and class supports yield the three support facts needed
by the rate-weighted sum. No hypothesis about residence counts is used. -/
theorem local_support_bounds (r : Lane → ℕ) (X : Lane → Finset Class)
    (hsupp : ∀ j, ∀ p ∈ rs j, p.2.1 < r p.1 ∧ p.2.2 ∈ X p.1) (H : Lane) :
    (univ.filter fun x => Mtot k s rs H x ≠ 0).card ≤ (X H).card ∧
    ((range k).filter fun j => Btot rs H j ≠ 0).card ≤ r H ∧
    (∀ d, Gtot rs H d ≠ 0 → d < r H) := by
  constructor
  · apply card_le_card
    intro x hx
    have hx0 := (mem_filter.mp hx).2
    obtain ⟨d, _, hd⟩ := exists_ne_zero_of_sum_ne_zero hx0
    have hA : Atot rs H d x ≠ 0 := by
      intro h0
      exact hd (by simp [h0])
    obtain ⟨j, _, hj⟩ := exists_ne_zero_of_sum_ne_zero hA
    obtain ⟨p, hp, he⟩ := List.countP_pos_iff.mp (Nat.pos_of_ne_zero hj)
    simp only [decide_eq_true_eq] at he
    subst p
    exact (hsupp j (H, d, x) hp).2
  constructor
  · have hsub : (range k).filter (fun j => Btot rs H j ≠ 0) ⊆ range (r H) := by
      intro d hd
      obtain ⟨j, _, hj⟩ := exists_ne_zero_of_sum_ne_zero (mem_filter.mp hd).2
      obtain ⟨p, hp, he⟩ := List.countP_pos_iff.mp (Nat.pos_of_ne_zero hj)
      simp only [decide_eq_true_eq] at he
      have ht := (hsupp j p hp).1
      rw [he.1] at ht
      exact mem_range.mpr (lt_of_le_of_lt he.2 ht)
    exact (card_le_card hsub).trans_eq (card_range _)
  · intro d hd
    obtain ⟨j, _, hj⟩ := exists_ne_zero_of_sum_ne_zero hd
    obtain ⟨p, hp, he⟩ := List.countP_pos_iff.mp (Nat.pos_of_ne_zero hj)
    simp only [decide_eq_true_eq] at he
    have ht := (hsupp j p hp).1
    rwa [he.1, he.2] at ht

/-- Uniform per-lane budget using only traffic and support assumptions. -/
theorem lane_budget (n : ℕ) (r : Lane → ℕ) (X : Lane → Finset Class)
    (hdk : ∀ j, ∀ p ∈ rs j, p.2.1 < k)
    (hsupp : ∀ j, ∀ p ∈ rs j, p.2.1 < r p.1 ∧ p.2.2 ∈ X p.1)
    (hbatch : ∀ j H (Q : Lane × ℕ × Class → Prop) [DecidablePred Q],
      (rs j).countP (fun p => decide (p.1 = H ∧ Q p)) ≤ k) (H : Lane) :
    ∑ x, (Nbx k s rs n H x : ℝ) ≤
      41 / 30 * (r H * s) + 41 / 40 * (k * (r H + 1)) +
        (X H).card * (15 * lamN n) := by
  obtain ⟨hc, hb, hd⟩ := local_support_bounds k s rs r X hsupp H
  exact sum_lane_le k s rs hdk (fun j H d => list_count_tail k (rs j) (hdk j) H d)
    hbatch (fun j H d => list_count_class (rs j) H d) n H (r H) (X H).card hc hb hd

/-- A common round order works for every consistent execution trace and every
prefix of it. The statistics never depend on clean versus dirty tile identity.
This is an abstract pipe theorem, not a physical puzzle path theorem. -/
theorem exists_uniform_residence (n : ℕ) (offset : Lane → ℕ)
    (hoff : ∀ H, offset H < s) (r : Lane → ℕ) (X : Lane → Finset Class)
    (hk : 0 < k)
    (hdk : ∀ j, ∀ p ∈ rs j, p.2.1 < k)
    (hsupp : ∀ j, ∀ p ∈ rs j, p.2.1 < r p.1 ∧ p.2.2 ∈ X p.1)
    (hbatch : ∀ j H (Q : Lane × ℕ × Class → Prop) [DecidablePred Q],
      (rs j).countP (fun p => decide (p.1 = H ∧ Q p)) ≤ k)
    (hclass : ∀ j H x, ∑ d ∈ range k,
      (rs j).countP (fun p => decide (p = (H, d, x))) ≤ 1)
    {la : ℕ} (hcap : 76 * k * la ≤ 5 * s)
    (hcA : 2 * Fintype.card (Lane × Fin k × Fin Δ) ≤ 2 ^ la)
    (hcB : 2 * Fintype.card (Lane × Class × Fin Δ) < 2 ^ lamN n) :
    ∃ σ : Equiv.Perm (Fin Δ),
      (∀ H, ∑ x, (Nbx k s rs n H x : ℝ) ≤
        41 / 30 * (r H * s) + 41 / 40 * (k * (r H + 1)) +
          (X H).card * (15 * lamN n)) ∧
      ∀ (L : List (GroupedPipe.InsRec Lane Class)) (_r0 : GroupedPipe.InsRec Lane Class),
        L.Pairwise (fun a b => a.τ ≤ b.τ) → (∀ e ∈ L, e.τ < Δ) →
        (∀ τ, ((L.filter fun e => e.τ = τ).map GroupedPipe.proj).Perm (rnd rs σ τ)) →
        ∀ m, m ≤ L.length → ∀ H x len,
          ((range len).filter fun q =>
            (GroupedPipe.ghostRun s offset (fun _ _ => none) (L.take m) H q).map Prod.fst = some x).card ≤
            Nbx k s rs n H x := by
  obtain ⟨σ, hσ⟩ := exists_goodOrder k s rs hbatch hclass n hk hcap hcA hcB
  refine ⟨σ, lane_budget k s rs n r X hdk hsupp hbatch, ?_⟩
  intro L r0 hsort hlt hperm m hm H x len
  apply GroupedPipe.ghost_count_le s offset hoff r0 (win s rs) (Nbx k s rs n)
    hsort hlt hperm ?_ hσ.A hσ.B hm
  intro τ p hp
  obtain ⟨j, hj⟩ := mem_rnd rs hp
  exact hdk j p hj

end SlidingPuzzle.GroupedOrder
