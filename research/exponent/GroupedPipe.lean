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
