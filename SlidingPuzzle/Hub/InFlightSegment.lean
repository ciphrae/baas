import SlidingPuzzle.Hub.InFlightWindow

/-! # Segmented residence

A tile at position at most `B` of a half moves one step toward the head with
every later insertion into that half at a position `≥ B` (`seg_bound`). Since
the insertion positions of consecutive distances differ by `s`, a tile inserted
from distance `d` has left band `j` after `s` insertions from distances `≥ j`,
and has left the half after `s` insertions from distances `≥ 0`. If every
window of `w j` rounds holds `s` insertions from distances `≥ j`, the tile is
therefore gone `w d + w (d-1) + ... + w 0` rounds after its insertion
(`last_le_of_segments`). Summed against the insertion rates, these residence
times telescope; this removes the harmonic factor of the fixed-distance
estimate in `InFlightWindow.lean`. -/
namespace SlidingPuzzle.Hub

open Finset

variable {k : ℕ} (s : ℕ)

/-- Consecutive insertion bands are one square width apart. -/
theorem insPos_sub_prev (k s : ℕ) (H : RowH k) (hs : k + 1 ≤ s) {j : ℕ} (hj : 0 < j) :
    insPos k s H j = insPos k s H (j - 1) + s := by
  have hj' : j - 1 + 1 = j := by omega
  have hmul : (j + 1) * s = j * s + s := by ring
  have hprod : k + 1 ≤ j * s := le_trans hs (Nat.le_mul_of_pos_left s hj)
  unfold insPos
  split <;> rw [hmul, hj'] <;> omega

/-- The lowest band lies within one square width of the head. -/
theorem insPos_zero_lt (k s : ℕ) (H : RowH k) (hs : k + 1 ≤ s) : insPos k s H 0 < s := by
  unfold insPos; split <;> omega

/-- Insertions with index in `[t, m)` into `H` at a position `≥ B`. -/
def pushesAbove (e : ℕ → InsRec k) (H : RowH k) (B t m : ℕ) : ℕ :=
  ((Ico t m).filter fun l => (e l).H = H ∧ B ≤ insPos k s (e l).H (e l).d).card

theorem pushesAbove_succ (e : ℕ → InsRec k) (H : RowH k) (B t m : ℕ) (htm : t ≤ m) :
    pushesAbove s e H B t (m + 1) = pushesAbove s e H B t m +
      if (e m).H = H ∧ B ≤ insPos k s (e m).H (e m).d then 1 else 0 := by
  unfold pushesAbove
  rw [show m + 1 = m.succ from rfl, Nat.Ico_succ_right_eq_insert_Ico htm, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

theorem pushesAbove_mono (e : ℕ → InsRec k) (H : RowH k) (B t : ℕ) {m m' : ℕ} (h : m ≤ m') :
    pushesAbove s e H B t m ≤ pushesAbove s e H B t m' := by
  unfold pushesAbove
  apply card_le_card
  intro l; simp only [mem_filter, mem_Ico]; intro h'; exact ⟨⟨h'.1.1, by omega⟩, h'.2⟩

/-- **Segment lemma**: a tile at position `≤ B` at step `t` is moved toward the
head by each later insertion into its half at a position `≥ B`. -/
theorem seg_bound (e : ℕ → InsRec k) (H : RowH k) {i B t : ℕ} (hit : i < t)
    (h0 : ∀ q, irun s e t H q = some i → q ≤ B) :
    ∀ m, t ≤ m → ∀ q, irun s e m H q = some i → q + pushesAbove s e H B t m ≤ B := by
  intro m htm
  induction m, htm using Nat.le_induction with
  | base =>
    intro q hq
    have : pushesAbove s e H B t t = 0 := by simp [pushesAbove]
    rw [this]; simpa using h0 q hq
  | succ m htm ih =>
    intro q hq
    rw [pushesAbove_succ s e H B t m htm]
    simp only [irun, istep] at hq
    by_cases hH : H = (e m).H
    · subst hH
      rw [Function.update_self] at hq
      have hc : ∀ q', irun s e m (e m).H q' = some i → q' + pushesAbove s e (e m).H B t m ≤ B := ih
      by_cases hP : B ≤ insPos k s (e m).H (e m).d
      · rw [if_pos ⟨rfl, hP⟩]
        unfold shiftIn at hq
        by_cases h1 : q < insPos k s (e m).H (e m).d
        · rw [if_pos h1] at hq; have := hc _ hq; omega
        · rw [if_neg h1] at hq
          by_cases h2 : q = insPos k s (e m).H (e m).d
          · rw [if_pos h2] at hq; cases hq; omega
          · rw [if_neg h2] at hq; have := hc _ hq; omega
      · rw [if_neg (fun h => hP h.2)]
        unfold shiftIn at hq
        by_cases h1 : q < insPos k s (e m).H (e m).d
        · rw [if_pos h1] at hq; have := hc _ hq; omega
        · rw [if_neg h1] at hq
          by_cases h2 : q = insPos k s (e m).H (e m).d
          · rw [if_pos h2] at hq; cases hq; omega
          · rw [if_neg h2] at hq; have := hc _ hq; omega
    · rw [Function.update_of_ne hH] at hq
      have := ih _ hq
      rw [if_neg (fun h => hH h.1.symm)]
      omega

/-- The prefix of a sorted list up to the end of time `T`. -/
def upto (L : List (InsRec k)) (r0 : InsRec k) (T : ℕ) : ℕ :=
  ((range L.length).filter fun l => (L.getD l r0).τ ≤ T).card

section list

variable {L : List (InsRec k)} (r0 : InsRec k)

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
    {R : ℕ → List (RowH k × ℕ × Sq k)}
    (hperm : ∀ τ, ((L.filter fun r => r.τ = τ).map proj).Perm (R τ))
    (H : RowH k) (j T w : ℕ) :
    ∑ τ ∈ Ioc T (T + w), (R τ).countP (fun p => decide (p.1 = H ∧ j ≤ p.2.1)) ≤
      pushesAbove s (fun l => L.getD l r0) H (insPos k s H j) (upto L r0 T)
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
  · rw [hH]; exact insPos_mono s H hd

/-- **Residence lemma**: with the window property for every band `j ≤ d`, a
present tile inserted from distance `d` was inserted at most `∑_{j ≤ d} w j`
times before the last time of the prefix. -/
theorem last_le_of_segments {R : ℕ → List (RowH k × ℕ × Sq k)} {T : ℕ}
    (hsort : L.Pairwise fun a b => a.τ ≤ b.τ) (hlt : ∀ r ∈ L, r.τ < T)
    (hperm : ∀ τ, ((L.filter fun r => r.τ = τ).map proj).Perm (R τ))
    (w : ℕ → ℕ) (H : RowH k) (d : ℕ)
    (hgap : ∀ j, 0 < j → insPos k s H j = insPos k s H (j - 1) + s)
    (hzero : insPos k s H 0 < s)
    (hA : ∀ j ≤ d, ∀ τ0, τ0 + w j < T → s ≤
      ∑ τ ∈ Ioc τ0 (τ0 + w j), (R τ).countP (fun p => decide (p.1 = H ∧ j ≤ p.2.1)))
    {m i q : ℕ} (hm : m ≤ L.length) (him : i < m) (hd : (L.getD i r0).d = d)
    (hq : irun s (fun l => L.getD l r0) m H q = some i) :
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
  have hpush : ∀ j ≤ d, s ≤ pushesAbove s e H (insPos k s H j) (upto L r0 (S j))
      (upto L r0 (S j + w j)) :=
    fun j hj => (hA j hj (S j) (hfit j hj)).trans (sum_window_le_pushesAbove s r0 hsort hperm H j _ _)
  have hI := iinv s e (i + 1)
  have hstart : ∀ q', irun s e (i + 1) H q' = some i → q' ≤ insPos k s H d := by
    intro q' hq'
    obtain ⟨-, -, hb⟩ := hI.val _ _ _ hq'
    simp only [he] at hb
    rw [hd] at hb
    omega
  have hstage : ∀ r ≤ d, ∀ q', irun s e (upto L r0 (S (d - r))) H q' = some i →
      q' ≤ insPos k s H (d - r) := by
    intro r
    induction r with
    | zero =>
      intro _ q' hq'
      have := seg_bound s e H (by omega) hstart (upto L r0 (S d)) (by omega) q' hq'
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
      have := seg_bound s e H hlo (ih (by omega)) _ hmono q' hq'
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
  have hfinal := seg_bound s e H hlo h0 m hmono q hq
  have hp := hpush 0 (by omega)
  have hpm := pushesAbove_mono s e H (insPos k s H 0) (upto L r0 (S 0))
    (le_of_lt (hup_m 0 (by omega)))
  omega

end list

section main

variable {L : List (InsRec k)} (r0 : InsRec k) {R : ℕ → List (RowH k × ℕ × Sq k)} {T : ℕ}
  (w : RowH k → ℕ → ℕ) (Nb : RowH k → ℕ → Sq k → ℕ)

/-- Present class-`x` tiles of one half, for a prefix of length `m ≤ |L|`, with
the segmented residence windows `∑_{j ≤ d} w H j`. -/
theorem count_tagged_le_seg
    (hsort : L.Pairwise fun a b => a.τ ≤ b.τ) (hlt : ∀ r ∈ L, r.τ < T)
    (hperm : ∀ τ, ((L.filter fun r => r.τ = τ).map proj).Perm (R τ))
    (hdk : ∀ τ, ∀ p ∈ R τ, p.2.1 < k)
    (hgap : ∀ H j, 0 < j → insPos k s H j = insPos k s H (j - 1) + s)
    (hzero : ∀ H, insPos k s H 0 < s)
    (hA : ∀ H j, j < k → ∀ τ0, τ0 + w H j < T → s ≤
      ∑ τ ∈ Ioc τ0 (τ0 + w H j), (R τ).countP (fun p => decide (p.1 = H ∧ j ≤ p.2.1)))
    (hB : ∀ H d, d < k → ∀ x τ0, τ0 < T →
      ∑ τ ∈ Icc τ0 (τ0 + ∑ j ∈ range (d + 1), w H j),
        (R τ).countP (fun p => decide (p = (H, d, x))) ≤ Nb H d x)
    {m : ℕ} (hm : m ≤ L.length) (H : RowH k) (x : Sq k) (len : ℕ) :
    ((range len).filter fun q =>
        (irun s (fun i => L.getD i r0) m H q).map (fun i => (L.getD i r0).x) = some x).card ≤
      ∑ d ∈ range k, Nb H d x := by
  set e := fun i => L.getD i r0 with he
  have hI := iinv s e m
  -- present tiles inject into their insertions
  have hinj : ((range len).filter fun q => (irun s e m H q).map (fun i => (e i).x) = some x).card ≤
      ((range m).filter fun i => (e i).H = H ∧ (e i).x = x ∧
        ∃ q ∈ range len, irun s e m H q = some i).card := by
    refine card_le_card_of_injOn (fun q => (irun s e m H q).getD 0) ?_ ?_
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
      ∃ q ∈ range len, irun s e m H q = some i), (e i).d ∈ range k := by
    intro i hi
    simp only [mem_filter, mem_range] at hi
    exact mem_range.mpr (hdk _ _ (proj_mem r0 hperm (i := i) (by omega)))
  rw [card_eq_sum_card_fiberwise hmaps]
  apply sum_le_sum
  intro d hd
  have hdk' := mem_range.mp hd
  set τl := (L.getD (m - 1) r0).τ
  set W := ∑ j ∈ range (d + 1), w H j
  calc _ ≤ ((range L.length).filter fun i => (L.getD i r0).τ ∈ Icc (τl - W) (τl - W + W) ∧
        proj (L.getD i r0) = (H, d, x)).card := by
        apply card_le_card
        intro i hi
        simp only [mem_filter, mem_range] at hi
        obtain ⟨⟨him, hH, hx, q, -, hq⟩, hdi⟩ := hi
        have h1 := last_le_of_segments s r0 hsort hlt hperm (w H) H d (hgap H) (hzero H)
          (fun j hj => hA H j (by omega)) hm him hdi hq
        have h2 := tau_mono r0 hsort (j := i) (j' := m - 1) (by omega) (by omega)
        simp only [mem_filter, mem_range, mem_Icc, proj]
        refine ⟨by omega, ⟨by omega, by omega⟩, ?_⟩
        simp only [he] at hH hx hdi
        rw [hH, hdi, hx]
    _ = ∑ τ ∈ Icc (τl - W) (τl - W + W), ((range L.length).filter fun i =>
          (L.getD i r0).τ = τ ∧ proj (L.getD i r0) = (H, d, x)).card :=
        (sum_card_fiber _ _ _ _).symm
    _ = ∑ τ ∈ Icc (τl - W) (τl - W + W), (R τ).countP (fun p => decide (p = (H, d, x))) :=
        sum_congr rfl fun τ _ => card_time_filter r0 hperm τ (fun p => p = (H, d, x))
    _ ≤ Nb H d x := by
        apply hB H d hdk' x
        have hmem : L.getD (m - 1) r0 ∈ L := by
          rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
        have := hlt _ hmem
        omega

/-- **In-flight counts from the segmented window properties.** -/
theorem newCnt_le_of_segments (r0 : InsRec k)
    (hsort : L.Pairwise fun a b => a.τ ≤ b.τ) (hlt : ∀ r ∈ L, r.τ < T)
    (hperm : ∀ τ, ((L.filter fun r => r.τ = τ).map proj).Perm (R τ))
    (hdk : ∀ τ, ∀ p ∈ R τ, p.2.1 < k)
    (hgap : ∀ H j, 0 < j → insPos k s H j = insPos k s H (j - 1) + s)
    (hzero : ∀ H, insPos k s H 0 < s)
    (hA : ∀ H j, j < k → ∀ τ0, τ0 + w H j < T → s ≤
      ∑ τ ∈ Ioc τ0 (τ0 + w H j), (R τ).countP (fun p => decide (p.1 = H ∧ j ≤ p.2.1)))
    (hB : ∀ H d, d < k → ∀ x τ0, τ0 < T →
      ∑ τ ∈ Icc τ0 (τ0 + ∑ j ∈ range (d + 1), w H j),
        (R τ).countP (fun p => decide (p = (H, d, x))) ≤ Nb H d x)
    (m : ℕ) (h x : Sq k) :
    newCnt s (ghostRun s (fun _ _ => none) (L.take m)) h x ≤
      ∑ side : Bool, ∑ d ∈ range k, Nb (h.1, h.2, side) d x := by
  have htake : L.take m = L.take (min m L.length) := by
    rcases le_total m L.length with hml | hml
    · rw [min_eq_left hml]
    · rw [min_eq_right hml, List.take_of_length_le hml, List.take_length]
  rw [htake, ghostRun_take s L r0 _ (min_le_right _ _)]
  unfold newCnt
  apply sum_le_sum
  intro side _
  simp only [Option.map_map, Function.comp_def]
  exact count_tagged_le_seg s r0 w Nb hsort hlt hperm hdk hgap hzero hA hB
    (min_le_right _ _) _ x _

end main

end SlidingPuzzle.Hub
