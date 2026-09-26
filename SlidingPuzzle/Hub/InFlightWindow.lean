import SlidingPuzzle.Hub.InFlightPush

/-! # From window properties of the order to the in-flight counts

Deterministic part of the in-flight bound. The insertion list `L` is sorted by
time and, at each time `τ`, performs exactly the insertions `R τ` (in any order).
Suppose, for a half `H` and distance `d`:
* (A) every window `(τ0, τ0 + w]` ending before `T` contains more than
  `insPos H d` insertions into `H` from distances `≥ d`;
* (B) every window `[τ0, τ0 + w]` contains at most `Nb H d x` insertions of
  `(H, d, x)`.
Then a present class-`x` tile inserted from distance `d` was inserted within the
last `w + 1` times (by the push lemma and (A)), so at most `Nb H d x` of them are
present (by (B)): `newCnt_le_of_windows`. -/
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

/-- The pushes of an insertion include all insertions of the times strictly
between it and the end of the prefix. -/
theorem pushes_ge {L : List (InsRec k)} (r0 : InsRec k) {R : ℕ → List (RowH k × ℕ × Sq k)}
    (hsort : L.Pairwise fun a b => a.τ ≤ b.τ)
    (hperm : ∀ τ, ((L.filter fun r => r.τ = τ).map proj).Perm (R τ))
    {m i : ℕ} (hm : m ≤ L.length) (him : i < m) :
    ∑ τ ∈ Ioo (L.getD i r0).τ (L.getD (m - 1) r0).τ,
        (R τ).countP (fun p => decide (p.1 = (L.getD i r0).H ∧ (L.getD i r0).d ≤ p.2.1)) ≤
      pushes (fun j => L.getD j r0) i m := by
  set e := fun j => L.getD j r0 with he
  simp_rw [← card_time_filter r0 hperm]
  rw [sum_card_fiber]
  apply card_le_card
  intro j hj
  simp only [mem_filter, mem_range, mem_Ioo, proj] at hj ⊢
  obtain ⟨hjl, ⟨h1, h2⟩, hH, hd⟩ := hj
  have hij : i < j := by
    by_contra hc
    have := tau_mono r0 hsort (not_lt.mp hc) (by omega)
    omega
  have hjm : j < m - 1 := by
    by_contra hc
    have := tau_mono r0 hsort (not_lt.mp hc) hjl
    omega
  exact ⟨by omega, hij, hH, hd⟩

/-- **Window lemma**: a present tile was inserted at most `w` times before the
last time of the prefix. -/
theorem last_le_of_windows {L : List (InsRec k)} (r0 : InsRec k)
    {R : ℕ → List (RowH k × ℕ × Sq k)} {T : ℕ}
    (hsort : L.Pairwise fun a b => a.τ ≤ b.τ) (hlt : ∀ r ∈ L, r.τ < T)
    (hperm : ∀ τ, ((L.filter fun r => r.τ = τ).map proj).Perm (R τ))
    (w : ℕ) (H : RowH k) (d : ℕ)
    (hA : ∀ τ0, τ0 + w < T → insPos k s H d + 1 ≤
      ∑ τ ∈ Ioc τ0 (τ0 + w), (R τ).countP (fun p => decide (p.1 = H ∧ d ≤ p.2.1)))
    {m i : ℕ} (hm : m ≤ L.length) (him : i < m) (hH : (L.getD i r0).H = H)
    (hd : (L.getD i r0).d = d)
    (hp : pushes (fun j => L.getD j r0) i m ≤ insPos k s H d) :
    (L.getD (m - 1) r0).τ ≤ (L.getD i r0).τ + w := by
  by_contra hc
  have hT : (L.getD (m - 1) r0).τ < T := by
    have hmem : L.getD (m - 1) r0 ∈ L := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    have := hlt _ hmem
    exact this
  have h1 := hA (L.getD i r0).τ (by omega)
  have h2 := pushes_ge r0 hsort hperm hm him
  rw [hH, hd] at h2
  have h3 : ∑ τ ∈ Ioc (L.getD i r0).τ ((L.getD i r0).τ + w),
      (R τ).countP (fun p => decide (p.1 = H ∧ d ≤ p.2.1)) ≤
      ∑ τ ∈ Ioo (L.getD i r0).τ (L.getD (m - 1) r0).τ,
        (R τ).countP (fun p => decide (p.1 = H ∧ d ≤ p.2.1)) := by
    apply sum_le_sum_of_subset
    intro τ; simp only [mem_Ioc, mem_Ioo]; omega
  omega

section main

variable {L : List (InsRec k)} (r0 : InsRec k) {R : ℕ → List (RowH k × ℕ × Sq k)} {T : ℕ}
  (w : RowH k → ℕ → ℕ) (Nb : RowH k → ℕ → Sq k → ℕ)

/-- Present class-`x` tiles of one half, for a prefix of length `m ≤ |L|`. -/
theorem count_tagged_le
    (hsort : L.Pairwise fun a b => a.τ ≤ b.τ) (hlt : ∀ r ∈ L, r.τ < T)
    (hperm : ∀ τ, ((L.filter fun r => r.τ = τ).map proj).Perm (R τ))
    (hdk : ∀ τ, ∀ p ∈ R τ, p.2.1 < k)
    (hA : ∀ H d, d < k → ∀ τ0, τ0 + w H d < T → insPos k s H d + 1 ≤
      ∑ τ ∈ Ioc τ0 (τ0 + w H d), (R τ).countP (fun p => decide (p.1 = H ∧ d ≤ p.2.1)))
    (hB : ∀ H d, d < k → ∀ x τ0, τ0 < T →
      ∑ τ ∈ Icc τ0 (τ0 + w H d), (R τ).countP (fun p => decide (p = (H, d, x))) ≤ Nb H d x)
    {m : ℕ} (hm : m ≤ L.length) (H : RowH k) (x : Sq k) (len : ℕ) :
    ((range len).filter fun q =>
        (irun s (fun i => L.getD i r0) m H q).map (fun i => (L.getD i r0).x) = some x).card ≤
      ∑ d ∈ range k, Nb H d x := by
  refine (card_present_le s (fun i => L.getD i r0) m H len (fun i => (L.getD i r0).x) x).trans ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp
  have hmaps : ∀ i ∈ (range m).filter (fun i => (L.getD i r0).H = H ∧ (L.getD i r0).x = x ∧
      pushes (fun j => L.getD j r0) i m ≤ insPos k s H (L.getD i r0).d),
      (L.getD i r0).d ∈ range k := by
    intro i hi
    simp only [mem_filter, mem_range] at hi
    exact mem_range.mpr (hdk _ _ (proj_mem r0 hperm (i := i) (by omega)))
  rw [card_eq_sum_card_fiberwise hmaps]
  apply sum_le_sum
  intro d hd
  have hdk' := mem_range.mp hd
  set τl := (L.getD (m - 1) r0).τ
  set w0 := w H d
  calc _ ≤ ((range L.length).filter fun i => (L.getD i r0).τ ∈ Icc (τl - w0) (τl - w0 + w0) ∧
        proj (L.getD i r0) = (H, d, x)).card := by
        apply card_le_card
        intro i hi
        simp only [mem_filter, mem_range] at hi
        obtain ⟨⟨him, hH, hx, hp⟩, hdi⟩ := hi
        rw [hdi] at hp
        have h1 := last_le_of_windows s r0 hsort hlt hperm w0 H d (hA H d hdk') hm him hH hdi hp
        have h2 := tau_mono r0 hsort (j := i) (j' := m - 1) (by omega) (by omega)
        simp only [mem_filter, mem_range, mem_Icc, proj, hH, hdi, hx]
        exact ⟨by omega, ⟨by omega, by omega⟩, trivial⟩
    _ = ∑ τ ∈ Icc (τl - w0) (τl - w0 + w0), ((range L.length).filter fun i =>
          (L.getD i r0).τ = τ ∧ proj (L.getD i r0) = (H, d, x)).card :=
        (sum_card_fiber _ _ _ _).symm
    _ = ∑ τ ∈ Icc (τl - w0) (τl - w0 + w0), (R τ).countP (fun p => decide (p = (H, d, x))) :=
        sum_congr rfl fun τ _ => card_time_filter r0 hperm τ (fun p => p = (H, d, x))
    _ ≤ Nb H d x := by
        apply hB H d hdk' x
        have hmem : L.getD (m - 1) r0 ∈ L := by
          rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
        have := hlt _ hmem
        omega

/-- **In-flight counts from window properties.** -/
theorem newCnt_le_of_windows (r0 : InsRec k)
    (hsort : L.Pairwise fun a b => a.τ ≤ b.τ) (hlt : ∀ r ∈ L, r.τ < T)
    (hperm : ∀ τ, ((L.filter fun r => r.τ = τ).map proj).Perm (R τ))
    (hdk : ∀ τ, ∀ p ∈ R τ, p.2.1 < k)
    (hA : ∀ H d, d < k → ∀ τ0, τ0 + w H d < T → insPos k s H d + 1 ≤
      ∑ τ ∈ Ioc τ0 (τ0 + w H d), (R τ).countP (fun p => decide (p.1 = H ∧ d ≤ p.2.1)))
    (hB : ∀ H d, d < k → ∀ x τ0, τ0 < T →
      ∑ τ ∈ Icc τ0 (τ0 + w H d), (R τ).countP (fun p => decide (p = (H, d, x))) ≤ Nb H d x)
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
  exact count_tagged_le s r0 w Nb hsort hlt hperm hdk hA hB (min_le_right _ _) _ x _

end main

end SlidingPuzzle.Hub
