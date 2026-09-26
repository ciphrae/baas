import SlidingPuzzle.Hub.InFlightDefs

/-! # The push lemma for the ghost rows

We run the ghost rows with *indices* instead of tags: the insertion number `m`
writes `some m`. A tile present at position `q` of a half, inserted by insertion
`i`, satisfies `q + pushes i m ≤ insPos (e i).d`, where `pushes i m` counts the
later insertions into the same half from a distance `≥ (e i).d` (these insert at
positions `≥` the tile's, so each moves it one step toward the head). Since
indices are distinct, present tiles inject into insertions with few pushes
(`card_present_le`). `ghostRun_take` relates the indexed run to `ghostRun`. -/
namespace SlidingPuzzle.Hub

open Finset

variable {k : ℕ} (s : ℕ)

/-- Ghost rows holding insertion indices. -/
abbrev IGhost (k : ℕ) := RowH k → ℕ → Option ℕ

/-- Insertion number `m` of the sequence `e`. -/
def istep (e : ℕ → InsRec k) (g : IGhost k) (m : ℕ) : IGhost k :=
  Function.update g (e m).H (shiftIn (g (e m).H) (insPos k s (e m).H (e m).d) (some m))

/-- The first `m` insertions of `e`, with indices. -/
def irun (e : ℕ → InsRec k) : ℕ → IGhost k
  | 0 => fun _ _ => none
  | m + 1 => istep s e (irun e m) m

/-- Insertions after `i` and before `m` into the same half from a distance `≥`. -/
def pushes (e : ℕ → InsRec k) (i m : ℕ) : ℕ :=
  ((range m).filter fun j => i < j ∧ (e j).H = (e i).H ∧ (e i).d ≤ (e j).d).card

theorem insPos_mono (H : RowH k) {d d' : ℕ} (h : d ≤ d') : insPos k s H d ≤ insPos k s H d' := by
  have : (d + 1) * s ≤ (d' + 1) * s := Nat.mul_le_mul_right _ (by omega)
  unfold insPos; split <;> omega

theorem pushes_succ (e : ℕ → InsRec k) (i m : ℕ) :
    pushes e i (m + 1) = pushes e i m +
      if i < m ∧ (e m).H = (e i).H ∧ (e i).d ≤ (e m).d then 1 else 0 := by
  unfold pushes
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

theorem pushes_self (e : ℕ → InsRec k) (m : ℕ) : pushes e m (m + 1) = 0 := by
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
structure IInv (e : ℕ → InsRec k) (m : ℕ) : Prop where
  val : ∀ H q i, irun s e m H q = some i →
    i < m ∧ (e i).H = H ∧ q + pushes e i m ≤ insPos k s H (e i).d
  inj : ∀ H q q' i, irun s e m H q = some i → irun s e m H q' = some i → q = q'

theorem iinv_zero (e : ℕ → InsRec k) : IInv s e 0 :=
  ⟨fun _ _ _ h => by simp [irun] at h, fun _ _ _ _ h => by simp [irun] at h⟩

theorem iinv_succ (e : ℕ → InsRec k) (m : ℕ) (hI : IInv s e m) : IInv s e (m + 1) := by
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
        · have := insPos_mono s (e m).H hc.2.2
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

theorem iinv (e : ℕ → InsRec k) : ∀ m, IInv s e m
  | 0 => iinv_zero s e
  | m + 1 => iinv_succ s e m (iinv e m)

/-- Present tiles inject into their insertions, which had few pushes since. -/
theorem card_present_le {β : Type*} [DecidableEq β] (e : ℕ → InsRec k) (m : ℕ) (H : RowH k)
    (len : ℕ) (f : ℕ → β) (b : β) :
    ((range len).filter fun q => (irun s e m H q).map f = some b).card ≤
      ((range m).filter fun i =>
        (e i).H = H ∧ f i = b ∧ pushes e i m ≤ insPos k s H (e i).d).card := by
  have hI := iinv s e m
  refine card_le_card_of_injOn (fun q => (irun s e m H q).getD 0) ?_ ?_
  · intro q hq
    simp only [coe_filter, Set.mem_ofPred_eq] at hq
    obtain ⟨i, hi, hfi⟩ := Option.map_eq_some_iff.mp hq.2
    obtain ⟨him, hH, hb⟩ := hI.val _ _ _ hi
    simp only [coe_filter, Set.mem_ofPred_eq, mem_range, hi, Option.getD_some]
    exact ⟨him, hH, hfi, by omega⟩
  · intro q hq q' hq' heq
    simp only [coe_filter, Set.mem_ofPred_eq] at hq hq'
    obtain ⟨i, hi, -⟩ := Option.map_eq_some_iff.mp hq.2
    obtain ⟨i', hi', -⟩ := Option.map_eq_some_iff.mp hq'.2
    simp only [hi, hi', Option.getD_some] at heq
    subst heq
    exact hI.inj _ _ _ _ hi hi'

/-- `ghostRun` on a prefix is the indexed run with the tags read off. -/
theorem ghostRun_take (L : List (InsRec k)) (r0 : InsRec k) :
    ∀ m, m ≤ L.length → ghostRun s (fun _ _ => none) (L.take m) =
      fun H q => (irun s (fun i => L.getD i r0) m H q).map
        fun i => ((L.getD i r0).x, (L.getD i r0).d)
  | 0, _ => by funext H q; simp [ghostRun, irun]
  | m + 1, hm => by
    have ih := ghostRun_take L r0 m (by omega)
    have hget : L[m]? = some (L.getD m r0) := by
      rw [List.getElem?_eq_getElem (by omega), List.getD_eq_getElem _ _ (by omega)]
    have happ : ∀ (A : List (InsRec k)) (r : InsRec k), ghostRun s (fun _ _ => none) (A ++ [r]) =
        ghostStep s (ghostRun s (fun _ _ => none) A) r := fun A r => by simp [ghostRun]
    rw [List.take_add_one, hget, Option.toList_some, happ, ih]
    funext H q
    simp only [ghostStep, irun, istep]
    by_cases hH : H = (L.getD m r0).H
    · subst hH
      simp only [Function.update_self]
      unfold shiftIn
      split_ifs <;> simp
    · simp only [Function.update_of_ne hH]

end SlidingPuzzle.Hub
