import SlidingPuzzle.Hub.Interface

/-! # Generic lemmas for the abstract run

Counting lemmas for `shiftIn` (an insertion shifts a prefix of a half by one
position), sums over `Function.update`, `incCnt`/`decCnt` in closed form, and
the behaviour of `IState.run`, `Valid` and `totalCost` on concatenations. -/
namespace SlidingPuzzle.Hub

open Finset

section shift

variable {α : Type*}

theorem shiftIn_of_lt {f : ℕ → α} {p q : ℕ} {v : α} (h : q < p) :
    shiftIn f p v q = f (q + 1) := by
  simp [shiftIn, h]

theorem shiftIn_self' {f : ℕ → α} {p : ℕ} {v : α} : shiftIn f p v p = v := by
  simp [shiftIn]

theorem shiftIn_of_gt {f : ℕ → α} {p q : ℕ} {v : α} (h : p < q) :
    shiftIn f p v q = f q := by
  simp [shiftIn, show ¬ q < p by omega, show q ≠ p by omega]

/-- Counting positions `< L` satisfying `P` before and after an insertion at
`p < L`: the head leaves, the inserted value enters. -/
theorem card_filter_shiftIn (P : α → Prop) [DecidablePred P] (f : ℕ → α) {p L : ℕ}
    (hp : p < L) (v : α) :
    ((range L).filter fun q => P (shiftIn f p v q)).card + (if P (f 0) then 1 else 0) =
      ((range L).filter fun q => P (f q)).card + (if P v then 1 else 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, L = (p + 1) + m := ⟨L - (p + 1), by omega⟩
  have hsplit : ∀ g : ℕ → ℕ, ∑ x ∈ range (p + 1 + m), g x =
      (∑ x ∈ range (p + 1), g x) + ∑ x ∈ range m, g (p + 1 + x) := fun g => sum_range_add g _ _
  simp only [card_filter]
  rw [hsplit, hsplit]
  have htail : (∑ x ∈ range m, if P (shiftIn f p v (p + 1 + x)) then 1 else 0) =
      ∑ x ∈ range m, if P (f (p + 1 + x)) then 1 else 0 := by
    refine sum_congr rfl fun x _ => ?_
    rw [shiftIn_of_gt (by omega)]
  have h1 : (∑ x ∈ range (p + 1), if P (shiftIn f p v x) then 1 else 0) =
      (∑ x ∈ range p, if P (f (x + 1)) then 1 else 0) + (if P v then 1 else 0) := by
    rw [sum_range_succ, shiftIn_self']
    congr 1
    refine sum_congr rfl fun x hx => ?_
    rw [shiftIn_of_lt (mem_range.1 hx)]
  have h2 : (∑ x ∈ range (p + 1), if P (f x) then 1 else 0) =
      (∑ x ∈ range p, if P (f (x + 1)) then 1 else 0) + (if P (f 0) then 1 else 0) :=
    sum_range_succ' _ _
  rw [htail, h1, h2]
  ring

/-- Weighted version: with weights `q + 1` and a value `v` not satisfying `P`,
the weight drops by the number of `P`-positions in `0..p`. -/
theorem sum_filter_shiftIn (P : α → Prop) [DecidablePred P] (f : ℕ → α) {p L : ℕ}
    (hp : p < L) {v : α} (hv : ¬ P v) :
    (∑ q ∈ (range L).filter (fun q => P (shiftIn f p v q)), (q + 1)) +
        ((range (p + 1)).filter fun q => P (f q)).card =
      ∑ q ∈ (range L).filter (fun q => P (f q)), (q + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, L = (p + 1) + m := ⟨L - (p + 1), by omega⟩
  have hsplit : ∀ g : ℕ → ℕ, ∑ x ∈ range (p + 1 + m), g x =
      (∑ x ∈ range (p + 1), g x) + ∑ x ∈ range m, g (p + 1 + x) := fun g => sum_range_add g _ _
  simp only [sum_filter, card_filter]
  rw [hsplit, hsplit]
  have htail : (∑ x ∈ range m, if P (shiftIn f p v (p + 1 + x)) then p + 1 + x + 1 else 0) =
      ∑ x ∈ range m, if P (f (p + 1 + x)) then p + 1 + x + 1 else 0 := by
    refine sum_congr rfl fun x _ => ?_
    rw [shiftIn_of_gt (by omega)]
  have h1 : (∑ x ∈ range (p + 1), if P (shiftIn f p v x) then x + 1 else 0) =
      (∑ x ∈ range p, if P (f (x + 1)) then x + 1 else 0) := by
    rw [sum_range_succ, shiftIn_self', if_neg hv, add_zero]
    refine sum_congr rfl fun x hx => ?_
    rw [shiftIn_of_lt (mem_range.1 hx)]
  have h2 : (∑ x ∈ range (p + 1), if P (f x) then x + 1 else 0) =
      (∑ x ∈ range p, if P (f (x + 1)) then x + 1 + 1 else 0) + (if P (f 0) then 1 else 0) := by
    rw [sum_range_succ']
  have h3 : (∑ x ∈ range (p + 1), if P (f x) then 1 else 0) =
      (∑ x ∈ range p, if P (f (x + 1)) then 1 else 0) + (if P (f 0) then 1 else 0) :=
    sum_range_succ' _ _
  have h4 : (∑ x ∈ range p, if P (f (x + 1)) then x + 1 + 1 else 0) =
      (∑ x ∈ range p, if P (f (x + 1)) then x + 1 else 0) +
        ∑ x ∈ range p, if P (f (x + 1)) then 1 else 0 := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  rw [htail, h1, h2, h3, h4]
  ring

/-- Positions of `0..p` satisfying `P` are at most `p + 1`. -/
theorem card_filter_range_le (P : ℕ → Prop) [DecidablePred P] (p : ℕ) :
    ((range p).filter P).card ≤ p :=
  (card_filter_le _ _).trans (card_range p).le

end shift

section update

variable {ι β : Type*} [Fintype ι] [DecidableEq ι]

/-- A sum over a function changed at one point. -/
theorem sum_update_add (F : ι → β → ℕ) (f : ι → β) (i : ι) (v : β) :
    (∑ j, F j (Function.update f i v j)) + F i (f i) = (∑ j, F j (f j)) + F i v := by
  rw [← add_sum_erase _ _ (mem_univ i), ← add_sum_erase _ _ (mem_univ i)]
  have : (∑ j ∈ univ.erase i, F j (Function.update f i v j)) = ∑ j ∈ univ.erase i, F j (f j) :=
    sum_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]
  rw [this, Function.update_self]
  ring

end update

section cnt

variable {k : ℕ}

theorem incCnt_apply (c : Sq k → Sq k → ℕ) (Q y Q' y' : Sq k) :
    incCnt c Q y Q' y' = c Q' y' + if Q' = Q ∧ y' = y then 1 else 0 := by
  unfold incCnt; split_ifs <;> simp

theorem decCnt_apply (c : Sq k → Sq k → ℕ) (Q y Q' y' : Sq k) :
    decCnt c Q y Q' y' = c Q' y' - if Q' = Q ∧ y' = y then 1 else 0 := by
  unfold decCnt; split_ifs <;> simp

theorem sum_incCnt (c : Sq k → Sq k → ℕ) (Q y Q' : Sq k) :
    ∑ y', incCnt c Q y Q' y' = (∑ y', c Q' y') + if Q' = Q then 1 else 0 := by
  simp only [incCnt_apply, sum_add_distrib]
  congr 1
  by_cases h : Q' = Q
  · simp [h]
  · simp [h]

theorem sum_decCnt (c : Sq k → Sq k → ℕ) (Q y Q' : Sq k) (hc : 1 ≤ c Q y) :
    ∑ y', decCnt c Q y Q' y' = (∑ y', c Q' y') - if Q' = Q then 1 else 0 := by
  simp only [decCnt_apply]
  rw [sum_tsub_distrib]
  · congr 1
    by_cases h : Q' = Q
    · simp [h]
    · simp [h]
  · intro y' _
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; exact hc
    · exact Nat.zero_le _

theorem sum_decCnt_le (c : Sq k → Sq k → ℕ) (Q y Q' : Sq k) :
    (∑ y', c Q' y') ≤ (∑ y', decCnt c Q y Q' y') + if Q' = Q then 1 else 0 := by
  simp only [decCnt_apply]
  by_cases h : Q' = Q
  · subst h
    simp only [true_and, if_true]
    rw [← add_sum_erase _ _ (mem_univ y), ← add_sum_erase _ _ (mem_univ y)]
    have : (∑ x ∈ univ.erase y, (c Q' x - if x = y then 1 else 0)) =
        ∑ x ∈ univ.erase y, c Q' x :=
      sum_congr rfl fun x hx => by simp [ne_of_mem_erase hx]
    rw [this]; simp; omega
  · simp [h]

end cnt

namespace IState

variable {k : ℕ} (s : ℕ)

theorem run_append (σ : IState k) (l₁ l₂ : List (REvent k)) :
    run s σ (l₁ ++ l₂) = run s (run s σ l₁) l₂ := by
  induction l₁ generalizing σ with
  | nil => rfl
  | cons e es ih => exact ih _

theorem valid_append (σ : IState k) (l₁ l₂ : List (REvent k)) :
    Valid s σ (l₁ ++ l₂) ↔ Valid s σ l₁ ∧ Valid s (run s σ l₁) l₂ := by
  induction l₁ generalizing σ with
  | nil => simp [Valid, run]
  | cons e es ih =>
    simp only [List.cons_append, Valid, run, ih]
    tauto

theorem totalCost_append (σ : IState k) (l₁ l₂ : List (REvent k)) :
    totalCost s σ (l₁ ++ l₂) = totalCost s σ l₁ + totalCost s (run s σ l₁) l₂ := by
  induction l₁ generalizing σ with
  | nil => simp [totalCost, run]
  | cons e es ih =>
    simp only [List.cons_append, totalCost, run, ih]
    ring

theorem run_singleton (σ : IState k) (e : REvent k) : run s σ [e] = σ.step s e := rfl

theorem valid_singleton (σ : IState k) (e : REvent k) : Valid s σ [e] ↔ σ.Pre s e := by
  simp [Valid]

theorem totalCost_singleton (σ : IState k) (e : REvent k) :
    totalCost s σ [e] = σ.cost s e := by
  simp [totalCost]

end IState

end SlidingPuzzle.Hub
