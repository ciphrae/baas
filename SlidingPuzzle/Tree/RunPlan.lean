import SlidingPuzzle.Tree.RunRes

/-! # The plan: demand and dummy edges -/
namespace SlidingPuzzle.Tree
open Finset
open SlidingPuzzle.Hub (Sq Round sends recv IsLast)

variable {k q : ℕ}

/-- The demand matrix: region tiles of `S` with target square `D ≠ S`. -/
def tdemand (σ0 : IState k q) (S D : Sq k) : ℕ := if S = D then 0 else σ0.cnt S D

theorem tdemand_diag (σ0 : IState k q) (S : Sq k) : tdemand σ0 S S = 0 := by simp [tdemand]

theorem tsends_add (σ0 : IState k q) (S : Sq k) :
    sends (tdemand σ0) S + σ0.cnt S S = ∑ y, σ0.cnt S y := by
  unfold sends tdemand
  rw [← add_sum_erase _ _ (mem_univ S), ← add_sum_erase _ _ (mem_univ S)]
  simp only [if_true]
  have : (∑ x ∈ univ.erase S, if S = x then 0 else σ0.cnt S x) = ∑ x ∈ univ.erase S, σ0.cnt S x :=
    sum_congr rfl fun x hx => by rw [if_neg (Ne.symm (ne_of_mem_erase hx))]
  rw [this]; ring

theorem trecv_add (σ0 : IState k q) (D : Sq k) :
    recv (tdemand σ0) D + σ0.cnt D D = ∑ S, σ0.cnt S D := by
  unfold recv tdemand
  rw [← add_sum_erase _ _ (mem_univ D), ← add_sum_erase _ _ (mem_univ D)]
  simp only [if_true]
  have : (∑ x ∈ univ.erase D, if x = D then 0 else σ0.cnt x D) = ∑ x ∈ univ.erase D, σ0.cnt x D :=
    sum_congr rfl fun x hx => by rw [if_neg (ne_of_mem_erase hx)]
  rw [this]; ring

section plan

variable {s : ℕ} (L : LaneSys k q) (σ0 : IState k q) (rsz : Sq k → ℕ)
  (hF1 : ∀ Q, (∑ y, σ0.cnt Q y) + (if σ0.blank = Q then 1 else 0) = rsz Q)
  (hF2 : ∀ y, (∑ Q, σ0.cnt Q y) + σ0.corrCount L s y = s ^ 2 - (if IsLast y then 1 else 0))

include hF1 in
theorem tsends_eq (S : Sq k) :
    sends (tdemand σ0) S + σ0.cnt S S + (if σ0.blank = S then 1 else 0) = rsz S := by
  have := tsends_add σ0 S; have := hF1 S; omega

include hF2 in
theorem trecv_le (D : Sq k) : recv (tdemand σ0) D + σ0.cnt D D ≤ s ^ 2 := by
  have := trecv_add σ0 D; have := hF2 D; omega

include hF1 hF2 in
/-- Dummy in-edges: at most the lane cells of the square plus one. -/
theorem trecv_sub_sends (S : Sq k) :
    recv (tdemand σ0) S - sends (tdemand σ0) S ≤ s ^ 2 - rsz S + 1 := by
  have h1 := tsends_eq σ0 rsz hF1 S
  have h2 := trecv_le L σ0 hF2 S
  split_ifs at h1 <;> omega

include hF1 hF2 in
theorem tmax_le (hrsz : ∀ S, rsz S ≤ s ^ 2) (S : Sq k) :
    sends (tdemand σ0) S ≤ s ^ 2 ∧ recv (tdemand σ0) S ≤ s ^ 2 := by
  have h1 := tsends_eq σ0 rsz hF1 S
  have h2 := trecv_le L σ0 hF2 S
  have := hrsz S
  constructor <;> omega

end plan

end SlidingPuzzle.Tree
