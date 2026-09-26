import SlidingPuzzle.Hub.RunShift
import SlidingPuzzle.Hub.Plan

/-! # Arithmetic for the abstract run

Layout facts (insertion positions lie inside their halves, lengths of halves)
and the plan arithmetic from the class totals `hF1`, `hF2`: the demand matrix
`T`, the dummy and loop counts, and `Δ0 ≤ s²`. -/
namespace SlidingPuzzle.Hub

open Finset

section layout

variable {k s : ℕ}

theorem sqCorridor_le : sqCorridor k s ≤ 2 * k * s := by
  unfold sqCorridor
  have h1 : (k - 1) * s ≤ k * s := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have h2 : (k - 1) * (s - k) ≤ k * s := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  nlinarith

theorem sqCorridor_le_sq (hks : 2 * k ≤ s) : sqCorridor k s ≤ s ^ 2 := by
  have := sqCorridor_le (k := k) (s := s)
  have : 2 * k * s ≤ s * s := Nat.mul_le_mul_right _ hks
  nlinarith

theorem regionSize_add (hks : 2 * k ≤ s) : regionSize k s + sqCorridor k s = s ^ 2 := by
  have := sqCorridor_le_sq hks
  unfold regionSize; omega

theorem rowLen_le (H : RowH k) : rowLen k s H ≤ (k - 1) * s := by
  unfold rowLen
  have := H.2.1.isLt
  split_ifs
  · exact Nat.mul_le_mul_right _ (by omega)
  · exact Nat.mul_le_mul_right _ (by omega)

theorem rowLen_pair (b c : Fin k) :
    rowLen k s (b, c, true) + rowLen k s (b, c, false) = (k - 1) * s := by
  unfold rowLen
  simp only [if_true, Bool.false_eq_true, if_false]
  rw [← add_mul]
  have := c.isLt
  congr 1; omega

theorem colLen_le (V : ColH k) : colLen k s V ≤ (k - 1) * (s - k) := by
  unfold colLen
  have := V.2.1.isLt
  split_ifs
  · exact Nat.mul_le_mul_right _ (by omega)
  · exact Nat.mul_le_mul_right _ (by omega)

/-- The insertion position of a hop1 lies inside its half. -/
theorem hop1Pos_lt {S h : Sq k} (hS : S.2 ≠ h.2) (hs : k + 1 ≤ s) :
    hop1Pos s S h < rowLen k s (hop1Half S h) := by
  unfold hop1Pos insPos hop1Half hop1Dist rowLen
  have hS2 := S.2.isLt
  have hh2 := h.2.isLt
  have hne : S.2.val ≠ h.2.val := fun e => hS (Fin.ext e)
  by_cases hlt : h.2 < S.2
  · have hlt' : h.2.val < S.2.val := hlt
    simp only [hlt, decide_true, if_true]
    have hd : Nat.dist S.2.val h.2.val - 1 + 1 = S.2.val - h.2.val := by
      unfold Nat.dist; omega
    rw [hd]
    have : (S.2.val - h.2.val) * s ≤ (k - 1 - h.2.val) * s :=
      Nat.mul_le_mul_right _ (by omega)
    have : s ≤ (S.2.val - h.2.val) * s := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · have hlt' : S.2.val < h.2.val := by
      have : ¬ h.2.val < S.2.val := hlt
      omega
    simp only [hlt, decide_false, Bool.false_eq_true, if_false]
    have hd : Nat.dist S.2.val h.2.val - 1 + 1 = h.2.val - S.2.val := by
      unfold Nat.dist; omega
    rw [hd]
    have : (h.2.val - S.2.val) * s ≤ h.2.val * s := Nat.mul_le_mul_right _ (by omega)
    have : s ≤ (h.2.val - S.2.val) * s := Nat.le_mul_of_pos_left _ (by omega)
    omega

/-- The insertion position of a hop2 lies inside its half. -/
theorem hop2Pos_lt {h D : Sq k} (hD : h.1 ≠ D.1) (hs : k + 1 ≤ s) :
    hop2Pos s h D < colLen k s (hop2Half h D) := by
  unfold hop2Pos hop2Half colLen
  have hD1 := D.1.isLt
  have hh1 := h.1.isLt
  have hne : h.1.val ≠ D.1.val := fun e => hD (Fin.ext e)
  by_cases hlt : D.1 < h.1
  · have hlt' : D.1.val < h.1.val := hlt
    simp only [hlt, decide_true, if_true]
    have : Nat.dist h.1.val D.1.val - 1 < k - 1 - D.1.val := by unfold Nat.dist; omega
    exact Nat.mul_lt_mul_of_pos_right this (by omega)
  · have hlt' : h.1.val < D.1.val := by
      have : ¬ D.1.val < h.1.val := hlt
      omega
    simp only [hlt, decide_false, Bool.false_eq_true, if_false]
    have : Nat.dist h.1.val D.1.val - 1 < D.1.val := by unfold Nat.dist; omega
    exact Nat.mul_lt_mul_of_pos_right this (by omega)

theorem sqDist_le {P Q : Sq k} : sqDist P Q ≤ 2 * k := by
  unfold sqDist Nat.dist
  have := P.1.isLt; have := P.2.isLt; have := Q.1.isLt; have := Q.2.isLt
  omega

end layout

section plan

variable {k s : ℕ}

/-- The demand matrix: region tiles of `S` with target square `D ≠ S`. -/
def demand (σ0 : IState k) (S D : Sq k) : ℕ := if S = D then 0 else σ0.cnt S D

theorem demand_diag (σ0 : IState k) (S : Sq k) : demand σ0 S S = 0 := by simp [demand]

theorem sends_add (σ0 : IState k) (S : Sq k) :
    sends (demand σ0) S + σ0.cnt S S = ∑ y, σ0.cnt S y := by
  unfold sends demand
  rw [← add_sum_erase _ _ (mem_univ S), ← add_sum_erase _ _ (mem_univ S)]
  simp only [if_true]
  have : (∑ x ∈ univ.erase S, if S = x then 0 else σ0.cnt S x) = ∑ x ∈ univ.erase S, σ0.cnt S x :=
    sum_congr rfl fun x hx => by rw [if_neg (Ne.symm (ne_of_mem_erase hx))]
  rw [this]; ring

theorem recv_add (σ0 : IState k) (D : Sq k) :
    recv (demand σ0) D + σ0.cnt D D = ∑ S, σ0.cnt S D := by
  unfold recv demand
  rw [← add_sum_erase _ _ (mem_univ D), ← add_sum_erase _ _ (mem_univ D)]
  simp only [if_true]
  have : (∑ x ∈ univ.erase D, if x = D then 0 else σ0.cnt x D) = ∑ x ∈ univ.erase D, σ0.cnt x D :=
    sum_congr rfl fun x hx => by rw [if_neg (ne_of_mem_erase hx)]
  rw [this]; ring

variable {σ0 : IState k}
  (hF1 : ∀ Q, (∑ y, σ0.cnt Q y) + (if σ0.blank = Q then 1 else 0) = regionSize k s)
  (hF2 : ∀ y, (∑ Q, σ0.cnt Q y) + σ0.corrCount s y = s ^ 2 - (if IsLast y then 1 else 0))
include hF1

theorem sends_le (S : Sq k) : sends (demand σ0) S ≤ regionSize k s := by
  have := sends_add σ0 S; have := hF1 S; omega

theorem sends_eq (S : Sq k) :
    sends (demand σ0) S + σ0.cnt S S + (if σ0.blank = S then 1 else 0) = regionSize k s := by
  have := sends_add σ0 S; have := hF1 S; omega

omit hF1 in
include hF2 in
theorem recv_le (D : Sq k) : recv (demand σ0) D + σ0.cnt D D ≤ s ^ 2 := by
  have := recv_add σ0 D; have := hF2 D; omega

include hF2

/-- Dummy in-edges: `recv - sends ≤ sqCorridor + 1`. -/
theorem recv_sub_sends (hks : 2 * k ≤ s) (S : Sq k) :
    recv (demand σ0) S - sends (demand σ0) S ≤ sqCorridor k s + 1 := by
  have h1 := sends_eq hF1 S
  have h2 := recv_le hF2 S
  have h3 := regionSize_add (k := k) (s := s) hks
  split_ifs at h1 <;> omega

end plan

end SlidingPuzzle.Hub
