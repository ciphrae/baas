import SlidingPuzzle.Tree.Route
import SlidingPuzzle.Tree.Residence
import SlidingPuzzle.Hub.RunShift

/-! # The abstract run: lanes of both axes, hops, junk and potential

`σ.lane l` is the content of lane `l` of either axis; a hop along `l` from
source coordinate `J` (`hopEv`) shifts it by an insertion at `lpos`, removes the
inserted class from the source's region and adds the head to the landing
region. Junk positions (tiles not moving toward their target) pay for the
inefficient lane steps through the potential `Σ (r + 1)` over junk positions. -/
namespace SlidingPuzzle.Tree
open Finset
open SlidingPuzzle.Hub (Sq shiftIn incCnt decCnt shiftIn_of_lt shiftIn_self' shiftIn_of_gt
  card_filter_shiftIn incCnt_apply decCnt_apply sum_update_add)

variable {k q : ℕ}

namespace IState

/-- The content of a lane of either axis. -/
def lane (σ : IState k q) (l : Ln k q) : ℕ → Sq k := if l.1 then σ.col l.2 else σ.row l.2

variable (L : LaneSys k q) (s : ℕ)

theorem run_append (σ : IState k q) (l₁ l₂ : List (REvent k q)) :
    run s σ (l₁ ++ l₂) = run s (run s σ l₁) l₂ := by
  induction l₁ generalizing σ with
  | nil => rfl
  | cons e es ih => exact ih _

theorem valid_append (σ : IState k q) (l₁ l₂ : List (REvent k q)) :
    Valid L s σ (l₁ ++ l₂) ↔ Valid L s σ l₁ ∧ Valid L s (run s σ l₁) l₂ := by
  induction l₁ generalizing σ with
  | nil => simp [Valid, run]
  | cons e es ih =>
    simp only [List.cons_append, Valid, run, ih]
    tauto

theorem totalCost_append (σ : IState k q) (l₁ l₂ : List (REvent k q)) :
    totalCost s σ (l₁ ++ l₂) = totalCost s σ l₁ + totalCost s (run s σ l₁) l₂ := by
  induction l₁ generalizing σ with
  | nil => simp [totalCost, run]
  | cons e es ih =>
    simp only [List.cons_append, totalCost, run, ih]
    ring

theorem valid_singleton (σ : IState k q) (e : REvent k q) : Valid L s σ [e] ↔ σ.Pre L e := by
  simp [Valid]

theorem totalCost_singleton (σ : IState k q) (e : REvent k q) :
    totalCost s σ [e] = σ.cost s e := by
  simp [totalCost]

/-- Junk positions `0..p` of a lane. -/
def ljunk (σ : IState k q) (l : Ln k q) (p : ℕ) : ℕ :=
  ((range (p + 1)).filter fun r => ¬ lgood l (σ.lane l r)).card

/-- All junk positions. -/
def junkCnt (σ : IState k q) : ℕ :=
  ∑ l : Ln k q, ((range (llen L s l)).filter fun r => ¬ lgood l (σ.lane l r)).card

/-- The junk potential. -/
def pot (σ : IState k q) : ℕ :=
  ∑ l : Ln k q, ∑ r ∈ (range (llen L s l)).filter (fun r => ¬ lgood l (σ.lane l r)), (r + 1)

end IState

/-! ## A hop along a lane of either axis -/

section hop

variable (L : LaneSys k q) (s : ℕ)

/-- The fixed part of a hop's budget. -/
def hopK (k q s : ℕ) : ℕ := 20 * s + 20 * k * (q + 2) + 600 * k + 2000

theorem pre_hopEv (σ : IState k q) (l : Ln k q) (J : Fin k) (y : Sq k) :
    σ.Pre L (hopEv l J y) ↔ σ.blank = land l ∧ LIn L l.2 J ∧ 1 ≤ σ.cnt (src l J) y := by
  unfold hopEv land src
  split_ifs <;> rfl

theorem step_hopEv_cnt (σ : IState k q) (l : Ln k q) (J : Fin k) (y : Sq k) :
    (σ.step s (hopEv l J y)).cnt =
      incCnt (decCnt σ.cnt (src l J) y) (land l) (σ.lane l 0) := by
  unfold hopEv land src IState.lane
  split_ifs <;> rfl

theorem step_hopEv_blank (σ : IState k q) (l : Ln k q) (J : Fin k) (y : Sq k) :
    (σ.step s (hopEv l J y)).blank = src l J := by
  unfold hopEv src
  split_ifs <;> rfl

theorem step_hopEv_lane (σ : IState k q) (l : Ln k q) (J : Fin k) (y : Sq k) :
    (σ.step s (hopEv l J y)).lane = Function.update σ.lane l
      (shiftIn (σ.lane l) (lpos k s l J) y) := by
  funext l' r
  obtain ⟨a, H⟩ := l
  obtain ⟨a', H'⟩ := l'
  unfold hopEv IState.lane lpos
  cases a <;> cases a'
  · simp only [Bool.false_eq_true, if_false, IState.step]
    by_cases h : H' = H
    · subst h; simp
    · rw [Function.update_of_ne h, Function.update_of_ne (by simp [h])]; rfl
  · simp [IState.step]
  · simp [IState.step]
  · simp only [if_true, IState.step]
    by_cases h : H' = H
    · subst h; simp
    · rw [Function.update_of_ne h, Function.update_of_ne (by simp [h])]; rfl

theorem cost_hopEv (σ : IState k q) (l : Ln k q) (J : Fin k) (y : Sq k) :
    σ.cost s (hopEv l J y) ≤ hopK k q s + σ.ljunk l (lpos k s l J) := by
  obtain ⟨a, H⟩ := l
  unfold hopEv IState.ljunk IState.lane lpos lgood hopK
  cases a
  · simp only [Bool.false_eq_true, if_false, IState.cost, IState.junkRow]; omega
  · simp only [if_true, IState.cost, IState.junkCol]; omega

/-- The insertion position lies in the lane. -/
theorem lpos_lt {n : ℕ} [NeZero n] (td : TDims n k s q) (l : Ln k q) (J : Fin k) (hJ : LIn L l.2 J) :
    lpos k s l J < llen L s l := by
  unfold lpos llen
  split_ifs
  · exact (colPos_geom L td l.2 J hJ).1
  · exact (rowPos_geom (n := n) L td l.2 J hJ).1

end hop

/-! ## Counting positions through a shift -/

section shift

variable {α : Type*}

/-- Weighted count through an insertion of any value. -/
theorem sum_filter_shiftIn' (P : α → Prop) [DecidablePred P] (f : ℕ → α) {p Ln : ℕ}
    (hp : p < Ln) (v : α) :
    (∑ r ∈ (range Ln).filter (fun r => P (shiftIn f p v r)), (r + 1)) +
        ((range (p + 1)).filter fun r => P (f r)).card =
      (∑ r ∈ (range Ln).filter (fun r => P (f r)), (r + 1)) + (if P v then p + 1 else 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, Ln = (p + 1) + m := ⟨Ln - (p + 1), by omega⟩
  have hsplit : ∀ g : ℕ → ℕ, ∑ x ∈ range (p + 1 + m), g x =
      (∑ x ∈ range (p + 1), g x) + ∑ x ∈ range m, g (p + 1 + x) := fun g => sum_range_add g _ _
  simp only [sum_filter, card_filter]
  rw [hsplit, hsplit]
  have htail : (∑ x ∈ range m, if P (shiftIn f p v (p + 1 + x)) then p + 1 + x + 1 else 0) =
      ∑ x ∈ range m, if P (f (p + 1 + x)) then p + 1 + x + 1 else 0 := by
    refine sum_congr rfl fun x _ => ?_
    rw [shiftIn_of_gt (by omega)]
  have h1 : (∑ x ∈ range (p + 1), if P (shiftIn f p v x) then x + 1 else 0) =
      (∑ x ∈ range p, if P (f (x + 1)) then x + 1 else 0) + (if P v then p + 1 else 0) := by
    rw [sum_range_succ, shiftIn_self']
    congr 1
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

end shift

section potential

variable (L : LaneSys k q) (s : ℕ)

/-- A hop pays its junk steps from the potential; a junk insertion adds at most
its position plus one. -/
theorem pot_hopEv {n : ℕ} [NeZero n] (td : TDims n k s q) (σ : IState k q) (l : Ln k q) (J : Fin k)
    (hJ : LIn L l.2 J) (y : Sq k) :
    (σ.step s (hopEv l J y)).pot L s + σ.ljunk l (lpos k s l J) =
      σ.pot L s + (if ¬ lgood l y then lpos k s l J + 1 else 0) := by
  unfold IState.pot IState.ljunk
  rw [step_hopEv_lane s σ l J y]
  have hsum := sum_update_add
    (fun (l' : Ln k q) (f : ℕ → Sq k) =>
      ∑ r ∈ (range (llen L s l')).filter (fun r => ¬ lgood l' (f r)), (r + 1))
    σ.lane l (shiftIn (σ.lane l) (lpos k s l J) y)
  have hc := sum_filter_shiftIn' (fun a : Sq k => ¬ lgood l a) (σ.lane l)
    (lpos_lt L s td l J hJ) y
  omega

/-- The junk count after a hop. -/
theorem junkCnt_hopEv {n : ℕ} [NeZero n] (td : TDims n k s q) (σ : IState k q) (l : Ln k q) (J : Fin k)
    (hJ : LIn L l.2 J) (y : Sq k) :
    (σ.step s (hopEv l J y)).junkCnt L s + (if ¬ lgood l (σ.lane l 0) then 1 else 0) =
      σ.junkCnt L s + (if ¬ lgood l y then 1 else 0) := by
  unfold IState.junkCnt
  rw [step_hopEv_lane s σ l J y]
  have hsum := sum_update_add
    (fun (l' : Ln k q) (f : ℕ → Sq k) =>
      ((range (llen L s l')).filter fun r => ¬ lgood l' (f r)).card)
    σ.lane l (shiftIn (σ.lane l) (lpos k s l J) y)
  have hc := card_filter_shiftIn (fun a : Sq k => ¬ lgood l a) (σ.lane l)
    (lpos_lt L s td l J hJ) y
  omega

end potential

end SlidingPuzzle.Tree
