import SlidingPuzzle.Port.PcAlg

/-! # The local invariant through a hop stage -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle.Hub (Sq shiftIn incCnt decCnt shiftIn_of_lt shiftIn_self' shiftIn_of_gt)
open SlidingPuzzle.Tree

variable {k q : ℕ} (L : LaneSys k q)

/-- The role taken from the inserting square is available. -/
def PRoleOK (G : PG k q) (u x : Sq k) (sp : Pt) : Kind → Sq k → Prop
  | .sch, y => y = x ∧ 1 ≤ G.sched u y
  | .stk, y => y = x ∧ 1 ≤ G.stock u sp y
  | .plh, y => 1 ≤ G.free u y

/-- The insertion mode keeps the demands of the source's ports. -/
def GoodMode (G : PG k q) (u x : Sq k) (kd : Kind) (y : Sq k) (sp : Pt) : Mode k → Prop
  | .cheap => 1 ≤ G.σ.pc u (dport L u x) y ∧
      ((kd = .stk ∧ sp = dport L u x) ∨ dem L G u (some (dport L u x)) y < G.σ.pc u (dport L u x) y)
  | .imp p z => p ≠ some (dport L u x) ∧ dem L G u p y < G.σ.partCnt u p y ∧
      dem L G u (some (dport L u x)) z < G.σ.pc u (dport L u x) z

theorem sum_sub_add {α : Type*} [Fintype α] (f a b : α → ℕ) (h : ∀ i, a i ≤ f i) :
    (∑ i, (f i - a i + b i)) + ∑ i, a i = (∑ i, f i) + ∑ i, b i := by
  rw [← sum_add_distrib, ← sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by have := h i; omega

theorem pStage_stk (s τ : ℕ) (G : PG k q) (u x : Sq k) (kd : Kind) (y : Sq k) (m : Mode k)
    (sp : Pt) (hr : kd = .stk → 1 ≤ G.stock u sp y) (Q z : Sq k) :
    (pStage L s τ G u x kd y m sp).stk Q z + (if kd = .stk ∧ Q = u ∧ z = y then 1 else 0) =
      G.stk Q z + (if gcl (pgh k s G (L.stage u x).1 0) = some z ∧ Q = L.nxt u x ∧ L.nxt u x ≠ z
        then 1 else 0) := by
  unfold PG.stk
  simp only [pStage]
  have h := sum_sub_add (fun pt => G.stock Q pt z)
    (fun pt => if kd = .stk ∧ Q = u ∧ pt = sp ∧ z = y then 1 else 0)
    (fun pt => if gcl (pgh k s G (L.stage u x).1 0) = some z ∧ Q = land (L.stage u x).1 ∧
      land (L.stage u x).1 ≠ z ∧ pt = lport (L.stage u x).1 then 1 else 0)
    (fun pt => by
      split_ifs with h1
      · obtain ⟨h1, rfl, rfl, rfl⟩ := h1; exact hr h1
      · exact Nat.zero_le _)
  have e1 : ∑ pt : Pt, (if kd = .stk ∧ Q = u ∧ pt = sp ∧ z = y then 1 else 0) =
      if kd = .stk ∧ Q = u ∧ z = y then 1 else 0 := by
    by_cases hc : kd = .stk ∧ Q = u ∧ z = y
    · rw [if_pos hc, Finset.sum_eq_single sp]
      · simp [hc]
      · intro b _ hb; simp [hb]
      · simp
    · rw [if_neg hc]; apply Finset.sum_eq_zero; intro b _
      rw [if_neg (fun h' => hc ⟨h'.1, h'.2.1, h'.2.2.2⟩)]
  have e2 : ∑ pt : Pt, (if gcl (pgh k s G (L.stage u x).1 0) = some z ∧ Q = land (L.stage u x).1 ∧
      land (L.stage u x).1 ≠ z ∧ pt = lport (L.stage u x).1 then 1 else 0) =
      if gcl (pgh k s G (L.stage u x).1 0) = some z ∧ Q = L.nxt u x ∧ L.nxt u x ≠ z then 1 else 0 := by
    by_cases hc : gcl (pgh k s G (L.stage u x).1 0) = some z ∧ Q = L.nxt u x ∧ L.nxt u x ≠ z
    · rw [if_pos hc, Finset.sum_eq_single (lport (L.stage u x).1)]
      · simp only [and_true]; exact if_pos hc
      · intro b _ hb; simp [hb]
      · simp
    · rw [if_neg hc]; apply Finset.sum_eq_zero; intro b _
      rw [if_neg (fun h' => hc ⟨h'.1, h'.2.1, h'.2.2.1⟩)]
  rw [e1, e2] at h
  exact h

end SlidingPuzzle.Port

namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle.Hub (Sq shiftIn incCnt decCnt shiftIn_of_lt shiftIn_self' shiftIn_of_gt)
open SlidingPuzzle.Tree

variable {k q : ℕ} (L : LaneSys k q)

section pres
variable {s σ' : ℕ} {σ0 : PState k q} {F0 : ℕ}

theorem ppre_append {G : PG k q} (hL : PLInv L s σ' σ0 F0 G) {e : PEvent k q} (he : G.σ.Pre L e) :
    G.σ.step s e = σ0.run s (G.evs ++ [e]) ∧ σ0.Valid L s (G.evs ++ [e]) := by
  rw [PState.run_append, ← hL.run_eq, PState.valid_append, ← hL.run_eq]
  exact ⟨rfl, hL.valid, he, trivial⟩

theorem pcost_append {G : PG k q} (hL : PLInv L s σ' σ0 F0 G) (e : PEvent k q) :
    σ0.totalCost s σ' (G.evs ++ [e]) = σ0.totalCost s σ' G.evs + G.σ.cost s σ' e := by
  rw [PState.totalCost_append, ← hL.run_eq]
  simp [PState.totalCost]

end pres

theorem pStage_cnt (s τ : ℕ) (G : PG k q) {u x : Sq k} (hux : u ≠ x) (kd : Kind) (y : Sq k)
    (m : Mode k) (sp : Pt) (Q z : Sq k) :
    (pStage L s τ G u x kd y m sp).σ.cnt Q z = G.σ.cnt Q z - (if Q = u ∧ z = y then 1 else 0) +
      (if Q = L.nxt u x ∧ z = G.σ.lane (L.stage u x).1 0 then 1 else 0) := by
  simp only [pStage, step_hop_cnt, Hub.incCnt_apply, Hub.decCnt_apply, stage_src hux, land_stage]

/-- Port counts after a stage, pointwise. -/
theorem pStage_pc (s τ : ℕ) (G : PG k q) {u x : Sq k} (hux : u ≠ x) (kd : Kind) (y : Sq k)
    (m : Mode k) (sp : Pt) :
    (pStage L s τ G u x kd y m sp).σ.pc =
      PState.srcPc (incP G.σ.pc (L.nxt u x) (dport L u x) (G.σ.lane (L.stage u x).1 0)) u
        (dport L u x) y m := by
  simp only [pStage, step_hop_pc, stage_src hux, land_stage, dport]

end SlidingPuzzle.Port
