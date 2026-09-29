import SlidingPuzzle.Port.GhostLocal

/-! # Turn counting through a hop stage -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle.Hub (Sq)
open SlidingPuzzle.Tree

variable {k q : ℕ} (L : LaneSys k q)

/-- The head of the stage lane, if it is a clean tile landing at a turn. -/
def turnHd (l : Ln k q) (g : Option (GCls k × ℕ)) : ℕ :=
  match gcl g with
  | some z => if turning L l z then 1 else 0
  | none => 0

theorem NS_pStage (s τ : ℕ) (G : PG k q) (u x : Sq k) (kd : Kind) (y : Sq k) (m : Mode k)
    (sp : Pt) (hr : kd = .stk → 1 ≤ G.stock u sp y) :
    NS L (pStage L s τ G u x kd y m sp) + (if kd = .stk ∧ sp ≠ dport L u y then 1 else 0) =
      NS L G + turnHd L (L.stage u x).1 (pgh k s G (L.stage u x).1 0) := by
  set l0 := (L.stage u x).1
  set g := pgh k s G l0 0
  have key := sum3_sub_add
    (fun Q z pt => if pt = dport L Q z then 0 else G.stock Q pt z)
    (fun Q z pt => if pt = dport L Q z then 0 else
      (if kd = .stk ∧ Q = u ∧ pt = sp ∧ z = y then 1 else 0))
    (fun Q z pt => if pt = dport L Q z then 0 else
      (if gcl g = some z ∧ Q = land l0 ∧ land l0 ≠ z ∧ pt = lport l0 then 1 else 0))
    (fun Q z pt => by
      split_ifs with h1 h2 <;> try omega
      obtain ⟨h2, rfl, rfl, rfl⟩ := h2; exact hr h2)
  have e0 : NS L (pStage L s τ G u x kd y m sp) = ∑ Q, ∑ z, ∑ pt,
      ((if pt = dport L Q z then 0 else G.stock Q pt z) -
        (if pt = dport L Q z then 0 else
          (if kd = .stk ∧ Q = u ∧ pt = sp ∧ z = y then 1 else 0)) +
        (if pt = dport L Q z then 0 else
          (if gcl g = some z ∧ Q = land l0 ∧ land l0 ≠ z ∧ pt = lport l0 then 1 else 0))) := by
    unfold NS
    refine Finset.sum_congr rfl fun Q _ => Finset.sum_congr rfl fun z _ =>
      Finset.sum_congr rfl fun pt _ => ?_
    simp only [pStage]
    split_ifs <;> rfl
  have e1 : (∑ Q, ∑ z, ∑ pt, (if pt = dport L Q z then 0 else
      (if kd = .stk ∧ Q = u ∧ pt = sp ∧ z = y then 1 else 0))) =
      if kd = .stk ∧ sp ≠ dport L u y then 1 else 0 := by
    have := sum3_single (fun Q z pt => if pt = dport L Q z then 0 else 1) u y sp (kd = .stk)
    rw [show (if kd = .stk ∧ sp ≠ dport L u y then 1 else 0) =
      (if kd = .stk then (if sp = dport L u y then 0 else 1) else 0) by
        by_cases h : kd = .stk <;> by_cases h' : sp = dport L u y <;> simp [h, h'], ← this]
    refine Finset.sum_congr rfl fun Q _ => Finset.sum_congr rfl fun z _ =>
      Finset.sum_congr rfl fun pt _ => ?_
    by_cases h : kd = .stk ∧ Q = u ∧ pt = sp ∧ z = y
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]; simp
  have e2 : (∑ Q, ∑ z, ∑ pt, (if pt = dport L Q z then 0 else
      (if gcl g = some z ∧ Q = land l0 ∧ land l0 ≠ z ∧ pt = lport l0 then 1 else 0))) =
      turnHd L l0 g := by
    unfold turnHd
    rcases hg : gcl g with _ | z0
    · apply Finset.sum_eq_zero; intro Q _; apply Finset.sum_eq_zero; intro z _
      apply Finset.sum_eq_zero; intro pt _; simp
    · have := sum3_single (fun Q z pt => if pt = dport L Q z then 0 else 1) (land l0) z0 (lport l0)
        (land l0 ≠ z0)
      show _ = if turning L l0 z0 then 1 else 0
      rw [show (if turning L l0 z0 then 1 else 0) =
        (if land l0 ≠ z0 then (if lport l0 = dport L (land l0) z0 then 0 else 1) else 0) by
          unfold turning
          by_cases h : land l0 = z0 <;> by_cases h' : lport l0 = dport L (land l0) z0 <;>
            simp [h, h'], ← this]
      refine Finset.sum_congr rfl fun Q _ => Finset.sum_congr rfl fun z _ =>
        Finset.sum_congr rfl fun pt _ => ?_
      by_cases h : land l0 ≠ z0 ∧ Q = land l0 ∧ pt = lport l0 ∧ z = z0
      · obtain ⟨h1, rfl, rfl, rfl⟩ := h
        simp [h1]
      · rw [if_neg h]
        split_ifs with h2 h3 <;> try rfl
        obtain ⟨h3, h4, h5, h6⟩ := h3
        cases h3
        exact absurd ⟨h5, h4, h6, rfl⟩ h
  have e3 : NS L G = ∑ Q, ∑ z, ∑ pt, (if pt = dport L Q z then 0 else G.stock Q pt z) := rfl
  rw [e0, e3, ← e1, ← e2]
  exact key

theorem turnCnt_pStage {n s : ℕ} [NeZero n] (td : TDims n k s q) (τ : ℕ) (G : PG k q) {u x : Sq k}
    (hux : u ≠ x) (kd : Kind) (y : Sq k) (m : Mode k) (sp : Pt) :
    (∑ x0, plcnt L s (pStage L s τ G u x kd y m sp) (fun l => turning L l x0)
        (fun g => gcl g = some x0)) + turnHd L (L.stage u x).1 (pgh k s G (L.stage u x).1 0) =
      (∑ x0, plcnt L s G (fun l => turning L l x0) (fun g => gcl g = some x0)) +
        (if kd ≠ .plh ∧ turning L (L.stage u x).1 x then 1 else 0) := by
  have h := fun x0 => plcnt_pStage L s τ td G hux kd y m sp (fun l => turning L l x0)
    (fun g => gcl g = some x0)
  have hs := Finset.sum_congr rfl (fun x0 (_ : x0 ∈ (univ : Finset (Sq k))) => h x0)
  simp only [sum_add_distrib] at hs
  have e1 : (∑ x0 : Sq k, if turning L (L.stage u x).1 x0 ∧
      gcl (pgh k s G (L.stage u x).1 0) = some x0 then 1 else 0) =
      turnHd L (L.stage u x).1 (pgh k s G (L.stage u x).1 0) := by
    unfold turnHd
    rcases gcl (pgh k s G (L.stage u x).1 0) with _ | z0
    · simp
    · rw [Finset.sum_eq_single z0]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
  have e2 : (∑ x0 : Sq k, if turning L (L.stage u x).1 x0 ∧
      gcl (some ((x, decide (kd ≠ .plh)), LaneSys.pdist (L.stage u x).1.2.t.val
        (L.stage u x).2.val)) = some x0 then 1 else 0) =
      (if kd ≠ .plh ∧ turning L (L.stage u x).1 x then 1 else 0) := by
    by_cases hk : kd = .plh
    · subst hk; simp [gcl]
    · simp only [hk, decide_true, gcl, ne_eq, not_false_eq_true, true_and, Option.some.injEq]
      rw [Finset.sum_eq_single x]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
  rw [e1, e2] at hs
  exact hs

end SlidingPuzzle.Port
