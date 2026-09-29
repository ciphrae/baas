import SlidingPuzzle.Port.Serve

/-! # The serve invariants through one stage -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle.Hub (Sq)
open SlidingPuzzle.Tree

variable {k q : ℕ} (L : LaneSys k q)

section fields
variable (s τ : ℕ) (G : PG k q) (u x : Sq k) (kd : Kind) (y : Sq k) (m : Mode k) (sp : Pt)
  (Q z : Sq k)

theorem pStage_dA : (pStage L s τ G u x kd y m sp).dA Q z = G.dA Q z +
    (if gdt (pgh k s G (L.stage u x).1 0) = some z ∧ Q = L.nxt u x then 1 else 0) := rfl

theorem pStage_B : (pStage L s τ G u x kd y m sp).B Q z = G.B Q z +
    (if kd = .plh ∧ Q = u ∧ z = x then 1 else 0) := rfl

theorem pStage_free : (pStage L s τ G u x kd y m sp).free Q z = G.free Q z -
    (if kd = .plh ∧ Q = u ∧ z = y then 1 else 0) +
    (if gcl (pgh k s G (L.stage u x).1 0) = none ∧ Q = L.nxt u x ∧
      z = G.σ.lane (L.stage u x).1 0 then 1 else 0) := rfl

theorem pStage_sched : (pStage L s τ G u x kd y m sp).sched Q z = G.sched Q z -
    (if kd = .sch ∧ Q = u ∧ z = y then 1 else 0) := rfl

end fields

section stage

variable {n s σ' : ℕ} [NeZero n] (td : TDims n k s q) {σ0 : PState k q} {F0 : ℕ} (τ : ℕ)

include td in
theorem pStage_Fcnt (G : PG k q) {u x : Sq k} (hux : u ≠ x) (kd : Kind) (y : Sq k) (m : Mode k)
    (sp : Pt) (v' x' : Sq k) :
    pFcnt L s (pStage L s τ G u x kd y m sp) v' x' +
        (if land (L.stage u x).1 = v' ∧ gtg (pgh k s G (L.stage u x).1 0) = some x' then 1 else 0) =
      pFcnt L s G v' x' + (if land (L.stage u x).1 = v' ∧ x' = x then 1 else 0) := by
  unfold pFcnt
  have h := plcnt_pStage L s τ td G hux kd y m sp (fun l => land l = v') (fun g => gtg g = some x')
  simp only [gtg, Option.map_some, Option.some.injEq] at h ⊢
  convert h using 3
  simp [eq_comm]

include td in
theorem pStage_Dpos (G : PG k q) {u x : Sq k} (hux : u ≠ x) (kd : Kind) (y : Sq k) (m : Mode k)
    (sp : Pt) (v' x' : Sq k) :
    pDpos L s (pStage L s τ G u x kd y m sp) v' x' +
        (if land (L.stage u x).1 = v' ∧ gdt (pgh k s G (L.stage u x).1 0) = some x' then 1 else 0) =
      pDpos L s G v' x' + (if land (L.stage u x).1 = v' ∧ kd = .plh ∧ x' = x then 1 else 0) := by
  unfold pDpos
  have h := plcnt_pStage L s τ td G hux kd y m sp (fun l => land l = v') (fun g => gdt g = some x')
  rw [h]
  congr 1
  cases kd <;> simp [gdt, eq_comm]

include td in
/-- The stock identity through one stage. -/
theorem pStage_ident {G : PG k q} {u x : Sq k} (hux : u ≠ x)
    {kd : Kind} {y : Sq k} {m : Mode k} {sp : Pt} (hr : PRoleOK G u x sp kd y)
    (hI : PIdent L s G x (L.pendB u x)) :
    PIdent L s (pStage L s τ G u x kd y m sp) x (pendA u kd) := by
  intro v' x' hvx
  have hF := pStage_Fcnt L td τ G hux kd y m sp v' x'
  have hsplit := gtg_split (pgh k s G (L.stage u x).1 0) x'
  have hI' := hI v' x' hvx
  have hvu : L.nxt u x ≠ u := nxt_ne L hux
  have hland : land (L.stage u x).1 = L.nxt u x := rfl
  rw [hland] at hF
  have hS := pStage_stk L s τ G u x kd y m sp (fun h => by subst h; exact hr.2) v' x'
  rw [pStage_dA, pStage_B]
  -- the pending terms
  have hpend : (if pendA u kd = some v' ∧ x' = x then 1 else 0) +
      (if L.nxt u x = v' ∧ x' = x then 1 else 0) =
      (if L.pendB u x = some v' ∧ x' = x then 1 else 0) +
      (if kd = Kind.plh ∧ v' = u ∧ x' = x then 1 else 0) +
      (if kd = Kind.stk ∧ v' = u ∧ x' = y then 1 else 0) := by
    by_cases hx : x' = x
    · subst hx
      have hy : kd = Kind.stk → y = x' := fun h => by subst h; exact hr.1
      by_cases hv : L.nxt u x' = x'
      · have hb : L.pendB u x' = none := by simp [LaneSys.pendB, hv]
        have : L.nxt u x' ≠ v' := by rw [hv]; exact Ne.symm hvx
        rw [hb]
        by_cases hvu' : v' = u
        · subst hvu'
          cases kd <;> simp [pendA, this, hy]
        · cases kd <;> simp [pendA, this, hvu', Ne.symm hvu']
      · have hb : L.pendB u x' = some (L.nxt u x') := by simp [LaneSys.pendB, hv]
        rw [hb]
        by_cases hvu' : v' = u
        · subst hvu'
          cases kd <;> simp [pendA, hvu, hy] <;> omega
        · cases kd <;> simp [pendA, hvu', Ne.symm hvu']
    · simp only [hx, and_false, if_false]
      cases kd <;> simp only [reduceCtorEq, false_and, if_false, true_and]
      · by_cases hh : v' = u ∧ x' = y
        · exfalso; exact hx (hh.2.trans hr.1)
        · rw [if_neg hh]
  have hcl : (if gcl (pgh k s G (L.stage u x).1 0) = some x' ∧ v' = L.nxt u x ∧ L.nxt u x ≠ x'
      then 1 else 0) = (if L.nxt u x = v' ∧ gcl (pgh k s G (L.stage u x).1 0) = some x'
      then 1 else 0) := by
    by_cases h : v' = L.nxt u x
    · subst h; simp [hvx, and_comm]
    · simp [h, Ne.symm h]
  have hdt : (if gdt (pgh k s G (L.stage u x).1 0) = some x' ∧ v' = L.nxt u x then 1 else 0) =
      (if L.nxt u x = v' ∧ gdt (pgh k s G (L.stage u x).1 0) = some x' then 1 else 0) := by
    by_cases h : v' = L.nxt u x
    · subst h; simp [and_comm]
    · simp [h, Ne.symm h]
  have hg3 : (if L.nxt u x = v' ∧ gtg (pgh k s G (L.stage u x).1 0) = some x' then 1 else 0) =
      (if L.nxt u x = v' ∧ gcl (pgh k s G (L.stage u x).1 0) = some x' then 1 else 0) +
      (if L.nxt u x = v' ∧ gdt (pgh k s G (L.stage u x).1 0) = some x' then 1 else 0) := by
    by_cases h : L.nxt u x = v'
    · simp only [h, true_and]; exact hsplit
    · simp [h]
  omega

include td in
/-- Dirty tiles through one stage. -/
theorem pStage_dirty {G : PG k q} {u x : Sq k} (hux : u ≠ x) {kd : Kind} {y : Sq k} {m : Mode k}
    {sp : Pt} (hD : PDirtyInv L s G) : PDirtyInv L s (pStage L s τ G u x kd y m sp) := by
  intro v' x'
  have hP := pStage_Dpos L td τ G hux kd y m sp v' x'
  have hD' := hD v' x'
  have hland : land (L.stage u x).1 = L.nxt u x := rfl
  rw [hland] at hP
  rw [pStage_dA]
  simp only [pStage_B]
  have hsum : ∑ w ∈ univ.filter (fun w => w ≠ x' ∧ L.nxt w x' = v'),
      (G.B w x' + if kd = Kind.plh ∧ w = u ∧ x' = x then 1 else 0) =
      (∑ w ∈ univ.filter (fun w => w ≠ x' ∧ L.nxt w x' = v'), G.B w x') +
        (if L.nxt u x = v' ∧ kd = Kind.plh ∧ x' = x then 1 else 0) := by
    rw [sum_add_distrib]
    congr 1
    by_cases h : kd = Kind.plh ∧ x' = x
    · obtain ⟨h1, rfl⟩ := h
      simp only [h1, true_and, and_true]
      rw [Finset.sum_ite_eq']
      simp only [mem_filter, mem_univ, true_and]
      by_cases hv : L.nxt u x' = v'
      · simp [hv, hux]
      · simp [hv]
    · have : ∀ w, ¬ (kd = Kind.plh ∧ w = u ∧ x' = x) := fun w h' => h ⟨h'.1, h'.2.2⟩
      simp only [this, if_false, sum_const_zero]
      rw [if_neg (fun h' => h ⟨h'.2.1, h'.2.2⟩)]
  have hdt : (if gdt (pgh k s G (L.stage u x).1 0) = some x' ∧ v' = L.nxt u x then 1 else 0) =
      (if L.nxt u x = v' ∧ gdt (pgh k s G (L.stage u x).1 0) = some x' then 1 else 0) := by
    by_cases h : v' = L.nxt u x
    · subst h; simp [and_comm]
    · simp [h, Ne.symm h]
  rw [hsum]
  omega

end stage

end SlidingPuzzle.Port
