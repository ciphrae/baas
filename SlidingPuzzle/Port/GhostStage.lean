import SlidingPuzzle.Port.GhostLocal

/-! # The local invariant through a hop stage -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle.Hub (Sq shiftIn incCnt decCnt shiftIn_of_lt shiftIn_self' shiftIn_of_gt)
open SlidingPuzzle.Tree

variable {k q : ℕ} (L : LaneSys k q)

section stage

variable {n s σ' : ℕ} [NeZero n] (td : TDims n k s q) {σ0 : PState k q} {F0 : ℕ} (τ : ℕ)

include td in
theorem pStage_linv {G : PG k q} (hL : PLInv L s σ' σ0 F0 G) {u x : Sq k} (hux : u ≠ x)
    (hb : G.σ.blank = L.nxt u x) (hbp : G.σ.bp = dport L u x) {kd : Kind} {y : Sq k} {m : Mode k}
    {sp : Pt} (hr : PRoleOK G u x sp kd y) (hm : GoodMode L G u x kd y sp m) :
    PLInv L s σ' σ0 F0 (pStage L s τ G u x kd y m sp) := by
  have hin : LIn L (L.stage u x).1.2 (L.stage u x).2 := stage_in hux
  have hsrc : src (L.stage u x).1 (L.stage u x).2 = u := stage_src hux
  have hvu : (L.nxt u x) ≠ u := nxt_ne L hux
  have hgood : lgood (L.stage u x).1 x := stage_good hux
  have hp := lposP_lt L td (L.stage u x).1 (L.stage u x).2 hin
  have hll := llen_le L s (L.stage u x).1
  have hgs := pgh_pStage L s τ G u x kd y m sp
  have hlane := step_hop_lane s G.σ (L.stage u x).1 (L.stage u x).2 y m
  have hlport : lport (L.stage u x).1 = (dport L u x) := rfl
  have hstk_role : kd = .stk → 1 ≤ G.stock u sp y := fun h => by
    subst h; exact hr.2
  have hrole : 1 ≤ G.sched u y + G.stk u y + G.free u y := by
    cases kd
    · have := hr.2; omega
    · have h1 := hr.2
      have : G.stock u sp y ≤ G.stk u y :=
        Finset.single_le_sum (f := fun pt => G.stock u pt y) (fun _ _ => Nat.zero_le _) (mem_univ sp)
      omega
    · have := hr; simp only [PRoleOK] at this; omega
  have hcnt1 : 1 ≤ G.σ.cnt u y := le_trans hrole (hL.roles_le u y)
  -- the mode's precondition
  have hmode : G.σ.ModeOK u (dport L u x) y m := by
    cases m with
    | cheap => exact hm.1
    | imp p z =>
      obtain ⟨h1, h2, h3⟩ := hm
      exact ⟨h1, lt_of_le_of_lt (Nat.zero_le _) h2, lt_of_le_of_lt (Nat.zero_le _) h3⟩
  have hpre : G.σ.Pre L (.hop (L.stage u x).1 (L.stage u x).2 y m) := by
    refine ⟨hb, hbp, hin, ?_⟩
    rw [hsrc]; exact hmode
  obtain ⟨hrun, hval⟩ := ppre_append L hL hpre
  have hclean : ∀ z, gcl (pgh k s G (L.stage u x).1 0) = some z → (G.σ.lane (L.stage u x).1 0) = z := by
    intro z hz
    rcases hgv : pgh k s G (L.stage u x).1 0 with _ | ⟨⟨x', b⟩, d'⟩
    · rw [hgv] at hz; cases hz
    · rw [hgv] at hz
      cases b
      · cases hz
      · simp only [gcl, Option.some.injEq] at hz
        subst hz
        exact hL.ghost_clean _ 0 _ d' hgv
  have hstk := pStage_stk L s τ G u x kd y m sp hstk_role
  have hsch : ∀ Q z, (pStage L s τ G u x kd y m sp).sched Q z =
      G.sched Q z - (if kd = .sch ∧ Q = u ∧ z = y then 1 else 0) := fun _ _ => rfl
  have hfree : ∀ Q z, (pStage L s τ G u x kd y m sp).free Q z =
      G.free Q z - (if kd = .plh ∧ Q = u ∧ z = y then 1 else 0) +
      (if gcl (pgh k s G (L.stage u x).1 0) = none ∧ Q = L.nxt u x ∧
        z = G.σ.lane (L.stage u x).1 0 then 1 else 0) := fun _ _ => rfl
  have hcnt := pStage_cnt L s τ G hux kd y m sp
  have hpc := pStage_pc L s τ G hux kd y m sp
  have hdec : ∀ Q z, (if kd = Kind.sch ∧ Q = u ∧ z = y then 1 else 0) +
      (if kd = Kind.stk ∧ Q = u ∧ z = y then 1 else 0) +
      (if kd = Kind.plh ∧ Q = u ∧ z = y then 1 else 0) = (if Q = u ∧ z = y then 1 else 0) := by
    intro Q z; cases kd <;> simp
  have r1 : ∀ Q z, (if kd = Kind.sch ∧ Q = u ∧ z = y then 1 else 0) ≤ G.sched Q z := by
    intro Q z; split_ifs with h
    · obtain ⟨h1, rfl, rfl⟩ := h; subst h1; exact hr.2
    · exact Nat.zero_le _
  have r2 : ∀ Q z, (if kd = Kind.stk ∧ Q = u ∧ z = y then 1 else 0) ≤ G.stk Q z := by
    intro Q z; split_ifs with h
    · obtain ⟨h1, rfl, rfl⟩ := h
      have := hstk_role h1
      have : G.stock Q sp z ≤ G.stk Q z :=
        Finset.single_le_sum (f := fun pt => G.stock Q pt z) (fun _ _ => Nat.zero_le _) (mem_univ sp)
      omega
    · exact Nat.zero_le _
  have r3 : ∀ Q z, (if kd = Kind.plh ∧ Q = u ∧ z = y then 1 else 0) ≤ G.free Q z := by
    intro Q z; split_ifs with h
    · obtain ⟨h1, rfl, rfl⟩ := h; subst h1; exact hr
    · exact Nat.zero_le _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrun, hval, ?_, ?_⟩
  · -- roles bounded by counts
    intro Q z
    rw [hcnt]
    have base := hL.roles_le Q z
    have hin1 := arr_le (gcl (pgh k s G (L.stage u x).1 0)) (G.σ.lane (L.stage u x).1 0) (L.nxt u x) Q z hclean
    have := hdec Q z; have := r1 Q z; have := r2 Q z; have := r3 Q z
    have := hstk Q z
    have hc1 : (if Q = u ∧ z = y then 1 else 0) ≤ G.sched Q z + G.stk Q z + G.free Q z := by
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h; exact hrole
      · exact Nat.zero_le _
    rw [hsch Q z, hfree Q z]
    omega
  · -- every non-home tile has a role
    intro Q z hzQ
    rw [hcnt]
    have base := hL.roles_ge Q z hzQ
    have hin1 := arr_ge (gcl (pgh k s G (L.stage u x).1 0)) (G.σ.lane (L.stage u x).1 0) (L.nxt u x) Q z hclean hzQ
    have := hdec Q z; have := r1 Q z; have := r2 Q z; have := r3 Q z
    have := hstk Q z
    have hc1 : (if Q = u ∧ z = y then 1 else 0) ≤ G.σ.cnt Q z := by
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h; exact hcnt1
      · exact Nat.zero_le _
    rw [hsch Q z, hfree Q z]
    omega
  · -- stock is never held for the square's own class
    intro Q pt'
    simp only [pStage]
    have := hL.stock_diag Q pt'
    have : ¬ (gcl (pgh k s G (L.stage u x).1 0) = some Q ∧ Q = land (L.stage u x).1 ∧ land (L.stage u x).1 ≠ Q ∧ pt' = lport (L.stage u x).1) :=
      fun h => h.2.2.1 h.2.1.symm
    rw [if_neg this]; omega
  · -- clean ghost entries are tiles of their tag
    intro l' r x' d' h'
    rw [hgs] at h'
    show (G.σ.step s (.hop (L.stage u x).1 (L.stage u x).2 y m)).lane l' r = x'
    rw [hlane]
    by_cases hl' : l' = (L.stage u x).1
    · subst hl'
      rw [Function.update_self] at h' ⊢
      unfold shiftIn at h' ⊢
      split_ifs at h' ⊢ with h1 h2
      · exact hL.ghost_clean _ _ _ _ h'
      · simp only [Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at h'
        obtain ⟨⟨rfl, hk⟩, -⟩ := h'
        cases kd with
        | sch => exact hr.1
        | stk => exact hr.1
        | plh => exact absurd rfl hk
      · exact hL.ghost_clean _ _ _ _ h'
    · rw [Function.update_of_ne hl'] at h' ⊢
      exact hL.ghost_clean _ _ _ _ h'
  · -- ghost entries lie inside their lanes
    intro l' r h'
    rw [hgs] at h'
    by_cases hl' : l' = (L.stage u x).1
    · subst hl'
      rw [Function.update_self] at h'
      unfold shiftIn at h'
      split_ifs at h' with h1 h2
      · exact lt_trans h1 hp
      · rw [h2]; exact hp
      · exact hL.ghost_len _ _ h'
    · rw [Function.update_of_ne hl'] at h'
      exact hL.ghost_len _ _ h'
  · -- port counts within region counts
    sorry
  · -- port sizes
    sorry
  · -- stock of the next hop's port stays in that port
    sorry
  · -- cost
    have hc := pcost_append L hL (.hop (L.stage u x).1 (L.stage u x).2 y m)
    have hpot := pot_hop L td G.σ (L.stage u x).1 (L.stage u x).2 hin y m
    have hB : (∑ Q, ∑ z, (pStage L s τ G u x kd y m sp).B Q z) =
        (∑ Q, ∑ z, G.B Q z) + (if kd = Kind.plh then 1 else 0) := by
      simp only [pStage]
      exact sum_sum_add_ind G.B _ u x
    have hjunk : (if ¬ lgood (L.stage u x).1 y then lposP k s (L.stage u x).1 (L.stage u x).2 + 1 else 0) ≤
        (k * s) * (if kd = Kind.plh then 1 else 0) := by
      cases kd
      · rw [hr.1, if_neg (not_not.mpr hgood)]; simp
      · rw [hr.1, if_neg (not_not.mpr hgood)]; simp
      · simp only [if_true, mul_one]; split_ifs <;> omega
    have hL' := hL.cost
    show σ0.totalCost s σ' (G.evs ++ [.hop (L.stage u x).1 (L.stage u x).2 y m]) +
        (G.σ.step s (.hop (L.stage u x).1 (L.stage u x).2 y m)).pot L s ≤
      σ0.pot L s + hopKc k q σ' * (G.nh + 1) +
        hopKi k s σ' * (G.ni + m.ind) +
        xferK k s σ' * G.nx + (k * s) * (∑ Q, ∑ z, (pStage L s τ G u x kd y m sp).B Q z) + G.jc
    rw [hc, hB]
    have hcost : G.σ.cost s σ' (.hop (L.stage u x).1 (L.stage u x).2 y m) = hopKc k q σ' + G.σ.ljunk (L.stage u x).1 (lposP k s (L.stage u x).1 (L.stage u x).2) +
        hopKi k s σ' * m.ind := by
      cases m <;> simp [PState.cost, Mode.ind]
    rw [hcost]
    have e1 : hopKc k q σ' * (G.nh + 1) = hopKc k q σ' * G.nh + hopKc k q σ' := by ring
    have e2 : hopKi k s σ' * (G.ni + m.ind) = hopKi k s σ' * G.ni + hopKi k s σ' * m.ind := by ring
    have e3 : (k * s) * ((∑ Q, ∑ z, G.B Q z) + (if kd = Kind.plh then 1 else 0)) =
        (k * s) * (∑ Q, ∑ z, G.B Q z) + (k * s) * (if kd = Kind.plh then 1 else 0) := by ring
    rw [e1, e2, e3]
    omega
  · -- free tiles, untagged positions and placeholders
    have hu := plcnt_pStage L s τ td G hux kd y m sp (fun _ => True) (fun g => g = none)
    simp only [true_and, reduceCtorEq, if_false, add_zero] at hu
    have hF := sum_sum_sub_add G.free (kd = Kind.plh) (gcl (pgh k s G (L.stage u x).1 0) = none)
      u y (land (L.stage u x).1) (G.σ.lane (L.stage u x).1 0)
      (fun h => by have := r3 u y; rw [if_pos ⟨h, rfl, rfl⟩] at this; exact this)
    have hB : (∑ Q, ∑ z, (pStage L s τ G u x kd y m sp).B Q z) =
        (∑ Q, ∑ z, G.B Q z) + (if kd = Kind.plh then 1 else 0) := by
      simp only [pStage]
      exact sum_sum_add_ind G.B _ u x
    have hA : (∑ Q, ∑ z, (pStage L s τ G u x kd y m sp).dA Q z) =
        (∑ Q, ∑ z, G.dA Q z) + (if gdt (pgh k s G (L.stage u x).1 0) = none then 0 else 1) := by
      simp only [pStage, sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
      rcases hg : gdt (pgh k s G (L.stage u x).1 0) with _ | z0
      · simp
      · rw [Finset.sum_eq_single z0]
        · simp
        · intro z _ hz; simp [Ne.symm hz]
        · simp
    have hcls : (if gcl (pgh k s G (L.stage u x).1 0) = none then 1 else 0) =
        (if pgh k s G (L.stage u x).1 0 = none then 1 else 0) +
          (if gdt (pgh k s G (L.stage u x).1 0) = none then 0 else 1) := by
      rcases pgh k s G (L.stage u x).1 0 with _ | ⟨⟨x', b⟩, d'⟩
      · simp [gcl, gdt]
      · cases b <;> simp [gcl, gdt]
    have hfr : (∑ Q, ∑ z, (pStage L s τ G u x kd y m sp).free Q z) =
        ∑ Q, ∑ z, (G.free Q z - (if kd = Kind.plh ∧ Q = u ∧ z = y then 1 else 0) +
          (if gcl (pgh k s G (L.stage u x).1 0) = none ∧ Q = land (L.stage u x).1 ∧ z = (G.σ.lane (L.stage u x).1 0) then 1 else 0)) := rfl
    have hut : puntagged L s (pStage L s τ G u x kd y m sp) + (if pgh k s G (L.stage u x).1 0 = none
        then 1 else 0) = puntagged L s G := hu
    have ht := hL.free_tot
    unfold puntagged at hut ht ⊢
    omega

end stage

end SlidingPuzzle.Port
