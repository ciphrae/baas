import SlidingPuzzle.Tree.RunGhost

/-! # The local invariant through a hop stage and a jump -/
namespace SlidingPuzzle.Tree
open Finset
open SlidingPuzzle.Hub (Sq shiftIn incCnt decCnt incCnt_apply decCnt_apply shiftIn_of_lt
  shiftIn_self' shiftIn_of_gt)

variable {k q : ℕ} (L : LaneSys k q)

theorem sum_sum_ind (Z y : Sq k) :
    (∑ Q : Sq k, ∑ x : Sq k, if Q = Z ∧ x = y then 1 else 0) = 1 := by
  rw [Finset.sum_eq_single Z]
  · simp
  · intro Q _ hQ; simp [hQ]
  · simp

theorem sum_sum_ind_cond (c : Prop) [Decidable c] (Z y : Sq k) :
    (∑ Q : Sq k, ∑ x : Sq k, if c ∧ Q = Z ∧ x = y then 1 else 0) = if c then 1 else 0 := by
  by_cases hc : c
  · simp only [hc, true_and, if_true]; exact sum_sum_ind Z y
  · simp [hc]

/-- Removing and adding one indicator. -/
theorem sum_sum_sub_add (f : Sq k → Sq k → ℕ) (c d : Prop) [Decidable c] [Decidable d]
    (Z y E w : Sq k) (hf : c → 1 ≤ f Z y) :
    (∑ Q, ∑ x, (f Q x - (if c ∧ Q = Z ∧ x = y then 1 else 0) +
      (if d ∧ Q = E ∧ x = w then 1 else 0))) + (if c then 1 else 0) =
      (∑ Q, ∑ x, f Q x) + if d then 1 else 0 := by
  have h : ∀ Q x, (f Q x - (if c ∧ Q = Z ∧ x = y then 1 else 0) +
      (if d ∧ Q = E ∧ x = w then 1 else 0)) + (if c ∧ Q = Z ∧ x = y then 1 else 0) =
      f Q x + (if d ∧ Q = E ∧ x = w then 1 else 0) := by
    intro Q x
    split_ifs with h1 h2 h2 <;> try omega
    · obtain ⟨hc, rfl, rfl⟩ := h1; have := hf hc; omega
    · obtain ⟨hc, rfl, rfl⟩ := h1; have := hf hc; omega
  have e := Finset.sum_congr rfl fun Q (_ : Q ∈ Finset.univ) =>
    Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => h Q x
  simp only [sum_add_distrib] at e ⊢
  rw [sum_sum_ind_cond, sum_sum_ind_cond] at e
  rw [sum_sum_ind_cond]
  omega

theorem sum_sum_add_ind (f : Sq k → Sq k → ℕ) (c : Prop) [Decidable c] (Z y : Sq k) :
    (∑ Q, ∑ x, (f Q x + if c ∧ Q = Z ∧ x = y then 1 else 0)) =
      (∑ Q, ∑ x, f Q x) + if c then 1 else 0 := by
  simp only [sum_add_distrib]
  congr 1
  by_cases hc : c
  · simp only [hc, true_and, if_true]; exact sum_sum_ind Z y
  · simp [hc]

theorem arr_le {α : Type*} [DecidableEq α] (c : Option α) (hd v Q z : α)
    (hc : ∀ z0, c = some z0 → hd = z0) :
    (if c = some z ∧ Q = v ∧ v ≠ z then 1 else 0) + (if c = none ∧ Q = v ∧ z = hd then 1 else 0) ≤
      (if Q = v ∧ z = hd then 1 else 0) := by
  rcases c with _ | z0
  · simp
  · have := hc z0 rfl
    subst this
    simp only [Option.some.injEq, reduceCtorEq, false_and, if_false, add_zero]
    split_ifs with h1 h2 <;> first | omega | (exfalso; exact h2 ⟨h1.2.1, h1.1.symm⟩)

theorem arr_ge {α : Type*} [DecidableEq α] (c : Option α) (hd v Q z : α)
    (hc : ∀ z0, c = some z0 → hd = z0) (hzQ : z ≠ Q) :
    (if Q = v ∧ z = hd then 1 else 0) ≤
      (if c = some z ∧ Q = v ∧ v ≠ z then 1 else 0) + (if c = none ∧ Q = v ∧ z = hd then 1 else 0) := by
  rcases c with _ | z0
  · simp
  · have := hc z0 rfl
    subst this
    simp only [Option.some.injEq, reduceCtorEq, false_and, if_false, add_zero]
    by_cases h1 : Q = v ∧ z = hd
    · obtain ⟨rfl, rfl⟩ := h1
      rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl, fun e => hzQ e.symm⟩]
    · rw [if_neg h1]; exact Nat.zero_le _

section stage

variable {n s : ℕ} [NeZero n] (td : TDims n k s q) {σ0 : IState k q} {F0 : ℕ} (τ : ℕ)

/-- The counts after a hop stage. -/
theorem gStage_cnt (G : GS k q) {u x : Sq k} (hux : u ≠ x) (kd : Kind) (y Q z : Sq k) :
    (gStage L s τ G u x kd y).σ.cnt Q z = G.σ.cnt Q z - (if Q = u ∧ z = y then 1 else 0) +
      (if Q = L.nxt u x ∧ z = G.σ.lane (L.stage u x).1 0 then 1 else 0) := by
  simp only [gStage, step_hopEv_cnt, incCnt_apply, decCnt_apply, stage_src hux, land_stage]

include td in
theorem gStage_linv {G : GS k q} (hL : LInv L s σ0 F0 G) {u x : Sq k} (hux : u ≠ x)
    (hb : G.σ.blank = L.nxt u x) {kd : Kind} {y : Sq k} (hr : RoleOK G u x kd y) :
    LInv L s σ0 F0 (gStage L s τ G u x kd y) := by
  have hin : LIn L (L.stage u x).1.2 (L.stage u x).2 := stage_in hux
  have hsrc : src (L.stage u x).1 (L.stage u x).2 = u := stage_src hux
  have hvu : L.nxt u x ≠ u := nxt_ne L hux
  have hgood : lgood (L.stage u x).1 x := stage_good hux
  have hp := lpos_lt L s td (L.stage u x).1 (L.stage u x).2 hin
  have hll := llen_le L s (L.stage u x).1
  have hgs := gh_gStage L s τ G u x kd y
  have hlane := step_hopEv_lane s G.σ (L.stage u x).1 (L.stage u x).2 y
  have hrole : 1 ≤ G.sched u y + G.stock u y + G.free u y := by
    cases kd <;> simp only [RoleOK] at hr <;> omega
  have hcnt1 : 1 ≤ G.σ.cnt u y := le_trans hrole (hL.roles_le u y)
  have hpre : G.σ.Pre L (hopEv (L.stage u x).1 (L.stage u x).2 y) := by
    rw [pre_hopEv]; exact ⟨hb, hin, by rw [hsrc]; exact hcnt1⟩
  obtain ⟨hrun, hval⟩ := pre_append L hL hpre
  have hclean : ∀ z, gcl (gh k s G (L.stage u x).1 0) = some z →
      G.σ.lane (L.stage u x).1 0 = z := by
    intro z hz
    rcases hgv : gh k s G (L.stage u x).1 0 with _ | ⟨⟨x', b⟩, d'⟩
    · rw [hgv] at hz; cases hz
    · rw [hgv] at hz
      cases b
      · cases hz
      · simp only [gcl, Option.some.injEq] at hz
        subst hz
        exact hL.ghost_clean _ 0 _ d' hgv
  have hdec : ∀ Q z, (if kd = Kind.sch ∧ Q = u ∧ z = y then 1 else 0) +
      (if kd = Kind.stk ∧ Q = u ∧ z = y then 1 else 0) +
      (if kd = Kind.plh ∧ Q = u ∧ z = y then 1 else 0) = (if Q = u ∧ z = y then 1 else 0) := by
    intro Q z; cases kd <;> simp
  have r1 : ∀ Q z, (if kd = Kind.sch ∧ Q = u ∧ z = y then 1 else 0) ≤ G.sched Q z := by
    intro Q z; split_ifs with h
    · obtain ⟨rfl, rfl, rfl⟩ := h; simp only [RoleOK] at hr; exact hr.2
    · exact Nat.zero_le _
  have r2 : ∀ Q z, (if kd = Kind.stk ∧ Q = u ∧ z = y then 1 else 0) ≤ G.stock Q z := by
    intro Q z; split_ifs with h
    · obtain ⟨rfl, rfl, rfl⟩ := h; simp only [RoleOK] at hr; exact hr.2
    · exact Nat.zero_le _
  have r3 : ∀ Q z, (if kd = Kind.plh ∧ Q = u ∧ z = y then 1 else 0) ≤ G.free Q z := by
    intro Q z; split_ifs with h
    · obtain ⟨rfl, rfl, rfl⟩ := h; simp only [RoleOK] at hr; exact hr
    · exact Nat.zero_le _
  refine ⟨?_, ?_, ?_, ?_, ?_, hrun, hval, ?_, ?_⟩
  · -- roles bounded by counts
    intro Q z
    rw [gStage_cnt L τ G hux, ← land_stage]
    have base := hL.roles_le Q z
    have hin1 := arr_le (gcl (gh k s G (L.stage u x).1 0)) (G.σ.lane (L.stage u x).1 0)
      (land (L.stage u x).1) Q z hclean
    have := hdec Q z; have := r1 Q z; have := r2 Q z; have := r3 Q z
    have hc1 : (if Q = u ∧ z = y then 1 else 0) ≤ G.sched Q z + G.stock Q z + G.free Q z := by
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h; exact hrole
      · exact Nat.zero_le _
    simp only [gStage]
    omega
  · -- every non-home tile has a role
    intro Q z hzQ
    rw [gStage_cnt L τ G hux, ← land_stage]
    have base := hL.roles_ge Q z hzQ
    have hin1 := arr_ge (gcl (gh k s G (L.stage u x).1 0)) (G.σ.lane (L.stage u x).1 0)
      (land (L.stage u x).1) Q z hclean hzQ
    have := hdec Q z; have := r1 Q z; have := r2 Q z; have := r3 Q z
    have hc1 : (if Q = u ∧ z = y then 1 else 0) ≤ G.σ.cnt Q z := by
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h; exact hcnt1
      · exact Nat.zero_le _
    simp only [gStage]
    omega
  · -- stock is never held for the square's own class
    intro Q
    simp only [gStage]
    have := hL.stock_diag Q
    have : ¬ (gcl (gh k s G (L.stage u x).1 0) = some Q ∧ Q = land (L.stage u x).1 ∧
        land (L.stage u x).1 ≠ Q) := fun h => h.2.2 h.2.1.symm
    rw [if_neg this]; omega
  · -- clean ghost entries are tiles of their tag
    intro l' r x' d' h'
    rw [hgs] at h'
    show (G.σ.step s (hopEv (L.stage u x).1 (L.stage u x).2 y)).lane l' r = x'
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
  · -- cost
    have hc := cost_append L hL (hopEv (L.stage u x).1 (L.stage u x).2 y)
    have hk := cost_hopEv s G.σ (L.stage u x).1 (L.stage u x).2 y
    have hpot := pot_hopEv L s td G.σ (L.stage u x).1 (L.stage u x).2 hin y
    have hB : (∑ Q, ∑ z, (gStage L s τ G u x kd y).B Q z) =
        (∑ Q, ∑ z, G.B Q z) + (if kd = Kind.plh then 1 else 0) := by
      simp only [gStage]
      exact sum_sum_add_ind G.B _ u x
    have hjunk : (if ¬ lgood (L.stage u x).1 y then lpos k s (L.stage u x).1 (L.stage u x).2 + 1
        else 0) ≤ (k * s) * (if kd = Kind.plh then 1 else 0) := by
      cases kd
      · simp only [RoleOK] at hr
        rw [hr.1, if_neg (not_not.mpr hgood)]; simp
      · simp only [RoleOK] at hr
        rw [hr.1, if_neg (not_not.mpr hgood)]; simp
      · simp only [if_true, mul_one]; split_ifs <;> omega
    have hmul : hopK k q s * (G.nh + 1) = hopK k q s * G.nh + hopK k q s := by ring
    have hmul2 : (k * s) * ((∑ Q, ∑ z, G.B Q z) + (if kd = Kind.plh then 1 else 0)) =
        (k * s) * (∑ Q, ∑ z, G.B Q z) + (k * s) * (if kd = Kind.plh then 1 else 0) := by ring
    have hL' := hL.cost
    show σ0.totalCost s (G.evs ++ [hopEv (L.stage u x).1 (L.stage u x).2 y]) +
        (G.σ.step s (hopEv (L.stage u x).1 (L.stage u x).2 y)).pot L s ≤
      σ0.pot L s + hopK k q s * (G.nh + 1) +
        (k * s) * (∑ Q, ∑ z, (gStage L s τ G u x kd y).B Q z) + G.jc
    rw [hc, hB, hmul, hmul2]
    omega
  · -- free tiles, untagged positions and placeholders
    have hu := lcnt_gStage L s τ td G hux kd y (fun _ => True) (fun g => g = none)
    simp only [true_and, reduceCtorEq, if_false, add_zero] at hu
    have hF := sum_sum_sub_add G.free (kd = Kind.plh) (gcl (gh k s G (L.stage u x).1 0) = none)
      u y (land (L.stage u x).1) (G.σ.lane (L.stage u x).1 0)
      (fun h => by have := r3 u y; rw [if_pos ⟨h, rfl, rfl⟩] at this; exact this)
    have hB : (∑ Q, ∑ z, (gStage L s τ G u x kd y).B Q z) =
        (∑ Q, ∑ z, G.B Q z) + (if kd = Kind.plh then 1 else 0) := by
      simp only [gStage]
      exact sum_sum_add_ind G.B _ u x
    have hA : (∑ Q, ∑ z, (gStage L s τ G u x kd y).dA Q z) =
        (∑ Q, ∑ z, G.dA Q z) + (if gdt (gh k s G (L.stage u x).1 0) = none then 0 else 1) := by
      simp only [gStage, sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
      rcases hg : gdt (gh k s G (L.stage u x).1 0) with _ | z0
      · simp
      · rw [Finset.sum_eq_single z0]
        · simp
        · intro z _ hz; simp [Ne.symm hz]
        · simp
    have hcls : (if gcl (gh k s G (L.stage u x).1 0) = none then 1 else 0) =
        (if gh k s G (L.stage u x).1 0 = none then 1 else 0) +
          (if gdt (gh k s G (L.stage u x).1 0) = none then 0 else 1) := by
      rcases gh k s G (L.stage u x).1 0 with _ | ⟨⟨x', b⟩, d'⟩
      · simp [gcl, gdt]
      · cases b <;> simp [gcl, gdt]
    have hfr : (∑ Q, ∑ z, (gStage L s τ G u x kd y).free Q z) =
        ∑ Q, ∑ z, (G.free Q z - (if kd = Kind.plh ∧ Q = u ∧ z = y then 1 else 0) +
          (if gcl (gh k s G (L.stage u x).1 0) = none ∧ Q = land (L.stage u x).1 ∧
            z = G.σ.lane (L.stage u x).1 0 then 1 else 0)) := rfl
    have hut : untagged L s (gStage L s τ G u x kd y) + (if gh k s G (L.stage u x).1 0 = none
        then 1 else 0) = untagged L s G := hu
    have ht := hL.free_tot
    unfold untagged at hut ht ⊢
    omega

end stage

section jump

variable {s : ℕ} {σ0 : IState k q} {F0 : ℕ}

theorem gJump_linv {G : GS k q} (hL : LInv L s σ0 F0 G) {E Z y : Sq k} (hb : G.σ.blank = E)
    (hEZ : E ≠ Z) (hal : E.1 = Z.1 ∨ E.2 = Z.2) (hf : 1 ≤ G.free Z y) :
    LInv L s σ0 F0 (gJump s G E Z y) := by
  have hcnt1 : 1 ≤ G.σ.cnt Z y := by have := hL.roles_le Z y; omega
  have hpre : G.σ.Pre L (.jump E Z y) := ⟨hb, hEZ, hal, hcnt1⟩
  obtain ⟨hrun, hval⟩ := pre_append L hL hpre
  have hcnt : ∀ Q x, (gJump s G E Z y).σ.cnt Q x = G.σ.cnt Q x -
      (if Q = Z ∧ x = y then 1 else 0) + (if Q = E ∧ x = y then 1 else 0) := by
    intro Q x; simp only [gJump, IState.step, incCnt_apply, decCnt_apply]
  have hlane : (gJump s G E Z y).σ.lane = G.σ.lane := rfl
  have hgh : gh k s (gJump s G E Z y) = gh k s G := rfl
  have hZ : ∀ Q x, (if Q = Z ∧ x = y then 1 else 0) ≤ G.free Q x := by
    intro Q x; split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; exact hf
    · exact Nat.zero_le _
  have hZc : ∀ Q x, (if Q = Z ∧ x = y then 1 else 0) ≤ G.σ.cnt Q x := by
    intro Q x; split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; exact hcnt1
    · exact Nat.zero_le _
  refine ⟨?_, ?_, hL.stock_diag, ?_, ?_, hrun, hval, ?_, ?_⟩
  · intro Q x
    rw [hcnt]
    have := hL.roles_le Q x; have := hZ Q x
    simp only [gJump]; omega
  · intro Q x hx
    rw [hcnt]
    have := hL.roles_ge Q x hx; have := hZ Q x; have := hZc Q x
    simp only [gJump]; omega
  · intro l r x d h; rw [hlane]; rw [hgh] at h; exact hL.ghost_clean l r x d h
  · intro l r h; rw [hgh] at h; exact hL.ghost_len l r h
  · have hc := cost_append L hL (.jump E Z y)
    have hL' := hL.cost
    show σ0.totalCost s (G.evs ++ [.jump E Z y]) + (G.σ.step s (.jump E Z y)).pot L s ≤
      σ0.pot L s + hopK k q s * G.nh + (k * s) * (∑ Q, ∑ x, G.B Q x) +
        (G.jc + G.σ.cost s (.jump E Z y))
    have hp : (G.σ.step s (.jump E Z y)).pot L s = G.σ.pot L s := rfl
    rw [hc, hp]; omega
  · have hF := sum_sum_sub_add G.free True True Z y E y (fun _ => hf)
    simp only [true_and, if_true] at hF
    have ht := hL.free_tot
    have hu : untagged L s (gJump s G E Z y) = untagged L s G := rfl
    show (∑ Q, ∑ x, (G.free Q x - (if Q = Z ∧ x = y then 1 else 0) +
      (if Q = E ∧ x = y then 1 else 0))) + untagged L s (gJump s G E Z y) +
        (∑ Q, ∑ x, G.B Q x) = F0 + ∑ Q, ∑ x, G.dA Q x
    rw [hu]; omega

end jump

end SlidingPuzzle.Tree
