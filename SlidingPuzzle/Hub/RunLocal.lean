import SlidingPuzzle.Hub.RunGhost

/-! # The local invariant is preserved by the three ghost operations

For each operation: junk count and potential after the step, preservation of
`LInv` (under the role preconditions), and the exact cost identity
`totalCost + pot` grows by the fixed part of the operation's cost. -/
namespace SlidingPuzzle.Hub

open Finset

variable {k : ℕ}

section junk

variable (s : ℕ)

theorem junkCnt_hop1 (σ : IState k) {S h y : Sq k} (hS : S.2 ≠ h.2) (hy : y.2 = h.2)
    (hs : k + 1 ≤ s) :
    junkCnt s (σ.step s (.hop1 S h y)) +
        (if (σ.row (hop1Half S h) 0).2 ≠ h.2 then 1 else 0) = junkCnt s σ := by
  unfold junkCnt
  have hcol : ∑ V, junkC s (σ.step s (.hop1 S h y)) V = ∑ V, junkC s σ V := rfl
  rw [hcol]
  have hsum := sum_update_add
    (fun (H : RowH k) (f : ℕ → Sq k) =>
      ((range (rowLen k s H)).filter fun q => (f q).2 ≠ H.2.1).card)
    σ.row (hop1Half S h) (shiftIn (σ.row (hop1Half S h)) (hop1Pos s S h) y)
  have hc := card_filter_shiftIn (fun a : Sq k => a.2 ≠ (hop1Half S h).2.1)
    (σ.row (hop1Half S h)) (hop1Pos_lt hS hs) y
  have hyn : ¬ (y.2 ≠ (hop1Half S h).2.1) := by simp [hop1Half, hy]
  rw [if_neg hyn] at hc
  have e : ∑ H, junkR s (σ.step s (.hop1 S h y)) H =
      ∑ H, ((range (rowLen k s H)).filter fun q =>
        ((Function.update σ.row (hop1Half S h)
          (shiftIn (σ.row (hop1Half S h)) (hop1Pos s S h) y) H) q).2 ≠ H.2.1).card := rfl
  have e2 : ∑ H, junkR s σ H =
      ∑ H, ((range (rowLen k s H)).filter fun q => (σ.row H q).2 ≠ H.2.1).card := rfl
  rw [e, e2]
  have : (hop1Half S h).2.1 = h.2 := rfl
  rw [this] at hc hsum
  omega

theorem pot_hop1 (σ : IState k) {S h y : Sq k} (hS : S.2 ≠ h.2) (hy : y.2 = h.2)
    (hs : k + 1 ≤ s) :
    pot s (σ.step s (.hop1 S h y)) + σ.junkRow (hop1Half S h) (hop1Pos s S h) = pot s σ := by
  unfold pot
  have hcol : ∑ V, potC s (σ.step s (.hop1 S h y)) V = ∑ V, potC s σ V := rfl
  rw [hcol]
  have hsum := sum_update_add
    (fun (H : RowH k) (f : ℕ → Sq k) =>
      ∑ q ∈ (range (rowLen k s H)).filter (fun q => (f q).2 ≠ H.2.1), (q + 1))
    σ.row (hop1Half S h) (shiftIn (σ.row (hop1Half S h)) (hop1Pos s S h) y)
  have hyn : ¬ (y.2 ≠ (hop1Half S h).2.1) := by simp [hop1Half, hy]
  have hc := sum_filter_shiftIn (fun a : Sq k => a.2 ≠ (hop1Half S h).2.1)
    (σ.row (hop1Half S h)) (hop1Pos_lt hS hs) hyn
  have e : ∑ H, potR s (σ.step s (.hop1 S h y)) H =
      ∑ H, ∑ q ∈ (range (rowLen k s H)).filter (fun q =>
        ((Function.update σ.row (hop1Half S h)
          (shiftIn (σ.row (hop1Half S h)) (hop1Pos s S h) y) H) q).2 ≠ H.2.1), (q + 1) := rfl
  have e2 : ∑ H, potR s σ H =
      ∑ H, ∑ q ∈ (range (rowLen k s H)).filter (fun q => (σ.row H q).2 ≠ H.2.1), (q + 1) := rfl
  have e3 : σ.junkRow (hop1Half S h) (hop1Pos s S h) =
      ((range (hop1Pos s S h + 1)).filter
        fun q => (σ.row (hop1Half S h) q).2 ≠ (hop1Half S h).2.1).card := rfl
  rw [e, e2, e3]
  omega

theorem junkCnt_hop2 (σ : IState k) {h D : Sq k} (hD : h.1 ≠ D.1) (hs : k + 1 ≤ s) :
    junkCnt s (σ.step s (.hop2 h D D)) +
        (if σ.col (hop2Half h D) 0 ≠ D then 1 else 0) = junkCnt s σ := by
  unfold junkCnt
  have hrow : ∑ H, junkR s (σ.step s (.hop2 h D D)) H = ∑ H, junkR s σ H := rfl
  rw [hrow]
  have hsum := sum_update_add
    (fun (V : ColH k) (f : ℕ → Sq k) =>
      ((range (colLen k s V)).filter fun q => f q ≠ (V.2.1, V.1)).card)
    σ.col (hop2Half h D) (shiftIn (σ.col (hop2Half h D)) (hop2Pos s h D) D)
  have hc := card_filter_shiftIn (fun a : Sq k => a ≠ ((hop2Half h D).2.1, (hop2Half h D).1))
    (σ.col (hop2Half h D)) (hop2Pos_lt hD hs) D
  have hD' : ((hop2Half h D).2.1, (hop2Half h D).1) = D := rfl
  rw [hD'] at hc
  simp only [ne_eq, not_true_eq_false, if_false, add_zero] at hc
  have e : ∑ V, junkC s (σ.step s (.hop2 h D D)) V =
      ∑ V, ((range (colLen k s V)).filter fun q =>
        (Function.update σ.col (hop2Half h D)
          (shiftIn (σ.col (hop2Half h D)) (hop2Pos s h D) D) V) q ≠ (V.2.1, V.1)).card := rfl
  have e2 : ∑ V, junkC s σ V =
      ∑ V, ((range (colLen k s V)).filter fun q => σ.col V q ≠ (V.2.1, V.1)).card := rfl
  rw [e, e2]
  simp only [hD', ne_eq] at hsum hc ⊢
  omega

theorem pot_hop2 (σ : IState k) {h D : Sq k} (hD : h.1 ≠ D.1) (hs : k + 1 ≤ s) :
    pot s (σ.step s (.hop2 h D D)) + σ.junkCol (hop2Half h D) (hop2Pos s h D) = pot s σ := by
  unfold pot
  have hrow : ∑ H, potR s (σ.step s (.hop2 h D D)) H = ∑ H, potR s σ H := rfl
  rw [hrow]
  have hsum := sum_update_add
    (fun (V : ColH k) (f : ℕ → Sq k) =>
      ∑ q ∈ (range (colLen k s V)).filter (fun q => f q ≠ (V.2.1, V.1)), (q + 1))
    σ.col (hop2Half h D) (shiftIn (σ.col (hop2Half h D)) (hop2Pos s h D) D)
  have hD' : ((hop2Half h D).2.1, (hop2Half h D).1) = D := rfl
  have hyn : ¬ (D ≠ ((hop2Half h D).2.1, (hop2Half h D).1)) := by rw [hD']; simp
  have hc := sum_filter_shiftIn (fun a : Sq k => a ≠ ((hop2Half h D).2.1, (hop2Half h D).1))
    (σ.col (hop2Half h D)) (hop2Pos_lt hD hs) hyn
  have e : ∑ V, potC s (σ.step s (.hop2 h D D)) V =
      ∑ V, ∑ q ∈ (range (colLen k s V)).filter (fun q =>
        (Function.update σ.col (hop2Half h D)
          (shiftIn (σ.col (hop2Half h D)) (hop2Pos s h D) D) V) q ≠ (V.2.1, V.1)), (q + 1) := rfl
  have e2 : ∑ V, potC s σ V =
      ∑ V, ∑ q ∈ (range (colLen k s V)).filter (fun q => σ.col V q ≠ (V.2.1, V.1)), (q + 1) := rfl
  have e3 : σ.junkCol (hop2Half h D) (hop2Pos s h D) =
      ((range (hop2Pos s h D + 1)).filter
        fun q => σ.col (hop2Half h D) q ≠ ((hop2Half h D).2.1, (hop2Half h D).1)).card := rfl
  rw [e, e2, e3]
  omega

end junk

section pres

variable {s : ℕ} {σ0 : IState k} {F0 : ℕ}

theorem gHop1_linv {G : GS k} (hL : LInv s σ0 F0 G) (τ : ℕ) {S h y : Sq k}
    (hb : G.σ.blank = h) (h1 : S.1 = h.1) (h2 : S.2 ≠ h.2) (hy : y.2 = h.2)
    (hsch : 1 ≤ G.sched S y) (hs : k + 1 ≤ s) : LInv s σ0 F0 (gHop1 s τ G S h y) := by
  have hpre : G.σ.Pre (.hop1 S h y) := ⟨hb, h1, h2, by have := hL.roles_le S y; omega⟩
  obtain ⟨hrun, hval⟩ := pre_append hL hpre
  have hcnt : ∀ Q x, (gHop1 s τ G S h y).σ.cnt Q x = G.σ.cnt Q x -
      (if Q = S ∧ x = y then 1 else 0) + (if Q = h ∧ x = rowHead G S h then 1 else 0) :=
    fun Q x => cnt_hop1 s G.σ S h y Q x
  have hA : ∀ Q x, (if Q = S ∧ x = y then 1 else 0) ≤ G.sched Q x := by
    intro Q x
    split_ifs with hA
    · obtain ⟨rfl, rfl⟩ := hA; exact hsch
    · exact Nat.zero_le _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hrun, hval⟩
  · intro Q x
    rw [gHop1_sched, gHop1_stock, gHop1_free, hcnt]
    have hdisj : (if isStk h (rowHead G S h) ∧ Q = h ∧ x = rowHead G S h then 1 else 0) +
        (if (rowHead G S h).2 ≠ h.2 ∧ Q = h ∧ x = rowHead G S h then 1 else 0) ≤
        (if Q = h ∧ x = rowHead G S h then 1 else 0) := by
      unfold isStk; split_ifs <;> simp_all
    have := hL.roles_le Q x
    have := hA Q x
    omega
  · intro Q x hx
    rw [gHop1_sched, gHop1_stock, gHop1_free, hcnt]
    have hcov : (if Q = h ∧ x = rowHead G S h then 1 else 0) ≤
        (if isStk h (rowHead G S h) ∧ Q = h ∧ x = rowHead G S h then 1 else 0) +
        (if (rowHead G S h).2 ≠ h.2 ∧ Q = h ∧ x = rowHead G S h then 1 else 0) := by
      unfold isStk
      split_ifs with c1 c2 c3 <;> simp_all
    have := hL.roles_ge Q x hx
    have := hA Q x
    omega
  · intro h' x hne
    rw [gHop1_stock] at hne
    by_cases hc : isStk h (rowHead G S h) ∧ h' = h ∧ x = rowHead G S h
    · obtain ⟨hs', rfl, rfl⟩ := hc; exact hs'
    · rw [if_neg hc, add_zero] at hne; exact hL.stock_supp h' x hne
  · intro H q x d hg
    rw [gh_gHop1] at hg
    show (Function.update G.σ.row (hop1Half S h)
      (shiftIn (G.σ.row (hop1Half S h)) (hop1Pos s S h) y)) H q = x ∧ _
    by_cases hH : H = hop1Half S h
    · subst hH
      rw [Function.update_self] at hg ⊢
      rcases lt_trichotomy q (hop1Pos s S h) with hq | hq | hq
      · rw [shiftIn_of_lt hq] at hg ⊢; exact hL.ghost_row _ _ _ _ hg
      · subst hq
        rw [shiftIn_self'] at hg ⊢
        simp only [Option.some.injEq, Prod.mk.injEq] at hg
        obtain ⟨rfl, -⟩ := hg
        exact ⟨rfl, hy⟩
      · rw [shiftIn_of_gt hq] at hg ⊢; exact hL.ghost_row _ _ _ _ hg
    · rw [Function.update_of_ne hH] at hg ⊢; exact hL.ghost_row _ _ _ _ hg
  · intro h'
    have e1 : ∑ x, (gHop1 s τ G S h y).out h' x = (∑ x, G.out h' x) +
        (if (isStk h (rowHead G S h) ∧ gh s G (hop1Half S h) 0 = none) ∧ h' = h then 1 else 0) := by
      simp only [gHop1_out, sum_add_distrib]
      congr 1
      by_cases hc : (isStk h (rowHead G S h) ∧ gh s G (hop1Half S h) 0 = none) ∧ h' = h
      · rw [if_pos hc]
        simp only [hc.1, hc.2, true_and]
        simp
      · rw [if_neg hc]
        refine sum_eq_zero fun x _ => ?_
        rw [if_neg]; tauto
    have e2 := hubCnt_gHop1 s τ G h2 hs y (fun o => o = none) h'
    simp only [reduceCtorEq, and_false, if_false, add_zero] at e2
    have hle : (if (isStk h (rowHead G S h) ∧ gh s G (hop1Half S h) 0 = none) ∧ h' = h
        then 1 else 0) ≤ (if h' = h ∧ gh s G (hop1Half S h) 0 = none then 1 else 0) := by
      split_ifs <;> simp_all
    have := hL.out_le h'
    unfold noneCnt at this ⊢
    omega
  · have e1 : ∑ Q, ∑ x, (gHop1 s τ G S h y).free Q x =
        (∑ Q, ∑ x, G.free Q x) + if (rowHead G S h).2 ≠ h.2 then 1 else 0 := by
      simp only [gHop1_free]; exact sum_sum_add_ind _ _ _ _
    have e2 := junkCnt_hop1 s G.σ h2 hy hs
    have := hL.free_junk
    show _ + junkCnt s (G.σ.step s (.hop1 S h y)) ≤ F0
    have hrh : rowHead G S h = G.σ.row (hop1Half S h) 0 := rfl
    rw [e1, hrh]
    omega

theorem gHop1_cost {G : GS k} (hL : LInv s σ0 F0 G) (τ : ℕ) {S h y : Sq k}
    (h2 : S.2 ≠ h.2) (hy : y.2 = h.2) (hs : k + 1 ≤ s) :
    IState.totalCost s σ0 (gHop1 s τ G S h y).evs + pot s (gHop1 s τ G S h y).σ =
      IState.totalCost s σ0 G.evs + pot s G.σ + 4000 * s := by
  show IState.totalCost s σ0 (G.evs ++ [.hop1 S h y]) + pot s (G.σ.step s (.hop1 S h y)) = _
  rw [cost_append hL]
  have := pot_hop1 s G.σ h2 hy hs
  simp only [IState.cost]
  omega

theorem gHop2_linv {G : GS k} (hL : LInv s σ0 F0 G) {st : Bool} {h D : Sq k}
    (hb : G.σ.blank = D) (h1 : h.2 = D.2) (h2 : h.1 ≠ D.1)
    (hrole : if st then 1 ≤ G.stock h D else 1 ≤ G.sched h D) (hs : k + 1 ≤ s) :
    LInv s σ0 F0 (gHop2 s G st h D D) := by
  have hrole' : 1 ≤ G.σ.cnt h D := by
    have := hL.roles_le h D
    cases st <;> simp at hrole <;> omega
  have hpre : G.σ.Pre (.hop2 h D D) := ⟨hb, h1, h2, hrole'⟩
  obtain ⟨hrun, hval⟩ := pre_append hL hpre
  have hcnt : ∀ Q x, (gHop2 s G st h D D).σ.cnt Q x = G.σ.cnt Q x -
      (if Q = h ∧ x = D then 1 else 0) + (if Q = D ∧ x = colHead G h D then 1 else 0) :=
    fun Q x => cnt_hop2 s G.σ h D D Q x
  have hA : ∀ Q x, (if st = false ∧ Q = h ∧ x = D then 1 else 0) +
      (if st = true ∧ Q = h ∧ x = D then 1 else 0) = (if Q = h ∧ x = D then 1 else 0) := by
    intro Q x; cases st <;> simp
  have hA1 : ∀ Q x, (if st = false ∧ Q = h ∧ x = D then 1 else 0) ≤ G.sched Q x := by
    intro Q x
    split_ifs with hc
    · obtain ⟨hst, rfl, rfl⟩ := hc; subst hst; simpa using hrole
    · exact Nat.zero_le _
  have hA2 : ∀ Q x, (if st = true ∧ Q = h ∧ x = D then 1 else 0) ≤ G.stock Q x := by
    intro Q x
    split_ifs with hc
    · obtain ⟨hst, rfl, rfl⟩ := hc; subst hst; simpa using hrole
    · exact Nat.zero_le _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hrun, hval⟩
  · intro Q x
    rw [gHop2_sched, gHop2_stock, gHop2_free, hcnt]
    have hB : (if colHead G h D ≠ D ∧ Q = D ∧ x = colHead G h D then 1 else 0) ≤
        (if Q = D ∧ x = colHead G h D then 1 else 0) := by
      split_ifs <;> simp_all
    have := hL.roles_le Q x
    have := hA Q x; have := hA1 Q x; have := hA2 Q x
    omega
  · intro Q x hx
    rw [gHop2_sched, gHop2_stock, gHop2_free, hcnt]
    have hB : (if Q = D ∧ x = colHead G h D then 1 else 0) ≤
        (if colHead G h D ≠ D ∧ Q = D ∧ x = colHead G h D then 1 else 0) := by
      split_ifs with c1 c2 <;> simp_all
    have := hL.roles_ge Q x hx
    have := hA Q x; have := hA1 Q x; have := hA2 Q x
    omega
  · intro h' x hne
    rw [gHop2_stock] at hne
    exact hL.stock_supp h' x (by omega)
  · exact hL.ghost_row
  · exact hL.out_le
  · have e1 : ∑ Q, ∑ x, (gHop2 s G st h D D).free Q x =
        (∑ Q, ∑ x, G.free Q x) + if colHead G h D ≠ D then 1 else 0 := by
      simp only [gHop2_free]; exact sum_sum_add_ind _ _ _ _
    have e2 := junkCnt_hop2 s G.σ h2 hs
    have := hL.free_junk
    show _ + junkCnt s (G.σ.step s (.hop2 h D D)) ≤ F0
    have hrh : colHead G h D = G.σ.col (hop2Half h D) 0 := rfl
    rw [e1, hrh]
    omega

theorem gHop2_cost {G : GS k} (hL : LInv s σ0 F0 G) {st : Bool} {h D : Sq k}
    (h2 : h.1 ≠ D.1) (hs : k + 1 ≤ s) :
    IState.totalCost s σ0 (gHop2 s G st h D D).evs + pot s (gHop2 s G st h D D).σ =
      IState.totalCost s σ0 G.evs + pot s G.σ + (4000 * s + 30 * k ^ 2) := by
  show IState.totalCost s σ0 (G.evs ++ [.hop2 h D D]) + pot s (G.σ.step s (.hop2 h D D)) = _
  rw [cost_append hL]
  have := pot_hop2 s G.σ h2 hs
  simp only [IState.cost]
  omega

theorem gJump_linv {G : GS k} (hL : LInv s σ0 F0 G) {E Z y : Sq k}
    (hb : G.σ.blank = E) (hEZ : E ≠ Z) (hal : E.1 = Z.1 ∨ E.2 = Z.2)
    (hfree : 1 ≤ G.free Z y) : LInv s σ0 F0 (gJump s G E Z y) := by
  have hpre : G.σ.Pre (.jump E Z y) :=
    ⟨hb, hEZ, hal, by have := hL.roles_le Z y; omega⟩
  obtain ⟨hrun, hval⟩ := pre_append hL hpre
  have hcnt : ∀ Q x, (gJump s G E Z y).σ.cnt Q x = G.σ.cnt Q x -
      (if Q = Z ∧ x = y then 1 else 0) + (if Q = E ∧ x = y then 1 else 0) :=
    fun Q x => cnt_jump s G.σ E Z y Q x
  have hA : ∀ Q x, (if Q = Z ∧ x = y then 1 else 0) ≤ G.free Q x := by
    intro Q x
    split_ifs with hA
    · obtain ⟨rfl, rfl⟩ := hA; exact hfree
    · exact Nat.zero_le _
  refine ⟨?_, ?_, hL.stock_supp, hL.ghost_row, hL.out_le, ?_, hrun, hval⟩
  · intro Q x
    rw [gJump_free, hcnt]
    have := hL.roles_le Q x; have := hA Q x
    show G.sched Q x + G.stock Q x + _ ≤ _
    omega
  · intro Q x hx
    rw [gJump_free, hcnt]
    have := hL.roles_ge Q x hx; have := hA Q x
    show _ ≤ G.sched Q x + G.stock Q x + _
    omega
  · have e1 : ∑ Q, ∑ x, (gJump s G E Z y).free Q x = ∑ Q, ∑ x, G.free Q x := by
      simp only [gJump_free]
      have h1 : ∀ Q x, G.free Q x - (if Q = Z ∧ x = y then 1 else 0) +
          (if Q = E ∧ x = y then 1 else 0) + (if Q = Z ∧ x = y then 1 else 0) =
          G.free Q x + (if Q = E ∧ x = y then 1 else 0) := by
        intro Q x; have := hA Q x; omega
      have h2 : (∑ Q, ∑ x, (G.free Q x - (if Q = Z ∧ x = y then 1 else 0) +
          (if Q = E ∧ x = y then 1 else 0))) + ∑ Q, ∑ x, (if Q = Z ∧ x = y then 1 else 0) =
          (∑ Q, ∑ x, G.free Q x) + ∑ Q, ∑ x, (if Q = E ∧ x = y then 1 else 0) := by
        rw [← sum_add_distrib, ← sum_add_distrib]
        refine sum_congr rfl fun Q _ => ?_
        rw [← sum_add_distrib, ← sum_add_distrib]
        exact sum_congr rfl fun x _ => h1 Q x
      rw [sum_sum_ind, sum_sum_ind] at h2
      omega
    have := hL.free_junk
    show _ + junkCnt s G.σ ≤ F0
    rw [e1]
    exact this

theorem gJump_cost {G : GS k} (hL : LInv s σ0 F0 G) {E Z y : Sq k} :
    IState.totalCost s σ0 (gJump s G E Z y).evs + pot s (gJump s G E Z y).σ =
      IState.totalCost s σ0 G.evs + pot s G.σ + 4000 * s * (1 + sqDist E Z) := by
  show IState.totalCost s σ0 (G.evs ++ [.jump E Z y]) + pot s G.σ = _
  rw [cost_append hL]
  simp only [IState.cost]
  omega

end pres

end SlidingPuzzle.Hub
