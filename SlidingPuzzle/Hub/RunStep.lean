import SlidingPuzzle.Hub.RunHigh

/-! # One high-level step

Effects of relocations, the high-level invariant `HInv` (stock identity,
bypass bound, free lower bound, cost, scheduled total), and its preservation
by `hstep`. -/
namespace SlidingPuzzle.Hub

open Finset

variable {k : ℕ}

/-! ## Relocations -/

section reloc

variable {s : ℕ} {σ0 : IState k} {F0 : ℕ}

/-- Unrecorded designated cells. -/
noncomputable def ndes (σ : IState k) : ℕ :=
  (Finset.univ.filter fun p : Sq k × Bool => σ.des p.1 p.2 = none).card

theorem ndes_le (σ : IState k) : ndes σ ≤ 2 * k ^ 2 := by
  unfold ndes
  refine (Finset.card_filter_le _ _).trans ?_
  simp [Fintype.card_prod]; ring_nf; exact le_refl _

theorem sum_dcnt_le_one {σ : IState k} {Q : Sq k} {c : Bool} (h : σ.des Q c = none) :
    ∑ y, σ.dcnt Q y ≤ 1 := by
  classical
  unfold IState.dcnt
  rw [Finset.sum_add_distrib]
  have h1 : ∀ o : Option (Sq k), (∑ y : Sq k, if o = some y then 1 else 0) ≤ 1 := by
    intro o; cases o with
    | none => simp
    | some z => simp
  cases c
  · rw [h]; simp only [reduceCtorEq, if_false, Finset.sum_const_zero, zero_add]
    exact h1 _
  · rw [h]; simp only [reduceCtorEq, if_false, Finset.sum_const_zero, add_zero]
    exact h1 _

theorem hReloc_of_al {G : GS k} {E Z : Sq k} (c : E.1 = Z.1 ∨ E.2 = Z.2) :
    hReloc s G E Z = hLeg s G E Z := by
  unfold hReloc; rw [if_pos c]

theorem hReloc_of_corner {G : GS k} {E Z : Sq k} (c : ¬ (E.1 = Z.1 ∨ E.2 = Z.2)) :
    hReloc s G E Z = hLeg s (hLeg s G E (Z.1, E.2)) (Z.1, E.2) Z := by
  unfold hReloc; rw [if_neg c]

theorem hLeg_same (G : GS k) (E Z : Sq k) :
    (hLeg s G E Z).sched = G.sched ∧ (hLeg s G E Z).stock = G.stock ∧
      (hLeg s G E Z).out = G.out ∧ (hLeg s G E Z).byp = G.byp ∧
      (hLeg s G E Z).ins = G.ins ∧ (hLeg s G E Z).served = G.served ∧
      (hLeg s G E Z).sent = G.sent ∧ (hLeg s G E Z).wt = G.wt ∧
      (hLeg s G E Z).dd = G.dd ∧ (hLeg s G E Z).σ.blank = Z := by
  unfold hLeg
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hReloc_same (G : GS k) (E Z : Sq k) :
    (hReloc s G E Z).sched = G.sched ∧ (hReloc s G E Z).stock = G.stock ∧
      (hReloc s G E Z).out = G.out ∧ (hReloc s G E Z).byp = G.byp ∧
      (hReloc s G E Z).ins = G.ins ∧ (hReloc s G E Z).served = G.served ∧
      (hReloc s G E Z).sent = G.sent ∧ (hReloc s G E Z).wt = G.wt ∧
      (hReloc s G E Z).dd = G.dd ∧ (hReloc s G E Z).σ.blank = Z := by
  unfold hReloc
  split_ifs
  · exact hLeg_same G E Z
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, -⟩ := hLeg_same (s := s) G E (Z.1, E.2)
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ :=
      hLeg_same (s := s) (hLeg s G E (Z.1, E.2)) (Z.1, E.2) Z
    exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6,
      b7.trans a7, b8.trans a8, b9.trans a9, b10⟩

theorem corner_facts {E Z : Sq k} (c : ¬ (E.1 = Z.1 ∨ E.2 = Z.2)) :
    E ≠ (Z.1, E.2) ∧ (Z.1, E.2) ≠ Z := by
  have c1 : E.1 ≠ Z.1 := fun e => c (Or.inl e)
  have c2 : E.2 ≠ Z.2 := fun e => c (Or.inr e)
  refine ⟨fun e => c1 (by simpa using congrArg Prod.fst e),
    fun e => c2 (by simpa using congrArg Prod.snd e)⟩

theorem gRJump_free_eq (G : GS k) (E Z : Sq k) (a : Bool) (y : Sq k) :
    (gRJump s G E Z a y).free = (gJump s G E Z y).free := rfl

theorem hLeg_some {G : GS k} {E Z y : Sq k} (h : G.σ.des Z (landB s E Z false) = some y) :
    hLeg s G E Z = gRestore s (gRJump s G E Z false y) Z (landB s E Z false)
      (pickFree (gRJump s G E Z false y) Z) := by
  unfold hLeg; rw [h]

theorem hLeg_none {G : GS k} {E Z : Sq k} (h : G.σ.des Z (landB s E Z false) = none) :
    hLeg s G E Z = { gRestore s (gJump s G E Z (pickFree G Z)) Z (landB s E Z false)
        (pickFree (gJump s G E Z (pickFree G Z)) Z) with fb := G.fb + 1 } := by
  unfold hLeg; rw [h]

theorem hLeg_linv {G : GS k} (hL : LInv s σ0 F0 G) {E Z : Sq k} (hb : G.σ.blank = E)
    (hEZ : E ≠ Z) (hal : E.1 = Z.1 ∨ E.2 = Z.2) (hZ : 3 ≤ ∑ y, G.free Z y) :
    LInv s σ0 F0 (hLeg s G E Z) := by
  rcases hdes : G.σ.des Z (landB s E Z false) with _ | y
  · rw [hLeg_none hdes]
    have hs := sum_free_gJump s G E Z (pickFree G Z) Z
    rw [if_neg (Ne.symm hEZ), if_pos rfl] at hs
    have hL1 := gJump_linv hL hb hEZ hal (pickFree_spec G Z hZ)
    have hnone : (gJump s G E Z (pickFree G Z)).σ.des Z (landB s E Z false) = none := by
      change (G.σ.step s (.jump E Z (pickFree G Z))).des Z _ = none
      rw [IState.des_step s G.σ (.jump E Z (pickFree G Z)) trivial]; exact hdes
    have h1 := sum_dcnt_le_one hnone
    exact (gRestore_linv hL1 rfl hnone
      (pickFree_spec' (gJump s G E Z (pickFree G Z)) Z (by omega))).congr
        rfl rfl rfl rfl rfl rfl rfl
  · rw [hLeg_some hdes]
    have hL1 := gRJump_linv hL hb hEZ hal hdes
    have hs1 := sum_free_gJump s G E Z y Z
    rw [if_neg (Ne.symm hEZ), if_pos rfl, ← gRJump_free_eq (s := s) G E Z false y] at hs1
    have hnone : (gRJump s G E Z false y).σ.des Z (landB s E Z false) = none := by
      simp [gRJump, IState.step]
    have h1 := sum_dcnt_le_one hnone
    exact gRestore_linv hL1 rfl hnone
      (pickFree_spec' (gRJump s G E Z false y) Z (by omega))

theorem hLeg_free (G : GS k) (E Z Q : Sq k) :
    (∑ x, G.free Q x) + (if Q = E then 1 else 0) ≤
      (∑ x, (hLeg s G E Z).free Q x) + (if Q = Z then 1 else 0) := by
  rcases hdes : G.σ.des Z (landB s E Z false) with _ | y
  · rw [hLeg_none hdes]; exact sum_free_gJump s G E Z _ Q
  · rw [hLeg_some hdes]; exact sum_free_gJump s G E Z y Q

theorem hLeg_fb (G : GS k) {E Z : Sq k} (hEZ : E ≠ Z) :
    (hLeg s G E Z).fb + ndes (hLeg s G E Z).σ ≤ G.fb + ndes G.σ := by
  unfold ndes
  rcases hdes : G.σ.des Z (landB s E Z false) with _ | y
  · rw [hLeg_none hdes]
    show G.fb + 1 + _ ≤ _
    have hsub : (Finset.univ.filter fun p : Sq k × Bool =>
        ((gRestore s (gJump s G E Z (pickFree G Z)) Z (landB s E Z false)
          (pickFree (gJump s G E Z (pickFree G Z)) Z)).σ.des p.1 p.2 = none)) ⊂
        Finset.univ.filter fun p : Sq k × Bool => G.σ.des p.1 p.2 = none := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨(Z, landB s E Z false), by simp [hdes], ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        change ¬ (if Z = Z ∧ landB s E Z false = landB s E Z false then _ else _) = none
        rw [if_pos ⟨rfl, rfl⟩]; simp
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        change (if p.1 = Z ∧ p.2 = landB s E Z false then _ else G.σ.des p.1 p.2) = none at hp
        split_ifs at hp <;> simp_all
    have := Finset.card_lt_card hsub
    change G.fb + 1 + (Finset.univ.filter fun p : Sq k × Bool =>
        ((gRestore s (gJump s G E Z (pickFree G Z)) Z (landB s E Z false)
          (pickFree (gJump s G E Z (pickFree G Z)) Z)).σ.des p.1 p.2 = none)).card ≤
      G.fb + (Finset.univ.filter fun p : Sq k × Bool => G.σ.des p.1 p.2 = none).card
    omega
  · rw [hLeg_some hdes]
    show G.fb + _ ≤ _
    have := Finset.card_le_card (s := Finset.univ.filter fun p : Sq k × Bool =>
      ((gRestore s (gRJump s G E Z false y) Z (landB s E Z false)
        (pickFree (gRJump s G E Z false y) Z)).σ.des p.1 p.2 = none))
      (t := Finset.univ.filter fun p : Sq k × Bool => G.σ.des p.1 p.2 = none) (by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        change (if p.1 = Z ∧ p.2 = landB s E Z false then _ else
          (if p.1 = Z ∧ p.2 = landB s E Z false then none
            else if p.1 = E ∧ p.2 = false then some y else G.σ.des p.1 p.2)) = none at hp
        split_ifs at hp <;> simp_all)
    omega

theorem hLeg_fb_le (G : GS k) (E Z : Sq k) : (hLeg s G E Z).fb ≤ G.fb + 1 := by
  rcases hdes : G.σ.des Z (landB s E Z false) with _ | y
  · rw [hLeg_none hdes]
  · rw [hLeg_some hdes]; exact Nat.le_succ _

theorem hLeg_cost {G : GS k} (hL : LInv s σ0 F0 G) {E Z : Sq k} (hb : G.σ.blank = E)
    (hEZ : E ≠ Z) (hal : E.1 = Z.1 ∨ E.2 = Z.2) (hZ : 3 ≤ ∑ y, G.free Z y)
    (hd : sqDist E Z + 1 ≤ k) :
    IState.totalCost s σ0 (hLeg s G E Z).evs + pot s (hLeg s G E Z).σ +
        (s + 3) * (14 * k) * G.fb ≤
      IState.totalCost s σ0 G.evs + pot s G.σ + (s + 3) * (16 + 7 * sqDist E Z) +
        (s + 3) * (14 * k) * (hLeg s G E Z).fb := by
  rcases hdes : G.σ.des Z (landB s E Z false) with _ | y
  swap
  · rw [hLeg_some hdes]
    have hL1 := gRJump_linv hL hb hEZ hal hdes
    have e1 := gRJump_cost (s := s) hL (E := E) (Z := Z) (a := false) (y := y)
    have e2 := gRestore_cost (s := s) hL1 (Z := Z) (c := landB s E Z false)
      (y := pickFree (gRJump s G E Z false y) Z)
    show _ + (s + 3) * (14 * k) * G.fb ≤ _ + (s + 3) * (14 * k) * G.fb
    have : (s + 3) * (3 + 7 * sqDist E Z) + 13 * s ≤ (s + 3) * (16 + 7 * sqDist E Z) := by
      nlinarith
    omega
  · rw [hLeg_none hdes]
    have hL1 := gJump_linv hL hb hEZ hal (pickFree_spec G Z hZ)
    have e1 := gJump_cost (s := s) hL (E := E) (Z := Z) (y := pickFree G Z)
    have e2 := gRestore_cost (s := s) hL1 (Z := Z) (c := landB s E Z false)
      (y := pickFree (gJump s G E Z (pickFree G Z)) Z)
    show IState.totalCost s σ0 (gRestore s _ Z _ _).evs + pot s (gRestore s _ Z _ _).σ +
        (s + 3) * (14 * k) * G.fb ≤ _ + (s + 3) * (14 * k) * (G.fb + 1)
    have : (s + 3) * (13 + 21 * sqDist E Z) + 13 * s ≤
        (s + 3) * (16 + 7 * sqDist E Z) + (s + 3) * (14 * k) := by
      have : 13 + 21 * sqDist E Z + 13 ≤ 16 + 7 * sqDist E Z + 14 * k := by omega
      nlinarith
    have e3 : (s + 3) * (14 * k) * (G.fb + 1) = (s + 3) * (14 * k) * G.fb + (s + 3) * (14 * k) := by
      ring
    omega

theorem hReloc_linv {G : GS k} (hL : LInv s σ0 F0 G) {E Z : Sq k} (hb : G.σ.blank = E)
    (hEZ : E ≠ Z) (hfree : ∀ Q, 3 ≤ ∑ y, G.free Q y) : LInv s σ0 F0 (hReloc s G E Z) := by
  by_cases c : E.1 = Z.1 ∨ E.2 = Z.2
  · rw [hReloc_of_al c]
    exact hLeg_linv hL hb hEZ c (hfree Z)
  · rw [hReloc_of_corner c]
    obtain ⟨h1, h2⟩ := corner_facts c
    have hL1 := hLeg_linv hL hb h1 (Or.inr rfl) (hfree _)
    have hs := hLeg_free (s := s) G E (Z.1, E.2) Z
    rw [if_neg (Ne.symm h2), if_neg (fun e => hEZ e.symm)] at hs
    have := hfree Z
    exact hLeg_linv hL1 (hLeg_same G E (Z.1, E.2)).2.2.2.2.2.2.2.2.2 h2 (Or.inl rfl) (by omega)

theorem hReloc_free (G : GS k) (E Z Q : Sq k) :
    (∑ x, G.free Q x) + (if Q = E then 1 else 0) ≤
      (∑ x, (hReloc s G E Z).free Q x) + (if Q = Z then 1 else 0) := by
  by_cases c : E.1 = Z.1 ∨ E.2 = Z.2
  · rw [hReloc_of_al c]; exact hLeg_free G E Z Q
  · rw [hReloc_of_corner c]
    have h1 := hLeg_free (s := s) G E (Z.1, E.2) Q
    have h2 := hLeg_free (s := s) (hLeg s G E (Z.1, E.2)) (Z.1, E.2) Z Q
    omega

theorem hReloc_fb (G : GS k) {E Z : Sq k} (hEZ : E ≠ Z) :
    (hReloc s G E Z).fb + ndes (hReloc s G E Z).σ ≤ G.fb + ndes G.σ := by
  by_cases c : E.1 = Z.1 ∨ E.2 = Z.2
  · rw [hReloc_of_al c]; exact hLeg_fb G hEZ
  · rw [hReloc_of_corner c]
    obtain ⟨h1, h2⟩ := corner_facts c
    exact (hLeg_fb _ h2).trans (hLeg_fb G h1)

theorem hReloc_cost {G : GS k} (hL : LInv s σ0 F0 G) {E Z : Sq k} (hb : G.σ.blank = E)
    (hEZ : E ≠ Z) (hfree : ∀ Q, 3 ≤ ∑ y, G.free Q y) :
    IState.totalCost s σ0 (hReloc s G E Z).evs + pot s (hReloc s G E Z).σ +
        (s + 3) * (14 * k) * G.fb ≤
      IState.totalCost s σ0 G.evs + pot s G.σ + (s + 3) * relocWeight (.reloc E Z) +
        (s + 3) * (14 * k) * (hReloc s G E Z).fb := by
  simp only [relocWeight]
  by_cases c : E.1 = Z.1 ∨ E.2 = Z.2
  · rw [if_pos c, hReloc_of_al c]
    have hd : sqDist E Z + 1 ≤ k := by
      unfold sqDist; have := E.1.isLt; have := E.2.isLt; have := Z.1.isLt; have := Z.2.isLt
      rcases c with c | c <;> rw [c] <;> simp only [Nat.dist_self, zero_add, add_zero, Nat.dist] <;>
        omega
    exact hLeg_cost hL hb hEZ c (hfree Z) hd
  · rw [if_neg c, hReloc_of_corner c]
    obtain ⟨h1, h2⟩ := corner_facts c
    have hL1 := hLeg_linv hL hb h1 (Or.inr rfl) (hfree _)
    have hs := hLeg_free (s := s) G E (Z.1, E.2) Z
    rw [if_neg (Ne.symm h2), if_neg (fun e => hEZ e.symm)] at hs
    have hfz := hfree Z
    have hd1 : sqDist E (Z.1, E.2) + 1 ≤ k := by
      unfold sqDist; have := E.1.isLt; have := Z.1.isLt
      simp only [Nat.dist_self, add_zero, Nat.dist]; omega
    have hd2 : sqDist (Z.1, E.2) Z + 1 ≤ k := by
      unfold sqDist; have := E.2.isLt; have := Z.2.isLt
      simp only [Nat.dist_self, zero_add, Nat.dist]; omega
    have e1 := hLeg_cost hL hb h1 (Or.inr rfl) (hfree _) hd1
    have e2 := hLeg_cost hL1 (hLeg_same G E (Z.1, E.2)).2.2.2.2.2.2.2.2.2 h2 (Or.inl rfl)
      (by omega) hd2
    have hd : sqDist E (Z.1, E.2) + sqDist (Z.1, E.2) Z = sqDist E Z := by
      unfold sqDist; simp only [Nat.dist_self]; ring
    have : (s + 3) * (16 + 7 * sqDist E (Z.1, E.2)) + (s + 3) * (16 + 7 * sqDist (Z.1, E.2) Z) =
        (s + 3) * (32 + 7 * sqDist E Z) := by
      rw [← hd]; ring
    omega

end reloc

/-! ## The high-level invariant -/

/-- Budget constant of a hop. -/
def hopC (k s : ℕ) : ℕ := 25 * s + 7 * k ^ 2 + 1033 * k + 2076

/-- Invariants holding between high-level events. -/
structure HInv (s : ℕ) (σ0 : IState k) (free0 : Sq k → ℕ) (N : Sq k → Sq k → ℕ) (S0 : ℕ)
    (G : GS k) : Prop where
  ident : ∀ h x, isStk h x → G.stock h x + newCnt s (gh s G) h x = G.out h x + G.byp h x
  byp_le : ∀ h x, G.byp h x ≤ N h x + 1
  free_lo : ∀ Z, free0 Z + G.sent Z + (if σ0.blank = Z then 1 else 0) ≤
    (∑ y, G.free Z y) + (∑ x, G.byp Z x) + G.served Z + (if G.σ.blank = Z then 1 else 0)
  cost : IState.totalCost s σ0 G.evs + pot s G.σ ≤ pot s σ0 +
    hopC k s * (∑ Z, G.served Z) + (s + 3) * (21 * k + 9) * (∑ h, ∑ x, G.byp h x) +
    (s + 3) * G.wt + (s + 3) * (14 * k) * G.fb
  sched_sum : (∑ Z, G.served Z) + (∑ S, ∑ D, G.sched S D) = S0
  fbnd : G.fb + ndes G.σ ≤ 2 * k ^ 2

section step

variable {s : ℕ} {σ0 : IState k} {F0 : ℕ} {free0 : Sq k → ℕ} {N : Sq k → Sq k → ℕ} {S0 : ℕ}

theorem sum_bump (f : Sq k → ℕ) (Q : Sq k) : ∑ Z, bump f Q Z = (∑ Z, f Z) + 1 := by
  simp [bump, sum_add_distrib]

theorem hServe_fb_des (τ : ℕ) (G : GS k) (S D : Sq k) :
    (hServe s τ G S D).fb = G.fb ∧ (hServe s τ G S D).σ.des = G.σ.des := by
  unfold hServe
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem hstep_serve {G : GS k} (hL : LInv s σ0 F0 G) (hH : HInv s σ0 free0 N S0 G) (τ : ℕ)
    {S D : Sq k} (ok : ServeOK s N G S D) :
    LInv s σ0 F0 (hstep s τ G (.serve S D)) ∧ HInv s σ0 free0 N S0 (hstep s τ G (.serve S D)) := by
  have hL' := hServe_linv hL τ ok
  obtain ⟨r1, r2, r3, r4⟩ := hServe_rest (s := s) τ G S D
  obtain ⟨f1, f2⟩ := hServe_fb_des (s := s) τ G S D
  refine ⟨hL'.congr rfl rfl rfl rfl rfl rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hServe_ident hL τ ok hH.ident
  · exact hServe_byp_le s τ ok hH.ident hH.byp_le
  · intro Z
    have h1 := hH.free_lo Z
    have h2 := hServe_free s τ G S D Z
    have hb := hServe_blank (s := s) τ G S D
    have hb0 := ok.blank
    have hne := ok.ne
    show free0 Z + bump G.sent S Z + _ ≤ (∑ y, (hServe s τ G S D).free Z y) +
      (∑ x, (hServe s τ G S D).byp Z x) + bump G.served D Z +
      (if (hServe s τ G S D).σ.blank = Z then 1 else 0)
    rw [hb]
    rw [hb0] at h1
    simp only [bump, @eq_comm _ D Z, @eq_comm _ S Z] at h1 ⊢
    omega
  · have h1 := hH.cost
    have h2 := hServe_cost hL τ ok
    show IState.totalCost s σ0 (hServe s τ G S D).evs + pot s (hServe s τ G S D).σ ≤
      pot s σ0 + hopC k s * (∑ Z, bump G.served D Z) +
      (s + 3) * (21 * k + 9) * (∑ h, ∑ x, (hServe s τ G S D).byp h x) +
      (s + 3) * (hServe s τ G S D).wt + (s + 3) * (14 * k) * (hServe s τ G S D).fb
    rw [sum_bump, r3, f1]
    unfold hopC at *
    nlinarith
  · have h1 := hH.sched_sum
    show (∑ Z, bump G.served D Z) + (∑ S', ∑ D', (hServe s τ G S D).sched S' D') = S0
    rw [sum_bump, hServe_sched]
    have hp : ∀ Q x, decCnt G.sched S D Q x + (if Q = S ∧ x = D then 1 else 0) = G.sched Q x := by
      intro Q x
      rw [decCnt_apply]
      split_ifs with e
      · obtain ⟨rfl, rfl⟩ := e; have := ok.sched; omega
      · simp
    have : (∑ Q, ∑ x, decCnt G.sched S D Q x) + 1 = ∑ Q, ∑ x, G.sched Q x := by
      rw [← sum_sum_ind S D, ← sum_add_distrib]
      refine sum_congr rfl fun Q _ => ?_
      rw [← sum_add_distrib]
      exact sum_congr rfl fun x _ => hp Q x
    omega
  · show (hServe s τ G S D).fb + ndes (hServe s τ G S D).σ ≤ _
    have e : ndes (hServe s τ G S D).σ = ndes G.σ := by unfold ndes; rw [f2]
    rw [f1, e]; exact hH.fbnd

theorem hstep_reloc {G : GS k} (hL : LInv s σ0 F0 G) (hH : HInv s σ0 free0 N S0 G) (τ : ℕ)
    {E Z : Sq k} (hb : G.σ.blank = E) (hEZ : E ≠ Z) (hfree : ∀ Q, 3 ≤ ∑ y, G.free Q y) :
    LInv s σ0 F0 (hstep s τ G (.reloc E Z)) ∧ HInv s σ0 free0 N S0 (hstep s τ G (.reloc E Z)) := by
  have hL' := hReloc_linv hL hb hEZ hfree
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩ := hReloc_same (s := s) G E Z
  have hgh : gh s (hReloc s G E Z) = gh s G := by simp only [gh, r5]
  refine ⟨hL'.congr rfl rfl rfl rfl rfl rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h x hx
    show (hReloc s G E Z).stock h x + newCnt s (gh s (hReloc s G E Z)) h x =
      (hReloc s G E Z).out h x + (hReloc s G E Z).byp h x
    rw [r2, r3, r4, hgh]; exact hH.ident h x hx
  · intro h x
    show (hReloc s G E Z).byp h x ≤ _
    rw [r4]; exact hH.byp_le h x
  · intro Q
    have h1 := hH.free_lo Q
    have h2 := hReloc_free (s := s) G E Z Q
    show free0 Q + (hReloc s G E Z).sent Q + _ ≤ (∑ y, (hReloc s G E Z).free Q y) +
      (∑ x, (hReloc s G E Z).byp Q x) + (hReloc s G E Z).served Q +
      (if (hReloc s G E Z).σ.blank = Q then 1 else 0)
    rw [r7, r4, r6, r10]
    rw [hb] at h1
    simp only [@eq_comm _ E Q, @eq_comm _ Z Q] at h1 h2 ⊢
    omega
  · have h1 := hH.cost
    have h2 := hReloc_cost hL (Z := Z) hb hEZ hfree
    show IState.totalCost s σ0 (hReloc s G E Z).evs + pot s (hReloc s G E Z).σ ≤
      pot s σ0 + hopC k s * (∑ Q, (hReloc s G E Z).served Q) +
      (s + 3) * (21 * k + 9) * (∑ h, ∑ x, (hReloc s G E Z).byp h x) +
      (s + 3) * (G.wt + relocWeight (.reloc E Z)) + (s + 3) * (14 * k) * (hReloc s G E Z).fb
    rw [r6, r4]
    nlinarith
  · show (∑ Q, (hReloc s G E Z).served Q) + (∑ S', ∑ D', (hReloc s G E Z).sched S' D') = S0
    rw [r6, r1]; exact hH.sched_sum
  · exact (hReloc_fb G hEZ).trans hH.fbnd

end step

end SlidingPuzzle.Hub
