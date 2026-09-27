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

theorem hReloc_of_al {G : GS k} {E Z : Sq k} (c : E.1 = Z.1 ∨ E.2 = Z.2) :
    hReloc s G E Z = gJump s G E Z (pickFree G Z) := by
  unfold hReloc; rw [if_pos c]

theorem hReloc_of_corner {G : GS k} {E Z : Sq k} (c : ¬ (E.1 = Z.1 ∨ E.2 = Z.2)) :
    hReloc s G E Z = gJump s (gJump s G E (Z.1, E.2) (pickFree G (Z.1, E.2))) (Z.1, E.2) Z
      (pickFree (gJump s G E (Z.1, E.2) (pickFree G (Z.1, E.2))) Z) := by
  unfold hReloc; rw [if_neg c]

theorem hReloc_same (G : GS k) (E Z : Sq k) :
    (hReloc s G E Z).sched = G.sched ∧ (hReloc s G E Z).stock = G.stock ∧
      (hReloc s G E Z).out = G.out ∧ (hReloc s G E Z).byp = G.byp ∧
      (hReloc s G E Z).ins = G.ins ∧ (hReloc s G E Z).served = G.served ∧
      (hReloc s G E Z).sent = G.sent ∧ (hReloc s G E Z).wt = G.wt ∧
      (hReloc s G E Z).dd = G.dd ∧ (hReloc s G E Z).σ.blank = Z := by
  unfold hReloc
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem corner_facts {E Z : Sq k} (c : ¬ (E.1 = Z.1 ∨ E.2 = Z.2)) :
    E ≠ (Z.1, E.2) ∧ (Z.1, E.2) ≠ Z := by
  have c1 : E.1 ≠ Z.1 := fun e => c (Or.inl e)
  have c2 : E.2 ≠ Z.2 := fun e => c (Or.inr e)
  refine ⟨fun e => c1 (by simpa using congrArg Prod.fst e),
    fun e => c2 (by simpa using congrArg Prod.snd e)⟩

theorem hReloc_linv {G : GS k} (hL : LInv s σ0 F0 G) {E Z : Sq k} (hb : G.σ.blank = E)
    (hEZ : E ≠ Z) (hfree : ∀ Q, 1 ≤ ∑ y, G.free Q y) : LInv s σ0 F0 (hReloc s G E Z) := by
  by_cases c : E.1 = Z.1 ∨ E.2 = Z.2
  · rw [hReloc_of_al c]
    exact gJump_linv hL hb hEZ c (pickFree_spec G Z (hfree Z))
  · rw [hReloc_of_corner c]
    obtain ⟨h1, h2⟩ := corner_facts c
    have hL1 := gJump_linv hL hb h1 (Or.inr rfl) (pickFree_spec G _ (hfree _))
    have hs := sum_free_gJump s G E (Z.1, E.2) (pickFree G (Z.1, E.2)) Z
    rw [if_neg (Ne.symm h2)] at hs
    have := hfree Z
    exact gJump_linv hL1 rfl h2 (Or.inl rfl) (pickFree_spec _ _ (by omega))

theorem hReloc_free (G : GS k) (E Z Q : Sq k) :
    (∑ x, G.free Q x) + (if Q = E then 1 else 0) ≤
      (∑ x, (hReloc s G E Z).free Q x) + (if Q = Z then 1 else 0) := by
  by_cases c : E.1 = Z.1 ∨ E.2 = Z.2
  · rw [hReloc_of_al c]; exact sum_free_gJump s G E Z _ Q
  · rw [hReloc_of_corner c]
    have h1 := sum_free_gJump s G E (Z.1, E.2) (pickFree G (Z.1, E.2)) Q
    have h2 := sum_free_gJump s (gJump s G E (Z.1, E.2) (pickFree G (Z.1, E.2))) (Z.1, E.2) Z
      (pickFree (gJump s G E (Z.1, E.2) (pickFree G (Z.1, E.2))) Z) Q
    omega

theorem hReloc_cost {G : GS k} (hL : LInv s σ0 F0 G) {E Z : Sq k} (hb : G.σ.blank = E)
    (hfree : ∀ Q, 1 ≤ ∑ y, G.free Q y) :
    IState.totalCost s σ0 (hReloc s G E Z).evs + pot s (hReloc s G E Z).σ ≤
      IState.totalCost s σ0 G.evs + pot s G.σ + (s + 3) * (if E.1 = Z.1 ∨ E.2 = Z.2 then 54 + 39 * sqDist E Z else 108 + 39 * sqDist E Z) := by
  by_cases c : E.1 = Z.1 ∨ E.2 = Z.2
  · rw [if_pos c, hReloc_of_al c]
    have := gJump_cost hL (E := E) (Z := Z) (y := pickFree G Z)
    nlinarith
  · rw [if_neg c, hReloc_of_corner c]
    obtain ⟨h1, h2⟩ := corner_facts c
    have hL1 := gJump_linv hL hb h1 (Or.inr rfl) (pickFree_spec G _ (hfree _))
    have e1 := gJump_cost hL (E := E) (Z := (Z.1, E.2)) (y := pickFree G (Z.1, E.2))
    have e2 := gJump_cost hL1 (E := (Z.1, E.2)) (Z := Z)
      (y := pickFree (gJump s G E (Z.1, E.2) (pickFree G (Z.1, E.2))) Z)
    have hd : sqDist E (Z.1, E.2) + sqDist (Z.1, E.2) Z = sqDist E Z := by
      unfold sqDist; simp only [Nat.dist_self]; ring
    have : (s + 3) * (54 + 39 * sqDist E (Z.1, E.2)) + (s + 3) * (54 + 39 * sqDist (Z.1, E.2) Z) ≤
        (s + 3) * (108 + 39 * sqDist E Z) := by
      rw [← hd]; nlinarith
    omega

end reloc

/-! ## The high-level invariant -/

/-- Budget constant of a hop. -/
def hopC (k s : ℕ) : ℕ := 55 * s + 13 * k ^ 2 + 65 * k + 78

/-- Invariants holding between high-level events. -/
structure HInv (s : ℕ) (σ0 : IState k) (free0 : Sq k → ℕ) (N : Sq k → Sq k → ℕ) (S0 : ℕ)
    (G : GS k) : Prop where
  ident : ∀ h x, isStk h x → G.stock h x + newCnt s (gh s G) h x = G.out h x + G.byp h x
  byp_le : ∀ h x, G.byp h x ≤ N h x + 1
  free_lo : ∀ Z, free0 Z + G.sent Z + (if σ0.blank = Z then 1 else 0) ≤
    (∑ y, G.free Z y) + (∑ x, G.byp Z x) + G.served Z + (if G.σ.blank = Z then 1 else 0)
  cost : IState.totalCost s σ0 G.evs + pot s G.σ ≤ pot s σ0 +
    2 * hopC k s * (∑ Z, G.served Z) + (s + 3) * (39 * k + 15) * (∑ h, ∑ x, G.byp h x) +
    (s + 3) * G.wt
  sched_sum : (∑ Z, G.served Z) + (∑ S, ∑ D, G.sched S D) = S0

section step

variable {s : ℕ} {σ0 : IState k} {F0 : ℕ} {free0 : Sq k → ℕ} {N : Sq k → Sq k → ℕ} {S0 : ℕ}

theorem sum_bump (f : Sq k → ℕ) (Q : Sq k) : ∑ Z, bump f Q Z = (∑ Z, f Z) + 1 := by
  simp [bump, sum_add_distrib]

theorem hstep_serve {G : GS k} (hL : LInv s σ0 F0 G) (hH : HInv s σ0 free0 N S0 G) (τ : ℕ)
    {S D : Sq k} (ok : ServeOK s N G S D) :
    LInv s σ0 F0 (hstep s τ G (.serve S D)) ∧ HInv s σ0 free0 N S0 (hstep s τ G (.serve S D)) := by
  have hL' := hServe_linv hL τ ok
  obtain ⟨r1, r2, r3, r4⟩ := hServe_rest (s := s) τ G S D
  refine ⟨hL'.congr rfl rfl rfl rfl rfl rfl rfl, ?_, ?_, ?_, ?_, ?_⟩
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
      pot s σ0 + 2 * hopC k s * (∑ Z, bump G.served D Z) +
      (s + 3) * (39 * k + 15) * (∑ h, ∑ x, (hServe s τ G S D).byp h x) +
      (s + 3) * (hServe s τ G S D).wt
    rw [sum_bump, r3]
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

theorem hstep_reloc {G : GS k} (hL : LInv s σ0 F0 G) (hH : HInv s σ0 free0 N S0 G) (τ : ℕ)
    {E Z : Sq k} (hb : G.σ.blank = E) (hEZ : E ≠ Z) (hfree : ∀ Q, 1 ≤ ∑ y, G.free Q y) :
    LInv s σ0 F0 (hstep s τ G (.reloc E Z)) ∧ HInv s σ0 free0 N S0 (hstep s τ G (.reloc E Z)) := by
  have hL' := hReloc_linv hL hb hEZ hfree
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩ := hReloc_same (s := s) G E Z
  have hgh : gh s (hReloc s G E Z) = gh s G := by simp only [gh, r5]
  refine ⟨hL'.congr rfl rfl rfl rfl rfl rfl rfl, ?_, ?_, ?_, ?_, ?_⟩
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
    have h2 := hReloc_cost hL (Z := Z) hb hfree
    show IState.totalCost s σ0 (hReloc s G E Z).evs + pot s (hReloc s G E Z).σ ≤
      pot s σ0 + 2 * hopC k s * (∑ Q, (hReloc s G E Z).served Q) +
      (s + 3) * (39 * k + 15) * (∑ h, ∑ x, (hReloc s G E Z).byp h x) +
      (s + 3) * (G.wt + (if E.1 = Z.1 ∨ E.2 = Z.2 then 54 + 39 * sqDist E Z else 108 + 39 * sqDist E Z))
    rw [r6, r4]
    nlinarith
  · show (∑ Q, (hReloc s G E Z).served Q) + (∑ S', ∑ D', (hReloc s G E Z).sched S' D') = S0
    rw [r6, r1]; exact hH.sched_sum

end step

end SlidingPuzzle.Hub
