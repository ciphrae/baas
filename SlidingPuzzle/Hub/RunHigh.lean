import SlidingPuzzle.Hub.RunLocal
import SlidingPuzzle.Hub.RoundWalk

/-! # Resolving high-level events

`hServe` resolves `serve S D` (own column: `hop2 S D D`; own band: `hop1 S D D`;
otherwise through the hub `(S.1, D.2)`, from stock or after a bypass), and
`hReloc` resolves `reloc E Z` (one jump, or two through the corner
`(Z.1, E.2)`). This file proves the effect of each on the ghost state. -/
namespace SlidingPuzzle.Hub

open Finset

variable {k : ℕ}

/-- Some class with a free tile in `Z` (if there is one). -/
noncomputable def pickFree (G : GS k) (Z : Sq k) : Sq k :=
  if h : ∃ y, 1 ≤ G.free Z y then Classical.choose h else Z

theorem pickFree_spec (G : GS k) (Z : Sq k) (h : 1 ≤ ∑ y, G.free Z y) :
    1 ≤ G.free Z (pickFree G Z) := by
  have hex : ∃ y, 1 ≤ G.free Z y := by
    by_contra hne
    push Not at hne
    have : ∑ y, G.free Z y = 0 := sum_eq_zero fun y _ => by have := hne y; omega
    omega
  unfold pickFree
  rw [dif_pos hex]
  exact Classical.choose_spec hex

/-- Add one at `Q`. -/
def bump (f : Sq k → ℕ) (Q : Sq k) : Sq k → ℕ := fun Q' => f Q' + if Q' = Q then 1 else 0

/-- Record a bypass of class `x` at hub `h`. -/
def addByp (G : GS k) (h x : Sq k) : GS k := { G with byp := incCnt G.byp h x }

/-- Resolution of `serve S D`. -/
noncomputable def hServe (s τ : ℕ) (G : GS k) (S D : Sq k) : GS k :=
  if S.2 = D.2 then gHop2 s G false S D D
  else if S.1 = D.1 then gHop1 s τ G S D D
  else if 1 ≤ G.stock (S.1, D.2) D then
    gHop1 s τ (gHop2 s G true (S.1, D.2) D D) S (S.1, D.2) D
  else
    gHop1 s τ (addByp (gJump s G D (S.1, D.2) (pickFree G (S.1, D.2))) (S.1, D.2) D) S (S.1, D.2) D

/-- Resolution of `reloc E Z`. -/
noncomputable def hReloc (s : ℕ) (G : GS k) (E Z : Sq k) : GS k :=
  if E.1 = Z.1 ∨ E.2 = Z.2 then gJump s G E Z (pickFree G Z)
  else
    gJump s (gJump s G E (Z.1, E.2) (pickFree G (Z.1, E.2))) (Z.1, E.2) Z
      (pickFree (gJump s G E (Z.1, E.2) (pickFree G (Z.1, E.2))) Z)

/-- One high-level event of round `τ`. -/
noncomputable def hstep (s τ : ℕ) (G : GS k) : HEvent k → GS k
  | .serve S D =>
    { hServe s τ G S D with served := bump G.served D, sent := bump G.sent S }
  | .reloc E Z => { hReloc s G E Z with wt := G.wt + (1 + sqDist E Z) }

/-- The row insertion made by a high-level event. -/
def hIns (τ : ℕ) : HEvent k → Option (InsRec k)
  | .serve S D => if S.2 = D.2 then none else
      some ⟨τ, hop1Half S (S.1, D.2), hop1Dist S (S.1, D.2), D⟩
  | .reloc _ _ => none

/-- The square of the blank after an event. -/
def hNext : HEvent k → Sq k
  | .serve S _ => S
  | .reloc _ Z => Z

section congr

variable {s : ℕ} {σ0 : IState k} {F0 : ℕ}

theorem LInv.congr {G G' : GS k} (h : LInv s σ0 F0 G) (e1 : G'.σ = G.σ) (e2 : G'.evs = G.evs)
    (e3 : G'.ins = G.ins) (e4 : G'.sched = G.sched) (e5 : G'.stock = G.stock)
    (e6 : G'.free = G.free) (e7 : G'.out = G.out) : LInv s σ0 F0 G' := by
  have e8 : gh s G' = gh s G := by simp only [gh, e3]
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [e1, e2, e4, e5, e6, e7, e8] <;> assumption

end congr

/-! ## Stock identity through a hop1 -/

section ident

variable {s : ℕ} {σ0 : IState k} {F0 : ℕ}

theorem gHop1_ident {G : GS k} (hL : LInv s σ0 F0 G) (τ : ℕ) {S h y : Sq k}
    (h2 : S.2 ≠ h.2) (hs : k + 1 ≤ s) {h' x : Sq k} (hx : isStk h' x) :
    (gHop1 s τ G S h y).stock h' x + newCnt s (gh s (gHop1 s τ G S h y)) h' x + G.out h' x =
      G.stock h' x + newCnt s (gh s G) h' x + (gHop1 s τ G S h y).out h' x +
        (if h' = h ∧ y = x then 1 else 0) := by
  have e := hubCnt_gHop1 s τ G h2 hs y (fun o => o.map Prod.fst = some x) h'
  rw [← newCnt_eq_hubCnt, ← newCnt_eq_hubCnt] at e
  simp only [Option.map_some, Option.some.injEq] at e
  rw [gHop1_stock, gHop1_out]
  have key : (if isStk h (rowHead G S h) ∧ h' = h ∧ x = rowHead G S h then 1 else 0) =
      (if h' = h ∧ (gh s G (hop1Half S h) 0).map Prod.fst = some x then 1 else 0) +
      (if (isStk h (rowHead G S h) ∧ gh s G (hop1Half S h) 0 = none) ∧ h' = h ∧
        x = rowHead G S h then 1 else 0) := by
    by_cases hh : h' = h
    · subst hh
      rcases hg : gh s G (hop1Half S h') 0 with _ | ⟨x', d⟩
      · simp
      · have hr := (hL.ghost_row _ _ _ _ hg).1
        simp only [rowHead, hr, Option.map_some, Option.some.injEq, true_and, reduceCtorEq,
          and_false, false_and, if_false, add_zero]
        by_cases hxx : x = x'
        · subst hxx; simp [hx]
        · simp [hxx, Ne.symm hxx]
    · simp [hh]
  omega

end ident

/-! ## Effects of `hServe` -/

section serve

variable {s : ℕ} {σ0 : IState k} {F0 : ℕ}

theorem hServe_sched (τ : ℕ) (G : GS k) (S D : Sq k) :
    (hServe s τ G S D).sched = decCnt G.sched S D := by
  unfold hServe
  split_ifs
  · funext Q x; simp [gHop2, decCnt_apply]
  · rfl
  · rfl
  · rfl

theorem hServe_blank (τ : ℕ) (G : GS k) (S D : Sq k) : (hServe s τ G S D).σ.blank = S := by
  unfold hServe
  split_ifs <;> rfl

theorem hServe_ins (τ : ℕ) (G : GS k) (S D : Sq k) :
    (hServe s τ G S D).ins = G.ins ++ (hIns τ (.serve S D)).toList := by
  simp only [hIns]
  unfold hServe
  by_cases c1 : S.2 = D.2
  · simp [c1, gHop2]
  · rw [if_neg c1, if_neg c1]
    by_cases c2 : S.1 = D.1
    · have : D = (S.1, D.2) := Prod.ext c2.symm rfl
      rw [if_pos c2]
      simp only [gHop1, Option.toList_some]
      rw [← this]
    · rw [if_neg c2]
      split_ifs <;> rfl

theorem hServe_rest (τ : ℕ) (G : GS k) (S D : Sq k) :
    (hServe s τ G S D).served = G.served ∧ (hServe s τ G S D).sent = G.sent ∧
      (hServe s τ G S D).wt = G.wt ∧ (hServe s τ G S D).dd = G.dd := by
  unfold hServe
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem hServe_byp (τ : ℕ) (G : GS k) (S D : Sq k) :
    (hServe s τ G S D).byp = if S.2 ≠ D.2 ∧ S.1 ≠ D.1 ∧ G.stock (S.1, D.2) D = 0 then
      incCnt G.byp (S.1, D.2) D else G.byp := by
  unfold hServe
  split_ifs with c1 c2 c3 c4 c4 c4 c4 <;> first | rfl | omega

/-- Bundled hypotheses for a serve. -/
structure ServeOK (s : ℕ) (N : Sq k → Sq k → ℕ) (G : GS k) (S D : Sq k) : Prop where
  blank : G.σ.blank = D
  ne : S ≠ D
  sched : 1 ≤ G.sched S D
  newle : ∀ h x, newCnt s (gh s G) h x ≤ N h x
  free : ∀ Z, 1 ≤ ∑ y, G.free Z y
  room : k + 1 ≤ s

theorem hServe_linv {G : GS k} (hL : LInv s σ0 F0 G) {N : Sq k → Sq k → ℕ} (τ : ℕ)
    {S D : Sq k} (ok : ServeOK s N G S D) : LInv s σ0 F0 (hServe s τ G S D) := by
  unfold hServe
  split_ifs with c1 c2 c3
  · have h1 : S.1 ≠ D.1 := fun e => ok.ne (Prod.ext e c1)
    exact gHop2_linv hL ok.blank c1 h1 (by simpa using ok.sched) ok.room
  · exact gHop1_linv hL τ ok.blank c2 c1 rfl ok.sched ok.room
  · have hL1 := gHop2_linv hL (st := true) (h := (S.1, D.2)) ok.blank rfl c2
      (by simpa using c3) ok.room
    exact gHop1_linv hL1 τ rfl rfl c1 rfl ok.sched ok.room
  · have hf := pickFree_spec G (S.1, D.2) (ok.free _)
    have hL1 := gJump_linv hL (Z := (S.1, D.2)) ok.blank (fun e => c2 (congrArg Prod.fst e).symm)
      (Or.inr rfl) hf
    have hL2 := hL1.congr (G' := (addByp (gJump s G D (S.1, D.2) (pickFree G (S.1, D.2))) (S.1, D.2) D)) rfl rfl rfl rfl rfl rfl rfl
    exact gHop1_linv hL2 τ rfl rfl c1 rfl ok.sched ok.room

theorem hServe_of_col {s τ : ℕ} {G : GS k} {S D : Sq k} (c1 : S.2 = D.2) :
    hServe s τ G S D = gHop2 s G false S D D := by
  unfold hServe; rw [if_pos c1]

theorem hServe_of_row {s τ : ℕ} {G : GS k} {S D : Sq k} (c1 : S.2 ≠ D.2) (c2 : S.1 = D.1) :
    hServe s τ G S D = gHop1 s τ G S D D := by
  unfold hServe; rw [if_neg c1, if_pos c2]

theorem hServe_of_stock {s τ : ℕ} {G : GS k} {S D : Sq k} (c1 : S.2 ≠ D.2) (c2 : S.1 ≠ D.1)
    (c3 : 1 ≤ G.stock (S.1, D.2) D) :
    hServe s τ G S D = gHop1 s τ (gHop2 s G true (S.1, D.2) D D) S (S.1, D.2) D := by
  unfold hServe; rw [if_neg c1, if_neg c2, if_pos c3]

theorem hServe_of_byp {s τ : ℕ} {G : GS k} {S D : Sq k} (c1 : S.2 ≠ D.2) (c2 : S.1 ≠ D.1)
    (c3 : ¬ 1 ≤ G.stock (S.1, D.2) D) :
    hServe s τ G S D = gHop1 s τ (addByp (gJump s G D (S.1, D.2) (pickFree G (S.1, D.2))) (S.1, D.2) D) S (S.1, D.2) D := by
  unfold hServe; rw [if_neg c1, if_neg c2, if_neg c3]

theorem hServe_ident {G : GS k} (hL : LInv s σ0 F0 G) {N : Sq k → Sq k → ℕ} (τ : ℕ)
    {S D : Sq k} (ok : ServeOK s N G S D)
    (hI : ∀ h x, isStk h x → G.stock h x + newCnt s (gh s G) h x = G.out h x + G.byp h x)
    (h x : Sq k) (hx : isStk h x) :
    (hServe s τ G S D).stock h x + newCnt s (gh s (hServe s τ G S D)) h x =
      (hServe s τ G S D).out h x + (hServe s τ G S D).byp h x := by
  have hI0 := hI h x hx
  by_cases c1 : S.2 = D.2
  · rw [hServe_of_col c1]
    simpa [gHop2, gh] using hI0
  by_cases c2 : S.1 = D.1
  · rw [hServe_of_row c1 c2]
    have := gHop1_ident hL τ (h := D) (y := D) c1 ok.room hx
    have hne : ¬ (h = D ∧ D = x) := by
      rintro ⟨rfl, rfl⟩; exact hx.1 rfl
    rw [if_neg hne] at this
    have hb : (gHop1 s τ G S D D).byp = G.byp := rfl
    rw [hb]
    omega
  by_cases c3 : 1 ≤ G.stock (S.1, D.2) D
  · rw [hServe_of_stock c1 c2 c3]
    have hL1 := gHop2_linv hL (st := true) (h := (S.1, D.2)) ok.blank rfl c2
      (by simpa using c3) ok.room
    have := gHop1_ident hL1 τ (h := (S.1, D.2)) (y := D) c1 ok.room hx
    have e1 : gh s (gHop2 s G true (S.1, D.2) D D) = gh s G := rfl
    have hout : (gHop2 s G true (S.1, D.2) D D).out = G.out := rfl
    rw [e1, hout] at this
    have hst := gHop2_stock s G true (S.1, D.2) D D h x
    have hbyp2 : (gHop1 s τ (gHop2 s G true (S.1, D.2) D D) S (S.1, D.2) D).byp = G.byp := rfl
    rw [hbyp2]
    by_cases hc : h = (S.1, D.2) ∧ D = x
    · obtain ⟨rfl, rfl⟩ := hc
      simp only [and_self, if_true] at hst this
      omega
    · rw [if_neg hc] at this
      have : ¬ (true = true ∧ h = (S.1, D.2) ∧ x = D) := by
        rintro ⟨-, rfl, rfl⟩; exact hc ⟨rfl, rfl⟩
      rw [if_neg this] at hst
      omega
  · rw [hServe_of_byp c1 c2 c3]
    have hf := pickFree_spec G (S.1, D.2) (ok.free _)
    have hL1 := gJump_linv hL (Z := (S.1, D.2)) ok.blank (fun e => c2 (congrArg Prod.fst e).symm)
      (Or.inr rfl) hf
    have hL2 := hL1.congr (G' := (addByp (gJump s G D (S.1, D.2) (pickFree G (S.1, D.2))) (S.1, D.2) D)) rfl rfl rfl rfl rfl rfl rfl
    have := gHop1_ident hL2 τ (h := (S.1, D.2)) (y := D) c1 ok.room hx
    have e1 : gh s (addByp (gJump s G D (S.1, D.2) (pickFree G (S.1, D.2))) (S.1, D.2) D) = gh s G := rfl
    rw [e1] at this
    have hb : (gHop1 s τ (addByp (gJump s G D (S.1, D.2) (pickFree G (S.1, D.2))) (S.1, D.2) D)
      S (S.1, D.2) D).byp = incCnt G.byp (S.1, D.2) D := rfl
    rw [hb, incCnt_apply]
    have hst : (addByp (gJump s G D (S.1, D.2) (pickFree G (S.1, D.2))) (S.1, D.2) D).stock =
      G.stock := rfl
    have hou : (addByp (gJump s G D (S.1, D.2) (pickFree G (S.1, D.2))) (S.1, D.2) D).out =
      G.out := rfl
    rw [hst, hou] at this
    have hiff : (h = (S.1, D.2) ∧ D = x) ↔ (h = (S.1, D.2) ∧ x = D) := by
      constructor <;> rintro ⟨a, b⟩ <;> exact ⟨a, b.symm⟩
    simp only [hiff] at this
    omega

end serve

/-! ## Free tiles and bypasses -/

section free

variable (s : ℕ)

theorem sum_ind_eq (Q Z y : Sq k) :
    (∑ x : Sq k, if Q = Z ∧ x = y then 1 else 0) = if Q = Z then 1 else 0 := by
  by_cases h : Q = Z <;> simp [h]

theorem sum_free_gJump (G : GS k) (E Z y Q : Sq k) :
    (∑ x, G.free Q x) + (if Q = E then 1 else 0) ≤
      (∑ x, (gJump s G E Z y).free Q x) + (if Q = Z then 1 else 0) := by
  simp only [gJump_free]
  rw [← sum_ind_eq Q E y, ← sum_ind_eq Q Z y, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_le_sum fun x _ => ?_
  omega

theorem sum_free_gHop1 (τ : ℕ) (G : GS k) (S h y Q : Sq k) :
    (∑ x, G.free Q x) ≤ ∑ x, (gHop1 s τ G S h y).free Q x := by
  simp only [gHop1_free]
  exact sum_le_sum fun x _ => Nat.le_add_right _ _

theorem sum_free_gHop2 (G : GS k) (st : Bool) (h D y Q : Sq k) :
    (∑ x, G.free Q x) ≤ ∑ x, (gHop2 s G st h D y).free Q x := by
  simp only [gHop2_free]
  exact sum_le_sum fun x _ => Nat.le_add_right _ _

theorem hServe_free (τ : ℕ) (G : GS k) (S D Q : Sq k) :
    (∑ x, G.free Q x) + (∑ x, G.byp Q x) ≤
      (∑ x, (hServe s τ G S D).free Q x) + (∑ x, (hServe s τ G S D).byp Q x) := by
  by_cases c1 : S.2 = D.2
  · rw [hServe_of_col c1]
    have := sum_free_gHop2 s G false S D D Q
    have hb : (gHop2 s G false S D D).byp = G.byp := rfl
    rw [hb]; omega
  by_cases c2 : S.1 = D.1
  · rw [hServe_of_row c1 c2]
    have := sum_free_gHop1 s τ G S D D Q
    have hb : (gHop1 s τ G S D D).byp = G.byp := rfl
    rw [hb]; omega
  by_cases c3 : 1 ≤ G.stock (S.1, D.2) D
  · rw [hServe_of_stock c1 c2 c3]
    have := sum_free_gHop2 s G true (S.1, D.2) D D Q
    have := sum_free_gHop1 s τ (gHop2 s G true (S.1, D.2) D D) S (S.1, D.2) D Q
    have hb : (gHop1 s τ (gHop2 s G true (S.1, D.2) D D) S (S.1, D.2) D).byp = G.byp := rfl
    rw [hb]; omega
  · rw [hServe_of_byp c1 c2 c3]
    have h1 := sum_free_gJump s G D (S.1, D.2) (pickFree G (S.1, D.2)) Q
    have h2 := sum_free_gHop1 s τ (addByp (gJump s G D (S.1, D.2) (pickFree G (S.1, D.2)))
      (S.1, D.2) D) S (S.1, D.2) D Q
    have hb : (gHop1 s τ (addByp (gJump s G D (S.1, D.2) (pickFree G (S.1, D.2))) (S.1, D.2) D)
      S (S.1, D.2) D).byp = incCnt G.byp (S.1, D.2) D := rfl
    have hf : (addByp (gJump s G D (S.1, D.2) (pickFree G (S.1, D.2))) (S.1, D.2) D).free =
      (gJump s G D (S.1, D.2) (pickFree G (S.1, D.2))).free := rfl
    rw [hb, sum_incCnt]
    rw [hf] at h2
    split_ifs at h1 ⊢ <;> omega

theorem hServe_bypSum (τ : ℕ) (G : GS k) (S D : Sq k) :
    (∑ h, ∑ x, (hServe s τ G S D).byp h x) = (∑ h, ∑ x, G.byp h x) +
      if S.2 ≠ D.2 ∧ S.1 ≠ D.1 ∧ G.stock (S.1, D.2) D = 0 then 1 else 0 := by
  rw [hServe_byp]
  split_ifs
  · simp only [sum_incCnt, sum_add_distrib]
    simp
  · simp

theorem hServe_byp_le {G : GS k} {N : Sq k → Sq k → ℕ} (τ : ℕ) {S D : Sq k}
    (ok : ServeOK s N G S D)
    (hI : ∀ h x, isStk h x → G.stock h x + newCnt s (gh s G) h x = G.out h x + G.byp h x)
    (hB : ∀ h x, G.byp h x ≤ N h x + 1) (h x : Sq k) :
    (hServe s τ G S D).byp h x ≤ N h x + 1 := by
  rw [hServe_byp]
  split_ifs with c
  · rw [incCnt_apply]
    split_ifs with e
    · obtain ⟨e1, e2⟩ := e
      rw [e1, e2]
      have hstk : isStk (S.1, D.2) D := ⟨fun e => c.2.1 (congrArg Prod.fst e).symm, rfl⟩
      have := hI _ _ hstk
      have := ok.newle (S.1, D.2) D
      omega
    · exact hB h x
  · exact hB h x

end free

/-! ## Cost of a serve -/

section cost

variable {s : ℕ} {σ0 : IState k} {F0 : ℕ}

theorem hServe_cost {G : GS k} (hL : LInv s σ0 F0 G) {N : Sq k → Sq k → ℕ} (τ : ℕ)
    {S D : Sq k} (ok : ServeOK s N G S D) :
    IState.totalCost s σ0 (hServe s τ G S D).evs + pot s (hServe s τ G S D).σ +
        4000 * s * (1 + k) * (∑ h, ∑ x, G.byp h x) ≤
      IState.totalCost s σ0 G.evs + pot s G.σ + 2 * (4000 * s + 30 * k ^ 2) +
        4000 * s * (1 + k) * (∑ h, ∑ x, (hServe s τ G S D).byp h x) := by
  have hbs := hServe_bypSum s τ G S D
  by_cases c1 : S.2 = D.2
  · have h1 : S.1 ≠ D.1 := fun e => ok.ne (Prod.ext e c1)
    have := gHop2_cost hL (st := false) h1 ok.room
    rw [hServe_of_col c1]
    rw [if_neg (by tauto)] at hbs
    rw [hServe_of_col c1] at hbs
    rw [hbs]
    nlinarith
  by_cases c2 : S.1 = D.1
  · have := gHop1_cost hL τ (S := S) (h := D) (y := D) c1 rfl ok.room
    rw [hServe_of_row c1 c2] at hbs ⊢
    rw [if_neg (by tauto)] at hbs
    rw [hbs]
    nlinarith
  by_cases c3 : 1 ≤ G.stock (S.1, D.2) D
  · have hL1 := gHop2_linv hL (st := true) (h := (S.1, D.2)) ok.blank rfl c2
      (by simpa using c3) ok.room
    have e1 := gHop2_cost hL (st := true) (h := (S.1, D.2)) (D := D) c2 ok.room
    have e2 := gHop1_cost hL1 τ (S := S) (h := (S.1, D.2)) (y := D) c1 rfl ok.room
    rw [hServe_of_stock c1 c2 c3] at hbs ⊢
    rw [if_neg (by omega)] at hbs
    rw [hbs]
    nlinarith
  · have hf := pickFree_spec G (S.1, D.2) (ok.free _)
    have hL1 := gJump_linv hL (Z := (S.1, D.2)) ok.blank (fun e => c2 (congrArg Prod.fst e).symm)
      (Or.inr rfl) hf
    have hL2 := hL1.congr (G' := (addByp (gJump s G D (S.1, D.2) (pickFree G (S.1, D.2)))
      (S.1, D.2) D)) rfl rfl rfl rfl rfl rfl rfl
    have e1 := gJump_cost hL (E := D) (Z := (S.1, D.2)) (y := pickFree G (S.1, D.2))
    have e2 := gHop1_cost hL2 τ (S := S) (h := (S.1, D.2)) (y := D) c1 rfl ok.room
    have e3 : (addByp (gJump s G D (S.1, D.2) (pickFree G (S.1, D.2))) (S.1, D.2) D).evs =
      (gJump s G D (S.1, D.2) (pickFree G (S.1, D.2))).evs := rfl
    have e4 : (addByp (gJump s G D (S.1, D.2) (pickFree G (S.1, D.2))) (S.1, D.2) D).σ =
      (gJump s G D (S.1, D.2) (pickFree G (S.1, D.2))).σ := rfl
    rw [e3, e4] at e2
    rw [hServe_of_byp c1 c2 c3] at hbs ⊢
    rw [if_pos ⟨c1, c2, by omega⟩] at hbs
    rw [hbs]
    have hd : sqDist D (S.1, D.2) ≤ k := by
      unfold sqDist
      simp only [Nat.dist_self, add_zero]
      unfold Nat.dist
      have := D.1.isLt; have := S.1.isLt
      omega
    have : 4000 * s * (1 + sqDist D (S.1, D.2)) ≤ 4000 * s * (1 + k) :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith

end cost

end SlidingPuzzle.Hub
