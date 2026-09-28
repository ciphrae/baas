import SlidingPuzzle.Tree.RunAux

/-! # The abstract run exists, is valid and cheap

From an `IState` (the abstraction of the prepared input board), build the plan
(`exists_rounds`), order its rounds (`exists_uniform_residence`), walk every
round (`exists_round_events`) and resolve every event: serves along the whole
route, relocations by jumps. -/
namespace SlidingPuzzle.Tree
open Finset
open SlidingPuzzle.Hub (Sq Round sends recv IsLast exists_rounds ind dummyAt roundW idleRound
  roundEvs)

variable {k q : ℕ} (L : LaneSys k q)

/-- The initial ghost state. -/
def G0 (σ0 : IState k q) (R : Sq k → ℕ) : GS k q where
  σ := σ0
  evs := []
  ins := []
  sched := tdemand σ0
  stock := fun _ _ => 0
  free := fun Q y => if y = Q then R Q else 0
  B := fun _ _ => 0
  dA := fun _ _ => 0
  served := fun _ => 0
  sent := fun _ => 0
  nh := 0
  jc := 0
  wt := 0

theorem gh_G0 (s : ℕ) (σ0 : IState k q) (R : Sq k → ℕ) :
    gh k s (G0 σ0 R) = fun _ _ => none := rfl

theorem lcnt_none (s : ℕ) (G : GS k q) (hG : gh k s G = fun _ _ => none) (V : Ln k q → Prop)
    [DecidablePred V] (P : Option (GCls k × ℕ) → Prop) [DecidablePred P] (hP : ¬ P none) :
    lcnt L s G V P = 0 := by
  unfold lcnt
  apply Finset.sum_eq_zero
  intro l _
  split_ifs
  · rw [hG]; simp [hP]
  · rfl

/-- Transport budget. -/
def runCost (n k q s depth lc nd : ℕ) : ℕ :=
  lc * (k * s) + hopK k q s * (2 * depth * n ^ 2) + (k * s) * ((2 * depth + 1) * nd) +
    3 * (s + 3) * (s ^ 2 * (15 * k ^ 2 + 30 * k + 18) + (14 * k + 18) * (lc + k ^ 2))

theorem sum_dA_le (dA B : Sq k → Sq k → ℕ)
    (hdA : ∀ v x, dA v x ≤ ∑ u ∈ univ.filter (fun u => u ≠ x ∧ L.nxt u x = v), B u x) :
    ∑ v, ∑ x, dA v x ≤ ∑ v, ∑ x, B v x := by
  rw [Finset.sum_comm, Finset.sum_comm (f := fun v x => B v x)]
  refine sum_le_sum fun x _ => ?_
  calc ∑ v, dA v x ≤ ∑ v, ∑ u ∈ univ.filter (fun u => u ≠ x ∧ L.nxt u x = v), B u x :=
        sum_le_sum fun v _ => hdA v x
    _ = ∑ u ∈ univ.filter (fun u => u ≠ x), B u x := by
        rw [Finset.sum_comm' (t' := univ.filter (fun u => u ≠ x)) (s' := fun u => {L.nxt u x})]
        · simp
        · intro v u; simp only [mem_filter, mem_univ, true_and, mem_singleton]; aesop
    _ ≤ ∑ u, B u x := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)

theorem pot_le (s : ℕ) (σ : IState k q) : σ.pot L s ≤ laneCells L s * (k * s) := by
  unfold IState.pot
  have h1 : ∀ l : Ln k q, ∑ r ∈ (range (llen L s l)).filter (fun r => ¬ lgood l (σ.lane l r)), (r + 1)
      ≤ llen L s l * (k * s) := by
    intro l
    calc _ ≤ ∑ r ∈ range (llen L s l), (k * s) := by
          refine le_trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun _ _ _ => Nat.zero_le _)) (sum_le_sum fun r hr => ?_)
          have := llen_le L s l; simp at hr; omega
      _ = llen L s l * (k * s) := by simp
  refine (sum_le_sum fun l _ => h1 l).trans ?_
  rw [← sum_mul]
  apply Nat.mul_le_mul_right
  unfold laneCells
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp [llen, add_comm]

/-- The bounds at the end of the run. -/
theorem outer_final {n s : ℕ} (c : Ctx k q) (_hcs : c.s = s) (Gf : GS k q)
    (hOf : Outer L c c.Δ Gf) (need : Sq k → ℕ)
    (hNv : ∀ Z, ∑ x, (c.Nv Z x + if L.Act Z x then 1 else 0) ≤ need Z)
    (hS0 : c.S0 ≤ n ^ 2) {W P : ℕ} (hW : ∑ τ ∈ range c.Δ, roundW (c.rd τ) ≤ W)
    (hpot : c.σ0.pot L c.s ≤ P) :
    c.σ0.Valid L c.s Gf.evs ∧
      c.σ0.totalCost c.s Gf.evs ≤ P + hopK k q c.s * (2 * L.depth * n ^ 2) +
        (k * c.s) * ((2 * L.depth + 1) * ∑ v, need v) + 3 * (c.s + 3) * W ∧
      (c.σ0.run c.s Gf.evs).offCount ≤ (∑ v, need v) + c.F0 := by
  have hsch0 : ∀ S D, Gf.sched S D = 0 := by
    intro S D; rw [hOf.sched]; simp
  have hserved : ∑ Z, Gf.served Z ≤ n ^ 2 := by
    have := hOf.hin.sched_sum; omega
  have hdA : ∀ v x, Gf.dA v x ≤ ∑ u ∈ univ.filter (fun u => u ≠ x ∧ L.nxt u x = v), Gf.B u x :=
    fun v x => by have := hOf.hin.dirty v x; omega
  have hBc : ∀ v x, Gf.B v x ≤ Gf.dA v x + (c.Nv v x + if L.Act v x then 1 else 0) := by
    intro v x
    obtain ⟨h1, h2⟩ := hOf.hin.binv v x
    split_ifs with ha
    · omega
    · have : Gf.B v x = 0 := by by_contra h0; exact ha (h2 h0)
      omega
  have hBtot : ∑ v, ∑ x, Gf.B v x ≤ (2 * L.depth + 1) * ∑ v, need v := by
    rw [Finset.sum_comm]
    calc ∑ x, ∑ v, Gf.B v x ≤ ∑ x, (2 * L.depth + 1) * ∑ v,
          (c.Nv v x + if L.Act v x then 1 else 0) :=
          sum_le_sum fun x _ => sum_B_le L Gf.B Gf.dA
            (fun v x => c.Nv v x + if L.Act v x then 1 else 0) x (fun v => hBc v x)
            (fun v => hdA v x)
      _ = (2 * L.depth + 1) * ∑ v, ∑ x, (c.Nv v x + if L.Act v x then 1 else 0) := by
          rw [← mul_sum, Finset.sum_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ (sum_le_sum fun v _ => hNv v)
  refine ⟨hOf.lin.valid, ?_, ?_⟩
  · have hcost := hOf.lin.cost
    have h3 : hopK k q c.s * Gf.nh ≤ hopK k q c.s * (2 * L.depth * n ^ 2) :=
      Nat.mul_le_mul_left _ (hOf.hin.nh.trans (Nat.mul_le_mul_left _ hserved))
    have h4 := Nat.mul_le_mul_left (k * c.s) hBtot
    have h5 : Gf.jc ≤ 3 * (c.s + 3) * W := hOf.hin.jc.trans (Nat.mul_le_mul_left _ (hOf.wt.trans hW))
    have := Nat.zero_le (Gf.σ.pot L c.s)
    omega
  · rw [← hOf.lin.run_eq]
    have hoff : Gf.σ.offCount ≤ ∑ Q, ∑ y, (Gf.stock Q y + Gf.free Q y) := by
      unfold IState.offCount
      refine sum_le_sum fun Q _ => sum_le_sum fun y _ => ?_
      split_ifs with hy
      · exact Nat.zero_le _
      · have := hOf.lin.roles_ge Q y hy; rw [hsch0] at this; omega
    have hstock : ∀ v x, Gf.stock v x ≤ c.Nv v x + if L.Act v x then 1 else 0 := by
      intro v x
      by_cases hvx : v = x
      · subst hvx; rw [hOf.lin.stock_diag]; exact Nat.zero_le _
      · have h1 := hOf.hin.ident v x hvx
        have h2 := hBc v x
        omega
    have hst : ∑ Q, ∑ y, Gf.stock Q y ≤ ∑ v, need v :=
      sum_le_sum fun v _ => (sum_le_sum fun x _ => hstock v x).trans (hNv v)
    have hdAtot : ∑ v, ∑ x, Gf.dA v x ≤ ∑ v, ∑ x, Gf.B v x :=
      sum_dA_le L Gf.dA Gf.B hdA
    have hfr := hOf.lin.free_tot
    have hsplit : ∑ Q, ∑ y, (Gf.stock Q y + Gf.free Q y) =
        (∑ Q, ∑ y, Gf.stock Q y) + ∑ Q, ∑ y, Gf.free Q y := by
      simp [sum_add_distrib]
    omega

theorem exists_valid_run {n s : ℕ} [NeZero n] (td : TDims n k s q) (σ0 : IState k q)
    (rsz : Sq k → ℕ)
    (hF1 : ∀ Q, (∑ y, σ0.cnt Q y) + (if σ0.blank = Q then 1 else 0) = rsz Q)
    (hF2 : ∀ y, (∑ Q, σ0.cnt Q y) + σ0.corrCount L s y = s ^ 2 - (if IsLast y then 1 else 0))
    (hrsz : ∀ S, rsz S ≤ s ^ 2) (hlane : ∑ Q, (s ^ 2 - rsz Q) ≤ laneCells L s)
    (R : Sq k → ℕ) (hR : ∀ Q, R Q ≤ σ0.cnt Q Q)
    (hRn : ∀ Q, Rneed L s (GroupedOrder.lamN n) rsz Q ≤ R Q)
    {la : ℕ} (hcap : 76 * k * la ≤ 5 * s)
    (hcA : 2 * (4 * k ^ 2 * q * k * s ^ 2) ≤ 2 ^ la)
    (hcB : 2 * (4 * k ^ 2 * q * k ^ 2 * s ^ 2) < 2 ^ GroupedOrder.lamN n) :
    ∃ es : List (REvent k q), σ0.Valid L s es ∧
      σ0.totalCost s es ≤ runCost n k q s L.depth (laneCells L s)
        (∑ v, needAt L s (GroupedOrder.lamN n) v) ∧
      (σ0.run s es).offCount ≤ (∑ v, needAt L s (GroupedOrder.lamN n) v) +
        ((∑ Q, R Q) + laneCells L s) := by
  classical
  have hk2 := td.hd.two_le
  have hq2 := td.two_le_q
  have hks := td.k_lt_s
  have hqs := td.q_lt_s
  -- the plan
  obtain ⟨Δ0, rs0, hc1, hc2, hc3, hc4, hc5⟩ := exists_rounds (tdemand σ0) (tdemand_diag σ0)
  have hmx := tmax_le L σ0 rsz hF1 hF2 hrsz
  have hΔ0 : Δ0 ≤ s ^ 2 := hc5 _ (fun S => hmx S)
  -- the good order
  set rs : Fin Δ0 → List (Ln k q × ℕ × Sq k) := fun j => roundIns L (rs0 j) with hrs
  have hk : 0 < k := by omega
  have hoff : ∀ H : Ln k q, loff k s H < lstep s H := by
    intro H; unfold loff lstep; split_ifs <;> omega
  have hst : ∀ H : Ln k q, lstep s H ≤ s := by
    intro H; unfold lstep; split_ifs <;> omega
  have hsupp : ∀ j, ∀ p ∈ rs j, p.2.1 < blen L p.1.2 ∧ p.2.2 ∈ Xs L p.1 :=
    fun j p hp => roundIns_supp L (rs0 j) p hp
  have hdk : ∀ j, ∀ p ∈ rs j, p.2.1 < k :=
    fun j p hp => lt_of_lt_of_le (hsupp j p hp).1 (blen_le L _)
  have hbatch : ∀ j H (Q : Ln k q × ℕ × Sq k → Prop) [DecidablePred Q],
      (rs j).countP (fun p => decide (p.1 = H ∧ Q p)) ≤ k := by
    intro j H Q _
    refine le_trans (List.countP_mono_left fun p _ h => ?_) (roundIns_batch L (rs0 j) H)
    simp only [decide_eq_true_eq] at h ⊢; exact h.1
  have hclass : ∀ j H x, ∑ d ∈ range k, (rs j).countP (fun p => decide (p = (H, d, x))) ≤ 1 :=
    fun j H x => roundIns_class L (rs0 j) H x
  have hcA' : 2 * Fintype.card (Ln k q × Fin k × Fin Δ0) ≤ 2 ^ la := by
    rw [Fintype.card_prod, card_Ln, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    refine le_trans ?_ hcA
    have := Nat.mul_le_mul_left (2 * (4 * k ^ 2 * q * k)) hΔ0
    nlinarith
  have hcB' : 2 * Fintype.card (Ln k q × Sq k × Fin Δ0) < 2 ^ GroupedOrder.lamN n := by
    rw [Fintype.card_prod, card_Ln, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
    refine lt_of_le_of_lt ?_ hcB
    have := Nat.mul_le_mul_left (2 * (4 * k ^ 2 * q * (k * k))) hΔ0
    nlinarith
  obtain ⟨σo, hbud, hres⟩ := GroupedOrder.exists_uniform_residence k s rs n (lstep s) (loff k s)
    hoff hst (fun l => blen L l.2) (Xs L) hk hdk hsupp hbatch hclass hcap hcA' hcB'
  -- the run
  set rd := ordR rs0 σo with hrd
  set G00 := G0 σ0 R with hG00
  set Gf := runRounds L s rd Δ0 G00 with hGf
  obtain ⟨i1, i2, i3⟩ := runRounds_consistent L s rd G00 rfl Δ0
  set Lres := Gf.ins.map toRes with hLres
  have hperm : ∀ τ, ((Lres.filter fun e => e.τ = τ).map GroupedPipe.proj).Perm
      (GroupedOrder.rnd rs σo τ) := by
    intro τ
    by_cases hτ : τ < Δ0
    · have e : GroupedOrder.rnd rs σo τ = roundIns L (rd τ) := by
        simp [GroupedOrder.rnd, hτ, hrd, ordR, hrs]
      rw [e]; exact i3 τ hτ
    · have e1 : GroupedOrder.rnd rs σo τ = [] := by simp [GroupedOrder.rnd, hτ]
      have e2 : Lres.filter (fun e => decide (e.τ = τ)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx; have := i1 x hx; simp; omega
      rw [e1, e2]; rfl
  have k0 : Fin k := ⟨0, by omega⟩
  have q0 : Fin q := ⟨0, by omega⟩
  have r0 : GroupedPipe.InsRec (Ln k q) (Sq k) := ⟨0, (false, ⟨k0, q0, k0, false⟩), 0, (k0, k0)⟩
  have hres' := hres Lres r0 i2 i1 hperm
  set N : Ln k q → Sq k → ℕ := fun l x => GroupedOrder.Nbx k s rs n l x with hN
  have hFb : ∀ G' : GS k q, G'.ins <+: Gf.ins → ∀ v x, Fcnt L s G' v x ≤ NvOf N v x := by
    intro G' hG' v x
    exact Fcnt_le L s N Lres hres' G' (hG'.map toRes) v x
  -- per-lane budgets in natural numbers
  have hbudN : ∀ l, ∑ x, N l x ≤ laneBud L s (GroupedOrder.lamN n) l := by
    intro l
    have h := hbud l
    have h2 : (41 / 30 * ((blen L l.2 : ℕ) * s : ℝ) + 41 / 40 * (k * ((blen L l.2 : ℕ) + 1)) +
        ((Xs L l).card : ℝ) * (15 * GroupedOrder.lamN n)) ≤ (laneBud L s (GroupedOrder.lamN n) l : ℝ) := by
      unfold laneBud; push_cast
      have : (0 : ℝ) ≤ (blen L l.2 : ℝ) * s := by positivity
      have : (0 : ℝ) ≤ (k : ℝ) * ((blen L l.2 : ℝ) + 1) := by positivity
      nlinarith
    have h3 : ((∑ x, N l x : ℕ) : ℝ) ≤ (laneBud L s (GroupedOrder.lamN n) l : ℝ) := by
      push_cast; exact h.trans h2
    exact_mod_cast h3
  have hNv : ∀ Z, ∑ x, (NvOf N Z x + if L.Act Z x then 1 else 0) ≤
      needAt L s (GroupedOrder.lamN n) Z := by
    intro Z
    rw [sum_add_distrib]
    have h1 : ∑ x, NvOf N Z x ≤ ∑ l ∈ univ.filter (fun l : Ln k q => land l = Z),
        laneBud L s (GroupedOrder.lamN n) l := by
      unfold NvOf; rw [Finset.sum_comm]; exact sum_le_sum fun l _ => hbudN l
    have h2 := card_act_le L Z
    unfold needAt; rw [sum_add_distrib]
    omega
  -- the context
  set c : Ctx k q := ⟨s, σ0, (∑ Q, R Q) + laneCells L s, R, NvOf N,
    ∑ S, ∑ D, tdemand σ0 S D, Gf.ins, rd, Δ0,
    fun Z => recv (tdemand σ0) Z - sends (tdemand σ0) Z⟩ with hcdef
  have hdum : ∀ Z, ∑ τ ∈ range Δ0, dummyAt (rd τ) Z = recv (tdemand σ0) Z - sends (tdemand σ0) Z := by
    intro Z
    rw [hrd, sum_ordR rs0 σo (fun r => dummyAt r Z), ← hc2 Z, card_filter]
    rfl
  have hcOK : c.OK L := by
    refine ⟨hFb, ?_, fun Z => le_of_eq (hdum Z)⟩
    intro _ Z
    have h1 := hNv Z
    have h2 := trecv_sub_sends L σ0 rsz hF1 hF2 Z
    have h3 := hRn Z
    unfold Rneed at h3
    show (∑ x, (NvOf N Z x + if L.Act Z x then 1 else 0)) +
      (recv (tdemand σ0) Z - sends (tdemand σ0) Z) + 5 ≤ R Z
    omega
  -- the initial state
  have hgh0 : gh k s G00 = fun _ _ => none := rfl
  have hunt0 : untagged L s G00 = laneCells L s := by
    unfold untagged lcnt laneCells
    rw [hgh0]
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp [llen, add_comm]
  have hfr0 : ∀ Z, fr G00 Z = R Z := by
    intro Z; unfold fr; simp [hG00, G0]
  have hL0 : LInv L s σ0 ((∑ Q, R Q) + laneCells L s) G00 := by
    refine ⟨?_, ?_, fun _ => rfl, ?_, ?_, rfl, trivial, ?_, ?_⟩
    · intro Q y
      by_cases hQy : y = Q
      · subst hQy; simp only [hG00, G0, tdemand, if_true]; have := hR y; omega
      · simp only [hG00, G0, tdemand, if_neg hQy, if_neg (Ne.symm hQy)]; omega
    · intro Q y hy
      simp only [hG00, G0, tdemand, if_neg (Ne.symm hy), if_neg hy]; omega
    · intro l r x d h; rw [hgh0] at h; cases h
    · intro l r h; rw [hgh0] at h; exact absurd rfl h
    · simp [hG00, G0, IState.totalCost]
    · rw [hunt0]
      simp only [hG00, G0, sum_const_zero, add_zero]
      congr 1
      refine sum_congr rfl fun Q _ => ?_
      simp
  have hH0 : HInv L c G00 := by
    refine ⟨?_, ?_, ?_, ?_, le_of_eq (by simp [hG00, G0]), by simp [hG00, G0],
      by simp [hG00, G0]; rfl⟩
    · intro v x _
      have := lcnt_none L s G00 hgh0 (fun l => land l = v) (fun g => gtg g = some x) (by simp [gtg])
      show 0 + Fcnt L s G00 v x + 0 = 0
      unfold Fcnt; rw [this]
    · intro v x
      have := lcnt_none L s G00 hgh0 (fun l => land l = v) (fun g => gdt g = some x) (by simp [gdt])
      show 0 + Dpos L s G00 v x = ∑ u ∈ _, 0
      unfold Dpos; rw [this]; simp
    · intro v x; simp [hG00, G0]
    · intro Z
      show R Z + 0 + _ + sA G00 Z ≤ fr G00 Z + sB G00 Z + 0 + _
      have e1 : sA G00 Z = 0 := by simp [sA, hG00, G0]
      have e2 : sB G00 Z = 0 := by simp [sB, hG00, G0]
      rw [e1, e2, hfr0]
      simp [hG00, G0]
      exact le_rfl
  have hO0 : Outer L c 0 G00 := by
    refine ⟨Nat.zero_le _, hL0, hH0, ?_, fun Z => by simp [hG00, G0], by simp [hG00, G0]⟩
    intro S D
    show tdemand σ0 S D = ∑ τ ∈ Ico 0 Δ0, ind (rd τ) S D
    rw [← range_eq_Ico, hrd, sum_ordR rs0 σo (fun r => ind r S D), ← hc1 S D, card_filter]
    rfl
  have hOf : Outer L c Δ0 Gf := Outer.all L hcOK td hO0 rfl Δ0 le_rfl
  have hS0 : c.S0 ≤ n ^ 2 := by
    have hn : n = k * s := td.mul.symm
    have : ∀ S, ∑ D, tdemand σ0 S D ≤ s ^ 2 := fun S => (hmx S).1
    refine (sum_le_sum fun S _ => this S).trans ?_
    simp [Fintype.card_prod, hn]; ring_nf; exact le_refl _
  have hW : ∑ τ ∈ range c.Δ, roundW (c.rd τ) ≤
      s ^ 2 * (15 * k ^ 2 + 30 * k + 18) + (14 * k + 18) * (laneCells L s + k ^ 2) := by
    have hdc : ∀ r : Round k, (univ.filter fun S => r.isDummy S).card = ∑ S, dummyAt r S := by
      intro r; rw [card_filter]; rfl
    show ∑ τ ∈ range Δ0, roundW (rd τ) ≤ _
    simp only [roundW, hdc, sum_add_distrib, sum_const, card_range, smul_eq_mul, ← mul_sum]
    rw [sum_comm]
    have h1 : ∑ S : Sq k, ∑ τ ∈ range Δ0, dummyAt (rd τ) S ≤ laneCells L s + k ^ 2 := by
      simp only [hdum]
      calc ∑ S : Sq k, (recv (tdemand σ0) S - sends (tdemand σ0) S)
          ≤ ∑ S : Sq k, ((s ^ 2 - rsz S) + 1) :=
            sum_le_sum fun S _ => trecv_sub_sends L σ0 rsz hF1 hF2 S
        _ ≤ laneCells L s + k ^ 2 := by
            rw [sum_add_distrib]; simp [Fintype.card_prod]; nlinarith [hlane]
    have h2 : Δ0 * (15 * k ^ 2 + 30 * k + 18) ≤ s ^ 2 * (15 * k ^ 2 + 30 * k + 18) :=
      Nat.mul_le_mul_right _ hΔ0
    nlinarith
  obtain ⟨h1, h2, h3⟩ := outer_final L c rfl Gf hOf (needAt L s (GroupedOrder.lamN n)) hNv hS0 hW
    (pot_le L s σ0)
  exact ⟨Gf.evs, h1, by unfold runCost; exact h2, h3⟩

end SlidingPuzzle.Tree
