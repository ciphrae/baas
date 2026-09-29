import SlidingPuzzle.Port.Final

/-! # The port run exists, is valid and cheap

As `Tree.exists_valid_run`, from a `PState` whose ports can hold the stock of their
square (`hpsz`). -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle.Hub (Sq Round sends recv IsLast exists_rounds ind dummyAt roundW idleRound
  roundEvs)
open SlidingPuzzle.Tree

variable {k q : ℕ} (L : LaneSys k q)

theorem exists_valid_prun {n s : ℕ} [NeZero n] (td : TDims n k s q) (σ' : ℕ) (σ0 : PState k q)
    (rsz : Sq k → ℕ)
    (hF1 : ∀ Q, (∑ y, σ0.cnt Q y) + (if σ0.blank = Q then 1 else 0) = rsz Q)
    (hF2 : ∀ y, (∑ Q, σ0.cnt Q y) + σ0.toI.corrCount L s y = s ^ 2 - (if IsLast y then 1 else 0))
    (hrsz : ∀ S, rsz S ≤ s ^ 2) (hlane : ∑ Q, (s ^ 2 - rsz Q) ≤ laneCells L s)
    (R : Sq k → ℕ) (hR : ∀ Q, R Q ≤ σ0.cnt Q Q)
    (hRn : ∀ Q, Rneed L s (GroupedOrder.lamN n) rsz Q ≤ R Q)
    (hpc : ∀ Q y, ∑ pt, σ0.pc Q pt y ≤ σ0.cnt Q y)
    (hpsz : ∀ Q pt, needAt L s (GroupedOrder.lamN n) Q + 1 < psz σ0 Q pt)
    {la : ℕ} (hcap : 76 * k * la ≤ 5 * s)
    (hcA : 2 * (4 * k ^ 2 * q * k * s ^ 2) ≤ 2 ^ la)
    (hcB : 2 * (4 * k ^ 2 * q * k ^ 2 * s ^ 2) < 2 ^ GroupedOrder.lamN n) :
    ∃ es : List (PEvent k q), σ0.Valid L s es ∧
      σ0.totalCost s σ' es ≤ prunCost n k q s σ' L.depth (laneCells L s)
        (∑ v, needAt L s (GroupedOrder.lamN n) v)
        (s ^ 2 * (15 * k ^ 2 + 30 * k + 18) + (14 * k + 18) * (laneCells L s + k ^ 2)) ∧
      (σ0.run s es).offCount ≤ (∑ v, needAt L s (GroupedOrder.lamN n) v) +
        ((∑ Q, R Q) + laneCells L s) := by
  classical
  have hk2 := td.hd.two_le
  have hq2 := td.two_le_q
  have hks := td.k_lt_s
  have hqs := td.q_lt_s
  -- the plan
  obtain ⟨Δ0, rs0, hc1, hc2, hc3, hc4, hc5⟩ := exists_rounds (tdemand σ0.toI) (tdemand_diag σ0.toI)
  have hmx := tmax_le L σ0.toI rsz hF1 hF2 hrsz
  have hΔ0 : Δ0 ≤ s ^ 2 := hc5 _ (fun S => hmx S)
  -- the good order
  set rs : Fin Δ0 → List (Ln k q × ℕ × Sq k) := fun j => roundIns L (rs0 j) with hrs
  have hk : 0 < k := by omega
  have hqk := td.q_le
  have hoff : ∀ H : Ln k q, loffP k s H < lstep s H := by
    intro H; unfold loffP lstep; split_ifs <;> omega
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
  obtain ⟨σo, hbud, hres⟩ := GroupedOrder.exists_uniform_residence k s rs n (lstep s) (loffP k s)
    hoff hst (fun l => blen L l.2) (Xs L) hk hdk hsupp hbatch hclass hcap hcA' hcB'
  -- the run
  set rd := ordR rs0 σo with hrd
  set G00 := PG0 σ0 R with hG00
  set Gf := prunRounds L s σ' rd Δ0 G00 with hGf
  obtain ⟨i1, i2, i3⟩ := prunRounds_consistent L s σ' rd G00 rfl Δ0
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
  have hFb : ∀ G' : PG k q, G'.ins <+: Gf.ins → ∀ v x, pFcnt L s G' v x ≤ NvOf N v x := by
    intro G' hG' v x
    exact pFcnt_le L s N Lres hres' G' (hG'.map toRes) v x
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
  set c : PCtx k q := ⟨s, σ', σ0, (∑ Q, R Q) + laneCells L s, R, NvOf N,
    ∑ S, ∑ D, tdemand σ0.toI S D, Gf.ins, rd, Δ0,
    fun Z => recv (tdemand σ0.toI) Z - sends (tdemand σ0.toI) Z⟩ with hcdef
  have hdum : ∀ Z, ∑ τ ∈ range Δ0, dummyAt (rd τ) Z = recv (tdemand σ0.toI) Z - sends (tdemand σ0.toI) Z := by
    intro Z
    rw [hrd, sum_ordR rs0 σo (fun r => dummyAt r Z), ← hc2 Z, card_filter]
    rfl
  have hcOK : c.OK L := by
    refine ⟨hFb, ?_, fun Z => le_of_eq (hdum Z), ?_⟩
    · intro _ Z
      have h1 := hNv Z
      have h2 := trecv_sub_sends L σ0.toI rsz hF1 hF2 Z
      have h3 := hRn Z
      unfold Rneed at h3
      show stkCap L (NvOf N) Z +
        (recv (tdemand σ0.toI) Z - sends (tdemand σ0.toI) Z) + 5 ≤ R Z
      unfold stkCap
      omega
    · intro Q pt
      have := hNv Q
      have := hpsz Q pt
      show stkCap L (NvOf N) Q + 1 < psz σ0 Q pt
      unfold stkCap
      omega
  -- the initial state
  have hgh0 : pgh k s G00 = fun _ _ => none := rfl
  have hunt0 : puntagged L s G00 = laneCells L s := by
    unfold puntagged plcnt laneCells
    rw [hgh0]
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp [llen, add_comm]
  have hfr0 : ∀ Z, pfr G00 Z = R Z := by
    intro Z; unfold pfr; simp [hG00, PG0]
  have hstk0 : ∀ Q y, G00.stk Q y = 0 := by
    intro Q y; simp [PG.stk, hG00, PG0]
  have hL0 : PLInv L s σ' σ0 ((∑ Q, R Q) + laneCells L s) G00 := by
    refine ⟨?_, ?_, fun _ _ => rfl, ?_, ?_, hpc, fun _ _ => rfl, ?_, rfl, trivial, ?_, ?_, ?_⟩
    · intro Q y
      rw [hstk0]
      by_cases hQy : y = Q
      · subst hQy; simp only [hG00, PG0, tdemand, PState.toI, if_true]; have := hR y; omega
      · simp only [hG00, PG0, tdemand, PState.toI, if_neg hQy, if_neg (Ne.symm hQy)]; omega
    · intro Q y hy
      rw [hstk0]
      simp only [hG00, PG0, tdemand, PState.toI, if_neg (Ne.symm hy), if_neg hy]; omega
    · intro l r x d h; rw [hgh0] at h; cases h
    · intro l r h; rw [hgh0] at h; exact absurd rfl h
    · intro u x _; exact Nat.zero_le _
    · simp [hG00, PG0, PState.totalCost]
    · rw [hunt0]
      simp only [hG00, PG0, sum_const_zero, add_zero]
      congr 1
      refine sum_congr rfl fun Q _ => ?_
      simp
    · have e1 : ∀ x0, plcnt L s G00 (fun l => turning L l x0) (fun g => gcl g = some x0) = 0 :=
        fun x0 => plcnt_none L s G00 hgh0 _ _ (by simp [gcl])
      simp only [e1, sum_const_zero]
      simp [NS, hG00, PG0]
  have hH0 : PHInv L c G00 := by
    refine ⟨?_, ?_, ?_, ?_, le_of_eq (by simp [hG00, PG0]), by simp [hG00, PG0],
      by simp [hG00, PG0]; rfl, by simp [hG00, PG0], by simp [hG00, PG0], by simp [hG00, PG0]⟩
    · intro v x _
      have := plcnt_none L s G00 hgh0 (fun l => land l = v) (fun g => gtg g = some x) (by simp [gtg])
      rw [hstk0]
      show 0 + pFcnt L s G00 v x + 0 = 0
      unfold pFcnt; rw [this]
    · intro v x
      have := plcnt_none L s G00 hgh0 (fun l => land l = v) (fun g => gdt g = some x) (by simp [gdt])
      show 0 + pDpos L s G00 v x = ∑ u ∈ _, 0
      unfold pDpos; rw [this]; simp
    · intro v x; simp [hG00, PG0]
    · intro Z
      show R Z + 0 + _ + psA G00 Z ≤ pfr G00 Z + psB G00 Z + 0 + _
      have e1 : psA G00 Z = 0 := by simp [psA, hG00, PG0]
      have e2 : psB G00 Z = 0 := by simp [psB, hG00, PG0]
      rw [e1, e2, hfr0]
      simp [hG00, PG0]
      exact le_rfl
  have hO0 : POuter L c 0 G00 := by
    refine ⟨Nat.zero_le _, hL0, hH0, ?_, fun Z => by simp [hG00, PG0], by simp [hG00, PG0]⟩
    intro S D
    show tdemand σ0.toI S D = ∑ τ ∈ Ico 0 Δ0, ind (rd τ) S D
    rw [← range_eq_Ico, hrd, sum_ordR rs0 σo (fun r => ind r S D), ← hc1 S D, card_filter]
    rfl
  have hOf : POuter L c Δ0 Gf := POuter.all L hcOK td hO0 rfl Δ0 le_rfl
  have hS0 : c.S0 ≤ n ^ 2 := by
    have hn : n = k * s := td.mul.symm
    have : ∀ S, ∑ D, tdemand σ0.toI S D ≤ s ^ 2 := fun S => (hmx S).1
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
      calc ∑ S : Sq k, (recv (tdemand σ0.toI) S - sends (tdemand σ0.toI) S)
          ≤ ∑ S : Sq k, ((s ^ 2 - rsz S) + 1) :=
            sum_le_sum fun S _ => trecv_sub_sends L σ0.toI rsz hF1 hF2 S
        _ ≤ laneCells L s + k ^ 2 := by
            rw [sum_add_distrib]; simp [Fintype.card_prod]; nlinarith [hlane]
    have h2 : Δ0 * (15 * k ^ 2 + 30 * k + 18) ≤ s ^ 2 * (15 * k ^ 2 + 30 * k + 18) :=
      Nat.mul_le_mul_right _ hΔ0
    nlinarith
  have hNv' : ∀ Z, stkCap L c.Nv Z ≤ needAt L s (GroupedOrder.lamN n) Z := fun Z => hNv Z
  obtain ⟨h1, h2, h3⟩ := pouter_final L c Gf hOf (needAt L s (GroupedOrder.lamN n)) hNv' hS0 hW
    (ppot_le' L s σ0)
  exact ⟨Gf.evs, h1, by unfold prunCost; exact h2, h3⟩

end SlidingPuzzle.Port
