import SlidingPuzzle.Hub.RunRound

/-! # Invariants along rounds

`Inner` holds between the events of a round, `Outer` between rounds. Every
event keeps `Inner` (validity of its resolution included), a round turns
`Outer m` into `Outer (m+1)`. The free lower bound makes every jump possible. -/
namespace SlidingPuzzle.Hub

open Finset

variable {k : ℕ}

/-- The fixed data of the run. -/
structure Ctx (k : ℕ) where
  s : ℕ
  σ0 : IState k
  F0 : ℕ
  free0 : Sq k → ℕ
  N : Sq k → Sq k → ℕ
  S0 : ℕ
  L : List (InsRec k)
  rd : ℕ → Round k
  Δ : ℕ
  dmax : Sq k → ℕ

/-- Hypotheses on the data. -/
structure Ctx.OK (c : Ctx k) : Prop where
  room : k + 1 ≤ c.s
  newle : ∀ m h x, newCnt c.s (ghostRun c.s (fun _ _ => none) (c.L.take m)) h x ≤ c.N h x
  free0 : 0 < c.Δ → ∀ Z, (∑ x, (c.N Z x + 1)) + c.dmax Z + 3 ≤ c.free0 Z
  dmax : ∀ Z, (∑ τ ∈ range c.Δ, dummyAt (c.rd τ) Z) ≤ c.dmax Z

/-- Invariant between the events of round `m`; `rem` are the remaining events. -/
structure Inner (c : Ctx k) (m : ℕ) (G : GS k) (rem : List (HEvent k)) : Prop where
  lt : m < c.Δ
  lin : LInv c.s c.σ0 c.F0 G
  hin : HInv c.s c.σ0 c.free0 c.N c.S0 G
  chain : HChain G.σ.blank rem
  cnt_le : ∀ S D, rem.count (.serve S D) ≤ ind (c.rd m) S D
  sched : ∀ S D, G.sched S D = (∑ τ ∈ Ico (m + 1) c.Δ, ind (c.rd τ) S D) + rem.count (.serve S D)
  bal : ∀ Z, G.served Z + cntIn rem Z ≤ G.sent Z + cntOut rem Z + G.dd Z + dummyAt (c.rd m) Z
  dd : ∀ Z, G.dd Z = ∑ τ ∈ range m, dummyAt (c.rd τ) Z

/-- Invariant between rounds (`m` rounds done). -/
structure Outer (c : Ctx k) (m : ℕ) (G : GS k) : Prop where
  le : m ≤ c.Δ
  lin : LInv c.s c.σ0 c.F0 G
  hin : HInv c.s c.σ0 c.free0 c.N c.S0 G
  sched : ∀ S D, G.sched S D = ∑ τ ∈ Ico m c.Δ, ind (c.rd τ) S D
  bal : ∀ Z, G.served Z ≤ G.sent Z + G.dd Z
  dd : ∀ Z, G.dd Z = ∑ τ ∈ range m, dummyAt (c.rd τ) Z
  wt : G.wt ≤ ∑ τ ∈ range m, roundW (c.rd τ)

theorem real_add_dummy_le (r : Round k) (Z : Sq k) :
    (if r.real Z then 1 else 0) + dummyAt r Z ≤ 1 := by
  unfold dummyAt
  by_cases h1 : r.real Z
  · have : ¬ r.isDummy Z := fun hd => by
      unfold Round.real at h1; unfold Round.isDummy at hd
      rw [h1.2] at hd; exact absurd hd.2 (by decide)
    simp [h1, this]
  · simp only [h1, if_false, zero_add]; split_ifs <;> omega

theorem sum_ind_left (r : Round k) (Z : Sq k) :
    (∑ D, ind r Z D) = if r.real Z then 1 else 0 := by
  unfold ind
  by_cases h : r.real Z
  · simp [h]
  · simp [h]

theorem sum_ind_right (r : Round k) (Z : Sq k) :
    (∑ S, ind r S Z) ≤ (if r.real Z then 1 else 0) + dummyAt r Z := by
  unfold ind
  rw [Finset.sum_eq_single (r.perm.symm Z)]
  · simp only [Equiv.apply_symm_apply, true_and]
    by_cases hz : r.perm Z = Z
    · have : r.perm.symm Z = Z := by rw [Equiv.symm_apply_eq]; exact hz.symm
      rw [this]; split_ifs <;> simp
    · by_cases hr : r.real Z
      · simp only [hr, if_true]; split_ifs <;> omega
      · have hd : r.isDummy Z := by
          unfold Round.real at hr; unfold Round.isDummy
          refine ⟨hz, ?_⟩
          cases h : r.dummy Z
          · exact absurd ⟨hz, h⟩ hr
          · rfl
        simp only [dummyAt, hd, if_true]; split_ifs <;> omega
  · intro S _ hS
    rw [if_neg]
    rintro ⟨e, -⟩
    exact hS (by rw [← e]; simp)
  · simp

theorem cntOut_le {rem : List (HEvent k)} {r : Round k}
    (h : ∀ S D, rem.count (.serve S D) ≤ ind r S D) (Z : Sq k) :
    cntOut rem Z ≤ if r.real Z then 1 else 0 := by
  rw [← sum_ind_left]
  exact sum_le_sum fun D _ => h Z D

section inner

variable {c : Ctx k} (hc : c.OK)
include hc

theorem Inner.free_pos {m : ℕ} {G : GS k} {rem : List (HEvent k)} (hI : Inner c m G rem)
    (Q : Sq k) : 1 ≤ ∑ y, G.free Q y := by
  have h1 := hI.hin.free_lo Q
  have h2 := hI.bal Q
  have h3 := cntOut_le hI.cnt_le Q
  have h4 := real_add_dummy_le (c.rd m) Q
  have h5 : G.dd Q ≤ c.dmax Q := by
    rw [hI.dd Q]
    refine le_trans ?_ (hc.dmax Q)
    exact sum_le_sum_of_subset (range_subset_range.2 hI.lt.le)
  have h6 : (∑ x, G.byp Q x) ≤ ∑ x, (c.N Q x + 1) := sum_le_sum fun x _ => hI.hin.byp_le Q x
  have h7 := hc.free0 (by have := hI.lt; omega) Q
  have h8 : (if G.σ.blank = Q then 1 else 0) ≤ 1 := by split_ifs <;> omega
  omega

theorem Inner.step {m : ℕ} {G : GS k} {e : HEvent k} {rest : List (HEvent k)}
    (hI : Inner c m G (e :: rest)) (hpre : G.ins <+: c.L) :
    Inner c m (hstep c.s m G e) rest := by
  have hnew : ∀ h x, newCnt c.s (gh c.s G) h x ≤ c.N h x := by
    intro h x
    have : gh c.s G = ghostRun c.s (fun _ _ => none) (c.L.take G.ins.length) := by
      unfold gh; rw [← List.prefix_iff_eq_take.1 hpre]
    rw [this]; exact hc.newle _ h x
  cases e with
  | serve S D =>
    have hch := hI.chain
    simp only [HChain] at hch
    obtain ⟨hb, hrest⟩ := hch
    have hcnt := hI.cnt_le S D
    rw [count_cons_serve] at hcnt
    simp only [and_self, if_true] at hcnt
    have hedge : (c.rd m).perm S = D ∧ (c.rd m).real S := by
      unfold ind at hcnt; split_ifs at hcnt with h
      · exact h
      · omega
    have hne : S ≠ D := by
      intro e; exact hedge.2.1 (hedge.1.trans e.symm)
    have hsch := hI.sched S D
    rw [count_cons_serve] at hsch
    simp only [and_self, if_true] at hsch
    have ok : ServeOK c.s c.N G S D :=
      ⟨hb.symm ▸ rfl, hne, by omega, hnew, hI.free_pos hc, hc.room⟩
    obtain ⟨hL', hH'⟩ := hstep_serve hI.lin hI.hin m ok
    refine ⟨hI.lt, hL', hH', ?_, ?_, ?_, ?_, ?_⟩
    · rw [hstep_blank]; exact hrest
    · intro S' D'
      have := hI.cnt_le S' D'
      rw [count_cons_serve] at this
      omega
    · intro S' D'
      have := hI.sched S' D'
      rw [count_cons_serve] at this
      show (hServe c.s m G S D).sched S' D' = _
      rw [hServe_sched, decCnt_apply]
      split_ifs at this ⊢ <;> omega
    · intro Z
      have := hI.bal Z
      rw [cntIn_cons_serve, cntOut_cons_serve] at this
      show bump G.served D Z + _ ≤ bump G.sent S Z + _ + (hServe c.s m G S D).dd Z + _
      rw [(hServe_rest (s := c.s) m G S D).2.2.2]
      simp only [bump]
      omega
    · intro Z
      rw [hstep_dd]; exact hI.dd Z
  | reloc E Z =>
    have hch := hI.chain
    simp only [HChain] at hch
    obtain ⟨hb, hEZ, hrest⟩ := hch
    obtain ⟨hL', hH'⟩ := hstep_reloc hI.lin hI.hin m hb hEZ (hI.free_pos hc)
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩ := hReloc_same (s := c.s) G E Z
    refine ⟨hI.lt, hL', hH', ?_, ?_, ?_, ?_, ?_⟩
    · rw [hstep_blank]; exact hrest
    · intro S' D'
      have := hI.cnt_le S' D'
      rwa [count_cons_reloc] at this
    · intro S' D'
      have := hI.sched S' D'
      rw [count_cons_reloc] at this
      show (hReloc c.s G E Z).sched S' D' = _
      rw [r1]; exact this
    · intro Q
      have := hI.bal Q
      rw [cntIn_cons_reloc, cntOut_cons_reloc] at this
      show (hReloc c.s G E Z).served Q + _ ≤ (hReloc c.s G E Z).sent Q + _ +
        (hReloc c.s G E Z).dd Q + _
      rw [r6, r7, r9]; exact this
    · intro Q
      rw [hstep_dd]; exact hI.dd Q

theorem Inner.run {m : ℕ} : ∀ (rem : List (HEvent k)) (G : GS k), Inner c m G rem →
    (runEvs c.s m G rem).ins <+: c.L → Inner c m (runEvs c.s m G rem) []
  | [], G, hI, _ => hI
  | e :: rest, G, hI, hpre => by
    have hG : G.ins <+: c.L := by
      refine List.IsPrefix.trans ?_ hpre
      rw [runEvs_ins]; exact List.prefix_append _ _
    have h1 := hI.step hc hG
    exact Inner.run rest _ h1 hpre

omit hc in
theorem Outer.start {m : ℕ} {G : GS k} (hO : Outer c m G) (hm : m < c.Δ) :
    Inner c m G (roundEvs (c.rd m) G.σ.blank) := by
  refine ⟨hm, hO.lin, hO.hin, roundEvs_chain _ _, ?_, ?_, ?_, hO.dd⟩
  · intro S D; rw [roundEvs_count]
  · intro S D
    rw [hO.sched, roundEvs_count, Finset.sum_eq_sum_Ico_succ_bot hm]
    ring
  · intro Z
    have h1 := hO.bal Z
    have h2 : cntIn (roundEvs (c.rd m) G.σ.blank) Z = ∑ S, ind (c.rd m) S Z := by
      unfold cntIn; simp only [roundEvs_count]
    have h3 : cntOut (roundEvs (c.rd m) G.σ.blank) Z = if (c.rd m).real Z then 1 else 0 := by
      unfold cntOut; simp only [roundEvs_count]; exact sum_ind_left _ _
    have h4 := sum_ind_right (c.rd m) Z
    omega

theorem Outer.round {m : ℕ} {G : GS k} (hO : Outer c m G) (hm : m < c.Δ)
    (hpre : (runRound c.s m (c.rd m) G).ins <+: c.L) :
    Outer c (m + 1) (runRound c.s m (c.rd m) G) := by
  have hI := Inner.run hc _ _ (hO.start hm) hpre
  have hwt := runRound_wt c.s m (c.rd m) G
  set R := runEvs c.s m G (roundEvs (c.rd m) G.σ.blank) with hR
  have e1 : (runRound c.s m (c.rd m) G).served = R.served := rfl
  have e2 : (runRound c.s m (c.rd m) G).sent = R.sent := rfl
  have e3 : (runRound c.s m (c.rd m) G).sched = R.sched := rfl
  have e4 : ∀ Z, (runRound c.s m (c.rd m) G).dd Z = R.dd Z + dummyAt (c.rd m) Z := fun Z => rfl
  refine ⟨hm, hI.lin.congr rfl rfl rfl rfl rfl rfl rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hI.hin.ident, hI.hin.byp_le, hI.hin.free_lo, hI.hin.cost, hI.hin.sched_sum⟩
  · intro S D
    have := hI.sched S D
    rw [e3]; simpa using this
  · intro Z
    have := hI.bal Z
    rw [e1, e2, e4]
    simp only [cntIn, cntOut, List.count_nil, sum_const_zero, add_zero] at this
    omega
  · intro Z
    rw [e4, hI.dd Z, sum_range_succ]
  · rw [sum_range_succ]
    have := hO.wt
    omega

theorem Outer.all {G : GS k} (h0 : Outer c 0 G) (hL : c.L = (runRounds c.s c.rd c.Δ G).ins) :
    ∀ m ≤ c.Δ, Outer c m (runRounds c.s c.rd m G) := by
  intro m hm
  induction m with
  | zero => exact h0
  | succ m ih =>
    have hO := ih (by omega)
    refine hO.round hc (by omega) ?_
    rw [hL]
    exact runRounds_ins_prefix c.s c.rd G hm

end inner

end SlidingPuzzle.Hub
