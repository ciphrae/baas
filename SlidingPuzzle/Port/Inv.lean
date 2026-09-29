import SlidingPuzzle.Port.Round
import SlidingPuzzle.Tree.RunInv

/-! # Invariants of the port run

As `Tree.RunInv`, with the counters of transfers (`nx ≤ 4 · served`), turns
(`nt ≤ served`) and imports (`ni ≤ nis + placeholders + served`). -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle.Hub (Sq sqDist HEvent relocWeight Round bump roundEvs ind dummyAt roundW
  roundEvs_count roundEvs_chain roundEvs_weight HChain)
open SlidingPuzzle.Tree

variable {k q : ℕ} (L : LaneSys k q)

/-- The fixed data of the run. -/
structure PCtx (k q : ℕ) where
  s : ℕ
  σ' : ℕ
  σ0 : PState k q
  F0 : ℕ
  fr0 : Sq k → ℕ
  Nv : Sq k → Sq k → ℕ
  S0 : ℕ
  Lfin : List (GRec k q)
  rd : ℕ → Round k
  Δ : ℕ
  dmax : Sq k → ℕ

/-- Hypotheses on the data. -/
structure PCtx.OK (c : PCtx k q) : Prop where
  Fb : ∀ G' : PG k q, G'.ins <+: c.Lfin → ∀ v x, pFcnt L c.s G' v x ≤ c.Nv v x
  free0 : 0 < c.Δ → ∀ Z, stkCap L c.Nv Z + c.dmax Z + 5 ≤ c.fr0 Z
  dmax : ∀ Z, (∑ τ ∈ range c.Δ, dummyAt (c.rd τ) Z) ≤ c.dmax Z
  cap : CapOK L c.σ0 c.Nv

/-- Invariants between high-level events. -/
structure PHInv (c : PCtx k q) (G : PG k q) : Prop where
  ident : ∀ v x, v ≠ x → G.stk v x + pFcnt L c.s G v x + G.dA v x = G.B v x
  dirty : PDirtyInv L c.s G
  binv : PBInv L G c.Nv
  free_lo : ∀ Z, c.fr0 Z + G.sent Z + (if c.σ0.blank = Z then 1 else 0) + psA G Z ≤
    pfr G Z + psB G Z + G.served Z + (if G.σ.blank = Z then 1 else 0)
  jc : G.jc ≤ 3 * legA k c.s c.σ' * G.wt
  nh : G.nh ≤ 2 * L.depth * (∑ Z, G.served Z)
  sched_sum : (∑ Z, G.served Z) + (∑ S, ∑ D, G.sched S D) = c.S0
  nx : G.nx ≤ 4 * (∑ Z, G.served Z)
  nt : G.nt ≤ ∑ Z, G.served Z
  ni : G.ni ≤ G.nis + sBt G + ∑ Z, G.served Z
  ncr : G.ncr ≤ 2 * k * ∑ Z, G.served Z

theorem PHInv.identD {c : PCtx k q} {G : PG k q} (h : PHInv L c G) (D : Sq k) :
    PIdent L c.s G D none := by
  intro v x hvx; simpa using h.ident v x hvx

theorem PHInv.cap {c : PCtx k q} (hc : c.OK L) {G : PG k q}
    (hL : PLInv L c.s c.σ' c.σ0 c.F0 G) (h : PHInv L c G) (Q : Sq k) (pt : Pt) :
    (∑ z, G.stk Q z) + 1 < psz c.σ0 Q pt :=
  lt_of_le_of_lt (Nat.add_le_add_right (stk_sum_le L hL (h.identD L Q) h.binv Q) 1) (hc.cap Q pt)

/-- Placeholders are dirty arrivals plus at most the in-flight bound, where active. -/
theorem psB_le {c : PCtx k q} {G : PG k q} (h : PHInv L c G) (Z : Sq k) :
    psB G Z ≤ psA G Z + stkCap L c.Nv Z := by
  unfold psB psA stkCap
  rw [← sum_add_distrib]
  refine sum_le_sum fun x _ => ?_
  obtain ⟨h1, h2⟩ := h.binv Z x
  split_ifs with ha
  · omega
  · have : G.B Z x = 0 := by by_contra h0; exact ha (h2 h0)
    omega

/-- The local invariant does not see the served, sent and weight counters. -/
theorem PLInv.congr {s σ' : ℕ} {σ0 : PState k q} {F0 : ℕ} {G : PG k q}
    (hL : PLInv L s σ' σ0 F0 G) (sv st : Sq k → ℕ) (w : ℕ) :
    PLInv L s σ' σ0 F0 { G with served := sv, sent := st, wt := w } := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := hL
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩

theorem sum_bump (f : Sq k → ℕ) (D : Sq k) : ∑ Z, bump f D Z = (∑ Z, f Z) + 1 := by
  simp [bump, sum_add_distrib]

section step

variable {c : PCtx k q} (hc : c.OK L) {n : ℕ} [NeZero n] (td : TDims n k c.s q)
include hc td

theorem phstep_serve {G : PG k q} (hL : PLInv L c.s c.σ' c.σ0 c.F0 G) (hH : PHInv L c G) (τ : ℕ)
    {S D : Sq k} (hb : G.σ.blank = D) (hSD : S ≠ D) (hsch : 1 ≤ G.sched S D)
    (hfree : ∀ Q, Q ≠ G.σ.blank → 1 ≤ pfr G Q)
    (hpre : (phstep L c.s c.σ' τ G (.serve S D)).ins <+: c.Lfin) :
    PLInv L c.s c.σ' c.σ0 c.F0 (phstep L c.s c.σ' τ G (.serve S D)) ∧
      PHInv L c (phstep L c.s c.σ' τ G (.serve S D)) := by
  have hav : ∀ u ∈ L.nodes (L.nxt S D) D, 1 ≤ pfr G u := by
    intro u hu
    refine hfree u ?_
    rw [hb]; exact (mem_nodes L hu).1
  have I := pServe_inv L td τ c.Nv hc.cap hL hSD hb (hH.identD L D) hH.dirty hH.binv c.Lfin
    hc.Fb hsch hav hpre
  have htc := tcnt_le_one L D S
  have hsv : ∀ Z, (phstep L c.s c.σ' τ G (.serve S D)).served Z =
      G.served Z + if Z = D then 1 else 0 :=
    fun Z => by show bump G.served D Z = _; rfl
  have hst : ∀ Z, (phstep L c.s c.σ' τ G (.serve S D)).sent Z =
      G.sent Z + if Z = S then 1 else 0 :=
    fun Z => by show bump G.sent S Z = _; rfl
  have hsum : ∑ Z, (phstep L c.s c.σ' τ G (.serve S D)).served Z = (∑ Z, G.served Z) + 1 :=
    sum_bump G.served D
  refine ⟨I.lin.congr L _ _ _, ?_⟩
  refine ⟨fun v x hvx => by
    have := I.ident v x hvx
    simp only [reduceCtorEq, false_and, if_false, add_zero] at this
    exact this, I.dirty, I.binv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Z
    have h1 := hH.free_lo Z
    have h2 := I.mono Z
    have hbl : (phstep L c.s c.σ' τ G (.serve S D)).σ.blank = S := I.blank
    show c.fr0 Z + (phstep L c.s c.σ' τ G (.serve S D)).sent Z + _ + psA (pServe L c.s τ G S D) Z ≤
      pfr (pServe L c.s τ G S D) Z + psB (pServe L c.s τ G S D) Z +
        (phstep L c.s c.σ' τ G (.serve S D)).served Z + _
    rw [hsv, hst, hbl]
    rw [hb] at h1
    by_cases h3 : Z = D
    · subst h3; simp only [if_true, if_neg hSD, if_neg (Ne.symm hSD)] at h1 ⊢; omega
    · by_cases h4 : Z = S
      · subst h4; simp only [if_true, if_neg h3, if_neg (Ne.symm h3)] at h1 ⊢; omega
      · simp only [if_neg h3, if_neg h4, if_neg (Ne.symm h3), if_neg (Ne.symm h4)] at h1 ⊢; omega
  · show (pServe L c.s τ G S D).jc ≤ 3 * legA k c.s c.σ' * (pServe L c.s τ G S D).wt
    rw [I.jc, I.wt]; exact hH.jc
  · rw [hsum]
    show (pServe L c.s τ G S D).nh ≤ _
    rw [I.nh]
    have := srank_le (L := L) S D
    have := hH.nh
    nlinarith
  · show (∑ Z, bump G.served D Z) + (∑ S', ∑ D', (pServe L c.s τ G S D).sched S' D') = c.S0
    rw [sum_bump]
    simp only [I.sched]
    have hp : ∀ Q x, (G.sched Q x - (if Q = S ∧ x = D then 1 else 0)) +
        (if Q = S ∧ x = D then 1 else 0) = G.sched Q x := by
      intro Q x
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h; omega
      · simp
    have e1 := Finset.sum_congr rfl fun Q (_ : Q ∈ univ) =>
      Finset.sum_congr rfl fun x (_ : x ∈ univ) => hp Q x
    simp only [sum_add_distrib] at e1
    have e2 := sum_sum_ind (k := k) S D
    have : (∑ Q, ∑ x, (G.sched Q x - (if Q = S ∧ x = D then 1 else 0))) + 1 =
        ∑ Q, ∑ x, G.sched Q x := by
      have e3 : (∑ Q, univ.sum (G.sched Q)) = ∑ Q, ∑ x, G.sched Q x := rfl
      omega
    have := hH.sched_sum
    omega
  · rw [hsum]
    show (pServe L c.s τ G S D).nx ≤ _
    have := I.nx; have := hH.nx; omega
  · rw [hsum]
    show (pServe L c.s τ G S D).nt ≤ _
    have := I.nt; have := hH.nt; omega
  · rw [hsum]
    show (pServe L c.s τ G S D).ni ≤ (pServe L c.s τ G S D).nis + sBt (pServe L c.s τ G S D) + _
    have := I.ni; have := hH.ni; omega
  · rw [hsum]
    show (pServe L c.s τ G S D).ncr ≤ _
    rw [I.ncr]
    have := hH.ncr; have := rcross_le_k L D S
    rw [mul_add]; omega

theorem phstep_reloc {G : PG k q} (hL : PLInv L c.s c.σ' c.σ0 c.F0 G) (hH : PHInv L c G) (τ : ℕ)
    {E Z : Sq k} (hb : G.σ.blank = E) (hEZ : E ≠ Z)
    (hfree : ∀ Q, Q ≠ G.σ.blank → 1 ≤ pfr G Q) :
    PLInv L c.s c.σ' c.σ0 c.F0 (phstep L c.s c.σ' τ G (.reloc E Z)) ∧
      PHInv L c (phstep L c.s c.σ' τ G (.reloc E Z)) := by
  obtain ⟨hL', hfr, hjc⟩ := pReloc_linv L hL hb hEZ (fun Q hQ => hfree Q (by rw [hb]; exact hQ))
    (hH.cap L hc hL)
  obtain ⟨r, rb, -⟩ := pReloc_same L (s := c.s) (σ' := c.σ') G E Z
  refine ⟨hL'.congr L _ _ _, ?_, r.dirty L hH.dirty, r.binv L hH.binv, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · intro v x hvx
    have := (r.ident L (hH.identD L v)) v x hvx
    simp only [reduceCtorEq, false_and, if_false, add_zero] at this
    exact this
  · intro Q
    have h1 := hH.free_lo Q
    have h2 := hfr Q
    show c.fr0 Q + (pReloc L c.s c.σ' G E Z).sent Q + _ + psA (pReloc L c.s c.σ' G E Z) Q ≤
      pfr (pReloc L c.s c.σ' G E Z) Q + psB (pReloc L c.s c.σ' G E Z) Q +
        (pReloc L c.s c.σ' G E Z).served Q +
        (if (pReloc L c.s c.σ' G E Z).σ.blank = Q then 1 else 0)
    have hsA : psA (pReloc L c.s c.σ' G E Z) Q = psA G Q := by unfold psA; rw [r.dA]
    have hsB : psB (pReloc L c.s c.σ' G E Z) Q = psB G Q := by unfold psB; rw [r.B]
    rw [r.sent, r.served, rb, hsA, hsB]
    rw [hb] at h1
    simp only [@eq_comm _ E Q, @eq_comm _ Z Q] at h1 h2 ⊢
    omega
  · show (pReloc L c.s c.σ' G E Z).jc ≤ 3 * legA k c.s c.σ' * (G.wt + relocWeight (HEvent.reloc E Z))
    have := hH.jc
    nlinarith
  · show (pReloc L c.s c.σ' G E Z).nh ≤ 2 * L.depth * ∑ Q, (pReloc L c.s c.σ' G E Z).served Q
    rw [r.nh, r.served]; exact hH.nh
  · show (∑ Q, (pReloc L c.s c.σ' G E Z).served Q) +
      (∑ S', ∑ D', (pReloc L c.s c.σ' G E Z).sched S' D') = c.S0
    rw [r.served, r.sched]; exact hH.sched_sum
  · show (pReloc L c.s c.σ' G E Z).nx ≤ 4 * ∑ Q, (pReloc L c.s c.σ' G E Z).served Q
    rw [r.nx, r.served]; exact hH.nx
  · show (pReloc L c.s c.σ' G E Z).nt ≤ ∑ Q, (pReloc L c.s c.σ' G E Z).served Q
    rw [r.nt, r.served]; exact hH.nt
  · show (pReloc L c.s c.σ' G E Z).ni ≤ (pReloc L c.s c.σ' G E Z).nis +
      sBt (pReloc L c.s c.σ' G E Z) + ∑ Q, (pReloc L c.s c.σ' G E Z).served Q
    have hsBt : sBt (pReloc L c.s c.σ' G E Z) = sBt G := by unfold sBt; rw [r.B]
    rw [r.ni, r.nis, hsBt, r.served]; exact hH.ni
  · show (pReloc L c.s c.σ' G E Z).ncr ≤ 2 * k * ∑ Q, (pReloc L c.s c.σ' G E Z).served Q
    rw [r.ncr, r.served]; exact hH.ncr

end step

end SlidingPuzzle.Port
