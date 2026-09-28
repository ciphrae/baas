import SlidingPuzzle.Tree.RunRound
import SlidingPuzzle.Hub.RunInner

/-! # Invariants of the run

`HInv` holds between high-level events: the stock identity, the dirty-tile
count, the placeholder bound, the lower bound on free tiles of every square,
and the counters. `Inner` adds the bookkeeping of the current round, `Outer`
holds between rounds. -/
namespace SlidingPuzzle.Tree
open Finset
open SlidingPuzzle.Hub (Sq sqDist HEvent relocWeight Round bump roundEvs ind dummyAt roundW
  roundEvs_count roundEvs_chain roundEvs_weight HChain cntIn cntOut count_cons_serve
  count_cons_reloc cntIn_cons_serve cntOut_cons_serve cntIn_cons_reloc cntOut_cons_reloc
  real_add_dummy_le sum_ind_left sum_ind_right cntOut_le)

variable {k q : ℕ} (L : LaneSys k q)

/-- The fixed data of the run. -/
structure Ctx (k q : ℕ) where
  s : ℕ
  σ0 : IState k q
  F0 : ℕ
  fr0 : Sq k → ℕ
  Nv : Sq k → Sq k → ℕ
  S0 : ℕ
  Lfin : List (GRec k q)
  rd : ℕ → Round k
  Δ : ℕ
  dmax : Sq k → ℕ

/-- Hypotheses on the data. -/
structure Ctx.OK (c : Ctx k q) : Prop where
  Fb : ∀ G' : GS k q, G'.ins <+: c.Lfin → ∀ v x, Fcnt L c.s G' v x ≤ c.Nv v x
  free0 : 0 < c.Δ → ∀ Z, (∑ x, (c.Nv Z x + if L.Act Z x then 1 else 0)) + c.dmax Z + 5 ≤ c.fr0 Z
  dmax : ∀ Z, (∑ τ ∈ range c.Δ, dummyAt (c.rd τ) Z) ≤ c.dmax Z

/-- Invariants between high-level events. -/
structure HInv (c : Ctx k q) (G : GS k q) : Prop where
  ident : ∀ v x, v ≠ x → G.stock v x + Fcnt L c.s G v x + G.dA v x = G.B v x
  dirty : DirtyInv L c.s G
  binv : BInv L G c.Nv
  free_lo : ∀ Z, c.fr0 Z + G.sent Z + (if c.σ0.blank = Z then 1 else 0) + sA G Z ≤
    fr G Z + sB G Z + G.served Z + (if G.σ.blank = Z then 1 else 0)
  jc : G.jc ≤ 3 * (c.s + 3) * G.wt
  nh : G.nh ≤ 2 * L.depth * (∑ Z, G.served Z)
  sched_sum : (∑ Z, G.served Z) + (∑ S, ∑ D, G.sched S D) = c.S0

theorem HInv.identD {c : Ctx k q} {G : GS k q} (h : HInv L c G) (D : Sq k) :
    Ident L c.s G D none := by
  intro v x hvx; simpa using h.ident v x hvx

/-- Placeholders are dirty arrivals plus at most the in-flight bound, where active. -/
theorem sB_le {c : Ctx k q} {G : GS k q} (h : HInv L c G) (Z : Sq k) :
    sB G Z ≤ sA G Z + ∑ x, (c.Nv Z x + if L.Act Z x then 1 else 0) := by
  unfold sB sA
  rw [← sum_add_distrib]
  refine sum_le_sum fun x _ => ?_
  obtain ⟨h1, h2⟩ := h.binv Z x
  split_ifs with ha
  · omega
  · have : G.B Z x = 0 := by by_contra h0; exact ha (h2 h0)
    omega

section step

variable {c : Ctx k q} (hc : c.OK L) {n : ℕ} [NeZero n] (td : TDims n k c.s q)
include hc td

theorem hstep_serve {G : GS k q} (hL : LInv L c.s c.σ0 c.F0 G) (hH : HInv L c G) (τ : ℕ)
    {S D : Sq k} (hb : G.σ.blank = D) (hSD : S ≠ D) (hsch : 1 ≤ G.sched S D)
    (hfree : ∀ Q, Q ≠ G.σ.blank → 1 ≤ fr G Q)
    (hpre : (hstep L c.s τ G (.serve S D)).ins <+: c.Lfin) :
    LInv L c.s c.σ0 c.F0 (hstep L c.s τ G (.serve S D)) ∧
      HInv L c (hstep L c.s τ G (.serve S D)) := by
  have hav : ∀ u ∈ L.nodes (L.nxt S D) D, 1 ≤ fr G u := by
    intro u hu
    refine hfree u ?_
    rw [hb]; exact (mem_nodes L hu).1
  have I := hServe_inv L td τ c.Nv hL hSD hb (hH.identD L D) hH.dirty hH.binv c.Lfin hc.Fb hsch
    hav hpre
  have hsv : ∀ Z, (hstep L c.s τ G (.serve S D)).served Z = G.served Z + if Z = D then 1 else 0 :=
    fun Z => by show bump G.served D Z = _; rfl
  have hst : ∀ Z, (hstep L c.s τ G (.serve S D)).sent Z = G.sent Z + if Z = S then 1 else 0 :=
    fun Z => by show bump G.sent S Z = _; rfl
  have hF : ∀ v x, Fcnt L c.s (hstep L c.s τ G (.serve S D)) v x =
      Fcnt L c.s (hServe L c.s τ G S D) v x := fun _ _ => rfl
  refine ⟨I.lin.congr L rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, ?_⟩
  refine ⟨fun v x hvx => by
    have := I.ident v x hvx
    simp only [reduceCtorEq, false_and, if_false, add_zero] at this
    exact this, I.dirty, I.binv, ?_, ?_, ?_, ?_⟩
  · intro Z
    have h1 := hH.free_lo Z
    have h2 := I.mono Z
    have hbl : (hstep L c.s τ G (.serve S D)).σ.blank = S := I.blank
    show c.fr0 Z + (hstep L c.s τ G (.serve S D)).sent Z + _ + sA (hServe L c.s τ G S D) Z ≤
      fr (hServe L c.s τ G S D) Z + sB (hServe L c.s τ G S D) Z +
        (hstep L c.s τ G (.serve S D)).served Z + _
    rw [hsv, hst, hbl]
    rw [hb] at h1
    by_cases h3 : Z = D
    · subst h3; simp only [if_true, if_neg hSD, if_neg (Ne.symm hSD)] at h1 ⊢; omega
    · by_cases h4 : Z = S
      · subst h4; simp only [if_true, if_neg h3, if_neg (Ne.symm h3)] at h1 ⊢; omega
      · simp only [if_neg h3, if_neg h4, if_neg (Ne.symm h3), if_neg (Ne.symm h4)] at h1 ⊢; omega
  · show (hServe L c.s τ G S D).jc ≤ 3 * (c.s + 3) * (hServe L c.s τ G S D).wt
    rw [I.jc, I.wt]; exact hH.jc
  · show (hServe L c.s τ G S D).nh ≤ 2 * L.depth * ∑ Z, bump G.served D Z
    rw [I.nh]
    have e : ∑ Z, bump G.served D Z = (∑ Z, G.served Z) + 1 := by
      simp [bump, sum_add_distrib]
    rw [e]
    have := srank_le (L := L) S D
    have := hH.nh
    nlinarith
  · show (∑ Z, bump G.served D Z) + (∑ S', ∑ D', (hServe L c.s τ G S D).sched S' D') = c.S0
    have e : ∑ Z, bump G.served D Z = (∑ Z, G.served Z) + 1 := by
      simp [bump, sum_add_distrib]
    rw [e]
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

theorem hstep_reloc {G : GS k q} (hL : LInv L c.s c.σ0 c.F0 G) (hH : HInv L c G) (τ : ℕ)
    {E Z : Sq k} (hb : G.σ.blank = E) (hEZ : E ≠ Z)
    (hfree : ∀ Q, Q ≠ G.σ.blank → 1 ≤ fr G Q) :
    LInv L c.s c.σ0 c.F0 (hstep L c.s τ G (.reloc E Z)) ∧
      HInv L c (hstep L c.s τ G (.reloc E Z)) := by
  obtain ⟨hL', hfr, hjc⟩ := hReloc_linv L hL hb hEZ (fun Q hQ => hfree Q (by rw [hb]; exact hQ))
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11⟩ := hReloc_same (s := c.s) G E Z
  have hgh : gh k c.s (hReloc c.s G E Z) = gh k c.s G := by simp only [gh, r1]
  have hF : ∀ v x, Fcnt L c.s (hReloc c.s G E Z) v x = Fcnt L c.s G v x := by
    intro v x; unfold Fcnt lcnt; rw [hgh]
  have hDp : ∀ v x, Dpos L c.s (hReloc c.s G E Z) v x = Dpos L c.s G v x := by
    intro v x; unfold Dpos lcnt; rw [hgh]
  have hF' : ∀ v x, Fcnt L c.s (hstep L c.s τ G (.reloc E Z)) v x =
      Fcnt L c.s (hReloc c.s G E Z) v x := fun _ _ => rfl
  have hDp' : ∀ v x, Dpos L c.s (hstep L c.s τ G (.reloc E Z)) v x =
      Dpos L c.s (hReloc c.s G E Z) v x := fun _ _ => rfl
  refine ⟨hL'.congr L rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v x hvx
    show (hReloc c.s G E Z).stock v x + _ + (hReloc c.s G E Z).dA v x = (hReloc c.s G E Z).B v x
    rw [r3, r4, r5, hF', hF]; exact hH.ident v x hvx
  · intro v x
    show (hReloc c.s G E Z).dA v x + _ = ∑ u ∈ _, (hReloc c.s G E Z).B u x
    rw [r4, r5, hDp', hDp]; exact hH.dirty v x
  · intro v x
    show (hReloc c.s G E Z).B v x ≤ (hReloc c.s G E Z).dA v x + c.Nv v x + 1 ∧
      ((hReloc c.s G E Z).B v x ≠ 0 → L.Act v x)
    rw [r4, r5]; exact hH.binv v x
  · intro Q
    have h1 := hH.free_lo Q
    have h2 := hfr Q
    show c.fr0 Q + (hReloc c.s G E Z).sent Q + _ + sA (hReloc c.s G E Z) Q ≤
      fr (hReloc c.s G E Z) Q + sB (hReloc c.s G E Z) Q + (hReloc c.s G E Z).served Q +
        (if (hReloc c.s G E Z).σ.blank = Q then 1 else 0)
    have hsA : sA (hReloc c.s G E Z) Q = sA G Q := by unfold sA; rw [r5]
    have hsB : sB (hReloc c.s G E Z) Q = sB G Q := by unfold sB; rw [r4]
    rw [r7, r6, r11, hsA, hsB]
    rw [hb] at h1
    simp only [@eq_comm _ E Q, @eq_comm _ Z Q] at h1 h2 ⊢
    omega
  · show (hReloc c.s G E Z).jc ≤ 3 * (c.s + 3) * (G.wt + relocWeight (HEvent.reloc E Z))
    have := hH.jc
    nlinarith
  · show (hReloc c.s G E Z).nh ≤ 2 * L.depth * ∑ Q, (hReloc c.s G E Z).served Q
    rw [r8, r6]; exact hH.nh
  · show (∑ Q, (hReloc c.s G E Z).served Q) + (∑ S', ∑ D', (hReloc c.s G E Z).sched S' D') = c.S0
    rw [r6, r2]; exact hH.sched_sum

end step

end SlidingPuzzle.Tree
