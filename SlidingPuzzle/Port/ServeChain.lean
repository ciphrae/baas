import SlidingPuzzle.Port.ServeStep

/-! # The gateways of a route, and a whole serve, with ports -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle.Hub (Sq)
open SlidingPuzzle.Tree

variable {k q : ℕ} (L : LaneSys k q)

/-- Stages of the route from `w` to `D` landing at a turn. -/
def tcnt (w D : Sq k) : ℕ := (L.nodes w D).countP fun u => decide (turning L (L.stage u D).1 D)

theorem tcnt_self (D : Sq k) : tcnt L D D = 0 := by unfold tcnt; rw [nodes_self]; rfl

theorem tcnt_cons {w D : Sq k} (h : w ≠ D) :
    tcnt L w D = tcnt L (L.nxt w D) D + (if turning L (L.stage w D).1 D then 1 else 0) := by
  unfold tcnt; rw [nodes_cons L h, List.countP_cons]; simp

/-- All placeholders. -/
def sBt (G : PG k q) : ℕ := ∑ Q, ∑ x, G.B Q x

theorem pStep_sBt (s τ : ℕ) (G : PG k q) (u x : Sq k) (kd : Kind) (y : Sq k) (sp : Pt) :
    sBt (pStep L s τ G u x kd y sp) = sBt G + (if kd = .plh then 1 else 0) := by
  unfold sBt
  simp only [pStep_B]
  exact sum_sum_add_ind G.B _ u x

theorem turning_of_bp {w D : Sq k} (hn : L.nxt w D ≠ D)
    (h : dport L (L.nxt w D) D ≠ dport L w D) : turning L (L.stage w D).1 D :=
  ⟨hn, fun e => h e.symm⟩

section gates

variable {n s σ' : ℕ} [NeZero n] (td : TDims n k s q) {σ0 : PState k q} {F0 : ℕ} (τ : ℕ)

/-- What holds after the gateways of the route from `w` to `D`. -/
structure PGateInv (Nv : Sq k → Sq k → ℕ) (G0 G : PG k q) (w D : Sq k) : Prop where
  lin : PLInv L s σ' σ0 F0 G
  blank : G.σ.blank = w
  bp : w ≠ D → G.σ.bp = dport L w D
  ident : PIdent L s G D (if w = D then none else some w)
  dirty : PDirtyInv L s G
  binv : PBInv L G Nv
  frame : ∀ Z, Z ∉ L.nodes w D → Z ≠ D → G.free Z = G0.free Z
  mono : ∀ Z, pfr G0 Z + psB G0 Z + psA G Z ≤ pfr G Z + psB G Z + psA G0 Z
  sched : G.sched = G0.sched
  served : G.served = G0.served
  sent : G.sent = G0.sent
  nh : G.nh = G0.nh + (L.nodes w D).length
  jc : G.jc = G0.jc
  wt : G.wt = G0.wt
  pre : G0.ins <+: G.ins
  nx : G.nx ≤ G0.nx + (if w = D then 0 else 2) + 2 * tcnt L w D
  ni : G.ni + G0.nis + sBt G0 ≤ G0.ni + G.nis + sBt G
  nt : G.nt ≤ G0.nt + tcnt L w D

theorem pGate_ins_prefix (G : PG k q) (u D : Sq k) : G.ins <+: (pGate L s τ G u D).ins := by
  unfold pGate; split_ifs <;> (rw [pStep_ins]; exact List.prefix_append _ _)

include td in
theorem pGates_inv (Nv : Sq k → Sq k → ℕ) (hK : CapOK L σ0 Nv) {G0 : PG k q}
    (hL : PLInv L s σ' σ0 F0 G0) {D : Sq k}
    (hb : G0.σ.blank = D) (hI : PIdent L s G0 D none) (hD : PDirtyInv L s G0)
    (hB : PBInv L G0 Nv) (Lfin : List (GRec k q))
    (hFb : ∀ G' : PG k q, G'.ins <+: Lfin → ∀ v x, pFcnt L s G' v x ≤ Nv v x) :
    ∀ w, (∀ u ∈ L.nodes w D, 1 ≤ pfr G0 u ∧ L.Act u D) →
      (pGates L s τ G0 w D).ins <+: Lfin →
      PGateInv L (s := s) (σ' := σ') (σ0 := σ0) (F0 := F0) Nv G0 (pGates L s τ G0 w D) w D := by
  intro w
  induction hr : L.srank w D generalizing w with
  | zero =>
    intro _ _
    have hw := srank_eq_zero hr
    subst hw
    rw [pGates_self]
    refine ⟨hL, hb, fun h => absurd rfl h, by simpa using hI, hD, hB, fun _ _ _ => rfl,
      fun Z => le_rfl, rfl, rfl, rfl, by rw [nodes_self]; rfl, rfl, rfl, List.prefix_refl _,
      by simp, le_rfl, by simp⟩
  | succ r ih =>
    intro hav hpre
    have hwD : w ≠ D := fun e => by rw [e, srank_self] at hr; omega
    have hrn := srank_nxt (L := L) hwD
    rw [pGates_cons L s τ G0 hwD] at hpre ⊢
    have hav1 : ∀ u ∈ L.nodes (L.nxt w D) D, 1 ≤ pfr G0 u ∧ L.Act u D := fun u hu =>
      hav u (by rw [nodes_cons L hwD]; exact List.mem_cons_of_mem _ hu)
    have hpre1 : (pGates L s τ G0 (L.nxt w D) D).ins <+: Lfin :=
      (pGate_ins_prefix L τ _ w D).trans hpre
    have I1 := ih (L.nxt w D) (by omega) hav1 hpre1
    generalize hG1 : pGates L s τ G0 (L.nxt w D) D = G1 at I1 hpre1 hpre ⊢
    have hwn : w ∉ L.nodes (L.nxt w D) D := fun hm => by
      have := (mem_nodes L hm).2.1; omega
    have hfree : G1.free w = G0.free w := I1.frame w hwn hwD
    have havw := hav w (by rw [nodes_cons L hwD]; exact List.mem_cons_self)
    have hfrw : 1 ≤ pfr G1 w := by unfold pfr; rw [hfree]; exact havw.1
    have hI1 : PIdent L s G1 D (L.pendB w D) := I1.ident
    -- the kind of the inserted tile
    have hkind : ∃ kd y sp, pGate L s τ G1 w D = pStep L s τ G1 w D kd y sp ∧ kd ≠ .sch ∧
        PRoleOK G1 w D sp kd y ∧ (kd = .plh → G1.stk w D = 0) := by
      unfold pGate
      split_ifs with hst
      · exact ⟨.stk, D, _, rfl, by simp, ⟨rfl, pickSp_spec L G1 w D hst⟩, by simp⟩
      · exact ⟨.plh, pickFreeP G1 w, .tl, rfl, by simp, pickFreeP_spec G1 w hfrw,
          fun _ => by omega⟩
    obtain ⟨kd, y, sp, hgate, hkd, hrole, hzero⟩ := hkind
    rw [hgate]
    have hpA : pendA w kd = some w := by unfold pendA; simp [hkd]
    have O := pStep_out L td τ I1.lin hwD I1.blank hI1 I1.binv hK hrole
    have hdirty : PDirtyInv L s (pStep L s τ G1 w D kd y sp) :=
      pStage_dirty L td τ hwD ((pAlign_same L s G1 (dport L w D)).dirty L I1.dirty)
    obtain ⟨o1, o2, o3, o4, o5⟩ := pStep_other L s τ G1 w D kd y sp
    refine ⟨O.lin, O.blank, fun _ => O.bp, ?_, hdirty, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · rw [if_neg hwD, ← hpA]; exact O.ident
    · -- placeholders
      intro v x
      have hB1 := I1.binv v x
      rw [pStep_B, pStep_dA]
      by_cases hvx : kd = .plh ∧ v = w ∧ x = D
      · obtain ⟨hp, hv, hx⟩ := hvx
        rw [if_pos ⟨hp, hv, hx⟩, hv, hx]
        have hid := I1.ident w D hwD
        have h0 : ¬ ((if L.nxt w D = D then none else some (L.nxt w D)) = some w ∧ D = D) := by
          rintro ⟨h1, -⟩
          by_cases h3 : L.nxt w D = D
          · rw [if_pos h3] at h1; simp at h1
          · rw [if_neg h3] at h1; exact nxt_ne L hwD (Option.some.inj h1)
        rw [if_neg h0] at hid
        have hst := hzero hp
        have hF := hFb G1 hpre1 w D
        refine ⟨by omega, fun _ => havw.2⟩
      · rw [if_neg hvx]
        refine ⟨by omega, hB1.2⟩
    · intro Z hZ hZD
      have hZw : Z ≠ w := fun e => hZ (by rw [e, nodes_cons L hwD]; exact List.mem_cons_self)
      have hZn : Z ∉ L.nodes (L.nxt w D) D := fun hm =>
        hZ (by rw [nodes_cons L hwD]; exact List.mem_cons_of_mem _ hm)
      have hZv : Z ≠ L.nxt w D := by
        intro e
        by_cases hn : L.nxt w D = D
        · exact hZD (e.trans hn)
        · apply hZn; rw [e, nodes_cons L hn]; exact List.mem_cons_self
      rw [pStep_free_frame L s τ G1 w D kd y sp Z hZw hZv]
      exact I1.frame Z hZn hZD
    · intro Z
      have h1 := I1.mono Z
      have h2 := pStep_frmono L s τ G1 w D kd y sp (fun h => by
        subst h; exact hrole) Z
      omega
    · funext Q z; rw [pStep_sched, ← I1.sched]; simp [hkd]
    · rw [o1, I1.served]
    · rw [o2, I1.sent]
    · rw [o3, I1.nh, nodes_cons L hwD, List.length_cons]; ring
    · rw [o4, I1.jc]
    · rw [o5, I1.wt]
    · rw [pStep_ins]; exact I1.pre.trans (List.prefix_append _ _)
    · -- transfers
      have h1 := O.nx
      have h2 := I1.nx
      rw [tcnt_cons L hwD, if_neg hwD]
      by_cases hn : L.nxt w D = D
      · rw [if_pos hn] at h2
        split_ifs at h1 ⊢ <;> omega
      · rw [if_neg hn] at h2
        rw [I1.bp hn] at h1
        by_cases hd : dport L (L.nxt w D) D = dport L w D
        · rw [if_pos hd] at h1
          split_ifs <;> omega
        · rw [if_neg hd] at h1
          rw [if_pos (turning_of_bp L hn hd)]
          omega
    · have h1 := O.ni
      have h2 := I1.ni
      have h3 := pStep_sBt L s τ G1 w D kd y sp
      cases kd <;> simp at hkd h1 h3 ⊢ <;> omega
    · have h1 := O.nt
      have h2 := I1.nt
      rw [tcnt_cons L hwD]
      omega

theorem act_of_nodes' (D : Sq k) : ∀ w u, u ∈ L.nodes (L.nxt w D) D → w ≠ D → L.Act u D :=
  act_of_nodes L D

/-- What holds after a serve. -/
structure PServeInv (Nv : Sq k → Sq k → ℕ) (G0 G : PG k q) (S D : Sq k) : Prop where
  lin : PLInv L s σ' σ0 F0 G
  blank : G.σ.blank = S
  ident : PIdent L s G D none
  dirty : PDirtyInv L s G
  binv : PBInv L G Nv
  frame : ∀ Z, Z ∉ L.nodes S D → Z ≠ D → G.free Z = G0.free Z
  mono : ∀ Z, pfr G0 Z + psB G0 Z + psA G Z ≤ pfr G Z + psB G Z + psA G0 Z
  sched : ∀ Q z, G.sched Q z = G0.sched Q z - (if Q = S ∧ z = D then 1 else 0)
  served : G.served = G0.served
  sent : G.sent = G0.sent
  nh : G.nh = G0.nh + L.srank S D
  jc : G.jc = G0.jc
  wt : G.wt = G0.wt
  pre : G0.ins <+: G.ins
  nx : G.nx ≤ G0.nx + 2 + 2 * tcnt L S D
  ni : G.ni + G0.nis + sBt G0 ≤ G0.ni + G.nis + sBt G + 1
  nt : G.nt ≤ G0.nt + tcnt L S D

include td in
theorem pServe_inv (Nv : Sq k → Sq k → ℕ) (hK : CapOK L σ0 Nv) {G0 : PG k q}
    (hL : PLInv L s σ' σ0 F0 G0) {S D : Sq k}
    (hSD : S ≠ D) (hb : G0.σ.blank = D) (hI : PIdent L s G0 D none) (hD : PDirtyInv L s G0)
    (hB : PBInv L G0 Nv) (Lfin : List (GRec k q))
    (hFb : ∀ G' : PG k q, G'.ins <+: Lfin → ∀ v x, pFcnt L s G' v x ≤ Nv v x)
    (hsch : 1 ≤ G0.sched S D) (hav : ∀ u ∈ L.nodes (L.nxt S D) D, 1 ≤ pfr G0 u)
    (hpre : (pServe L s τ G0 S D).ins <+: Lfin) :
    PServeInv L (s := s) (σ' := σ') (σ0 := σ0) (F0 := F0) Nv G0 (pServe L s τ G0 S D) S D := by
  have hpre1 : (pGates L s τ G0 (L.nxt S D) D).ins <+: Lfin := by
    refine List.IsPrefix.trans ?_ hpre
    unfold pServe; rw [pStep_ins]; exact List.prefix_append _ _
  have I1 := pGates_inv L td τ Nv hK hL hb hI hD hB Lfin hFb (L.nxt S D)
    (fun u hu => ⟨hav u hu, act_of_nodes L D S u hu hSD⟩) hpre1
  unfold pServe
  generalize hG1 : pGates L s τ G0 (L.nxt S D) D = G1 at I1
  have hrole : PRoleOK G1 S D .tl .sch D := ⟨rfl, by rw [I1.sched]; exact hsch⟩
  have hI1 : PIdent L s G1 D (L.pendB S D) := I1.ident
  have hSn : S ∉ L.nodes (L.nxt S D) D := fun hm => by
    have := (mem_nodes L hm).2.1; have := srank_nxt (L := L) hSD; omega
  have O := pStep_out L td τ I1.lin hSD I1.blank hI1 I1.binv hK hrole
  have hdirty : PDirtyInv L s (pStep L s τ G1 S D .sch D .tl) :=
    pStage_dirty L td τ hSD ((pAlign_same L s G1 (dport L S D)).dirty L I1.dirty)
  obtain ⟨o1, o2, o3, o4, o5⟩ := pStep_other L s τ G1 S D .sch D .tl
  refine ⟨O.lin, O.blank, ?_, hdirty, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := O.ident
    simpa [pendA] using this
  · intro v x
    have := I1.binv v x
    rw [pStep_B, pStep_dA]
    simp only [reduceCtorEq, false_and, if_false, add_zero]
    exact ⟨by omega, this.2⟩
  · intro Z hZ hZD
    have hZS : Z ≠ S := fun e => hZ (by rw [e, nodes_cons L hSD]; exact List.mem_cons_self)
    have hZn : Z ∉ L.nodes (L.nxt S D) D := fun hm =>
      hZ (by rw [nodes_cons L hSD]; exact List.mem_cons_of_mem _ hm)
    have hZv : Z ≠ L.nxt S D := by
      intro e
      by_cases hn : L.nxt S D = D
      · exact hZD (e.trans hn)
      · apply hZn; rw [e, nodes_cons L hn]; exact List.mem_cons_self
    rw [pStep_free_frame L s τ G1 S D .sch D .tl Z hZS hZv]
    exact I1.frame Z hZn hZD
  · intro Z
    have h1 := I1.mono Z
    have h2 := pStep_frmono L s τ G1 S D .sch D .tl (fun h => by cases h) Z
    omega
  · intro Q z
    rw [pStep_sched, I1.sched]
    simp
  · rw [o1, I1.served]
  · rw [o2, I1.sent]
  · rw [o3, I1.nh, length_nodes, srank_nxt (L := L) hSD]; ring
  · rw [o4, I1.jc]
  · rw [o5, I1.wt]
  · rw [pStep_ins]; exact I1.pre.trans (List.prefix_append _ _)
  · have h1 := O.nx
    have h2 := I1.nx
    rw [tcnt_cons L hSD]
    by_cases hn : L.nxt S D = D
    · rw [if_pos hn] at h2
      split_ifs at h1 ⊢ <;> omega
    · rw [if_neg hn] at h2
      rw [I1.bp hn] at h1
      by_cases hd : dport L (L.nxt S D) D = dport L S D
      · rw [if_pos hd] at h1
        split_ifs <;> omega
      · rw [if_neg hd] at h1
        rw [if_pos (turning_of_bp L hn hd)]
        omega
  · have h1 := O.ni
    have h2 := I1.ni
    have h3 := pStep_sBt L s τ G1 S D .sch D .tl
    simp at h1 h3
    omega
  · have h1 := O.nt
    have h2 := I1.nt
    rw [tcnt_cons L hSD]
    omega

end gates

end SlidingPuzzle.Port
