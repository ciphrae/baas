import SlidingPuzzle.Tree.RunServe

/-! # The gateways of a route, and a whole serve -/
namespace SlidingPuzzle.Tree
open Finset
open SlidingPuzzle.Hub (Sq)

variable {k q : ℕ} (L : LaneSys k q)

/-- Free tiles of a square. -/
def fr (G : GS k q) (Z : Sq k) : ℕ := ∑ y, G.free Z y

/-- Placeholders of a square. -/
def sB (G : GS k q) (Z : Sq k) : ℕ := ∑ x, G.B Z x

/-- Dirty arrivals at a square. -/
def sA (G : GS k q) (Z : Sq k) : ℕ := ∑ x, G.dA Z x

section stage

variable (s τ : ℕ)

theorem sum_ind_row (f : Sq k → ℕ) (c : Prop) [Decidable c] (Z Q y : Sq k) :
    ∑ z, (f z + if c ∧ Q = Z ∧ z = y then 1 else 0) =
      (∑ z, f z) + if c ∧ Q = Z then 1 else 0 := by
  rw [sum_add_distrib]
  congr 1
  by_cases h : c ∧ Q = Z
  · obtain ⟨hc, rfl⟩ := h
    simp [hc]
  · have : ∀ z, ¬ (c ∧ Q = Z ∧ z = y) := fun z h' => h ⟨h'.1, h'.2.1⟩
    simp [this, h]

/-- Free tiles plus placeholders minus dirty arrivals never decrease at a square. -/
theorem gStage_frmono (G : GS k q) (u x : Sq k) (kd : Kind) (y : Sq k)
    (hf : kd = .plh → 1 ≤ G.free u y) (Z : Sq k) :
    fr G Z + sB G Z + sA (gStage L s τ G u x kd y) Z ≤
      fr (gStage L s τ G u x kd y) Z + sB (gStage L s τ G u x kd y) Z + sA G Z := by
  unfold fr sB sA
  simp only [gStage_free, gStage_B, gStage_dA]
  rw [sum_ind_row (fun z => G.B Z z) (kd = .plh) u Z x]
  have hA : ∑ z, (G.dA Z z + if gdt (gh k s G (L.stage u x).1 0) = some z ∧ Z = L.nxt u x
      then 1 else 0) ≤ (∑ z, G.dA Z z) +
        if gcl (gh k s G (L.stage u x).1 0) = none ∧ Z = L.nxt u x then 1 else 0 := by
    rw [sum_add_distrib]
    apply Nat.add_le_add_left
    rcases hg : gdt (gh k s G (L.stage u x).1 0) with _ | z0
    · simp
    · have : gcl (gh k s G (L.stage u x).1 0) = none := by
        rcases h' : gh k s G (L.stage u x).1 0 with _ | ⟨⟨x', b⟩, d⟩
        · rfl
        · rw [h'] at hg; cases b <;> simp_all [gcl, gdt]
      rw [this]
      by_cases hZ : Z = L.nxt u x
      · subst hZ
        simp only [Option.some.injEq, and_true, if_true]
        rw [Finset.sum_ite_eq]; simp
      · simp [hZ]
  have hF : (∑ z, G.free Z z) + (if gcl (gh k s G (L.stage u x).1 0) = none ∧ Z = L.nxt u x
      then 1 else 0) ≤ ∑ z, (G.free Z z - (if kd = .plh ∧ Z = u ∧ z = y then 1 else 0) +
        (if gcl (gh k s G (L.stage u x).1 0) = none ∧ Z = L.nxt u x ∧
          z = G.σ.lane (L.stage u x).1 0 then 1 else 0)) + (if kd = .plh ∧ Z = u then 1 else 0) := by
    have e1 := sum_ind_row (fun z => G.free Z z - (if kd = .plh ∧ Z = u ∧ z = y then 1 else 0))
      (gcl (gh k s G (L.stage u x).1 0) = none) (L.nxt u x) Z (G.σ.lane (L.stage u x).1 0)
    rw [e1]
    have e2 : (∑ z, (G.free Z z - if kd = .plh ∧ Z = u ∧ z = y then 1 else 0)) +
        (if kd = .plh ∧ Z = u then 1 else 0) = ∑ z, G.free Z z := by
      have := sum_ind_row (fun z => G.free Z z - (if kd = .plh ∧ Z = u ∧ z = y then 1 else 0))
        (kd = .plh) u Z y
      have h2 : ∀ z, (G.free Z z - (if kd = .plh ∧ Z = u ∧ z = y then 1 else 0)) +
          (if kd = .plh ∧ Z = u ∧ z = y then 1 else 0) = G.free Z z := by
        intro z
        split_ifs with h
        · obtain ⟨h1, rfl, rfl⟩ := h; have := hf h1; omega
        · rfl
      rw [Finset.sum_congr rfl fun z _ => h2 z] at this
      have e3 : univ.sum (G.free Z) = ∑ z, G.free Z z := rfl
      omega
    omega
  omega

theorem gStage_free_frame (G : GS k q) (u x : Sq k) (kd : Kind) (y Z : Sq k)
    (h1 : Z ≠ u) (h2 : Z ≠ L.nxt u x) : (gStage L s τ G u x kd y).free Z = G.free Z := by
  funext z; rw [gStage_free]; simp [h1, h2]

end stage

section gates

variable {n s : ℕ} [NeZero n] (td : TDims n k s q) {σ0 : IState k q} {F0 : ℕ} (τ : ℕ)

/-- What holds after the gateways of the route from `w` to `D`. -/
structure GateInv (Nv : Sq k → Sq k → ℕ) (G0 G : GS k q) (w D : Sq k) : Prop where
  lin : LInv L s σ0 F0 G
  blank : G.σ.blank = w
  ident : Ident L s G D (if w = D then none else some w)
  dirty : DirtyInv L s G
  binv : BInv L G Nv
  frame : ∀ Z, Z ∉ L.nodes w D → Z ≠ D → G.free Z = G0.free Z
  mono : ∀ Z, fr G0 Z + sB G0 Z + sA G Z ≤ fr G Z + sB G Z + sA G0 Z
  sched : G.sched = G0.sched
  served : G.served = G0.served
  sent : G.sent = G0.sent
  nh : G.nh = G0.nh + (L.nodes w D).length
  jc : G.jc = G0.jc
  wt : G.wt = G0.wt
  pre : G0.ins <+: G.ins

theorem gGate_ins_prefix (G : GS k q) (u D : Sq k) : G.ins <+: (gGate L s τ G u D).ins := by
  unfold gGate; split_ifs <;> exact List.prefix_append _ _

include td in
theorem hGates_inv (Nv : Sq k → Sq k → ℕ) {G0 : GS k q} (hL : LInv L s σ0 F0 G0) {D : Sq k}
    (hb : G0.σ.blank = D) (hI : Ident L s G0 D none) (hD : DirtyInv L s G0)
    (hB : BInv L G0 Nv) (Lfin : List (GRec k q))
    (hFb : ∀ G' : GS k q, G'.ins <+: Lfin → ∀ v x, Fcnt L s G' v x ≤ Nv v x) :
    ∀ w, (∀ u ∈ L.nodes w D, 1 ≤ fr G0 u ∧ L.Act u D) →
      (hGates L s τ G0 w D).ins <+: Lfin →
      GateInv L (s := s) (σ0 := σ0) (F0 := F0) Nv G0 (hGates L s τ G0 w D) w D := by
  intro w
  induction hr : L.srank w D generalizing w with
  | zero =>
    intro _ _
    have hw := srank_eq_zero hr
    subst hw
    rw [hGates_self]
    refine ⟨hL, hb, by simpa using hI, hD, hB, fun _ _ _ => rfl, fun Z => le_rfl, rfl, rfl, rfl,
      by rw [nodes_self]; rfl, rfl, rfl, List.prefix_refl _⟩
  | succ r ih =>
    intro hav hpre
    have hwD : w ≠ D := fun e => by rw [e, srank_self] at hr; omega
    have hrn := srank_nxt (L := L) hwD
    rw [hGates_cons L s τ G0 hwD] at hpre ⊢
    have hav1 : ∀ u ∈ L.nodes (L.nxt w D) D, 1 ≤ fr G0 u ∧ L.Act u D := fun u hu =>
      hav u (by rw [nodes_cons L hwD]; exact List.mem_cons_of_mem _ hu)
    have hpre1 : (hGates L s τ G0 (L.nxt w D) D).ins <+: Lfin :=
      (gGate_ins_prefix L τ _ w D).trans hpre
    have I1 := ih (L.nxt w D) (by omega) hav1 hpre1
    generalize hG1 : hGates L s τ G0 (L.nxt w D) D = G1 at I1 hpre1 hpre ⊢
    have hwn : w ∉ L.nodes (L.nxt w D) D := fun hm => by
      have := (mem_nodes L hm).2.1; omega
    have hfree : G1.free w = G0.free w := I1.frame w hwn hwD
    have havw := hav w (by rw [nodes_cons L hwD]; exact List.mem_cons_self)
    have hfrw : 1 ≤ fr G1 w := by unfold fr; rw [hfree]; exact havw.1
    have hI1 : Ident L s G1 D (L.pendB w D) := I1.ident
    -- the kind of the inserted tile
    have hkind : ∃ kd y, gGate L s τ G1 w D = gStage L s τ G1 w D kd y ∧ kd ≠ .sch ∧
        RoleOK G1 w D kd y ∧ (kd = .plh → G1.stock w D = 0) := by
      unfold gGate
      split_ifs with hst
      · exact ⟨.stk, D, rfl, by simp, ⟨rfl, hst⟩, by simp⟩
      · exact ⟨.plh, pickFree G1 w, rfl, by simp, pickFree_spec G1 w hfrw, fun _ => by omega⟩
    obtain ⟨kd, y, hgate, hkd, hrole, hzero⟩ := hkind
    rw [hgate]
    have hpA : pendA w kd = some w := by unfold pendA; simp [hkd]
    refine ⟨gStage_linv L td τ I1.lin hwD I1.blank hrole, ?_, ?_,
      gStage_dirty L td τ hwD I1.dirty, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (G1.σ.step s (hopEv (L.stage w D).1 (L.stage w D).2 y)).blank = w
      rw [step_hopEv_blank, stage_src hwD]
    · rw [if_neg hwD, ← hpA]
      exact gStage_ident L td τ I1.lin hwD hrole hI1
    · -- placeholders
      intro v x
      have hB1 := I1.binv v x
      rw [gStage_B, gStage_dA]
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
      rw [gStage_free_frame L s τ G1 w D kd y Z hZw hZv]
      exact I1.frame Z hZn hZD
    · intro Z
      have h1 := I1.mono Z
      have h2 := gStage_frmono L s τ G1 w D kd y (fun h => by
        subst h; simp only [RoleOK] at hrole; exact hrole) Z
      omega
    · show (gStage L s τ G1 w D kd y).sched = G0.sched
      funext Q z; rw [gStage_sched, ← I1.sched]; simp [hkd]
    · exact I1.served
    · exact I1.sent
    · show G1.nh + 1 = G0.nh + (L.nodes w D).length
      rw [I1.nh, nodes_cons L hwD, List.length_cons]; ring
    · exact I1.jc
    · exact I1.wt
    · exact I1.pre.trans (List.prefix_append _ _)

theorem act_of_nodes (D : Sq k) : ∀ w u, u ∈ L.nodes (L.nxt w D) D → w ≠ D → L.Act u D := by
  intro w u hu hw
  induction hr : L.srank (L.nxt w D) D generalizing w with
  | zero =>
    rw [srank_eq_zero hr, nodes_self] at hu; simp at hu
  | succ r ih =>
    have hne : L.nxt w D ≠ D := fun e => by rw [e, srank_self] at hr; omega
    rw [nodes_cons L hne, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact ⟨w, hw, rfl⟩
    · have := srank_nxt (L := L) hne
      exact ih (L.nxt w D) hu hne (by omega)

/-- What holds after a serve. -/
structure ServeInv (Nv : Sq k → Sq k → ℕ) (G0 G : GS k q) (S D : Sq k) : Prop where
  lin : LInv L s σ0 F0 G
  blank : G.σ.blank = S
  ident : Ident L s G D none
  dirty : DirtyInv L s G
  binv : BInv L G Nv
  frame : ∀ Z, Z ∉ L.nodes S D → Z ≠ D → G.free Z = G0.free Z
  mono : ∀ Z, fr G0 Z + sB G0 Z + sA G Z ≤ fr G Z + sB G Z + sA G0 Z
  sched : ∀ Q z, G.sched Q z = G0.sched Q z - (if Q = S ∧ z = D then 1 else 0)
  served : G.served = G0.served
  sent : G.sent = G0.sent
  nh : G.nh = G0.nh + L.srank S D
  jc : G.jc = G0.jc
  wt : G.wt = G0.wt
  pre : G0.ins <+: G.ins

include td in
theorem hServe_inv (Nv : Sq k → Sq k → ℕ) {G0 : GS k q} (hL : LInv L s σ0 F0 G0) {S D : Sq k}
    (hSD : S ≠ D) (hb : G0.σ.blank = D) (hI : Ident L s G0 D none) (hD : DirtyInv L s G0)
    (hB : BInv L G0 Nv) (Lfin : List (GRec k q))
    (hFb : ∀ G' : GS k q, G'.ins <+: Lfin → ∀ v x, Fcnt L s G' v x ≤ Nv v x)
    (hsch : 1 ≤ G0.sched S D) (hav : ∀ u ∈ L.nodes (L.nxt S D) D, 1 ≤ fr G0 u)
    (hpre : (hServe L s τ G0 S D).ins <+: Lfin) :
    ServeInv L (s := s) (σ0 := σ0) (F0 := F0) Nv G0 (hServe L s τ G0 S D) S D := by
  have hpre1 : (hGates L s τ G0 (L.nxt S D) D).ins <+: Lfin :=
    (List.prefix_append _ _).trans hpre
  have I1 := hGates_inv L td τ Nv hL hb hI hD hB Lfin hFb (L.nxt S D)
    (fun u hu => ⟨hav u hu, act_of_nodes L D S u hu hSD⟩) hpre1
  unfold hServe
  generalize hG1 : hGates L s τ G0 (L.nxt S D) D = G1 at I1
  have hrole : RoleOK G1 S D .sch D := ⟨rfl, by rw [I1.sched]; exact hsch⟩
  have hI1 : Ident L s G1 D (L.pendB S D) := I1.ident
  have hSn : S ∉ L.nodes (L.nxt S D) D := fun hm => by
    have := (mem_nodes L hm).2.1; have := srank_nxt (L := L) hSD; omega
  refine ⟨gStage_linv L td τ I1.lin hSD I1.blank hrole, ?_, ?_,
    gStage_dirty L td τ hSD I1.dirty, ?_, ?_, ?_, ?_, I1.served, I1.sent, ?_, I1.jc, I1.wt,
    I1.pre.trans (List.prefix_append _ _)⟩
  · show (G1.σ.step s (hopEv (L.stage S D).1 (L.stage S D).2 D)).blank = S
    rw [step_hopEv_blank, stage_src hSD]
  · have := gStage_ident L td τ I1.lin hSD hrole hI1
    simpa [pendA] using this
  · intro v x
    have := I1.binv v x
    rw [gStage_B, gStage_dA]
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
    rw [gStage_free_frame L s τ G1 S D .sch D Z hZS hZv]
    exact I1.frame Z hZn hZD
  · intro Z
    have h1 := I1.mono Z
    have h2 := gStage_frmono L s τ G1 S D .sch D (fun h => by cases h) Z
    omega
  · intro Q z
    rw [gStage_sched, I1.sched]
    simp
  · show G1.nh + 1 = G0.nh + L.srank S D
    rw [I1.nh, length_nodes, srank_nxt (L := L) hSD]; ring

end gates

end SlidingPuzzle.Tree
