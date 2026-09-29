import SlidingPuzzle.Port.ServeStage
import SlidingPuzzle.Tree.RunChain

/-! # An aligned stage -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle.Hub (Sq)
open SlidingPuzzle.Tree

variable {k q : ℕ} (L : LaneSys k q)

theorem pAlign_same (s : ℕ) (G : PG k q) (pt : Pt) : XSame G (pAlign L s G pt) := by
  unfold pAlign
  split_ifs
  · exact XSame.refl G
  · exact XSame.pX L G pt
  · exact (XSame.pX L G .tl).trans (XSame.pX L _ pt)

/-- Free tiles of a square. -/
def pfr (G : PG k q) (Z : Sq k) : ℕ := ∑ y, G.free Z y

/-- Placeholders of a square. -/
def psB (G : PG k q) (Z : Sq k) : ℕ := ∑ x, G.B Z x

/-- Dirty arrivals at a square. -/
def psA (G : PG k q) (Z : Sq k) : ℕ := ∑ x, G.dA Z x

section fields
variable (s τ : ℕ) (G : PG k q) (u x : Sq k) (kd : Kind) (y : Sq k) (sp : Pt) (Q z : Sq k)

theorem pStep_dA : (pStep L s τ G u x kd y sp).dA Q z = G.dA Q z +
    (if gdt (pgh k s G (L.stage u x).1 0) = some z ∧ Q = L.nxt u x then 1 else 0) := by
  have h := pAlign_same L s G (dport L u x)
  show (pAlign L s G (dport L u x)).dA Q z + _ = _
  rw [h.dA, h.gh]; rfl

theorem pStep_B : (pStep L s τ G u x kd y sp).B Q z = G.B Q z +
    (if kd = .plh ∧ Q = u ∧ z = x then 1 else 0) := by
  have h := pAlign_same L s G (dport L u x)
  show (pAlign L s G (dport L u x)).B Q z + _ = _
  rw [h.B]

theorem pStep_free : (pStep L s τ G u x kd y sp).free Q z = G.free Q z -
    (if kd = .plh ∧ Q = u ∧ z = y then 1 else 0) +
    (if gcl (pgh k s G (L.stage u x).1 0) = none ∧ Q = L.nxt u x ∧
      z = G.σ.lane (L.stage u x).1 0 then 1 else 0) := by
  have h := pAlign_same L s G (dport L u x)
  show (pAlign L s G (dport L u x)).free Q z - _ + _ = _
  rw [h.free, h.gh, h.lane]; rfl

theorem pStep_sched : (pStep L s τ G u x kd y sp).sched Q z = G.sched Q z -
    (if kd = .sch ∧ Q = u ∧ z = y then 1 else 0) := by
  have h := pAlign_same L s G (dport L u x)
  show (pAlign L s G (dport L u x)).sched Q z - _ = _
  rw [h.sched]

theorem pStep_ins : (pStep L s τ G u x kd y sp).ins = G.ins ++ [⟨τ, (L.stage u x).1,
      LaneSys.pdist (L.stage u x).1.2.t.val (L.stage u x).2.val, (x, decide (kd ≠ .plh))⟩] := by
  have h := pAlign_same L s G (dport L u x)
  show (pAlign L s G (dport L u x)).ins ++ _ = _
  rw [h.ins]

theorem pStep_other : (pStep L s τ G u x kd y sp).served = G.served ∧
    (pStep L s τ G u x kd y sp).sent = G.sent ∧
    (pStep L s τ G u x kd y sp).nh = G.nh + 1 ∧
    (pStep L s τ G u x kd y sp).jc = G.jc ∧ (pStep L s τ G u x kd y sp).wt = G.wt := by
  have h := pAlign_same L s G (dport L u x)
  refine ⟨h.served, h.sent, ?_, h.jc, h.wt⟩
  show (pAlign L s G (dport L u x)).nh + 1 = _
  rw [h.nh]

theorem pStep_frmono (hf : kd = .plh → 1 ≤ G.free u y) (Z : Sq k) :
    pfr G Z + psB G Z + psA (pStep L s τ G u x kd y sp) Z ≤
      pfr (pStep L s τ G u x kd y sp) Z + psB (pStep L s τ G u x kd y sp) Z + psA G Z := by
  unfold pfr psB psA
  simp only [pStep_free, pStep_B, pStep_dA]
  rw [sum_ind_row (fun z => G.B Z z) (kd = .plh) u Z x]
  have hA : ∑ z, (G.dA Z z + if gdt (pgh k s G (L.stage u x).1 0) = some z ∧ Z = L.nxt u x
      then 1 else 0) ≤ (∑ z, G.dA Z z) +
        if gcl (pgh k s G (L.stage u x).1 0) = none ∧ Z = L.nxt u x then 1 else 0 := by
    rw [sum_add_distrib]
    apply Nat.add_le_add_left
    rcases hg : gdt (pgh k s G (L.stage u x).1 0) with _ | z0
    · simp
    · have : gcl (pgh k s G (L.stage u x).1 0) = none := by
        rcases h' : pgh k s G (L.stage u x).1 0 with _ | ⟨⟨x', b⟩, d⟩
        · rfl
        · rw [h'] at hg; cases b <;> simp_all [gcl, gdt]
      rw [this]
      by_cases hZ : Z = L.nxt u x
      · subst hZ
        simp only [Option.some.injEq, and_true, if_true]
        rw [Finset.sum_ite_eq]; simp
      · simp [hZ]
  have hF : (∑ z, G.free Z z) + (if gcl (pgh k s G (L.stage u x).1 0) = none ∧ Z = L.nxt u x
      then 1 else 0) ≤ ∑ z, (G.free Z z - (if kd = .plh ∧ Z = u ∧ z = y then 1 else 0) +
        (if gcl (pgh k s G (L.stage u x).1 0) = none ∧ Z = L.nxt u x ∧
          z = G.σ.lane (L.stage u x).1 0 then 1 else 0)) + (if kd = .plh ∧ Z = u then 1 else 0) := by
    have e1 := sum_ind_row (fun z => G.free Z z - (if kd = .plh ∧ Z = u ∧ z = y then 1 else 0))
      (gcl (pgh k s G (L.stage u x).1 0) = none) (L.nxt u x) Z (G.σ.lane (L.stage u x).1 0)
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

theorem pStep_free_frame (Z : Sq k) (h1 : Z ≠ u) (h2 : Z ≠ L.nxt u x) :
    (pStep L s τ G u x kd y sp).free Z = G.free Z := by
  funext z; rw [pStep_free]; simp [h1, h2]

end fields

section step

variable {n s σ' : ℕ} [NeZero n] (td : TDims n k s q) {σ0 : PState k q} {F0 : ℕ} (τ : ℕ)

/-- The capacity condition: every port exceeds the stock its square can hold. -/
def CapOK (σ0 : PState k q) (Nv : Sq k → Sq k → ℕ) : Prop :=
  ∀ Q pt, stkCap L Nv Q + 1 < psz σ0 Q pt

/-- What an aligned stage gives. -/
structure StepOut (G G' : PG k q) (u x : Sq k) (kd : Kind) : Prop where
  lin : PLInv L s σ' σ0 F0 G'
  blank : G'.σ.blank = u
  bp : G'.σ.bp = dport L u x
  ident : PIdent L s G' x (pendA u kd)
  nx : G'.nx ≤ G.nx + (if G.σ.bp = dport L u x then 0 else 2)
  ni : G'.ni + G.nis ≤ G.ni + G'.nis + (if kd = .stk then 0 else 1)
  nt : G'.nt ≤ G.nt + (if turning L (L.stage u x).1 x then 1 else 0)

include td in
theorem pStep_out {G : PG k q} (hL : PLInv L s σ' σ0 F0 G) {u x : Sq k} (hux : u ≠ x)
    (hb : G.σ.blank = L.nxt u x) (hI : PIdent L s G x (L.pendB u x))
    {Nv : Sq k → Sq k → ℕ} (hB : PBInv L G Nv) (hK : CapOK L σ0 Nv)
    {kd : Kind} {y : Sq k} {sp : Pt} (hr : PRoleOK G u x sp kd y) :
    StepOut L (s := s) (σ' := σ') (σ0 := σ0) (F0 := F0) G (pStep L s τ G u x kd y sp) u x kd := by
  have hcap : ∀ Q pt', (∑ z, G.stk Q z) + 1 < psz σ0 Q pt' := fun Q pt' =>
    lt_of_le_of_lt (Nat.add_le_add_right (stk_sum_le L hL hI hB Q) 1) (hK Q pt')
  set G1 := pAlign L s G (dport L u x) with hG1
  have hs : XSame G G1 := pAlign_same L s G (dport L u x)
  obtain ⟨l1, bp1, -, nx1⟩ := pAlign_linv L hL (dport L u x) (fun pt' => hcap _ pt')
  rw [← hG1] at l1 bp1 nx1
  have hr1 : PRoleOK G1 u x sp kd y := by
    cases kd
    · exact ⟨hr.1, by rw [hs.sched]; exact hr.2⟩
    · exact ⟨hr.1, by rw [hs.stock]; exact hr.2⟩
    · show 1 ≤ G1.free u y; rw [hs.free]; exact hr
  have hcap1 : (∑ z, G1.stk u z) + 1 < psz σ0 u (dport L u x) := by
    rw [hs.stk]; exact hcap u _
  obtain ⟨hm, hsp⟩ := pMode_good L l1 hux hr1 hcap1
  have hb1 : G1.σ.blank = L.nxt u x := by rw [hs.blank]; exact hb
  have hI1 : PIdent L s G1 x (L.pendB u x) := hs.ident L hI
  refine ⟨pStage_linv L td τ l1 hux hb1 bp1 hr1 hm hsp, ?_, rfl, pStage_ident L td τ hux hr1 hI1,
    ?_, ?_, ?_⟩
  · show (G1.σ.step s _).blank = u
    rw [(step_hop_blank _ _ _ _ _ _).1, stage_src hux]
  · show G1.nx ≤ _; exact nx1
  · show G1.ni + _ + G.nis ≤ G.ni + (G1.nis + _) + _
    rw [hs.ni, hs.nis]
    have : Mode.ind (pMode L (pAlign L s G (dport L u x)) u x kd y sp) ≤ 1 := by
      cases pMode L (pAlign L s G (dport L u x)) u x kd y sp <;> simp [Mode.ind]
    split_ifs <;> omega
  · show G1.nt + _ ≤ _
    rw [hs.nt]
    split_ifs <;> simp_all

end step

end SlidingPuzzle.Port
