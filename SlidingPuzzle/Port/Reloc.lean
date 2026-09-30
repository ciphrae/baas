import SlidingPuzzle.Port.Turns
import SlidingPuzzle.Hub.RoundWalk

/-! # Relocations of the blank, with ports

As `Tree.RunReloc`: a relocation is one leg (aligned squares) or two through the
corner `(Z.1, E.2)`. Each leg carries a free tile of its target from a part with a
surplus of its class, evicting a surplus class of the blank's port kind if needed. -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle.Hub (Sq sqDist HEvent relocWeight)
open SlidingPuzzle.Tree

variable {k q : ℕ} (L : LaneSys k q)

open Classical in
/-- A part of `Q` with a surplus of class `y`. -/
noncomputable def pickAny (G : PG k q) (Q y : Sq k) : Part :=
  if h : ∃ p, dem L G Q p y < G.σ.partCnt Q p y then Classical.choose h else none

theorem pickAny_spec (G : PG k q) (Q y : Sq k) (h : ∃ p, dem L G Q p y < G.σ.partCnt Q p y) :
    dem L G Q (pickAny L G Q y) y < G.σ.partCnt Q (pickAny L G Q y) y := by
  unfold pickAny; rw [dif_pos h]; exact Classical.choose_spec h

/-- One leg to `Z`, carrying a free tile of `Z`. -/
noncomputable def pLegF (s σ' : ℕ) (G : PG k q) (Z : Sq k) : PG k q :=
  pLeg s σ' G Z (pickFreeP G Z) (pickAny L G Z (pickFreeP G Z)) (pickSur L G Z G.σ.bp)

/-- A relocation. -/
noncomputable def pReloc (s σ' : ℕ) (G : PG k q) (E Z : Sq k) : PG k q :=
  if E.1 = Z.1 ∨ E.2 = Z.2 then pLegF L s σ' G Z else pLegF L s σ' (pLegF L s σ' G (Z.1, E.2)) Z

/-- What a leg keeps. -/
structure LSame (G G' : PG k q) : Prop where
  ins : G'.ins = G.ins
  sched : G'.sched = G.sched
  stock : G'.stock = G.stock
  B : G'.B = G.B
  dA : G'.dA = G.dA
  served : G'.served = G.served
  sent : G'.sent = G.sent
  nh : G'.nh = G.nh
  ni : G'.ni = G.ni
  nx : G'.nx = G.nx
  nt : G'.nt = G.nt
  nis : G'.nis = G.nis
  wt : G'.wt = G.wt
  ncr : G'.ncr = G.ncr

theorem LSame.refl (G : PG k q) : LSame G G :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem LSame.trans {G G' G'' : PG k q} (h : LSame G G') (h' : LSame G' G'') : LSame G G'' :=
  ⟨h'.ins.trans h.ins, h'.sched.trans h.sched, h'.stock.trans h.stock, h'.B.trans h.B,
    h'.dA.trans h.dA, h'.served.trans h.served, h'.sent.trans h.sent, h'.nh.trans h.nh,
    h'.ni.trans h.ni, h'.nx.trans h.nx, h'.nt.trans h.nt, h'.nis.trans h.nis, h'.wt.trans h.wt,
    h'.ncr.trans h.ncr⟩

theorem LSame.stk {G G' : PG k q} (h : LSame G G') : G'.stk = G.stk := by
  funext Q z; unfold PG.stk; rw [h.stock]

theorem LSame.gh {s : ℕ} {G G' : PG k q} (h : LSame G G') : pgh k s G' = pgh k s G := by
  unfold SlidingPuzzle.Port.pgh; rw [h.ins]

theorem LSame.lc {s : ℕ} {G G' : PG k q} (h : LSame G G') (V : Ln k q → Prop) [DecidablePred V]
    (P : Option (GCls k × ℕ) → Prop) [DecidablePred P] : plcnt L s G' V P = plcnt L s G V P := by
  unfold SlidingPuzzle.Port.plcnt; rw [h.gh]

theorem LSame.ident {s : ℕ} {G G' : PG k q} (h : LSame G G') {D : Sq k} {p : Option (Sq k)}
    (hI : PIdent L s G D p) : PIdent L s G' D p := by
  intro v x hvx
  have := hI v x hvx
  unfold pFcnt at this ⊢
  rw [h.stk, h.lc, h.dA, h.B]; exact this

theorem LSame.dirty {s : ℕ} {G G' : PG k q} (h : LSame G G') (hD : PDirtyInv L s G) :
    PDirtyInv L s G' := by
  intro v x
  have := hD v x
  unfold pDpos at this ⊢
  rw [h.lc, h.dA, h.B]; exact this

theorem LSame.binv {G G' : PG k q} (h : LSame G G') {Nv : Sq k → Sq k → ℕ} (hB : PBInv L G Nv) :
    PBInv L G' Nv := by
  intro v x; rw [h.B, h.dA]; exact hB v x

section legs

variable {s σ' : ℕ} {σ0 : PState k q} {F0 : ℕ}

theorem pLegF_same (G : PG k q) (Z : Sq k) : LSame G (pLegF L s σ' G Z) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem pLegF_blank (G : PG k q) (Z : Sq k) : (pLegF L s σ' G Z).σ.blank = Z ∧
    (pLegF L s σ' G Z).σ.bp = G.σ.bp := ⟨rfl, rfl⟩

theorem pLegF_jc (G : PG k q) (Z : Sq k) :
    (pLegF L s σ' G Z).jc = G.jc + legK k s σ' (sqDist G.σ.blank Z) := rfl

theorem pLegF_fr (G : PG k q) (Z : Sq k) (hEZ : G.σ.blank ≠ Z) (hf : 1 ≤ pfr G Z) (Q : Sq k) :
    pfr (pLegF L s σ' G Z) Q + (if Q = Z then 1 else 0) =
      pfr G Q + (if Q = G.σ.blank then 1 else 0) := by
  have hp := pickFreeP_spec G Z hf
  set E := G.σ.blank
  set y := pickFreeP G Z
  unfold pfr
  have e : ∀ x, (pLegF L s σ' G Z).free Q x = G.free Q x - (if Q = Z ∧ x = y then 1 else 0) +
      (if Q = E ∧ x = y then 1 else 0) := fun x => rfl
  simp only [e]
  have e2 : ∀ x, (G.free Q x - (if Q = Z ∧ x = y then 1 else 0) +
      (if Q = E ∧ x = y then 1 else 0)) + (if Q = Z ∧ x = y then 1 else 0) =
      G.free Q x + (if Q = E ∧ x = y then 1 else 0) := by
    intro x
    split_ifs with h1 h2 h2 <;> try omega
    · obtain ⟨rfl, rfl⟩ := h1; omega
    · obtain ⟨rfl, rfl⟩ := h1; omega
  have e1 := Finset.sum_congr rfl fun x (_ : x ∈ univ) => e2 x
  simp only [sum_add_distrib] at e1 ⊢
  have hZ : ∑ x, (if Q = Z ∧ x = y then 1 else 0) = if Q = Z then 1 else 0 := by
    by_cases hq : Q = Z <;> simp [hq]
  have hE : ∑ x, (if Q = E ∧ x = y then 1 else 0) = if Q = E then 1 else 0 := by
    by_cases hq : Q = E <;> simp [hq]
  rw [hZ, hE] at e1
  omega

/-- A leg keeps the local invariant, given the capacity of `Z`'s ports. -/
theorem pLegF_linv {G : PG k q} (hL : PLInv L s σ' σ0 F0 G) {Z : Sq k}
    (hEZ : G.σ.blank ≠ Z) (hal : G.σ.blank.1 = Z.1 ∨ G.σ.blank.2 = Z.2) (hf : 1 ≤ pfr G Z)
    (hcap : (∑ z, G.stk Z z) + 1 < psz σ0 Z G.σ.bp) :
    PLInv L s σ' σ0 F0 (pLegF L s σ' G Z) := by
  have hy := pickFreeP_spec G Z hf
  set y := pickFreeP G Z
  have hmore : G.stock Z (dport L Z y) y < G.σ.cnt Z y := by
    have h1 := hL.roles_le Z y
    have h2 : G.stock Z (dport L Z y) y ≤ G.stk Z y :=
      Finset.single_le_sum (f := fun pt => G.stock Z pt y) (fun _ _ => Nat.zero_le _) (mem_univ _)
    omega
  obtain ⟨p, hp⟩ := surplus_part L hL Z y hmore
  obtain ⟨z, hz⟩ := surplus_port L hL Z G.σ.bp hcap
  exact pLeg_linv L hL hEZ hal hy (pickAny_spec L G Z y ⟨p, hp⟩)
    (fun _ => pickSur_spec L G Z G.σ.bp ⟨z, hz⟩)

end legs

theorem corner_facts' {E Z : Sq k} (c : ¬ (E.1 = Z.1 ∨ E.2 = Z.2)) :
    E ≠ (Z.1, E.2) ∧ (Z.1, E.2) ≠ Z ∧ (E.1 = (Z.1, E.2).1 ∨ E.2 = (Z.1, E.2).2) ∧
      ((Z.1, E.2).1 = Z.1 ∨ (Z.1, E.2).2 = Z.2) ∧
      sqDist E (Z.1, E.2) + sqDist (Z.1, E.2) Z = sqDist E Z ∧ Z ≠ E :=
  corner_facts c

/-- Eight times the cost of a relocation, per unit of relocation weight: the distance part
of a leg costs `3s` per unit, the fixed part at most one eighth per unit (a relocation has
weight at least `16` per leg). -/
def legA (k s σ' : ℕ) : ℕ := 24 * s + (6 * σ' + 600 * k + 3053)

theorem legK_eq (k s σ' d : ℕ) :
    legK k s σ' d = 21 * d * s + 10 * s + (12 * σ' + 1200 * k + 6105) := by
  unfold legK; ring

section reloc

variable {s σ' : ℕ} {σ0 : PState k q} {F0 : ℕ}

theorem pReloc_same (G : PG k q) (E Z : Sq k) : LSame G (pReloc L s σ' G E Z) ∧
    (pReloc L s σ' G E Z).σ.blank = Z ∧ (pReloc L s σ' G E Z).σ.bp = G.σ.bp := by
  unfold pReloc
  split_ifs
  · exact ⟨pLegF_same L G Z, rfl, rfl⟩
  · exact ⟨(pLegF_same L G _).trans (pLegF_same L _ Z), rfl, rfl⟩

theorem pReloc_linv {G : PG k q} (hL : PLInv L s σ' σ0 F0 G) {E Z : Sq k} (hb : G.σ.blank = E)
    (hEZ : E ≠ Z) (hf : ∀ Q, Q ≠ E → 1 ≤ pfr G Q)
    (hcap : ∀ Q pt, (∑ z, G.stk Q z) + 1 < psz σ0 Q pt) :
    PLInv L s σ' σ0 F0 (pReloc L s σ' G E Z) ∧ (∀ Q, pfr (pReloc L s σ' G E Z) Q +
      (if Q = Z then 1 else 0) = pfr G Q + (if Q = E then 1 else 0)) ∧
      8 * (pReloc L s σ' G E Z).jc ≤ 8 * G.jc + legA k s σ' * relocWeight (HEvent.reloc E Z) := by
  unfold pReloc
  split_ifs with c
  · rw [show relocWeight (HEvent.reloc E Z) = 16 + 7 * sqDist E Z by simp [relocWeight, c]]
    subst hb
    refine ⟨pLegF_linv L hL hEZ c (hf Z (Ne.symm hEZ)) (hcap Z _),
      pLegF_fr L G Z hEZ (hf Z (Ne.symm hEZ)), ?_⟩
    rw [pLegF_jc, legK_eq]
    unfold legA
    generalize sqDist G.σ.blank Z = d
    nlinarith
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := corner_facts' c
    set C : Sq k := (Z.1, E.2)
    rw [show relocWeight (HEvent.reloc E Z) = 32 + 7 * sqDist E Z by simp [relocWeight, c]]
    subst hb
    have hfC := hf C (Ne.symm h1)
    have L1 := pLegF_linv L hL h1 h3 hfC (hcap C _)
    have f1 := pLegF_fr L (s := s) (σ' := σ') G C h1 hfC
    have hZ1 : 1 ≤ pfr (pLegF L s σ' G C) Z := by
      have := f1 Z; have := hf Z h6
      simp only [if_neg (Ne.symm h2), if_neg h6] at *; omega
    have hs1 := pLegF_same L (s := s) (σ' := σ') G C
    obtain ⟨b1, bp1⟩ := pLegF_blank L (s := s) (σ' := σ') G C
    have hcap1 : (∑ z, (pLegF L s σ' G C).stk Z z) + 1 < psz σ0 Z (pLegF L s σ' G C).σ.bp := by
      rw [hs1.stk, bp1]; exact hcap Z _
    refine ⟨pLegF_linv L L1 (by rw [b1]; exact h2) (by rw [b1]; exact h4) hZ1 hcap1, ?_, ?_⟩
    · intro Q
      have g1 := f1 Q
      have g2 := pLegF_fr L (s := s) (σ' := σ') (pLegF L s σ' G C) Z (by rw [b1]; exact h2) hZ1 Q
      rw [b1] at g2
      omega
    · rw [pLegF_jc, pLegF_jc, b1, legK_eq, legK_eq, ← h5]
      unfold legA
      generalize sqDist G.σ.blank C = d1
      generalize sqDist C Z = d2
      nlinarith

end reloc

end SlidingPuzzle.Port
