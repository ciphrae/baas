import SlidingPuzzle.Port.Choice
import SlidingPuzzle.Tree.RunServe

/-! # Serving one demand along its route, with ports

As `Tree.RunServe`. Before the stage of `u` the blank is aligned to the port of its
hop at `nxt u x` (`pAlign`, at most two transfers), then `u` inserts in the mode
chosen by `pMode`. -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle.Hub (Sq)
open SlidingPuzzle.Tree

variable {k q : ℕ} (L : LaneSys k q)

/-- Tiles tagged `x` in the lanes landing at `v`. -/
def pFcnt (s : ℕ) (G : PG k q) (v x : Sq k) : ℕ :=
  plcnt L s G (fun l => land l = v) (fun g => gtg g = some x)

/-- Dirty tiles tagged `x` in the lanes landing at `v`. -/
def pDpos (s : ℕ) (G : PG k q) (v x : Sq k) : ℕ :=
  plcnt L s G (fun l => land l = v) (fun g => gdt g = some x)

/-- The stock identity, with a pending gateway `p` for class `D`. -/
def PIdent (s : ℕ) (G : PG k q) (D : Sq k) (p : Option (Sq k)) : Prop :=
  ∀ v x, v ≠ x → G.stk v x + pFcnt L s G v x + G.dA v x +
    (if p = some v ∧ x = D then 1 else 0) = G.B v x

/-- Dirty tiles in flight or arrived come from placeholders of the previous squares. -/
def PDirtyInv (s : ℕ) (G : PG k q) : Prop :=
  ∀ v x, G.dA v x + pDpos L s G v x = ∑ u ∈ univ.filter (fun u => u ≠ x ∧ L.nxt u x = v), G.B u x

/-- Placeholders of `v` for `x` exceed its dirty arrivals by at most the in-flight bound plus one. -/
def PBInv (G : PG k q) (Nv : Sq k → Sq k → ℕ) : Prop :=
  ∀ v x, G.B v x ≤ G.dA v x + Nv v x + 1 ∧ (G.B v x ≠ 0 → L.Act v x)

/-- The stock a square can hold. -/
noncomputable def stkCap (Nv : Sq k → Sq k → ℕ) (Q : Sq k) : ℕ := ∑ x, (Nv Q x + if L.Act Q x then 1 else 0)

theorem stk_le_B {s : ℕ} {G : PG k q} {D : Sq k} {p : Option (Sq k)} (hI : PIdent L s G D p)
    {v x : Sq k} (h : v ≠ x) : G.stk v x ≤ G.B v x := by
  have := hI v x h; omega

/-- The stock of a square is within its capacity. -/
theorem stk_sum_le {s σ' : ℕ} {σ0 : PState k q} {F0 : ℕ} {G : PG k q}
    (hL : PLInv L s σ' σ0 F0 G) {D : Sq k} {p : Option (Sq k)} (hI : PIdent L s G D p)
    {Nv : Sq k → Sq k → ℕ} (hB : PBInv L G Nv) (Q : Sq k) :
    ∑ z, G.stk Q z ≤ stkCap L Nv Q := by
  unfold stkCap
  refine sum_le_sum fun x _ => ?_
  by_cases hQx : Q = x
  · subst hQx
    have : G.stk Q Q = 0 := by
      unfold PG.stk; exact Finset.sum_eq_zero fun pt _ => hL.stock_diag Q pt
    omega
  · have h1 := hI Q x hQx
    obtain ⟨h2, h3⟩ := hB Q x
    split_ifs with ha
    · omega
    · have : G.B Q x = 0 := by by_contra h0; exact ha (h3 h0)
      omega

/-! ## Choices of a gateway -/

open Classical in
/-- Some free tile of `u`, if there is one. -/
noncomputable def pickFreeP (G : PG k q) (u : Sq k) : Sq k :=
  if h : ∃ y, 1 ≤ G.free u y then Classical.choose h else u

theorem pickFreeP_spec (G : PG k q) (u : Sq k) (h : 1 ≤ ∑ y, G.free u y) :
    1 ≤ G.free u (pickFreeP G u) := by
  have hex : ∃ y, 1 ≤ G.free u y := by
    by_contra hne
    push Not at hne
    have : ∑ y, G.free u y = 0 := Finset.sum_eq_zero fun y _ => by have := hne y; omega
    omega
  unfold pickFreeP
  rw [dif_pos hex]
  exact Classical.choose_spec hex

open Classical in
/-- The port of the stock used: that of the hop if it holds some. -/
noncomputable def pickSp (G : PG k q) (u x : Sq k) : Pt :=
  if 1 ≤ G.stock u (dport L u x) x then dport L u x
  else if h : ∃ pt, 1 ≤ G.stock u pt x then Classical.choose h else dport L u x

theorem pickSp_spec (G : PG k q) (u x : Sq k) (h : 1 ≤ G.stk u x) :
    1 ≤ G.stock u (pickSp L G u x) x := by
  unfold pickSp
  split_ifs with h1 h2
  · exact h1
  · exact Classical.choose_spec h2
  · exfalso
    push Not at h2
    have : G.stk u x = 0 := Finset.sum_eq_zero fun pt _ => by have := h2 pt; omega
    omega

/-- A transfer to port `pt`, with a surplus class of `pt`. -/
noncomputable def pX (s : ℕ) (G : PG k q) (pt : Pt) : PG k q :=
  pXfer s G pt (pickSur L G G.σ.blank pt)

/-- Aligns the blank to port `pt` of its square. -/
noncomputable def pAlign (s : ℕ) (G : PG k q) (pt : Pt) : PG k q :=
  if G.σ.bp = pt then G
  else if G.σ.bp = .tl ∨ pt = .tl then pX L s G pt
  else pX L s (pX L s G .tl) pt

/-- One stage of `u` toward `x` in role `kd`, class `y`, stock port `sp`, aligned first. -/
noncomputable def pStep (s τ : ℕ) (G : PG k q) (u x : Sq k) (kd : Kind) (y : Sq k) (sp : Pt) :
    PG k q :=
  let G1 := pAlign L s G (dport L u x)
  pStage L s τ G1 u x kd y (pMode L G1 u x kd y sp) sp

/-- One gateway: a stock tile if there is one, else a placeholder. -/
noncomputable def pGate (s τ : ℕ) (G : PG k q) (u D : Sq k) : PG k q :=
  if 1 ≤ G.stk u D then pStep L s τ G u D .stk D (pickSp L G u D)
  else pStep L s τ G u D .plh (pickFreeP G u) .tl

/-- The gateways of the route from `w` to `D`, the last one first. -/
noncomputable def pGates (s τ : ℕ) (G : PG k q) (w D : Sq k) : PG k q :=
  (L.nodes w D).foldr (fun u G' => pGate L s τ G' u D) G

/-- A served demand: the gateways, then the source. -/
noncomputable def pServe (s τ : ℕ) (G : PG k q) (S D : Sq k) : PG k q :=
  pStep L s τ (pGates L s τ G (L.nxt S D) D) S D .sch D .tl

theorem pGates_self (s τ : ℕ) (G : PG k q) (D : Sq k) : pGates L s τ G D D = G := by
  unfold pGates; rw [nodes_self]; rfl

theorem pGates_cons (s τ : ℕ) (G : PG k q) {w D : Sq k} (h : w ≠ D) :
    pGates L s τ G w D = pGate L s τ (pGates L s τ G (L.nxt w D) D) w D := by
  unfold pGates; rw [nodes_cons L h]; rfl

/-! ## Alignment -/

section align
variable {s σ' : ℕ} {σ0 : PState k q} {F0 : ℕ}

/-- What a sequence of transfers keeps. -/
structure XSame (G G' : PG k q) : Prop where
  ins : G'.ins = G.ins
  sched : G'.sched = G.sched
  stock : G'.stock = G.stock
  free : G'.free = G.free
  B : G'.B = G.B
  dA : G'.dA = G.dA
  served : G'.served = G.served
  sent : G'.sent = G.sent
  nh : G'.nh = G.nh
  ni : G'.ni = G.ni
  nt : G'.nt = G.nt
  nis : G'.nis = G.nis
  jc : G'.jc = G.jc
  wt : G'.wt = G.wt
  blank : G'.σ.blank = G.σ.blank
  lane : G'.σ.lane = G.σ.lane

theorem XSame.refl (G : PG k q) : XSame G G :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem XSame.pX (G : PG k q) (pt : Pt) : XSame G (pX L s G pt) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem XSame.trans {G G' G'' : PG k q} (h : XSame G G') (h' : XSame G' G'') : XSame G G'' :=
  ⟨h'.ins.trans h.ins, h'.sched.trans h.sched, h'.stock.trans h.stock, h'.free.trans h.free,
    h'.B.trans h.B, h'.dA.trans h.dA, h'.served.trans h.served, h'.sent.trans h.sent,
    h'.nh.trans h.nh, h'.ni.trans h.ni, h'.nt.trans h.nt, h'.nis.trans h.nis, h'.jc.trans h.jc,
    h'.wt.trans h.wt, h'.blank.trans h.blank, h'.lane.trans h.lane⟩

theorem XSame.stk {G G' : PG k q} (h : XSame G G') : G'.stk = G.stk := by
  funext Q z; unfold PG.stk; rw [h.stock]

theorem XSame.gh {G G' : PG k q} (h : XSame G G') : pgh k s G' = pgh k s G := by
  unfold SlidingPuzzle.Port.pgh; rw [h.ins]

theorem XSame.lc {G G' : PG k q} (h : XSame G G') (V : Ln k q → Prop) [DecidablePred V]
    (P : Option (GCls k × ℕ) → Prop) [DecidablePred P] : plcnt L s G' V P = plcnt L s G V P := by
  unfold SlidingPuzzle.Port.plcnt; rw [h.gh]

theorem XSame.ident {G G' : PG k q} (h : XSame G G') {D : Sq k} {p : Option (Sq k)}
    (hI : PIdent L s G D p) : PIdent L s G' D p := by
  intro v x hvx
  have := hI v x hvx
  unfold pFcnt at this ⊢
  rw [h.stk, h.lc, h.dA, h.B]; exact this

theorem XSame.dirty {G G' : PG k q} (h : XSame G G') (hD : PDirtyInv L s G) : PDirtyInv L s G' := by
  intro v x
  have := hD v x
  unfold pDpos at this ⊢
  rw [h.lc, h.dA, h.B]; exact this

theorem XSame.binv {G G' : PG k q} (h : XSame G G') {Nv : Sq k → Sq k → ℕ} (hB : PBInv L G Nv) :
    PBInv L G' Nv := by
  intro v x; rw [h.B, h.dA]; exact hB v x

theorem pX_linv {G : PG k q} (hL : PLInv L s σ' σ0 F0 G) {pt : Pt}
    (hne : G.σ.bp ≠ pt) (htl : G.σ.bp = .tl ∨ pt = .tl)
    (hcap : (∑ z, G.stk G.σ.blank z) + 1 < psz σ0 G.σ.blank pt) :
    PLInv L s σ' σ0 F0 (pX L s G pt) ∧ (pX L s G pt).σ.bp = pt ∧
      (pX L s G pt).nx = G.nx + 1 := by
  obtain ⟨c, hc⟩ := surplus_port L hL G.σ.blank pt hcap
  exact ⟨pXfer_linv L hL hne htl (pickSur_spec L G _ pt ⟨c, hc⟩), rfl, rfl⟩

/-- Alignment keeps the local invariant and costs at most two transfers. -/
theorem pAlign_linv {G : PG k q} (hL : PLInv L s σ' σ0 F0 G) (pt : Pt)
    (hcap : ∀ pt', (∑ z, G.stk G.σ.blank z) + 1 < psz σ0 G.σ.blank pt') :
    PLInv L s σ' σ0 F0 (pAlign L s G pt) ∧ (pAlign L s G pt).σ.bp = pt ∧
      XSame G (pAlign L s G pt) ∧
      (pAlign L s G pt).nx ≤ G.nx + (if G.σ.bp = pt then 0 else 2) := by
  unfold pAlign
  split_ifs with h1 h2
  · exact ⟨hL, h1, XSame.refl G, by simp⟩
  · obtain ⟨a, b, c⟩ := pX_linv L hL h1 h2 (hcap pt)
    exact ⟨a, b, XSame.pX L G pt, by omega⟩
  · push Not at h2
    obtain ⟨a1, b1, c1⟩ := pX_linv L hL h2.1 (Or.inr rfl) (hcap .tl)
    have hs := XSame.pX L (s := s) G .tl
    have hcap' : (∑ z, (pX L s G .tl).stk (pX L s G .tl).σ.blank z) + 1 <
        psz σ0 (pX L s G .tl).σ.blank pt := by
      rw [hs.stk, hs.blank]; exact hcap pt
    obtain ⟨a2, b2, c2⟩ := pX_linv L a1 (by rw [b1]; exact Ne.symm h2.2) (Or.inl b1) hcap'
    exact ⟨a2, b2, hs.trans (XSame.pX L _ pt), by omega⟩

end align

end SlidingPuzzle.Port
