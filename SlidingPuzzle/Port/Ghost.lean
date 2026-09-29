import SlidingPuzzle.Port.StepFacts

/-! # The ghost state of the port run

As `Tree.GS`, with a `PState`, stock recorded by the port it arrived through, and
counters of importing hops (`ni`) and transfers (`nx`).

A stage `gStage u x kd y m sp` is one hop of a route toward `x`, inserted by `u` in
mode `m`; if the inserted tile is stock, one unit of stock of port `sp` is used.
`gXfer` moves the blank to another port of its square, `gLeg` relocates it,
carrying a free tile back.

The demand `dem Q p z` is the stock of class `z` that part `p` of `Q` must keep:
the stock that arrived through the port of the next hop toward `z`. A tile only
leaves a part where its class exceeds the demand (`stockIn` is kept). -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle.Hub (Sq sqDist shiftIn incCnt decCnt incCnt_apply decCnt_apply
  card_filter_shiftIn sum_update_add)
open SlidingPuzzle.Tree

variable {k q : ℕ}

/-- One for importing modes. -/
def Mode.ind : Mode k → ℕ
  | .cheap => 0
  | .imp _ _ => 1

structure PG (k q : ℕ) where
  σ : PState k q
  evs : List (PEvent k q)
  ins : List (GRec k q)
  sched : Sq k → Sq k → ℕ
  stock : Sq k → Pt → Sq k → ℕ
  free : Sq k → Sq k → ℕ
  B : Sq k → Sq k → ℕ
  dA : Sq k → Sq k → ℕ
  served : Sq k → ℕ
  sent : Sq k → ℕ
  nh : ℕ
  ni : ℕ
  nx : ℕ
  nt : ℕ
  nis : ℕ
  ncr : ℕ
  jc : ℕ
  wt : ℕ

/-- Stock of `Q` for class `x`, over all ports. -/
def PG.stk (G : PG k q) (Q x : Sq k) : ℕ := ∑ pt, G.stock Q pt x

/-- The ghost lanes. -/
def pgh (k s : ℕ) (G : PG k q) : Ln k q → ℕ → Option (GCls k × ℕ) :=
  GroupedPipe.ghostRun (lstep s) (loffP k s) (fun _ _ => none) G.ins

variable (L : LaneSys k q)

/-- The port of the next hop of `x` from `u`. -/
def dport (u x : Sq k) : Pt := lport (L.stage u x).1

/-- A clean tile tagged `x` on lane `l` lands at a turn: its next hop leaves by another port. -/
def turning (l : Ln k q) (x : Sq k) : Prop := land l ≠ x ∧ lport l ≠ dport L (land l) x

instance (l : Ln k q) (x : Sq k) : Decidable (turning L l x) := by
  unfold turning; infer_instance

/-- Stock held outside the port of its next hop. -/
def NS (G : PG k q) : ℕ :=
  ∑ u, ∑ x, ∑ pt, if pt = dport L u x then 0 else G.stock u pt x

/-- Stock of part `p` of `Q` that must stay there. -/
def dem (G : PG k q) (Q : Sq k) : Part → Sq k → ℕ
  | none, _ => 0
  | some pt, z => if z ≠ Q ∧ dport L Q z = pt then G.stock Q pt z else 0

/-- One hop of a route: `u` inserts a class-`y` tile tagged `x` in mode `m`. -/
def pStage (s τ : ℕ) (G : PG k q) (u x : Sq k) (kd : Kind) (y : Sq k) (m : Mode k) (sp : Pt) :
    PG k q :=
  let l := (L.stage u x).1
  let J := (L.stage u x).2
  let v := land l
  let hd := G.σ.lane l 0
  let g := pgh k s G l 0
  { σ := G.σ.step s (.hop l J y m)
    evs := G.evs ++ [.hop l J y m]
    ins := G.ins ++ [⟨τ, l, LaneSys.pdist l.2.t.val J.val, (x, decide (kd ≠ .plh))⟩]
    sched := fun Q z => G.sched Q z - (if kd = .sch ∧ Q = u ∧ z = y then 1 else 0)
    stock := fun Q pt z => G.stock Q pt z - (if kd = .stk ∧ Q = u ∧ pt = sp ∧ z = y then 1 else 0) +
      (if gcl g = some z ∧ Q = v ∧ v ≠ z ∧ pt = lport l then 1 else 0)
    free := fun Q z => G.free Q z - (if kd = .plh ∧ Q = u ∧ z = y then 1 else 0) +
      (if gcl g = none ∧ Q = v ∧ z = hd then 1 else 0)
    B := fun Q z => G.B Q z + (if kd = .plh ∧ Q = u ∧ z = x then 1 else 0)
    dA := fun Q z => G.dA Q z + (if gdt g = some z ∧ Q = v then 1 else 0)
    served := G.served
    sent := G.sent
    nh := G.nh + 1
    ni := G.ni + m.ind
    nx := G.nx
    nt := G.nt + (if kd ≠ .plh ∧ turning L (L.stage u x).1 x then 1 else 0)
    nis := G.nis + (if kd = .stk then m.ind else 0)
    ncr := G.ncr + LaneSys.pdist (L.stage u x).1.2.t.val (L.stage u x).2.val
    jc := G.jc
    wt := G.wt }

/-- A transfer of the blank to port `pt`, a class-`c` tile going the other way. -/
def pXfer (s : ℕ) (G : PG k q) (pt : Pt) (c : Sq k) : PG k q :=
  { G with
    σ := G.σ.step s (.xfer pt c)
    evs := G.evs ++ [.xfer pt c]
    nx := G.nx + 1 }

/-- A leg to `Z`, carrying a free class-`y` tile from part `p` of `Z`. -/
def pLeg (s σ' : ℕ) (G : PG k q) (Z y : Sq k) (p : Part) (z : Sq k) : PG k q :=
  { G with
    σ := G.σ.step s (.leg Z y p z)
    evs := G.evs ++ [.leg Z y p z]
    free := fun Q x => G.free Q x - (if Q = Z ∧ x = y then 1 else 0) +
      (if Q = G.σ.blank ∧ x = y then 1 else 0)
    jc := G.jc + G.σ.cost s σ' (.leg Z y p z) }

/-! ## Counting ghost positions of lanes -/

/-- Ghost positions of the lanes selected by `V` satisfying `P`. -/
def plcnt (s : ℕ) (G : PG k q) (V : Ln k q → Prop) [DecidablePred V]
    (P : Option (GCls k × ℕ) → Prop) [DecidablePred P] : ℕ :=
  ∑ l : Ln k q, if V l then ((range (llen L s l)).filter fun r => P (pgh k s G l r)).card else 0

/-- Lane positions without a ghost record. -/
def puntagged (s : ℕ) (G : PG k q) : ℕ := plcnt L s G (fun _ => True) (fun g => g = none)

section stage
variable (s τ : ℕ)

theorem pgh_pStage (G : PG k q) (u x : Sq k) (kd : Kind) (y : Sq k) (m : Mode k) (sp : Pt) :
    pgh k s (pStage L s τ G u x kd y m sp) = Function.update (pgh k s G) (L.stage u x).1
      (shiftIn (pgh k s G (L.stage u x).1) (lposP k s (L.stage u x).1 (L.stage u x).2)
        (some ((x, decide (kd ≠ .plh)), LaneSys.pdist (L.stage u x).1.2.t.val
          (L.stage u x).2.val))) := by
  simp only [pgh, pStage, GroupedPipe.ghostRun, List.foldl_append, List.foldl_cons,
    List.foldl_nil, GroupedPipe.ghostStep, GroupedPipe.insPos]
  rw [lposP_eq]

theorem plcnt_pStage {n : ℕ} [NeZero n] (td : TDims n k s q) (G : PG k q) {u x : Sq k}
    (hux : u ≠ x) (kd : Kind) (y : Sq k) (m : Mode k) (sp : Pt)
    (V : Ln k q → Prop) [DecidablePred V] (P : Option (GCls k × ℕ) → Prop) [DecidablePred P] :
    plcnt L s (pStage L s τ G u x kd y m sp) V P +
        (if V (L.stage u x).1 ∧ P (pgh k s G (L.stage u x).1 0) then 1 else 0) =
      plcnt L s G V P + (if V (L.stage u x).1 ∧ P (some ((x, decide (kd ≠ .plh)),
        LaneSys.pdist (L.stage u x).1.2.t.val (L.stage u x).2.val)) then 1 else 0) := by
  unfold plcnt
  rw [pgh_pStage]
  set l0 := (L.stage u x).1
  have hp := lposP_lt L td l0 (L.stage u x).2 (stage_in hux)
  have hsum := sum_update_add
    (fun (l : Ln k q) (f : ℕ → Option (GCls k × ℕ)) =>
      if V l then ((range (llen L s l)).filter fun r => P (f r)).card else 0)
    (pgh k s G) l0 (shiftIn (pgh k s G l0) (lposP k s l0 (L.stage u x).2)
      (some ((x, decide (kd ≠ .plh)), LaneSys.pdist l0.2.t.val (L.stage u x).2.val)))
  have hc := card_filter_shiftIn P (pgh k s G l0) hp
    (some ((x, decide (kd ≠ .plh)), LaneSys.pdist l0.2.t.val (L.stage u x).2.val))
  by_cases hV : V l0
  · simp only [hV, if_true, true_and] at hsum ⊢
    omega
  · simp only [hV, if_false, false_and] at hsum ⊢
    omega

end stage

/-! ## The local invariant -/

/-- The local invariant, preserved by every ghost operation. -/
structure PLInv (s σ' : ℕ) (σ0 : PState k q) (F0 : ℕ) (G : PG k q) : Prop where
  roles_le : ∀ Q y, G.sched Q y + G.stk Q y + G.free Q y ≤ G.σ.cnt Q y
  roles_ge : ∀ Q y, y ≠ Q → G.σ.cnt Q y ≤ G.sched Q y + G.stk Q y + G.free Q y
  stock_diag : ∀ Q pt, G.stock Q pt Q = 0
  ghost_clean : ∀ l r x d, pgh k s G l r = some ((x, true), d) → G.σ.lane l r = x
  ghost_len : ∀ l r, pgh k s G l r ≠ none → r < llen L s l
  pc_le : ∀ Q y, ∑ pt, G.σ.pc Q pt y ≤ G.σ.cnt Q y
  psum : ∀ Q pt, (∑ z, G.σ.pc Q pt z) + (if G.σ.blank = Q ∧ G.σ.bp = pt then 1 else 0) =
    (∑ z, σ0.pc Q pt z) + (if σ0.blank = Q ∧ σ0.bp = pt then 1 else 0)
  stockIn : ∀ u x, u ≠ x → G.stock u (dport L u x) x ≤ G.σ.pc u (dport L u x) x
  run_eq : G.σ = σ0.run s G.evs
  valid : σ0.Valid L s G.evs
  cost : σ0.totalCost s σ' G.evs + G.σ.pot L s ≤
    σ0.pot L s + hopKc k σ' * G.nh + 7 * (q + 2) * G.ncr + hopKi k s σ' * G.ni +
      xferK k s σ' * G.nx +
      (k * s) * (∑ Q, ∑ x, G.B Q x) + G.jc
  free_tot : (∑ Q, ∑ y, G.free Q y) + puntagged L s G + (∑ Q, ∑ x, G.B Q x) =
    F0 + ∑ Q, ∑ x, G.dA Q x
  turn : (∑ x, plcnt L s G (fun l => turning L l x) (fun g => gcl g = some x)) + NS L G + G.nis ≤
    G.nt

end SlidingPuzzle.Port
