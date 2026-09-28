import SlidingPuzzle.Tree.RouteList

/-! # The ghost state of the abstract run

`GS` carries the `IState`, the resolved operations, the insertion records (the
ghost lanes are `ghostRun` of them; a record's class is the tag and whether the
inserted tile is clean), the roles `sched`, `stock` (clean tiles of a tag held
by an intermediate square), `free`, and the counters `B` (placeholders emitted,
by square and tag), `dA` (dirty arrivals), `served`, `sent`, `nh` (hops), `jc`
(cost of the jumps) and `wt` (relocation weight).

`gStage` is one hop of a route: square `u` inserts a tile of actual class `y`
tagged `x` into the lane of its next hop toward `x`; the head of that lane drops
into the landing square: a clean head becomes stock (or a home tile at its
final square), any other head becomes free. `gJump` moves a free tile. -/
namespace SlidingPuzzle.Tree
open Finset
open SlidingPuzzle.Hub (Sq shiftIn incCnt decCnt card_filter_shiftIn sum_update_add)

variable {k q : ℕ}

/-- Ghost class of an inserted tile: its tag and whether it is clean. -/
abbrev GCls (k : ℕ) := Sq k × Bool

/-- Ghost insertion records. -/
abbrev GRec (k q : ℕ) := GroupedPipe.InsRec (Ln k q) (GCls k)

/-- Kind of an inserted tile. -/
inductive Kind where
  | sch
  | stk
  | plh
  deriving DecidableEq

structure GS (k q : ℕ) where
  σ : IState k q
  evs : List (REvent k q)
  ins : List (GRec k q)
  sched : Sq k → Sq k → ℕ
  stock : Sq k → Sq k → ℕ
  free : Sq k → Sq k → ℕ
  B : Sq k → Sq k → ℕ
  dA : Sq k → Sq k → ℕ
  served : Sq k → ℕ
  sent : Sq k → ℕ
  nh : ℕ
  jc : ℕ
  wt : ℕ

/-- The ghost lanes. -/
def gh (k s : ℕ) (G : GS k q) : Ln k q → ℕ → Option (GCls k × ℕ) :=
  GroupedPipe.ghostRun (lstep s) (loff k s) (fun _ _ => none) G.ins

/-- The tag of a clean ghost entry. -/
def gcl : Option (GCls k × ℕ) → Option (Sq k)
  | some ((x, true), _) => some x
  | _ => none

/-- The tag of a dirty ghost entry. -/
def gdt : Option (GCls k × ℕ) → Option (Sq k)
  | some ((x, false), _) => some x
  | _ => none

/-- The tag of a ghost entry. -/
def gtg (g : Option (GCls k × ℕ)) : Option (Sq k) := g.map fun a => a.1.1

variable (L : LaneSys k q)

/-- One hop of a route: `u` inserts a class-`y` tile tagged `x`. -/
def gStage (s τ : ℕ) (G : GS k q) (u x : Sq k) (kd : Kind) (y : Sq k) : GS k q :=
  let l := (L.stage u x).1
  let J := (L.stage u x).2
  let v := land l
  let hd := G.σ.lane l 0
  let g := gh k s G l 0
  { σ := G.σ.step s (hopEv l J y)
    evs := G.evs ++ [hopEv l J y]
    ins := G.ins ++ [⟨τ, l, LaneSys.pdist l.2.t.val J.val, (x, decide (kd ≠ .plh))⟩]
    sched := fun Q z => G.sched Q z - (if kd = .sch ∧ Q = u ∧ z = y then 1 else 0)
    stock := fun Q z => G.stock Q z - (if kd = .stk ∧ Q = u ∧ z = y then 1 else 0) +
      (if gcl g = some z ∧ Q = v ∧ v ≠ z then 1 else 0)
    free := fun Q z => G.free Q z - (if kd = .plh ∧ Q = u ∧ z = y then 1 else 0) +
      (if gcl g = none ∧ Q = v ∧ z = hd then 1 else 0)
    B := fun Q z => G.B Q z + (if kd = .plh ∧ Q = u ∧ z = x then 1 else 0)
    dA := fun Q z => G.dA Q z + (if gdt g = some z ∧ Q = v then 1 else 0)
    served := G.served
    sent := G.sent
    nh := G.nh + 1
    jc := G.jc
    wt := G.wt }

/-- A jump moving a free class-`y` tile of `Z` to `E`. -/
def gJump (s : ℕ) (G : GS k q) (E Z y : Sq k) : GS k q :=
  { G with
    σ := G.σ.step s (.jump E Z y)
    evs := G.evs ++ [.jump E Z y]
    free := fun Q z => G.free Q z - (if Q = Z ∧ z = y then 1 else 0) +
      (if Q = E ∧ z = y then 1 else 0)
    jc := G.jc + G.σ.cost s (.jump E Z y) }

/-! ## Counting ghost positions of lanes -/

/-- Ghost positions of the lanes selected by `V` satisfying `P`. -/
def lcnt (s : ℕ) (G : GS k q) (V : Ln k q → Prop) [DecidablePred V]
    (P : Option (GCls k × ℕ) → Prop) [DecidablePred P] : ℕ :=
  ∑ l : Ln k q, if V l then ((range (llen L s l)).filter fun r => P (gh k s G l r)).card else 0

section stage

variable (s τ : ℕ)

theorem gh_gStage (G : GS k q) (u x : Sq k) (kd : Kind) (y : Sq k) :
    gh k s (gStage L s τ G u x kd y) = Function.update (gh k s G) (L.stage u x).1
      (shiftIn (gh k s G (L.stage u x).1) (lpos k s (L.stage u x).1 (L.stage u x).2)
        (some ((x, decide (kd ≠ .plh)), LaneSys.pdist (L.stage u x).1.2.t.val
          (L.stage u x).2.val))) := by
  simp only [gh, gStage, GroupedPipe.ghostRun, List.foldl_append, List.foldl_cons,
    List.foldl_nil, GroupedPipe.ghostStep, GroupedPipe.insPos]
  rw [lpos_eq]

theorem lcnt_gStage {n : ℕ} [NeZero n] (td : TDims n k s q) (G : GS k q) {u x : Sq k}
    (hux : u ≠ x) (kd : Kind) (y : Sq k)
    (V : Ln k q → Prop) [DecidablePred V] (P : Option (GCls k × ℕ) → Prop) [DecidablePred P] :
    lcnt L s (gStage L s τ G u x kd y) V P +
        (if V (L.stage u x).1 ∧ P (gh k s G (L.stage u x).1 0) then 1 else 0) =
      lcnt L s G V P + (if V (L.stage u x).1 ∧ P (some ((x, decide (kd ≠ .plh)),
        LaneSys.pdist (L.stage u x).1.2.t.val (L.stage u x).2.val)) then 1 else 0) := by
  unfold lcnt
  rw [gh_gStage]
  set l0 := (L.stage u x).1
  have hp := lpos_lt L s td l0 (L.stage u x).2 (stage_in hux)
  have hsum := sum_update_add
    (fun (l : Ln k q) (f : ℕ → Option (GCls k × ℕ)) =>
      if V l then ((range (llen L s l)).filter fun r => P (f r)).card else 0)
    (gh k s G) l0 (shiftIn (gh k s G l0) (lpos k s l0 (L.stage u x).2)
      (some ((x, decide (kd ≠ .plh)), LaneSys.pdist l0.2.t.val (L.stage u x).2.val)))
  have hc := card_filter_shiftIn P (gh k s G l0) hp
    (some ((x, decide (kd ≠ .plh)), LaneSys.pdist l0.2.t.val (L.stage u x).2.val))
  by_cases hV : V l0
  · simp only [hV, if_true, true_and] at hsum ⊢
    omega
  · simp only [hV, if_false, false_and] at hsum ⊢
    omega

end stage

end SlidingPuzzle.Tree

namespace SlidingPuzzle.Tree
open Finset
open SlidingPuzzle.Hub (Sq shiftIn incCnt decCnt incCnt_apply decCnt_apply)

variable {k q : ℕ} (L : LaneSys k q)

/-- Lane positions without a ghost record (initial lane contents). -/
def untagged (s : ℕ) (G : GS k q) : ℕ := lcnt L s G (fun _ => True) (fun g => g = none)

/-- The local invariant, preserved by every ghost operation. -/
structure LInv (s : ℕ) (σ0 : IState k q) (F0 : ℕ) (G : GS k q) : Prop where
  roles_le : ∀ Q y, G.sched Q y + G.stock Q y + G.free Q y ≤ G.σ.cnt Q y
  roles_ge : ∀ Q y, y ≠ Q → G.σ.cnt Q y ≤ G.sched Q y + G.stock Q y + G.free Q y
  stock_diag : ∀ Q, G.stock Q Q = 0
  ghost_clean : ∀ l r x d, gh k s G l r = some ((x, true), d) → G.σ.lane l r = x
  ghost_len : ∀ l r, gh k s G l r ≠ none → r < llen L s l
  run_eq : G.σ = σ0.run s G.evs
  valid : σ0.Valid L s G.evs
  cost : σ0.totalCost s G.evs + G.σ.pot L s ≤
    σ0.pot L s + hopK k q s * G.nh + (k * s) * (∑ Q, ∑ x, G.B Q x) + G.jc
  free_tot : (∑ Q, ∑ y, G.free Q y) + untagged L s G + (∑ Q, ∑ x, G.B Q x) =
    F0 + ∑ Q, ∑ x, G.dA Q x

/-- `LInv` only depends on the fields it mentions. -/
theorem LInv.congr {s : ℕ} {σ0 : IState k q} {F0 : ℕ} {G G' : GS k q} (h : LInv L s σ0 F0 G)
    (e1 : G'.σ = G.σ) (e2 : G'.evs = G.evs) (e3 : G'.ins = G.ins) (e4 : G'.sched = G.sched)
    (e5 : G'.stock = G.stock) (e6 : G'.free = G.free) (e7 : G'.B = G.B) (e8 : G'.dA = G.dA)
    (e9 : G'.nh = G.nh) (e10 : G'.jc = G.jc) : LInv L s σ0 F0 G' := by
  have e11 : gh k s G' = gh k s G := by simp only [gh, e3]
  have e12 : untagged L s G' = untagged L s G := by unfold untagged lcnt; rw [e11]
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [e1, e2, e4, e5, e6, e7, e8, e9, e10, e11, e12] <;> assumption

theorem blen_le (H : LaneI k q) : blen L H ≤ k := by
  have := L.right_lt H.o H.t
  have := L.left_le H.o H.t
  have := H.t.isLt
  unfold blen; cases H.side <;> omega

theorem llen_le (s : ℕ) (l : Ln k q) : llen L s l ≤ k * s := by
  unfold llen colLen rowLen
  split_ifs
  · exact (Nat.mul_le_mul_right _ (blen_le L _)).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  · exact Nat.mul_le_mul_right _ (blen_le L _)

theorem nxt_ne {u x : Sq k} (h : u ≠ x) : L.nxt u x ≠ u := by
  intro e
  have := srank_nxt (L := L) h
  rw [e] at this; omega

theorem land_stage (u x : Sq k) : land (L.stage u x).1 = L.nxt u x := rfl

section pres

variable {s : ℕ} {σ0 : IState k q} {F0 : ℕ}

theorem pre_append {G : GS k q} (hL : LInv L s σ0 F0 G) {e : REvent k q} (he : G.σ.Pre L e) :
    G.σ.step s e = σ0.run s (G.evs ++ [e]) ∧ σ0.Valid L s (G.evs ++ [e]) := by
  rw [IState.run_append, ← hL.run_eq, IState.valid_append, ← hL.run_eq]
  exact ⟨rfl, hL.valid, (IState.valid_singleton L s _ _).2 he⟩

theorem cost_append {G : GS k q} (hL : LInv L s σ0 F0 G) (e : REvent k q) :
    σ0.totalCost s (G.evs ++ [e]) = σ0.totalCost s G.evs + G.σ.cost s e := by
  rw [IState.totalCost_append, ← hL.run_eq, IState.totalCost_singleton]

/-- The role taken from the inserting square is available. -/
def RoleOK (G : GS k q) (u x : Sq k) : Kind → Sq k → Prop
  | .sch, y => y = x ∧ 1 ≤ G.sched u y
  | .stk, y => y = x ∧ 1 ≤ G.stock u y
  | .plh, y => 1 ≤ G.free u y

end pres

end SlidingPuzzle.Tree
