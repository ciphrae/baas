import SlidingPuzzle.Tree.RunLocal

/-! # Serving one demand along its route

`hServe G S D` executes the route from `S` to `D` backwards: first the gateways
(`hGates`, from the last one to `nxt S D`), each inserting a clean stock tile
tagged `D` if it has one and otherwise a free tile as a placeholder, then the
source `S`, which inserts its scheduled tile.

Between serves the stock identity holds for every square `v` and tag `x ≠ v`:
`stock + inflight + dirty arrivals = placeholders`. Inside a serve the gateway
that has just inserted is *pending*: its incoming lane is refilled by the next
stage. -/
namespace SlidingPuzzle.Tree
open Finset
open SlidingPuzzle.Hub (Sq)

variable {k q : ℕ} (L : LaneSys k q)

/-- Tiles tagged `x` in the lanes landing at `v`. -/
def Fcnt (s : ℕ) (G : GS k q) (v x : Sq k) : ℕ :=
  lcnt L s G (fun l => land l = v) (fun g => gtg g = some x)

/-- Dirty tiles tagged `x` in the lanes landing at `v`. -/
def Dpos (s : ℕ) (G : GS k q) (v x : Sq k) : ℕ :=
  lcnt L s G (fun l => land l = v) (fun g => gdt g = some x)

/-- The stock identity, with a pending gateway `p` for class `D`. -/
def Ident (s : ℕ) (G : GS k q) (D : Sq k) (p : Option (Sq k)) : Prop :=
  ∀ v x, v ≠ x → G.stock v x + Fcnt L s G v x + G.dA v x +
    (if p = some v ∧ x = D then 1 else 0) = G.B v x

/-- Dirty tiles in flight or arrived come from placeholders of the previous
squares. -/
def DirtyInv (s : ℕ) (G : GS k q) : Prop :=
  ∀ v x, G.dA v x + Dpos L s G v x = ∑ u ∈ univ.filter (fun u => u ≠ x ∧ L.nxt u x = v), G.B u x

/-- `v` receives tiles tagged `x` from some square. -/
def LaneSys.Act (v x : Sq k) : Prop := ∃ u, u ≠ x ∧ L.nxt u x = v

open Classical in
noncomputable instance (v x : Sq k) : Decidable (L.Act v x) := inferInstance

/-- Placeholders of `v` for `x` exceed its dirty arrivals by at most the
in-flight bound plus one. -/
def BInv (G : GS k q) (Nv : Sq k → Sq k → ℕ) : Prop :=
  ∀ v x, G.B v x ≤ G.dA v x + Nv v x + 1 ∧ (G.B v x ≠ 0 → L.Act v x)

/-- Some free tile of `u`, if there is one. -/
noncomputable def pickFree (G : GS k q) (u : Sq k) : Sq k := by
  classical
  exact if h : ∃ y, 1 ≤ G.free u y then Classical.choose h else u

theorem pickFree_spec (G : GS k q) (u : Sq k) (h : 1 ≤ ∑ y, G.free u y) :
    1 ≤ G.free u (pickFree G u) := by
  classical
  have hex : ∃ y, 1 ≤ G.free u y := by
    by_contra hne
    push Not at hne
    have : ∑ y, G.free u y = 0 := Finset.sum_eq_zero fun y _ => by have := hne y; omega
    omega
  unfold pickFree
  rw [dif_pos hex]
  exact Classical.choose_spec hex

/-- One gateway: a stock tile if there is one, else a placeholder. -/
noncomputable def gGate (s τ : ℕ) (G : GS k q) (u D : Sq k) : GS k q :=
  if 1 ≤ G.stock u D then gStage L s τ G u D .stk D
  else gStage L s τ G u D .plh (pickFree G u)

/-- The gateways of the route from `w` to `D`, the last one first. -/
noncomputable def hGates (s τ : ℕ) (G : GS k q) (w D : Sq k) : GS k q :=
  (L.nodes w D).foldr (fun u G' => gGate L s τ G' u D) G

/-- A served demand: the gateways, then the source. -/
noncomputable def hServe (s τ : ℕ) (G : GS k q) (S D : Sq k) : GS k q :=
  gStage L s τ (hGates L s τ G (L.nxt S D) D) S D .sch D

theorem hGates_self (s τ : ℕ) (G : GS k q) (D : Sq k) : hGates L s τ G D D = G := by
  unfold hGates; rw [nodes_self]; rfl

theorem hGates_cons (s τ : ℕ) (G : GS k q) {w D : Sq k} (h : w ≠ D) :
    hGates L s τ G w D = gGate L s τ (hGates L s τ G (L.nxt w D) D) w D := by
  unfold hGates; rw [nodes_cons L h]; rfl

theorem gtg_split (g : Option (GCls k × ℕ)) (x : Sq k) :
    (if gtg g = some x then 1 else 0) =
      (if gcl g = some x then 1 else 0) + (if gdt g = some x then 1 else 0) := by
  rcases g with _ | ⟨⟨x', b⟩, d⟩
  · simp [gtg, gcl, gdt]
  · cases b <;> simp [gtg, gcl, gdt]

section fields
variable (s τ : ℕ) (G : GS k q) (u x : Sq k) (kd : Kind) (y Q z : Sq k)

theorem gStage_stock : (gStage L s τ G u x kd y).stock Q z = G.stock Q z -
    (if kd = .stk ∧ Q = u ∧ z = y then 1 else 0) +
    (if gcl (gh k s G (L.stage u x).1 0) = some z ∧ Q = L.nxt u x ∧ L.nxt u x ≠ z then 1 else 0) :=
  rfl

theorem gStage_dA : (gStage L s τ G u x kd y).dA Q z = G.dA Q z +
    (if gdt (gh k s G (L.stage u x).1 0) = some z ∧ Q = L.nxt u x then 1 else 0) := rfl

theorem gStage_B : (gStage L s τ G u x kd y).B Q z = G.B Q z +
    (if kd = .plh ∧ Q = u ∧ z = x then 1 else 0) := rfl

theorem gStage_free : (gStage L s τ G u x kd y).free Q z = G.free Q z -
    (if kd = .plh ∧ Q = u ∧ z = y then 1 else 0) +
    (if gcl (gh k s G (L.stage u x).1 0) = none ∧ Q = L.nxt u x ∧
      z = G.σ.lane (L.stage u x).1 0 then 1 else 0) := rfl

theorem gStage_sched : (gStage L s τ G u x kd y).sched Q z = G.sched Q z -
    (if kd = .sch ∧ Q = u ∧ z = y then 1 else 0) := rfl

end fields

/-- The pending gateway before the stage of `u`: the square it lands in. -/
def LaneSys.pendB (u x : Sq k) : Option (Sq k) := if L.nxt u x = x then none else some (L.nxt u x)

/-- The pending gateway after the stage of `u`. -/
def pendA (u : Sq k) (kd : Kind) : Option (Sq k) := if kd = .sch then none else some u

section stage

variable {n s : ℕ} [NeZero n] (td : TDims n k s q) {σ0 : IState k q} {F0 : ℕ} (τ : ℕ)

include td in
theorem gStage_Fcnt (G : GS k q) {u x : Sq k} (hux : u ≠ x) (kd : Kind) (y v' x' : Sq k) :
    Fcnt L s (gStage L s τ G u x kd y) v' x' +
        (if land (L.stage u x).1 = v' ∧ gtg (gh k s G (L.stage u x).1 0) = some x' then 1 else 0) =
      Fcnt L s G v' x' + (if land (L.stage u x).1 = v' ∧ x' = x then 1 else 0) := by
  unfold Fcnt
  have h := lcnt_gStage L s τ td G hux kd y (fun l => land l = v') (fun g => gtg g = some x')
  simp only [gtg, Option.map_some, Option.some.injEq] at h ⊢
  convert h using 3
  simp [eq_comm]

include td in
theorem gStage_Dpos (G : GS k q) {u x : Sq k} (hux : u ≠ x) (kd : Kind) (y v' x' : Sq k) :
    Dpos L s (gStage L s τ G u x kd y) v' x' +
        (if land (L.stage u x).1 = v' ∧ gdt (gh k s G (L.stage u x).1 0) = some x' then 1 else 0) =
      Dpos L s G v' x' + (if land (L.stage u x).1 = v' ∧ kd = .plh ∧ x' = x then 1 else 0) := by
  unfold Dpos
  have h := lcnt_gStage L s τ td G hux kd y (fun l => land l = v') (fun g => gdt g = some x')
  rw [h]
  congr 1
  cases kd <;> simp [gdt, eq_comm]

include td in
/-- The stock identity through one stage. -/
theorem gStage_ident {G : GS k q} (hL : LInv L s σ0 F0 G) {u x : Sq k} (hux : u ≠ x)
    {kd : Kind} {y : Sq k} (hr : RoleOK G u x kd y) (hI : Ident L s G x (L.pendB u x)) :
    Ident L s (gStage L s τ G u x kd y) x (pendA u kd) := by
  intro v' x' hvx
  have hF := gStage_Fcnt L td τ G hux kd y v' x'
  have hsplit := gtg_split (gh k s G (L.stage u x).1 0) x'
  have hI' := hI v' x' hvx
  have hvu : L.nxt u x ≠ u := nxt_ne L hux
  have hland : land (L.stage u x).1 = L.nxt u x := rfl
  rw [hland] at hF
  rw [gStage_stock, gStage_dA, gStage_B]
  -- the pending terms
  have hpend : (if pendA u kd = some v' ∧ x' = x then 1 else 0) +
      (if L.nxt u x = v' ∧ x' = x then 1 else 0) =
      (if L.pendB u x = some v' ∧ x' = x then 1 else 0) +
      (if kd = Kind.plh ∧ v' = u ∧ x' = x then 1 else 0) +
      (if kd = Kind.stk ∧ v' = u ∧ x' = y then 1 else 0) := by
    by_cases hx : x' = x
    · subst hx
      have hy : kd = Kind.stk → y = x' := fun h => by subst h; simp only [RoleOK] at hr; exact hr.1
      by_cases hv : L.nxt u x' = x'
      · have hb : L.pendB u x' = none := by simp [LaneSys.pendB, hv]
        have : L.nxt u x' ≠ v' := by rw [hv]; exact Ne.symm hvx
        rw [hb]
        by_cases hvu' : v' = u
        · subst hvu'
          cases kd <;> simp [pendA, this, hy]
        · cases kd <;> simp [pendA, this, hvu', Ne.symm hvu']
      · have hb : L.pendB u x' = some (L.nxt u x') := by simp [LaneSys.pendB, hv]
        rw [hb]
        by_cases hvu' : v' = u
        · subst hvu'
          cases kd <;> simp [pendA, hvu, hy] <;> omega
        · cases kd <;> simp [pendA, hvu', Ne.symm hvu']
    · simp only [hx, and_false, if_false]
      cases kd <;> simp only [reduceCtorEq, false_and, if_false, true_and]
      · by_cases hh : v' = u ∧ x' = y
        · exfalso; simp only [RoleOK] at hr; exact hx (hh.2.trans hr.1)
        · rw [if_neg hh]
  have hstk : (if kd = Kind.stk ∧ v' = u ∧ x' = y then 1 else 0) ≤ G.stock v' x' := by
    split_ifs with h
    · obtain ⟨rfl, rfl, rfl⟩ := h; simp only [RoleOK] at hr; exact hr.2
    · exact Nat.zero_le _
  have hcl : (if gcl (gh k s G (L.stage u x).1 0) = some x' ∧ v' = L.nxt u x ∧ L.nxt u x ≠ x'
      then 1 else 0) = (if L.nxt u x = v' ∧ gcl (gh k s G (L.stage u x).1 0) = some x'
      then 1 else 0) := by
    by_cases h : v' = L.nxt u x
    · subst h; simp [hvx, and_comm]
    · simp [h, Ne.symm h]
  have hdt : (if gdt (gh k s G (L.stage u x).1 0) = some x' ∧ v' = L.nxt u x then 1 else 0) =
      (if L.nxt u x = v' ∧ gdt (gh k s G (L.stage u x).1 0) = some x' then 1 else 0) := by
    by_cases h : v' = L.nxt u x
    · subst h; simp [and_comm]
    · simp [h, Ne.symm h]
  have hg3 : (if L.nxt u x = v' ∧ gtg (gh k s G (L.stage u x).1 0) = some x' then 1 else 0) =
      (if L.nxt u x = v' ∧ gcl (gh k s G (L.stage u x).1 0) = some x' then 1 else 0) +
      (if L.nxt u x = v' ∧ gdt (gh k s G (L.stage u x).1 0) = some x' then 1 else 0) := by
    by_cases h : L.nxt u x = v'
    · simp only [h, true_and]; exact hsplit
    · simp [h]
  omega

include td in
/-- Dirty tiles through one stage. -/
theorem gStage_dirty {G : GS k q} {u x : Sq k} (hux : u ≠ x) {kd : Kind} {y : Sq k}
    (hD : DirtyInv L s G) : DirtyInv L s (gStage L s τ G u x kd y) := by
  intro v' x'
  have hP := gStage_Dpos L td τ G hux kd y v' x'
  have hD' := hD v' x'
  have hland : land (L.stage u x).1 = L.nxt u x := rfl
  rw [hland] at hP
  rw [gStage_dA]
  simp only [gStage_B]
  have hsum : ∑ w ∈ univ.filter (fun w => w ≠ x' ∧ L.nxt w x' = v'),
      (G.B w x' + if kd = Kind.plh ∧ w = u ∧ x' = x then 1 else 0) =
      (∑ w ∈ univ.filter (fun w => w ≠ x' ∧ L.nxt w x' = v'), G.B w x') +
        (if L.nxt u x = v' ∧ kd = Kind.plh ∧ x' = x then 1 else 0) := by
    rw [sum_add_distrib]
    congr 1
    by_cases h : kd = Kind.plh ∧ x' = x
    · obtain ⟨h1, rfl⟩ := h
      simp only [h1, true_and, and_true]
      rw [Finset.sum_ite_eq']
      simp only [mem_filter, mem_univ, true_and]
      by_cases hv : L.nxt u x' = v'
      · simp [hv, hux]
      · simp [hv]
    · have : ∀ w, ¬ (kd = Kind.plh ∧ w = u ∧ x' = x) := fun w h' => h ⟨h'.1, h'.2.2⟩
      simp only [this, if_false, sum_const_zero]
      rw [if_neg (fun h' => h ⟨h'.2.1, h'.2.2⟩)]
  have hdt : (if gdt (gh k s G (L.stage u x).1 0) = some x' ∧ v' = L.nxt u x then 1 else 0) =
      (if L.nxt u x = v' ∧ gdt (gh k s G (L.stage u x).1 0) = some x' then 1 else 0) := by
    by_cases h : v' = L.nxt u x
    · subst h; simp [and_comm]
    · simp [h, Ne.symm h]
  rw [hsum]
  omega

end stage

end SlidingPuzzle.Tree
