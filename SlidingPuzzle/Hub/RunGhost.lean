import SlidingPuzzle.Hub.RunArith
import SlidingPuzzle.Hub.InFlight

/-! # The ghost state of the abstract run

`GS` carries the current `IState`, the resolved operations so far, the row
insertions so far (the ghost rows are `ghostRun` of them), the tile roles
(`sched`, `stock`, `free`; everything else of a region is `home`), the counters
`out` (initial row tiles dropped into a hub as stock) and `byp` (bypasses), and
round bookkeeping (`served`, `sent`, `wt`, `dd`).

This file defines the three ghost operations (one per resolved operation) and
proves that they preserve the local invariant `LInv`. -/
namespace SlidingPuzzle.Hub

open Finset

variable {k : ℕ}

/-- The ghost state. -/
structure GS (k : ℕ) where
  σ : IState k
  evs : List (REvent k)
  ins : List (InsRec k)
  sched : Sq k → Sq k → ℕ
  stock : Sq k → Sq k → ℕ
  free : Sq k → Sq k → ℕ
  out : Sq k → Sq k → ℕ
  byp : Sq k → Sq k → ℕ
  served : Sq k → ℕ
  sent : Sq k → ℕ
  wt : ℕ
  dd : Sq k → ℕ
  fb : ℕ

/-- The ghost rows. -/
def gh (s : ℕ) (G : GS k) : Ghost k := ghostRun s (fun _ _ => none) G.ins

/-- A tile of class `z` dropping into hub `h` becomes stock. -/
def isStk (h z : Sq k) : Prop := z ≠ h ∧ z.2 = h.2

instance (h z : Sq k) : Decidable (isStk h z) := by unfold isStk; infer_instance

/-- Positions of the two halves of `R(h)` whose ghost satisfies `P`. -/
def hubCnt (s : ℕ) (g : Ghost k) (P : Option (Sq k × ℕ) → Prop) [DecidablePred P]
    (h : Sq k) : ℕ :=
  ∑ side : Bool, ((range (rowLen k s (h.1, h.2, side))).filter
    fun q => P (g (h.1, h.2, side) q)).card

theorem newCnt_eq_hubCnt (s : ℕ) (g : Ghost k) (h x : Sq k) :
    newCnt s g h x = hubCnt s g (fun o => o.map Prod.fst = some x) h := rfl

/-- Initial tiles still in the halves of `R(h)`. -/
def noneCnt (s : ℕ) (g : Ghost k) (h : Sq k) : ℕ := hubCnt s g (fun o => o = none) h

/-- Junk positions of a row half. -/
def junkR (s : ℕ) (σ : IState k) (H : RowH k) : ℕ :=
  ((range (rowLen k s H)).filter fun q => (σ.row H q).2 ≠ H.2.1).card

/-- Junk positions of a column half. -/
def junkC (s : ℕ) (σ : IState k) (V : ColH k) : ℕ :=
  ((range (colLen k s V)).filter fun q => σ.col V q ≠ (V.2.1, V.1)).card

/-- All junk positions. -/
def junkCnt (s : ℕ) (σ : IState k) : ℕ := (∑ H, junkR s σ H) + ∑ V, junkC s σ V

/-- Weighted junk of a row half. -/
def potR (s : ℕ) (σ : IState k) (H : RowH k) : ℕ :=
  ∑ q ∈ (range (rowLen k s H)).filter (fun q => (σ.row H q).2 ≠ H.2.1), (q + 1)

/-- Weighted junk of a column half. -/
def potC (s : ℕ) (σ : IState k) (V : ColH k) : ℕ :=
  ∑ q ∈ (range (colLen k s V)).filter (fun q => σ.col V q ≠ (V.2.1, V.1)), (q + 1)

/-- The junk potential: it pays for the junk terms of the hop costs. -/
def pot (s : ℕ) (σ : IState k) : ℕ := (∑ H, potR s σ H) + ∑ V, potC s σ V

/-! ## The three ghost operations -/

/-- The head of the half used by a hop1. -/
abbrev rowHead (G : GS k) (S h : Sq k) : Sq k := G.σ.row (hop1Half S h) 0

/-- The head of the half used by a hop2. -/
abbrev colHead (G : GS k) (h D : Sq k) : Sq k := G.σ.col (hop2Half h D) 0

/-- `hop1 S h y`, sending a scheduled tile of `S`. -/
def gHop1 (s τ : ℕ) (G : GS k) (S h y : Sq k) : GS k :=
  { G with
    σ := G.σ.step s (.hop1 S h y)
    evs := G.evs ++ [.hop1 S h y]
    ins := G.ins ++ [⟨τ, hop1Half S h, hop1Dist S h, y⟩]
    sched := decCnt G.sched S y
    stock := if isStk h (rowHead G S h) then incCnt G.stock h (rowHead G S h) else G.stock
    free := if (rowHead G S h).2 ≠ h.2 then incCnt G.free h (rowHead G S h) else G.free
    out := if isStk h (rowHead G S h) ∧ gh s G (hop1Half S h) 0 = none then
      incCnt G.out h (rowHead G S h) else G.out }

/-- `hop2 h D y`, sending a stock tile (`st = true`) or a scheduled tile of `h`. -/
def gHop2 (s : ℕ) (G : GS k) (st : Bool) (h D y : Sq k) : GS k :=
  { G with
    σ := G.σ.step s (.hop2 h D y)
    evs := G.evs ++ [.hop2 h D y]
    sched := if st then G.sched else decCnt G.sched h y
    stock := if st then decCnt G.stock h y else G.stock
    free := if colHead G h D ≠ D then incCnt G.free D (colHead G h D) else G.free }

/-- `jump E Z y`, moving a free tile. -/
def gJump (s : ℕ) (G : GS k) (E Z y : Sq k) : GS k :=
  { G with
    σ := G.σ.step s (.jump E Z y)
    evs := G.evs ++ [.jump E Z y]
    free := incCnt (decCnt G.free Z y) E y }

/-- `rjump E Z a y`, moving the designated tile of `Z` (a free tile) to `E`. -/
def gRJump (s : ℕ) (G : GS k) (E Z : Sq k) (a : Bool) (y : Sq k) : GS k :=
  { G with
    σ := G.σ.step s (.rjump E Z a y)
    evs := G.evs ++ [.rjump E Z a y]
    free := incCnt (decCnt G.free Z y) E y }

/-- `restore Z c y`, designating a free class-`y` tile of `Z`. -/
def gRestore (s : ℕ) (G : GS k) (Z : Sq k) (c : Bool) (y : Sq k) : GS k :=
  { G with
    σ := G.σ.step s (.restore Z c y)
    evs := G.evs ++ [.restore Z c y] }

/-! ## Effects -/

section effects

variable (s : ℕ)

theorem ghostRun_append_one (g : Ghost k) (L : List (InsRec k)) (r : InsRec k) :
    ghostRun s g (L ++ [r]) = ghostStep s (ghostRun s g L) r := by
  simp [ghostRun, List.foldl_append]

theorem gh_gHop1 (τ : ℕ) (G : GS k) (S h y : Sq k) :
    gh s (gHop1 s τ G S h y) = Function.update (gh s G) (hop1Half S h)
      (shiftIn (gh s G (hop1Half S h)) (hop1Pos s S h) (some (y, hop1Dist S h))) := by
  simp only [gh, gHop1, ghostRun_append_one, ghostStep]
  rfl

theorem row_hop1 (σ : IState k) (S h y : Sq k) :
    (σ.step s (.hop1 S h y)).row = Function.update σ.row (hop1Half S h)
      (shiftIn (σ.row (hop1Half S h)) (hop1Pos s S h) y) := rfl

theorem cnt_hop1 (σ : IState k) (S h y Q y' : Sq k) :
    (σ.step s (.hop1 S h y)).cnt Q y' = σ.cnt Q y' - (if Q = S ∧ y' = y then 1 else 0) +
      (if Q = h ∧ y' = σ.row (hop1Half S h) 0 then 1 else 0) := by
  simp only [IState.step, incCnt_apply, decCnt_apply]

theorem cnt_hop2 (σ : IState k) (h D y Q y' : Sq k) :
    (σ.step s (.hop2 h D y)).cnt Q y' = σ.cnt Q y' - (if Q = h ∧ y' = y then 1 else 0) +
      (if Q = D ∧ y' = σ.col (hop2Half h D) 0 then 1 else 0) := by
  simp only [IState.step, incCnt_apply, decCnt_apply]

theorem cnt_rjump (σ : IState k) (E Z : Sq k) (a : Bool) (y Q y' : Sq k) :
    (σ.step s (.rjump E Z a y)).cnt Q y' = σ.cnt Q y' - (if Q = Z ∧ y' = y then 1 else 0) +
      (if Q = E ∧ y' = y then 1 else 0) := by
  simp only [IState.step, incCnt_apply, decCnt_apply]

omit s in
/-- Clearing one recorded class and recording another at a different square. -/
theorem dcnt_upd (d : Sq k → Bool → Option (Sq k)) {E Z : Sq k} (hEZ : E ≠ Z) (a b : Bool)
    {y : Sq k} (hdes : d Z b = some y) (Q x : Sq k) :
    ((if (if Q = Z ∧ false = b then none else if Q = E ∧ false = a then some y else d Q false) =
          some x then 1 else 0) +
        (if (if Q = Z ∧ true = b then none else if Q = E ∧ true = a then some y else d Q true) =
          some x then 1 else 0)) + (if Q = Z ∧ x = y then 1 else 0) ≤
      ((if d Q false = some x then 1 else 0) + (if d Q true = some x then 1 else 0)) +
        (if Q = E ∧ x = y then 1 else 0) := by
  by_cases hQZ : Q = Z
  · subst hQZ
    have hQE : ¬ (Q = E) := fun e => hEZ e.symm
    cases b <;> simp only [hQE, true_and, false_and, if_false, Bool.false_eq_true, if_true,
      reduceCtorEq] at hdes ⊢ <;> rw [hdes] <;> split_ifs <;> simp_all
  · by_cases hQE : Q = E
    · subst hQE
      cases a <;> simp only [hQZ, true_and, false_and, if_false, Bool.false_eq_true, if_true] <;>
        split_ifs <;> simp_all
    · simp [hQE, hQZ]

/-- A designated jump clears the landing record and records the departure cell. -/
theorem dcnt_rjump (σ : IState k) {E Z : Sq k} (hEZ : E ≠ Z) (a : Bool) {y : Sq k}
    (hdes : σ.des Z (landB s E Z a) = some y) (Q x : Sq k) :
    (σ.step s (.rjump E Z a y)).dcnt Q x + (if Q = Z ∧ x = y then 1 else 0) ≤
      σ.dcnt Q x + (if Q = E ∧ x = y then 1 else 0) :=
  dcnt_upd σ.des hEZ a (landB s E Z a) hdes Q x

theorem dcnt_restore (σ : IState k) {Z : Sq k} {c : Bool} {y : Sq k} (hnone : σ.des Z c = none)
    (Q x : Sq k) :
    (σ.step s (.restore Z c y)).dcnt Q x = σ.dcnt Q x + (if Q = Z ∧ x = y then 1 else 0) := by
  unfold IState.dcnt
  simp only [IState.step]
  by_cases hQ : Q = Z
  · subst hQ
    cases c <;> simp only [true_and, Bool.false_eq_true, if_true, if_false] at hnone ⊢ <;>
      rw [hnone] <;> split_ifs <;> simp_all
  · simp [hQ]

theorem cnt_jump (σ : IState k) (E Z y Q y' : Sq k) :
    (σ.step s (.jump E Z y)).cnt Q y' = σ.cnt Q y' - (if Q = Z ∧ y' = y then 1 else 0) +
      (if Q = E ∧ y' = y then 1 else 0) := by
  simp only [IState.step, incCnt_apply, decCnt_apply]

/-- The count of a hub after an insertion into one of its halves. -/
theorem hubCnt_update (g : Ghost k) (P : Option (Sq k × ℕ) → Prop) [DecidablePred P]
    {h : Sq k} {side0 : Bool} {p : ℕ} (hp : p < rowLen k s (h.1, h.2, side0))
    (v : Option (Sq k × ℕ)) (h' : Sq k) :
    hubCnt s (Function.update g (h.1, h.2, side0) (shiftIn (g (h.1, h.2, side0)) p v)) P h' +
        (if h' = h ∧ P (g (h.1, h.2, side0) 0) then 1 else 0) =
      hubCnt s g P h' + (if h' = h ∧ P v then 1 else 0) := by
  unfold hubCnt
  rw [Fintype.sum_bool, Fintype.sum_bool]
  by_cases hh : h' = h
  · subst hh
    have key := card_filter_shiftIn P (g (h'.1, h'.2, side0)) hp v
    cases side0
    · simp only [Function.update_self, true_and]
      rw [Function.update_of_ne (by simp)]
      omega
    · simp only [Function.update_self, true_and]
      rw [Function.update_of_ne (by simp)]
      omega
  · have hne : ∀ b : Bool, ((h'.1, h'.2, b) : RowH k) ≠ (h.1, h.2, side0) := by
      intro b e
      apply hh
      simp only [Prod.mk.injEq] at e
      exact Prod.ext e.1 e.2.1
    simp only [Function.update_of_ne (hne _), hh, false_and, if_false]

theorem hubCnt_gHop1 (τ : ℕ) (G : GS k) {S h : Sq k} (hS : S.2 ≠ h.2) (hs : k + 1 ≤ s)
    (y : Sq k) (P : Option (Sq k × ℕ) → Prop) [DecidablePred P] (h' : Sq k) :
    hubCnt s (gh s (gHop1 s τ G S h y)) P h' +
        (if h' = h ∧ P (gh s G (hop1Half S h) 0) then 1 else 0) =
      hubCnt s (gh s G) P h' + (if h' = h ∧ P (some (y, hop1Dist S h)) then 1 else 0) := by
  rw [gh_gHop1]
  exact hubCnt_update s (gh s G) P (hop1Pos_lt hS hs) _ h'

/-! Coordinates of the role counts after each operation. -/

theorem gHop1_sched (τ : ℕ) (G : GS k) (S h y Q x : Sq k) :
    (gHop1 s τ G S h y).sched Q x = G.sched Q x - (if Q = S ∧ x = y then 1 else 0) := by
  simp [gHop1, decCnt_apply]

theorem gHop1_stock (τ : ℕ) (G : GS k) (S h y Q x : Sq k) :
    (gHop1 s τ G S h y).stock Q x =
      G.stock Q x + (if isStk h (rowHead G S h) ∧ Q = h ∧ x = rowHead G S h then 1 else 0) := by
  simp only [gHop1]
  by_cases hc : isStk h (rowHead G S h)
  · simp [hc, incCnt_apply]
  · simp [hc]

theorem gHop1_free (τ : ℕ) (G : GS k) (S h y Q x : Sq k) :
    (gHop1 s τ G S h y).free Q x =
      G.free Q x + (if (rowHead G S h).2 ≠ h.2 ∧ Q = h ∧ x = rowHead G S h then 1 else 0) := by
  simp only [gHop1]
  by_cases hc : (rowHead G S h).2 ≠ h.2
  · simp only [hc, ne_eq, not_false_eq_true, if_true, incCnt_apply, true_and]
  · simp [hc]

theorem gHop1_out (τ : ℕ) (G : GS k) (S h y Q x : Sq k) :
    (gHop1 s τ G S h y).out Q x =
      G.out Q x + (if (isStk h (rowHead G S h) ∧ gh s G (hop1Half S h) 0 = none) ∧
        Q = h ∧ x = rowHead G S h then 1 else 0) := by
  simp only [gHop1]
  by_cases hc : isStk h (rowHead G S h) ∧ gh s G (hop1Half S h) 0 = none
  · rw [if_pos hc, incCnt_apply]; simp [hc]
  · rw [if_neg hc]; simp [hc]

theorem gHop2_sched (G : GS k) (st : Bool) (h D y Q x : Sq k) :
    (gHop2 s G st h D y).sched Q x =
      G.sched Q x - (if st = false ∧ Q = h ∧ x = y then 1 else 0) := by
  cases st <;> simp [gHop2, decCnt_apply]

theorem gHop2_stock (G : GS k) (st : Bool) (h D y Q x : Sq k) :
    (gHop2 s G st h D y).stock Q x =
      G.stock Q x - (if st = true ∧ Q = h ∧ x = y then 1 else 0) := by
  cases st <;> simp [gHop2, decCnt_apply]

theorem gHop2_free (G : GS k) (st : Bool) (h D y Q x : Sq k) :
    (gHop2 s G st h D y).free Q x =
      G.free Q x + (if colHead G h D ≠ D ∧ Q = D ∧ x = colHead G h D then 1 else 0) := by
  simp only [gHop2]
  by_cases hc : colHead G h D ≠ D
  · simp only [hc, ne_eq, not_false_eq_true, if_true, incCnt_apply, true_and]
  · simp [hc]

theorem gJump_free (G : GS k) (E Z y Q x : Sq k) :
    (gJump s G E Z y).free Q x =
      G.free Q x - (if Q = Z ∧ x = y then 1 else 0) + (if Q = E ∧ x = y then 1 else 0) := by
  simp [gJump, incCnt_apply, decCnt_apply]

end effects

/-! ## The local invariant -/

/-- Invariants preserved by every single operation. `F0` bounds free tiles
plus junk positions (free tiles only grow by junk heads). -/
structure LInv (s : ℕ) (σ0 : IState k) (F0 : ℕ) (G : GS k) : Prop where
  roles_le : ∀ Q y, G.sched Q y + G.stock Q y + G.free Q y ≤ G.σ.cnt Q y
  roles_ge : ∀ Q y, y ≠ Q → G.σ.cnt Q y ≤ G.sched Q y + G.stock Q y + G.free Q y
  stock_supp : ∀ h x, G.stock h x ≠ 0 → isStk h x
  ghost_row : ∀ H q x d, gh s G H q = some (x, d) → G.σ.row H q = x ∧ x.2 = H.2.1
  out_le : ∀ h : Sq k, (∑ x, G.out h x) + noneCnt s (gh s G) h ≤ (k - 1) * s
  free_junk : (∑ Q, ∑ y, G.free Q y) + junkCnt s G.σ ≤ F0
  run_eq : G.σ = IState.run s σ0 G.evs
  valid : IState.Valid s σ0 G.evs
  dfree : ∀ Q y, G.σ.dcnt Q y ≤ G.free Q y

section sums

theorem sum_sum_ind (Z y : Sq k) :
    (∑ Q : Sq k, ∑ x : Sq k, if Q = Z ∧ x = y then 1 else 0) = 1 := by
  rw [Finset.sum_eq_single Z]
  · simp
  · intro Q _ hQ; simp [hQ]
  · simp

theorem sum_sum_ind_cond (c : Prop) [Decidable c] (Z y : Sq k) :
    (∑ Q : Sq k, ∑ x : Sq k, if c ∧ Q = Z ∧ x = y then 1 else 0) = if c then 1 else 0 := by
  by_cases hc : c
  · simp only [hc, true_and, if_true]; exact sum_sum_ind Z y
  · simp [hc]

/-- Adding indicators to a double sum. -/
theorem sum_sum_add_ind (f : Sq k → Sq k → ℕ) (c : Prop) [Decidable c] (Z y : Sq k) :
    (∑ Q, ∑ x, (f Q x + if c ∧ Q = Z ∧ x = y then 1 else 0)) =
      (∑ Q, ∑ x, f Q x) + if c then 1 else 0 := by
  simp only [sum_add_distrib, sum_sum_ind_cond]

end sums

section pres

variable {s : ℕ} {σ0 : IState k} {F0 : ℕ}

theorem pre_append {G : GS k} (hL : LInv s σ0 F0 G) {e : REvent k} (he : G.σ.Pre s e) :
    G.σ.step s e = IState.run s σ0 (G.evs ++ [e]) ∧ IState.Valid s σ0 (G.evs ++ [e]) := by
  rw [IState.run_append, ← hL.run_eq, IState.valid_append, ← hL.run_eq]
  exact ⟨rfl, hL.valid, (IState.valid_singleton s _ _).2 he⟩

theorem cost_append {G : GS k} (hL : LInv s σ0 F0 G) (e : REvent k) :
    IState.totalCost s σ0 (G.evs ++ [e]) = IState.totalCost s σ0 G.evs + G.σ.cost s e := by
  rw [IState.totalCost_append, ← hL.run_eq, IState.totalCost_singleton]

end pres

end SlidingPuzzle.Hub
