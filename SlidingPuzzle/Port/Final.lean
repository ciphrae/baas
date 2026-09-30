import SlidingPuzzle.Port.Outer
import SlidingPuzzle.Tree.RunMain

/-! # The end of the port run

The residence bound for the port lanes (`pFcnt_le`), and the bounds on the cost and
on the tiles left outside their squares at the end of the run (`pouter_final`). -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle.Hub (Sq Round sends recv IsLast ind dummyAt roundW)
open SlidingPuzzle.Tree

variable {k q : ℕ} (L : LaneSys k q)

theorem gtg_eq_resP (s : ℕ) (G : PG k q) (l : Ln k q) (r : ℕ) :
    gtg (pgh k s G l r) = (GroupedPipe.ghostRun (lstep s) (loffP k s) (fun _ _ => none)
      (G.ins.map toRes) l r).map Prod.fst := by
  have h := ghostRun_toRes (lstep (q := q) s) (loffP k s) G.ins (fun _ _ => none)
  simp only [Option.map_none] at h
  rw [h]
  simp only [gtg, SlidingPuzzle.Port.pgh, Option.map_map]
  rfl

theorem pFcnt_le (s : ℕ) (N : Ln k q → Sq k → ℕ)
    (Lres : List (GroupedPipe.InsRec (Ln k q) (Sq k)))
    (hres : ∀ m, m ≤ Lres.length → ∀ H x len,
      ((range len).filter fun r =>
        (GroupedPipe.ghostRun (lstep s) (loffP k s) (fun _ _ => none) (Lres.take m) H r).map
          Prod.fst = some x).card ≤ N H x)
    (G : PG k q) (hpre : G.ins.map toRes <+: Lres) (v x : Sq k) :
    pFcnt L s G v x ≤ NvOf N v x := by
  unfold pFcnt plcnt NvOf
  rw [← Finset.sum_filter]
  refine sum_le_sum fun l _ => ?_
  have hm : (G.ins.map toRes).length ≤ Lres.length := hpre.length_le
  have e : Lres.take (G.ins.map toRes).length = G.ins.map toRes :=
    (List.prefix_iff_eq_take.1 hpre).symm
  have := hres _ hm l x (llen L s l)
  rw [e] at this
  refine le_trans (le_of_eq ?_) this
  congr 1
  apply filter_congr
  intro r _
  show gtg (pgh k s G l r) = some x ↔ _
  rw [gtg_eq_resP]

/-- The lanes and region counts of a port state. -/
def PState.toI (σ : PState k q) : IState k q := ⟨σ.row, σ.col, σ.cnt, σ.blank⟩

/-- The initial ghost state. -/
def PG0 (σ0 : PState k q) (R : Sq k → ℕ) : PG k q where
  σ := σ0
  evs := []
  ins := []
  sched := tdemand σ0.toI
  stock := fun _ _ _ => 0
  free := fun Q y => if y = Q then R Q else 0
  B := fun _ _ => 0
  dA := fun _ _ => 0
  served := fun _ => 0
  sent := fun _ => 0
  nh := 0
  ni := 0
  nx := 0
  nt := 0
  nis := 0
  ncr := 0
  jc := 0
  wt := 0

theorem pgh_PG0 (s : ℕ) (σ0 : PState k q) (R : Sq k → ℕ) :
    pgh k s (PG0 σ0 R) = fun _ _ => none := rfl

theorem plcnt_none (s : ℕ) (G : PG k q) (hG : pgh k s G = fun _ _ => none) (V : Ln k q → Prop)
    [DecidablePred V] (P : Option (GCls k × ℕ) → Prop) [DecidablePred P] (hP : ¬ P none) :
    plcnt L s G V P = 0 := by
  unfold plcnt
  apply Finset.sum_eq_zero
  intro l _
  split_ifs
  · rw [hG]; simp [hP]
  · rfl

theorem ppot_le' (s : ℕ) (σ : PState k q) : σ.pot L s ≤ laneCells L s * (k * s) := by
  unfold PState.pot
  have h1 : ∀ l : Ln k q, ∑ r ∈ (range (llen L s l)).filter (fun r => ¬ lgood l (σ.lane l r)),
      (r + 1) ≤ llen L s l * (k * s) := by
    intro l
    calc _ ≤ ∑ r ∈ range (llen L s l), (k * s) := by
          refine le_trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun _ _ _ => Nat.zero_le _)) (sum_le_sum fun r hr => ?_)
          have := llen_le L s l; simp at hr; omega
      _ = llen L s l * (k * s) := by simp
  refine (sum_le_sum fun l _ => h1 l).trans ?_
  rw [← sum_mul]
  apply Nat.mul_le_mul_right
  unfold laneCells
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp [llen, add_comm]

/-- The remaining cost of a route: blocks and hops. -/
def rrem (u x : Sq k) : ℕ := rcross L u x + L.srank u x

theorem rrem_step {u x : Sq k} (h : u ≠ x) : rrem L u x = pw L u x + rrem L (L.nxt u x) x := by
  unfold rrem pw
  rw [if_neg h, rcross_cons L h, srank_nxt (L := L) h]; ring

theorem rrem_self (x : Sq k) : rrem L x x = 0 := by
  unfold rrem; rw [rcross_self, srank_self]

theorem rrem_le (u x : Sq k) : rrem L u x ≤ 2 * k + 2 * L.depth := by
  unfold rrem
  have := rcross_le_k L x u
  have := srank_le (L := L) u x
  omega

/-- Placeholders weighted by their hops: each chain of dirty arrivals follows a route, so the
weights telescope to the remaining cost of the route where it started. -/
theorem sum_Bw_le (B dA c : Sq k → Sq k → ℕ) (x : Sq k)
    (h1 : ∀ v, B v x ≤ dA v x + c v x)
    (h2 : ∀ v, dA v x ≤ ∑ u ∈ univ.filter (fun u => u ≠ x ∧ L.nxt u x = v), B u x) :
    ∑ v, B v x * pw L v x ≤ ∑ v, c v x * rrem L v x := by
  classical
  have hA : ∑ v, B v x * rrem L v x ≤ ∑ v, dA v x * rrem L v x + ∑ v, c v x * rrem L v x := by
    rw [← sum_add_distrib]
    exact sum_le_sum fun v _ => by rw [← add_mul]; exact Nat.mul_le_mul_right _ (h1 v)
  have hB : ∑ v, dA v x * rrem L v x ≤
      ∑ u ∈ univ.filter (fun u => u ≠ x), B u x * rrem L (L.nxt u x) x := by
    calc ∑ v, dA v x * rrem L v x
        ≤ ∑ v, ∑ u ∈ univ.filter (fun u => u ≠ x ∧ L.nxt u x = v), B u x * rrem L v x :=
          sum_le_sum fun v _ => by rw [← sum_mul]; exact Nat.mul_le_mul_right _ (h2 v)
      _ = ∑ u ∈ univ.filter (fun u => u ≠ x), ∑ v ∈ ({L.nxt u x} : Finset (Sq k)),
            B u x * rrem L v x := by
          rw [Finset.sum_comm' (t' := univ.filter (fun u => u ≠ x))
            (s' := fun u => ({L.nxt u x} : Finset (Sq k)))]
          intro v u; simp only [mem_filter, mem_univ, true_and, mem_singleton]; aesop
      _ = _ := by simp
  have hC : ∑ v, B v x * rrem L v x = ∑ v, B v x * pw L v x +
      ∑ u ∈ univ.filter (fun u => u ≠ x), B u x * rrem L (L.nxt u x) x := by
    rw [sum_filter, ← sum_add_distrib]
    refine sum_congr rfl fun v _ => ?_
    by_cases hv : v = x
    · subst hv; simp [rrem_self, pw]
    · rw [if_pos hv, rrem_step L hv]; ring
  omega

/-- Transport budget of the port run: `W` bounds the relocation weight, `nd` the needs. -/
def prunCost (n k q s σ' depth lc nd W : ℕ) : ℕ :=
  lc * (k * s) + hopKc k σ' * (2 * depth * n ^ 2) + 7 * (q + 2) * (2 * k * n ^ 2) +
    hopKi k s σ' * (2 * n ^ 2 + (2 * depth + 1) * nd) + xferK k s σ' * (4 * n ^ 2) +
    s * ((2 * k + 2 * depth) * nd) + legA k s σ' * W / 8

/-- The bounds at the end of the run. -/
theorem pouter_final {n : ℕ} (c : PCtx k q) (Gf : PG k q)
    (hOf : POuter L c c.Δ Gf) (need : Sq k → ℕ)
    (hNv : ∀ Z, stkCap L c.Nv Z ≤ need Z)
    (hS0 : c.S0 ≤ n ^ 2) {W P : ℕ} (hW : ∑ τ ∈ range c.Δ, roundW (c.rd τ) ≤ W)
    (hpot : c.σ0.pot L c.s ≤ P) :
    c.σ0.Valid L c.s Gf.evs ∧
      c.σ0.totalCost c.s c.σ' Gf.evs ≤ P + hopKc k c.σ' * (2 * L.depth * n ^ 2) +
        7 * (q + 2) * (2 * k * n ^ 2) +
        hopKi k c.s c.σ' * (2 * n ^ 2 + (2 * L.depth + 1) * ∑ v, need v) +
        xferK k c.s c.σ' * (4 * n ^ 2) +
        c.s * ((2 * k + 2 * L.depth) * ∑ v, need v) + legA k c.s c.σ' * W / 8 ∧
      (c.σ0.run c.s Gf.evs).offCount ≤ (∑ v, need v) + c.F0 := by
  have hsch0 : ∀ S D, Gf.sched S D = 0 := by
    intro S D; rw [hOf.sched]; simp
  have hserved : ∑ Z, Gf.served Z ≤ n ^ 2 := by
    have := hOf.hin.sched_sum; omega
  have hdA : ∀ v x, Gf.dA v x ≤ ∑ u ∈ univ.filter (fun u => u ≠ x ∧ L.nxt u x = v), Gf.B u x :=
    fun v x => by have := hOf.hin.dirty v x; omega
  have hBc : ∀ v x, Gf.B v x ≤ Gf.dA v x + (c.Nv v x + if L.Act v x then 1 else 0) := by
    intro v x
    obtain ⟨h1, h2⟩ := hOf.hin.binv v x
    split_ifs with ha
    · omega
    · have : Gf.B v x = 0 := by by_contra h0; exact ha (h2 h0)
      omega
  have hBtot : ∑ v, ∑ x, Gf.B v x ≤ (2 * L.depth + 1) * ∑ v, need v := by
    rw [Finset.sum_comm]
    calc ∑ x, ∑ v, Gf.B v x ≤ ∑ x, (2 * L.depth + 1) * ∑ v,
          (c.Nv v x + if L.Act v x then 1 else 0) :=
          sum_le_sum fun x _ => sum_B_le L Gf.B Gf.dA
            (fun v x => c.Nv v x + if L.Act v x then 1 else 0) x (fun v => hBc v x)
            (fun v => hdA v x)
      _ = (2 * L.depth + 1) * ∑ v, ∑ x, (c.Nv v x + if L.Act v x then 1 else 0) := by
          rw [← mul_sum, Finset.sum_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ (sum_le_sum fun v _ => hNv v)
  refine ⟨hOf.lin.valid, ?_, ?_⟩
  · have hcost := hOf.lin.cost
    have hturn := hOf.lin.turn
    have h3 : hopKc k c.σ' * Gf.nh ≤ hopKc k c.σ' * (2 * L.depth * n ^ 2) :=
      Nat.mul_le_mul_left _ (hOf.hin.nh.trans (Nat.mul_le_mul_left _ hserved))
    have h3' : 7 * (q + 2) * Gf.ncr ≤ 7 * (q + 2) * (2 * k * n ^ 2) :=
      Nat.mul_le_mul_left _ (hOf.hin.ncr.trans (Nat.mul_le_mul_left _ hserved))
    have hni : Gf.ni ≤ 2 * n ^ 2 + (2 * L.depth + 1) * ∑ v, need v := by
      have := hOf.hin.ni; have := hOf.hin.nt
      unfold sBt at this
      have : Gf.nis ≤ Gf.nt := by omega
      unfold sBt at *
      omega
    have h4 := Nat.mul_le_mul_left (hopKi k c.s c.σ') hni
    have h5 : xferK k c.s c.σ' * Gf.nx ≤ xferK k c.s c.σ' * (4 * n ^ 2) :=
      Nat.mul_le_mul_left _ (hOf.hin.nx.trans (by omega))
    have hBw : ∑ v, ∑ x, Gf.B v x * pw L v x ≤ (2 * k + 2 * L.depth) * ∑ v, need v := by
      rw [Finset.sum_comm]
      calc ∑ x, ∑ v, Gf.B v x * pw L v x ≤ ∑ x, ∑ v,
            (c.Nv v x + if L.Act v x then 1 else 0) * rrem L v x :=
            sum_le_sum fun x _ => sum_Bw_le L Gf.B Gf.dA
              (fun v x => c.Nv v x + if L.Act v x then 1 else 0) x (fun v => hBc v x)
              (fun v => hdA v x)
        _ ≤ ∑ x, ∑ v, (c.Nv v x + if L.Act v x then 1 else 0) * (2 * k + 2 * L.depth) :=
            sum_le_sum fun x _ => sum_le_sum fun v _ => Nat.mul_le_mul_left _ (rrem_le L v x)
        _ = (2 * k + 2 * L.depth) * ∑ v, ∑ x, (c.Nv v x + if L.Act v x then 1 else 0) := by
            rw [Finset.sum_comm, mul_sum]
            refine sum_congr rfl fun v _ => ?_
            rw [mul_sum]; exact sum_congr rfl fun x _ => by ring
        _ ≤ _ := Nat.mul_le_mul_left _ (sum_le_sum fun v _ => hNv v)
    have h6 := Nat.mul_le_mul_left c.s hBw
    have h7 : Gf.jc ≤ legA k c.s c.σ' * W / 8 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      have := hOf.hin.jc
      have := Nat.mul_le_mul_left (legA k c.s c.σ') (hOf.wt.trans hW)
      linarith
    have := Nat.zero_le (Gf.σ.pot L c.s)
    omega
  · rw [← hOf.lin.run_eq]
    have hoff : Gf.σ.offCount ≤ ∑ Q, ∑ y, (Gf.stk Q y + Gf.free Q y) := by
      unfold PState.offCount
      refine sum_le_sum fun Q _ => sum_le_sum fun y _ => ?_
      split_ifs with hy
      · exact Nat.zero_le _
      · have := hOf.lin.roles_ge Q y hy; rw [hsch0] at this; omega
    have hstock : ∀ v x, Gf.stk v x ≤ c.Nv v x + if L.Act v x then 1 else 0 := by
      intro v x
      by_cases hvx : v = x
      · subst hvx
        have : Gf.stk v v = 0 := by
          unfold PG.stk; exact Finset.sum_eq_zero fun pt _ => hOf.lin.stock_diag v pt
        omega
      · have h1 := hOf.hin.ident v x hvx
        have h2 := hBc v x
        omega
    have hst : ∑ Q, ∑ y, Gf.stk Q y ≤ ∑ v, need v :=
      sum_le_sum fun v _ => (sum_le_sum fun x _ => hstock v x).trans (hNv v)
    have hdAtot : ∑ v, ∑ x, Gf.dA v x ≤ ∑ v, ∑ x, Gf.B v x :=
      sum_dA_le L Gf.dA Gf.B hdA
    have hfr := hOf.lin.free_tot
    have hsplit : ∑ Q, ∑ y, (Gf.stk Q y + Gf.free Q y) =
        (∑ Q, ∑ y, Gf.stk Q y) + ∑ Q, ∑ y, Gf.free Q y := by
      simp [sum_add_distrib]
    omega

end SlidingPuzzle.Port
