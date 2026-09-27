import SlidingPuzzle.Hub.Interface
import SlidingPuzzle.Hub.RoundWalk
import SlidingPuzzle.Hub.InFlight
import SlidingPuzzle.Hub.RunBounds

/-! # The abstract transport run

From an `IState` (the abstraction of the normalized input board) build the
plan (`exists_rounds`), set aside the reserve matchings, order the remaining
rounds (`exists_good_order`), walk every round (`exists_round_events`), and
resolve every high-level event into operations:

* `serve S D` with `S.2 = D.2`: `hop2 S D D`;
* with `S.1 = D.1`: `hop1 S D D`;
* otherwise, with the hub `h = (S.1, D.2)`: `hop2 h D D` if `h` has class-`D`
  stock, else the bypass `jump D h y` (a free tile `y` of `h`), then `hop1 S h D`;
* `reloc E Z`: `jump E Z y`, or two jumps through the corner `(Z.1, E.2)`.

Roles (scheduled, stock, free, home) are ghost counts; the stock identity
bounds the bypasses by the in-flight maxima. See `PROOF.md` §§3-7.

The proof is spread over `Hub/Run*.lean`: `RunShift` (generic lemmas),
`RunArith` (layout and plan arithmetic), `RunGhost`/`RunLocal` (ghost state,
single operations), `RunHigh`/`RunStep` (high-level events), `RunRound`/
`RunInner` (rounds), `RunInit` (initial state), `RunBounds` (numeric bounds). -/
namespace SlidingPuzzle.Hub

open Finset

/-- Transport budget retaining the actual grid dimensions and logarithm. -/
def transportBound (n k s : ℕ) : ℕ :=
  4 * k ^ 2 * n ^ 2 + 2 * (55 * s + 13 * k ^ 2 + 65 * k + 78) * n ^ 2 +
    (s + 3) * (39 * k + 15) * (k ^ 2 * (Rhub n + k ^ 2)) +
    (s + 3) * (s ^ 2 * (66 * k ^ 2 + 132 * k + 30) + (78 * k + 30) * (k ^ 2 * (2 * n + 1)))

/-- Region tiles left outside their squares, before absorbing lower-order terms. -/
def misplacedBound (n k : ℕ) : ℕ :=
  k ^ 2 * n + k ^ 2 * (Rhub n + k ^ 2) +
    k ^ 2 * (Rhub n + 8 * n + 10) + 4 * k ^ 2 * n

variable {k : ℕ}

/-- Scheduled tiles at the start: real plan edges. -/
def schedInit (rd : ℕ → Round k) (Δ : ℕ) (S D : Sq k) : ℕ := ∑ τ ∈ range Δ, ind (rd τ) S D

/-- Real edges of `S` among the set-aside rounds. -/
def realInit {Δ0 : ℕ} (rs0 : Fin Δ0 → Round k) (Q' : ℕ) (S : Sq k) : ℕ :=
  ∑ j ∈ range Q', if (rsN rs0 j).real S then 1 else 0

/-- Free tiles at the start: real edges of the set-aside rounds, padded with
home tiles up to `Q'` in total. -/
def freeInit (σ0 : IState k) {Δ0 : ℕ} (rs0 : Fin Δ0 → Round k) (Q' : ℕ) (S D : Sq k) : ℕ :=
  (∑ j ∈ range Q', ind (rsN rs0 j) S D) +
    if S = D then min (σ0.cnt S S) (Q' - realInit rs0 Q' S) else 0

theorem realInit_le {Δ0 : ℕ} (rs0 : Fin Δ0 → Round k) (Q' : ℕ) (S : Sq k) :
    realInit rs0 Q' S ≤ Q' := by
  unfold realInit
  have h1 : ∑ j ∈ range Q', (if (rsN rs0 j).real S then 1 else 0) ≤ ∑ _j ∈ range Q', 1 :=
    sum_le_sum fun j _ => by split_ifs <;> omega
  simpa using h1

theorem sum_freeInit (σ0 : IState k) {Δ0 : ℕ} (rs0 : Fin Δ0 → Round k) (Q' : ℕ) (S : Sq k) :
    ∑ D, freeInit σ0 rs0 Q' S D =
      realInit rs0 Q' S + min (σ0.cnt S S) (Q' - realInit rs0 Q' S) := by
  unfold freeInit realInit
  rw [sum_add_distrib, sum_comm]
  simp only [sum_ind_left, sum_ite_eq, mem_univ, if_true]

theorem sum_freeInit_le (σ0 : IState k) {Δ0 : ℕ} (rs0 : Fin Δ0 → Round k) (Q' : ℕ) (S : Sq k) :
    ∑ D, freeInit σ0 rs0 Q' S D ≤ Q' := by
  rw [sum_freeInit]
  have := realInit_le rs0 Q' S
  have := min_le_right (σ0.cnt S S) (Q' - realInit rs0 Q' S)
  omega

/-- The abstract run exists, is valid, and is cheap. -/
theorem exists_valid_run {n k s : ℕ} (hd : HDims n k s)
    (hP1 : 48 * k * (Nat.log 2 n + 1) ≤ s) (hks2 : 8 * k ^ 2 ≤ s) (σ0 : IState k)
    (hF1 : ∀ Q, (∑ y, σ0.cnt Q y) + (if σ0.blank = Q then 1 else 0) = regionSize k s)
    (hF2 : ∀ y, (∑ Q, σ0.cnt Q y) + σ0.corrCount s y = s ^ 2 - (if IsLast y then 1 else 0)) :
    ∃ es : List (REvent k), σ0.Valid s es ∧ σ0.totalCost s es ≤ transportBound n k s ∧
      (σ0.run s es).offCount ≤ misplacedBound n k := by
  classical
  have hmul := hd.mul
  subst hmul
  have hk2 := hd.two_le
  have hroom4 := hd.room
  have hks : k ≤ s := by omega
  have hsize := capacity_lower_bounds hd hP1
  have h2ks : 2 * k ≤ s := by omega
  have hroom : k + 1 ≤ s := by omega
  have hsqC := sqCorridor_le (k := k) (s := s)
  have hreg := regionSize_add (k := k) (s := s) h2ks
  obtain ⟨Δ0, rs0, hc1, hc2, hc3, hc4, hc5⟩ := exists_rounds (demand σ0) (demand_diag σ0)
  have hsends : ∀ S, sends (demand σ0) S ≤ s ^ 2 := fun S => by
    have := sends_le hF1 S; omega
  have hrecv : ∀ S, recv (demand σ0) S ≤ s ^ 2 := fun S => by have := recv_le hF2 S; omega
  have hΔ0 : Δ0 ≤ s ^ 2 := hc5 _ fun S => ⟨hsends S, hrecv S⟩
  obtain ⟨Q', hQ'⟩ : ∃ Q', Q' = min Δ0 (Rhub (k * s) + 8 * k * s + 10) := ⟨_, rfl⟩
  have hQle : Q' ≤ Δ0 := by rw [hQ']; exact min_le_left _ _
  have hQle2 : Q' ≤ Rhub (k * s) + 8 * k * s + 10 := by rw [hQ']; exact min_le_right _ _
  have hΔ : Δ0 - Q' ≤ s ^ 2 + 1 := by omega
  obtain ⟨σo, hσo⟩ := exists_good_order hd hP1 hks2 hΔ (planRs rs0 Q')
  obtain ⟨rd, hrd⟩ : ∃ rd, rd = ordRd rs0 Q' σo := ⟨_, rfl⟩
  -- counting over all rounds
  have cnt_ind : ∀ S D, ∑ j ∈ range Δ0, ind (rsN rs0 j) S D = demand σ0 S D := by
    intro S D
    have e := sum_rsN rs0 (fun r => ind r S D)
    beta_reduce at e
    rw [e, ← hc1 S D, card_filter]
    rfl
  have cnt_dum : ∀ S, ∑ j ∈ range Δ0, dummyAt (rsN rs0 j) S =
      recv (demand σ0) S - sends (demand σ0) S := by
    intro S
    have e := sum_rsN rs0 (fun r => dummyAt r S)
    beta_reduce at e
    rw [e, ← hc2 S, card_filter]
    rfl
  have cnt_loop : ∀ S, ∑ j ∈ range Δ0, (if (rsN rs0 j).perm S = S then 1 else 0) =
      Δ0 - max (sends (demand σ0) S) (recv (demand σ0) S) := by
    intro S
    have e := sum_rsN rs0 (fun r => if r.perm S = S then 1 else 0)
    beta_reduce at e
    rw [e, ← hc3 S, card_filter]
  have hsplit := fun f => sum_rsN_split rs0 f hQle
  have hord := fun f => sum_ordRd rs0 f Q' σo
  rw [← hrd] at hord
  have hdum_plan : ∀ Z, ∑ τ ∈ range (Δ0 - Q'), dummyAt (rd τ) Z ≤ sqCorridor k s + 1 := by
    intro Z
    have e := hord (fun r => dummyAt r Z)
    beta_reduce at e
    rw [e]
    have := hsplit (fun r => dummyAt r Z)
    beta_reduce at this
    have := cnt_dum Z
    have := recv_sub_sends hF1 hF2 h2ks Z
    omega
  -- initial roles
  set sched0 := schedInit rd (Δ0 - Q') with hsched0
  set free0 := freeInit σ0 rs0 Q' with hfree0
  have hsum_role : ∀ Q y, sched0 Q y + (∑ j ∈ range Q', ind (rsN rs0 j) Q y) =
      demand σ0 Q y := by
    intro Q y
    have e1 := hsplit (fun r => ind r Q y)
    have e2 := hord (fun r => ind r Q y)
    beta_reduce at e1 e2
    rw [← cnt_ind, e1, hsched0, schedInit, e2]
    ring
  have hle : ∀ Q y, sched0 Q y + free0 Q y ≤ σ0.cnt Q y := by
    intro Q y
    have := hsum_role Q y
    simp only [hfree0, freeInit]
    by_cases hQy : Q = y
    · subst hQy
      rw [demand_diag] at this
      simp only [if_true]
      have := min_le_left (σ0.cnt Q Q) (Q' - realInit rs0 Q' Q)
      omega
    · rw [if_neg hQy]
      simp only [demand, if_neg hQy] at this
      omega
  have hge : ∀ Q y, y ≠ Q → σ0.cnt Q y ≤ sched0 Q y + free0 Q y := by
    intro Q y hy
    have := hsum_role Q y
    have hQy : Q ≠ y := Ne.symm hy
    simp only [hfree0, freeInit, if_neg hQy]
    simp only [demand, if_neg hQy] at this
    omega
  -- the run
  set G00 := G0 σ0 sched0 free0 with hG00
  set Gf := runRounds s rd (Δ0 - Q') G00 with hGf
  obtain ⟨i1, i2, i3⟩ := runRounds_consistent s rd G00 rfl (Δ0 - Q')
  have hcons : Consistent (planRs rs0 Q') σo Gf.ins := by
    refine ⟨i2, i1, fun τ hτ => ?_⟩
    have := i3 τ hτ
    have e : rd τ = planRs rs0 Q' (σo ⟨τ, hτ⟩) := by rw [hrd]; simp [ordRd, hτ]
    rw [e] at this
    exact this
  obtain ⟨N, hNsum, hN⟩ := hσo Gf.ins hcons
  -- the context
  let c : Ctx k := ⟨s, σ0, (∑ Q, ∑ y, free0 Q y) + junkCnt s σ0, fun Z => ∑ y, free0 Z y, N,
    ∑ S, ∑ D, sched0 S D, Gf.ins, rd, Δ0 - Q', fun _ => sqCorridor k s + 1⟩
  have hNk : ∀ Z, ∑ x, (N Z x + 1) = (∑ x, N Z x) + k * k := by
    intro Z; simp [sum_add_distrib, Fintype.card_prod]
  have hcOK : c.OK := by
    refine ⟨hroom, hN, ?_, hdum_plan⟩
    intro hpos Z
    have hpos' : 0 < Δ0 - Q' := hpos
    have hQ : Q' = Rhub (k * s) + 8 * k * s + 10 := by
      rw [hQ']; exact min_eq_right (by omega)
    show (∑ x, (N Z x + 1)) + (sqCorridor k s + 1) + 3 ≤ ∑ y, free0 Z y
    rw [hNk]
    have hNZ := hNsum Z
    have htri : ∑ j ∈ range Q', ((if (rsN rs0 j).real Z then 1 else 0) +
        dummyAt (rsN rs0 j) Z + (if (rsN rs0 j).perm Z = Z then 1 else 0)) = Q' := by
      simp [trichotomy]
    rw [sum_add_distrib, sum_add_distrib] at htri
    have hd1 := hsplit (fun r => dummyAt r Z)
    have hd2 := hsplit (fun r => if r.perm Z = Z then 1 else 0)
    beta_reduce at hd1 hd2
    have hd3 := cnt_dum Z
    have hd4 := cnt_loop Z
    have hd5 := recv_sub_sends hF1 hF2 h2ks Z
    have hd6 := sends_eq hF1 Z
    have hf : ∑ y, free0 Z y = (∑ j ∈ range Q', if (rsN rs0 j).real Z then 1 else 0) +
        min (σ0.cnt Z Z) (Q' - realInit rs0 Q' Z) := by
      rw [hfree0, sum_freeInit]; rfl
    have hreal : realInit rs0 Q' Z = ∑ j ∈ range Q', if (rsN rs0 j).real Z then 1 else 0 := rfl
    have hrealle := realInit_le rs0 Q' Z
    rw [hf]
    have hmax := le_max_left (sends (demand σ0) Z) (recv (demand σ0) Z)
    have hkk : k * k ≤ k * s := Nat.mul_le_mul_left _ hks
    have h8 : 8 * k * s = 8 * (k * s) := by ring
    have h2 : 2 * k * s = 2 * (k * s) := by ring
    have hmin := min_le_left (σ0.cnt Z Z) (Q' - realInit rs0 Q' Z)
    have hmin2 : min (σ0.cnt Z Z) (Q' - realInit rs0 Q' Z) = σ0.cnt Z Z ∨
        min (σ0.cnt Z Z) (Q' - realInit rs0 Q' Z) = Q' - realInit rs0 Q' Z := by
      rcases le_total (σ0.cnt Z Z) (Q' - realInit rs0 Q' Z) with h | h
      · left; exact min_eq_left h
      · right; exact min_eq_right h
    split_ifs at hd6 <;> omega
  have hO0 : Outer c 0 G00 := by
    refine ⟨Nat.zero_le _, G0_linv s σ0 sched0 free0 hle hge,
      G0_hinv s σ0 sched0 free0 _ (fun _ => rfl) N, ?_, ?_, ?_, ?_⟩
    · intro S D; simp [hG00, G0, hsched0, schedInit, c]
    · intro Z; simp [hG00, G0]
    · intro Z; simp [hG00, G0]
    · simp [hG00, G0]
  have hOf : Outer c (Δ0 - Q') Gf := Outer.all hcOK hO0 rfl _ le_rfl
  refine ⟨Gf.evs, hOf.lin.valid, ?_, ?_⟩
  · -- cost
    have hcost : IState.totalCost s σ0 Gf.evs + pot s Gf.σ ≤ pot s σ0 +
        2 * hopC k s * (∑ Z, Gf.served Z) + (s + 3) * (39 * k + 15) * (∑ h, ∑ x, Gf.byp h x) +
        (s + 3) * Gf.wt := hOf.hin.cost
    have hss : (∑ Z, Gf.served Z) + (∑ S, ∑ D, Gf.sched S D) = ∑ S, ∑ D, sched0 S D :=
      hOf.hin.sched_sum
    have hS0 : ∑ S, ∑ D, sched0 S D ≤ (k * s) ^ 2 := by
      have : ∀ S, ∑ D, sched0 S D ≤ s ^ 2 := by
        intro S
        refine le_trans (sum_le_sum fun D _ => ?_) (hsends S)
        have := hsum_role S D
        omega
      refine (sum_le_sum fun S _ => this S).trans ?_
      simp [Fintype.card_prod]; ring_nf; exact le_refl _
    have hserved : ∑ Z, Gf.served Z ≤ (k * s) ^ 2 := by
      omega
    have hbyp : ∑ h, ∑ x, Gf.byp h x ≤ k ^ 2 * (Rhub (k * s) + k ^ 2) := by
      have : ∀ h, ∑ x, Gf.byp h x ≤ Rhub (k * s) + k * k := by
        intro h
        refine (sum_le_sum fun x _ => hOf.hin.byp_le h x).trans ?_
        rw [hNk]; have := hNsum h; omega
      refine (sum_le_sum fun h _ => this h).trans ?_
      simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
      unfold Rhub; ring_nf; exact le_refl _
    have hwt : Gf.wt ≤ s ^ 2 * (66 * k ^ 2 + 132 * k + 30) +
        (78 * k + 30) * (k ^ 2 * (2 * k * s + 1)) := by
      refine hOf.wt.trans ?_
      have hdc : ∀ r : Round k, (univ.filter fun S => r.isDummy S).card = ∑ S, dummyAt r S := by
        intro r; rw [card_filter]; rfl
      simp only [roundW, hdc, sum_add_distrib, sum_const, card_range, smul_eq_mul, ← mul_sum]
      rw [sum_comm]
      have h1 : ∑ S : Sq k, ∑ τ ∈ range (Δ0 - Q'), dummyAt (rd τ) S ≤
          ∑ _S : Sq k, (sqCorridor k s + 1) := sum_le_sum fun S _ => hdum_plan S
      simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul] at h1
      have h2 : (Δ0 - Q') * (66 * k ^ 2 + 132 * k + 30) ≤ s ^ 2 * (66 * k ^ 2 + 132 * k + 30) :=
        Nat.mul_le_mul_right _ (by omega)
      have h3 : (78 * k + 30) * (k * k * (sqCorridor k s + 1)) ≤
          (78 * k + 30) * (k ^ 2 * (2 * k * s + 1)) := by
        refine Nat.mul_le_mul_left _ ?_
        rw [sq]; exact Nat.mul_le_mul_left _ (by omega)
      have h4 : (78 * k + 30) * ∑ S : Sq k, ∑ τ ∈ range (Δ0 - Q'), dummyAt (rd τ) S ≤
          (78 * k + 30) * (k * k * (sqCorridor k s + 1)) := Nat.mul_le_mul_left _ h1
      nlinarith
    have hpot : pot s σ0 ≤ 4 * k ^ 2 * (k * s) * (k * s) :=
      (pot_le s σ0).trans (Nat.mul_le_mul_right _ (junkCnt_le s σ0))
    have ht1 := Nat.mul_le_mul_left (2 * (55 * s + 13 * k ^ 2 + 65 * k + 78)) hserved
    have ht2 := Nat.mul_le_mul_left ((s + 3) * (39 * k + 15)) hbyp
    have ht3 := Nat.mul_le_mul_left (s + 3) hwt
    unfold transportBound hopC at *
    nlinarith only [hcost, hpot, ht1, ht2, ht3, Nat.zero_le (pot s Gf.σ)]

  · -- misplaced tiles
    rw [← hOf.lin.run_eq]
    have hsch0 : ∀ S D, Gf.sched S D = 0 := by
      intro S D
      rw [hOf.sched]
      show ∑ τ ∈ Ico (Δ0 - Q') (Δ0 - Q'), _ = 0
      simp
    have hoff : Gf.σ.offCount ≤ ∑ Q, ∑ y, (Gf.stock Q y + Gf.free Q y) := by
      unfold IState.offCount
      refine sum_le_sum fun Q _ => sum_le_sum fun y _ => ?_
      split_ifs with hy
      · exact Nat.zero_le _
      · have := hOf.lin.roles_ge Q y hy; rw [hsch0] at this; omega
    have hstock : ∀ Q y, Gf.stock Q y ≤ Gf.out Q y + Gf.byp Q y := by
      intro Q y
      by_cases h : Gf.stock Q y = 0
      · omega
      · have := hOf.hin.ident Q y (hOf.lin.stock_supp Q y h); omega
    have hout : ∑ Q, ∑ y, Gf.out Q y ≤ k ^ 2 * (k * s) := by
      have : ∀ Q, ∑ y, Gf.out Q y ≤ k * s := fun Q => by
        have : (∑ x, Gf.out Q x) + noneCnt s (gh s Gf) Q ≤ (k - 1) * s := hOf.lin.out_le Q
        have : (k - 1) * s ≤ k * s := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
        omega
      refine (sum_le_sum fun Q _ => this Q).trans ?_
      simp [Fintype.card_prod]; ring_nf; exact le_refl _
    have hbyp : ∑ h, ∑ x, Gf.byp h x ≤ k ^ 2 * (Rhub (k * s) + k ^ 2) := by
      have : ∀ h, ∑ x, Gf.byp h x ≤ Rhub (k * s) + k * k := by
        intro h
        refine (sum_le_sum fun x _ => hOf.hin.byp_le h x).trans ?_
        rw [hNk]; have := hNsum h; omega
      refine (sum_le_sum fun h _ => this h).trans ?_
      simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
      unfold Rhub; ring_nf; exact le_refl _
    have hfree : ∑ Q, ∑ y, Gf.free Q y ≤
        k ^ 2 * (Rhub (k * s) + 8 * (k * s) + 10) +
          4 * k ^ 2 * (k * s) := by
      have h1 := hOf.lin.free_junk
      have h2 := junkCnt_le s σ0
      have h3 : ∑ Q, ∑ y, free0 Q y ≤ ∑ _Q : Sq k, Q' :=
        sum_le_sum fun Q _ => sum_freeInit_le σ0 rs0 Q' Q
      simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul] at h3
      have h4 : k * k * Q' ≤ k ^ 2 * (Rhub (k * s) +
          8 * (k * s) + 10) := by
        rw [sq]; refine Nat.mul_le_mul_left _ ?_
        have : 8 * k * s = 8 * (k * s) := by ring
        omega
      have : junkCnt s Gf.σ ≥ 0 := Nat.zero_le _
      show _ ≤ _
      have h5 : (∑ Q, ∑ y, Gf.free Q y) + junkCnt s Gf.σ ≤
          (∑ Q, ∑ y, free0 Q y) + junkCnt s σ0 := h1
      omega
    have hsplit2 : ∑ Q, ∑ y, (Gf.stock Q y + Gf.free Q y) =
        (∑ Q, ∑ y, Gf.stock Q y) + ∑ Q, ∑ y, Gf.free Q y := by
      simp [sum_add_distrib]
    have hst2 : ∑ Q, ∑ y, Gf.stock Q y ≤ (∑ Q, ∑ y, Gf.out Q y) + ∑ Q, ∑ y, Gf.byp Q y := by
      rw [← sum_add_distrib]
      refine sum_le_sum fun Q _ => ?_
      rw [← sum_add_distrib]
      exact sum_le_sum fun y _ => hstock Q y
    unfold misplacedBound
    omega

end SlidingPuzzle.Hub
