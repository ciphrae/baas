import SlidingPuzzle.Port.Asymp

/-! # Wide hierarchies: error `O(n^(5/2) ln n / ln ln n)`

The cheap hops cost `O(σ) = O(√n)` whatever the branching, so the lane budget `q ≤ 2λ`
of the tree grids is no longer needed: any hierarchy with `8 q K² ≤ n` and `16 λ K² ≤ n`
gives the bound `278 K² (n/K)³` apart from the hops. With `m` levels of branching `b` and
one free level `d ∈ [b, b²)`, chosen maximal, the grid is within a factor `2` of
`(8q + 16λ) K² = n`, the depth is at most `ln n / (2 ln b)` and `q < m b + b²`.
Taking `b ≈ √(ln n)` balances the hops (`ln n / ln b`) against the lanes (`√q`). -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle
open SlidingPuzzle.Tree

/-- The port bound for any mixed hierarchy with `8 q K² ≤ n` and `16 λ K² ≤ n`. -/
theorem port_le_budget_wide {n h : ℕ} [NeZero n] (hn : 2 ^ 23 ≤ n) (B : ℕ → ℕ)
    (hB : ∀ ℓ, 2 ≤ B ℓ) (hh : 1 ≤ h)
    (hke : Even (HierMix.sz B h 0)) (hqe : Even (HierMix.nq B h))
    (hq14 : 14 ≤ HierMix.nq B h) (hK : 64 ≤ HierMix.sz B h 0)
    (hlo : 16 * GroupedOrder.lamN n * HierMix.sz B h 0 ^ 2 ≤ n)
    (hq8 : 8 * HierMix.nq B h * HierMix.sz B h 0 ^ 2 ≤ n) (Bd : ReachableBoard n) :
    optimalLength Bd ≤ manhattan Bd.val +
      2 * ((15 * n ^ 2 + 3002 * n + 1) * HierMix.sz B h 0) +
      2 * (278 * (HierMix.sz B h 0 ^ 2 * (n / HierMix.sz B h 0) ^ 3) +
        hopKc (HierMix.sz B h 0) (portSide n (HierMix.sz B h 0) (HierMix.nq B h)
          (GroupedOrder.lamN n)) *
          (2 * h * (HierMix.sz B h 0 * (n / HierMix.sz B h 0)) ^ 2)) := by
  set K := HierMix.sz B h 0 with hKd
  set q := HierMix.nq B h with hqd
  set lam := GroupedOrder.lamN n with hlam
  have hl72 : 72 ≤ lam := lam_ge hn
  have hqK : q ≤ K := HierMix.nq_le_sz hB
  obtain ⟨-, -, h9, h8, hσ⟩ := portSide_facts (q := q) hn hl72 hqK hK hlo
  have hhk : 2 * h + 1 ≤ K := by
    rcases Nat.lt_or_ge h 32 with h1 | h1
    · omega
    · exact le_trans (two_mul_succ_le_pow h (by omega)) (sz_ge_pow hB)
  have hK2 : 16 * K * lam * K ≤ n := by
    have e : 16 * K * lam * K = 16 * lam * K ^ 2 := by ring
    omega
  have hlo8 : 8 * K * q * K ≤ n := by
    have e : 8 * K * q * K = 8 * q * K ^ 2 := by ring
    omega
  have hres := optimalLength_le_port_lanes (h := h) (HierMix.sys B h hB hh) (HierMix.tight hB hh)
    rfl hh hke hqe (by omega) hqK hK (by omega) hlo8 hK2 hhk h9 h8
    (by unfold resX at hσ; exact hσ) Bd
  rw [← hKd, ← hqd] at hres
  set s := n / K with hs
  have hK0 : 0 < K := by omega
  have h8s : 8 * K * q ≤ s := by
    rw [hs, Nat.le_div_iff_mul_le hK0]; exact hlo8
  have hV : 8 * (848 * (K ^ 3 * q * s ^ 2)) ≤ 848 * (K ^ 2 * s ^ 3) := by
    have := Nat.mul_le_mul_left (848 * (K ^ 2 * s ^ 2)) h8s
    calc 8 * (848 * (K ^ 3 * q * s ^ 2)) = 848 * (K ^ 2 * s ^ 2) * (8 * K * q) := by ring
      _ ≤ 848 * (K ^ 2 * s ^ 2) * s := this
      _ = _ := by ring
  omega

/-! ## The grid -/

/-- `(8 q + 16 λ) K²` for `m` levels of branching `b` and a last level `d`. -/
def wideF (lam b m d : ℕ) : ℕ := (8 * (m * b + d) + 16 * lam) * (b ^ m * d) ^ 2

theorem wideF_mono_d {lam b m d d' : ℕ} (h : d ≤ d') : wideF lam b m d ≤ wideF lam b m d' := by
  unfold wideF
  apply Nat.mul_le_mul (by omega)
  exact Nat.pow_le_pow_left (Nat.mul_le_mul_left _ h) 2

theorem wideF_succ_le {lam b m : ℕ} (hb : 2 ≤ b) : wideF lam b (m + 1) b ≤ wideF lam b m (b ^ 2) := by
  unfold wideF
  have e : b ^ (m + 1) * b = b ^ m * b ^ 2 := by ring
  rw [e]
  apply Nat.mul_le_mul_right
  have : (m + 1) * b + b ≤ m * b + b ^ 2 := by
    have e2 : (m + 1) * b + b = m * b + 2 * b := by ring
    have : 2 * b ≤ b ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right _ hb
    omega
  omega

theorem wideF_ge_pow {lam b m : ℕ} : 8 * b ^ (2 * m + 3) ≤ wideF lam b m b := by
  unfold wideF
  have e : 8 * b ^ (2 * m + 3) = 8 * b * (b ^ m * b) ^ 2 := by ring
  rw [e]
  apply Nat.mul_le_mul_right
  have : b ≤ m * b + b := by omega
  omega

/-- One step of the free level costs at most a factor `2`. -/
theorem wideF_step {lam b m d : ℕ} (hd : 8 ≤ d) : wideF lam b m (d + 2) ≤ 2 * wideF lam b m d := by
  unfold wideF
  set A := 8 * (m * b + d) + 16 * lam with hA
  set P := b ^ m with hP
  have hAd : 8 * d ≤ A := by
    have : d ≤ m * b + d := by omega
    omega
  have e1 : 8 * (m * b + (d + 2)) + 16 * lam = A + 16 := by rw [hA]; ring
  rw [e1]
  have c1 : (A + 16) * d ≤ A * (d + 2) := by nlinarith
  have c2 : (d + 2) ^ 3 ≤ 2 * d ^ 3 := by
    have a1 : 8 * d ^ 2 ≤ d ^ 3 := by
      have := Nat.mul_le_mul_right (d ^ 2) hd
      calc 8 * d ^ 2 ≤ d * d ^ 2 := this
        _ = d ^ 3 := by ring
    have a2 : 12 * d + 8 ≤ 2 * d ^ 2 := by nlinarith
    have e : (d + 2) ^ 3 = d ^ 3 + 6 * d ^ 2 + 12 * d + 8 := by ring
    omega
  have c3 : (A + 16) * (d + 2) ^ 2 * d ≤ 2 * A * d ^ 2 * d := by
    calc (A + 16) * (d + 2) ^ 2 * d = (A + 16) * d * (d + 2) ^ 2 := by ring
      _ ≤ A * (d + 2) * (d + 2) ^ 2 := Nat.mul_le_mul_right _ c1
      _ = A * (d + 2) ^ 3 := by ring
      _ ≤ A * (2 * d ^ 3) := Nat.mul_le_mul_left _ c2
      _ = 2 * A * d ^ 2 * d := by ring
  have c4 : (A + 16) * (d + 2) ^ 2 ≤ 2 * A * d ^ 2 := Nat.le_of_mul_le_mul_right c3 (by omega)
  calc (A + 16) * (P * (d + 2)) ^ 2 = (A + 16) * (d + 2) ^ 2 * P ^ 2 := by ring
    _ ≤ 2 * A * d ^ 2 * P ^ 2 := Nat.mul_le_mul_right _ c4
    _ = 2 * (A * (P * d) ^ 2) := by ring

theorem lt_wideF {lam b m d : ℕ} (hb : 2 ≤ b) (hd : 1 ≤ d) : m + d < wideF lam b m d := by
  unfold wideF
  have h1 : m < 2 ^ m := Nat.lt_two_pow_self
  have h2 : 2 ^ m ≤ b ^ m := Nat.pow_le_pow_left hb m
  have h3 : b ^ m * d ≤ (b ^ m * d) ^ 2 := by
    rw [sq]; exact Nat.le_mul_self _
  have h4 : b ^ m ≤ b ^ m * d := Nat.le_mul_of_pos_right _ hd
  have h5 : d ≤ b ^ m * d := Nat.le_mul_of_pos_left _ (by positivity)
  have h6 : 8 * (m * b + d) + 16 * lam ≥ 8 := by omega
  have h7 : 8 * (b ^ m * d) ^ 2 ≤ (8 * (m * b + d) + 16 * lam) * (b ^ m * d) ^ 2 :=
    Nat.mul_le_mul_right _ h6
  omega

/-- The grid: `m` levels of branching `b`, then the largest even `d` with `wideF ≤ n`. -/
theorem exists_wide {n lam b : ℕ} (hb : 64 ≤ b) (hbe : Even b) (h0 : wideF lam b 0 b ≤ n) :
    ∃ m d : ℕ, Even d ∧ b ≤ d ∧ d < b ^ 2 ∧ wideF lam b m d ≤ n ∧ n < 2 * wideF lam b m d ∧
      8 * b ^ (2 * m + 3) ≤ n := by
  classical
  -- the number of full levels
  set m := Nat.findGreatest (fun m => wideF lam b m b ≤ n) n with hm
  have hPm : wideF lam b m b ≤ n := Nat.findGreatest_spec (P := fun m => wideF lam b m b ≤ n)
    (Nat.zero_le n) h0
  have hmn : m < n := by
    have := @lt_wideF lam b m b (by omega) (by omega); omega
  have hnm : ¬ wideF lam b (m + 1) b ≤ n :=
    Nat.findGreatest_is_greatest (P := fun m => wideF lam b m b ≤ n) (n := n) (k := m + 1)
      (by omega) (by omega)
  -- the free level `d = 2 e`
  obtain ⟨b2, hb2⟩ := hbe
  set e := Nat.findGreatest (fun e => wideF lam b m (2 * e) ≤ n) n with he
  have hb2n : b2 ≤ n := by
    have := @lt_wideF lam b m b (by omega) (by omega); omega
  have hPb : wideF lam b m (2 * b2) ≤ n := by
    have : 2 * b2 = b := by omega
    rw [this]; exact hPm
  have hbe' : b2 ≤ e := Nat.le_findGreatest hb2n hPb
  have hPe : wideF lam b m (2 * e) ≤ n :=
    Nat.findGreatest_spec (P := fun e => wideF lam b m (2 * e) ≤ n) hb2n hPb
  have hen : e < n := by
    have := @lt_wideF lam b m (2 * e) (by omega) (by omega); omega
  have hne : ¬ wideF lam b m (2 * (e + 1)) ≤ n :=
    Nat.findGreatest_is_greatest (P := fun e => wideF lam b m (2 * e) ≤ n) (n := n) (k := e + 1)
      (by omega) (by omega)
  refine ⟨m, 2 * e, even_two_mul e, by omega, ?_, hPe, ?_, le_trans wideF_ge_pow hPm⟩
  · by_contra hc
    push Not at hc
    have := wideF_mono_d (lam := lam) (b := b) (m := m) hc
    have := wideF_succ_le (lam := lam) (m := m) (show 2 ≤ b by omega)
    omega
  · have e2 : 2 * (e + 1) = 2 * e + 2 := by ring
    rw [e2] at hne
    have := wideF_step (lam := lam) (b := b) (m := m) (show 8 ≤ 2 * e by omega)
    omega

/-- The port bound on the wide grid of branching `b`. -/
theorem port_wide {n b : ℕ} [NeZero n] (hn : 2 ^ 23 ≤ n) (hb : 64 ≤ b) (hbe : Even b)
    (h0 : wideF (GroupedOrder.lamN n) b 0 b ≤ n) (Bd : ReachableBoard n) :
    ∃ h K q σ : ℕ, 1 ≤ h ∧ 64 ≤ K ∧ 16 * GroupedOrder.lamN n * K ^ 2 ≤ n ∧
      n < 2 * ((8 * q + 16 * GroupedOrder.lamN n) * K ^ 2) ∧ q < h * b + b ^ 2 ∧
      8 * b ^ (2 * h + 1) ≤ n ∧ σ * σ ≤ 13 * n ∧
      optimalLength Bd ≤ manhattan Bd.val + 2 * ((15 * n ^ 2 + 3002 * n + 1) * K) +
        2 * (278 * (K ^ 2 * (n / K) ^ 3) + hopKc K σ * (2 * h * (K * (n / K)) ^ 2)) := by
  set lam := GroupedOrder.lamN n with hlam
  obtain ⟨m, d, hde, hbd, hdb, hf, hf2, hpow⟩ := exists_wide hb hbe h0
  set B := Bfree b 0 d m with hBd
  have hB : ∀ ℓ, 2 ≤ B ℓ := Bfree_ge (by omega) (by omega)
  have hsz : HierMix.sz B (m + 1) 0 = b ^ m * d := by
    rw [hBd, sz_Bfree (Nat.zero_le m)]; simp
  have hnq : HierMix.nq B (m + 1) = m * b + d := by
    rw [hBd, nq_Bfree (Nat.zero_le m)]; simp
  have hqK : m * b + d ≤ b ^ m * d := by
    have := HierMix.nq_le_sz (h := m + 1) hB; rw [hsz, hnq] at this; exact this
  have hK : 64 ≤ b ^ m * d := by
    have : d ≤ b ^ m * d := Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hF : wideF lam b m d = (8 * (m * b + d) + 16 * lam) * (b ^ m * d) ^ 2 := rfl
  have hlo : 16 * lam * (b ^ m * d) ^ 2 ≤ n := by
    have := Nat.mul_le_mul_right ((b ^ m * d) ^ 2) (show 16 * lam ≤ 8 * (m * b + d) + 16 * lam by omega)
    omega
  have hq8 : 8 * (m * b + d) * (b ^ m * d) ^ 2 ≤ n := by
    have := Nat.mul_le_mul_right ((b ^ m * d) ^ 2)
      (show 8 * (m * b + d) ≤ 8 * (m * b + d) + 16 * lam by omega)
    omega
  have hres := port_le_budget_wide (h := m + 1) hn B hB (by omega) (by rw [hsz]; exact hde.mul_left _)
    (by rw [hnq]; exact (hbe.mul_left m).add hde) (by have := hnq; omega) (by rw [hsz]; exact hK)
    (by rw [hsz]; exact hlo) (by rw [hnq, hsz]; exact hq8) Bd
  rw [hsz, hnq] at hres
  obtain ⟨-, hσ, -⟩ := portSide_facts (q := m * b + d) hn (lam_ge hn) hqK hK hlo
  refine ⟨m + 1, b ^ m * d, m * b + d, _, by omega, hK, hlo, by rw [← hF]; exact hf2, ?_, ?_,
    hσ, hres⟩
  · have : m * b + b ^ 2 ≤ (m + 1) * b + b ^ 2 := by
      have e : (m + 1) * b = m * b + b := by ring
      omega
    omega
  · have e : 2 * (m + 1) + 1 = 2 * m + 3 := by ring
    rw [e]; exact hpow

/-! ## Branching `b = 2 ⌊√(log₂ n)⌋` -/

theorem sqrt_branch {E : ℕ} (hE : 1024 ≤ E) :
    64 ≤ 2 * Nat.sqrt E ∧ E + 1 ≤ (2 * Nat.sqrt E) ^ 2 ∧ (2 * Nat.sqrt E) ^ 2 ≤ 4 * E := by
  set r := Nat.sqrt E with hr
  have h1 : r * r ≤ E := Nat.sqrt_le E
  have h2 : E < (r + 1) * (r + 1) := Nat.lt_succ_sqrt E
  have h3 : 32 ≤ r := Nat.le_sqrt.2 (by omega)
  refine ⟨by omega, ?_, ?_⟩
  · nlinarith
  · nlinarith

theorem sq_le_two_pow (E : ℕ) (hE : 20 ≤ E) : 400 * E ^ 2 ≤ 2 ^ E := by
  induction E, hE using Nat.le_induction with
  | base => norm_num
  | succ E hE ih =>
    have : (E + 1) ^ 2 ≤ 2 * E ^ 2 := by nlinarith
    have e : 2 ^ (E + 1) = 2 * 2 ^ E := by ring
    omega

theorem wide_start {E b : ℕ} (hE : 1024 ≤ E) (hb : b ^ 2 ≤ 4 * E) :
    wideF (3 * (E + 1)) b 0 b ≤ 2 ^ E := by
  unfold wideF
  have hbb : b ≤ b ^ 2 := by rw [sq]; exact Nat.le_mul_self b
  have e : (8 * (0 * b + b) + 16 * (3 * (E + 1))) * (b ^ 0 * b) ^ 2 =
      (8 * b + 48 * E + 48) * b ^ 2 := by ring
  rw [e]
  have h1 : (8 * b + 48 * E + 48) * b ^ 2 ≤ (100 * E) * (4 * E) :=
    Nat.mul_le_mul (by omega) hb
  have h2 := sq_le_two_pow E (by omega)
  have e2 : 100 * E * (4 * E) = 400 * E ^ 2 := by ring
  omega

/-- `557 t ≤ 1.04 e^(t/4)` for `t ≥ 40`. -/
theorem exp_quarter_ge {t : ℝ} (ht : 40 ≤ t) : 557 * t ≤ 1.04 * Real.exp (t / 4) := by
  have h10 : (22026 : ℝ) ≤ Real.exp 10 := by
    have := Real.exp_one_gt_d9
    have h : (2.7182818283 : ℝ) ^ 10 ≤ Real.exp 1 ^ 10 :=
      pow_le_pow_left₀ (by norm_num) this.le 10
    rw [Real.exp_one_pow] at h
    norm_num at h ⊢
    linarith
  have hsplit : Real.exp (t / 4) = Real.exp 10 * Real.exp ((t - 40) / 4) := by
    rw [← Real.exp_add]; ring_nf
  have h1 := Real.add_one_le_exp ((t - 40) / 4)
  rw [hsplit]
  have h2 : 22026 * ((t - 40) / 4 + 1) ≤ Real.exp 10 * Real.exp ((t - 40) / 4) :=
    mul_le_mul h10 h1 (by linarith) (by positivity)
  linarith

theorem depth_mul_le {hr lb L l8 : ℝ} (h : l8 + (2 * hr + 1) * lb ≤ L) (h8 : 0 ≤ l8)
    (hlb : 0 ≤ lb) : hr * (2 * lb) ≤ L := by nlinarith

/-- The coefficient: `1 + 556 W³ + 240.96 h ≤ 242 L / t` for `W = e^(t/4)`, `W⁴ = L`. -/
theorem coef_le {W t L hr : ℝ} (ht40 : 40 ≤ t) (hW : W = Real.exp (t / 4)) (hW4 : W ^ 4 = L)
    (hht : hr * t ≤ L) : 1 + 2 * 278 * W ^ 3 + 2 * 120.48 * hr ≤ 242 * L / t := by
  have ht0 : 0 < t := by linarith
  rw [le_div_iff₀ ht0]
  have hq1 := exp_quarter_ge ht40
  rw [← hW] at hq1
  have hW1 : 1 ≤ W := by rw [hW]; exact Real.one_le_exp (by linarith)
  have hW3 : 1 ≤ W ^ 3 := one_le_pow₀ hW1
  have a1 : t ≤ t * W ^ 3 := by nlinarith
  have a2 : 557 * t * W ^ 3 ≤ 1.04 * W * W ^ 3 := by
    have := mul_le_mul_of_nonneg_right hq1 (show 0 ≤ W ^ 3 by positivity)
    linarith
  have e4 : 1.04 * W * W ^ 3 = 1.04 * L := by rw [← hW4]; ring
  have e : (1 + 2 * 278 * W ^ 3 + 2 * 120.48 * hr) * t =
      t + 556 * (t * W ^ 3) + 240.96 * (hr * t) := by ring
  rw [e]
  have e2 : 557 * t * W ^ 3 = 557 * (t * W ^ 3) := by ring
  linarith

set_option maxHeartbeats 1000000 in
/-- The bound of `port_loglog`, for `2⁶⁰ ≤ log₂ n`. -/
theorem port_loglog_log {n : ℕ} [NeZero n] (hE60 : 2 ^ 60 ≤ Nat.log 2 n) (Bd : ReachableBoard n) :
    (optimalLength Bd : ℝ) ≤ (manhattan Bd.val : ℝ) +
      242 * (n : ℝ) ^ ((5 : ℝ) / 2) * Real.log n / Real.log (Real.log n) := by
  set E := Nat.log 2 n with hE
  have hEn : 2 ^ E ≤ n := Nat.pow_log_le_self 2 (NeZero.ne n)
  have hn23 : 2 ^ 23 ≤ n :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (le_trans (by norm_num) hE60)) hEn
  have hnE : n < 2 ^ (E + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hE1024 : 1024 ≤ E := le_trans (by norm_num) hE60
  set b := 2 * Nat.sqrt E with hbd
  obtain ⟨hb64, hbE1, hbE4⟩ := sqrt_branch hE1024
  have hlamE : GroupedOrder.lamN n = 3 * (E + 1) := rfl
  have h0 : wideF (GroupedOrder.lamN n) b 0 b ≤ n := by
    rw [hlamE]; exact le_trans (wide_start hE1024 hbE4) hEn
  obtain ⟨h, K, q, σ, hh, hK64, hlo, hhi, hq, hpow, hσ, hnat⟩ :=
    port_wide hn23 hb64 (even_two_mul _) h0 Bd
  set lam := GroupedOrder.lamN n with hlam
  have hl72 : 72 ≤ lam := lam_ge hn23
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn23
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set nr : ℝ := (n : ℝ) with hnr
  set Kr : ℝ := (K : ℝ) with hKr
  set sr : ℝ := (σ : ℝ) with hsr
  set hr : ℝ := (h : ℝ) with hhr
  set br : ℝ := (b : ℝ) with hbr
  set Er : ℝ := (E : ℝ) with hEr
  set Ar : ℝ := 8 * (q : ℝ) + 16 * (lam : ℝ) with hAr
  have hKpos : 0 < Kr := by rw [hKr]; exact_mod_cast (show 0 < K by omega)
  have hl64 : (64 : ℝ) ≤ (lam : ℝ) := by exact_mod_cast (show 64 ≤ lam by omega)
  have hloR : 16 * (lam : ℝ) * Kr ^ 2 ≤ nr := by rw [hKr, hnr]; exact_mod_cast hlo
  have hhiR : nr < 2 * (Ar * Kr ^ 2) := by
    rw [hAr, hKr, hnr]; exact_mod_cast hhi
  have hσR : sr * sr ≤ 13 * nr := by rw [hsr, hnr]; exact_mod_cast hσ
  have hsr0 : 0 ≤ sr := by rw [hsr]; exact Nat.cast_nonneg _
  have hhr1 : (1 : ℝ) ≤ hr := by rw [hhr]; exact_mod_cast hh
  -- the natural bound, cast
  have hcast : (optimalLength Bd : ℝ) ≤ (manhattan Bd.val : ℝ) +
      2 * ((15 * nr ^ 2 + 3002 * nr + 1) * Kr) +
      2 * (278 * (Kr ^ 2 * ((n / K : ℕ) : ℝ) ^ 3) +
        (12 * sr + 526 * Kr + 1535) * (2 * hr * (Kr * ((n / K : ℕ) : ℝ)) ^ 2)) := by
    have := (Nat.cast_le (α := ℝ)).2 hnat
    unfold hopKc at this
    push_cast at this
    rw [hnr, hKr, hsr, hhr]
    exact this
  -- logarithms: `L = ln n`, `t = ln L`, `W = e^(t/4)`
  set L := Real.log nr with hL
  have hlog2 := Real.log_two_gt_d9
  have hlog2' := Real.log_two_lt_d9
  have hEL : Er * Real.log 2 ≤ L := by
    have : ((2 : ℝ) ^ E) ≤ nr := by rw [hnr]; exact_mod_cast hEn
    have := Real.log_le_log (by positivity) this
    rwa [Real.log_pow] at this
  have hLE : L ≤ (Er + 1) * Real.log 2 := by
    have : nr ≤ ((2 : ℝ) ^ (E + 1)) := by rw [hnr]; exact_mod_cast hnE.le
    have := Real.log_le_log hn0 this
    rw [Real.log_pow] at this; push_cast at this; exact this
  have hE60R : (2 : ℝ) ^ 60 ≤ Er := by rw [hEr]; exact_mod_cast hE60
  have hLbig : (10 : ℝ) ^ 12 ≤ L := by
    have : (2 : ℝ) ^ 60 * 0.6931471803 ≤ Er * Real.log 2 :=
      mul_le_mul hE60R hlog2.le (by norm_num) (by positivity)
    norm_num at this; linarith
  have hL0 : 0 < L := by linarith
  set t := Real.log L with ht
  have ht40 : 40 ≤ t := by
    rw [ht, Real.le_log_iff_exp_le hL0]
    have := Real.exp_one_lt_d9
    have h : Real.exp 1 ^ 40 ≤ (2.7182818286 : ℝ) ^ 40 := pow_le_pow_left₀ (by positivity) this.le 40
    rw [Real.exp_one_pow] at h
    norm_num at h
    nlinarith
  set W := Real.exp (t / 4) with hW
  have hW0 : 0 < W := Real.exp_pos _
  have hW4 : W ^ 4 = L := by
    rw [hW, ← Real.exp_nat_mul]; push_cast
    rw [show (4 : ℝ) * (t / 4) = t by ring, ht, Real.exp_log hL0]
  have hsqL : Real.sqrt L = W ^ 2 := by
    rw [← hW4, show W ^ 4 = (W ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hW1 : 1 ≤ W := by
    rw [hW]; exact Real.one_le_exp (by linarith)
  -- the branching: `L ≤ b²`, `b² ≤ 4E`, so `t ≤ 2 ln b`
  have hbE1R : Er + 1 ≤ br ^ 2 := by rw [hEr, hbr]; exact_mod_cast hbE1
  have hbE4R : br ^ 2 ≤ 4 * Er := by rw [hEr, hbr]; exact_mod_cast hbE4
  have hb0 : (64 : ℝ) ≤ br := by rw [hbr]; exact_mod_cast hb64
  have hLb : L ≤ br ^ 2 := by
    have h1 : (Er + 1) * Real.log 2 ≤ Er + 1 :=
      mul_le_of_le_one_right (by positivity) (by linarith)
    linarith
  have htb : t ≤ 2 * Real.log br := by
    have := Real.log_le_log hL0 hLb
    rw [Real.log_pow] at this; push_cast at this; exact this
  -- the depth: `h t ≤ L`
  have hht : hr * t ≤ L := by
    have hp : 8 * br ^ (2 * h + 1) ≤ nr := by rw [hbr, hnr]; exact_mod_cast hpow
    have := Real.log_le_log (by positivity) hp
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at this
    have hl8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    have hlb : 0 ≤ Real.log br := Real.log_nonneg (by linarith)
    push_cast at this
    have : hr * (2 * Real.log br) ≤ L := depth_mul_le this hl8 hlb
    calc hr * t ≤ hr * (2 * Real.log br) := mul_le_mul_of_nonneg_left htb (by linarith)
      _ ≤ L := this
  have ht0 : 0 < t := by linarith
  have hhL : hr ≤ L / 40 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  -- the lane count: `2 A ≤ L √L = W⁶`
  have hqR : (q : ℝ) ≤ hr * br + br ^ 2 := by
    have : (q : ℝ) < hr * br + br ^ 2 := by rw [hhr, hbr]; exact_mod_cast hq
    exact this.le
  have hlamR : (lam : ℝ) = 3 * (Er + 1) := by
    have := hlamE; rw [hEr]; exact_mod_cast this
  have hEL' : Er ≤ 1.4428 * L := by
    have : Er * 0.6931471803 ≤ Er * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlog2.le (by positivity)
    linarith
  have hsqLbig : (10 : ℝ) ^ 6 ≤ Real.sqrt L := by
    rw [show (10 : ℝ) ^ 6 = Real.sqrt ((10 ^ 6) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have hbL : br ≤ 2.4024 * Real.sqrt L := by
    rw [← Real.sqrt_sq (show 0 ≤ br by linarith)]
    rw [show (2.4024 : ℝ) = Real.sqrt (2.4024 ^ 2) by rw [Real.sqrt_sq (by norm_num)],
      ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hsq2 : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
  have hA : 2 * Ar ≤ W ^ 6 := by
    have e6 : W ^ 6 = L * Real.sqrt L := by rw [hsqL, ← hW4]; ring
    rw [e6, hAr, hlamR]
    have hhb : hr * br ≤ L / 40 * (2.4024 * Real.sqrt L) :=
      mul_le_mul hhL hbL (by linarith) (by positivity)
    have h1 : 230.9 * L + 96 ≤ 0.039 * (L * Real.sqrt L) := by nlinarith
    nlinarith
  -- `√n ≤ W³ K`
  have hsn : 0 ≤ Real.sqrt nr := Real.sqrt_nonneg _
  have hsq_n : Real.sqrt nr ^ 2 = nr := Real.sq_sqrt hn0.le
  have hup : Real.sqrt nr ≤ W ^ 3 * Kr := by
    rw [Real.sqrt_le_left (by positivity)]
    have : 2 * (Ar * Kr ^ 2) ≤ W ^ 6 * Kr ^ 2 := by
      have := mul_le_mul_of_nonneg_right hA (sq_nonneg Kr)
      linarith
    nlinarith
  -- as in `port_optimalLength_le`
  set P : ℝ := nr ^ ((5 : ℝ) / 2) with hP
  have hPe : P = nr ^ 2 * Real.sqrt nr := by
    rw [hP, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hn0]; norm_num
  have hnbig : (8388608 : ℝ) ≤ nr := by
    have c : ((8388608 : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 (by norm_num at hn23 ⊢; exact hn23)
    rw [hnr]; exact_mod_cast c
  have hP0 : 0 ≤ P := by rw [hPe]; positivity
  have hdown : 32 * Kr ≤ Real.sqrt nr := by
    rw [show 32 * Kr = Real.sqrt ((32 * Kr) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    have := mul_le_mul_of_nonneg_right hl64 (sq_nonneg Kr)
    linarith
  have hσn : sr ≤ 3.6056 * Real.sqrt nr := by
    have h1 : sr ^ 2 ≤ (3.6056 * Real.sqrt nr) ^ 2 := by
      rw [mul_pow, hsq_n, sq]; norm_num; linarith
    exact (pow_le_pow_iff_left₀ hsr0 (by positivity) two_ne_zero).1 h1
  have hn23' : (2896 : ℝ) ≤ Real.sqrt nr := by
    have : (2896 : ℝ) ^ 2 ≤ nr := by norm_num; linarith
    calc (2896 : ℝ) = Real.sqrt (2896 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ _ := Real.sqrt_le_sqrt this
  have hKc : 12 * sr + 526 * Kr + 1535 ≤ 60.24 * Real.sqrt nr := by
    have : (1535 : ℝ) ≤ 0.5301 * Real.sqrt nr := by linarith
    linarith
  set m : ℝ := ((n / K : ℕ) : ℝ) with hm
  have hm0 : 0 ≤ m := by positivity
  have hmK : m * Kr ≤ nr := by
    have : K * (n / K) ≤ n := Nat.mul_div_le n _
    have : (K : ℝ) * ((n / K : ℕ) : ℝ) ≤ n := by exact_mod_cast this
    rw [hm, hKr, hnr]; linarith
  have hmain : Kr ^ 2 * m ^ 3 ≤ W ^ 3 * P := by
    have h1 : Kr ^ 2 * m ^ 3 * Kr ≤ nr ^ 3 := by
      have := pow_le_pow_left₀ (by positivity) hmK 3
      calc Kr ^ 2 * m ^ 3 * Kr = (m * Kr) ^ 3 := by ring
        _ ≤ _ := this
    have h2 : nr ^ 3 ≤ W ^ 3 * P * Kr := by
      rw [hPe]
      have e3 : nr ^ 3 = nr ^ 2 * Real.sqrt nr * Real.sqrt nr := by
        rw [mul_assoc, ← sq, hsq_n]; ring
      rw [e3]
      have := mul_le_mul_of_nonneg_left hup (by positivity : (0 : ℝ) ≤ nr ^ 2 * Real.sqrt nr)
      calc nr ^ 2 * Real.sqrt nr * Real.sqrt nr ≤ _ := this
        _ = _ := by ring
    exact le_of_mul_le_mul_right (le_trans h1 h2) hKpos
  have hpre : 2 * ((15 * nr ^ 2 + 3002 * nr + 1) * Kr) ≤ P := by
    have hn3003 : (3003 : ℝ) ≤ nr := by linarith
    have hsq : 3003 * nr ≤ nr ^ 2 := by
      have := mul_le_mul_of_nonneg_right hn3003 hn0.le
      rw [sq]; linarith
    have ha : 15 * nr ^ 2 + 3002 * nr + 1 ≤ 16 * nr ^ 2 := by linarith
    have h1 := mul_le_mul_of_nonneg_right ha hKpos.le
    have h2 := mul_le_mul_of_nonneg_left hdown (by positivity : (0 : ℝ) ≤ nr ^ 2)
    rw [hPe]; linarith
  have hhop : (12 * sr + 526 * Kr + 1535) * (2 * hr * (Kr * m) ^ 2) ≤ 120.48 * hr * P := by
    have h1 : (Kr * m) ^ 2 ≤ nr ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) (show Kr * m ≤ nr by linarith) 2
      exact this
    have h2 : (12 * sr + 526 * Kr + 1535) * (2 * hr * (Kr * m) ^ 2) ≤
        (60.24 * Real.sqrt nr) * (2 * hr * nr ^ 2) := by
      apply mul_le_mul hKc _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [hPe]
    calc _ ≤ _ := h2
      _ = _ := by ring
  -- the coefficient: `1 + 556 W³ + 240.96 h ≤ 242 L / t`
  have hcoef := coef_le ht40 hW hW4 hht
  calc (optimalLength Bd : ℝ) ≤ _ := hcast
    _ ≤ (manhattan Bd.val : ℝ) + (1 + 2 * 278 * W ^ 3 + 2 * 120.48 * hr) * P := by
        have := mul_le_mul_of_nonneg_left hmain (show (0 : ℝ) ≤ 556 by norm_num)
        have e : (1 + 2 * 278 * W ^ 3 + 2 * 120.48 * hr) * P =
            P + 556 * (W ^ 3 * P) + 2 * (120.48 * hr * P) := by ring
        rw [e]
        linarith
    _ ≤ (manhattan Bd.val : ℝ) + (242 * L / t) * P := by
        have := mul_le_mul_of_nonneg_right hcoef hP0
        linarith
    _ = _ := by rw [hL, ht]; ring

theorem log_ge_of_pow_le {n : ℕ} : ∀ E0 : ℕ, 2 ^ 60 ≤ E0 → 2 ^ E0 ≤ n → 2 ^ 60 ≤ Nat.log 2 n :=
  fun _ h1 h2 => le_trans h1 (Nat.le_log_of_pow_le (by norm_num) h2)

/-- **`OPT(B) ≤ M(B) + 242 n^(5/2) ln n / ln ln n`** for `n ≥ 2^(2^60)`. -/
theorem port_loglog {n : ℕ} [NeZero n] (hn : 2 ^ (2 ^ 60) ≤ n) (Bd : ReachableBoard n) :
    (optimalLength Bd : ℝ) ≤ (manhattan Bd.val : ℝ) +
      242 * (n : ℝ) ^ ((5 : ℝ) / 2) * Real.log n / Real.log (Real.log n) :=
  port_loglog_log (log_ge_of_pow_le _ le_rfl hn) Bd

end SlidingPuzzle.Port
