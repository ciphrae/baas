import SlidingPuzzle.Port.Lanes
import SlidingPuzzle.Tree.LamLog
import SlidingPuzzle.Tree.LamGrid

/-! # The port algorithm on the fine mixed grid

As `Tree.optimalLength_le_fine`: the mixed hierarchy that rounds `16 λ K² ≤ n` by at most
`33/32`, with ports of side `σ = ⌊√X⌋ + 1`. The cheap hops stay apart: they cost
`hopKc K σ` per hop, with `σ² ≤ 13 n`. -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle
open SlidingPuzzle.Tree

/-- The reserve bound that the ports must exceed. -/
def resX (n k q lam : ℕ) : ℕ :=
  2 * ((2 * (n / k) + 2 * k + (15 * lam + 1) * k) * (2 * k) + 4 * k * q) + 2

/-- The port side. -/
def portSide (n k q lam : ℕ) : ℕ := Nat.sqrt (resX n k q lam) + 1

theorem sz_ge_pow {B : ℕ → ℕ} {h : ℕ} (hB : ∀ ℓ, 2 ≤ B ℓ) : 2 ^ h ≤ HierMix.sz B h 0 := by
  unfold HierMix.sz
  calc 2 ^ h = ∏ _j ∈ Ico 0 h, 2 := by simp
    _ ≤ ∏ j ∈ Ico 0 h, B j := Finset.prod_le_prod' fun j _ => hB j

theorem two_mul_succ_le_pow : ∀ h : ℕ, 3 ≤ h → 2 * h + 1 ≤ 2 ^ h
  | 3, _ => by norm_num
  | h + 4, _ => by
    have := two_mul_succ_le_pow (h + 3) (by omega)
    rw [pow_succ]; omega

/-- The sizes of the port side: `X ≤ 12 n`, `σ² ≤ 13 n` and `9 σ K ≤ n`. -/
theorem portSide_facts {n K q lam : ℕ} (hn : 2 ^ 23 ≤ n) (hl : 72 ≤ lam) (hqK : q ≤ K)
    (hK : 64 ≤ K)
    (hlo : 16 * lam * K ^ 2 ≤ n) :
    resX n K q lam ≤ 12 * n ∧ portSide n K q lam * portSide n K q lam ≤ 13 * n ∧
      9 * portSide n K q lam * K ≤ n ∧ 8 ≤ portSide n K q lam ∧
      resX n K q lam + 0 ≤ portSide n K q lam ^ 2 := by
  have hsK : n / K * K ≤ n := Nat.div_mul_le_self n K
  have hKK : 1152 * (K * K) ≤ n := by
    have : 1152 * (K * K) ≤ 16 * lam * K ^ 2 := by
      have := Nat.mul_le_mul_right (K * K) (Nat.mul_le_mul_left 16 hl)
      calc 1152 * (K * K) = 16 * 72 * (K * K) := by ring
        _ ≤ 16 * lam * (K * K) := this
        _ = _ := by ring
    omega
  have hlK : 16 * (lam * (K * K)) ≤ n := by
    have e : 16 * lam * K ^ 2 = 16 * (lam * (K * K)) := by ring
    omega
  have hX : resX n K q lam ≤ 12 * n := by
    unfold resX
    have e : 2 * ((2 * (n / K) + 2 * K + (15 * lam + 1) * K) * (2 * K) + 4 * K * q) + 2 =
        8 * (n / K * K) + 12 * (K * K) + 60 * (lam * (K * K)) + 8 * (K * q) + 2 := by ring
    have hq : K * q ≤ K * K := Nat.mul_le_mul_left _ hqK
    omega
  set X := resX n K q lam with hXd
  set r := Nat.sqrt X with hr
  have hσ : portSide n K q lam = r + 1 := rfl
  have hrX : r * r ≤ X := Nat.sqrt_le X
  have hXσ : X < (r + 1) * (r + 1) := Nat.lt_succ_sqrt X
  have hr8 : r ≤ n / 8 := by
    by_contra hc
    push Not at hc
    have : (n / 8 + 1) * (n / 8 + 1) ≤ r * r := Nat.mul_le_mul hc hc
    have : 12 * n < (n / 8 + 1) * (n / 8 + 1) := by
      have a : 96 ≤ n / 8 := by omega
      have b : 8 * (n / 8) + 8 > n := by omega
      nlinarith
    omega
  refine ⟨hX, ?_, ?_, ?_, ?_⟩
  · rw [hσ]
    have : (r + 1) * (r + 1) = r * r + 2 * r + 1 := by ring
    omega
  · rw [hσ]
    -- `117 r K ≤ 12 n` and `117 K ≤ n`
    have a1 : (117 * r * K) * (117 * r * K) ≤ (12 * n) * (12 * n) := by
      have e : (117 * r * K) * (117 * r * K) = 13689 * (r * r) * (K * K) := by ring
      rw [e]
      have b1 : 13689 * (r * r) * (K * K) ≤ 13689 * (12 * n) * (K * K) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hrX.trans hX))
      have b2 : 13689 * (12 * n) * (K * K) * 1152 ≤ 13689 * (12 * n) * n := by
        have := Nat.mul_le_mul_left (13689 * (12 * n)) hKK
        calc 13689 * (12 * n) * (K * K) * 1152 = 13689 * (12 * n) * (1152 * (K * K)) := by ring
          _ ≤ _ := this
      have b3 : 13689 * (12 * n) * n ≤ 144 * n * n * 1152 := by nlinarith
      have e2 : (12 * n) * (12 * n) = 144 * n * n := by ring
      nlinarith
    have a2 : 117 * r * K ≤ 12 * n := Nat.mul_self_le_mul_self_iff.1 a1
    have a3 : 117 * K ≤ n := by
      have : (117 * K) * (117 * K) ≤ n * n := by
        have e : (117 * K) * (117 * K) = 13689 * (K * K) := by ring
        rw [e]
        have : 13689 * (K * K) ≤ 12 * n := by omega
        nlinarith
      exact Nat.mul_self_le_mul_self_iff.1 this
    have e : 13 * (9 * (r + 1) * K) = 117 * r * K + 117 * K := by ring
    omega
  · rw [hσ]
    have hX64 : 64 ≤ X := by
      rw [hXd]; unfold resX
      have a : 2 * K * (2 * K) ≤ (2 * (n / K) + 2 * K + (15 * lam + 1) * K) * (2 * K) :=
        Nat.mul_le_mul_right _ (by omega)
      have b : 64 ≤ 2 * K * (2 * K) := by
        have := Nat.mul_le_mul (show 2 ≤ 2 * K by omega) (show 32 ≤ 2 * K by omega)
        omega
      omega
    have : 8 ≤ r := by rw [hr]; exact Nat.le_sqrt'.2 (by omega)
    omega
  · rw [hσ, sq]; omega

/-- The port bound for any mixed hierarchy within the lane budget `2λ`. -/
theorem port_le_budget {n h : ℕ} [NeZero n] (hn : 2 ^ 23 ≤ n) (B : ℕ → ℕ)
    (hB : ∀ ℓ, 2 ≤ B ℓ) (hh : 1 ≤ h)
    (hke : Even (HierMix.sz B h 0)) (hqe : Even (HierMix.nq B h))
    (hq : HierMix.nq B h ≤ 2 * GroupedOrder.lamN n) (hK : 64 ≤ HierMix.sz B h 0)
    (hlo : 16 * GroupedOrder.lamN n * HierMix.sz B h 0 ^ 2 ≤ n) (Bd : ReachableBoard n) :
    optimalLength Bd ≤ manhattan Bd.val +
      2 * ((15 * n ^ 2 + 3002 * n + 1) * HierMix.sz B h 0) +
      2 * (300 * (HierMix.sz B h 0 ^ 2 * (n / HierMix.sz B h 0) ^ 3) +
        hopKc (HierMix.sz B h 0) (portSide n (HierMix.sz B h 0) (HierMix.nq B h)
          (GroupedOrder.lamN n)) *
          (2 * h * (HierMix.sz B h 0 * (n / HierMix.sz B h 0)) ^ 2)) := by
  set K := HierMix.sz B h 0 with hKd
  set q := HierMix.nq B h with hqd
  set lam := GroupedOrder.lamN n with hlam
  have hl72 : 72 ≤ lam := lam_ge hn
  have hqK : q ≤ K := HierMix.nq_le_sz hB
  have hq2 : 2 ≤ q := by
    have e : q = ∑ ℓ ∈ range h, B ℓ := Fin.sum_univ_eq_sum_range B h
    rw [e]
    have := Finset.single_le_sum (f := B) (fun i _ => Nat.zero_le _)
      (mem_range.2 (show 0 < h by omega))
    exact le_trans (hB 0) this
  obtain ⟨hX, -, h9, h8, hσ⟩ := portSide_facts (q := q) hn hl72 hqK hK hlo
  have hhk : 2 * h + 1 ≤ K := by
    rcases Nat.lt_or_ge h 32 with h1 | h1
    · omega
    · exact le_trans (two_mul_succ_le_pow h (by omega)) (sz_ge_pow hB)
  have hK2 : 16 * K * lam * K ≤ n := by
    have e : 16 * K * lam * K = 16 * lam * K ^ 2 := by ring
    omega
  have hlo8 : 8 * K * q * K ≤ n := by
    have := Nat.mul_le_mul_right (K ^ 2) (Nat.mul_le_mul_left 8 hq)
    calc 8 * K * q * K = 8 * q * K ^ 2 := by ring
      _ ≤ 8 * (2 * lam) * K ^ 2 := this
      _ = 16 * lam * K ^ 2 := by ring
      _ ≤ n := hlo
  have hcr : 7 * (q + 2) * K * K ≤ n := by
    have : 7 * (q + 2) ≤ 16 * lam := by omega
    have := Nat.mul_le_mul_right (K ^ 2) this
    calc 7 * (q + 2) * K * K = 7 * (q + 2) * K ^ 2 := by ring
      _ ≤ 16 * lam * K ^ 2 := this
      _ ≤ n := hlo
  have h9' : 9 * portSide n K q lam * K ≤ n := h9
  exact optimalLength_le_port_lanes (h := h) (HierMix.sys B h hB hh) (HierMix.tight hB hh) rfl
    hh hke hqe hq2 hqK hK (by omega) hlo8 hK2 hhk hcr h9' h8
    (by unfold resX at hσ; exact hσ) Bd

open SlidingPuzzle.Tree.HierMix in
theorem port_fine {n : ℕ} [NeZero n] (hn : 2 ^ 23 ≤ n) (Bd : ReachableBoard n) :
    ∃ h K : ℕ, 1 ≤ h ∧ 16 * GroupedOrder.lamN n * 73 ^ (2 * (h - 1)) ≤ n ∧
      (h = 2 → 16 * GroupedOrder.lamN n * (2 * GroupedOrder.lamN n - 1) ^ 2 ≤ n) ∧ 64 ≤ K ∧
      16 * GroupedOrder.lamN n * K ^ 2 ≤ n ∧ 64 * n < 1089 * GroupedOrder.lamN n * K ^ 2 ∧
      ∃ σ : ℕ, σ * σ ≤ 13 * n ∧
      optimalLength Bd ≤ manhattan Bd.val + 2 * ((15 * n ^ 2 + 3002 * n + 1) * K) +
        2 * (300 * (K ^ 2 * (n / K) ^ 3) + hopKc K σ * (2 * h * (K * (n / K)) ^ 2)) := by
  obtain ⟨h, b, j, hh, hbe, hb8, hj, hbud, hlo, hhi, h73, htwo⟩ := exists_lam_grid hn
  set lam := GroupedOrder.lamN n with hlam
  have hl72 : 72 ≤ lam := lam_ge hn
  have hsmall : 102400 * lam ≤ n := lam_small hn
  have hh4 : 4 * h ≤ lam := by nlinarith
  have hn23 := hn
  by_cases hb64 : 64 ≤ b
  · -- the mixed grid rounds by `(b + 2)/b ≤ 33/32`
    set K := (b + 2) ^ j * b ^ (h - j) with hK
    have hround : n * b ^ 2 < 16 * lam * (K * (b + 2)) ^ 2 := by
      have e1 : (b + 2) ^ (j + 1) * b ^ (h - (j + 1)) * b = K * (b + 2) := by
        rw [hK]
        have : h - j = h - (j + 1) + 1 := by omega
        rw [this, pow_succ, pow_succ]; ring
      rw [← e1]
      have := Nat.mul_lt_mul_of_pos_right hhi (show 0 < b ^ 2 by positivity)
      calc n * b ^ 2 < _ := this
        _ = _ := by ring
    have hK64 : 64 ≤ K := by
      have h1 : 64 ≤ b ^ (h - j) := le_trans hb64 (Nat.le_self_pow (by omega) _)
      have h2 : 1 ≤ (b + 2) ^ j := Nat.one_le_pow _ _ (by omega)
      calc 64 = 1 * 64 := by norm_num
        _ ≤ K := Nat.mul_le_mul h2 h1
    have hb2 : 2 ≤ b := by omega
    have hsz := sz_Bmix (b := b) (h := h) hj.le
    have hnq := nq_Bmix (b := b) (h := h) hj.le
    have hq2l : HierMix.nq (Bmix b j) h ≤ 2 * lam := by rw [hnq]; nlinarith
    have hres := port_le_budget hn (Bmix b j) (Bmix_ge hb2 j) hh
      (by rw [hsz]; exact (hbe.pow_of_ne_zero (by omega)).mul_left _)
      (by rw [hnq]; obtain ⟨c, hc⟩ := hbe; exact ⟨h * c + j, by rw [hc]; ring⟩)
      hq2l (by rw [hsz]; exact hK64) (by rw [hsz]; exact hlo) Bd
    have hqK := HierMix.nq_le_sz (Bmix_ge hb2 j) (h := h)
    rw [hsz] at hres hqK
    obtain ⟨-, hσσ, -⟩ := portSide_facts (n := n) (lam := lam) hn23 hl72 hqK hK64 hlo
    exact ⟨h, K, hh, h73, htwo, hK64, hlo, round_fine hb64 hround, _, hσσ, hres⟩
  · push Not at hb64
    have hb62 : b ≤ 62 := by obtain ⟨r, hr⟩ := hbe; omega
    -- the grid of branching `b < 64` is below `64^h`
    have hup : n < 16 * lam * (64 ^ h) ^ 2 := by
      have h1 : (b + 2) ^ (j + 1) * b ^ (h - (j + 1)) ≤ 64 ^ (j + 1) * 64 ^ (h - (j + 1)) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _) (Nat.pow_le_pow_left (by omega) _)
      rw [← pow_add, show j + 1 + (h - (j + 1)) = h by omega] at h1
      exact lt_of_lt_of_le hhi (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 2))
    -- so the depth is at least `2`
    obtain ⟨m, rfl⟩ : ∃ m, h = m + 2 := by
      refine ⟨h - 2, ?_⟩
      by_contra hc
      have h1 : h = 1 := by omega
      rw [h1] at hup
      nlinarith
    have hm1 : m + 2 - 1 = m + 1 := by omega
    rw [hm1] at h73
    have hlamd := lam_depth (m := m + 1) (by omega) h73
    -- lowest branching `c` of the `m + 1` upper levels, sized for `K / 64`
    let Pc : ℕ → Prop := fun t => 16 * lam * (64 * (2 * t) ^ (m + 1)) ^ 2 ≤ n
    have hPc1 : Pc 1 := by
      show 16 * lam * (64 * (2 * 1) ^ (m + 1)) ^ 2 ≤ n
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        have h2 := htwo rfl
        have : 128 ≤ 2 * lam - 1 := by omega
        calc 16 * lam * (64 * (2 * 1) ^ (0 + 1)) ^ 2 = 16 * lam * 128 ^ 2 := by norm_num
          _ ≤ 16 * lam * (2 * lam - 1) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left this 2)
          _ ≤ n := h2
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        have h1 := pow2_le73 m'
        have h2 : (64 * 2 ^ (m' + 2)) ^ 2 ≤ 73 ^ (2 * (m' + 1 + 1)) := by
          rw [show 2 * (m' + 1 + 1) = (m' + 2) * 2 by ring, pow_mul]
          exact Nat.pow_le_pow_left h1 2
        calc 16 * lam * (64 * (2 * 1) ^ (m' + 1 + 1)) ^ 2 =
              16 * lam * (64 * 2 ^ (m' + 2)) ^ 2 := by norm_num
          _ ≤ 16 * lam * 73 ^ (2 * (m' + 1 + 1)) := Nat.mul_le_mul_left _ h2
          _ ≤ n := h73
    set t := Nat.findGreatest Pc n with ht
    have hPt : Pc t := Nat.findGreatest_spec (P := Pc) (by omega) hPc1
    have ht1 : 1 ≤ t := Nat.le_findGreatest (by omega) hPc1
    have htn : t < n := by
      have h1 : 2 * t ≤ (2 * t) ^ (m + 1) := Nat.le_self_pow (by omega) _
      have h2 : (2 * t) ^ (m + 1) ≤ (64 * (2 * t) ^ (m + 1)) ^ 2 := by nlinarith
      have h3 : (64 * (2 * t) ^ (m + 1)) ^ 2 ≤ 16 * lam * (64 * (2 * t) ^ (m + 1)) ^ 2 :=
        Nat.le_mul_of_pos_left _ (by omega)
      have : 16 * lam * (64 * (2 * t) ^ (m + 1)) ^ 2 ≤ n := hPt
      omega
    have hnPt : ¬ Pc (t + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self t) (by omega)
    set c := 2 * t with hc
    have hc2 : 2 ≤ c := by omega
    -- `c ≤ 62`, as `c ≥ 64` would give `64^(m+2)` below `K`
    have hc62 : c ≤ 62 := by
      by_contra hcc
      push Not at hcc
      have h1 : 64 * 64 ^ (m + 1) ≤ 64 * c ^ (m + 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      have h2 : 16 * lam * (64 ^ (m + 2)) ^ 2 ≤ n := by
        rw [show 64 ^ (m + 2) = 64 * 64 ^ (m + 1) by ring]
        exact le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 2)) hPt
      omega
    -- the mixed grid of `c` and `c + 2` on the upper levels
    let Q : ℕ → Prop := fun i => 16 * lam * (64 * ((c + 2) ^ i * c ^ (m + 1 - i))) ^ 2 ≤ n
    set i := Nat.findGreatest Q (m + 1) with hi
    have hQ0 : Q 0 := by
      show 16 * lam * (64 * ((c + 2) ^ 0 * c ^ (m + 1 - 0))) ^ 2 ≤ n
      rw [Nat.sub_zero, pow_zero, one_mul]; exact hPt
    have hQi : Q i := Nat.findGreatest_spec (P := Q) (Nat.zero_le _) hQ0
    have him : i ≤ m + 1 := Nat.findGreatest_le _
    have hQm : ¬ Q (m + 1) := by
      show ¬ 16 * lam * (64 * ((c + 2) ^ (m + 1) * c ^ (m + 1 - (m + 1)))) ^ 2 ≤ n
      rw [Nat.sub_self, pow_zero, mul_one, hc, show 2 * t + 2 = 2 * (t + 1) by ring]
      exact hnPt
    have hilt : i < m + 1 := by
      rcases Nat.lt_or_ge i (m + 1) with h1 | h1
      · exact h1
      · exact absurd (show i = m + 1 by omega ▸ hQi) hQm
    have hQi1 : ¬ Q (i + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self i) (by omega)
    set P := (c + 2) ^ i * c ^ (m + 1 - i) with hP
    have hP1 : 1 ≤ P := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hnc : n * c ^ 2 < 16 * lam * (64 * P * (c + 2)) ^ 2 := by
      have e1 : (c + 2) ^ (i + 1) * c ^ (m + 1 - (i + 1)) * c = P * (c + 2) := by
        rw [hP]
        have : m + 1 - i = m + 1 - (i + 1) + 1 := by omega
        rw [this, pow_succ, pow_succ]; ring
      have h1 : n < 16 * lam * (64 * ((c + 2) ^ (i + 1) * c ^ (m + 1 - (i + 1)))) ^ 2 := by
        simpa [Q] using hQi1
      have := Nat.mul_lt_mul_of_pos_right h1 (show 0 < c ^ 2 by positivity)
      calc n * c ^ 2 < _ := this
        _ = 16 * lam * (64 * ((c + 2) ^ (i + 1) * c ^ (m + 1 - (i + 1)) * c)) ^ 2 := by ring
        _ = _ := by rw [e1]; ring
    -- the free level: the largest even `d` with `16 λ (P d)² ≤ n`
    let R : ℕ → Prop := fun u => 16 * lam * (P * (2 * u)) ^ 2 ≤ n
    have hR32 : R 32 := by
      show 16 * lam * (P * (2 * 32)) ^ 2 ≤ n
      have : 16 * lam * (64 * P) ^ 2 ≤ n := hQi
      calc 16 * lam * (P * (2 * 32)) ^ 2 = 16 * lam * (64 * P) ^ 2 := by ring
        _ ≤ n := this
    set u := Nat.findGreatest R n with hu
    have hRu : R u := Nat.findGreatest_spec (P := R) (by omega) hR32
    have hu32 : 32 ≤ u := Nat.le_findGreatest (by omega) hR32
    have hun : u < n := by
      have h1 : 2 * u ≤ P * (2 * u) := Nat.le_mul_of_pos_left _ (by omega)
      have h2 : P * (2 * u) ≤ (P * (2 * u)) ^ 2 := Nat.le_self_pow (by norm_num) _
      have h3 : (P * (2 * u)) ^ 2 ≤ 16 * lam * (P * (2 * u)) ^ 2 :=
        Nat.le_mul_of_pos_left _ (by omega)
      have : 16 * lam * (P * (2 * u)) ^ 2 ≤ n := hRu
      omega
    have hnRu : ¬ R (u + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self u) (by omega)
    set d := 2 * u with hd
    have hd64 : 64 ≤ d := by omega
    set K := P * d with hK
    have hlo' : 16 * lam * K ^ 2 ≤ n := hRu
    have hround : n * d ^ 2 < 16 * lam * (K * (d + 2)) ^ 2 := by
      have h1 : n < 16 * lam * (P * (d + 2)) ^ 2 := by
        have : ¬ 16 * lam * (P * (2 * (u + 1))) ^ 2 ≤ n := hnRu
        rw [show 2 * (u + 1) = d + 2 by omega] at this
        omega
      have := Nat.mul_lt_mul_of_pos_right h1 (show 0 < d ^ 2 by positivity)
      calc n * d ^ 2 < _ := this
        _ = _ := by rw [hK]; ring
    -- the budget: `d c < 64 (c + 2)`
    have hdc : d * c < 64 * (c + 2) := by
      have h1 : 16 * lam * (P * d) ^ 2 * c ^ 2 ≤ n * c ^ 2 := Nat.mul_le_mul_right _ hlo'
      have h2 : 16 * lam * ((P * d * c) ^ 2) < 16 * lam * ((P * (64 * (c + 2))) ^ 2) := by
        calc 16 * lam * ((P * d * c) ^ 2) = 16 * lam * (P * d) ^ 2 * c ^ 2 := by ring
          _ ≤ n * c ^ 2 := h1
          _ < 16 * lam * (64 * P * (c + 2)) ^ 2 := hnc
          _ = _ := by ring
      have h3 : (P * d * c) ^ 2 < (P * (64 * (c + 2))) ^ 2 := Nat.lt_of_mul_lt_mul_left h2
      have h4 : P * d * c < P * (64 * (c + 2)) := (Nat.pow_lt_pow_iff_left (by norm_num)).1 h3
      rw [mul_assoc] at h4
      exact Nat.lt_of_mul_lt_mul_left h4
    have hroom := free_room hc2 hc62 hdc
    have hmc : m * c ≤ m * 62 := Nat.mul_le_mul_left m hc62
    have hbudget : (m + 1) * c + 2 * i + d ≤ 2 * lam := by
      have e : (m + 1) * c = m * c + c := by ring
      rw [e]
      have : i ≤ m := by omega
      linarith
    have hsz := sz_Bfree (c := c) (j := i) (d := d) (m := m + 1) him
    have hnq := nq_Bfree (c := c) (j := i) (d := d) (m := m + 1) him
    have hK64 : 64 ≤ K := le_trans hd64 (Nat.le_mul_of_pos_left _ (by omega))
    have hres := port_le_budget (h := m + 1 + 1) hn (Bfree c i d (m + 1)) (Bfree_ge hc2 (by omega))
      (by omega)
      (by rw [hsz]; exact ⟨P * u, by rw [hP, hd]; ring⟩)
      (by rw [hnq]; exact ⟨(m + 1) * t + i + u, by rw [hc, hd]; ring⟩)
      (by rw [hnq]; exact hbudget)
      (by rw [hsz]; exact hK64) (by rw [hsz]; exact hlo') Bd
    have hqK := HierMix.nq_le_sz (Bfree_ge hc2 (by omega) : ∀ ℓ, 2 ≤ Bfree c i d (m + 1) ℓ)
      (h := m + 1 + 1)
    rw [hsz] at hres hqK
    have hPd : (c + 2) ^ i * c ^ (m + 1 - i) * d = K := by rw [hK, hP]
    rw [hPd] at hres hqK
    obtain ⟨-, hσσ, -⟩ := portSide_facts (n := n) (lam := lam) hn23 hl72 hqK hK64 hlo'
    exact ⟨m + 1 + 1, K, by omega, by rw [show m + 1 + 1 - 1 = m + 1 by omega]; exact h73, htwo,
      hK64, hlo', round_fine hd64 hround, _, hσσ, hres⟩

end SlidingPuzzle.Port
