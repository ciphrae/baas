import SlidingPuzzle.Port.Fine

/-! # A deep grid for the ports

The lane budget `q` enters the port bound only through `780 K³ q (n/K)²`, so a deep
hierarchy with small branching pays off: `m` levels of branching `4` or `6` (the mixed grid),
then a free level of even branching `d ≥ 32`, the largest with `16 λ K² ≤ n`. Then
`q = 4m + 2j + d ≤ 6m + 128`, and the grid rounds by at most `17/16`. -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle
open SlidingPuzzle.Tree

theorem pow16_le_n {n : ℕ} {E : ℕ} (h : 2 ^ E ≤ n) : E < Nat.log 2 n + 1 := by
  have := Nat.le_log_of_pow_le (by norm_num) h
  omega

/-- The deep grid and its port bound. -/
theorem port_deep {n : ℕ} [NeZero n] (hn : 2 ^ 23 ≤ n) (Bd : ReachableBoard n) :
    ∃ m K q σ : ℕ, 16 * GroupedOrder.lamN n * (32 * 4 ^ m) ^ 2 ≤ n ∧
      16 * GroupedOrder.lamN n * K ^ 2 ≤ n ∧ 64 * n < 1156 * GroupedOrder.lamN n * K ^ 2 ∧
      64 ≤ K ∧ q ≤ 6 * m + 128 ∧ σ * σ ≤ 13 * n ∧
      optimalLength Bd ≤ manhattan Bd.val + 2 * ((15 * n ^ 2 + 3002 * n + 1) * K) +
        2 * (190 * (K ^ 2 * (n / K) ^ 3) + 780 * (K ^ 3 * q * (n / K) ^ 2) +
          hopKc K σ * (2 * (m + 1) * (K * (n / K)) ^ 2)) := by
  set lam := GroupedOrder.lamN n with hlam
  have hl72 : 72 ≤ lam := lam_ge hn
  have hsmall : 102400 * lam ≤ n := lam_small hn
  -- the depth of the mixed levels
  let PM : ℕ → Prop := fun m => 16 * lam * (32 * 4 ^ m) ^ 2 ≤ n
  have hPM0 : PM 0 := by show 16 * lam * (32 * 4 ^ 0) ^ 2 ≤ n; norm_num; omega
  set m := Nat.findGreatest PM n with hm
  have hPm : PM m := Nat.findGreatest_spec (P := PM) (Nat.zero_le _) hPM0
  have h4m : 4 ^ m ≤ n := by
    have : 4 ^ m ≤ 16 * lam * (32 * 4 ^ m) ^ 2 := by
      have : 4 ^ m ≤ (32 * 4 ^ m) ^ 2 := by nlinarith [Nat.one_le_pow m 4 (by norm_num)]
      exact le_trans this (Nat.le_mul_of_pos_left _ (by omega))
    exact le_trans this hPm
  have hmn : m + 1 ≤ n := by
    have : m < 4 ^ m := Nat.lt_pow_self (by norm_num)
    omega
  have hnPm : ¬ PM (m + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self m) hmn
  -- the levels of branching `6`
  let PJ : ℕ → Prop := fun j => 16 * lam * (32 * (6 ^ j * 4 ^ (m - j))) ^ 2 ≤ n
  have hPJ0 : PJ 0 := by show 16 * lam * (32 * (6 ^ 0 * 4 ^ (m - 0))) ^ 2 ≤ n; simpa using hPm
  set j := Nat.findGreatest PJ m with hj
  have hPj : PJ j := Nat.findGreatest_spec (P := PJ) (Nat.zero_le _) hPJ0
  have hjm : j ≤ m := Nat.findGreatest_le _
  set P := 6 ^ j * 4 ^ (m - j) with hP
  have hP1 : 1 ≤ P := Nat.one_le_iff_ne_zero.2 (by positivity)
  -- the free level
  let PU : ℕ → Prop := fun u => 16 * lam * (P * (2 * u)) ^ 2 ≤ n
  have hPU16 : PU 16 := by
    show 16 * lam * (P * (2 * 16)) ^ 2 ≤ n
    have : 16 * lam * (32 * P) ^ 2 ≤ n := hPj
    calc 16 * lam * (P * (2 * 16)) ^ 2 = 16 * lam * (32 * P) ^ 2 := by ring
      _ ≤ n := this
  set u := Nat.findGreatest PU n with hu
  have hPu : PU u := Nat.findGreatest_spec (P := PU) (by omega) hPU16
  have hu16 : 16 ≤ u := Nat.le_findGreatest (by omega) hPU16
  have hun : u + 1 ≤ n := by
    have h1 : 2 * u ≤ P * (2 * u) := Nat.le_mul_of_pos_left _ (by omega)
    have h2 : P * (2 * u) ≤ (P * (2 * u)) ^ 2 := Nat.le_self_pow (by norm_num) _
    have h3 : (P * (2 * u)) ^ 2 ≤ 16 * lam * (P * (2 * u)) ^ 2 :=
      Nat.le_mul_of_pos_left _ (by omega)
    have : 16 * lam * (P * (2 * u)) ^ 2 ≤ n := hPu
    omega
  have hnPu : ¬ PU (u + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self u) hun
  set d := 2 * u with hd
  set K := P * d with hK
  have hlo : 16 * lam * K ^ 2 ≤ n := hPu
  -- rounding by `17/16`
  have hround : 64 * n < 1156 * lam * K ^ 2 := by
    have h1 : n < 16 * lam * (P * (d + 2)) ^ 2 := by
      have : ¬ 16 * lam * (P * (2 * (u + 1))) ^ 2 ≤ n := hnPu
      rw [show 2 * (u + 1) = d + 2 by omega] at this
      omega
    have h2 : 1024 * (d + 2) ^ 2 ≤ 1156 * d ^ 2 := by nlinarith
    have h3 : 1024 * (16 * lam * (P * (d + 2)) ^ 2) ≤ 16 * (1156 * lam * K ^ 2) := by
      have := Nat.mul_le_mul_left (16 * lam * P ^ 2) h2
      calc 1024 * (16 * lam * (P * (d + 2)) ^ 2) = 16 * lam * P ^ 2 * (1024 * (d + 2) ^ 2) := by
            ring
        _ ≤ 16 * lam * P ^ 2 * (1156 * d ^ 2) := this
        _ = _ := by rw [hK]; ring
    omega
  have hK64 : 64 ≤ K := by
    by_contra hc
    push Not at hc
    have : K ^ 2 ≤ 63 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have : 1156 * lam * K ^ 2 ≤ 1156 * lam * 63 ^ 2 := Nat.mul_le_mul_left _ this
    omega
  -- the free level is below `128`, and `q ≤ 2λ`
  have hd128 : d < 128 := by
    rcases Nat.lt_or_ge j m with hjl | hjl
    · have hnPj : ¬ PJ (j + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self j) (by omega)
      have e : 6 ^ (j + 1) * 4 ^ (m - (j + 1)) * 4 = 6 * P := by
        rw [hP]
        have : m - j = m - (j + 1) + 1 := by omega
        rw [this, pow_succ, pow_succ]; ring
      have h1 : n < 16 * lam * (32 * (6 ^ (j + 1) * 4 ^ (m - (j + 1)))) ^ 2 := by
        have : ¬ 16 * lam * (32 * (6 ^ (j + 1) * 4 ^ (m - (j + 1)))) ^ 2 ≤ n := hnPj
        omega
      have h2 : 16 * lam * (P * d) ^ 2 < 16 * lam * (48 * P) ^ 2 := by
        have e2 : 16 * lam * (32 * (6 ^ (j + 1) * 4 ^ (m - (j + 1)))) ^ 2 * 16 =
            16 * lam * (48 * P) ^ 2 * 16 := by
          have : 32 * (6 ^ (j + 1) * 4 ^ (m - (j + 1))) * 4 = 48 * P * 4 := by
            rw [show 32 * (6 ^ (j + 1) * 4 ^ (m - (j + 1))) * 4 = 32 * (6 ^ (j + 1) *
              4 ^ (m - (j + 1)) * 4) by ring, e]; ring
          have h' : 32 * (6 ^ (j + 1) * 4 ^ (m - (j + 1))) = 48 * P := by omega
          rw [h']
        have : 16 * lam * (32 * (6 ^ (j + 1) * 4 ^ (m - (j + 1)))) ^ 2 = 16 * lam * (48 * P) ^ 2 :=
          by omega
        have := lt_of_le_of_lt hlo h1
        rw [hK] at this; omega
      have h3 : (P * d) ^ 2 < (48 * P) ^ 2 := Nat.lt_of_mul_lt_mul_left h2
      have h4 : P * d < 48 * P := (Nat.pow_lt_pow_iff_left (by norm_num)).1 h3
      have h5 : P * d < P * 48 := by rw [mul_comm P 48]; exact h4
      have := Nat.lt_of_mul_lt_mul_left h5
      omega
    · have hjm' : j = m := by omega
      have h1 : n < 16 * lam * (32 * 4 ^ (m + 1)) ^ 2 := by
        have : ¬ 16 * lam * (32 * 4 ^ (m + 1)) ^ 2 ≤ n := hnPm
        omega
      have hPm6 : P = 6 ^ m := by rw [hP, hjm', Nat.sub_self, pow_zero, mul_one]
      have h2 : 16 * lam * (P * d) ^ 2 < 16 * lam * (128 * 4 ^ m) ^ 2 := by
        have e : 32 * 4 ^ (m + 1) = 128 * 4 ^ m := by rw [pow_succ]; ring
        rw [← e]
        have := lt_of_le_of_lt hlo h1
        rw [hK] at this; exact this
      have h3 : (P * d) ^ 2 < (128 * 4 ^ m) ^ 2 := Nat.lt_of_mul_lt_mul_left h2
      have h4 : P * d < 128 * 4 ^ m := (Nat.pow_lt_pow_iff_left (by norm_num)).1 h3
      have h5 : 4 ^ m ≤ P := by rw [hPm6]; exact Nat.pow_le_pow_left (by norm_num) m
      have h6 : 4 ^ m * d < 4 ^ m * 128 := by
        have := lt_of_le_of_lt (Nat.mul_le_mul_right d h5) h4
        rw [mul_comm 128] at this; exact this
      exact Nat.lt_of_mul_lt_mul_left h6
  set q := 4 * m + 2 * j + d with hq
  have hq128 : q ≤ 6 * m + 128 := by omega
  have hq2l : q ≤ 2 * lam := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · have : j = 0 := by omega
      omega
    · -- `2^(20 + 4m) ≤ n < 2^(λ/3)`
      have h1 : 2 ^ (20 + 4 * m) ≤ n := by
        have e : 2 ^ (20 + 4 * m) = 1024 * 1024 * 16 ^ m := by
          rw [pow_add, pow_mul]; norm_num
        have : 1024 * 1024 * 16 ^ m ≤ 16 * lam * (32 * 4 ^ m) ^ 2 := by
          have e2 : 16 * lam * (32 * 4 ^ m) ^ 2 = 16 * lam * 1024 * 16 ^ m := by
            rw [mul_pow, ← pow_mul, show (4 : ℕ) ^ (m * 2) = 16 ^ m by
              rw [pow_mul']; norm_num]; ring
          rw [e2]
          exact Nat.mul_le_mul_right _ (by nlinarith)
        rw [e]; exact le_trans this hPm
      have h2 := pow16_le_n h1
      have : lam = 3 * (Nat.log 2 n + 1) := rfl
      omega
  -- the lane system
  have hc2 : (2 : ℕ) ≤ 4 := by norm_num
  have hsz := sz_Bfree (c := 4) (j := j) (d := d) (m := m) hjm
  have hnq := nq_Bfree (c := 4) (j := j) (d := d) (m := m) hjm
  have hres := port_le_budgetq (h := m + 1) hn (Bfree 4 j d m) (Bfree_ge hc2 (by omega))
    (by omega)
    (by rw [hsz]; exact ⟨P * u, by rw [hP, hd]; ring⟩)
    (by rw [hnq]; exact ⟨2 * m + j + u, by rw [hd]; ring⟩)
    (by rw [hnq]; omega)
    (by rw [hsz]; exact hK64) (by rw [hsz]; exact hlo) Bd
  have hqK := HierMix.nq_le_sz (Bfree_ge hc2 (by omega) : ∀ ℓ, 2 ≤ Bfree 4 j d m ℓ) (h := m + 1)
  rw [hsz, hnq] at hres hqK
  have hPK : (4 + 2) ^ j * 4 ^ (m - j) * d = K := by rw [hK, hP]
  have hq' : m * 4 + 2 * j + d = q := by rw [hq]; ring
  rw [hPK, hq'] at hres hqK
  obtain ⟨-, hσσ, -⟩ := portSide_facts (n := n) (lam := lam) hn hl72 hqK hK64 hlo
  exact ⟨m, K, q, _, hPm, hlo, hround, hK64, hq128, hσσ, hres⟩

end SlidingPuzzle.Port
