import SlidingPuzzle.Port.Grid4
import SlidingPuzzle.Port.Asymp

/-! # The deep grid with a free level of at least `16`

As `port_deep`: `m ≥ 1` levels of branching `4` or `6`, then the largest even free level
`d ≥ 16` with `16 λ K² ≤ n`. The rounding is kept exact, `n < 16 λ (P (d + 2))²` with
`K = P d`, and `d < 24` or `6^m d < 64 · 4^m`, so `d ≤ 42`. -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle
open SlidingPuzzle.Tree

/-- The deep grid with a free level `d ≥ 16`, `K = P d`, and its port bound. -/
theorem port_deep16 {n : ℕ} [NeZero n] (hn : 2 ^ 23 ≤ n) (Bd : ReachableBoard n) :
    ∃ m d P K q σ : ℕ, 1 ≤ m ∧ 16 * GroupedOrder.lamN n * (16 * 4 ^ m) ^ 2 ≤ n ∧
      16 * GroupedOrder.lamN n * (4 ^ m * d) ^ 2 ≤ n ∧ 16 ≤ d ∧
      (d < 24 ∨ 6 ^ m * d < 64 * 4 ^ m) ∧ K = P * d ∧
      16 * GroupedOrder.lamN n * K ^ 2 ≤ n ∧ n < 16 * GroupedOrder.lamN n * (P * (d + 2)) ^ 2 ∧
      64 ≤ K ∧ q ≤ 6 * m + d ∧ σ * σ ≤ 13 * n ∧
      optimalLength Bd ≤ manhattan Bd.val + 2 * ((15 * n ^ 2 + 3002 * n + 1) * K) +
        2 * (172 * (K ^ 2 * (n / K) ^ 3) + 848 * (K ^ 3 * q * (n / K) ^ 2) +
          hopKc K σ * (2 * (m + 1) * (K * (n / K)) ^ 2)) := by
  set lam := GroupedOrder.lamN n with hlam
  have hl72 : 72 ≤ lam := lam_ge hn
  have hsmall : 102400 * lam ≤ n := lam_small hn
  -- the depth of the mixed levels
  let PM : ℕ → Prop := fun m => 16 * lam * (16 * 4 ^ m) ^ 2 ≤ n
  have hPM0 : PM 0 := by show 16 * lam * (16 * 4 ^ 0) ^ 2 ≤ n; norm_num; omega
  set m := Nat.findGreatest PM n with hm
  have hPm : PM m := Nat.findGreatest_spec (P := PM) (Nat.zero_le _) hPM0
  have h4m : 4 ^ m ≤ n := by
    have : 4 ^ m ≤ 16 * lam * (16 * 4 ^ m) ^ 2 := by
      have : 4 ^ m ≤ (16 * 4 ^ m) ^ 2 := by nlinarith [Nat.one_le_pow m 4 (by norm_num)]
      exact le_trans this (Nat.le_mul_of_pos_left _ (by omega))
    exact le_trans this hPm
  have hmn : m + 1 ≤ n := by
    have : m < 4 ^ m := Nat.lt_pow_self (by norm_num)
    omega
  have hnPm : ¬ PM (m + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self m) hmn
  -- the levels of branching `6`
  let PJ : ℕ → Prop := fun j => 16 * lam * (16 * (6 ^ j * 4 ^ (m - j))) ^ 2 ≤ n
  have hPJ0 : PJ 0 := by show 16 * lam * (16 * (6 ^ 0 * 4 ^ (m - 0))) ^ 2 ≤ n; simpa using hPm
  set j := Nat.findGreatest PJ m with hj
  have hPj : PJ j := Nat.findGreatest_spec (P := PJ) (Nat.zero_le _) hPJ0
  have hjm : j ≤ m := Nat.findGreatest_le _
  set P := 6 ^ j * 4 ^ (m - j) with hP
  have hP1 : 1 ≤ P := Nat.one_le_iff_ne_zero.2 (by positivity)
  -- the free level
  let PU : ℕ → Prop := fun u => 16 * lam * (P * (2 * u)) ^ 2 ≤ n
  have hPU16 : PU 8 := by
    show 16 * lam * (P * (2 * 8)) ^ 2 ≤ n
    have : 16 * lam * (16 * P) ^ 2 ≤ n := hPj
    calc 16 * lam * (P * (2 * 8)) ^ 2 = 16 * lam * (16 * P) ^ 2 := by ring
      _ ≤ n := this
  set u := Nat.findGreatest PU n with hu
  have hPu : PU u := Nat.findGreatest_spec (P := PU) (by omega) hPU16
  have hu16 : 8 ≤ u := Nat.le_findGreatest (by omega) hPU16
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
  have hround : n < 16 * lam * (P * (d + 2)) ^ 2 := by
    have : ¬ 16 * lam * (P * (2 * (u + 1))) ^ 2 ≤ n := hnPu
    rw [show 2 * (u + 1) = d + 2 by omega] at this
    omega
  -- `m ≥ 1`: `16 λ 64² ≤ 2²³`
  have hm1 : 1 ≤ m := by
    have hPM1 : PM 1 := by
      show 16 * lam * (16 * 4 ^ 1) ^ 2 ≤ n
      have e : 16 * lam * (16 * 4 ^ 1) ^ 2 = 65536 * lam := by ring
      rw [e]; omega
    exact Nat.le_findGreatest (by omega) hPM1
  have hK64 : 64 ≤ K := by
    have h4 : 4 ≤ P := by
      have : 4 ^ 1 ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
      have : 4 ^ m ≤ P := by
        rw [hP]
        calc 4 ^ m = 4 ^ j * 4 ^ (m - j) := by rw [← pow_add]; congr 1; omega
          _ ≤ 6 ^ j * 4 ^ (m - j) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) j)
      omega
    have := Nat.mul_le_mul h4 (show 16 ≤ d by omega)
    rw [hK]; omega
  -- the free level: `d < 24` below a mixed level of `4`, else `6^m d < 64 · 4^m`
  have hdj : d < 24 ∨ 6 ^ m * d < 64 * 4 ^ m := by
    rcases Nat.lt_or_ge j m with hjl | hjl
    · left
      have hnPj : ¬ PJ (j + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self j) (by omega)
      have e : 16 * (6 ^ (j + 1) * 4 ^ (m - (j + 1))) * 2 = 24 * P * 2 := by
        rw [hP]
        have : m - j = m - (j + 1) + 1 := by omega
        rw [this, pow_succ, pow_succ]; ring
      have h1 : n < 16 * lam * (24 * P) ^ 2 := by
        have : ¬ 16 * lam * (16 * (6 ^ (j + 1) * 4 ^ (m - (j + 1)))) ^ 2 ≤ n := hnPj
        have h' : 16 * (6 ^ (j + 1) * 4 ^ (m - (j + 1))) = 24 * P := by omega
        rw [h'] at this; omega
      have h2 : 16 * lam * (P * d) ^ 2 < 16 * lam * (24 * P) ^ 2 := by
        have := lt_of_le_of_lt hlo h1
        rw [hK] at this; exact this
      have h3 : (P * d) ^ 2 < (24 * P) ^ 2 := Nat.lt_of_mul_lt_mul_left h2
      have h4 : P * d < 24 * P := (Nat.pow_lt_pow_iff_left (by norm_num)).1 h3
      have h5 : P * d < P * 24 := by rw [mul_comm P 24]; exact h4
      exact Nat.lt_of_mul_lt_mul_left h5
    · right
      have hjm' : j = m := by omega
      have h1 : n < 16 * lam * (16 * 4 ^ (m + 1)) ^ 2 := by
        have : ¬ 16 * lam * (16 * 4 ^ (m + 1)) ^ 2 ≤ n := hnPm
        omega
      have hPm6 : P = 6 ^ m := by rw [hP, hjm', Nat.sub_self, pow_zero, mul_one]
      have h2 : 16 * lam * (P * d) ^ 2 < 16 * lam * (64 * 4 ^ m) ^ 2 := by
        have e : 16 * 4 ^ (m + 1) = 64 * 4 ^ m := by rw [pow_succ]; ring
        rw [← e]
        have := lt_of_le_of_lt hlo h1
        rw [hK] at this; exact this
      have h3 : (P * d) ^ 2 < (64 * 4 ^ m) ^ 2 := Nat.lt_of_mul_lt_mul_left h2
      have h4 : P * d < 64 * 4 ^ m := (Nat.pow_lt_pow_iff_left (by norm_num)).1 h3
      rw [hPm6] at h4; exact h4
  have hd80 : d < 64 := by
    rcases hdj with h | h
    · omega
    · have : 4 ^ m ≤ 6 ^ m := Nat.pow_le_pow_left (by norm_num) m
      have h' : 4 ^ m * d < 4 ^ m * 64 := by
        have := lt_of_le_of_lt (Nat.mul_le_mul_right d this) h
        rw [mul_comm 64] at this; exact this
      exact Nat.lt_of_mul_lt_mul_left h'
  have h4d : 16 * lam * (4 ^ m * d) ^ 2 ≤ n := by
    have : 4 ^ m ≤ P := by
      rw [hP]
      calc 4 ^ m = 4 ^ j * 4 ^ (m - j) := by rw [← pow_add]; congr 1; omega
        _ ≤ 6 ^ j * 4 ^ (m - j) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) j)
    have : 4 ^ m * d ≤ K := by rw [hK]; exact Nat.mul_le_mul_right d this
    exact le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left this 2)) hlo
  set q := 4 * m + 2 * j + d with hq
  have hq6 : q ≤ 6 * m + d := by omega
  have hq2l : q ≤ 2 * lam := by
    -- `2^(18 + 4m) ≤ n < 2^(λ/3)`
    have h1 : 2 ^ (18 + 4 * m) ≤ n := by
      have e : 2 ^ (18 + 4 * m) = 256 * 1024 * 16 ^ m := by
        rw [pow_add, pow_mul]; norm_num
      have : 256 * 1024 * 16 ^ m ≤ 16 * lam * (16 * 4 ^ m) ^ 2 := by
        have e2 : 16 * lam * (16 * 4 ^ m) ^ 2 = 16 * lam * 256 * 16 ^ m := by
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
  exact ⟨m, d, P, K, q, _, hm1, hPm, h4d, by omega, hdj, hK, hlo, hround, hK64, hq6, hσσ, hres⟩

set_option maxHeartbeats 2000000 in
/-- The port bound on the grid of free level `≥ 16`, as a coefficient of `n^(5/2)`. -/
theorem port_coef16 {n : ℕ} [NeZero n] (hn : 2 ^ 23 ≤ n) (B : ReachableBoard n) :
    ∃ m d q : ℕ, 1 ≤ m ∧ 16 * GroupedOrder.lamN n * (16 * 4 ^ m) ^ 2 ≤ n ∧
      16 * GroupedOrder.lamN n * (4 ^ m * d) ^ 2 ≤ n ∧ 16 ≤ d ∧
      (d < 24 ∨ 6 ^ m * d < 64 * 4 ^ m) ∧ q ≤ 6 * m + d ∧
      (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
        (1 + 8 * Real.sqrt (GroupedOrder.lamN n) * (1 + 2 / (d : ℝ)) *
          (172 + 53 * (q : ℝ) / (GroupedOrder.lamN n)) + 240.96 * ((m : ℝ) + 1)) *
          (n : ℝ) ^ ((5 : ℝ) / 2) := by
  obtain ⟨m, d, Pn, K, q, σ, hm1, hPm, h4d, hd16, hdj, hKP, hlo, hround, hK64, hq6, hσ, hnat⟩ :=
    port_deep16 hn B
  refine ⟨m, d, q, hm1, hPm, h4d, hd16, hdj, hq6, ?_⟩
  set lam := GroupedOrder.lamN n with hlam
  have hl72 : 72 ≤ lam := lam_ge hn
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hK0 : 0 < K := by omega
  have hsK : 16 * lam * K ≤ n / K := by
    rw [Nat.le_div_iff_mul_le hK0]
    calc 16 * lam * K * K = 16 * lam * K ^ 2 := by ring
      _ ≤ n := hlo
  have hKK : K * (n / K) ≤ n := Nat.mul_div_le n _
  have hK1024 : 1024 * K ^ 2 ≤ n := by
    have := Nat.mul_le_mul_right (K ^ 2) (show 1024 ≤ 16 * lam by omega)
    omega
  have hbig : 8388608 ≤ n := by norm_num at hn; exact hn
  set nr : ℝ := (n : ℝ) with hnr
  set Kr : ℝ := (K : ℝ) with hKr
  set lr : ℝ := (lam : ℝ) with hlr
  set sr : ℝ := (σ : ℝ) with hsr
  set mr : ℝ := (m : ℝ) with hmr
  set qr : ℝ := (q : ℝ) with hqr
  set s : ℝ := ((n / K : ℕ) : ℝ) with hs
  have hKpos : 0 < Kr := by rw [hKr]; exact_mod_cast hK0
  have hs0 : 0 ≤ s := by positivity
  have hlr0 : 0 < lr := by rw [hlr]; exact_mod_cast (show 0 < lam by omega)
  have hsKr : 16 * lr * Kr ≤ s := by rw [hlr, hKr, hs]; exact_mod_cast hsK
  have hKs : Kr * s ≤ nr := by rw [hKr, hs, hnr]; exact_mod_cast hKK
  set ρ : ℝ := 1 + 2 / (d : ℝ) with hρ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hρ1 : 1 ≤ ρ := by rw [hρ]; have : 0 ≤ 2 / (d : ℝ) := by positivity
                         linarith
  have hroundR : nr ≤ 16 * lr * (ρ * Kr) ^ 2 := by
    have h1 : (n : ℝ) < 16 * (lam : ℝ) * ((Pn : ℝ) * ((d : ℝ) + 2)) ^ 2 := by exact_mod_cast hround
    have e : (Pn : ℝ) * ((d : ℝ) + 2) = ρ * Kr := by
      rw [hρ, hKr, hKP]; push_cast; field_simp
    rw [e] at h1
    rw [hnr, hlr]; exact h1.le
  have hK1024R : 1024 * Kr ^ 2 ≤ nr := by rw [hKr, hnr]; exact_mod_cast hK1024
  have hσR : sr * sr ≤ 13 * nr := by rw [hsr, hnr]; exact_mod_cast hσ
  have hsr0 : 0 ≤ sr := by rw [hsr]; exact Nat.cast_nonneg _
  have hq0 : 0 ≤ qr := by rw [hqr]; exact Nat.cast_nonneg _
  have hm0 : 0 ≤ mr := by rw [hmr]; exact Nat.cast_nonneg _
  have hnbig : (8388608 : ℝ) ≤ nr := by rw [hnr]; exact_mod_cast hbig
  -- the natural bound, cast
  have hcast : (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      2 * ((15 * nr ^ 2 + 3002 * nr + 1) * Kr) +
      2 * (172 * (Kr ^ 2 * s ^ 3) + 848 * (Kr ^ 3 * qr * s ^ 2) +
        (12 * sr + 526 * Kr + 1535) * (2 * (mr + 1) * (Kr * s) ^ 2)) := by
    have := (Nat.cast_le (α := ℝ)).2 hnat
    unfold hopKc at this
    push_cast at this
    rw [hnr, hKr, hsr, hmr, hqr, hs]
    exact this
  -- `n^(5/2) = n² √n`
  set P : ℝ := nr ^ ((5 : ℝ) / 2) with hP
  have hsn : 0 ≤ Real.sqrt nr := Real.sqrt_nonneg _
  have hPe : P = nr ^ 2 * Real.sqrt nr := by
    rw [hP, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hn0]; norm_num
  have hsq_n : Real.sqrt nr ^ 2 = nr := Real.sq_sqrt hn0.le
  have hP0 : 0 ≤ P := by rw [hPe]; positivity
  have hsl : 0 ≤ Real.sqrt lr := Real.sqrt_nonneg _
  -- `√n ≤ 4 √λ ρ K`, `32 K ≤ √n`
  have hup : Real.sqrt nr ≤ 4 * Real.sqrt lr * ρ * Kr := by
    have hρ0 : 0 ≤ ρ := by linarith
    rw [show 4 * Real.sqrt lr * ρ * Kr = Real.sqrt (16 * lr * (ρ * Kr) ^ 2) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (by positivity), show (16 : ℝ) = 4 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]; ring]
    exact Real.sqrt_le_sqrt hroundR
  have hdown : 32 * Kr ≤ Real.sqrt nr := by
    rw [show 32 * Kr = Real.sqrt ((32 * Kr) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hσn : sr ≤ 3.6056 * Real.sqrt nr := by
    have h1 : sr ^ 2 ≤ (3.6056 * Real.sqrt nr) ^ 2 := by
      rw [mul_pow, hsq_n]; nlinarith
    exact (pow_le_pow_iff_left₀ hsr0 (by positivity) two_ne_zero).1 h1
  have hn23 : (2896 : ℝ) ≤ Real.sqrt nr := by
    have : (2896 : ℝ) ^ 2 ≤ nr := by norm_num; linarith
    calc (2896 : ℝ) = Real.sqrt (2896 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ _ := Real.sqrt_le_sqrt this
  have hKc : 12 * sr + 526 * Kr + 1535 ≤ 60.24 * Real.sqrt nr := by
    have : (1535 : ℝ) ≤ 0.5301 * Real.sqrt nr := by linarith
    linarith
  -- the grid term `K² s³ ≤ 4 √λ ρ P`
  have hmain : Kr ^ 2 * s ^ 3 ≤ 4 * Real.sqrt lr * ρ * P := by
    have h1 : Kr ^ 2 * s ^ 3 * Kr ≤ nr ^ 3 := by
      have := pow_le_pow_left₀ (by positivity) (show s * Kr ≤ nr by linarith) 3
      calc Kr ^ 2 * s ^ 3 * Kr = (s * Kr) ^ 3 := by ring
        _ ≤ _ := this
    have h2 : nr ^ 3 ≤ 4 * Real.sqrt lr * ρ * P * Kr := by
      rw [hPe]
      have e3 : nr ^ 3 = nr ^ 2 * Real.sqrt nr * Real.sqrt nr := by
        rw [mul_assoc, ← sq, hsq_n]; ring
      rw [e3]
      have := mul_le_mul_of_nonneg_left hup (by positivity : (0 : ℝ) ≤ nr ^ 2 * Real.sqrt nr)
      calc nr ^ 2 * Real.sqrt nr * Real.sqrt nr ≤ _ := this
        _ = _ := by ring
    exact le_of_mul_le_mul_right (le_trans h1 h2) hKpos
  -- the lane term: `848 K³ q s² ≤ 53 q/λ · K² s³`
  have hV : 848 * (Kr ^ 3 * qr * s ^ 2) ≤ 53 * qr / lr * (Kr ^ 2 * s ^ 3) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlr0]
    have := mul_le_mul_of_nonneg_left hsKr (by positivity : (0 : ℝ) ≤ 53 * qr * Kr ^ 2 * s ^ 2)
    calc 848 * (Kr ^ 3 * qr * s ^ 2) * lr = 53 * qr * Kr ^ 2 * s ^ 2 * (16 * lr * Kr) := by ring
      _ ≤ 53 * qr * Kr ^ 2 * s ^ 2 * s := this
      _ = _ := by ring
  have hgrid : 172 * (Kr ^ 2 * s ^ 3) + 848 * (Kr ^ 3 * qr * s ^ 2) ≤
      (172 + 53 * qr / lr) * (4 * Real.sqrt lr * ρ * P) := by
    have h1 : (172 + 53 * qr / lr) * (Kr ^ 2 * s ^ 3) ≤ (172 + 53 * qr / lr) * (4 * Real.sqrt lr * ρ * P) :=
      mul_le_mul_of_nonneg_left hmain (by positivity)
    have e : (172 + 53 * qr / lr) * (Kr ^ 2 * s ^ 3) =
        172 * (Kr ^ 2 * s ^ 3) + 53 * qr / lr * (Kr ^ 2 * s ^ 3) := by ring
    linarith
  -- the prefix term
  have hpre : 2 * ((15 * nr ^ 2 + 3002 * nr + 1) * Kr) ≤ P := by
    have hn3003 : (3003 : ℝ) ≤ nr := le_trans (by norm_num) hnbig
    have hsq : 3003 * nr ≤ nr ^ 2 := by
      have := mul_le_mul_of_nonneg_right hn3003 hn0.le
      rw [sq]; exact this
    have ha : 15 * nr ^ 2 + 3002 * nr + 1 ≤ 16 * nr ^ 2 := by
      have : (1 : ℝ) ≤ nr := le_trans (by norm_num) hnbig
      linarith only [hsq, this]
    have h1 := mul_le_mul_of_nonneg_right ha hKpos.le
    have h2 := mul_le_mul_of_nonneg_left hdown (by positivity : (0 : ℝ) ≤ nr ^ 2)
    rw [hPe]; linarith only [h1, h2]
  -- the cheap hops
  have hhop : (12 * sr + 526 * Kr + 1535) * (2 * (mr + 1) * (Kr * s) ^ 2) ≤
      120.48 * (mr + 1) * P := by
    have h1 : (Kr * s) ^ 2 ≤ nr ^ 2 := pow_le_pow_left₀ (by positivity) hKs 2
    have h2 : (12 * sr + 526 * Kr + 1535) * (2 * (mr + 1) * (Kr * s) ^ 2) ≤
        (60.24 * Real.sqrt nr) * (2 * (mr + 1) * nr ^ 2) := by
      apply mul_le_mul hKc _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [hPe]
    calc _ ≤ _ := h2
      _ = _ := by ring
  have e : (1 + 8 * Real.sqrt lr * ρ * (172 + 53 * qr / lr) + 240.96 * (mr + 1)) * P =
      P + 2 * ((172 + 53 * qr / lr) * (4 * Real.sqrt lr * ρ * P)) + 2 * (120.48 * (mr + 1) * P) := by
    ring
  rw [e]
  linarith only [hcast, hpre, hgrid, hhop]

end SlidingPuzzle.Port

namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle
open SlidingPuzzle.Tree

theorem m_le_of {lam n m mb E : ℕ} (h : 16 * lam * (16 * 4 ^ m) ^ 2 ≤ n) (hn : n < 2 ^ (E + 1))
    (hnum : 2 ^ (E + 1) ≤ 16 * lam * (16 * 4 ^ (mb + 1)) ^ 2) : m ≤ mb := by
  by_contra hc
  push Not at hc
  have h1 : 4 ^ (mb + 1) ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hc
  have h2 : (16 * 4 ^ (mb + 1)) ^ 2 ≤ (16 * 4 ^ m) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have := Nat.mul_le_mul_left (16 * lam) h2
  omega

theorem d_le_of {lam n m d c E : ℕ} (h : 16 * lam * (4 ^ m * d) ^ 2 ≤ n) (hn : n < 2 ^ (E + 1))
    (hm : 1 ≤ m) (hnum : 2 ^ (E + 1) ≤ 16 * lam * (4 * (c + 1)) ^ 2) : d ≤ c := by
  by_contra hc
  push Not at hc
  have h1 : 4 ≤ 4 ^ m := by
    calc 4 = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h2 : 4 * (c + 1) ≤ 4 ^ m * d := Nat.mul_le_mul h1 hc
  have h3 := Nat.pow_le_pow_left h2 2
  have := Nat.mul_le_mul_left (16 * lam) h3
  omega

theorem d_le42 {m d : ℕ} (hm : 1 ≤ m) (hdj : d < 24 ∨ 6 ^ m * d < 64 * 4 ^ m) : d ≤ 42 := by
  rcases hdj with h | h
  · omega
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have h1 : 4 ^ k ≤ 6 ^ k := Nat.pow_le_pow_left (by norm_num) k
    rw [pow_succ, pow_succ] at h
    have h2 : 6 ^ k * (6 * d) < 6 ^ k * 256 := by
      have : 64 * (4 ^ k * 4) ≤ 64 * (6 ^ k * 4) := by
        have := Nat.mul_le_mul_right 4 h1
        omega
      calc 6 ^ k * (6 * d) = 6 ^ k * 6 * d := by ring
        _ < 64 * (4 ^ k * 4) := h
        _ ≤ 64 * (6 ^ k * 4) := this
        _ = 6 ^ k * 256 := by ring
    have := Nat.lt_of_mul_lt_mul_left h2
    omega

end SlidingPuzzle.Port
