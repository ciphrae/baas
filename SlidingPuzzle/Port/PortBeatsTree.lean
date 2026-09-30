import SlidingPuzzle.Port.AsympDeep

/-! # The port algorithm beats the tree bound from `2²³`

On the grid with a free level of at least `20` (`port_deep20`) the error coefficient is
`1 + 8.8 √λ (172 + 53 q/λ) + 240.96 (m + 1)`. For `⌊log₂ n⌋ ≤ 31` it is checked case by case,
beyond with `q ≤ 6m + 53` and the depth against `ln n`: it stays below `0.95` times the
tree coefficient `(97 ln n + 2670) √(ln n)`. -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle
open SlidingPuzzle.Tree

set_option maxHeartbeats 2000000 in
/-- The port bound on the grid of free level `≥ 20`, as a coefficient of `n^(5/2)`. -/
theorem port_coef20 {n : ℕ} [NeZero n] (hn : 2 ^ 23 ≤ n) (B : ReachableBoard n) :
    ∃ m d q : ℕ, 1 ≤ m ∧ 16 * GroupedOrder.lamN n * (20 * 4 ^ m) ^ 2 ≤ n ∧
      16 * GroupedOrder.lamN n * (4 ^ m * d) ^ 2 ≤ n ∧ 20 ≤ d ∧
      (d < 30 ∨ 6 ^ m * d < 80 * 4 ^ m) ∧ q ≤ 6 * m + d ∧
      (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
        (1 + 8.8 * Real.sqrt (GroupedOrder.lamN n) *
          (172 + 53 * (q : ℝ) / (GroupedOrder.lamN n)) + 240.96 * ((m : ℝ) + 1)) *
          (n : ℝ) ^ ((5 : ℝ) / 2) := by
  obtain ⟨m, d, K, q, σ, hm1, hPm, h4d, hd20, hdj, hlo, hround, hK64, hq6, hσ, hnat⟩ :=
    port_deep20 hn B
  refine ⟨m, d, q, hm1, hPm, h4d, hd20, hdj, hq6, ?_⟩
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
  have hroundR : nr ≤ 1936 / 100 * lr * Kr ^ 2 := by
    have : (100 * n : ℝ) ≤ 1936 * lr * Kr ^ 2 := by rw [hlr, hKr]; exact_mod_cast hround.le
    rw [hnr]; linarith
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
  -- `√n ≤ 4.4 √λ K`, `32 K ≤ √n`
  have hup : Real.sqrt nr ≤ 4.4 * Real.sqrt lr * Kr := by
    rw [show 4.4 * Real.sqrt lr * Kr = Real.sqrt (1936 / 100 * lr * Kr ^ 2) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_sq hKpos.le,
        show (1936 / 100 : ℝ) = 4.4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
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
  -- the grid term `K² s³ ≤ 4.4 √λ P`
  have hmain : Kr ^ 2 * s ^ 3 ≤ 4.4 * Real.sqrt lr * P := by
    have h1 : Kr ^ 2 * s ^ 3 * Kr ≤ nr ^ 3 := by
      have := pow_le_pow_left₀ (by positivity) (show s * Kr ≤ nr by linarith) 3
      calc Kr ^ 2 * s ^ 3 * Kr = (s * Kr) ^ 3 := by ring
        _ ≤ _ := this
    have h2 : nr ^ 3 ≤ 4.4 * Real.sqrt lr * P * Kr := by
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
      (172 + 53 * qr / lr) * (4.4 * Real.sqrt lr * P) := by
    have h1 : (172 + 53 * qr / lr) * (Kr ^ 2 * s ^ 3) ≤ (172 + 53 * qr / lr) * (4.4 * Real.sqrt lr * P) :=
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
  have e : (1 + 8.8 * Real.sqrt lr * (172 + 53 * qr / lr) + 240.96 * (mr + 1)) * P =
      P + 2 * ((172 + 53 * qr / lr) * (4.4 * Real.sqrt lr * P)) + 2 * (120.48 * (mr + 1) * P) := by
    ring
  rw [e]
  linarith only [hcast, hpre, hgrid, hhop]

end SlidingPuzzle.Port

namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle
open SlidingPuzzle.Tree

theorem m_le_of {lam n m mb E : ℕ} (h : 16 * lam * (20 * 4 ^ m) ^ 2 ≤ n) (hn : n < 2 ^ (E + 1))
    (hnum : 2 ^ (E + 1) ≤ 16 * lam * (20 * 4 ^ (mb + 1)) ^ 2) : m ≤ mb := by
  by_contra hc
  push Not at hc
  have h1 : 4 ^ (mb + 1) ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hc
  have h2 : (20 * 4 ^ (mb + 1)) ^ 2 ≤ (20 * 4 ^ m) ^ 2 := Nat.pow_le_pow_left (by omega) 2
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

theorem d_le53 {m d : ℕ} (hm : 1 ≤ m) (hdj : d < 30 ∨ 6 ^ m * d < 80 * 4 ^ m) : d ≤ 53 := by
  rcases hdj with h | h
  · omega
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have h1 : 4 ^ k ≤ 6 ^ k := Nat.pow_le_pow_left (by norm_num) k
    rw [pow_succ, pow_succ] at h
    have h2 : 6 ^ k * (6 * d) < 6 ^ k * 320 := by
      have : 80 * (4 ^ k * 4) ≤ 80 * (6 ^ k * 4) := by
        have := Nat.mul_le_mul_right 4 h1
        omega
      calc 6 ^ k * (6 * d) = 6 ^ k * 6 * d := by ring
        _ < 80 * (4 ^ k * 4) := h
        _ ≤ 80 * (6 ^ k * 4) := this
        _ = 6 ^ k * 320 := by ring
    have := Nat.lt_of_mul_lt_mul_left h2
    omega

/-- A numeric check gives the comparison. -/
theorem num_check {lam q m qb mb : ℕ} {a L Lb t : ℝ} (hlam : 0 < lam) (ha : (lam : ℝ) ≤ a ^ 2)
    (ha0 : 0 ≤ a) (hq : q ≤ qb) (hm : m ≤ mb) (hLb : Lb ≤ L) (ht0 : 0 ≤ t) (ht : t ^ 2 ≤ Lb)
    (hnum : 1 + 8.8 * a * (172 + 53 * (qb : ℝ) / lam) + 240.96 * ((mb : ℝ) + 1) ≤
      0.95 * (97 * Lb + 2670) * t) :
    1 + 8.8 * Real.sqrt lam * (172 + 53 * (q : ℝ) / lam) + 240.96 * ((m : ℝ) + 1) ≤
      0.95 * (97 * L + 2670) * Real.sqrt L := by
  have hl0 : (0 : ℝ) < lam := by exact_mod_cast hlam
  have hsa : Real.sqrt lam ≤ a := by
    rw [show a = Real.sqrt (a ^ 2) from (Real.sqrt_sq ha0).symm]; exact Real.sqrt_le_sqrt ha
  have hLb0 : 0 ≤ Lb := le_trans (sq_nonneg t) ht
  have hst : t ≤ Real.sqrt L := by
    rw [show t = Real.sqrt (t ^ 2) from (Real.sqrt_sq ht0).symm]
    exact Real.sqrt_le_sqrt (ht.trans hLb)
  have hqq : (q : ℝ) ≤ qb := by exact_mod_cast hq
  have hmm : (m : ℝ) ≤ mb := by exact_mod_cast hm
  have h1 : 53 * (q : ℝ) / lam ≤ 53 * (qb : ℝ) / lam :=
    div_le_div_of_nonneg_right (by linarith) hl0.le
  have h2 : 8.8 * Real.sqrt lam * (172 + 53 * (q : ℝ) / lam) ≤
      8.8 * a * (172 + 53 * (qb : ℝ) / lam) := by
    have h0 : (0 : ℝ) ≤ 172 + 53 * (q : ℝ) / lam := by positivity
    apply mul_le_mul (by linarith) (by linarith) h0 (by linarith)
  have h3 : 0.95 * (97 * Lb + 2670) * t ≤ 0.95 * (97 * L + 2670) * Real.sqrt L := by
    apply mul_le_mul (by linarith) hst ht0 (by linarith)
  linarith

/-- The generic comparison, as pure real arithmetic. -/
theorem gen_coef (L t S mr qr : ℝ) (ht : t ^ 2 = L) (ht0 : 4.709 ≤ t)
    (hSU : S ≤ 2.1261 * t) (hSD : 2.0803 * t ≤ S) (hD : 2.7725 * mr ≤ L - 13.35) (hm0 : 0 ≤ mr)
    (hq : qr ≤ 6 * mr + 53) (hq0 : 0 ≤ qr) :
    1 + 8.8 * S * (172 + 53 * qr / S ^ 2) + 240.96 * (mr + 1) ≤ 0.95 * (97 * L + 2670) * t := by
  have htp : 0 < t := by linarith
  have hSp : 0 < S := by linarith
  set w := qr / S with hw
  have hwS : w * S = qr := by rw [hw]; field_simp
  have hw0 : 0 ≤ w := by positivity
  have e : 8.8 * S * (172 + 53 * qr / S ^ 2) = 1513.6 * S + 466.4 * w := by
    rw [hw]; field_simp; ring
  rw [e]
  set u := 1 / t with hu
  have hu0 : 0 < u := by positivity
  have htu : t * u = 1 := by rw [hu]; field_simp
  have h1 : 2.7725 * (mr * u) ≤ t - 13.35 * u := by
    have := mul_le_mul_of_nonneg_right hD hu0.le
    have e : (L - 13.35) * u = t - 13.35 * u := by
      rw [← ht]; have : t ^ 2 * u = t * (t * u) := by ring
      rw [sub_mul, this, htu]; ring
    linarith
  have h2 : 2.0803 * w ≤ 6 * (mr * u) + 53 * u := by
    have a : w * (2.0803 * t) ≤ w * S := mul_le_mul_of_nonneg_left hSD hw0
    have b : w * (2.0803 * t) ≤ 6 * mr + 53 := by linarith
    have c := mul_le_mul_of_nonneg_right b hu0.le
    have e : w * (2.0803 * t) * u = 2.0803 * w := by
      have : w * (2.0803 * t) * u = 2.0803 * w * (t * u) := by ring
      rw [this, htu, mul_one]
    linarith
  have h4 : 1513.6 * S ≤ 3218.2 * t := by linarith
  have h5 : u ≤ 0.2124 := by
    rw [hu, div_le_iff₀ htp]; linarith
  have h6 : 0 ≤ mr * u := by positivity
  have hL : 22.17 ≤ L := by nlinarith
  have h3 : 240.96 * mr ≤ 86.92 * L - 1160.3 := by linarith
  have h7 : 92.15 * L * t ≥ 86.91 * L + 1166.8 * t + 230 := by nlinarith
  nlinarith

end SlidingPuzzle.Port

namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle
open SlidingPuzzle.Tree

/-- The depth against `ln n` for `λ ≥ 99`: `2.7725 m ≤ ln n - 13.35`. -/
theorem depth20_log {n m : ℕ} (hl : 99 ≤ GroupedOrder.lamN n)
    (h : 16 * GroupedOrder.lamN n * (20 * 4 ^ m) ^ 2 ≤ n) :
    27725 / 10000 * (m : ℝ) ≤ Real.log n - 1335 / 100 := by
  have e : 16 * GroupedOrder.lamN n * (20 * 4 ^ m) ^ 2 = 6400 * GroupedOrder.lamN n * 2 ^ (4 * m) := by
    have e1 : (4 : ℕ) ^ m = 2 ^ (2 * m) := by rw [pow_mul]; norm_num
    rw [e1, mul_pow, ← pow_mul]; ring_nf
  rw [e] at h
  have hpos : (0 : ℝ) < 6400 * GroupedOrder.lamN n := by
    have : (0 : ℝ) < GroupedOrder.lamN n := by exact_mod_cast (show 0 < GroupedOrder.lamN n by omega)
    linarith
  have h1 : (6400 * GroupedOrder.lamN n : ℝ) * (2 : ℝ) ^ (4 * m) ≤ n := by exact_mod_cast h
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_mul hpos.ne' (by positivity), Real.log_pow] at h2
  have h3 : Real.log 633600 ≤ Real.log (6400 * GroupedOrder.lamN n : ℝ) := by
    apply Real.log_le_log (by norm_num)
    have : (99 : ℝ) ≤ GroupedOrder.lamN n := by exact_mod_cast hl
    linarith
  have h4 : (1335 / 100 : ℝ) ≤ Real.log 633600 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 633600)]
    have hb : Real.exp (1335 / 100) ≤ 633600 := by
      have := Real.exp_one_lt_d9
      have e13 : Real.exp (1335 / 100) = Real.exp 1 ^ 13 * Real.exp (35 / 100) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
      have h35 : Real.exp (35 / 100) ≤ 1.43 := by
        have := Real.exp_bound' (x := 35 / 100) (by norm_num) (by norm_num) (n := 4) (by norm_num)
        norm_num [Finset.sum_range_succ, Nat.factorial] at this
        linarith
      rw [e13]
      have hpow : Real.exp 1 ^ 13 ≤ 2.7182818286 ^ 13 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le this.le 13
      calc Real.exp 1 ^ 13 * Real.exp (35 / 100) ≤ 2.7182818286 ^ 13 * 1.43 :=
            mul_le_mul hpow h35 (Real.exp_pos _).le (by positivity)
        _ ≤ 633600 := by norm_num
    exact hb
  have hlog2 := Real.log_two_gt_d9
  push_cast at h2
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  nlinarith

/-- The coefficient of the grid of free level `≥ 20` is below `0.95` times the tree's. -/
theorem coef20_le_tree {n m d q : ℕ} (hn : 2 ^ 23 ≤ n) (hm1 : 1 ≤ m)
    (hPm : 16 * GroupedOrder.lamN n * (20 * 4 ^ m) ^ 2 ≤ n)
    (h4d : 16 * GroupedOrder.lamN n * (4 ^ m * d) ^ 2 ≤ n) (hd20 : 20 ≤ d)
    (hdj : d < 30 ∨ 6 ^ m * d < 80 * 4 ^ m) (hq : q ≤ 6 * m + d) :
    1 + 8.8 * Real.sqrt (GroupedOrder.lamN n) * (172 + 53 * (q : ℝ) / (GroupedOrder.lamN n)) +
      240.96 * ((m : ℝ) + 1) ≤ 0.95 * (97 * Real.log n + 2670) * Real.sqrt (Real.log n) := by
  have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by decide) n
  have hge : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hE23 : 23 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
  have hlam : GroupedOrder.lamN n = 3 * (Nat.log 2 n + 1) := rfl
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  generalize Nat.log 2 n = E at hlt hge hE23 hlam
  have hLE : (E : ℝ) * 0.69314 ≤ Real.log n := by
    have c : ((2 ^ E : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hge
    push_cast at c
    have := Real.log_le_log (by positivity) c
    rw [Real.log_pow] at this
    have := Real.log_two_gt_d9
    have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg _
    nlinarith
  rw [hlam] at hPm h4d ⊢
  rcases Nat.lt_or_ge E 32 with hE | hE
  · interval_cases E
    · -- `⌊log₂ n⌋ = 23`
      have e : 3 * (23 + 1) = 72 := by norm_num
      rw [e] at hPm h4d ⊢
      have hm : m ≤ 1 := m_le_of hPm hlt (by norm_num)
      have hd : d ≤ 30 := d_le_of h4d hlt hm1 (by norm_num)
      exact num_check (lam := 72) (a := 8.4853) (Lb := 15.94222) (t := 3.992) (qb := 36) (mb := 1)
        (by norm_num) (by norm_num) (by norm_num) (by omega) hm (by push_cast at hLE; linarith)
        (by norm_num) (by norm_num) (by norm_num)
    · -- `⌊log₂ n⌋ = 24`
      have e : 3 * (24 + 1) = 75 := by norm_num
      rw [e] at hPm h4d ⊢
      have hm : m ≤ 1 := m_le_of hPm hlt (by norm_num)
      have hd : d ≤ 41 := d_le_of h4d hlt hm1 (by norm_num)
      exact num_check (lam := 75) (a := 8.6603) (Lb := 16.63536) (t := 4.078) (qb := 47) (mb := 1)
        (by norm_num) (by norm_num) (by norm_num) (by omega) hm (by push_cast at hLE; linarith)
        (by norm_num) (by norm_num) (by norm_num)
    · -- `⌊log₂ n⌋ = 25`
      have e : 3 * (25 + 1) = 78 := by norm_num
      rw [e] at hPm h4d ⊢
      have hm : m ≤ 1 := m_le_of hPm hlt (by norm_num)
      have hd : d ≤ 53 := d_le53 hm1 hdj
      exact num_check (lam := 78) (a := 8.8318) (Lb := 17.3285) (t := 4.162) (qb := 59) (mb := 1)
        (by norm_num) (by norm_num) (by norm_num) (by omega) hm (by push_cast at hLE; linarith)
        (by norm_num) (by norm_num) (by norm_num)
    · -- `⌊log₂ n⌋ = 26`
      have e : 3 * (26 + 1) = 81 := by norm_num
      rw [e] at hPm h4d ⊢
      have hm : m ≤ 2 := m_le_of hPm hlt (by norm_num)
      have hd : d ≤ 53 := d_le53 hm1 hdj
      exact num_check (lam := 81) (a := 9.0) (Lb := 18.02164) (t := 4.245) (qb := 65) (mb := 2)
        (by norm_num) (by norm_num) (by norm_num) (by omega) hm (by push_cast at hLE; linarith)
        (by norm_num) (by norm_num) (by norm_num)
    · -- `⌊log₂ n⌋ = 27`
      have e : 3 * (27 + 1) = 84 := by norm_num
      rw [e] at hPm h4d ⊢
      have hm : m ≤ 2 := m_le_of hPm hlt (by norm_num)
      have hd : d ≤ 53 := d_le53 hm1 hdj
      exact num_check (lam := 84) (a := 9.1652) (Lb := 18.71478) (t := 4.326) (qb := 65) (mb := 2)
        (by norm_num) (by norm_num) (by norm_num) (by omega) hm (by push_cast at hLE; linarith)
        (by norm_num) (by norm_num) (by norm_num)
    · -- `⌊log₂ n⌋ = 28`
      have e : 3 * (28 + 1) = 87 := by norm_num
      rw [e] at hPm h4d ⊢
      have hm : m ≤ 2 := m_le_of hPm hlt (by norm_num)
      have hd : d ≤ 53 := d_le53 hm1 hdj
      exact num_check (lam := 87) (a := 9.3274) (Lb := 19.40792) (t := 4.405) (qb := 65) (mb := 2)
        (by norm_num) (by norm_num) (by norm_num) (by omega) hm (by push_cast at hLE; linarith)
        (by norm_num) (by norm_num) (by norm_num)
    · -- `⌊log₂ n⌋ = 29`
      have e : 3 * (29 + 1) = 90 := by norm_num
      rw [e] at hPm h4d ⊢
      have hm : m ≤ 2 := m_le_of hPm hlt (by norm_num)
      have hd : d ≤ 53 := d_le53 hm1 hdj
      exact num_check (lam := 90) (a := 9.4869) (Lb := 20.10106) (t := 4.483) (qb := 65) (mb := 2)
        (by norm_num) (by norm_num) (by norm_num) (by omega) hm (by push_cast at hLE; linarith)
        (by norm_num) (by norm_num) (by norm_num)
    · -- `⌊log₂ n⌋ = 30`
      have e : 3 * (30 + 1) = 93 := by norm_num
      rw [e] at hPm h4d ⊢
      have hm : m ≤ 2 := m_le_of hPm hlt (by norm_num)
      have hd : d ≤ 53 := d_le53 hm1 hdj
      exact num_check (lam := 93) (a := 9.6437) (Lb := 20.7942) (t := 4.56) (qb := 65) (mb := 2)
        (by norm_num) (by norm_num) (by norm_num) (by omega) hm (by push_cast at hLE; linarith)
        (by norm_num) (by norm_num) (by norm_num)
    · -- `⌊log₂ n⌋ = 31`
      have e : 3 * (31 + 1) = 96 := by norm_num
      rw [e] at hPm h4d ⊢
      have hm : m ≤ 3 := m_le_of hPm hlt (by norm_num)
      have hd : d ≤ 53 := d_le53 hm1 hdj
      exact num_check (lam := 96) (a := 9.798) (Lb := 21.48734) (t := 4.635) (qb := 71) (mb := 3)
        (by norm_num) (by norm_num) (by norm_num) (by omega) hm (by push_cast at hLE; linarith)
        (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ ≥ 32`
    have hd : d ≤ 53 := d_le53 hm1 hdj
    have hl99 : 99 ≤ 3 * (E + 1) := by omega
    have hD := depth20_log (n := n) (m := m) (by rw [hlam]; exact hl99) (by rw [hlam]; exact hPm)
    have hlamL : ((3 * (E + 1) : ℕ) : ℝ) ≤ 43281 / 10000 * Real.log n + 3 := by
      rw [← hlam]; exact lam_le_log (by omega)
    have hlamG : 4328 / 1000 * Real.log n ≤ ((3 * (E + 1) : ℕ) : ℝ) := by
      rw [← hlam]; exact lam_ge_log (by omega)
    set L := Real.log n with hL
    have hL22 : 22.18 ≤ L := by
      have : (32 : ℝ) ≤ E := by exact_mod_cast hE
      linarith
    set t := Real.sqrt L with ht
    have ht2 : t ^ 2 = L := Real.sq_sqrt (by linarith)
    have ht0 : 4.709 ≤ t := by
      rw [ht, show (4.709 : ℝ) = Real.sqrt (4.709 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num; linarith)
    set lr : ℝ := ((3 * (E + 1) : ℕ) : ℝ) with hlr
    have hlr0 : 0 < lr := by rw [hlr]; positivity
    set S := Real.sqrt lr with hS
    have hS2 : S ^ 2 = lr := Real.sq_sqrt hlr0.le
    have hSU : S ≤ 2.1261 * t := by
      have h1 : lr ≤ 4.5203 * L := by linarith
      calc S ≤ Real.sqrt (4.5203 * L) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt 4.5203 * Real.sqrt L := Real.sqrt_mul (by norm_num) _
        _ ≤ 2.1261 * t := by
            apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
            rw [show (2.1261 : ℝ) = Real.sqrt (2.1261 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
            exact Real.sqrt_le_sqrt (by norm_num)
    have hSD : 2.0803 * t ≤ S := by
      have h1 : 4.328 * L ≤ lr := by linarith
      calc 2.0803 * t ≤ Real.sqrt 4.328 * Real.sqrt L := by
            apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
            rw [show (2.0803 : ℝ) = Real.sqrt (2.0803 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
            exact Real.sqrt_le_sqrt (by norm_num)
        _ = Real.sqrt (4.328 * L) := (Real.sqrt_mul (by norm_num) _).symm
        _ ≤ S := Real.sqrt_le_sqrt h1
    have hqr : (q : ℝ) ≤ 6 * (m : ℝ) + 53 := by exact_mod_cast (show q ≤ 6 * m + 53 by omega)
    have := gen_coef L t S m q ht2 ht0 hSU hSD (by linarith) (Nat.cast_nonneg _) hqr
      (Nat.cast_nonneg _)
    rw [hS2] at this
    exact this

/-- **The port algorithm beats the tree bound**: for `n ≥ 2²³`,
`OPT(B) ≤ M(B) + 0.95 (97 ln n + 2670) √(ln n) n^(5/2)`. -/
theorem port_beats_tree {n : ℕ} [NeZero n] (hn : 2 ^ 23 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      0.95 * (97 * Real.log n + 2670) * Real.sqrt (Real.log n) * (n : ℝ) ^ ((5 : ℝ) / 2) := by
  obtain ⟨m, d, q, hm1, hPm, h4d, hd20, hdj, hq, hopt⟩ := port_coef20 hn B
  have hc := coef20_le_tree hn hm1 hPm h4d hd20 hdj hq
  have hP : (0 : ℝ) ≤ (n : ℝ) ^ ((5 : ℝ) / 2) := by positivity
  have := mul_le_mul_of_nonneg_right hc hP
  linarith

end SlidingPuzzle.Port
