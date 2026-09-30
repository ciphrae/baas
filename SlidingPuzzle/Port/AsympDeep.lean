import SlidingPuzzle.Port.Grid4
import SlidingPuzzle.Port.Asymp

/-! # The port algorithm on the deep grid

`OPT(B) ≤ M(B) + (87 ln n + 3900 √(ln n) + 19500 / √(ln n)) n^(5/2)` for `n ≥ 2²³`. -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle
open SlidingPuzzle.Tree

/-- `λ ≥ 4.328 ln n`. -/
theorem lam_ge_log {n : ℕ} (hn : 1 ≤ n) :
    4328 / 1000 * Real.log n ≤ (GroupedOrder.lamN n : ℝ) := by
  set E := Nat.log 2 n with hE
  have hlt : n < 2 ^ (E + 1) := Nat.lt_pow_succ_log_self (by decide) n
  have hlog : Real.log n ≤ ((E : ℝ) + 1) * Real.log 2 := by
    have c : ((n : ℕ) : ℝ) ≤ ((2 ^ (E + 1) : ℕ) : ℝ) := by exact_mod_cast hlt.le
    push_cast at c
    have := Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) c
    rw [Real.log_pow] at this; push_cast at this; linarith
  have h2 := Real.log_two_lt_d9
  have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg _
  have hcast : (GroupedOrder.lamN n : ℝ) = 3 * ((E : ℝ) + 1) := by
    unfold GroupedOrder.lamN; push_cast; ring
  rw [hcast]
  have hE1 : (0 : ℝ) < (E : ℝ) + 1 := by linarith
  have := mul_lt_mul_of_pos_left h2 hE1
  nlinarith

/-- The depth of the deep grid against `ln n`: `2.7725 m ≤ ln n - 13.97`. -/
theorem deep_depth_log {n m : ℕ} (hl : 72 ≤ GroupedOrder.lamN n)
    (h : 16 * GroupedOrder.lamN n * (32 * 4 ^ m) ^ 2 ≤ n) :
    27725 / 10000 * (m : ℝ) ≤ Real.log n - 1397 / 100 := by
  have hpos : (0 : ℝ) < 16 * GroupedOrder.lamN n := by
    have : (0 : ℝ) < GroupedOrder.lamN n := by exact_mod_cast (show 0 < GroupedOrder.lamN n by omega)
    linarith
  have e : 16 * GroupedOrder.lamN n * (32 * 4 ^ m) ^ 2 = 16 * GroupedOrder.lamN n * 2 ^ (10 + 4 * m) := by
    have e1 : (4 : ℕ) ^ m = 2 ^ (2 * m) := by rw [pow_mul]; norm_num
    have e2 : (32 * 2 ^ (2 * m)) ^ 2 = 2 ^ (10 + 4 * m) := by
      rw [show (32 : ℕ) = 2 ^ 5 by norm_num, ← pow_add, ← pow_mul]; ring_nf
    rw [e1, e2]
  rw [e] at h
  have h1 : (16 * GroupedOrder.lamN n : ℝ) * (2 : ℝ) ^ (10 + 4 * m) ≤ n := by exact_mod_cast h
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_mul hpos.ne' (by positivity), Real.log_pow] at h2
  have h3 : Real.log 1152 ≤ Real.log (16 * GroupedOrder.lamN n : ℝ) := by
    apply Real.log_le_log (by norm_num)
    have : (72 : ℝ) ≤ GroupedOrder.lamN n := by exact_mod_cast hl
    linarith
  have := log_1152_ge
  have hlog2 := Real.log_two_gt_d9
  push_cast at h2
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  nlinarith

/-- The coefficient of the deep grid, as pure real arithmetic. -/
theorem deep_coef (L t S mr qr w : ℝ) (ht : t ^ 2 = L) (ht0 : 3.99 ≤ t)
    (hSU : S ≤ 2.1261 * t) (hSD : 2.0803 * t ≤ S) (hD : 2.7725 * mr ≤ L - 13.97) (hm0 : 0 ≤ mr)
    (hq : qr ≤ 6 * mr + 128) (hw : w * S = qr) (hw0 : 0 ≤ w) :
    1 + 1615 * S + 414.38 * w + 240.96 * (mr + 1) ≤ 87 * L + 3900 * t + 19500 / t := by
  have htp : 0 < t := by linarith
  set u := 1 / t with hu
  have hu0 : 0 < u := by positivity
  have htu : t * u = 1 := by rw [hu]; field_simp
  have h19 : 19500 / t = 19500 * u := by rw [hu]; ring
  rw [h19]
  -- `2.7725 m u ≤ t - 13.97 u`
  have h1 : 2.7725 * (mr * u) ≤ t - 13.97 * u := by
    have := mul_le_mul_of_nonneg_right hD hu0.le
    have e : (L - 13.97) * u = t - 13.97 * u := by
      rw [← ht]; have : t ^ 2 * u = t * (t * u) := by ring
      rw [sub_mul, this, htu]; ring
    linarith
  -- `2.0803 w ≤ (6 m + 128) u`
  have h2 : 2.0803 * w ≤ 6 * (mr * u) + 128 * u := by
    have a : w * (2.0803 * t) ≤ w * S := mul_le_mul_of_nonneg_left hSD hw0
    have b : w * (2.0803 * t) ≤ 6 * mr + 128 := by linarith
    have c := mul_le_mul_of_nonneg_right b hu0.le
    have e : w * (2.0803 * t) * u = 2.0803 * w := by
      have : w * (2.0803 * t) * u = 2.0803 * w * (t * u) := by ring
      rw [this, htu, mul_one]
    linarith
  have h3 : 240.96 * (mr + 1) ≤ 86.92 * L - 973 := by linarith
  have h4 : 1615 * S ≤ 3433.7 * t := by linarith
  have h5 : 0 ≤ mr * u := by positivity
  have h6 : t ≤ L := by nlinarith
  nlinarith

set_option maxHeartbeats 2000000 in
/-- **`OPT(B) ≤ M(B) + (87 ln n + 3900 √(ln n) + 19500/√(ln n)) n^(5/2)`** for `n ≥ 2²³`. -/
theorem port_optimalLength_le_deep {n : ℕ} [NeZero n] (hn : 2 ^ 23 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      (87 * Real.log n + 3900 * Real.sqrt (Real.log n) + 19500 / Real.sqrt (Real.log n)) *
        (n : ℝ) ^ ((5 : ℝ) / 2) := by
  obtain ⟨m, K, q, σ, hPm, hlo, hround, hK64, hq128, hσ, hnat⟩ := port_deep hn B
  set lam := GroupedOrder.lamN n with hlam
  have hl72 : 72 ≤ lam := lam_ge hn
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hD := deep_depth_log hl72 hPm
  have hlamL : (lam : ℝ) ≤ 43281 / 10000 * Real.log n + 3 := lam_le_log hn1
  have hlamG : 4328 / 1000 * Real.log n ≤ (lam : ℝ) := lam_ge_log hn1
  have hL0 := log_ge_of_pow23 hn
  -- the natural facts used below
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
  set L := Real.log n with hL
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
  have hroundR : nr ≤ 1156 / 64 * lr * Kr ^ 2 := by
    have : (64 * n : ℝ) ≤ 1156 * lr * Kr ^ 2 := by rw [hlr, hKr]; exact_mod_cast hround.le
    rw [hnr]; linarith
  have hK1024R : 1024 * Kr ^ 2 ≤ nr := by rw [hKr, hnr]; exact_mod_cast hK1024
  have hσR : sr * sr ≤ 13 * nr := by rw [hsr, hnr]; exact_mod_cast hσ
  have hsr0 : 0 ≤ sr := by rw [hsr]; exact Nat.cast_nonneg _
  have hq128R : qr ≤ 6 * mr + 128 := by rw [hqr, hmr]; exact_mod_cast hq128
  have hq0 : 0 ≤ qr := by rw [hqr]; exact Nat.cast_nonneg _
  have hm0 : 0 ≤ mr := by rw [hmr]; exact Nat.cast_nonneg _
  have hnbig : (8388608 : ℝ) ≤ nr := by rw [hnr]; exact_mod_cast hbig
  -- the natural bound, cast
  have hcast : (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      2 * ((15 * nr ^ 2 + 3002 * nr + 1) * Kr) +
      2 * (190 * (Kr ^ 2 * s ^ 3) + 780 * (Kr ^ 3 * qr * s ^ 2) +
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
  -- `√n ≤ 4.25 √λ K`, `32 K ≤ √n`
  have hup : Real.sqrt nr ≤ 4.25 * Real.sqrt lr * Kr := by
    rw [show 4.25 * Real.sqrt lr * Kr = Real.sqrt (1156 / 64 * lr * Kr ^ 2) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_sq hKpos.le,
        show (1156 / 64 : ℝ) = 4.25 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
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
  -- the grid term `K² s³ ≤ 4.25 √λ P`
  have hmain : Kr ^ 2 * s ^ 3 ≤ 4.25 * Real.sqrt lr * P := by
    have h1 : Kr ^ 2 * s ^ 3 * Kr ≤ nr ^ 3 := by
      have := pow_le_pow_left₀ (by positivity) (show s * Kr ≤ nr by linarith) 3
      calc Kr ^ 2 * s ^ 3 * Kr = (s * Kr) ^ 3 := by ring
        _ ≤ _ := this
    have h2 : nr ^ 3 ≤ 4.25 * Real.sqrt lr * P * Kr := by
      rw [hPe]
      have e3 : nr ^ 3 = nr ^ 2 * Real.sqrt nr * Real.sqrt nr := by
        rw [mul_assoc, ← sq, hsq_n]; ring
      rw [e3]
      have := mul_le_mul_of_nonneg_left hup (by positivity : (0 : ℝ) ≤ nr ^ 2 * Real.sqrt nr)
      calc nr ^ 2 * Real.sqrt nr * Real.sqrt nr ≤ _ := this
        _ = _ := by ring
    exact le_of_mul_le_mul_right (le_trans h1 h2) hKpos
  -- the lane term `K³ q s² ≤ q/(16 λ) · K² s³`
  have hV : 16 * lr * (Kr ^ 3 * qr * s ^ 2) ≤ qr * (Kr ^ 2 * s ^ 3) := by
    have := mul_le_mul_of_nonneg_left hsKr (by positivity : (0 : ℝ) ≤ qr * Kr ^ 2 * s ^ 2)
    calc 16 * lr * (Kr ^ 3 * qr * s ^ 2) = qr * Kr ^ 2 * s ^ 2 * (16 * lr * Kr) := by ring
      _ ≤ qr * Kr ^ 2 * s ^ 2 * s := this
      _ = _ := by ring
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
  -- the coefficient
  set t := Real.sqrt L with ht
  have ht2 : t ^ 2 = L := Real.sq_sqrt (by linarith)
  have ht0 : (3.99 : ℝ) ≤ t := by
    rw [ht, show (3.99 : ℝ) = Real.sqrt (3.99 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hlrU : Real.sqrt lr ≤ 2.1261 * t := by
    have h1 : lr ≤ 4.5203 * L := by linarith
    calc Real.sqrt lr ≤ Real.sqrt (4.5203 * L) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt 4.5203 * Real.sqrt L := Real.sqrt_mul (by norm_num) _
      _ ≤ 2.1261 * t := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          rw [show (2.1261 : ℝ) = Real.sqrt (2.1261 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
          exact Real.sqrt_le_sqrt (by norm_num)
  have hlrD : 2.0803 * t ≤ Real.sqrt lr := by
    have h1 : 4.328 * L ≤ lr := by linarith
    calc 2.0803 * t ≤ Real.sqrt 4.328 * Real.sqrt L := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          rw [show (2.0803 : ℝ) = Real.sqrt (2.0803 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
          exact Real.sqrt_le_sqrt (by norm_num)
      _ = Real.sqrt (4.328 * L) := (Real.sqrt_mul (by norm_num) _).symm
      _ ≤ Real.sqrt lr := Real.sqrt_le_sqrt h1
  -- `780 K³ q s² ≤ 207.19 (q / √λ) P`
  have hslp : 0 < Real.sqrt lr := Real.sqrt_pos.2 hlr0
  have hsqlr : Real.sqrt lr * Real.sqrt lr = lr := Real.mul_self_sqrt hlr0.le
  set w := qr / Real.sqrt lr with hw
  have hqw : qr = w * Real.sqrt lr := by rw [hw]; field_simp
  have hw0 : 0 ≤ w := by positivity
  have hlane : 780 * (Kr ^ 3 * qr * s ^ 2) ≤ 207.19 * w * P := by
    have h1 : 16 * lr * (Kr ^ 3 * qr * s ^ 2) ≤ qr * (4.25 * Real.sqrt lr * P) :=
      le_trans hV (mul_le_mul_of_nonneg_left hmain hq0)
    have h2 : Real.sqrt lr * (16 * Real.sqrt lr * (Kr ^ 3 * qr * s ^ 2)) ≤
        Real.sqrt lr * (4.25 * w * P * Real.sqrt lr) := by
      calc Real.sqrt lr * (16 * Real.sqrt lr * (Kr ^ 3 * qr * s ^ 2))
          = 16 * (Real.sqrt lr * Real.sqrt lr) * (Kr ^ 3 * qr * s ^ 2) := by ring
        _ = 16 * lr * (Kr ^ 3 * qr * s ^ 2) := by rw [hsqlr]
        _ ≤ qr * (4.25 * Real.sqrt lr * P) := h1
        _ = Real.sqrt lr * (4.25 * w * P * Real.sqrt lr) := by rw [hqw]; ring
    have h3 := le_of_mul_le_mul_left h2 hslp
    have h4 : 16 * (Kr ^ 3 * qr * s ^ 2) * Real.sqrt lr ≤ 4.25 * w * P * Real.sqrt lr := by
      linarith
    have h5 := le_of_mul_le_mul_right h4 hslp
    have : 0 ≤ w * P := by positivity
    linarith
  -- `q / √λ ≤ 1.0402 t + 47 / t`
  have hcoef : 1 + 1615 * Real.sqrt lr + 414.38 * w + 240.96 * (mr + 1) ≤
      87 * L + 3900 * t + 19500 / t := by
    have hD' : 2.7725 * mr ≤ L - 13.97 := by linarith
    have hwS : w * Real.sqrt lr = qr := by rw [hqw]
    exact deep_coef L t (Real.sqrt lr) mr qr w ht2 ht0 hlrU hlrD hD' hm0 hq128R hwS.symm.symm hw0
  have hsum : (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      (1 + 1615 * Real.sqrt lr + 414.38 * w + 240.96 * (mr + 1)) * P := by
    have a1 : 380 * (Kr ^ 2 * s ^ 3) ≤ 380 * (4.25 * Real.sqrt lr * P) :=
      mul_le_mul_of_nonneg_left hmain (by norm_num)
    have e : (1 + 1615 * Real.sqrt lr + 414.38 * w + 240.96 * (mr + 1)) * P =
        P + 380 * (4.25 * Real.sqrt lr * P) + 2 * (207.19 * w * P) + 2 * (120.48 * (mr + 1) * P) := by
      ring
    rw [e]
    linarith only [hcast, hpre, a1, hlane, hhop]
  have hfin := mul_le_mul_of_nonneg_right hcoef hP0
  linarith only [hsum, hfin]

end SlidingPuzzle.Port
