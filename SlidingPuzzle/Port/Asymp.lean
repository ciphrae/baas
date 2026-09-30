import SlidingPuzzle.Port.Fine

/-! # The port algorithm: error `(29 ln n + 5300 √(ln n)) n^(5/2)`

From `port_fine`: the grid part costs `600 K² (n/K)³ ≤ 600 (33/8) √λ n^(5/2)`, the cheap
hops `4 h hopKc n²` with `hopKc ≤ 61 √n` (ports of side `σ ≤ √(13 n)`) and depth
`h ≤ (ln n + 1.52)/8.56`. -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle
open SlidingPuzzle.Tree

/-- **`OPT(B) ≤ M(B) + (29 ln n + 5300 √(ln n)) n^(5/2)`** for `n ≥ 2²³`. -/
theorem port_optimalLength_le {n : ℕ} [NeZero n] (hn : 2 ^ 23 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      (29 * Real.log n + 5300 * Real.sqrt (Real.log n)) * (n : ℝ) ^ ((5 : ℝ) / 2) := by
  obtain ⟨h, K, hh, h73, -, hK64, hlo, hhi, σ, hσ, hnat⟩ := port_fine hn B
  set lam := GroupedOrder.lamN n with hlam
  have hl72 : 72 ≤ lam := lam_ge hn
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hD := depth_le_log hh hl72 h73
  have hlamL : (lam : ℝ) ≤ 43281 / 10000 * Real.log n + 3 := lam_le_log hn1
  have hL0 := log_ge_of_pow23 hn
  set L := Real.log n with hL
  set nr : ℝ := (n : ℝ) with hnr
  set Kr : ℝ := (K : ℝ) with hKr
  set lr : ℝ := (lam : ℝ) with hlr
  set sr : ℝ := (σ : ℝ) with hsr
  set hr : ℝ := (h : ℝ) with hhr
  have hKpos : 0 < Kr := by rw [hKr]; exact_mod_cast (show 0 < K by omega)
  have hl64 : (64 : ℝ) ≤ lr := by rw [hlr]; exact_mod_cast (show 64 ≤ lam by omega)
  have hloR : 16 * lr * Kr ^ 2 ≤ nr := by rw [hlr, hKr, hnr]; exact_mod_cast hlo
  have hhiR : nr ≤ 1089 / 64 * lr * Kr ^ 2 := by
    have : (64 * n : ℝ) ≤ 1089 * lr * Kr ^ 2 := by rw [hlr, hKr]; exact_mod_cast hhi.le
    rw [hnr]; linarith
  have hσR : sr * sr ≤ 13 * nr := by rw [hsr, hnr]; exact_mod_cast hσ
  have hsr0 : 0 ≤ sr := by rw [hsr]; exact Nat.cast_nonneg _
  have hhr1 : (1 : ℝ) ≤ hr := by rw [hhr]; exact_mod_cast hh
  -- the natural bound, cast
  have hcast : (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      2 * ((15 * nr ^ 2 + 3002 * nr + 1) * Kr) +
      2 * (300 * (Kr ^ 2 * ((n / K : ℕ) : ℝ) ^ 3) +
        (12 * sr + 526 * Kr + 1535) * (2 * hr * (Kr * ((n / K : ℕ) : ℝ)) ^ 2)) := by
    have := (Nat.cast_le (α := ℝ)).2 hnat
    unfold hopKc at this
    push_cast at this
    rw [hnr, hKr, hsr, hhr]
    exact this
  -- `n^(5/2) = n² √n`
  set P : ℝ := nr ^ ((5 : ℝ) / 2) with hP
  have hsn : 0 ≤ Real.sqrt nr := Real.sqrt_nonneg _
  have hPe : P = nr ^ 2 * Real.sqrt nr := by
    rw [hP, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hn0]; norm_num
  have hsq_n : Real.sqrt nr ^ 2 = nr := Real.sq_sqrt hn0.le
  have hnbig : (8388608 : ℝ) ≤ nr := by
    have c : ((8388608 : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 (by norm_num at hn ⊢; exact hn)
    rw [hnr]; exact_mod_cast c
  have hP0 : 0 ≤ P := by rw [hPe]; positivity
  -- `√n ≤ (33/8) √λ K` and `32 K ≤ √n`
  have hsl : 0 ≤ Real.sqrt lr := Real.sqrt_nonneg _
  have hup : Real.sqrt nr ≤ 33 / 8 * Real.sqrt lr * Kr := by
    rw [show 33 / 8 * Real.sqrt lr * Kr = Real.sqrt (1089 / 64 * lr * Kr ^ 2) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_sq hKpos.le,
        show (1089 / 64 : ℝ) = (33 / 8) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hhiR
  have hdown : 32 * Kr ≤ Real.sqrt nr := by
    rw [show 32 * Kr = Real.sqrt ((32 * Kr) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    have := mul_le_mul_of_nonneg_right hl64 (sq_nonneg Kr)
    linarith
  -- `σ ≤ 3.6056 √n`
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
  -- the grid term: `K² ⌊n/K⌋³ ≤ n³ / K ≤ (33/8) √λ n^(5/2)`
  set m : ℝ := ((n / K : ℕ) : ℝ) with hm
  have hm0 : 0 ≤ m := by positivity
  have hmK : m * Kr ≤ nr := by
    have : K * (n / K) ≤ n := Nat.mul_div_le n _
    have : (K : ℝ) * ((n / K : ℕ) : ℝ) ≤ n := by exact_mod_cast this
    rw [hm, hKr, hnr]; linarith
  have hmain : Kr ^ 2 * m ^ 3 ≤ 33 / 8 * Real.sqrt lr * P := by
    have h1 : Kr ^ 2 * m ^ 3 * Kr ≤ nr ^ 3 := by
      have := pow_le_pow_left₀ (by positivity) hmK 3
      calc Kr ^ 2 * m ^ 3 * Kr = (m * Kr) ^ 3 := by ring
        _ ≤ _ := this
    have h2 : nr ^ 3 ≤ 33 / 8 * Real.sqrt lr * P * Kr := by
      rw [hPe]
      have e3 : nr ^ 3 = nr ^ 2 * Real.sqrt nr * Real.sqrt nr := by
        rw [mul_assoc, ← sq, hsq_n]; ring
      rw [e3]
      have := mul_le_mul_of_nonneg_left hup (by positivity : (0 : ℝ) ≤ nr ^ 2 * Real.sqrt nr)
      calc nr ^ 2 * Real.sqrt nr * Real.sqrt nr ≤ _ := this
        _ = _ := by ring
    exact le_of_mul_le_mul_right (le_trans h1 h2) hKpos
  -- the prefix term
  have hpre : 2 * ((15 * nr ^ 2 + 3002 * nr + 1) * Kr) ≤ P := by
    have hn3003 : (3003 : ℝ) ≤ nr := by linarith
    have hsq : 3003 * nr ≤ nr ^ 2 := by
      have := mul_le_mul_of_nonneg_right hn3003 hn0.le
      rw [sq]; linarith
    have ha : 15 * nr ^ 2 + 3002 * nr + 1 ≤ 16 * nr ^ 2 := by linarith
    have h1 := mul_le_mul_of_nonneg_right ha hKpos.le
    have h2 := mul_le_mul_of_nonneg_left hdown (by positivity : (0 : ℝ) ≤ nr ^ 2)
    rw [hPe]; linarith
  -- the cheap hops: `hopKc · 2h (K m)² ≤ 60.24 √n · 2 h n²`
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
  -- the logarithms
  have hlr : Real.sqrt lr ≤ 2.1261 * Real.sqrt L := by
    have h1 : lr ≤ 4.5203 * L := by linarith
    calc Real.sqrt lr ≤ Real.sqrt (4.5203 * L) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt 4.5203 * Real.sqrt L := Real.sqrt_mul (by norm_num) _
      _ ≤ 2.1261 * Real.sqrt L := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          rw [show (2.1261 : ℝ) = Real.sqrt (2.1261 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
          exact Real.sqrt_le_sqrt (by norm_num)
  have hsL : (3.99 : ℝ) ≤ Real.sqrt L := by
    rw [show (3.99 : ℝ) = Real.sqrt (3.99 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hhL : 240.96 * hr ≤ 28.15 * L + 42.79 := by linarith
  have hcoef : 1 + 2 * 300 * (33 / 8) * Real.sqrt lr + 2 * 120.48 * hr ≤
      29 * L + 5300 * Real.sqrt L := by linarith
  calc (optimalLength B : ℝ) ≤ _ := hcast
    _ ≤ (manhattan B.val : ℝ) + (1 + 2 * 300 * (33 / 8) * Real.sqrt lr + 2 * 120.48 * hr) * P := by
        have e : (Kr * m) = Kr * m := rfl
        linarith
    _ ≤ (manhattan B.val : ℝ) + (29 * L + 5300 * Real.sqrt L) * P := by
        have := mul_le_mul_of_nonneg_right hcoef hP0
        linarith

end SlidingPuzzle.Port
