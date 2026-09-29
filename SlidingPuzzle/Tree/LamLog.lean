import SlidingPuzzle.Tree.LamGrid

/-! # Error `(117 ln n + 4100) √(ln n) n^(5/2)`

From `optimalLength_le_lam`: the cost is at most `(1 + 10(48h + 142)√λ) n^(5/2)`, with
`73^(2(h-1)) ≤ n` (so `48h ≤ 48 + 5.6075 ln n`) and `λ ≤ 4.3281 ln n + 3`. -/
namespace SlidingPuzzle.Tree

theorem log_73_ge : (107 / 25 : ℝ) ≤ Real.log 73 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 : Real.exp (107 / 25) ^ 25 = Real.exp 1 ^ 107 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 : Real.exp 1 ^ 107 ≤ (2.7182818286 : ℝ) ^ 107 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le h2.le 107
  have h5 : (2.7182818286 : ℝ) ^ 107 ≤ 73 ^ 25 := by norm_num
  have h4 : Real.exp (107 / 25) ^ 25 ≤ (73 : ℝ) ^ 25 := by rw [h1]; exact h3.trans h5
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num)).1 h4

/-- `λ ≤ 4.3281 ln n + 3`. -/
theorem lam_le_log {n : ℕ} (hn : 1 ≤ n) :
    (GroupedOrder.lamN n : ℝ) ≤ 43281 / 10000 * Real.log n + 3 := by
  set E := Nat.log 2 n with hE
  have hpow : (2 : ℝ) ^ E ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hlog : (E : ℝ) * Real.log 2 ≤ Real.log n := by
    have := Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow] at this
  have h2 := Real.log_two_gt_d9
  have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg _
  have hcast : (GroupedOrder.lamN n : ℝ) = 3 * ((E : ℝ) + 1) := by
    unfold GroupedOrder.lamN; push_cast; ring
  rw [hcast]
  nlinarith

/-- The cubic behind the coefficient `117`. -/
theorem coef_poly {L : ℝ} (hL : 797 / 50 ≤ L) :
    (1900 + 56075 / 1000 * L) ^ 2 * (43281 / 10000 * L + 3) ≤ (117 * L + 4099) ^ 2 * L := by
  have ht : 0 ≤ L - 797 / 50 := by linarith
  have ht2 := mul_nonneg ht ht
  have ht3 := mul_nonneg ht2 ht
  nlinarith

/-- `1 + 10 (48h + 142) √λ ≤ (117 L + 4100) √L`. -/
theorem coef_le {H lam L : ℝ} (hH : 214 / 25 * (H - 1) ≤ L) (hH0 : 0 ≤ H)
    (hlam : lam ≤ 43281 / 10000 * L + 3) (hlam0 : 0 ≤ lam) (hL : 797 / 50 ≤ L) :
    1 + 10 * (48 * H + 142) * Real.sqrt lam ≤ (117 * L + 4100) * Real.sqrt L := by
  have hL0 : 0 ≤ L := by linarith
  set A := 10 * (48 * H + 142) with hA
  have hA0 : 0 ≤ A := by positivity
  have hAle : A ≤ 1900 + 56075 / 1000 * L := by rw [hA]; linarith
  have hsq : A ^ 2 * lam ≤ (117 * L + 4099) ^ 2 * L := by
    have h1 : A ^ 2 ≤ (1900 + 56075 / 1000 * L) ^ 2 := pow_le_pow_left₀ hA0 hAle 2
    calc A ^ 2 * lam ≤ (1900 + 56075 / 1000 * L) ^ 2 * (43281 / 10000 * L + 3) :=
          mul_le_mul h1 hlam hlam0 (by positivity)
      _ ≤ _ := coef_poly hL
  have hroot : A * Real.sqrt lam ≤ (117 * L + 4099) * Real.sqrt L := by
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hA0,
      Real.sqrt_sq (by positivity)] at this
  have h1 : 1 ≤ Real.sqrt L := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  linarith

open SlidingPuzzle in
/-- **Error `n^(5/2) (ln n)^(3/2)` with leading constant `117`**: for `n ≥ 2²³`,
`OPT(B) ≤ M(B) + (117 ln n + 4100) √(ln n) · n^(5/2)`. -/
theorem tree_lam_approximation {n : ℕ} [NeZero n] (hn : 2 ^ 23 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      (117 * Real.log n + 4100) * Real.sqrt (Real.log n) * (n : ℝ) ^ ((5 : ℝ) / 2) := by
  obtain ⟨h, K, hh, h73, hK64, hlo, hhi, hnat⟩ := optimalLength_le_lam hn B
  set lam := GroupedOrder.lamN n with hlam
  have hl72 : 72 ≤ lam := lam_ge hn
  -- reals
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set Kr : ℝ := (K : ℝ) with hKr
  set lr : ℝ := (lam : ℝ) with hlr
  have hKpos : 0 < Kr := by rw [hKr]; exact_mod_cast (show 0 < K by omega)
  have hlr0 : 0 ≤ lr := Nat.cast_nonneg _
  have hl64 : (64 : ℝ) ≤ lr := by rw [hlr]; exact_mod_cast (show 64 ≤ lam by omega)
  have hloR : 16 * lr * Kr ^ 2 ≤ n := by rw [hlr, hKr]; exact_mod_cast hlo
  have hhiR : (n : ℝ) ≤ 25 * lr * Kr ^ 2 := by rw [hlr, hKr]; exact_mod_cast hhi.le
  have hcast : (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      2 * ((15 * (n : ℝ) ^ 2 + 3002 * n + 1) * Kr) +
      2 * ((48 * (h : ℝ) + 142) * (Kr ^ 2 * ((n / K : ℕ) : ℝ) ^ 3)) := by
    have := (Nat.cast_le (α := ℝ)).2 hnat
    push_cast at this
    rw [hKr]
    linarith [this]
  -- `n^(5/2) = n² √n`
  set P : ℝ := (n : ℝ) ^ ((5 : ℝ) / 2) with hP
  have hsn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hPe : P = (n : ℝ) ^ 2 * Real.sqrt n := by
    rw [hP, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hn0]; norm_num
  have hsq_n : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0.le
  -- `K² ⌊n/K⌋³ ≤ n³ / K`
  have hks : Kr * ((n / K : ℕ) : ℝ) ≤ n := by
    have : K * (n / K) ≤ n := Nat.mul_div_le n _
    rw [hKr]; exact_mod_cast this
  have hterm2 : Kr ^ 2 * ((n / K : ℕ) : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 / Kr := by
    rw [le_div_iff₀ hKpos]
    have := pow_le_pow_left₀ (by positivity) hks 3
    nlinarith [this]
  -- `√n ≤ 5 √λ K` and `32 K ≤ √n`
  have hsl : 0 ≤ Real.sqrt lr := Real.sqrt_nonneg _
  have hsl2 : Real.sqrt lr ^ 2 = lr := Real.sq_sqrt hlr0
  have hup : Real.sqrt n ≤ 5 * Real.sqrt lr * Kr := by
    rw [show 5 * Real.sqrt lr * Kr = Real.sqrt (25 * lr * Kr ^ 2) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_sq hKpos.le,
        show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hhiR
  have hdown : 32 * Kr ≤ Real.sqrt n := by
    rw [show 32 * Kr = Real.sqrt ((32 * Kr) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    have := mul_le_mul_of_nonneg_right hl64 (sq_nonneg Kr)
    linarith
  have hmain : (n : ℝ) ^ 3 / Kr ≤ 5 * Real.sqrt lr * P := by
    rw [div_le_iff₀ hKpos, hPe]
    have e3 : (n : ℝ) ^ 3 = (n : ℝ) ^ 2 * Real.sqrt n * Real.sqrt n := by
      rw [mul_assoc, ← sq, hsq_n]; ring
    rw [e3]
    have : (n : ℝ) ^ 2 * Real.sqrt n * Real.sqrt n ≤ (n : ℝ) ^ 2 * Real.sqrt n * (5 * Real.sqrt lr * Kr) :=
      mul_le_mul_of_nonneg_left hup (by positivity)
    linarith
  have hn3003 : (3003 : ℝ) ≤ n := by
    have : (2 : ℝ) ^ 23 ≤ n := by exact_mod_cast hn
    linarith
  have hpre : 2 * ((15 * (n : ℝ) ^ 2 + 3002 * n + 1) * Kr) ≤ P := by
    have ha : 15 * (n : ℝ) ^ 2 + 3002 * n + 1 ≤ 16 * (n : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hn3003 hn0.le
      nlinarith
    have h1 := mul_le_mul_of_nonneg_right ha hKpos.le
    have h2 := mul_le_mul_of_nonneg_left hdown (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)
    rw [hPe]
    linarith
  -- the coefficient
  set L := Real.log n with hL
  have hlog2 := Real.log_two_gt_d9
  have hL0 : 797 / 50 ≤ L := by
    have h1 : ((2 : ℝ) ^ 23) ≤ n := by exact_mod_cast hn
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  have hH : 214 / 25 * ((h : ℝ) - 1) ≤ L := by
    have h1 : ((73 : ℝ) ^ (2 * (h - 1))) ≤ n := by exact_mod_cast h73
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    have h3 := log_73_ge
    have e : ((2 * (h - 1) : ℕ) : ℝ) = 2 * ((h : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub hh]; push_cast; ring
    rw [e] at h2
    have h4 : (0 : ℝ) ≤ (h : ℝ) - 1 := by
      have : (1 : ℝ) ≤ h := by exact_mod_cast hh
      linarith
    have := mul_le_mul_of_nonneg_left h3 h4
    linarith
  have hlamL : lr ≤ 43281 / 10000 * L + 3 := by rw [hlr, hlam]; exact lam_le_log hn1
  have hcoef := coef_le hH (Nat.cast_nonneg _) hlamL hlr0 hL0
  have hP0 : 0 ≤ P := by positivity
  have hcoefP := mul_le_mul_of_nonneg_right hcoef hP0
  have hT : 2 * ((48 * (h : ℝ) + 142) * (Kr ^ 2 * ((n / K : ℕ) : ℝ) ^ 3)) ≤
      10 * (48 * (h : ℝ) + 142) * Real.sqrt lr * P := by
    have hA : 0 ≤ 48 * (h : ℝ) + 142 := by positivity
    have := mul_le_mul_of_nonneg_left (hterm2.trans hmain) hA
    linarith
  calc (optimalLength B : ℝ) ≤ _ := hcast
    _ ≤ (manhattan B.val : ℝ) + (1 + 10 * (48 * (h : ℝ) + 142) * Real.sqrt lr) * P := by
        linarith
    _ ≤ _ := by linarith

open SlidingPuzzle in
/-- **`OPT(B) ≤ M(B) + 375 n^(5/2) (ln n)^(3/2)`** for `n ≥ 2²³ ≈ 8.4·10⁶`. -/
theorem tree_lam_approximation_uniform {n : ℕ} [NeZero n] (hn : 2 ^ 23 ≤ n)
    (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      375 * (n : ℝ) ^ ((5 : ℝ) / 2) * Real.log n ^ ((3 : ℝ) / 2) := by
  have h := tree_lam_approximation hn B
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from lt_of_lt_of_le (by norm_num) hn)
  set L := Real.log n with hL
  have hlog2 := Real.log_two_gt_d9
  have hL0 : 797 / 50 ≤ L := by
    have h1 : ((2 : ℝ) ^ 23) ≤ n := by exact_mod_cast hn
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  have e : L ^ ((3 : ℝ) / 2) = L * Real.sqrt L := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' (by linarith) (by norm_num)]; norm_num
  have hs : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have hP : 0 ≤ (n : ℝ) ^ ((5 : ℝ) / 2) := by positivity
  have hc : (117 * L + 4100) * Real.sqrt L ≤ 375 * (L * Real.sqrt L) := by
    have := mul_nonneg (show (0 : ℝ) ≤ 258 * L - 4100 by linarith) hs
    linarith
  rw [e]
  have := mul_le_mul_of_nonneg_right hc hP
  linarith

end SlidingPuzzle.Tree
