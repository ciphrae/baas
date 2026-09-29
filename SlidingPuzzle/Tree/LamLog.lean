import SlidingPuzzle.Tree.LamGrid

/-! # Error `(97 ln n + 2670) √(ln n) n^(5/2)`, and `245 n^(5/2) (ln n)^(3/2)`

From `optimalLength_le_fine`: `64 n < 1089 λ K²` gives `n³/K ≤ (33/8)√λ n^(5/2)`, so the
cost is at most `(1 + (33/4)(48h + 142)√λ) n^(5/2)`. The depth has `16λ·73^(2(h-1)) ≤ n`,
so `48h + 142 ≤ 5.61 ln n + 150.6`, and `λ ≤ 4.3281 ln n + 3`. For the uniform constant
the depths `1` and `2` are bounded apart; depth `2` only occurs for
`n ≥ 16λ(2λ - 1)² ≥ 26641200`. -/
namespace SlidingPuzzle.Tree

/-- `p/q ≤ ln x` from `2.7182818286^p ≤ x^q`. -/
theorem le_log_of_e_pow {p q : ℕ} {x : ℝ} (hq : 0 < q) (hx : 0 < x)
    (h : (2.7182818286 : ℝ) ^ p ≤ x ^ q) : (p : ℝ) / q ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le hx]
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have h1 : Real.exp ((p : ℝ) / q) ^ q = Real.exp 1 ^ p := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; field_simp
  have h3 : Real.exp 1 ^ p ≤ (2.7182818286 : ℝ) ^ p :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le p
  have h4 : Real.exp ((p : ℝ) / q) ^ q ≤ x ^ q := by rw [h1]; exact h3.trans h
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le hx.le (by omega)).1 h4

theorem log_73_ge : (107 / 25 : ℝ) ≤ Real.log 73 := by
  have := le_log_of_e_pow (p := 107) (q := 25) (x := 73) (by norm_num) (by norm_num) (by norm_num)
  norm_num at this ⊢; linarith

theorem log_1152_ge : (176 / 25 : ℝ) ≤ Real.log 1152 := by
  have := le_log_of_e_pow (p := 176) (q := 25) (x := 1152) (by norm_num) (by norm_num)
    (by norm_num)
  norm_num at this ⊢; linarith

theorem log_26641200_ge : (427 / 25 : ℝ) ≤ Real.log 26641200 := by
  have h1 := le_log_of_e_pow (p := 23) (q := 50) (x := 26641200 / 2 ^ 24) (by norm_num)
    (by norm_num) (by norm_num)
  have e : (26641200 : ℝ) = 2 ^ 24 * (26641200 / 2 ^ 24) := by norm_num
  rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  have h2 := Real.log_two_gt_d9
  norm_num at h1 ⊢; linarith

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

/-- `A √λ ≤ c √L` from `A² λ ≤ c² L`. -/
theorem mul_sqrt_le {A lam c L : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c)
    (h : A ^ 2 * lam ≤ c ^ 2 * L) : A * Real.sqrt lam ≤ c * Real.sqrt L := by
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hA,
    Real.sqrt_sq hc] at this

/-- The cubic behind the coefficient `97`. -/
theorem coef_poly {L : ℝ} (hL : 797 / 50 ≤ L) :
    (4950 / 107 * L + 265749 / 214) ^ 2 * (43281 / 10000 * L + 3) ≤ (97 * L + 2669) ^ 2 * L := by
  have ht : 0 ≤ L - 797 / 50 := by linarith
  have ht2 := mul_nonneg ht ht
  have ht3 := mul_nonneg ht2 ht
  nlinarith

/-- Depth `1`: `(3135/2)² λ ≤ (245 L - 1)² L`. -/
theorem coef_poly_one {L : ℝ} (hL : 797 / 50 ≤ L) :
    (3135 / 2) ^ 2 * (43281 / 10000 * L + 3) ≤ (245 * L - 1) ^ 2 * L := by
  have ht : 0 ≤ L - 797 / 50 := by linarith
  have ht2 := mul_nonneg ht ht
  have ht3 := mul_nonneg ht2 ht
  nlinarith

/-- Depth `2`: `(3927/2)² λ ≤ (245 L - 1)² L` from `L ≥ 17.08`. -/
theorem coef_poly_two {L : ℝ} (hL : 427 / 25 ≤ L) :
    (3927 / 2) ^ 2 * (43281 / 10000 * L + 3) ≤ (245 * L - 1) ^ 2 * L := by
  have ht : 0 ≤ L - 427 / 25 := by linarith
  have ht2 := mul_nonneg ht ht
  have ht3 := mul_nonneg ht2 ht
  nlinarith

/-- `1 + (33/4)(48h + 142)√λ ≤ (97 L + 2670) √L`. -/
theorem coef_le {H lam L : ℝ} (hH : 214 / 25 * (H - 1) ≤ L - 176 / 25) (hH0 : 0 ≤ H)
    (hlam : lam ≤ 43281 / 10000 * L + 3) (hlam0 : 0 ≤ lam) (hL : 797 / 50 ≤ L) :
    1 + 33 / 4 * (48 * H + 142) * Real.sqrt lam ≤ (97 * L + 2670) * Real.sqrt L := by
  have hL0 : 0 ≤ L := by linarith
  set A := 33 / 4 * (48 * H + 142) with hA
  have hA0 : 0 ≤ A := by positivity
  have hAle : A ≤ 4950 / 107 * L + 265749 / 214 := by rw [hA]; linarith
  have hsq : A ^ 2 * lam ≤ (97 * L + 2669) ^ 2 * L := by
    have h1 : A ^ 2 ≤ (4950 / 107 * L + 265749 / 214) ^ 2 := pow_le_pow_left₀ hA0 hAle 2
    calc A ^ 2 * lam ≤ (4950 / 107 * L + 265749 / 214) ^ 2 * (43281 / 10000 * L + 3) :=
          mul_le_mul h1 hlam hlam0 (by positivity)
      _ ≤ _ := coef_poly hL
  have hroot := mul_sqrt_le hA0 (by positivity) hsq
  have h1 : 1 ≤ Real.sqrt L := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  linarith

/-- `1 + A √λ ≤ 245 L √L` from `A² λ ≤ (245 L - 1)² L`. -/
theorem coef_le_245 {A lam L : ℝ} (hA0 : 0 ≤ A) (hL : 1 ≤ L)
    (h : A ^ 2 * lam ≤ (245 * L - 1) ^ 2 * L) :
    1 + A * Real.sqrt lam ≤ 245 * (L * Real.sqrt L) := by
  have hroot := mul_sqrt_le hA0 (by linarith) h
  have h1 : 1 ≤ Real.sqrt L := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hL
  nlinarith

open SlidingPuzzle in
/-- The cost against `n^(5/2)`: at most `(1 + (33/4)(48h + 142)√λ) n^(5/2)`, for a depth `h`
with `16 λ 73^(2(h-1)) ≤ n`. -/
theorem err_fine {n : ℕ} [NeZero n] (hn : 2 ^ 23 ≤ n) (B : ReachableBoard n) :
    ∃ h : ℕ, 1 ≤ h ∧ 16 * GroupedOrder.lamN n * 73 ^ (2 * (h - 1)) ≤ n ∧
      (h = 2 → 16 * GroupedOrder.lamN n * (2 * GroupedOrder.lamN n - 1) ^ 2 ≤ n) ∧
      (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
        (1 + 33 / 4 * (48 * (h : ℝ) + 142) * Real.sqrt (GroupedOrder.lamN n)) *
          (n : ℝ) ^ ((5 : ℝ) / 2) := by
  obtain ⟨h, K, hh, h73, htwo, hK64, hlo, hhi, hnat⟩ := optimalLength_le_fine hn B
  refine ⟨h, hh, h73, htwo, ?_⟩
  set lam := GroupedOrder.lamN n with hlam
  have hl72 : 72 ≤ lam := lam_ge hn
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set Kr : ℝ := (K : ℝ) with hKr
  set lr : ℝ := (lam : ℝ) with hlr
  have hKpos : 0 < Kr := by rw [hKr]; exact_mod_cast (show 0 < K by omega)
  have hlr0 : 0 ≤ lr := Nat.cast_nonneg _
  have hl64 : (64 : ℝ) ≤ lr := by rw [hlr]; exact_mod_cast (show 64 ≤ lam by omega)
  have hloR : 16 * lr * Kr ^ 2 ≤ n := by rw [hlr, hKr]; exact_mod_cast hlo
  have hhiR : (n : ℝ) ≤ 1089 / 64 * lr * Kr ^ 2 := by
    have : (64 * n : ℝ) ≤ 1089 * lr * Kr ^ 2 := by rw [hlr, hKr]; exact_mod_cast hhi.le
    linarith
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
  -- `√n ≤ (33/8) √λ K` and `32 K ≤ √n`
  have hsl : 0 ≤ Real.sqrt lr := Real.sqrt_nonneg _
  have hup : Real.sqrt n ≤ 33 / 8 * Real.sqrt lr * Kr := by
    rw [show 33 / 8 * Real.sqrt lr * Kr = Real.sqrt (1089 / 64 * lr * Kr ^ 2) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_sq hKpos.le,
        show (1089 / 64 : ℝ) = (33 / 8) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hhiR
  have hdown : 32 * Kr ≤ Real.sqrt n := by
    rw [show 32 * Kr = Real.sqrt ((32 * Kr) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    have := mul_le_mul_of_nonneg_right hl64 (sq_nonneg Kr)
    linarith
  have hmain : (n : ℝ) ^ 3 / Kr ≤ 33 / 8 * Real.sqrt lr * P := by
    rw [div_le_iff₀ hKpos, hPe]
    have e3 : (n : ℝ) ^ 3 = (n : ℝ) ^ 2 * Real.sqrt n * Real.sqrt n := by
      rw [mul_assoc, ← sq, hsq_n]; ring
    rw [e3]
    have : (n : ℝ) ^ 2 * Real.sqrt n * Real.sqrt n ≤
        (n : ℝ) ^ 2 * Real.sqrt n * (33 / 8 * Real.sqrt lr * Kr) :=
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
  have hT : 2 * ((48 * (h : ℝ) + 142) * (Kr ^ 2 * ((n / K : ℕ) : ℝ) ^ 3)) ≤
      33 / 4 * (48 * (h : ℝ) + 142) * Real.sqrt lr * P := by
    have hA : 0 ≤ 48 * (h : ℝ) + 142 := by positivity
    have := mul_le_mul_of_nonneg_left (hterm2.trans hmain) hA
    linarith
  calc (optimalLength B : ℝ) ≤ _ := hcast
    _ ≤ _ := by linarith

/-- `ln n ≥ 15.94` for `n ≥ 2²³`. -/
theorem log_ge_of_pow23 {n : ℕ} (hn : 2 ^ 23 ≤ n) : (797 / 50 : ℝ) ≤ Real.log n := by
  have hlog2 := Real.log_two_gt_d9
  have h1 : ((2 : ℝ) ^ 23) ≤ n := by exact_mod_cast hn
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_pow] at h2
  push_cast at h2
  linarith

/-- The depth against `ln n`: `8.56 (h - 1) ≤ ln n - 7.04`. -/
theorem depth_le_log {n h : ℕ} (hh : 1 ≤ h) (hl : 72 ≤ GroupedOrder.lamN n)
    (h73 : 16 * GroupedOrder.lamN n * 73 ^ (2 * (h - 1)) ≤ n) :
    214 / 25 * ((h : ℝ) - 1) ≤ Real.log n - 176 / 25 := by
  have hpos : (0 : ℝ) < 16 * GroupedOrder.lamN n := by
    have : (0 : ℝ) < GroupedOrder.lamN n := by exact_mod_cast (show 0 < GroupedOrder.lamN n by omega)
    linarith
  have h1 : (16 * GroupedOrder.lamN n : ℝ) * (73 : ℝ) ^ (2 * (h - 1)) ≤ n := by
    exact_mod_cast h73
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_mul hpos.ne' (by positivity), Real.log_pow] at h2
  have h3 : Real.log 1152 ≤ Real.log (16 * GroupedOrder.lamN n : ℝ) := by
    apply Real.log_le_log (by norm_num)
    have : (72 : ℝ) ≤ GroupedOrder.lamN n := by exact_mod_cast hl
    linarith
  have e : ((2 * (h - 1) : ℕ) : ℝ) = 2 * ((h : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hh]; push_cast; ring
  rw [e] at h2
  have h4 : (0 : ℝ) ≤ (h : ℝ) - 1 := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  have := mul_le_mul_of_nonneg_left log_73_ge h4
  have := log_1152_ge
  nlinarith

open SlidingPuzzle in
/-- **Error `n^(5/2) (ln n)^(3/2)` with leading constant `97`**: for `n ≥ 2²³`,
`OPT(B) ≤ M(B) + (97 ln n + 2670) √(ln n) · n^(5/2)`. -/
theorem tree_lam_approximation {n : ℕ} [NeZero n] (hn : 2 ^ 23 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      (97 * Real.log n + 2670) * Real.sqrt (Real.log n) * (n : ℝ) ^ ((5 : ℝ) / 2) := by
  obtain ⟨h, hh, h73, -, herr⟩ := err_fine hn B
  have hl72 : 72 ≤ GroupedOrder.lamN n := lam_ge hn
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hcoef := coef_le (depth_le_log hh hl72 h73) (Nat.cast_nonneg _) (lam_le_log hn1)
    (Nat.cast_nonneg _) (log_ge_of_pow23 hn)
  have hP : 0 ≤ (n : ℝ) ^ ((5 : ℝ) / 2) := by positivity
  have := mul_le_mul_of_nonneg_right hcoef hP
  linarith

open SlidingPuzzle in
/-- **`OPT(B) ≤ M(B) + 245 n^(5/2) (ln n)^(3/2)`** for `n ≥ 2²³ ≈ 8.4·10⁶`. -/
theorem tree_lam_approximation_uniform {n : ℕ} [NeZero n] (hn : 2 ^ 23 ≤ n)
    (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      245 * (n : ℝ) ^ ((5 : ℝ) / 2) * Real.log n ^ ((3 : ℝ) / 2) := by
  obtain ⟨h, hh, h73, htwo, herr⟩ := err_fine hn B
  set lam := GroupedOrder.lamN n with hlam
  have hl72 : 72 ≤ lam := lam_ge hn
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set L := Real.log n with hL
  have hL0 := log_ge_of_pow23 hn
  have hlamL : (lam : ℝ) ≤ 43281 / 10000 * L + 3 := lam_le_log hn1
  have hlam0 : (0 : ℝ) ≤ lam := Nat.cast_nonneg _
  have e : L ^ ((3 : ℝ) / 2) = L * Real.sqrt L := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' (by linarith) (by norm_num)]; norm_num
  have hP : 0 ≤ (n : ℝ) ^ ((5 : ℝ) / 2) := by positivity
  have hs : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have hc : 1 + 33 / 4 * (48 * (h : ℝ) + 142) * Real.sqrt lam ≤ 245 * (L * Real.sqrt L) := by
    rcases (show h = 1 ∨ h = 2 ∨ 3 ≤ h by omega) with h1 | h2 | h3
    · -- depth `1`
      subst h1
      apply coef_le_245 (by norm_num) (by linarith)
      calc (33 / 4 * (48 * ((1 : ℕ) : ℝ) + 142)) ^ 2 * lam
          = (3135 / 2) ^ 2 * lam := by norm_num
        _ ≤ (3135 / 2) ^ 2 * (43281 / 10000 * L + 3) :=
          mul_le_mul_of_nonneg_left hlamL (by norm_num)
        _ ≤ _ := coef_poly_one hL0
    · -- depth `2`: `n ≥ 16 λ (2λ - 1)² ≥ 26641200`
      subst h2
      have hn2 := htwo rfl
      have h24 : 2 ^ 24 ≤ n := by
        have : 16 * 72 * 143 ^ 2 ≤ 16 * lam * (2 * lam - 1) ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 16 hl72) (Nat.pow_le_pow_left (by omega) 2)
        omega
      have hl75 : 75 ≤ lam := by have := lamN_ge_of_pow h24; omega
      have hbig : 26641200 ≤ n := by
        have : 16 * 75 * 149 ^ 2 ≤ 16 * lam * (2 * lam - 1) ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 16 hl75) (Nat.pow_le_pow_left (by omega) 2)
        omega
      have hL2 : (427 / 25 : ℝ) ≤ L := by
        have h1 : (26641200 : ℝ) ≤ n := by exact_mod_cast hbig
        exact log_26641200_ge.trans (Real.log_le_log (by norm_num) h1)
      apply coef_le_245 (by norm_num) (by linarith)
      calc (33 / 4 * (48 * ((2 : ℕ) : ℝ) + 142)) ^ 2 * lam
          = (3927 / 2) ^ 2 * lam := by norm_num
        _ ≤ (3927 / 2) ^ 2 * (43281 / 10000 * L + 3) :=
          mul_le_mul_of_nonneg_left hlamL (by norm_num)
        _ ≤ _ := coef_poly_two hL2
    · -- depth `3` or more: `ln n ≥ 24.16`
      have hD := depth_le_log hh hl72 h73
      have hcoef := coef_le hD (Nat.cast_nonneg _) hlamL hlam0 hL0
      have h3' : (3 : ℝ) ≤ h := by exact_mod_cast h3
      have hL24 : 18 ≤ L := by linarith
      have := mul_nonneg (show (0 : ℝ) ≤ 148 * L - 2670 by linarith) hs
      nlinarith
  rw [e]
  have := mul_le_mul_of_nonneg_right hc hP
  linarith

end SlidingPuzzle.Tree
