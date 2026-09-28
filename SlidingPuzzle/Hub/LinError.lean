import SlidingPuzzle.Hub.LinBound
import Mathlib

/-! # The error scale `n^(8/3)`

With `x = n^(1/3)`, the grid of `LinBound.lean` satisfies `4m ≤ x`. The cost
`KX x³/m + 8 KW m²` of the hub algorithm, multiplied by `m`, is a concave function
of `m`, so on a range `a ≤ m ≤ x/4` its two endpoint values suffice
(`lin_core_of`). The lower end `a` is

* `m ≥ 25` for `2·10⁶ ≤ n < 2.1·10⁶` and `m ≥ 26` for `2.1·10⁶ ≤ n < 2.3·10⁶`
  (`lin_core_25`, `lin_core_26`);
* `0.1964 x` for `n ≥ 2.3·10⁶`: either `x < 4(m+1)` (cube scale) or the capacity
  condition fails at `m + 1`; there `Λ(m+1) ≤ 0.395 x` (`lin_log_le`), so
  `5x² < 120.08 (m+1)² + 2.5` (`lin_range`).

In each case the cost is at most `634.8 x²`, and the prefix adds at most `0.128 x²`.
The cubic solver covers `4096 ≤ n ≤ linN = 2·10⁶`. -/

open Filter Asymptotics

namespace SlidingPuzzle.Hub

/-- The error scale `n^(8/3)`. -/
noncomputable def linError (n : ℕ) : ℝ := Real.rpow (n : ℝ) (8 / 3 : ℝ)

theorem linError_nonneg (n : ℕ) : 0 ≤ linError n :=
  Real.rpow_nonneg (Nat.cast_nonneg n) _

/-- The cube root of `n`. -/
noncomputable def cbrtN (n : ℕ) : ℝ := Real.rpow (n : ℝ) (1 / 3 : ℝ)

theorem cbrtN_nonneg (n : ℕ) : 0 ≤ cbrtN n := Real.rpow_nonneg (Nat.cast_nonneg n) _

theorem cbrtN_cube (n : ℕ) : cbrtN n ^ 3 = n := by
  unfold cbrtN
  rw [Real.rpow_eq_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
  norm_num

theorem linError_eq (n : ℕ) : linError n = cbrtN n ^ 8 := by
  unfold linError cbrtN
  rw [Real.rpow_eq_pow, Real.rpow_eq_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
  norm_num

/-- Cube roots are monotone. -/
theorem le_of_cube_le {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 3 ≤ b ^ 3) : a ≤ b := by
  by_contra hc
  push Not at hc
  have := pow_lt_pow_left₀ hc hb (by norm_num : (3 : ℕ) ≠ 0)
  linarith

theorem lt_of_cube_lt {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 3 < b ^ 3) : a < b := by
  by_contra hc
  push Not at hc
  have := pow_le_pow_left₀ hb hc 3
  linarith

/-- On a range `a ≤ m ≤ x/4`, the hub cost `KX x³ + 8 KW m³ ≤ D m x²` follows from
its two endpoint values: `D m x² - 8 KW m³` is concave in `m`. -/
theorem lin_core_of {x m a D : ℝ} (hx4 : 4 * m ≤ x) (ham : a ≤ m) (ha0 : 0 ≤ a)
    (hA : (hubLinKX : ℝ) * x ^ 3 + 8 * hubLinKW * a ^ 3 ≤ D * a * x ^ 2)
    (hB : 64 * (hubLinKX : ℝ) + 8 * hubLinKW ≤ 16 * D) :
    (hubLinKX : ℝ) * x ^ 3 + 8 * hubLinKW * m ^ 3 ≤ D * m * x ^ 2 := by
  have hx : 0 ≤ x := by linarith
  set b := x / 4 with hb
  have hmb : m ≤ b := by rw [hb]; linarith
  set g : ℝ → ℝ := fun t => D * t * x ^ 2 - 8 * hubLinKW * t ^ 3 - hubLinKX * x ^ 3 with hg
  have hga : 0 ≤ g a := by simp only [hg]; linarith
  have hgb : 0 ≤ g b := by
    have hx3 : 0 ≤ x ^ 3 := by positivity
    have : g b = x ^ 3 * (16 * D - 64 * hubLinKX - 8 * hubLinKW) / 64 := by
      simp only [hg, hb]; ring
    rw [this]
    apply div_nonneg _ (by norm_num)
    exact mul_nonneg hx3 (by linarith)
  have key : (b - a) * g m = (b - m) * g a + (m - a) * g b +
      8 * hubLinKW * (b - a) * ((m - a) * (b - m) * (m + a + b)) := by
    simp only [hg]; ring
  have hKW : (0 : ℝ) ≤ hubLinKW := by norm_num [hubLinKW]
  have hrhs : 0 ≤ (b - m) * g a + (m - a) * g b +
      8 * hubLinKW * (b - a) * ((m - a) * (b - m) * (m + a + b)) := by
    have h1 := mul_nonneg (sub_nonneg.mpr hmb) hga
    have h2 := mul_nonneg (sub_nonneg.mpr ham) hgb
    have h3 : 0 ≤ (m - a) * (b - m) * (m + a + b) :=
      mul_nonneg (mul_nonneg (sub_nonneg.mpr ham) (sub_nonneg.mpr hmb)) (by linarith)
    have h4 : 0 ≤ 8 * (hubLinKW : ℝ) * (b - a) := mul_nonneg (by positivity) (by linarith)
    have := mul_nonneg h4 h3
    linarith
  have hgm : 0 ≤ g m := by
    rcases eq_or_lt_of_le (show a ≤ b by linarith) with hab | hab
    · have : m = a := le_antisymm (hab ▸ hmb) ham
      rw [this]; exact hga
    · by_contra hc
      push Not at hc
      have := mul_neg_of_pos_of_neg (sub_pos.mpr hab) hc
      linarith
  simp only [hg] at hgm
  linarith

/-- The upper endpoint `m = x/4`: `64 KX + 8 KW ≤ 16 · 634.8`. -/
theorem lin_top : 64 * (hubLinKX : ℝ) + 8 * hubLinKW ≤ 16 * (1000 * (6348 / 10)) := by
  norm_num [hubLinKX, hubLinKW]

/-- The hub cost for `m ≥ 25` and `125.99 ≤ x ≤ 128.07`. -/
theorem lin_core_25 {x m : ℝ} (hx4 : 4 * m ≤ x) (hm : 25 ≤ m) (hlo : 12599 / 100 ≤ x)
    (hhi : x ≤ 12807 / 100) :
    (hubLinKX : ℝ) * x ^ 3 + 8 * hubLinKW * m ^ 3 ≤ 1000 * (6348 / 10) * m * x ^ 2 := by
  refine lin_core_of hx4 hm (by norm_num) ?_ lin_top
  norm_num [hubLinKX, hubLinKW]
  have h1 : 0 ≤ x - 12599 / 100 := by linarith
  have h2 : 0 ≤ 12807 / 100 - x := by linarith
  nlinarith [mul_nonneg h1 h2, mul_nonneg (mul_nonneg h1 h2) (show (0 : ℝ) ≤ x by linarith)]

/-- The hub cost for `m ≥ 26` and `128.05 ≤ x ≤ 132.01`. -/
theorem lin_core_26 {x m : ℝ} (hx4 : 4 * m ≤ x) (hm : 26 ≤ m) (hlo : 12805 / 100 ≤ x)
    (hhi : x ≤ 13201 / 100) :
    (hubLinKX : ℝ) * x ^ 3 + 8 * hubLinKW * m ^ 3 ≤ 1000 * (6348 / 10) * m * x ^ 2 := by
  refine lin_core_of hx4 hm (by norm_num) ?_ lin_top
  norm_num [hubLinKX, hubLinKW]
  have h1 : 0 ≤ x - 12805 / 100 := by linarith
  have h2 : 0 ≤ 13201 / 100 - x := by linarith
  nlinarith [mul_nonneg h1 h2, mul_nonneg (mul_nonneg h1 h2) (show (0 : ℝ) ≤ x by linarith)]

/-- The hub cost on the grid range `0.1964 x ≤ m ≤ x/4`. -/
theorem lin_core {x m : ℝ} (hx4 : 4 * m ≤ x) (hxm : 1964 / 10000 * x ≤ m) :
    (hubLinKX : ℝ) * x ^ 3 + 8 * hubLinKW * m ^ 3 ≤ 1000 * (6348 / 10) * m * x ^ 2 := by
  have hx : 0 ≤ x := by nlinarith
  refine lin_core_of hx4 hxm (by positivity) ?_ lin_top
  have hx3 : 0 ≤ x ^ 3 := by positivity
  norm_num [hubLinKX, hubLinKW]
  nlinarith [hx3]

/-- The capacity logarithm against the cube root: if `2^(L+1) ≤ x⁷` and
`x ≥ 131.99`, then `L + 4 ≤ 0.395 x`. -/
theorem lin_log_le {x : ℝ} (hx : 13199 / 100 ≤ x) {L : ℕ} (hL : (2 : ℝ) ^ (L + 1) ≤ x ^ 7) :
    (L : ℝ) + 4 ≤ 395 / 1000 * x := by
  rcases (show L ≤ 48 ∨ 49 ≤ L by omega) with h48 | h49
  · have : (L : ℝ) ≤ 48 := by exact_mod_cast h48
    linarith
  · have hnat : ∀ i, 49 ≤ i → 1000 ^ 7 * (i + 4) ^ 7 ≤ 395 ^ 7 * 2 ^ (i + 1) := by
      intro i hi
      induction i, hi using Nat.le_induction with
      | base => norm_num
      | succ i hi ih =>
        have hstep : (i + 1 + 4) ^ 7 ≤ 2 * (i + 4) ^ 7 := by
          have h1 := Nat.pow_le_pow_left (show 53 * (i + 1 + 4) ≤ 54 * (i + 4) by omega) 7
          rw [mul_pow, mul_pow] at h1
          have h2 : 54 ^ 7 * (i + 4) ^ 7 ≤ 53 ^ 7 * (2 * (i + 4) ^ 7) := by
            have : (54 : ℕ) ^ 7 ≤ 53 ^ 7 * 2 := by norm_num
            calc 54 ^ 7 * (i + 4) ^ 7 ≤ 53 ^ 7 * 2 * (i + 4) ^ 7 := Nat.mul_le_mul_right _ this
              _ = 53 ^ 7 * (2 * (i + 4) ^ 7) := by ring
          exact Nat.le_of_mul_le_mul_left (h1.trans h2) (by norm_num)
        rw [pow_succ 2 (i + 1)]
        nlinarith
    have h := hnat L h49
    have hR : (1000 : ℝ) ^ 7 * ((L : ℝ) + 4) ^ 7 ≤ 395 ^ 7 * 2 ^ (L + 1) := by exact_mod_cast h
    have hx0 : 0 ≤ x := by linarith
    have h7 : ((L : ℝ) + 4) ^ 7 ≤ (395 / 1000 * x) ^ 7 := by
      rw [mul_pow]
      have : (395 / 1000 : ℝ) ^ 7 = 395 ^ 7 / 1000 ^ 7 := by norm_num
      rw [this]
      have h395 : (0 : ℝ) ≤ 395 ^ 7 / 1000 ^ 7 := by positivity
      have := mul_le_mul_of_nonneg_left hL h395
      nlinarith
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h7

/-- The grid range in terms of `x = n^(1/3)`, for `n ≥ 2.3·10⁶`. -/
theorem lin_range {n m : ℕ} (hn : 23 * 10 ^ 5 ≤ n) (hcube : 64 * m ^ 3 ≤ n)
    (hmax : 5 * n < gridCap n (m + 1) ∨ n < 64 * (m + 1) ^ 3) :
    1964 / 10000 * cbrtN n ≤ m := by
  set x := cbrtN n with hxdef
  have hx0 := cbrtN_nonneg n
  have hx3 := cbrtN_cube n
  rw [← hxdef] at hx0 hx3
  have hnR : (23 * 10 ^ 5 : ℝ) ≤ n := by exact_mod_cast hn
  have hx132 : 13199 / 100 ≤ x := by
    apply le_of_cube_le hx0; rw [hx3]; norm_num; linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  by_cases hc1 : 64 * (m + 1) ^ 3 ≤ n
  · have hcap : 5 * n < gridCap n (m + 1) := by
      rcases hmax with h | h
      · exact h
      · omega
    set L := Nat.log 2 (2 * (m + 1) * n ^ 2) with hLdef
    -- `2^(L+1) ≤ x⁷`
    have hx41 : 4 * ((m : ℝ) + 1) ≤ x := by
      apply le_of_cube_le hx0; rw [hx3]
      have : ((64 * (m + 1) ^ 3 : ℕ) : ℝ) ≤ n := by exact_mod_cast hc1
      push_cast at this; nlinarith
    have hpow : 2 ^ L ≤ 2 * (m + 1) * n ^ 2 := by
      have : 0 < n := by omega
      exact Nat.pow_log_le_self 2 (by positivity)
    have hpowR : (2 : ℝ) ^ L ≤ 2 * ((m : ℝ) + 1) * (x ^ 3) ^ 2 := by
      rw [hx3]; exact_mod_cast hpow
    have hL7 : (2 : ℝ) ^ (L + 1) ≤ x ^ 7 := by
      rw [pow_succ]
      have : 2 * ((m : ℝ) + 1) * (x ^ 3) ^ 2 * 2 ≤ x * x ^ 6 := by
        have := mul_le_mul_of_nonneg_right hx41 (show (0 : ℝ) ≤ x ^ 6 by positivity)
        nlinarith
      nlinarith
    have hLx := lin_log_le hx132 hL7
    have hcapR : 5 * (n : ℝ) < 304 * ((m : ℝ) + 1) ^ 2 * ((L : ℝ) + 4) + 10 * ((m : ℝ) + 1) := by
      have : ((5 * n : ℕ) : ℝ) < ((gridCap n (m + 1) : ℕ) : ℝ) := by exact_mod_cast hcap
      unfold gridCap at this
      push_cast at this
      linarith
    rw [← hx3] at hcapR
    have hxpos : 0 < x := by linarith
    have hm1 : 0 ≤ ((m : ℝ) + 1) ^ 2 := sq_nonneg _
    have h1 : x ^ 3 * 5 < x * (12008 / 100 * ((m : ℝ) + 1) ^ 2 + 25 / 10) := by
      have := mul_le_mul_of_nonneg_left hLx (show 0 ≤ 304 * ((m : ℝ) + 1) ^ 2 by positivity)
      nlinarith
    have h2 : 5 * x ^ 2 < 12008 / 100 * ((m : ℝ) + 1) ^ 2 + 25 / 10 := by
      by_contra hc
      push Not at hc
      nlinarith
    by_contra hc
    push Not at hc
    have h3 : ((m : ℝ) + 1) ^ 2 ≤ (1964 / 10000 * x + 1) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity); linarith
    nlinarith
  · have hcub : (n : ℝ) < 64 * ((m : ℝ) + 1) ^ 3 := by
      have : n < 64 * (m + 1) ^ 3 := by omega
      exact_mod_cast this
    have : x < 4 * ((m : ℝ) + 1) := by
      apply lt_of_cube_lt (by positivity); rw [hx3]; nlinarith
    nlinarith

/-- The cubic solver on the initial range, against `n^(8/3)`. -/
theorem cubic_le_linError {n : ℕ} (hn : 4096 ≤ n) (hhi : n ≤ linN) :
    ((5 * n ^ 3 + 1509 * n ^ 2 + 1505 * n + 4796 : ℕ) : ℝ) ≤ 635 * linError n := by
  rw [linError_eq]
  set x := cbrtN n with hxdef
  have hx0 := cbrtN_nonneg n
  have hx3 := cbrtN_cube n
  rw [← hxdef] at hx0 hx3
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hhiR : (n : ℝ) ≤ 2 * 10 ^ 6 := by exact_mod_cast (show n ≤ 2 * 10 ^ 6 by unfold linN at hhi; omega)
  have hx16 : 16 ≤ x := by
    apply le_of_cube_le hx0; rw [hx3]; linarith [show (16 : ℝ) ^ 3 = 4096 by norm_num]
  have hx126 : x ≤ 126 := by
    apply le_of_cube_le (by norm_num); rw [hx3]; linarith [show (126 : ℝ) ^ 3 = 2000376 by norm_num]
  push_cast
  have hn3 : (n : ℝ) = x ^ 3 := hx3.symm
  rw [hn3]
  have h1 : 0 ≤ 126 - x := by linarith
  have h2 : 0 ≤ x - 16 := by linarith
  have hx6 : 0 ≤ x ^ 6 := by positivity
  have hkey : 1509 * x ^ 6 + 1505 * x ^ 3 + 4796 ≤ x ^ 8 * (635 - 5 * x) := by
    have hx2 : 256 ≤ x ^ 2 := by nlinarith
    have hx3' : 4096 ≤ x ^ 3 := by nlinarith
    have hbase : 1600 ≤ x ^ 2 * (635 - 5 * x) := by nlinarith [mul_nonneg h1 h2]
    have hx8 : x ^ 8 * (635 - 5 * x) = x ^ 6 * (x ^ 2 * (635 - 5 * x)) := by ring
    rw [hx8]
    nlinarith [mul_le_mul_of_nonneg_left hbase hx6, pow_le_pow_left₀ (by norm_num) hx16 6]
  nlinarith

set_option maxHeartbeats 1600000 in
/-- The hub algorithm, given the core estimate `KX x³ + 8 KW m³ ≤ 634.8 m x²` for
its grid: `OPT(B) ≤ M(B) + 635 n^(8/3)`. -/
theorem optimalLength_le_of_core {n m : ℕ} [NeZero n] (B : ReachableBoard n)
    (hm25 : 25 ≤ m) (hx125 : 125 ≤ cbrtN n) (hx4 : 4 * (m : ℝ) ≤ cbrtN n)
    (hopt : 1000 * optimalLength B ≤ 1000 * manhattan B.val +
        2 * hubLinKX * (n ^ 2 * (n / (2 * m))) + 2 * hubLinKW * ((2 * m) ^ 2 * n ^ 2) +
        2000 * ((15 * n ^ 2 + 3002 * n + 1) * (n - 2 * m * (n / (2 * m)))))
    (hcore : (hubLinKX : ℝ) * cbrtN n ^ 3 + 8 * hubLinKW * (m : ℝ) ^ 3 ≤
      1000 * (6348 / 10) * m * cbrtN n ^ 2) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) + 635 * linError n := by
  rw [linError_eq]
  set x := cbrtN n with hxdef
  have hx3 := cbrtN_cube n
  rw [← hxdef] at hx3
  set s := n / (2 * m) with hsdef
  have hmR : (25 : ℝ) ≤ m := by exact_mod_cast hm25
  -- natural-number facts about `s` and the prefix
  have hks : 2 * m * s ≤ n := Nat.mul_div_le n (2 * m)
  have hd : n - 2 * m * s ≤ 2 * m := by
    have h1 : n % (2 * m) + 2 * m * s = n := Nat.mod_add_div n (2 * m)
    have := Nat.mod_lt n (by omega : 0 < 2 * m)
    omega
  have hn3003 : 3003 ≤ n := by
    have : (3003 : ℝ) ≤ n := by rw [← hx3]; nlinarith
    exact_mod_cast this
  have hpoly : 15 * n ^ 2 + 3002 * n + 1 ≤ 16 * n ^ 2 := by nlinarith
  have hZ : (15 * n ^ 2 + 3002 * n + 1) * (n - 2 * m * s) ≤ 16 * n ^ 2 * (2 * m) :=
    Nat.mul_le_mul hpoly hd
  have hoptR : 1000 * (optimalLength B : ℝ) ≤ 1000 * (manhattan B.val : ℝ) +
      2 * (hubLinKX : ℝ) * ((n : ℝ) ^ 2 * s) + 2 * (hubLinKW : ℝ) * ((2 * (m : ℝ)) ^ 2 * (n : ℝ) ^ 2) +
      2000 * (((15 * n ^ 2 + 3002 * n + 1) * (n - 2 * m * s) : ℕ) : ℝ) := by
    exact_mod_cast hopt
  have hZR : (((15 * n ^ 2 + 3002 * n + 1) * (n - 2 * m * s) : ℕ) : ℝ) ≤
      16 * (n : ℝ) ^ 2 * (2 * m) := by exact_mod_cast hZ
  have hksR : 2 * (m : ℝ) * s ≤ n := by exact_mod_cast hks
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hn3 : (n : ℝ) = x ^ 3 := hx3.symm
  rw [hn3] at hoptR hZR hksR
  have hx0 : 0 < x := by linarith
  have hmpos : (0 : ℝ) < m := by linarith
  have hX : 2 * (m : ℝ) * ((x ^ 3) ^ 2 * s) ≤ x ^ 9 := by
    have := mul_le_mul_of_nonneg_left hksR (show 0 ≤ (x ^ 3) ^ 2 by positivity)
    nlinarith
  have hKX : (0 : ℝ) ≤ hubLinKX := by norm_num [hubLinKX]
  have hKW : (0 : ℝ) ≤ hubLinKW := by norm_num [hubLinKW]
  -- multiply the core by `x⁶ / m`
  set X := (x ^ 3) ^ 2 * (s : ℝ) with hXdef
  have hmX : 2 * (m : ℝ) * X ≤ x ^ 9 := hX
  have h2 := mul_le_mul_of_nonneg_left hcore (show (0 : ℝ) ≤ x ^ 6 by positivity)
  have hmain : (m : ℝ) * (2 * (hubLinKX : ℝ) * X + 2 * hubLinKW * ((2 * (m : ℝ)) ^ 2 * (x ^ 3) ^ 2)) ≤
      (m : ℝ) * (1000 * (6348 / 10) * x ^ 8) := by
    have e1 : (m : ℝ) * (2 * (hubLinKX : ℝ) * X) = hubLinKX * (2 * m * X) := by ring
    have e2 : (m : ℝ) * (2 * hubLinKW * ((2 * (m : ℝ)) ^ 2 * (x ^ 3) ^ 2)) =
        x ^ 6 * (8 * hubLinKW * m ^ 3) := by ring
    have e3 : (m : ℝ) * (1000 * (6348 / 10) * x ^ 8) = x ^ 6 * (1000 * (6348 / 10) * m * x ^ 2) := by
      ring
    have e4 : x ^ 6 * ((hubLinKX : ℝ) * x ^ 3) = hubLinKX * x ^ 9 := by ring
    have hk := mul_le_mul_of_nonneg_left hmX hKX
    rw [mul_add, e1, e2, e3]
    rw [mul_add, e4] at h2
    linarith
  have hmain' := le_of_mul_le_mul_left hmain hmpos
  -- the prefix: `2000 · 16 n² · 2m ≤ 16000 x⁷ ≤ 128 x⁸`
  have hZx : 2000 * (16 * (x ^ 3) ^ 2 * (2 * (m : ℝ))) ≤ 128 * x ^ 8 := by
    have hx7 : 0 ≤ x ^ 7 := by positivity
    have e : 2000 * (16 * (x ^ 3) ^ 2 * (2 * (m : ℝ))) = 16000 * x ^ 6 * (4 * m) := by ring
    have h4 := mul_le_mul_of_nonneg_left hx4 (show (0 : ℝ) ≤ 16000 * x ^ 6 by positivity)
    have e' : 16000 * x ^ 6 * x = 16000 * x ^ 7 := by ring
    have h5 : 16000 * x ^ 7 ≤ 128 * x ^ 8 := by
      have e'' : x ^ 8 = x ^ 7 * x := by ring
      rw [e'']; nlinarith
    linarith
  have hZ2 := mul_le_mul_of_nonneg_left hZR (show (0 : ℝ) ≤ 2000 by norm_num)
  linarith

/-- **The hub algorithm without the logarithm**: for every `n ≥ linN`,
`OPT(B) ≤ M(B) + 635 n^(8/3)`. -/
theorem optimalLength_le_linError {n : ℕ} [NeZero n] (hn : linN ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) + 635 * linError n := by
  obtain ⟨m, hm25, hcube, hmax, h26, hopt⟩ := optimalLength_le_lin_nat hn B
  set x := cbrtN n with hxdef
  have hx0 := cbrtN_nonneg n
  have hx3 := cbrtN_cube n
  rw [← hxdef] at hx0 hx3
  have hnR : (2 * 10 ^ 6 : ℝ) ≤ n := by exact_mod_cast (show 2 * 10 ^ 6 ≤ n by unfold linN at hn; omega)
  have hx4 : 4 * (m : ℝ) ≤ x := by
    apply le_of_cube_le hx0; rw [hx3]
    have : ((64 * m ^ 3 : ℕ) : ℝ) ≤ n := by exact_mod_cast hcube
    push_cast at this; nlinarith
  have hlo : 12599 / 100 ≤ x := by
    apply le_of_cube_le hx0; rw [hx3]; norm_num; linarith
  have hm25R : (25 : ℝ) ≤ m := by exact_mod_cast hm25
  refine optimalLength_le_of_core B hm25 (by linarith) hx4 hopt ?_
  rw [← hxdef]
  by_cases h21 : 21 * 10 ^ 5 ≤ n
  · by_cases h23 : 23 * 10 ^ 5 ≤ n
    · exact lin_core hx4 (lin_range h23 hcube hmax)
    · have hm26 : (26 : ℝ) ≤ m := by exact_mod_cast h26 h21
      have hn21 : (21 * 10 ^ 5 : ℝ) ≤ n := by exact_mod_cast h21
      have hn23 : (n : ℝ) ≤ 23 * 10 ^ 5 := by exact_mod_cast (show n ≤ 23 * 10 ^ 5 by omega)
      refine lin_core_26 hx4 hm26 ?_ ?_
      · apply le_of_cube_le hx0; rw [hx3]; norm_num; linarith
      · apply le_of_cube_le (by norm_num); rw [hx3]; norm_num; linarith
  · have hn21 : (n : ℝ) ≤ 21 * 10 ^ 5 := by exact_mod_cast (show n ≤ 21 * 10 ^ 5 by omega)
    refine lin_core_25 hx4 hm25R hlo ?_
    apply le_of_cube_le (by norm_num); rw [hx3]; norm_num; linarith

end SlidingPuzzle.Hub
