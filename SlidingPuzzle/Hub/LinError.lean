import SlidingPuzzle.Hub.LinBound
import Mathlib

/-! # The error scale `n^(8/3)`

With `x = n^(1/3)`, the grid of `LinBound.lean` satisfies `4m ≤ x`, and either
`x < 4(m+1)` (cube scale) or the capacity condition fails at `m + 1`; there
`Λ(m+1) ≤ 0.266 x` (`lin_log_le`), so `5x² < 80.864 (m+1)² + 2.5`. Hence
`0.244 x ≤ m ≤ x/4` (`lin_range`), and on this range the cost
`KX x³/m + 8 KW m²` of the hub algorithm is at most `1083.6 x²`: it is a concave
function of `m` after multiplying by `m`, so its two endpoint values suffice
(`lin_core`). The cubic solver covers `4096 ≤ n ≤ linN`. -/

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

/-- The hub cost on the grid range `0.244 x ≤ m ≤ x/4`. -/
theorem lin_core {x m : ℝ} (hx4 : 4 * m ≤ x) (hxm : 244 / 1000 * x ≤ m) :
    (hubLinKX : ℝ) * x ^ 3 + 8 * hubLinKW * m ^ 3 ≤ 1000 * (10836 / 10) * m * x ^ 2 := by
  have hx : 0 ≤ x := by nlinarith
  have h1 : 0 ≤ m - 244 / 1000 * x := by linarith
  have h2 : 0 ≤ x - 4 * m := by linarith
  have h3 : 0 ≤ 4 * m + (4 * (244 / 1000) + 1) * x := by nlinarith
  have hP := mul_nonneg (mul_nonneg h1 h2) h3
  have hq1 := mul_nonneg h1 (sq_nonneg x)
  have hq2 := mul_nonneg h2 (sq_nonneg x)
  norm_num [hubLinKX, hubLinKW]
  nlinarith [hP, hq1, hq2]

/-- The capacity logarithm against the cube root: if `2^(L+1) ≤ x⁷` and
`x ≥ 215.44`, then `L + 4 ≤ 0.266 x`. -/
theorem lin_log_le {x : ℝ} (hx : 21544 / 100 ≤ x) {L : ℕ} (hL : (2 : ℝ) ^ (L + 1) ≤ x ^ 7) :
    (L : ℝ) + 4 ≤ 266 / 1000 * x := by
  rcases (show L ≤ 53 ∨ 54 ≤ L by omega) with h53 | h54
  · have : (L : ℝ) ≤ 53 := by exact_mod_cast h53
    linarith
  · have hnat : ∀ i, 54 ≤ i → 10 ^ 21 * (i + 4) ^ 7 ≤ 266 ^ 7 * 2 ^ (i + 1) := by
      intro i hi
      induction i, hi using Nat.le_induction with
      | base => norm_num
      | succ i hi ih =>
        have hstep : (i + 1 + 4) ^ 7 ≤ 2 * (i + 4) ^ 7 := by
          have h1 := Nat.pow_le_pow_left (show 58 * (i + 1 + 4) ≤ 59 * (i + 4) by omega) 7
          rw [mul_pow, mul_pow] at h1
          have h2 : 59 ^ 7 * (i + 4) ^ 7 ≤ 58 ^ 7 * (2 * (i + 4) ^ 7) := by
            have : (59 : ℕ) ^ 7 ≤ 58 ^ 7 * 2 := by norm_num
            calc 59 ^ 7 * (i + 4) ^ 7 ≤ 58 ^ 7 * 2 * (i + 4) ^ 7 := Nat.mul_le_mul_right _ this
              _ = 58 ^ 7 * (2 * (i + 4) ^ 7) := by ring
          exact Nat.le_of_mul_le_mul_left (h1.trans h2) (by norm_num)
        rw [pow_succ 2 (i + 1)]
        nlinarith
    have h := hnat L h54
    have hR : (10 : ℝ) ^ 21 * ((L : ℝ) + 4) ^ 7 ≤ 266 ^ 7 * 2 ^ (L + 1) := by exact_mod_cast h
    have hx0 : 0 ≤ x := by linarith
    have h7 : ((L : ℝ) + 4) ^ 7 ≤ (266 / 1000 * x) ^ 7 := by
      rw [mul_pow]
      have : (266 / 1000 : ℝ) ^ 7 = 266 ^ 7 / 10 ^ 21 := by norm_num
      rw [this]
      have h266 : (0 : ℝ) ≤ 266 ^ 7 / 10 ^ 21 := by positivity
      have := mul_le_mul_of_nonneg_left hL h266
      nlinarith
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h7

/-- The grid range in terms of `x = n^(1/3)`. -/
theorem lin_range {n m : ℕ} (hn : linN ≤ n) (hcube : 64 * m ^ 3 ≤ n)
    (hmax : 5 * n < gridCap n (m + 1) ∨ n < 64 * (m + 1) ^ 3) :
    215 ≤ cbrtN n ∧ 4 * (m : ℝ) ≤ cbrtN n ∧ 244 / 1000 * cbrtN n ≤ m := by
  set x := cbrtN n with hxdef
  have hx0 := cbrtN_nonneg n
  have hx3 := cbrtN_cube n
  rw [← hxdef] at hx0 hx3
  have hnR : (10 ^ 7 : ℝ) ≤ n := by exact_mod_cast (show 10 ^ 7 ≤ n by unfold linN at hn; omega)
  have hx215 : 21544 / 100 ≤ x := by
    apply le_of_cube_le hx0; rw [hx3]; norm_num; linarith
  have hx4 : 4 * (m : ℝ) ≤ x := by
    apply le_of_cube_le hx0; rw [hx3]
    have : ((64 * m ^ 3 : ℕ) : ℝ) ≤ n := by exact_mod_cast hcube
    push_cast at this; nlinarith
  refine ⟨by linarith, hx4, ?_⟩
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
      have : 0 < n := by unfold linN at hn; omega
      exact Nat.pow_log_le_self 2 (by positivity)
    have hpowR : (2 : ℝ) ^ L ≤ 2 * ((m : ℝ) + 1) * (x ^ 3) ^ 2 := by
      rw [hx3]; exact_mod_cast hpow
    have hL7 : (2 : ℝ) ^ (L + 1) ≤ x ^ 7 := by
      rw [pow_succ]
      have : 2 * ((m : ℝ) + 1) * (x ^ 3) ^ 2 * 2 ≤ x * x ^ 6 := by
        have := mul_le_mul_of_nonneg_right hx41 (show (0 : ℝ) ≤ x ^ 6 by positivity)
        nlinarith
      nlinarith
    have hLx := lin_log_le hx215 hL7
    have hcapR : 5 * (n : ℝ) < 304 * ((m : ℝ) + 1) ^ 2 * ((L : ℝ) + 4) + 10 * ((m : ℝ) + 1) := by
      have : ((5 * n : ℕ) : ℝ) < ((gridCap n (m + 1) : ℕ) : ℝ) := by exact_mod_cast hcap
      unfold gridCap at this
      push_cast at this
      linarith
    rw [← hx3] at hcapR
    have hxpos : 0 < x := by linarith
    have hm1 : 0 ≤ ((m : ℝ) + 1) ^ 2 := sq_nonneg _
    have h1 : x ^ 3 * 5 < x * (80864 / 1000 * ((m : ℝ) + 1) ^ 2 + 25 / 10) := by
      have := mul_le_mul_of_nonneg_left hLx (show 0 ≤ 304 * ((m : ℝ) + 1) ^ 2 by positivity)
      nlinarith
    have h2 : 5 * x ^ 2 < 80864 / 1000 * ((m : ℝ) + 1) ^ 2 + 25 / 10 := by
      by_contra hc
      push Not at hc
      nlinarith
    by_contra hc
    push Not at hc
    have h3 : ((m : ℝ) + 1) ^ 2 ≤ (244 / 1000 * x + 1) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity); linarith
    nlinarith
  · have hcub : (n : ℝ) < 64 * ((m : ℝ) + 1) ^ 3 := by
      have : n < 64 * (m + 1) ^ 3 := by omega
      exact_mod_cast this
    have : x < 4 * ((m : ℝ) + 1) := by
      apply lt_of_cube_lt (by positivity); rw [hx3]; nlinarith
    linarith

/-- The cubic solver on the initial range, against `n^(8/3)`. -/
theorem cubic_le_linError {n : ℕ} (hn : 4096 ≤ n) (hhi : n ≤ linN) :
    ((5 * n ^ 3 + 1509 * n ^ 2 + 1505 * n + 4796 : ℕ) : ℝ) ≤ 1084 * linError n := by
  rw [linError_eq]
  set x := cbrtN n with hxdef
  have hx0 := cbrtN_nonneg n
  have hx3 := cbrtN_cube n
  rw [← hxdef] at hx0 hx3
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hhiR : (n : ℝ) ≤ 10 ^ 7 := by exact_mod_cast (show n ≤ 10 ^ 7 by unfold linN at hhi; omega)
  have hx16 : 16 ≤ x := by
    apply le_of_cube_le hx0; rw [hx3]; linarith [show (16 : ℝ) ^ 3 = 4096 by norm_num]
  have hx226 : x ≤ 21545 / 100 := by
    apply le_of_cube_le (by norm_num); rw [hx3]; norm_num; linarith
  push_cast
  have hn3 : (n : ℝ) = x ^ 3 := hx3.symm
  rw [hn3]
  have h1 : 0 ≤ 21545 / 100 - x := by linarith
  have h2 : 0 ≤ x - 16 := by linarith
  have hx6 : 0 ≤ x ^ 6 := by positivity
  have hkey : 1509 * x ^ 6 + 1505 * x ^ 3 + 4796 ≤ x ^ 8 * (1084 - 5 * x) := by
    have hx2 : 256 ≤ x ^ 2 := by nlinarith
    have hx3' : 4096 ≤ x ^ 3 := by nlinarith
    have hbase : 7810 ≤ x ^ 2 * (1084 - 5 * x) := by nlinarith [mul_nonneg h1 h2]
    have hx8 : x ^ 8 * (1084 - 5 * x) = x ^ 6 * (x ^ 2 * (1084 - 5 * x)) := by ring
    rw [hx8]
    nlinarith [mul_le_mul_of_nonneg_left hbase hx6, pow_le_pow_left₀ (by norm_num) hx16 6]
  nlinarith

set_option maxHeartbeats 1600000 in
/-- **The hub algorithm without the logarithm**: for every `n ≥ linN`,
`OPT(B) ≤ M(B) + 1084 n^(8/3)`. -/
theorem optimalLength_le_linError {n : ℕ} [NeZero n] (hn : linN ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) + 1084 * linError n := by
  obtain ⟨m, hm50, hcube, hmax, hopt⟩ := optimalLength_le_lin_nat hn B
  obtain ⟨hx225, hx4, hxm⟩ := lin_range hn hcube hmax
  rw [linError_eq]
  set x := cbrtN n with hxdef
  have hx3 := cbrtN_cube n
  rw [← hxdef] at hx3
  set s := n / (2 * m) with hsdef
  have hmR : (50 : ℝ) ≤ m := by exact_mod_cast hm50
  -- natural-number facts about `s` and the prefix
  have hks : 2 * m * s ≤ n := Nat.mul_div_le n (2 * m)
  have hd : n - 2 * m * s ≤ 2 * m := by
    have h1 : n % (2 * m) + 2 * m * s = n := Nat.mod_add_div n (2 * m)
    have := Nat.mod_lt n (by omega : 0 < 2 * m)
    omega
  have hpoly : 15 * n ^ 2 + 3002 * n + 1 ≤ 16 * n ^ 2 := by
    unfold linN at hn; nlinarith
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
  -- the core inequality, multiplied out
  have hcore := lin_core hx4 hxm
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
      (m : ℝ) * (1000 * (10836 / 10) * x ^ 8) := by
    have e1 : (m : ℝ) * (2 * (hubLinKX : ℝ) * X) = hubLinKX * (2 * m * X) := by ring
    have e2 : (m : ℝ) * (2 * hubLinKW * ((2 * (m : ℝ)) ^ 2 * (x ^ 3) ^ 2)) =
        x ^ 6 * (8 * hubLinKW * m ^ 3) := by ring
    have e3 : (m : ℝ) * (1000 * (10836 / 10) * x ^ 8) = x ^ 6 * (1000 * (10836 / 10) * m * x ^ 2) := by
      ring
    have e4 : x ^ 6 * ((hubLinKX : ℝ) * x ^ 3) = hubLinKX * x ^ 9 := by ring
    have hk := mul_le_mul_of_nonneg_left hmX hKX
    rw [mul_add, e1, e2, e3]
    rw [mul_add, e4] at h2
    linarith
  have hmain' := le_of_mul_le_mul_left hmain hmpos
  have hZx : 2000 * (16 * (x ^ 3) ^ 2 * (2 * (m : ℝ))) ≤ 100 * x ^ 8 := by
    have hx7 : 0 ≤ x ^ 7 := by positivity
    have e : 2000 * (16 * (x ^ 3) ^ 2 * (2 * (m : ℝ))) = 16000 * x ^ 6 * (4 * m) := by ring
    have h4 := mul_le_mul_of_nonneg_left hx4 (show (0 : ℝ) ≤ 16000 * x ^ 6 by positivity)
    have e' : 16000 * x ^ 6 * x = 16000 * x ^ 7 := by ring
    have h5 : 16000 * x ^ 7 ≤ 100 * x ^ 8 := by
      have e'' : x ^ 8 = x ^ 7 * x := by ring
      rw [e'']; nlinarith
    linarith
  have hZ2 := mul_le_mul_of_nonneg_left hZR (show (0 : ℝ) ≤ 2000 by norm_num)
  linarith

end SlidingPuzzle.Hub
