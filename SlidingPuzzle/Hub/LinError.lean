import SlidingPuzzle.Hub.LinBound
import SlidingPuzzle.Hub.AsympError

/-! # The error scale `n^(8/3)`

With `x = n^(1/3)`, the grid of `LinBound.lean` satisfies `4m ≤ x` and
`x < 4.517 (m+1)` (from the cube scale, or from the capacity condition and
`192 L ≤ 20.4 x`). Hence `0.2169 x ≤ m ≤ x/4`, and on this range the cost
`KX x³/m + 8 KW m²` of the hub algorithm is at most `1132.9 x²`: it is a concave
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

/-- `hubError n = linError n · (log n)^(1/3)`. -/
theorem hubError_eq_linError_mul (n : ℕ) :
    hubError n = linError n * Real.rpow (Real.log n) (1 / 3 : ℝ) := rfl

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

/-- The hub cost on the grid range `0.2169 x ≤ m ≤ x/4`. -/
theorem lin_core {x m : ℝ} (hx4 : 4 * m ≤ x) (hxm : 2169 / 10000 * x ≤ m) :
    (hubLinKX : ℝ) * x ^ 3 + 8 * hubLinKW * m ^ 3 ≤ 1000 * (11329 / 10) * m * x ^ 2 := by
  have hx : 0 ≤ x := by nlinarith
  have h1 : 0 ≤ m - 2169 / 10000 * x := by linarith
  have h2 : 0 ≤ x - 4 * m := by linarith
  have h3 : 0 ≤ 4 * m + (4 * (2169 / 10000) + 1) * x := by nlinarith
  have hP := mul_nonneg (mul_nonneg h1 h2) h3
  have hq1 := mul_nonneg h1 (sq_nonneg x)
  have hq2 := mul_nonneg h2 (sq_nonneg x)
  norm_num [hubLinKX, hubLinKW]
  nlinarith [hP, hq1, hq2]

/-- The grid range in terms of `x = n^(1/3)`. -/
theorem lin_range {n m : ℕ} (hn : linN ≤ n) (hcube : 64 * m ^ 3 ≤ n)
    (hmax : n < 192 * (m + 1) ^ 2 * (Nat.log 2 n + 1) ∨ n < 64 * (m + 1) ^ 3) :
    225 ≤ cbrtN n ∧ 4 * (m : ℝ) ≤ cbrtN n ∧ 2169 / 10000 * cbrtN n ≤ m := by
  set x := cbrtN n with hxdef
  have hx0 := cbrtN_nonneg n
  have hx3 := cbrtN_cube n
  rw [← hxdef] at hx0 hx3
  have hnR : (11534336 : ℝ) ≤ n := by exact_mod_cast (show 11534336 ≤ n by unfold linN at hn; omega)
  have hx225 : 225 ≤ x := by
    apply le_of_cube_le hx0; rw [hx3]; linarith [show (225 : ℝ) ^ 3 = 11390625 by norm_num]
  have hx4 : 4 * (m : ℝ) ≤ x := by
    apply le_of_cube_le hx0; rw [hx3]
    have : ((64 * m ^ 3 : ℕ) : ℝ) ≤ n := by exact_mod_cast hcube
    push_cast at this; nlinarith
  refine ⟨hx225, hx4, ?_⟩
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  -- `x < 4.517 (m + 1)`
  have hρ : x < 4517 / 1000 * ((m : ℝ) + 1) := by
    rcases hmax with hcap | hcub
    · have hL := (lin_log_bounds hn).2
      set L := Nat.log 2 n + 1
      have hLR : 125 * (192 * (L : ℝ)) ^ 3 ≤ 1061208 * n := by exact_mod_cast hL
      have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
      have hLx : 192 * (L : ℝ) ≤ 102 / 5 * x := by
        apply le_of_cube_le (by positivity)
        rw [mul_pow, mul_pow, hx3]; nlinarith
      have hcapR : (n : ℝ) < 192 * ((m : ℝ) + 1) ^ 2 * L := by exact_mod_cast hcap
      have hx2 : x ^ 2 < 102 / 5 * ((m : ℝ) + 1) ^ 2 := by
        have hxpos : 0 < x := by linarith
        have : x ^ 3 < 102 / 5 * x * ((m : ℝ) + 1) ^ 2 := by
          rw [hx3]; nlinarith [sq_nonneg ((m : ℝ) + 1)]
        nlinarith
      nlinarith
    · have hcubR : (n : ℝ) < 64 * ((m : ℝ) + 1) ^ 3 := by exact_mod_cast hcub
      have : x < 4 * ((m : ℝ) + 1) := by
        apply lt_of_cube_lt (by positivity); rw [hx3]; nlinarith
      linarith
  nlinarith

/-- The cubic solver on the initial range, against `n^(8/3)`. -/
theorem cubic_le_linError {n : ℕ} (hn : 4096 ≤ n) (hhi : n ≤ linN) :
    ((5 * n ^ 3 + 1509 * n ^ 2 + 1505 * n + 4796 : ℕ) : ℝ) ≤ 1133 * linError n := by
  rw [linError_eq]
  set x := cbrtN n with hxdef
  have hx0 := cbrtN_nonneg n
  have hx3 := cbrtN_cube n
  rw [← hxdef] at hx0 hx3
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hhiR : (n : ℝ) ≤ 11534336 := by exact_mod_cast (show n ≤ 11534336 by unfold linN at hhi; omega)
  have hx16 : 16 ≤ x := by
    apply le_of_cube_le hx0; rw [hx3]; linarith [show (16 : ℝ) ^ 3 = 4096 by norm_num]
  have hx226 : x ≤ 226 := by
    apply le_of_cube_le (by norm_num); rw [hx3]; linarith [show (226 : ℝ) ^ 3 = 11543176 by norm_num]
  push_cast
  have hn3 : (n : ℝ) = x ^ 3 := hx3.symm
  rw [hn3]
  have h1 : 0 ≤ 226 - x := by linarith
  have h2 : 0 ≤ x - 16 := by linarith
  have hx6 : 0 ≤ x ^ 6 := by positivity
  have hkey : 1509 * x ^ 6 + 1505 * x ^ 3 + 4796 ≤ x ^ 8 * (1133 - 5 * x) := by
    have hx2 : 256 ≤ x ^ 2 := by nlinarith
    have hx3' : 4096 ≤ x ^ 3 := by nlinarith
    have hbase : 7810 ≤ x ^ 2 * (1133 - 5 * x) := by nlinarith [mul_nonneg h1 h2]
    have hx8 : x ^ 8 * (1133 - 5 * x) = x ^ 6 * (x ^ 2 * (1133 - 5 * x)) := by ring
    rw [hx8]
    nlinarith [mul_le_mul_of_nonneg_left hbase hx6, pow_le_pow_left₀ (by norm_num) hx16 6]
  nlinarith

set_option maxHeartbeats 1600000 in
/-- **The hub algorithm without the logarithm**: for every `n ≥ linN`,
`OPT(B) ≤ M(B) + 1133 n^(8/3)`. -/
theorem optimalLength_le_linError {n : ℕ} [NeZero n] (hn : linN ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) + 1133 * linError n := by
  obtain ⟨m, hm50, hcap, hcube, hmax, hopt⟩ := optimalLength_le_lin_nat hn B
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
      (m : ℝ) * (1000 * (11329 / 10) * x ^ 8) := by
    have e1 : (m : ℝ) * (2 * (hubLinKX : ℝ) * X) = hubLinKX * (2 * m * X) := by ring
    have e2 : (m : ℝ) * (2 * hubLinKW * ((2 * (m : ℝ)) ^ 2 * (x ^ 3) ^ 2)) =
        x ^ 6 * (8 * hubLinKW * m ^ 3) := by ring
    have e3 : (m : ℝ) * (1000 * (11329 / 10) * x ^ 8) = x ^ 6 * (1000 * (11329 / 10) * m * x ^ 2) := by
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
