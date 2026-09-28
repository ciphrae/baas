import SlidingPuzzle.Hub.LinBound
import Mathlib

/-! # The error scale `n^(8/3)`

With `x = n^(1/3)`, the grid of `LinBound.lean` satisfies `57 m³ ≤ x³`, so
`m ≤ 0.2599 x`. The cost `KX x³/m + 8 KW m²` of the hub algorithm, multiplied by
`m`, is a concave function of `m`, so on a range `a ≤ m ≤ b` its two endpoint
values suffice (`lin_core_of`). For `n ≥ linN = 10⁹` the range is
`0.2588 x ≤ m ≤ 0.2599 x` (`lin_range`): the capacity condition holds with room
to spare at `m + 1` (there `Λ(m+1) ≤ 0.08 x`, `lin_log_le`), so the grid is
the largest `m` with `57 m³ ≤ n`.

On this range the cost is at most `582.9 x²`, close to the minimum of
`KX/c + 8 KW c²` at `c ≈ 0.259`; the prefix adds at most `0.032 x²`. -/

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

/-- On a range `a ≤ m ≤ b`, the hub cost `KX x³ + 8 KW m³ ≤ D m x²` follows from
its two endpoint values: `D m x² - 8 KW m³` is concave in `m`. -/
theorem lin_core_of {x m a b D : ℝ} (hmb : m ≤ b) (ham : a ≤ m) (ha0 : 0 ≤ a)
    (hA : (hubLinKX : ℝ) * x ^ 3 + 8 * hubLinKW * a ^ 3 ≤ D * a * x ^ 2)
    (hB : (hubLinKX : ℝ) * x ^ 3 + 8 * hubLinKW * b ^ 3 ≤ D * b * x ^ 2) :
    (hubLinKX : ℝ) * x ^ 3 + 8 * hubLinKW * m ^ 3 ≤ D * m * x ^ 2 := by
  set g : ℝ → ℝ := fun t => D * t * x ^ 2 - 8 * hubLinKW * t ^ 3 - hubLinKX * x ^ 3 with hg
  have hga : 0 ≤ g a := by simp only [hg]; linarith
  have hgb : 0 ≤ g b := by simp only [hg]; linarith
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

/-- The hub cost on the grid range `0.2588 x ≤ m ≤ 0.2599 x`. -/
theorem lin_core {x m : ℝ} (hx : 0 ≤ x) (hxm : 2588 / 10000 * x ≤ m)
    (hmx : m ≤ 2599 / 10000 * x) :
    (hubLinKX : ℝ) * x ^ 3 + 8 * hubLinKW * m ^ 3 ≤ 1000 * (5829 / 10) * m * x ^ 2 := by
  have hx3 : 0 ≤ x ^ 3 := by positivity
  refine lin_core_of hmx hxm (by positivity) ?_ ?_
  · norm_num [hubLinKX, hubLinKW]; nlinarith [hx3]
  · norm_num [hubLinKX, hubLinKW]; nlinarith [hx3]

/-- The capacity logarithm against the cube root: if `2^L ≤ x⁷` and
`x ≥ 1000`, then `L + 4 ≤ 0.08 x`. -/
theorem lin_log_le {x : ℝ} (hx : 1000 ≤ x) {L : ℕ} (hL : (2 : ℝ) ^ L ≤ x ^ 7) :
    (L : ℝ) + 4 ≤ 8 / 100 * x := by
  rcases (show L ≤ 76 ∨ 77 ≤ L by omega) with h76 | h77
  · have : (L : ℝ) ≤ 76 := by exact_mod_cast h76
    linarith
  · have hnat : ∀ i, 77 ≤ i → 25 ^ 7 * (i + 4) ^ 7 ≤ 2 ^ 7 * 2 ^ i := by
      intro i hi
      induction i, hi using Nat.le_induction with
      | base => norm_num
      | succ i hi ih =>
        have hstep : (i + 1 + 4) ^ 7 ≤ 2 * (i + 4) ^ 7 := by
          have h1 := Nat.pow_le_pow_left (show 81 * (i + 1 + 4) ≤ 82 * (i + 4) by omega) 7
          rw [mul_pow, mul_pow] at h1
          have h2 : 82 ^ 7 * (i + 4) ^ 7 ≤ 81 ^ 7 * (2 * (i + 4) ^ 7) := by
            have : (82 : ℕ) ^ 7 ≤ 81 ^ 7 * 2 := by norm_num
            calc 82 ^ 7 * (i + 4) ^ 7 ≤ 81 ^ 7 * 2 * (i + 4) ^ 7 := Nat.mul_le_mul_right _ this
              _ = 81 ^ 7 * (2 * (i + 4) ^ 7) := by ring
          exact Nat.le_of_mul_le_mul_left (h1.trans h2) (by norm_num)
        rw [pow_succ 2 i]
        nlinarith
    have h := hnat L h77
    have hR : (25 : ℝ) ^ 7 * ((L : ℝ) + 4) ^ 7 ≤ 2 ^ 7 * 2 ^ L := by exact_mod_cast h
    have h7 : ((L : ℝ) + 4) ^ 7 ≤ (8 / 100 * x) ^ 7 := by
      rw [mul_pow]
      have := mul_le_mul_of_nonneg_left hL (show (0 : ℝ) ≤ 2 ^ 7 by positivity)
      nlinarith
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h7

/-- The grid range in terms of `x = n^(1/3)`, for `n ≥ linN = 10⁹`: the cube
scale bounds `m ≤ 0.2599 x`, and maximality gives `0.2588 x ≤ m`, since the
capacity condition cannot fail at `m + 1`. -/
theorem lin_range {n m : ℕ} (hn : linN ≤ n) (hcube : 57 * m ^ 3 ≤ n)
    (hmax : 5 * n < gridCap n (m + 1) ∨ n < 57 * (m + 1) ^ 3) :
    1000 ≤ cbrtN n ∧ 2588 / 10000 * cbrtN n ≤ m ∧ (m : ℝ) ≤ 2599 / 10000 * cbrtN n := by
  set x := cbrtN n with hxdef
  have hx0 := cbrtN_nonneg n
  have hx3 := cbrtN_cube n
  rw [← hxdef] at hx0 hx3
  have hnR : (10 ^ 9 : ℝ) ≤ n := by exact_mod_cast (show 10 ^ 9 ≤ n by unfold linN at hn; omega)
  have hx1000 : 1000 ≤ x := by
    apply le_of_cube_le hx0; rw [hx3]; norm_num at hnR ⊢; linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  -- `57 t³ ≤ x³` bounds `t ≤ 0.2599 x`
  have hup : ∀ t : ℝ, 0 ≤ t → 57 * t ^ 3 ≤ x ^ 3 → t ≤ 2599 / 10000 * x := by
    intro t ht h
    apply le_of_cube_le (by positivity)
    nlinarith [pow_nonneg hx0 3]
  have hmup : (m : ℝ) ≤ 2599 / 10000 * x := by
    apply hup _ hm0; rw [hx3]; exact_mod_cast hcube
  refine ⟨hx1000, ?_, hmup⟩
  by_cases hc1 : 57 * (m + 1) ^ 3 ≤ n
  · exfalso
    have hcap : 5 * n < gridCap n (m + 1) := by
      rcases hmax with h | h
      · exact h
      · omega
    have hm1 : (m : ℝ) + 1 ≤ 2599 / 10000 * x := by
      apply hup _ (by positivity); rw [hx3]; exact_mod_cast hc1
    set L := Nat.log 2 (2 * (m + 1) * n ^ 2) with hLdef
    have hpow : 2 ^ L ≤ 2 * (m + 1) * n ^ 2 := by
      have : 0 < n := by unfold linN at hn; omega
      exact Nat.pow_log_le_self 2 (by positivity)
    have hpowR : (2 : ℝ) ^ L ≤ 2 * ((m : ℝ) + 1) * (x ^ 3) ^ 2 := by
      rw [hx3]; exact_mod_cast hpow
    have hL7 : (2 : ℝ) ^ L ≤ x ^ 7 := by
      have := mul_le_mul_of_nonneg_right (show 2 * ((m : ℝ) + 1) ≤ x by linarith)
        (show (0 : ℝ) ≤ (x ^ 3) ^ 2 by positivity)
      nlinarith
    have hLx := lin_log_le hx1000 hL7
    have hcapR : 5 * (n : ℝ) < 304 * ((m : ℝ) + 1) ^ 2 * ((L : ℝ) + 4) + 10 * ((m : ℝ) + 1) := by
      have : ((5 * n : ℕ) : ℝ) < ((gridCap n (m + 1) : ℕ) : ℝ) := by exact_mod_cast hcap
      unfold gridCap at this
      push_cast at this
      linarith
    rw [← hx3] at hcapR
    have hsq : ((m : ℝ) + 1) ^ 2 ≤ (2599 / 10000 * x) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hm1 2
    have h1 := mul_le_mul hsq hLx (by positivity) (by positivity)
    nlinarith
  · -- the cube scale fails at `m + 1`
    have hcub : (n : ℝ) < 57 * ((m : ℝ) + 1) ^ 3 := by
      have : n < 57 * (m + 1) ^ 3 := by omega
      exact_mod_cast this
    by_contra hc
    push Not at hc
    have h1 : (m : ℝ) + 1 ≤ 2598 / 10000 * x := by linarith
    have h2 := pow_le_pow_left₀ (by positivity) h1 3
    rw [← hx3] at hcub
    nlinarith

set_option maxHeartbeats 1600000 in
/-- The hub algorithm, given the core estimate `KX x³ + 8 KW m³ ≤ 582.9 m x²` for
its grid: `OPT(B) ≤ M(B) + 583 n^(8/3)`. -/
theorem optimalLength_le_of_core {n m : ℕ} [NeZero n] (B : ReachableBoard n)
    (hm1 : 1 ≤ m) (hx1000 : 1000 ≤ cbrtN n) (hx2 : 2 * (m : ℝ) ≤ cbrtN n)
    (hopt : 1000 * optimalLength B ≤ 1000 * manhattan B.val +
        2 * hubLinKX * (n ^ 2 * (n / (2 * m))) + 2 * hubLinKW * ((2 * m) ^ 2 * n ^ 2) +
        2000 * ((15 * n ^ 2 + 3002 * n + 1) * (n - 2 * m * (n / (2 * m)))))
    (hcore : (hubLinKX : ℝ) * cbrtN n ^ 3 + 8 * hubLinKW * (m : ℝ) ^ 3 ≤
      1000 * (5829 / 10) * m * cbrtN n ^ 2) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) + 583 * linError n := by
  rw [linError_eq]
  set x := cbrtN n with hxdef
  have hx3 := cbrtN_cube n
  rw [← hxdef] at hx3
  set s := n / (2 * m) with hsdef
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
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
      (m : ℝ) * (1000 * (5829 / 10) * x ^ 8) := by
    have e1 : (m : ℝ) * (2 * (hubLinKX : ℝ) * X) = hubLinKX * (2 * m * X) := by ring
    have e2 : (m : ℝ) * (2 * hubLinKW * ((2 * (m : ℝ)) ^ 2 * (x ^ 3) ^ 2)) =
        x ^ 6 * (8 * hubLinKW * m ^ 3) := by ring
    have e3 : (m : ℝ) * (1000 * (5829 / 10) * x ^ 8) = x ^ 6 * (1000 * (5829 / 10) * m * x ^ 2) := by
      ring
    have e4 : x ^ 6 * ((hubLinKX : ℝ) * x ^ 3) = hubLinKX * x ^ 9 := by ring
    have hk := mul_le_mul_of_nonneg_left hmX hKX
    rw [mul_add, e1, e2, e3]
    rw [mul_add, e4] at h2
    linarith
  have hmain' := le_of_mul_le_mul_left hmain hmpos
  -- the prefix: `2000 · 16 n² · 2m ≤ 32000 x⁷ ≤ 32 x⁸`
  have hZx : 2000 * (16 * (x ^ 3) ^ 2 * (2 * (m : ℝ))) ≤ 32 * x ^ 8 := by
    have e : 2000 * (16 * (x ^ 3) ^ 2 * (2 * (m : ℝ))) = 32000 * x ^ 6 * (2 * m) := by ring
    have h4 := mul_le_mul_of_nonneg_left hx2 (show (0 : ℝ) ≤ 32000 * x ^ 6 by positivity)
    have h5 : 32000 * x ^ 6 * x ≤ 32 * x ^ 8 := by
      have e'' : x ^ 8 = x ^ 6 * x * x := by ring
      rw [e'']
      have : 0 ≤ x ^ 6 * x := by positivity
      nlinarith
    linarith
  have hZ2 := mul_le_mul_of_nonneg_left hZR (show (0 : ℝ) ≤ 2000 by norm_num)
  linarith

/-- **The hub algorithm without the logarithm**: for every `n ≥ linN = 10⁹`,
`OPT(B) ≤ M(B) + 583 n^(8/3)`. -/
theorem optimalLength_le_linError {n : ℕ} [NeZero n] (hn : linN ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) + 583 * linError n := by
  obtain ⟨m, hm, hcube, hmax, hopt⟩ := optimalLength_le_lin_nat hn B
  obtain ⟨hx1000, hlo, hhi⟩ := lin_range hn hcube hmax
  have hx0 := cbrtN_nonneg n
  exact optimalLength_le_of_core B (by omega) hx1000 (by linarith) hopt (lin_core hx0 hlo hhi)

end SlidingPuzzle.Hub
