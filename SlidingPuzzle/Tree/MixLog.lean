import SlidingPuzzle.Tree.MixGrid

/-! # Choosing the depth: error `O(n^(5/2) (ln n)^(3/2))`

For each `n` take the largest depth `h` with `8h·256^(2h+1) ≤ n`. Then
`n < 8(h+1)·256^(2h+3) ≤ 176^(4h+2)`, so `n^(1/(4h+2)) ≤ 176`, and `ln n ≥ 11h + 5.5`. -/

namespace SlidingPuzzle.Tree

/-- The threshold of `tree_uniform_approximation_explicit` at depth `h`. -/
def mixN (h : ℕ) : ℕ := 8 * h * 256 ^ (2 * h + 1)

theorem mixN_succ_le : ∀ h : ℕ, 1 ≤ h → mixN (h + 1) ≤ 176 ^ (4 * h + 2)
  | 1, _ => by unfold mixN; norm_num
  | h + 2, _ => by
    have ih := mixN_succ_le (h + 1) (by omega)
    unfold mixN at ih ⊢
    have e1 : 256 ^ (2 * (h + 2 + 1) + 1) = 256 ^ (2 * (h + 1 + 1) + 1) * 65536 := by
      rw [show 2 * (h + 2 + 1) + 1 = 2 * (h + 1 + 1) + 1 + 2 by ring, pow_add]; norm_num
    have e2 : 176 ^ (4 * (h + 2) + 2) = 176 ^ (4 * (h + 1) + 2) * 959512576 := by
      rw [show 4 * (h + 2) + 2 = 4 * (h + 1) + 2 + 4 by ring, pow_add]; norm_num
    have h3 : 8 * (h + 2 + 1) ≤ 2 * (8 * (h + 1 + 1)) := by omega
    calc 8 * (h + 2 + 1) * 256 ^ (2 * (h + 2 + 1) + 1)
        ≤ 2 * (8 * (h + 1 + 1)) * (256 ^ (2 * (h + 1 + 1) + 1) * 65536) := by
          rw [e1]; exact Nat.mul_le_mul_right _ h3
      _ = 131072 * (8 * (h + 1 + 1) * 256 ^ (2 * (h + 1 + 1) + 1)) := by ring
      _ ≤ 131072 * 176 ^ (4 * (h + 1) + 2) := Nat.mul_le_mul_left _ ih
      _ ≤ 176 ^ (4 * (h + 1) + 2) * 959512576 := by rw [mul_comm]; exact Nat.mul_le_mul_left _ (by norm_num)
      _ = _ := e2.symm

theorem log_256_ge : (5.5 : ℝ) ≤ Real.log 256 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 : Real.exp 5.5 ^ 2 = Real.exp 1 ^ 11 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 : Real.exp 1 ^ 11 ≤ (2.7182818286 : ℝ) ^ 11 := pow_le_pow_left₀ (Real.exp_pos 1).le h2.le 11
  have h5 : (2.7182818286 : ℝ) ^ 11 ≤ 256 ^ 2 := by norm_num
  have h4 : Real.exp 5.5 ^ 2 ≤ (256 : ℝ) ^ 2 := by rw [h1]; exact h3.trans h5
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num)).1 h4

/-- `(h+3) √h ≤ √5 (h + 1/2)^(3/2)`, squared. -/
theorem poly_le (x : ℝ) (hx : 1 ≤ x) : (x + 3) ^ 2 * x ≤ 5 * (x + 1 / 2) ^ 3 := by
  have h1 : 0 ≤ (x - 1) * (4 * x ^ 2 + 5.5 * x + 0.25) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith

theorem coef_le {h L : ℝ} (hh : 1 ≤ h) (hL : 11 * h + 5.5 ≤ L) :
    102 * (h + 3) * Real.sqrt (8 * h) * 176 ≤ 3200 * L ^ ((3 : ℝ) / 2) := by
  have hL0 : 0 < L := by linarith
  have e : L ^ ((3 : ℝ) / 2) = L * Real.sqrt L := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hL0.le (by norm_num)]; norm_num
  rw [e]
  have hA : 0 ≤ 102 * (h + 3) * Real.sqrt (8 * h) * 176 := by positivity
  have hB : 0 ≤ 3200 * (L * Real.sqrt L) := by positivity
  rw [← pow_le_pow_iff_left₀ hA hB (two_ne_zero)]
  have hs8 : Real.sqrt (8 * h) ^ 2 = 8 * h := Real.sq_sqrt (by positivity)
  have hsL : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
  have hp := poly_le h hh
  have hL' : h + 1 / 2 ≤ L / 11 := by linarith
  have hc : (h + 1 / 2) ^ 3 ≤ (L / 11) ^ 3 := pow_le_pow_left₀ (by positivity) hL' 3
  calc (102 * (h + 3) * Real.sqrt (8 * h) * 176) ^ 2
      = 102 ^ 2 * 176 ^ 2 * 8 * ((h + 3) ^ 2 * h) := by rw [mul_pow, mul_pow, mul_pow, hs8]; ring
    _ ≤ 102 ^ 2 * 176 ^ 2 * 8 * (5 * (L / 11) ^ 3) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith
    _ ≤ 3200 ^ 2 * L ^ 3 := by
        have : (0 : ℝ) ≤ L ^ 3 := by positivity
        rw [div_pow]; nlinarith
    _ = (3200 * (L * Real.sqrt L)) ^ 2 := by rw [mul_pow, mul_pow, hsL]; ring

open SlidingPuzzle in
/-- **Error `n^(5/2) (ln n)^(3/2)`**: `OPT(B) ≤ M(B) + 3200 n^(5/2) (ln n)^(3/2)` for every
reachable board with `n ≥ mixN 1 = 8·256³ ≈ 1.3·10⁸`. -/
theorem tree_log_approximation_explicit {n : ℕ} [NeZero n] (hn : mixN 1 ≤ n)
    (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      3200 * (n : ℝ) ^ ((5 : ℝ) / 2) * Real.log n ^ ((3 : ℝ) / 2) := by
  classical
  set h := Nat.findGreatest (fun h => mixN h ≤ n) n with hdef
  have hn1 : 1 ≤ n := le_trans (by unfold mixN; norm_num) hn
  have hh : 1 ≤ h := Nat.le_findGreatest hn1 hn
  have hT : mixN h ≤ n := Nat.findGreatest_spec (P := fun h => mixN h ≤ n) hn1 hn
  have hT1 : n < mixN (h + 1) := by
    have hle : h + 1 ≤ n := by
      have : h + 1 ≤ mixN h := by
        unfold mixN
        have : 1 ≤ 256 ^ (2 * h + 1) := Nat.one_le_pow _ _ (by norm_num)
        nlinarith
      omega
    have := Nat.findGreatest_is_greatest (P := fun h => mixN h ≤ n) (Nat.lt_succ_self h) hle
    simpa using this
  have hbound := tree_uniform_approximation_explicit h hh (n := n) hT B
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  -- `n^(1/(4h+2)) ≤ 176`
  have hroot : (n : ℝ) ^ (1 / (4 * (h : ℝ) + 2)) ≤ 176 := by
    have h1 : (n : ℝ) ≤ (176 : ℝ) ^ (4 * h + 2) := by
      exact_mod_cast hT1.le.trans (mixN_succ_le h hh)
    have h2 := Real.rpow_le_rpow hn0.le h1 (show (0 : ℝ) ≤ 1 / (4 * (h : ℝ) + 2) by positivity)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h2
    have e : ((4 * h + 2 : ℕ) : ℝ) * (1 / (4 * (h : ℝ) + 2)) = 1 := by
      push_cast; field_simp
    rwa [e, Real.rpow_one] at h2
  -- `11h + 5.5 ≤ ln n`
  have hlog : 11 * (h : ℝ) + 5.5 ≤ Real.log n := by
    have h1 : (8 * (h : ℝ)) * (256 : ℝ) ^ (2 * h + 1) ≤ n := by
      have := hT; unfold mixN at this; exact_mod_cast this
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h2
    have h3 : 0 ≤ Real.log (8 * (h : ℝ)) := Real.log_nonneg (by linarith)
    have h4 := log_256_ge
    push_cast at h2
    nlinarith
  have hcoef := coef_le hh1 hlog
  have hsplit : (n : ℝ) ^ (5 / 2 + 1 / (4 * (h : ℝ) + 2)) =
      (n : ℝ) ^ ((5 : ℝ) / 2) * (n : ℝ) ^ (1 / (4 * (h : ℝ) + 2)) := Real.rpow_add hn0 _ _
  have hP : 0 ≤ (n : ℝ) ^ ((5 : ℝ) / 2) := by positivity
  have hA : 0 ≤ 102 * ((h : ℝ) + 3) * Real.sqrt (8 * h) := by positivity
  calc (optimalLength B : ℝ) ≤ _ := hbound
    _ = (manhattan B.val : ℝ) + (n : ℝ) ^ ((5 : ℝ) / 2) *
          (102 * ((h : ℝ) + 3) * Real.sqrt (8 * h) * (n : ℝ) ^ (1 / (4 * (h : ℝ) + 2))) := by
        rw [hsplit]; ring
    _ ≤ (manhattan B.val : ℝ) + (n : ℝ) ^ ((5 : ℝ) / 2) *
          (102 * ((h : ℝ) + 3) * Real.sqrt (8 * h) * 176) := by
        have := mul_le_mul_of_nonneg_left hroot hA
        have := mul_le_mul_of_nonneg_left this hP
        linarith
    _ ≤ (manhattan B.val : ℝ) + (n : ℝ) ^ ((5 : ℝ) / 2) * (3200 * Real.log n ^ ((3 : ℝ) / 2)) := by
        have := mul_le_mul_of_nonneg_left hcoef hP
        linarith
    _ = _ := by ring

end SlidingPuzzle.Tree
