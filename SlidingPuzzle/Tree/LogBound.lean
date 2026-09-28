import SlidingPuzzle.Tree.Final

/-! # Choosing the depth: error `O(n^(5/2) (ln n)²)`

For each `n` take the largest depth `h` whose threshold `treeN h` is at most `n`.
Then `n < treeN (h+1) ≤ (290h)^(2h+4)`, so `n^(1/(4h+2)) ≤ 580 √h`, and
`258^(2h+1) ≤ n` gives `10h ≤ ln n`. -/

namespace SlidingPuzzle.Tree

/-- The threshold of `tree_uniform_approximation_explicit` at depth `h`. -/
def treeN (h : ℕ) : ℕ := 8 * h * (max 256 (16 * h) + 2) ^ (2 * h + 1)

theorem treeN_succ_le (h : ℕ) (hh : 1 ≤ h) : treeN (h + 1) ≤ (290 * h) ^ (2 * h + 4) := by
  unfold treeN
  have hM : max 256 (16 * (h + 1)) + 2 ≤ 290 * h := by
    rcases le_total 256 (16 * (h + 1)) with h1 | h1
    · rw [max_eq_right h1]; omega
    · rw [max_eq_left h1]; omega
  have h8 : 8 * (h + 1) ≤ 290 * h := by omega
  calc 8 * (h + 1) * (max 256 (16 * (h + 1)) + 2) ^ (2 * (h + 1) + 1)
      ≤ 290 * h * (290 * h) ^ (2 * (h + 1) + 1) :=
        Nat.mul_le_mul h8 (Nat.pow_le_pow_left hM _)
    _ = (290 * h) ^ (2 * h + 4) := by ring

theorem pow_le_treeN (h : ℕ) (hh : 1 ≤ h) : 258 ^ (2 * h + 1) ≤ treeN h := by
  unfold treeN
  calc 258 ^ (2 * h + 1) ≤ (max 256 (16 * h) + 2) ^ (2 * h + 1) :=
        Nat.pow_le_pow_left (by omega) _
    _ ≤ 8 * h * (max 256 (16 * h) + 2) ^ (2 * h + 1) := Nat.le_mul_of_pos_left _ (by omega)

theorem five_le_log_258 : (5 : ℝ) ≤ Real.log 258 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  have h2 := Real.exp_one_lt_d9
  rw [h1]
  calc Real.exp 1 ^ 5 ≤ (2.7182818286 : ℝ) ^ 5 := pow_le_pow_left₀ (Real.exp_pos 1).le h2.le 5
    _ ≤ 258 := by norm_num

/-- The root of the upper threshold: `n^(1/(4h+2)) ≤ 580 √h` when `n ≤ (290h)^(2h+4)`. -/
theorem root_le (h : ℕ) (hh : 1 ≤ h) {n : ℝ} (hn0 : 0 ≤ n) (hn : n ≤ (290 * (h : ℝ)) ^ (2 * h + 4)) :
    n ^ (1 / (4 * (h : ℝ) + 2)) ≤ 580 * Real.sqrt h := by
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  set e : ℝ := 1 / (4 * (h : ℝ) + 2) with he
  have he0 : 0 ≤ e := by positivity
  have h1 : n ^ e ≤ ((290 * (h : ℝ)) ^ (2 * h + 4)) ^ e := Real.rpow_le_rpow hn0 hn he0
  have h2 : ((290 * (h : ℝ)) ^ (2 * h + 4)) ^ e =
      (290 : ℝ) ^ ((1 : ℝ) / 2) * (h : ℝ) ^ ((1 : ℝ) / 2) *
        ((290 : ℝ) ^ (3 * e) * (h : ℝ) ^ (3 * e)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      Real.mul_rpow (by norm_num) (by positivity)]
    have hsplit : ((2 * h + 4 : ℕ) : ℝ) * e = 1 / 2 + 3 * e := by
      rw [he]; push_cast; field_simp; ring
    rw [hsplit, Real.rpow_add (by norm_num), Real.rpow_add (by positivity)]
    ring
  have h3e : 3 * e ≤ 1 / 2 := by
    rw [he, show 3 * (1 / (4 * (h : ℝ) + 2)) = 3 / (4 * (h : ℝ) + 2) by ring,
      div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h4 : (290 : ℝ) ^ (3 * e) ≤ (290 : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h3e
  have h5 : (h : ℝ) ^ (3 * e) ≤ 2 := by
    have h3h : 3 * e ≤ 1 / (h : ℝ) := by
      rw [he, show 3 * (1 / (4 * (h : ℝ) + 2)) = 3 / (4 * (h : ℝ) + 2) by ring,
        div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    calc (h : ℝ) ^ (3 * e) ≤ (h : ℝ) ^ (1 / (h : ℝ)) := Real.rpow_le_rpow_of_exponent_le hh1 h3h
      _ ≤ ((2 : ℝ) ^ h) ^ (1 / (h : ℝ)) := by
          apply Real.rpow_le_rpow (by positivity) _ (by positivity)
          exact_mod_cast (Nat.lt_two_pow_self).le
      _ = 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
            show (h : ℝ) * (1 / (h : ℝ)) = 1 by field_simp, Real.rpow_one]
  have h290 : (290 : ℝ) ^ ((1 : ℝ) / 2) * (290 : ℝ) ^ ((1 : ℝ) / 2) = 290 := by
    rw [← Real.rpow_add (by norm_num)]; norm_num
  rw [Real.sqrt_eq_rpow]
  calc n ^ e ≤ _ := h1
    _ = _ := h2
    _ ≤ (290 : ℝ) ^ ((1 : ℝ) / 2) * (h : ℝ) ^ ((1 : ℝ) / 2) *
          ((290 : ℝ) ^ ((1 : ℝ) / 2) * 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul h4 h5 (by positivity) (by positivity)
    _ = 580 * (h : ℝ) ^ ((1 : ℝ) / 2) := by
        have : (290 : ℝ) ^ ((1 : ℝ) / 2) * (h : ℝ) ^ ((1 : ℝ) / 2) *
            ((290 : ℝ) ^ ((1 : ℝ) / 2) * 2) =
            ((290 : ℝ) ^ ((1 : ℝ) / 2) * (290 : ℝ) ^ ((1 : ℝ) / 2)) * 2 *
              (h : ℝ) ^ ((1 : ℝ) / 2) := by ring
        rw [this, h290]; ring

open SlidingPuzzle in
/-- **Error `n^(5/2) (ln n)²`**: `OPT(B) ≤ M(B) + 8000 n^(5/2) (ln n)²` for every
reachable board with `n ≥ treeN 1 = 8·258³`. -/
theorem tree_log_approximation_explicit {n : ℕ} [NeZero n] (hn : treeN 1 ≤ n)
    (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      8000 * (n : ℝ) ^ ((5 : ℝ) / 2) * Real.log n ^ 2 := by
  classical
  set h := Nat.findGreatest (fun h => treeN h ≤ n) n with hdef
  have hn1 : 1 ≤ n := le_trans (by unfold treeN; norm_num) hn
  have hh : 1 ≤ h := Nat.le_findGreatest hn1 hn
  have hT : treeN h ≤ n := Nat.findGreatest_spec (P := fun h => treeN h ≤ n) hn1 hn
  have hT1 : n < treeN (h + 1) := by
    have hle : h + 1 ≤ n := by
      have := pow_le_treeN h hh
      have : h + 1 < 258 ^ (2 * h + 1) := by
        calc h + 1 < 2 ^ (h + 1) := Nat.lt_two_pow_self
          _ ≤ 258 ^ (h + 1) := Nat.pow_le_pow_left (by norm_num) _
          _ ≤ 258 ^ (2 * h + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have := Nat.findGreatest_is_greatest (P := fun h => treeN h ≤ n) (Nat.lt_succ_self h) hle
    simpa using this
  have hbound := tree_uniform_approximation_explicit h hh (n := n) hT B
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  -- `n^(1/(4h+2)) ≤ 580 √h`
  have hroot : (n : ℝ) ^ (1 / (4 * (h : ℝ) + 2)) ≤ 580 * Real.sqrt h := by
    apply root_le h hh hn0.le
    have := (hT1.le).trans (treeN_succ_le h hh)
    exact_mod_cast this
  -- `10 h ≤ ln n`
  have hlog : 10 * (h : ℝ) ≤ Real.log n := by
    have h1 : ((258 : ℕ) : ℝ) ^ (2 * h + 1) ≤ n := by exact_mod_cast (pow_le_treeN h hh).trans hT
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    nlinarith [five_le_log_258]
  have hsplit : (n : ℝ) ^ (5 / 2 + 1 / (4 * (h : ℝ) + 2)) =
      (n : ℝ) ^ ((5 : ℝ) / 2) * (n : ℝ) ^ (1 / (4 * (h : ℝ) + 2)) := Real.rpow_add hn0 _ _
  have hs8 : Real.sqrt (8 * h) = Real.sqrt 8 * Real.sqrt h := Real.sqrt_mul (by norm_num) _
  have hsq8 : Real.sqrt 8 ≤ 2.8285 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hsqh : Real.sqrt h * Real.sqrt h = h := Real.mul_self_sqrt (by positivity)
  have hP : 0 ≤ (n : ℝ) ^ ((5 : ℝ) / 2) := by positivity
  have hcoef : 120 * ((h : ℝ) + 3) * Real.sqrt (8 * h) * (n : ℝ) ^ (1 / (4 * (h : ℝ) + 2)) ≤
      8000 * Real.log n ^ 2 := by
    rw [hs8]
    have hA : 0 ≤ 120 * ((h : ℝ) + 3) * (Real.sqrt 8 * Real.sqrt h) := by positivity
    calc 120 * ((h : ℝ) + 3) * (Real.sqrt 8 * Real.sqrt h) * (n : ℝ) ^ (1 / (4 * (h : ℝ) + 2))
        ≤ 120 * ((h : ℝ) + 3) * (Real.sqrt 8 * Real.sqrt h) * (580 * Real.sqrt h) :=
          mul_le_mul_of_nonneg_left hroot hA
      _ = 69600 * Real.sqrt 8 * (((h : ℝ) + 3) * (Real.sqrt h * Real.sqrt h)) := by ring
      _ ≤ 69600 * 2.8285 * (4 * (h : ℝ) ^ 2) := by
          rw [hsqh]
          apply mul_le_mul (by linarith) (by nlinarith) (by positivity) (by norm_num)
      _ ≤ 8000 * Real.log n ^ 2 := by nlinarith
  calc (optimalLength B : ℝ) ≤ _ := hbound
    _ = (manhattan B.val : ℝ) + (n : ℝ) ^ ((5 : ℝ) / 2) *
          (120 * ((h : ℝ) + 3) * Real.sqrt (8 * h) * (n : ℝ) ^ (1 / (4 * (h : ℝ) + 2))) := by
        rw [hsplit]; ring
    _ ≤ (manhattan B.val : ℝ) + (n : ℝ) ^ ((5 : ℝ) / 2) * (8000 * Real.log n ^ 2) := by
        have := mul_le_mul_of_nonneg_left hcoef hP
        linarith
    _ = _ := by ring

end SlidingPuzzle.Tree
