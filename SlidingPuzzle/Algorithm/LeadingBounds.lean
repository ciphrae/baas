import SlidingPuzzle.Algorithm.LeadingBudgets

/-! Leading-term accounting for arbitrary dimensions. The single lower-order
remainder is absorbed only when passing to the eventual Proposition 9 interface. -/
namespace SlidingPuzzle.Algorithm

/-- Retain both coefficients while lifting a fourth-power solution. -/
theorem optimalLength_le_leading_reduction {n k : ℕ} [NeZero n]
    (B : ReachableBoard n) (hk : 2 ≤ k) (hlo : k^4 ≤ n) :
    optimalLength B ≤ manhattan B.val + 70*k^11+19030*k^10 +
      2*((15*n^2+3002*n+1)*(n-k^4)) := by
  letI : NeZero (k^4) := ⟨by positivity⟩
  have hk4 : 4 ≤ k^4 := by nlinarith [Nat.pow_le_pow_left hk 4]
  obtain ⟨C,p,hp,hC⟩ := Parberry.exists_prefix B.val (n-k^4) (by omega)
  have hd : n-k^4+k^4=n := Nat.sub_add_cancel hlo
  obtain ⟨A,hA⟩ := exists_residual_board (n-k^4) hd C hC
  have hreachC : Reachable C := by
    obtain ⟨r⟩ := B.property
    exact ⟨r.append p⟩
  have hreachA : Reachable A :=
    residual_reachable (by omega : 2 ≤ k^4) (n-k^4) hd C hC A hA hreachC
  obtain ⟨q,_,hq⟩ := exists_fourth_power_solution_leading k hk A hreachA
  have hq' : q.length ≤ manhattan A+(70*k^11+19030*k^10) := by omega
  have h := optimalLength_le_prefix_residual_solution B (n-k^4) hd C p hC A hA q hq'
  omega

/-- Convert the lower-order envelope without absorbing it into the leading term. -/
theorem pow_ten_le_rpow_of_fourth_power_le {k n : ℕ} (hkn : k^4 ≤ n) :
    (k : ℝ)^10 ≤ Real.rpow (n : ℝ) (5/2 : ℝ) := by
  have hkn' : (k : ℝ)^4 ≤ (n : ℝ) := by exact_mod_cast hkn
  calc
    (k : ℝ)^10 = Real.rpow ((k : ℝ)^4) (5/2 : ℝ) := by
      rw [Real.rpow_eq_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg k) 4]
      norm_num [Real.rpow_natCast]
    _ ≤ Real.rpow (n : ℝ) (5/2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hkn' (by norm_num)

/-- An explicit two-term bound uniform in the input board. The remainder is
intentionally loose, but cannot inflate the leading coefficient. -/
theorem optimalLength_le_leading {n : ℕ} [NeZero n]
    (hn : 16 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ)+
      190*Real.rpow (n : ℝ) (11/4 : ℝ)+43054*Real.rpow (n : ℝ) (5/2 : ℝ) := by
  obtain ⟨k,hk,hlo,hhi,_⟩ := exists_fourth_power_dimension hn
  have hnat := optimalLength_le_leading_reduction B hk hlo
  have hreal : (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ)+
      70*(k : ℝ)^11+19030*(k : ℝ)^10+
      2*(((15*n^2+3002*n+1)*(n-k^4) : ℕ) : ℝ) := by exact_mod_cast hnat
  have hbudget := parberry_reduction_budget hlo hhi
  have hscale := pow_eleven_le_rpow_of_fourth_power_le hlo
  have hsmall := pow_ten_le_rpow_of_fourth_power_le hlo
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have h7 := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (7/4 : ℝ) ≤ 5/2)
  have h3 := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (3/4 : ℝ) ≤ 5/2)
  norm_num at hreal hbudget hscale hsmall h7 h3 ⊢
  linarith

/-- Leading inefficiency 95, with all lower-order work in one envelope. -/
theorem exists_solution_with_leading_bound {n : ℕ} [NeZero n]
    (hn : 16 ≤ n) (B : ReachableBoard n) :
    ∃ p : Path B.val (target n),
      (p.inefficientMoves : ℝ) ≤ 95*Real.rpow (n : ℝ) (11/4 : ℝ)+
        21527*Real.rpow (n : ℝ) (5/2 : ℝ) ∧
      (p.length : ℝ) ≤ (manhattan B.val : ℝ)+190*Real.rpow (n : ℝ) (11/4 : ℝ)+
        43054*Real.rpow (n : ℝ) (5/2 : ℝ) := by
  obtain ⟨p,hp⟩ := shortest_witness B
  have hlength := optimalLength_le_leading hn B
  rw [← hp] at hlength
  refine ⟨p,?_,hlength⟩
  have hbalance : (p.length : ℝ)=(manhattan B.val : ℝ)+2*(p.inefficientMoves : ℝ) := by
    exact_mod_cast p.solution_length
  linarith

/-- A quarter-power gap absorbs any fixed remainder at a sufficiently large
size. This is applied once, after adding all phase remainders. -/
theorem quarter_gap_absorb (R n : ℕ) (hn : R^4 ≤ n) :
    (R : ℝ)*Real.rpow (n : ℝ) (5/2 : ℝ) ≤ Real.rpow (n : ℝ) (11/4 : ℝ) := by
  have hroot : (R : ℝ) ≤ Real.rpow (n : ℝ) (1/4 : ℝ) := by
    calc
      (R : ℝ) = Real.rpow ((R : ℝ)^4) (1/4 : ℝ) := by
        rw [Real.rpow_eq_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg R) 4]
        norm_num
      _ ≤ Real.rpow (n : ℝ) (1/4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn) (by norm_num)
  calc
    (R : ℝ)*Real.rpow (n : ℝ) (5/2 : ℝ) ≤
        Real.rpow (n : ℝ) (1/4 : ℝ)*Real.rpow (n : ℝ) (5/2 : ℝ) :=
      mul_le_mul_of_nonneg_right hroot (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = Real.rpow (n : ℝ) (11/4 : ℝ) := by
      convert (Real.rpow_add_of_nonneg (Nat.cast_nonneg n)
        (by norm_num : (0 : ℝ) ≤ 1/4) (by norm_num : (0 : ℝ) ≤ 5/2)).symm using 1 <;> norm_num

/-- Only the final asymptotic adapter spends one extra unit of additive length.
The threshold is deliberately not optimized. -/
theorem optimalLength_le_leading_eventually {n : ℕ} [NeZero n]
    (hn : max 16 (43054^4) ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ)+191*Real.rpow (n : ℝ) (11/4 : ℝ) := by
  have h := optimalLength_le_leading (le_trans (le_max_left _ _) hn) B
  have hr := quarter_gap_absorb 43054 n (le_trans (le_max_right _ _) hn)
  norm_num only [Nat.cast_ofNat] at hr
  linarith

/-- Proposition 9 already permits an eventual bound: small boards impose no
restriction on the leading-term accounting. -/
theorem uniformApproximation_leading : UniformApproximation := by
  refine ⟨191,by norm_num,max 16 (43054^4),?_⟩
  intro n hn hn2
  letI : NeZero n := ⟨by omega⟩
  intro B
  exact optimalLength_le_leading_eventually hn B

end SlidingPuzzle.Algorithm
