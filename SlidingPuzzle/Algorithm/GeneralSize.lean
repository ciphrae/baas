import SlidingPuzzle.Proposition9
import SlidingPuzzle.Algorithm.Dimension
import SlidingPuzzle.Algorithm.ResidualPotential
import SlidingPuzzle.Algorithm.Admissible
import SlidingPuzzle.Parberry.Prefix

/-! # Arbitrary board sides

Let `x = n^(1/4)`, `k = ⌊2x/3⌋ ≥ 2 and `s = ⌊n/k⌋ ≥ k³`. Solve the outer
`d = n - k*s < k` rows and columns with the Parberry prefix and the remaining
`k*s × k*s` board with `exists_admissible_solution`, whose quadrupled
inefficiency is `21*k²s³ + 52*k⁵s² + O(k*s³)`. Here

* `k²s³ ≤ n³/k ≤ (3/2)x¹¹ + 4x¹⁰` because `k > 2x/3 - 1`,
* `k⁵s² ≤ k³n² ≤ (8/27)x¹¹` because `k ≤ 2x/3`,
* `k*s³ ≤ 4x¹⁰` because `k ≥ x/2`,
* the prefix costs at most `103x¹⁰` because `d < k ≤ x`.

The factor `2/3` is close to the minimizer `(21/156)^(1/4) ≈ 0.606` of
`21/c + 52c³`; the paper's choice `c = 1` gives `36.5` instead of `23.46`.
For every `n ≥ 12⁴`,

```text
inefficiency ≤ 11.73*n^(11/4) + 78252*n^(5/2)      (exists_solution_explicit)
```

This bound is also the local solver of Finish at the second level
(`TwoLevel.lean`). -/
namespace SlidingPuzzle.Algorithm
open SlidingPuzzle.Partition

/-- The residual board `k*⌊n/k⌋` has admissible dimensions. -/
theorem residual_dims {n k : ℕ} (hk : 2 ≤ k) (hlo : k^4 ≤ n) : Dims (k*(n/k)) k := by
  have hk0 : 0 < k := by omega
  have hside : side (k*(n/k)) k = n/k := by
    unfold side; exact Nat.mul_div_cancel_left _ hk0
  refine ⟨hk, ?_, by rw [hside]⟩
  rw [hside]
  apply (Nat.le_div_iff_mul_le hk0).mpr
  calc k^3*k = k^4 := by ring
    _ ≤ n := hlo

/-- Prefix and residual combined: an OPT bound in terms of `k` and `n`. -/
theorem optimalLength_le_of_residual {n k : ℕ} [NeZero n]
    (B : ReachableBoard n) (hk : 2 ≤ k) (hlo : k^4 ≤ n) :
    2*optimalLength B ≤ 2*manhattan B.val + 21*(k^2*(n/k)^3)+52*(k^5*(n/k)^2)+
      78128*(k*(n/k)^3) +
      4*((15*n^2+3002*n+1)*(n-k*(n/k))) := by
  have hdims := residual_dims hk hlo
  have hm4 := hdims.two_le_n
  have hmn : k*(n/k) ≤ n := Nat.mul_div_le n k
  letI : NeZero (k*(n/k)) := ⟨by omega⟩
  have hside : side (k*(n/k)) k = n/k := by
    unfold side; exact Nat.mul_div_cancel_left _ (by omega)
  obtain ⟨C,p,hp,hC⟩ := Parberry.exists_prefix B.val (n-k*(n/k)) (by omega)
  have hd : n-k*(n/k)+k*(n/k)=n := Nat.sub_add_cancel hmn
  obtain ⟨A,hA⟩ := exists_residual_board (n-k*(n/k)) hd C hC
  have hreachC : Reachable C := by
    obtain ⟨r⟩ := B.property
    exact ⟨r.append p⟩
  have hreachA : Reachable A :=
    residual_reachable (by omega : 2 ≤ k*(n/k)) (n-k*(n/k)) hd C hC A hA hreachC
  obtain ⟨q,_,hq⟩ := exists_admissible_solution hdims A hreachA
  rw [hside] at hq
  have hq' : q.length ≤ manhattan A+(21*(k^2*(n/k)^3)+52*(k^5*(n/k)^2)+78128*(k*(n/k)^3))/2 := by
    omega
  have h := optimalLength_le_prefix_residual_solution B (n-k*(n/k)) hd C p hC A hA q hq'
  omega

/-- The quarter power of `n`, with `x⁴ = n` and `x^j = n^(j/4)`. -/
private theorem quarter_facts (n : ℕ) :
    0 ≤ Real.rpow (n : ℝ) (1/4 : ℝ) ∧ (Real.rpow (n : ℝ) (1/4 : ℝ))^4 = (n : ℝ) ∧
      (Real.rpow (n : ℝ) (1/4 : ℝ))^11 = Real.rpow (n : ℝ) (11/4 : ℝ) ∧
      (Real.rpow (n : ℝ) (1/4 : ℝ))^10 = Real.rpow (n : ℝ) (5/2 : ℝ) := by
  refine ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _, ?_, ?_, ?_⟩
  · simpa using Real.rpow_inv_natCast_pow (Nat.cast_nonneg n) (by norm_num : (4 : ℕ) ≠ 0)
  · convert (Real.rpow_mul_natCast (Nat.cast_nonneg n) (1/4 : ℝ) 11).symm using 1 <;> norm_num
  · convert (Real.rpow_mul_natCast (Nat.cast_nonneg n) (1/4 : ℝ) 10).symm using 1 <;> norm_num

/-- The four cost terms in powers of `x = n^(1/4)`. -/
private theorem residual_terms {n k : ℕ} (hn : 12^4 ≤ n) (hlo : 81*k^4 ≤ 16*n)
    (hhi : 16*n < 81*(k+1)^4) :
    let x := Real.rpow (n : ℝ) (1/4 : ℝ)
    ((k^2*(n/k)^3 : ℕ) : ℝ) ≤ 3/2*x^11+4*x^10 ∧
      ((k^5*(n/k)^2 : ℕ) : ℝ) ≤ 8/27*x^11 ∧ ((k*(n/k)^3 : ℕ) : ℝ) ≤ 4*x^10 ∧
      (((15*n^2+3002*n+1)*(n-k*(n/k)) : ℕ) : ℝ) ≤ 103*x^10 := by
  intro x
  obtain ⟨hx0, hx4, -, -⟩ := quarter_facts n
  have hnR : (n : ℝ) = x^4 := hx4.symm
  have hkx : 3*(k : ℝ) ≤ 2*x := by
    have h : (3*(k : ℝ))^4 ≤ (2*x)^4 := by
      have : (81*(k : ℝ)^4) ≤ 16*n := by exact_mod_cast hlo
      rw [hnR] at this; nlinarith
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h
  have hxk : 2*x < 3*((k : ℝ)+1) := by
    have h : (2*x)^4 < (3*((k : ℝ)+1))^4 := by
      have : 16*(n : ℝ) < 81*((k : ℝ)+1)^4 := by exact_mod_cast hhi
      rw [hnR] at this; nlinarith
    exact lt_of_pow_lt_pow_left₀ 4 (by positivity) h
  have hx8 : (12 : ℝ) ≤ x := by
    have h : (12 : ℝ)^4 ≤ x^4 := by rw [hx4]; exact_mod_cast hn
    exact le_of_pow_le_pow_left₀ (by norm_num) hx0 h
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hxk2 : x ≤ 2*(k : ℝ) := by linarith
  have hk1 : (1 : ℝ) ≤ k := by linarith
  set s := n/k with hsdef
  have hks : k*s ≤ n := Nat.mul_div_le n k
  have hsqR : ((k : ℝ)*s)^2 ≤ x^8 := by
    have : ((k*s)^2 : ℕ) ≤ n^2 := Nat.pow_le_pow_left hks 2
    have : ((k : ℝ)*s)^2 ≤ (n : ℝ)^2 := by exact_mod_cast this
    rw [hnR] at this; linarith [show (x^4)^2 = x^8 by ring]
  have hcubeR : ((k : ℝ)*s)^3 ≤ x^12 := by
    have : ((k*s)^3 : ℕ) ≤ n^3 := Nat.pow_le_pow_left hks 3
    have : ((k : ℝ)*s)^3 ≤ (n : ℝ)^3 := by exact_mod_cast this
    rw [hnR] at this; linarith [show (x^4)^3 = x^12 by ring]
  have hx10 : (0 : ℝ) ≤ x^10 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · push_cast
    have hkey : x^2 ≤ (k : ℝ)*(3/2*x+4) := by nlinarith
    have hmul : (k : ℝ)*((k : ℝ)^2*(s : ℝ)^3) ≤ (k : ℝ)*(3/2*x^11+4*x^10) := by
      calc (k : ℝ)*((k : ℝ)^2*(s : ℝ)^3) = ((k : ℝ)*s)^3 := by ring
        _ ≤ x^12 := hcubeR
        _ = x^10*x^2 := by ring
        _ ≤ x^10*((k : ℝ)*(3/2*x+4)) := mul_le_mul_of_nonneg_left hkey hx10
        _ = (k : ℝ)*(3/2*x^11+4*x^10) := by ring
    exact le_of_mul_le_mul_left hmul (by linarith)
  · push_cast
    have hk3 : (k : ℝ)^3 ≤ 8/27*x^3 := by
      have := pow_le_pow_left₀ (by positivity) hkx 3
      nlinarith
    calc (k : ℝ)^5*(s : ℝ)^2 = (k : ℝ)^3*((k : ℝ)*s)^2 := by ring
      _ ≤ 8/27*x^3*x^8 := mul_le_mul hk3 hsqR (by positivity) (by positivity)
      _ = 8/27*x^11 := by ring
  · push_cast
    have hkey : x^2 ≤ 4*(k : ℝ)^2 := by nlinarith
    have hmul : (k : ℝ)^2*((k : ℝ)*(s : ℝ)^3) ≤ (k : ℝ)^2*(4*x^10) := by
      calc (k : ℝ)^2*((k : ℝ)*(s : ℝ)^3) = ((k : ℝ)*s)^3 := by ring
        _ ≤ x^12 := hcubeR
        _ = x^10*x^2 := by ring
        _ ≤ x^10*(4*(k : ℝ)^2) := mul_le_mul_of_nonneg_left hkey hx10
        _ = (k : ℝ)^2*(4*x^10) := by ring
    exact le_of_mul_le_mul_left hmul (by positivity)
  · have hd : n-k*s < k := by
      have h := Nat.mod_add_div n k
      rw [← hsdef] at h
      have := Nat.mod_lt n (by exact_mod_cast (by linarith : (0 : ℝ) < k) : 0 < k)
      omega
    have hdR : ((n-k*s : ℕ) : ℝ) ≤ x := by
      have : ((n-k*s : ℕ) : ℝ) ≤ k := by exact_mod_cast hd.le
      linarith
    have hA : (0 : ℝ) ≤ 15*(n : ℝ)^2+3002*n+1 := by positivity
    have h9 : 2*x^9 ≤ x^10 := by
      have : 0 ≤ x^9 := by positivity
      nlinarith
    have h5 : 32*x^5 ≤ x^10 := by
      have h25 : (2 : ℝ)^5 ≤ x^5 := pow_le_pow_left₀ (by norm_num) (by linarith) 5
      have : 0 ≤ x^5 := by positivity
      nlinarith
    have h1 : 512*x ≤ x^10 := by
      have h29 : (2 : ℝ)^9 ≤ x^9 := pow_le_pow_left₀ (by norm_num) (by linarith) 9
      nlinarith
    push_cast
    calc (15*(n : ℝ)^2+3002*n+1)*((n-k*s : ℕ) : ℝ) ≤ (15*(n : ℝ)^2+3002*n+1)*x :=
          mul_le_mul_of_nonneg_left hdR hA
      _ = 15*x^9+3002*x^5+x := by rw [hnR]; ring
      _ ≤ 103*x^10 := by nlinarith

/-- An explicit two-term bound on OPT, uniform in the input board. -/
theorem optimalLength_le_explicit {n : ℕ} [NeZero n]
    (hn : 12^4 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ)+
      23.46*Real.rpow (n : ℝ) (11/4 : ℝ)+156504*Real.rpow (n : ℝ) (5/2 : ℝ) := by
  obtain ⟨k,hk,hlo,hhi⟩ := exists_scaled_dimension 16 81 (by norm_num) (by omega) (n := n)
  have hnat := optimalLength_le_of_residual B hk (by linarith)
  have hreal : 2*(optimalLength B : ℝ) ≤ 2*(manhattan B.val : ℝ)+
      21*((k^2*(n/k)^3 : ℕ) : ℝ)+52*((k^5*(n/k)^2 : ℕ) : ℝ)+78128*((k*(n/k)^3 : ℕ) : ℝ)+
      4*(((15*n^2+3002*n+1)*(n-k*(n/k)) : ℕ) : ℝ) := by exact_mod_cast hnat
  obtain ⟨ha, hb, hc, hd⟩ := residual_terms hn hlo hhi
  obtain ⟨hx0, -, h11, h10⟩ := quarter_facts n
  rw [← h11, ← h10]
  have : (0 : ℝ) ≤ (Real.rpow (n : ℝ) (1/4 : ℝ))^11 := by positivity
  linarith

/-- The explicit bound as a legal solution: inefficiency at most
`11.73*n^(11/4) + 78252*n^(5/2)` for every `n ≥ 12⁴`. -/
theorem exists_solution_explicit {n : ℕ} [NeZero n]
    (hn : 12^4 ≤ n) (B : ReachableBoard n) :
    ∃ p : Path B.val (target n),
      (p.inefficientMoves : ℝ) ≤ 11.73*Real.rpow (n : ℝ) (11/4 : ℝ)+
        78252*Real.rpow (n : ℝ) (5/2 : ℝ) ∧
      (p.length : ℝ) ≤ (manhattan B.val : ℝ)+23.46*Real.rpow (n : ℝ) (11/4 : ℝ)+
        156504*Real.rpow (n : ℝ) (5/2 : ℝ) := by
  obtain ⟨p,hp⟩ := shortest_witness B
  have hlength := optimalLength_le_explicit hn B
  rw [← hp] at hlength
  refine ⟨p,?_,hlength⟩
  have hbalance : (p.length : ℝ)=(manhattan B.val : ℝ)+2*(p.inefficientMoves : ℝ) := by
    exact_mod_cast p.solution_length
  have : (0 : ℝ) ≤ Real.rpow (n : ℝ) (11/4 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  linarith

end SlidingPuzzle.Algorithm
