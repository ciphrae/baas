import SlidingPuzzle.Algorithm.GeneralSize
import SlidingPuzzle.DistanceEstimates

/-! # Two levels: the explicit bound as the local solver of Finish

Finish solves `k²` squares of side `s` with a local solver. The one-level
algorithm is such a solver, with inefficiency `O(s^(11/4))` (`recursiveSolver`).
Charging the whole suffix by inefficiency
(`exists_admissible_solution_of_solver_ineff`), Finish contributes only
`O(k²s^(11/4))`, and twice the inefficiency is
`10*k²s³ + 26*k⁵s² + O(k*s³) + O(k²s^(11/4))`: Transport alone remains in the
`k²s³` term.

With `y = n^(1/16)`, `x = y⁴ = n^(1/4)`, `k = ⌊3x/5⌋` and `s = ⌊n/k⌋`:

* `k²s³ ≤ (5/3)x¹¹ + 4x¹⁰`, `k⁵s² ≤ (27/125)x¹¹`, `k*s³ ≤ 4x¹⁰`;
* `s ≥ x³`, so `s^(1/4) ≥ y³` and `k²s^(11/4) ≤ k²s³/y³ ≤ 2y⁴¹`.

The factor `3/5` is close to the minimizer `(10/78)^(1/4) ≈ 0.598` of
`10/c + 26c³`. For every `n ≥ 36⁴`,

```text
inefficiency ≤ 11.145*n^(11/4) + 179701*n^(41/16)      (exists_solution_two_level)
```

The remainder exponent `41/16` comes from the inner level's `s^(11/4)`. -/
namespace SlidingPuzzle.Algorithm
open SlidingPuzzle.Partition

/-- The cost of the one-level algorithm on a board of side `m`, and of the
Parberry solver below the explicit bound's threshold. -/
noncomputable def recursiveCost (m : ℕ) : ℕ :=
  if 12^4 ≤ m then
    m^3+⌈30.21*Real.rpow (m : ℝ) (11/4 : ℝ)+117722*Real.rpow (m : ℝ) (5/2 : ℝ)⌉₊
  else 5*m^3+1509*m^2+1505*m+4796

/-- The inefficiency of the one-level algorithm on a board of side `m`. -/
noncomputable def recursiveIneff (m : ℕ) : ℕ :=
  if 12^4 ≤ m then
    ⌈15.11*Real.rpow (m : ℝ) (11/4 : ℝ)+58861*Real.rpow (m : ℝ) (5/2 : ℝ)⌉₊
  else 5*m^3+1509*m^2+1505*m+4796

theorem recursiveSolver : SolverBound recursiveCost recursiveIneff := by
  intro m _ hm B
  by_cases h : 12^4 ≤ m
  · obtain ⟨p,hpi,hpl⟩ := exists_solution_explicit h B
    refine ⟨p,?_,?_⟩
    · unfold recursiveCost
      rw [if_pos h]
      have h2 := manhattan_le_cube_real B.val
      have h3 := Nat.le_ceil (30.21*Real.rpow (m : ℝ) (11/4 : ℝ)+
        117722*Real.rpow (m : ℝ) (5/2 : ℝ))
      have : (p.length : ℝ) ≤ ((m^3+⌈30.21*Real.rpow (m : ℝ) (11/4 : ℝ)+
          117722*Real.rpow (m : ℝ) (5/2 : ℝ)⌉₊ : ℕ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast this
    · unfold recursiveIneff
      rw [if_pos h]
      exact_mod_cast hpi.trans (Nat.le_ceil _)
  · obtain ⟨q,hq,hqi⟩ := parberrySolverCost hm B
    refine ⟨q,?_,?_⟩
    · unfold recursiveCost; rw [if_neg h]; exact hq
    · unfold recursiveIneff; rw [if_neg h]; exact hqi

/-- Prefix and residual combined, with the recursive Finish solver. -/
theorem optimalLength_le_of_residual_two_level {n k : ℕ} [NeZero n]
    (B : ReachableBoard n) (hk : 2 ≤ k) (hlo : k^4 ≤ n) :
    optimalLength B ≤ manhattan B.val + 10*(k^2*(n/k)^3)+26*(k^5*(n/k)^2)+
      30912*(k*(n/k)^3)+2*(k^2*recursiveIneff (n/k)) +
      2*((15*n^2+3002*n+1)*(n-k*(n/k))) := by
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
  obtain ⟨q,hq⟩ := exists_admissible_solution_of_solver_ineff recursiveSolver hdims A hreachA
  rw [hside] at hq
  have hq' : q.length ≤ manhattan A+(10*(k^2*(n/k)^3)+26*(k^5*(n/k)^2)+30912*(k*(n/k)^3)+
      2*(k^2*recursiveIneff (n/k))) := by
    omega
  have h := optimalLength_le_prefix_residual_solution B (n-k*(n/k)) hd C p hC A hA q hq'
  omega

/-- The sixteenth root of `n`, with `y¹⁶ = n`. -/
private theorem sixteenth_facts (n : ℕ) :
    0 ≤ Real.rpow (n : ℝ) (1/16 : ℝ) ∧ (Real.rpow (n : ℝ) (1/16 : ℝ))^16 = (n : ℝ) ∧
      (Real.rpow (n : ℝ) (1/16 : ℝ))^44 = Real.rpow (n : ℝ) (11/4 : ℝ) ∧
      (Real.rpow (n : ℝ) (1/16 : ℝ))^41 = Real.rpow (n : ℝ) (41/16 : ℝ) := by
  refine ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _, ?_, ?_, ?_⟩
  · simpa using Real.rpow_inv_natCast_pow (Nat.cast_nonneg n) (by norm_num : (16 : ℕ) ≠ 0)
  · convert (Real.rpow_mul_natCast (Nat.cast_nonneg n) (1/16 : ℝ) 44).symm using 1 <;> norm_num
  · convert (Real.rpow_mul_natCast (Nat.cast_nonneg n) (1/16 : ℝ) 41).symm using 1 <;> norm_num

/-- The quarter power of `m`, with `t⁴ = m`. -/
private theorem quarter_facts' (m : ℕ) :
    0 ≤ Real.rpow (m : ℝ) (1/4 : ℝ) ∧ (Real.rpow (m : ℝ) (1/4 : ℝ))^4 = (m : ℝ) ∧
      (Real.rpow (m : ℝ) (1/4 : ℝ))^11 = Real.rpow (m : ℝ) (11/4 : ℝ) ∧
      (Real.rpow (m : ℝ) (1/4 : ℝ))^10 = Real.rpow (m : ℝ) (5/2 : ℝ) := by
  refine ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _, ?_, ?_, ?_⟩
  · simpa using Real.rpow_inv_natCast_pow (Nat.cast_nonneg m) (by norm_num : (4 : ℕ) ≠ 0)
  · convert (Real.rpow_mul_natCast (Nat.cast_nonneg m) (1/4 : ℝ) 11).symm using 1 <;> norm_num
  · convert (Real.rpow_mul_natCast (Nat.cast_nonneg m) (1/4 : ℝ) 10).symm using 1 <;> norm_num

set_option maxHeartbeats 1000000 in
/-- The cost terms in powers of `y = n^(1/16)`. -/
private theorem two_level_terms {n k : ℕ} (hn : 36^4 ≤ n) (hlo : 625*k^4 ≤ 81*n)
    (hhi : 81*n < 625*(k+1)^4) :
    let y := Real.rpow (n : ℝ) (1/16 : ℝ)
    ((k^2*(n/k)^3 : ℕ) : ℝ) ≤ 5/3*y^44+4*y^40 ∧
      ((k^5*(n/k)^2 : ℕ) : ℝ) ≤ 27/125*y^44 ∧ ((k*(n/k)^3 : ℕ) : ℝ) ≤ 4*y^40 ∧
      (((15*n^2+3002*n+1)*(n-k*(n/k)) : ℕ) : ℝ) ≤ 103*y^40 ∧
      ((k^2*recursiveIneff (n/k) : ℕ) : ℝ) ≤ 117754*y^41 := by
  intro y
  obtain ⟨hy0, hy16, -, -⟩ := sixteenth_facts n
  change 0 ≤ y at hy0
  change y^16 = n at hy16
  set x := y^4 with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hnR : (n : ℝ) = x^4 := by rw [hxdef, ← hy16]; ring
  clear_value x y
  have hkx : 5*(k : ℝ) ≤ 3*x := by
    have h : (5*(k : ℝ))^4 ≤ (3*x)^4 := by
      have : (625*(k : ℝ)^4) ≤ 81*n := by exact_mod_cast hlo
      rw [hnR] at this; nlinarith
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h
  have hxk : 3*x < 5*((k : ℝ)+1) := by
    have h : (3*x)^4 < (5*((k : ℝ)+1))^4 := by
      have : 81*(n : ℝ) < 625*((k : ℝ)+1)^4 := by exact_mod_cast hhi
      rw [hnR] at this; nlinarith
    exact lt_of_pow_lt_pow_left₀ 4 (by positivity) h
  have hx25 : (36 : ℝ) ≤ x := by
    have h : (36 : ℝ)^4 ≤ x^4 := by rw [← hnR]; exact_mod_cast hn
    exact le_of_pow_le_pow_left₀ (by norm_num) hx0 h
  have hy1 : (1 : ℝ) ≤ y := by
    by_contra h
    push Not at h
    have : y^4 < 1 := pow_lt_one₀ hy0 h (by norm_num)
    linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hxk2 : x ≤ 2*(k : ℝ) := by linarith
  have hk1 : (1 : ℝ) ≤ k := by linarith
  have hkpos : 0 < k := by exact_mod_cast (by linarith : (0 : ℝ) < k)
  set s := n/k with hsdef
  have hks : k*s ≤ n := Nat.mul_div_le n k
  have hks1 : n < k*(s+1) := by
    have h := Nat.lt_mul_div_succ n hkpos
    rw [← hsdef] at h; linarith
  have hsqR : ((k : ℝ)*s)^2 ≤ x^8 := by
    have : ((k*s)^2 : ℕ) ≤ n^2 := Nat.pow_le_pow_left hks 2
    have : ((k : ℝ)*s)^2 ≤ (n : ℝ)^2 := by exact_mod_cast this
    rw [hnR] at this; linarith [show (x^4)^2 = x^8 by ring]
  have hcubeR : ((k : ℝ)*s)^3 ≤ x^12 := by
    have : ((k*s)^3 : ℕ) ≤ n^3 := Nat.pow_le_pow_left hks 3
    have : ((k : ℝ)*s)^3 ≤ (n : ℝ)^3 := by exact_mod_cast this
    rw [hnR] at this; linarith [show (x^4)^3 = x^12 by ring]
  have hx10 : (0 : ℝ) ≤ x^10 := by positivity
  have hx40 : x^10 = y^40 := by rw [hxdef]; ring
  have hx44 : x^11 = y^44 := by rw [hxdef]; ring
  -- `k²s³` and `k*s³`.
  have ha : (k : ℝ)^2*(s : ℝ)^3 ≤ 5/3*x^11+4*x^10 := by
    have hkey : x^2 ≤ (k : ℝ)*(5/3*x+4) := by nlinarith
    have hmul : (k : ℝ)*((k : ℝ)^2*(s : ℝ)^3) ≤ (k : ℝ)*(5/3*x^11+4*x^10) := by
      calc (k : ℝ)*((k : ℝ)^2*(s : ℝ)^3) = ((k : ℝ)*s)^3 := by ring
        _ ≤ x^12 := hcubeR
        _ = x^10*x^2 := by ring
        _ ≤ x^10*((k : ℝ)*(5/3*x+4)) := mul_le_mul_of_nonneg_left hkey hx10
        _ = (k : ℝ)*(5/3*x^11+4*x^10) := by ring
    exact le_of_mul_le_mul_left hmul (by linarith)
  have hc : (k : ℝ)*(s : ℝ)^3 ≤ 4*x^10 := by
    have hkey : x^2 ≤ 4*(k : ℝ)^2 := by nlinarith
    have hmul : (k : ℝ)^2*((k : ℝ)*(s : ℝ)^3) ≤ (k : ℝ)^2*(4*x^10) := by
      calc (k : ℝ)^2*((k : ℝ)*(s : ℝ)^3) = ((k : ℝ)*s)^3 := by ring
        _ ≤ x^12 := hcubeR
        _ = x^10*x^2 := by ring
        _ ≤ x^10*(4*(k : ℝ)^2) := mul_le_mul_of_nonneg_left hkey hx10
        _ = (k : ℝ)^2*(4*x^10) := by ring
    exact le_of_mul_le_mul_left hmul (by positivity)
  -- The side is large: `s ≥ x³ ≥ 10000`.
  have hsx : x^3 ≤ (s : ℝ) := by
    have h1 : (n : ℝ) < k*((s : ℝ)+1) := by exact_mod_cast hks1
    rw [hnR] at h1
    have h2 : x^4 ≤ (3/5*x)*((s : ℝ)+1) := by nlinarith
    have hx3 : 1 ≤ x^3/20 := by
      have : (36 : ℝ)^3 ≤ x^3 := pow_le_pow_left₀ (by norm_num) hx25 3
      linarith
    nlinarith
  have hs10 : 12^4 ≤ s := by
    have : (36 : ℝ)^3 ≤ x^3 := pow_le_pow_left₀ (by norm_num) hx25 3
    have : (20736 : ℝ) ≤ s := by linarith
    exact_mod_cast this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · push_cast; rw [← hx40, ← hx44]; exact ha
  · push_cast
    have hk3 : (k : ℝ)^3 ≤ 27/125*x^3 := by
      have := pow_le_pow_left₀ (by positivity) hkx 3
      nlinarith
    calc (k : ℝ)^5*(s : ℝ)^2 = (k : ℝ)^3*((k : ℝ)*s)^2 := by ring
      _ ≤ 27/125*x^3*x^8 := mul_le_mul hk3 hsqR (by positivity) (by positivity)
      _ = 27/125*y^44 := by rw [← hx44]; ring
  · push_cast; rw [← hx40]; exact hc
  · have hd : n-k*s < k := by
      have h := Nat.mod_add_div n k
      rw [← hsdef] at h
      have := Nat.mod_lt n hkpos
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
    rw [← hx40]
    calc (15*(n : ℝ)^2+3002*n+1)*((n-k*s : ℕ) : ℝ) ≤ (15*(n : ℝ)^2+3002*n+1)*x :=
          mul_le_mul_of_nonneg_left hdR hA
      _ = 15*x^9+3002*x^5+x := by rw [hnR]; ring
      _ ≤ 103*x^10 := by nlinarith
  · -- The inner level's remainder.
    have hcost : (recursiveIneff s : ℝ) ≤ 15.11*Real.rpow (s : ℝ) (11/4 : ℝ)+
        58861*Real.rpow (s : ℝ) (5/2 : ℝ)+1 := by
      unfold recursiveIneff
      rw [if_pos hs10]
      have := Nat.ceil_lt_add_one (show 0 ≤ 15.11*Real.rpow (s : ℝ) (11/4 : ℝ)+
        58861*Real.rpow (s : ℝ) (5/2 : ℝ) by
          have := Real.rpow_nonneg (Nat.cast_nonneg s) (11/4 : ℝ)
          have := Real.rpow_nonneg (Nat.cast_nonneg s) (5/2 : ℝ)
          positivity)
      push_cast
      linarith
    obtain ⟨ht0, ht4, ht11, ht10⟩ := quarter_facts' s
    rw [← ht11, ← ht10] at hcost
    generalize Real.rpow (s : ℝ) (1/4 : ℝ) = t at ht0 ht4 hcost
    have hty : y^3 ≤ t := by
      have h : (y^3)^4 ≤ t^4 := by
        rw [ht4]
        calc ((y^3)^4 : ℝ) = x^3 := by rw [hxdef]; ring
          _ ≤ (s : ℝ) := hsx
      exact le_of_pow_le_pow_left₀ (by norm_num) ht0 h
    have hk2s3 : (k : ℝ)^2*t^12 ≤ 2*y^44 := by
      have h1 : t^12 = (s : ℝ)^3 := by rw [← ht4]; ring
      have h2 : 4*x^10 ≤ 1/3*x^11 := by
        have h3 : x^10*4 ≤ x^10*(1/3*x) := mul_le_mul_of_nonneg_left (by linarith) hx10
        linarith [show x^10*(1/3*x) = 1/3*x^11 by ring]
      rw [h1, ← hx44]
      linarith
    have hy3 : 0 < y^3 := by positivity
    have hA : (k : ℝ)^2*t^11 ≤ 2*y^41 := by
      have h1 : (k : ℝ)^2*t^11*y^3 ≤ (k : ℝ)^2*t^11*t :=
        mul_le_mul_of_nonneg_left hty (by positivity)
      have h2 : (k : ℝ)^2*t^11*t ≤ 2*y^41*y^3 := by
        calc (k : ℝ)^2*t^11*t = (k : ℝ)^2*t^12 := by ring
          _ ≤ 2*y^44 := hk2s3
          _ = 2*y^41*y^3 := by ring
      exact le_of_mul_le_mul_right (h1.trans h2) hy3
    have hB : (k : ℝ)^2*t^10 ≤ 2*y^41 := by
      have hy6 : 0 < y^6 := by positivity
      have h1 : (k : ℝ)^2*t^10*y^6 ≤ (k : ℝ)^2*t^10*t^2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc y^6 = (y^3)^2 := by ring
          _ ≤ t^2 := pow_le_pow_left₀ (by positivity) hty 2
      have h2 : (k : ℝ)^2*t^10*t^2 ≤ 2*y^41*y^6 := by
        have : y^44 ≤ y^47 := pow_le_pow_right₀ hy1 (by norm_num)
        calc (k : ℝ)^2*t^10*t^2 = (k : ℝ)^2*t^12 := by ring
          _ ≤ 2*y^44 := hk2s3
          _ ≤ 2*y^47 := by linarith
          _ = 2*y^41*y^6 := by ring
      exact le_of_mul_le_mul_right (h1.trans h2) hy6
    have hC : (k : ℝ)^2 ≤ y^41 := by
      have : (k : ℝ)^2 ≤ x^2 := pow_le_pow_left₀ hk0 (by linarith) 2
      have : x^2 ≤ y^41 := by
        rw [hxdef]
        calc (y^4)^2 = y^8 := by ring
          _ ≤ y^41 := pow_le_pow_right₀ hy1 (by norm_num)
      linarith
    rw [Nat.cast_mul, Nat.cast_pow]
    have hk2 : (0 : ℝ) ≤ (k : ℝ)^2 := by positivity
    calc (k : ℝ)^2*(recursiveIneff s : ℝ) ≤ (k : ℝ)^2*(15.11*t^11+58861*t^10+1) :=
          mul_le_mul_of_nonneg_left hcost hk2
      _ = 15.11*((k : ℝ)^2*t^11)+58861*((k : ℝ)^2*t^10)+(k : ℝ)^2 := by ring
      _ ≤ 117754*y^41 := by
          have hy41 : (0 : ℝ) ≤ y^41 := by positivity
          have e : (15.11 : ℝ) = 1511/100 := by norm_num
          rw [e]
          linarith only [hA, hB, hC, hy41]

/-- An explicit bound on OPT with the recursive Finish solver. -/
theorem optimalLength_le_two_level {n : ℕ} [NeZero n]
    (hn : 36^4 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ)+
      22.29*Real.rpow (n : ℝ) (11/4 : ℝ)+359402*Real.rpow (n : ℝ) (41/16 : ℝ) := by
  obtain ⟨k,hk,hlo,hhi⟩ := exists_scaled_dimension 81 625 (by norm_num) (by omega)
    (n := n)
  have hnat := optimalLength_le_of_residual_two_level B hk (by linarith)
  have hreal : (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ)+
      10*((k^2*(n/k)^3 : ℕ) : ℝ)+26*((k^5*(n/k)^2 : ℕ) : ℝ)+30912*((k*(n/k)^3 : ℕ) : ℝ)+
      2*((k^2*recursiveIneff (n/k) : ℕ) : ℝ)+
      2*(((15*n^2+3002*n+1)*(n-k*(n/k)) : ℕ) : ℝ) := by exact_mod_cast hnat
  obtain ⟨ha, hb, hc, hd, he⟩ := two_level_terms hn hlo hhi
  obtain ⟨hy0, -, h44, h41⟩ := sixteenth_facts n
  rw [← h44, ← h41]
  set y := Real.rpow (n : ℝ) (1/16 : ℝ)
  have hy1 : 1 ≤ y := by
    by_contra h
    push Not at h
    have h16 : y^16 < 1 := pow_lt_one₀ hy0 h (by norm_num)
    have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have := (sixteenth_facts n).2.1
    linarith
  have h40 : y^40 ≤ y^41 := pow_le_pow_right₀ hy1 (by norm_num)
  have : (0 : ℝ) ≤ y^44 := by positivity
  nlinarith

/-- The two-level bound as a legal solution: inefficiency at most
`11.145*n^(11/4) + 179701*n^(41/16)` for every `n ≥ 36⁴`. -/
theorem exists_solution_two_level {n : ℕ} [NeZero n]
    (hn : 36^4 ≤ n) (B : ReachableBoard n) :
    ∃ p : Path B.val (target n),
      (p.inefficientMoves : ℝ) ≤ 11.145*Real.rpow (n : ℝ) (11/4 : ℝ)+
        179701*Real.rpow (n : ℝ) (41/16 : ℝ) ∧
      (p.length : ℝ) ≤ (manhattan B.val : ℝ)+22.29*Real.rpow (n : ℝ) (11/4 : ℝ)+
        359402*Real.rpow (n : ℝ) (41/16 : ℝ) := by
  obtain ⟨p,hp⟩ := shortest_witness B
  have hlength := optimalLength_le_two_level hn B
  rw [← hp] at hlength
  refine ⟨p,?_,hlength⟩
  have hbalance : (p.length : ℝ)=(manhattan B.val : ℝ)+2*(p.inefficientMoves : ℝ) := by
    exact_mod_cast p.solution_length
  linarith

/-- `R*n^(41/16) ≤ n^(11/4)` once `R¹⁶ ≤ n³`. -/
theorem sixteenth_gap_absorb (R n : ℕ) (hn : R^16 ≤ n^3) :
    (R : ℝ)*Real.rpow (n : ℝ) (41/16 : ℝ) ≤ Real.rpow (n : ℝ) (11/4 : ℝ) := by
  obtain ⟨hy0, hy16, h44, h41⟩ := sixteenth_facts n
  set y := Real.rpow (n : ℝ) (1/16 : ℝ)
  have hR : (R : ℝ) ≤ y^3 := by
    have h : (R : ℝ)^16 ≤ (y^3)^16 := by
      calc (R : ℝ)^16 ≤ (n : ℝ)^3 := by exact_mod_cast hn
        _ = (y^16)^3 := by rw [hy16]
        _ = (y^3)^16 := by ring
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h
  rw [← h44, ← h41]
  calc (R : ℝ)*y^41 ≤ y^3*y^41 := mul_le_mul_of_nonneg_right hR (by positivity)
    _ = y^44 := by ring

/-- For large `n`, `OPT ≤ M + 23.29*n^(11/4)`. The threshold is not optimized. -/
theorem optimalLength_le_eventually_two_level {n : ℕ} [NeZero n]
    (hn : 359402^6 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ)+23.29*Real.rpow (n : ℝ) (11/4 : ℝ) := by
  have h := optimalLength_le_two_level (le_trans (by norm_num) hn) B
  have hr := sixteenth_gap_absorb 359402 n (by
    calc 359402^16 ≤ (359402^6)^3 := by norm_num
      _ ≤ n^3 := Nat.pow_le_pow_left hn 3)
  norm_num only [Nat.cast_ofNat] at hr
  linarith

/-- The boardwise bound required by Proposition 9. -/
theorem uniformApproximation : UniformApproximation := by
  refine ⟨23.29,by norm_num,359402^6,?_⟩
  intro n hn hn2
  letI : NeZero n := ⟨by omega⟩
  intro B
  exact optimalLength_le_eventually_two_level hn B

end SlidingPuzzle.Algorithm
