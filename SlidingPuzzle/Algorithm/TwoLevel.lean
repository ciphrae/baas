import SlidingPuzzle.Algorithm.GeneralSize
import SlidingPuzzle.DistanceEstimates

/-! # Two levels: the explicit bound as the local solver of Finish

Finish solves `k²` squares of side `s` with a local solver whose cost must hold
for every board of side `s`. Since every board has `M ≤ s³`
(`manhattan_le_cube`), the one-level bound `optimalLength_le_explicit` is such a
solver with cost `s³ + O(s^(11/4))`, against `5*s³ + O(s²)` for the Parberry
solver. Finish then contributes `k²s³` instead of `5*k²s³` to twice the
inefficiency, which becomes `13*k²s³ + 47*k⁵s² + O(k*s³) + O(k²s^(11/4))`.

With `y = n^(1/16)`, `x = y⁴ = n^(1/4)`, `k = ⌊11x/20⌋` and `s = ⌊n/k⌋`:

* `k²s³ ≤ (20/11)x¹¹ + 4x¹⁰`, `k⁵s² ≤ (1331/8000)x¹¹`, `k*s³ ≤ 4x¹⁰`;
* `s ≥ x³`, so `s^(1/4) ≥ y³` and `k²s^(11/4) ≤ k²s³/y³ ≤ 2y⁴¹`.

The factor `11/20` is close to the minimizer `(13/141)^(1/4) ≈ 0.551` of
`13/c + 47c³`. For every `n ≥ 25⁴`,

```text
inefficiency ≤ 15.73*n^(11/4) + 158375*n^(41/16)      (exists_solution_two_level)
```

The remainder exponent `41/16` comes from the inner level's `s^(11/4)`. -/
namespace SlidingPuzzle.Algorithm
open SlidingPuzzle.Partition

/-- The cost of the one-level algorithm on a board of side `m`, and of the
Parberry solver below the explicit bound's threshold. -/
noncomputable def recursiveCost (m : ℕ) : ℕ :=
  if 10000 ≤ m then
    m^3+⌈38.49*Real.rpow (m : ℝ) (11/4 : ℝ)+125330*Real.rpow (m : ℝ) (5/2 : ℝ)⌉₊
  else 5*m^3+1509*m^2+1505*m+4796

theorem recursiveSolverCost : SolverCostBound recursiveCost := by
  intro m _ hm B
  obtain ⟨p,hp⟩ := shortest_witness B
  refine ⟨p,?_⟩
  unfold recursiveCost
  split_ifs with h
  · have h1 := optimalLength_le_explicit h B
    have h2 := manhattan_le_cube_real B.val
    have h3 := Nat.le_ceil (38.49*Real.rpow (m : ℝ) (11/4 : ℝ)+
      125330*Real.rpow (m : ℝ) (5/2 : ℝ))
    rw [← hp] at h1
    have : (p.length : ℝ) ≤ ((m^3+⌈38.49*Real.rpow (m : ℝ) (11/4 : ℝ)+
        125330*Real.rpow (m : ℝ) (5/2 : ℝ)⌉₊ : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  · obtain ⟨q,hq⟩ := parberrySolverCost hm B
    rw [hp]
    exact (optimalLength_le_path_length B q).trans hq

/-- Prefix and residual combined, with the recursive Finish solver. -/
theorem optimalLength_le_of_residual_two_level {n k : ℕ} [NeZero n]
    (B : ReachableBoard n) (hk : 2 ≤ k) (hlo : k^4 ≤ n) :
    optimalLength B ≤ manhattan B.val + 12*(k^2*(n/k)^3)+47*(k^5*(n/k)^2)+
      14100*(k*(n/k)^3)+(k^2*recursiveCost (n/k)+9354*k^2*(k*(n/k))) +
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
  obtain ⟨q,hq⟩ := exists_admissible_solution_of_solver recursiveSolverCost hdims A hreachA
  rw [hside] at hq
  have hq' : q.length ≤ manhattan A+(12*(k^2*(n/k)^3)+47*(k^5*(n/k)^2)+14100*(k*(n/k)^3)+
      (k^2*recursiveCost (n/k)+9354*k^2*(k*(n/k)))) := by
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
private theorem two_level_terms {n k : ℕ} (hn : 25^4 ≤ n) (hlo : 160000*k^4 ≤ 14641*n)
    (hhi : 14641*n < 160000*(k+1)^4) :
    let y := Real.rpow (n : ℝ) (1/16 : ℝ)
    ((k^2*(n/k)^3 : ℕ) : ℝ) ≤ 20/11*y^44+4*y^40 ∧
      ((k^5*(n/k)^2 : ℕ) : ℝ) ≤ 1331/8000*y^44 ∧ ((k*(n/k)^3 : ℕ) : ℝ) ≤ 4*y^40 ∧
      (((15*n^2+3002*n+1)*(n-k*(n/k)) : ℕ) : ℝ) ≤ 103*y^40 ∧
      ((k^2*recursiveCost (n/k) : ℕ) : ℝ) ≤ ((k^2*(n/k)^3 : ℕ) : ℝ)+250738*y^41 ∧
      ((9354*k^2*(k*(n/k)) : ℕ) : ℝ) ≤ 9354*y^40 := by
  intro y
  obtain ⟨hy0, hy16, -, -⟩ := sixteenth_facts n
  change 0 ≤ y at hy0
  change y^16 = n at hy16
  set x := y^4 with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hnR : (n : ℝ) = x^4 := by rw [hxdef, ← hy16]; ring
  clear_value x y
  have hkx : 20*(k : ℝ) ≤ 11*x := by
    have h : (20*(k : ℝ))^4 ≤ (11*x)^4 := by
      have : (160000*(k : ℝ)^4) ≤ 14641*n := by exact_mod_cast hlo
      rw [hnR] at this; nlinarith
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h
  have hxk : 11*x < 20*((k : ℝ)+1) := by
    have h : (11*x)^4 < (20*((k : ℝ)+1))^4 := by
      have : 14641*(n : ℝ) < 160000*((k : ℝ)+1)^4 := by exact_mod_cast hhi
      rw [hnR] at this; nlinarith
    exact lt_of_pow_lt_pow_left₀ 4 (by positivity) h
  have hx25 : (25 : ℝ) ≤ x := by
    have h : (25 : ℝ)^4 ≤ x^4 := by rw [← hnR]; exact_mod_cast hn
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
  have ha : (k : ℝ)^2*(s : ℝ)^3 ≤ 20/11*x^11+4*x^10 := by
    have hkey : x^2 ≤ (k : ℝ)*(20/11*x+4) := by nlinarith
    have hmul : (k : ℝ)*((k : ℝ)^2*(s : ℝ)^3) ≤ (k : ℝ)*(20/11*x^11+4*x^10) := by
      calc (k : ℝ)*((k : ℝ)^2*(s : ℝ)^3) = ((k : ℝ)*s)^3 := by ring
        _ ≤ x^12 := hcubeR
        _ = x^10*x^2 := by ring
        _ ≤ x^10*((k : ℝ)*(20/11*x+4)) := mul_le_mul_of_nonneg_left hkey hx10
        _ = (k : ℝ)*(20/11*x^11+4*x^10) := by ring
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
    have h2 : x^4 ≤ (11/20*x)*((s : ℝ)+1) := by nlinarith
    have hx3 : 1 ≤ x^3/20 := by
      have : (25 : ℝ)^3 ≤ x^3 := pow_le_pow_left₀ (by norm_num) hx25 3
      linarith
    nlinarith
  have hs10 : 10000 ≤ s := by
    have : (25 : ℝ)^3 ≤ x^3 := pow_le_pow_left₀ (by norm_num) hx25 3
    have : (10000 : ℝ) ≤ s := by linarith
    exact_mod_cast this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · push_cast; rw [← hx40, ← hx44]; exact ha
  · push_cast
    have hk3 : (k : ℝ)^3 ≤ 1331/8000*x^3 := by
      have := pow_le_pow_left₀ (by positivity) hkx 3
      nlinarith
    calc (k : ℝ)^5*(s : ℝ)^2 = (k : ℝ)^3*((k : ℝ)*s)^2 := by ring
      _ ≤ 1331/8000*x^3*x^8 := mul_le_mul hk3 hsqR (by positivity) (by positivity)
      _ = 1331/8000*y^44 := by rw [← hx44]; ring
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
    have hcost : (recursiveCost s : ℝ) ≤ (s : ℝ)^3+(38.49*Real.rpow (s : ℝ) (11/4 : ℝ)+
        125330*Real.rpow (s : ℝ) (5/2 : ℝ)+1) := by
      unfold recursiveCost
      rw [if_pos hs10]
      have := Nat.ceil_lt_add_one (show 0 ≤ 38.49*Real.rpow (s : ℝ) (11/4 : ℝ)+
        125330*Real.rpow (s : ℝ) (5/2 : ℝ) by
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
      have h2 : 4*x^10 ≤ 2/11*x^11 := by
        have h3 : x^10*4 ≤ x^10*(2/11*x) := mul_le_mul_of_nonneg_left (by linarith) hx10
        linarith [show x^10*(2/11*x) = 2/11*x^11 by ring]
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
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
    have hk2 : (0 : ℝ) ≤ (k : ℝ)^2 := by positivity
    calc (k : ℝ)^2*(recursiveCost s : ℝ) ≤ (k : ℝ)^2*((s : ℝ)^3+(38.49*t^11+125330*t^10+1)) :=
          mul_le_mul_of_nonneg_left hcost hk2
      _ = (k : ℝ)^2*(s : ℝ)^3+(38.49*((k : ℝ)^2*t^11)+125330*((k : ℝ)^2*t^10)+(k : ℝ)^2) := by
          ring
      _ ≤ (k : ℝ)^2*(s : ℝ)^3+250738*y^41 := by
          have hy41 : (0 : ℝ) ≤ y^41 := by positivity
          linarith only [hA, hB, hC, hy41]
  · push_cast
    have : (k : ℝ)^2*((k : ℝ)*s) ≤ y^40 := by
      have h1 : (k : ℝ)*s ≤ x^4 := by
        have : ((k*s : ℕ) : ℝ) ≤ n := by exact_mod_cast hks
        push_cast at this; linarith
      have h2 : (k : ℝ)^2 ≤ x^2 := pow_le_pow_left₀ hk0 (by linarith) 2
      calc (k : ℝ)^2*((k : ℝ)*s) ≤ x^2*x^4 := mul_le_mul h2 h1 (by positivity) (by positivity)
        _ = y^24 := by rw [hxdef]; ring
        _ ≤ y^40 := pow_le_pow_right₀ hy1 (by norm_num)
    linarith

/-- An explicit bound on OPT with the recursive Finish solver. -/
theorem optimalLength_le_two_level {n : ℕ} [NeZero n]
    (hn : 25^4 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ)+
      31.46*Real.rpow (n : ℝ) (11/4 : ℝ)+316750*Real.rpow (n : ℝ) (41/16 : ℝ) := by
  obtain ⟨k,hk,hlo,hhi⟩ := exists_scaled_dimension 14641 160000 (by norm_num) (by omega) (n := n)
  have hnat := optimalLength_le_of_residual_two_level B hk (by linarith)
  have hreal : (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ)+
      12*((k^2*(n/k)^3 : ℕ) : ℝ)+47*((k^5*(n/k)^2 : ℕ) : ℝ)+14100*((k*(n/k)^3 : ℕ) : ℝ)+
      (((k^2*recursiveCost (n/k) : ℕ) : ℝ)+((9354*k^2*(k*(n/k)) : ℕ) : ℝ))+
      2*(((15*n^2+3002*n+1)*(n-k*(n/k)) : ℕ) : ℝ) := by exact_mod_cast hnat
  obtain ⟨ha, hb, hc, hd, he, hf⟩ := two_level_terms hn hlo hhi
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
`15.73*n^(11/4) + 158375*n^(41/16)` for every `n ≥ 25⁴`. -/
theorem exists_solution_two_level {n : ℕ} [NeZero n]
    (hn : 25^4 ≤ n) (B : ReachableBoard n) :
    ∃ p : Path B.val (target n),
      (p.inefficientMoves : ℝ) ≤ 15.73*Real.rpow (n : ℝ) (11/4 : ℝ)+
        158375*Real.rpow (n : ℝ) (41/16 : ℝ) ∧
      (p.length : ℝ) ≤ (manhattan B.val : ℝ)+31.46*Real.rpow (n : ℝ) (11/4 : ℝ)+
        316750*Real.rpow (n : ℝ) (41/16 : ℝ) := by
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

/-- For large `n`, `OPT ≤ M + 32.46*n^(11/4)`. The threshold is not optimized. -/
theorem optimalLength_le_eventually_two_level {n : ℕ} [NeZero n]
    (hn : 316750^6 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ)+32.46*Real.rpow (n : ℝ) (11/4 : ℝ) := by
  have h := optimalLength_le_two_level (le_trans (by norm_num) hn) B
  have hr := sixteenth_gap_absorb 316750 n (by
    calc 316750^16 ≤ (316750^6)^3 := by norm_num
      _ ≤ n^3 := Nat.pow_le_pow_left hn 3)
  norm_num only [Nat.cast_ofNat] at hr
  linarith

/-- The boardwise bound required by Proposition 9. -/
theorem uniformApproximation : UniformApproximation := by
  refine ⟨32.46,by norm_num,316750^6,?_⟩
  intro n hn hn2
  letI : NeZero n := ⟨by omega⟩
  intro B
  exact optimalLength_le_eventually_two_level hn B

end SlidingPuzzle.Algorithm
