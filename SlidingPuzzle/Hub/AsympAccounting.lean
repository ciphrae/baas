import SlidingPuzzle.Hub.Transport

/-! # Combined accounting

Keep transport, cleanup and Finish in one polynomial, using capacity before
rounding. Coefficients are in thousandths so the final real bound can
round only once. -/
set_option maxRecDepth 4096

namespace SlidingPuzzle.Hub

/-- Numerators of the coefficients without the logarithm, with denominator `1000`. -/
def hubLinKX : ℕ := 101960
def hubLinKW : ℕ := 367100

set_option maxHeartbeats 1600000 in
/-- Combined accounting against `X = n²s` and `W = k²n²`: the in-flight budget is
linear in `n`, so no logarithm remains. Every lower-order monomial is absorbed
using `k ≥ 50` and `s ≥ 668 k`. -/
theorem hubBound_le_lin {k s : ℕ} (hk : 50 ≤ k) (hcap : 668 * k ≤ s) :
    1000 * hubBound (k * s) k s ≤ hubLinKX * ((k * s) ^ 2 * s) +
      hubLinKW * (k ^ 2 * (k * s) ^ 2) := by
  have hC : sqCorridor k s ≤ 2 * (k * s) := by
    unfold sqCorridor
    have h1 := Nat.mul_le_mul_right s (Nat.sub_le k 1)
    have h2 := Nat.mul_le_mul (Nat.sub_le k 1) (Nat.sub_le s k)
    omega
  have hCcost := Nat.mul_le_mul_left (26000 * (k ^ 3 * s)) hC
  have hRcost := Nat.mul_le_mul_left
    (94000 * k ^ 3 * s + 126000 * k ^ 3 + 18000 * k ^ 2 * s + 54000 * k ^ 2) (Rhub_upper (k * s))
  unfold hubBound transportBound misplacedBound hubLinKX hubLinKW
  generalize Rhub (k * s) = R at *
  generalize sqCorridor k s = C at *
  set Y := 26 * (k * s) * (k ^ 2 * C + (k ^ 2 * (k * s) + k ^ 2 * (R + k ^ 2) +
      k ^ 2 * (R + 8 * (k * s) + 10) + 4 * k ^ 2 * (k * s)) + 2 * (k * s) + 5) +
    (k ^ 2 * (5 * s ^ 3 + 1509 * s ^ 2 + 1505 * s + 4796) + 9354 * k ^ 2 * (k * s)) with hY
  have hdiv : 2 * (Y / 2) ≤ Y := Nat.mul_div_le Y 2
  have hs : 33400 ≤ s := by omega
  -- monomials absorbed into `W = k⁴s²`
  have w1 : 668 * (k ^ 5 * s) ≤ k ^ 4 * s ^ 2 := by
    have := Nat.mul_le_mul_left (k ^ 4 * s) hcap
    calc 668 * (k ^ 5 * s) = k ^ 4 * s * (668 * k) := by ring
      _ ≤ k ^ 4 * s * s := this
      _ = k ^ 4 * s ^ 2 := by ring
  have w2 : 50 * (k ^ 3 * s ^ 2) ≤ k ^ 4 * s ^ 2 := by
    have := Nat.mul_le_mul_left (k ^ 3 * s ^ 2) hk
    calc 50 * (k ^ 3 * s ^ 2) = k ^ 3 * s ^ 2 * 50 := by ring
      _ ≤ k ^ 3 * s ^ 2 * k := this
      _ = k ^ 4 * s ^ 2 := by ring
  have w3 : 50 * (k ^ 2 * s ^ 2) ≤ k ^ 3 * s ^ 2 := by
    have := Nat.mul_le_mul_left (k ^ 2 * s ^ 2) hk
    calc 50 * (k ^ 2 * s ^ 2) = k ^ 2 * s ^ 2 * 50 := by ring
      _ ≤ k ^ 2 * s ^ 2 * k := this
      _ = k ^ 3 * s ^ 2 := by ring
  have w4 : 50 * (k * s ^ 2) ≤ k ^ 2 * s ^ 2 := by
    have := Nat.mul_le_mul_left (k * s ^ 2) hk
    calc 50 * (k * s ^ 2) = k * s ^ 2 * 50 := by ring
      _ ≤ k * s ^ 2 * k := this
      _ = k ^ 2 * s ^ 2 := by ring
  have w5 : 50 * s ^ 2 ≤ k * s ^ 2 := by
    have := Nat.mul_le_mul_left (s ^ 2) hk
    linarith
  have w6 : 33400 * (k ^ 4 * s) ≤ k ^ 4 * s ^ 2 := by
    have := Nat.mul_le_mul_left (k ^ 4 * s) hs
    calc 33400 * (k ^ 4 * s) = k ^ 4 * s * 33400 := by ring
      _ ≤ k ^ 4 * s * s := this
      _ = k ^ 4 * s ^ 2 := by ring
  have w7 : 50 * (k ^ 3 * s) ≤ k ^ 4 * s := by
    have := Nat.mul_le_mul_left (k ^ 3 * s) hk
    calc 50 * (k ^ 3 * s) = k ^ 3 * s * 50 := by ring
      _ ≤ k ^ 3 * s * k := this
      _ = k ^ 4 * s := by ring
  have w8 : 50 * (k ^ 2 * s) ≤ k ^ 3 * s := by
    have := Nat.mul_le_mul_left (k ^ 2 * s) hk
    calc 50 * (k ^ 2 * s) = k ^ 2 * s * 50 := by ring
      _ ≤ k ^ 2 * s * k := this
      _ = k ^ 3 * s := by ring
  have w9 : 50 * (k * s) ≤ k ^ 2 * s := by
    have := Nat.mul_le_mul_left (k * s) hk
    calc 50 * (k * s) = k * s * 50 := by ring
      _ ≤ k * s * k := this
      _ = k ^ 2 * s := by ring
  have w10 : 33400 * k ^ 5 ≤ k ^ 5 * s := by
    have := Nat.mul_le_mul_left (k ^ 5) hs
    linarith
  have w11 : 50 * k ^ 4 ≤ k ^ 5 := by
    have := Nat.mul_le_mul_left (k ^ 4) hk
    calc 50 * k ^ 4 = k ^ 4 * 50 := by ring
      _ ≤ k ^ 4 * k := this
      _ = k ^ 5 := by ring
  have w12 : 50 * k ^ 3 ≤ k ^ 4 := by
    have := Nat.mul_le_mul_left (k ^ 3) hk
    calc 50 * k ^ 3 = k ^ 3 * 50 := by ring
      _ ≤ k ^ 3 * k := this
      _ = k ^ 4 := by ring
  have w13 : 50 * k ^ 2 ≤ k ^ 3 := by
    have := Nat.mul_le_mul_left (k ^ 2) hk
    calc 50 * k ^ 2 = k ^ 2 * 50 := by ring
      _ ≤ k ^ 2 * k := this
      _ = k ^ 3 := by ring
  -- monomials absorbed into `X = k²s³`
  have x1 : 50 * (k * s ^ 3) ≤ k ^ 2 * s ^ 3 := by
    have := Nat.mul_le_mul_left (k * s ^ 3) hk
    calc 50 * (k * s ^ 3) = k * s ^ 3 * 50 := by ring
      _ ≤ k * s ^ 3 * k := this
      _ = k ^ 2 * s ^ 3 := by ring
  have x2 : 50 * s ^ 3 ≤ k * s ^ 3 := by
    have := Nat.mul_le_mul_left (s ^ 3) hk
    linarith
  have key : 2000 * (2 * (k * s) + (4 * k ^ 2 * (k * s) ^ 2 +
      2 * (31 * s + 7 * k ^ 2 + 35 * k + 42) * (k * s) ^ 2 +
      (s + 3) * (21 * k + 9) * (k ^ 2 * (R + k ^ 2)) +
      (s + 3) * (s ^ 2 * (36 * k ^ 2 + 72 * k + 18) + (42 * k + 18) * (k ^ 2 * (2 * (k * s) + 1))))) +
      1000 * Y ≤ 2 * (101960 * ((k * s) ^ 2 * s) + 367100 * (k ^ 2 * (k * s) ^ 2)) := by
    rw [hY]
    ring_nf
    ring_nf at hCcost hRcost
    nlinarith [hCcost, hRcost, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, x1, x2]
  omega

end SlidingPuzzle.Hub
