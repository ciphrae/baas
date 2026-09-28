import SlidingPuzzle.Hub.Transport

/-! # Combined accounting

Keep transport, cleanup and Finish in one polynomial, using capacity before
rounding. Coefficients are in thousandths so the final real bound can
round only once. -/
set_option maxRecDepth 4096

namespace SlidingPuzzle.Hub

/-- Numerators of the coefficients without the logarithm, with denominator `1000`. -/
def hubLinKX : ℕ := 55650
def hubLinKW : ℕ := 251100

set_option maxHeartbeats 1600000 in
/-- Combined accounting against `X = n²s` and `W = k²n²`: the in-flight budget is
linear in `n`, so no logarithm remains. Every lower-order monomial is absorbed
using `k ≥ 500` and `s ≥ 881 k`. -/
theorem hubBound_le_lin {k s : ℕ} (hk : 500 ≤ k) (hcap : 881 * k ≤ s) :
    1000 * hubBound (k * s) k s ≤ hubLinKX * ((k * s) ^ 2 * s) +
      hubLinKW * (k ^ 2 * (k * s) ^ 2) := by
  have hC : sqCorridor k s ≤ 2 * (k * s) := by
    unfold sqCorridor
    have h1 := Nat.mul_le_mul_right s (Nat.sub_le k 1)
    have h2 := Nat.mul_le_mul (Nat.sub_le k 1) (Nat.sub_le s k)
    omega
  have hCcost := Nat.mul_le_mul_left (26000 * (k ^ 3 * s)) hC
  have hRcost := Nat.mul_le_mul_left
    (94 * k ^ 3 * s + 126 * k ^ 3 + 18 * k ^ 2 * s + 54 * k ^ 2) (Rhub_upper (k * s))
  unfold hubBound transportBound misplacedBound hubLinKX hubLinKW
  generalize Rhub (k * s) = R at *
  generalize sqCorridor k s = C at *
  set Y := 26 * (k * s) * (k ^ 2 * C + (k ^ 2 * (k * s) + k ^ 2 * (R + k ^ 2) +
      k ^ 2 * (R + 2 * (k * s) + k ^ 2 + 8) + 2 * k ^ 2 * (k * s)) + 2 * (k * s) + 5) +
    (k ^ 2 * (5 * s ^ 3 + 1509 * s ^ 2 + 1505 * s + 4796) + 9354 * k ^ 2 * (k * s)) with hY
  have hdiv : 2 * (Y / 2) ≤ Y := Nat.mul_div_le Y 2
  have hs : 440500 ≤ s := by omega
  -- monomials absorbed into `W = k⁴s²`
  have w1 : 881 * (k ^ 5 * s) ≤ k ^ 4 * s ^ 2 := by
    have := Nat.mul_le_mul_left (k ^ 4 * s) hcap
    calc 881 * (k ^ 5 * s) = k ^ 4 * s * (881 * k) := by ring
      _ ≤ k ^ 4 * s * s := this
      _ = k ^ 4 * s ^ 2 := by ring
  have w2 : 500 * (k ^ 3 * s ^ 2) ≤ k ^ 4 * s ^ 2 := by
    have := Nat.mul_le_mul_left (k ^ 3 * s ^ 2) hk
    calc 500 * (k ^ 3 * s ^ 2) = k ^ 3 * s ^ 2 * 500 := by ring
      _ ≤ k ^ 3 * s ^ 2 * k := this
      _ = k ^ 4 * s ^ 2 := by ring
  have w3 : 500 * (k ^ 2 * s ^ 2) ≤ k ^ 3 * s ^ 2 := by
    have := Nat.mul_le_mul_left (k ^ 2 * s ^ 2) hk
    calc 500 * (k ^ 2 * s ^ 2) = k ^ 2 * s ^ 2 * 500 := by ring
      _ ≤ k ^ 2 * s ^ 2 * k := this
      _ = k ^ 3 * s ^ 2 := by ring
  have w4 : 500 * (k * s ^ 2) ≤ k ^ 2 * s ^ 2 := by
    have := Nat.mul_le_mul_left (k * s ^ 2) hk
    calc 500 * (k * s ^ 2) = k * s ^ 2 * 500 := by ring
      _ ≤ k * s ^ 2 * k := this
      _ = k ^ 2 * s ^ 2 := by ring
  have w5 : 500 * s ^ 2 ≤ k * s ^ 2 := by
    have := Nat.mul_le_mul_left (s ^ 2) hk
    linarith
  have w6 : 440500 * (k ^ 4 * s) ≤ k ^ 4 * s ^ 2 := by
    have := Nat.mul_le_mul_left (k ^ 4 * s) hs
    calc 440500 * (k ^ 4 * s) = k ^ 4 * s * 440500 := by ring
      _ ≤ k ^ 4 * s * s := this
      _ = k ^ 4 * s ^ 2 := by ring
  have w7 : 500 * (k ^ 3 * s) ≤ k ^ 4 * s := by
    have := Nat.mul_le_mul_left (k ^ 3 * s) hk
    calc 500 * (k ^ 3 * s) = k ^ 3 * s * 500 := by ring
      _ ≤ k ^ 3 * s * k := this
      _ = k ^ 4 * s := by ring
  have w8 : 500 * (k ^ 2 * s) ≤ k ^ 3 * s := by
    have := Nat.mul_le_mul_left (k ^ 2 * s) hk
    calc 500 * (k ^ 2 * s) = k ^ 2 * s * 500 := by ring
      _ ≤ k ^ 2 * s * k := this
      _ = k ^ 3 * s := by ring
  have w9 : 500 * (k * s) ≤ k ^ 2 * s := by
    have := Nat.mul_le_mul_left (k * s) hk
    calc 500 * (k * s) = k * s * 500 := by ring
      _ ≤ k * s * k := this
      _ = k ^ 2 * s := by ring
  have w10 : 440500 * k ^ 5 ≤ k ^ 5 * s := by
    have := Nat.mul_le_mul_left (k ^ 5) hs
    linarith
  have w11 : 500 * k ^ 4 ≤ k ^ 5 := by
    have := Nat.mul_le_mul_left (k ^ 4) hk
    calc 500 * k ^ 4 = k ^ 4 * 500 := by ring
      _ ≤ k ^ 4 * k := this
      _ = k ^ 5 := by ring
  have w12 : 500 * k ^ 3 ≤ k ^ 4 := by
    have := Nat.mul_le_mul_left (k ^ 3) hk
    calc 500 * k ^ 3 = k ^ 3 * 500 := by ring
      _ ≤ k ^ 3 * k := this
      _ = k ^ 4 := by ring
  have w13 : 500 * k ^ 2 ≤ k ^ 3 := by
    have := Nat.mul_le_mul_left (k ^ 2) hk
    calc 500 * k ^ 2 = k ^ 2 * 500 := by ring
      _ ≤ k ^ 2 * k := this
      _ = k ^ 3 := by ring
  -- monomials absorbed into `X = k²s³`
  have x1 : 500 * (k * s ^ 3) ≤ k ^ 2 * s ^ 3 := by
    have := Nat.mul_le_mul_left (k * s ^ 3) hk
    calc 500 * (k * s ^ 3) = k * s ^ 3 * 500 := by ring
      _ ≤ k * s ^ 3 * k := this
      _ = k ^ 2 * s ^ 3 := by ring
  have x2 : 500 * s ^ 3 ≤ k * s ^ 3 := by
    have := Nat.mul_le_mul_left (s ^ 3) hk
    linarith
  have key : 2000 * (2 * (k * s) + (2 * k ^ 2 * (k * s) ^ 2 +
      (25 * s + 7 * k ^ 2 + 1033 * k + 2076) * (k * s) ^ 2 +
      (s + 3) * (21 * k + 9) * (k ^ 2 * (R + k ^ 2)) +
      (s + 3) * (s ^ 2 * (28 * k ^ 2 + 55 * k + 18) + (42 * k + 18) * (k ^ 2 * (2 * (k * s) + 1))))) +
      1000 * Y ≤ 2 * (55650 * ((k * s) ^ 2 * s) + 251100 * (k ^ 2 * (k * s) ^ 2)) := by
    rw [hY]
    ring_nf
    ring_nf at hCcost hRcost
    nlinarith [hCcost, hRcost, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, x1, x2]
  omega

end SlidingPuzzle.Hub
