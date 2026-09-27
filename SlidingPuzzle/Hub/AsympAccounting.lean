import SlidingPuzzle.Hub.Transport

/-! # Combined accounting on large grids

Keep transport and cleanup in one polynomial, using capacity before
rounding. Coefficients are in thousandths so the final real bound can
round only once. -/
set_option maxRecDepth 4096

namespace SlidingPuzzle.Hub

/-- Numerators of the large-grid coefficients, with denominator `1000`. -/
def hubScaledKX : ℕ := 270169
def hubScaledKY : ℕ := 309231

set_option maxHeartbeats 800000 in
/-- Combined transport, cleanup, and Finish accounting using the actual capacity. -/
theorem hubBound_le_scaled {k s : ℕ} (hk : 132 ≤ k)
    (hL : 28 ≤ Nat.log 2 (k * s) + 1)
    (hcap : 505 * k * (Nat.log 2 (k * s) + 1) ≤ s) :
    1000 * hubBound (k * s) k s ≤ hubScaledKX * ((k * s) ^ 2 * s) +
      hubScaledKY * (k ^ 2 * (k * s) ^ 2 * (Nat.log 2 (k * s) + 1)) := by
  have hC : sqCorridor k s ≤ 2 * (k * s) := by
    unfold sqCorridor
    have h1 := Nat.mul_le_mul_right s (Nat.sub_le k 1)
    have h2 := Nat.mul_le_mul (Nat.sub_le k 1) (Nat.sub_le s k)
    omega
  have hCcost := Nat.mul_le_mul_left (52 * (k * s) * k ^ 2) hC
  have hRcost := Nat.mul_le_mul_left
    (77 * s * (1 + k) * k ^ 2 + 104 * (k * s) * k ^ 2) (Rhub_upper (k * s))
  unfold hubBound transportBound misplacedBound hubScaledKX hubScaledKY
  generalize Rhub (k * s) = R at *
  generalize sqCorridor k s = C at *
  generalize Nat.log 2 (k * s) + 1 = L at *
  have hs : 1866480 ≤ s := by
    have h := Nat.mul_le_mul (Nat.mul_le_mul_left 505 hk) hL
    omega
  have hn : 1000000 ≤ k * s := by nlinarith
  -- Local relocation overhead: 154/k ≤ 1.167.
  have hx0 : 154000 ≤ 1167 * k := by omega
  have hx := Nat.mul_le_mul_right (k * s ^ 3) hx0
  -- Bypass leading overhead: 110.2717/k ≤ 0.836.
  have hy0 : 110272 ≤ 836 * k := by omega
  have hy := Nat.mul_le_mul_right (k ^ 3 * s ^ 2 * L) hy0
  -- All unlogged quadratic corridor terms are added before division by L.
  have hq := Nat.mul_le_mul_left (k ^ 4 * s ^ 2) hL
  have hq0 : 348884 ≤ 2644 * k := by omega
  have hq1 := Nat.mul_le_mul_right (k ^ 3 * s ^ 2) hq0
  have hq' : 1374441 * (k ^ 4 * s ^ 2) + 348884 * (k ^ 3 * s ^ 2) ≤
      49182 * (k ^ 4 * s ^ 2 * L) := by
    nlinarith only [hq, hq1, Nat.zero_le (k ^ 4 * s ^ 2)]
  -- Capacity controls the bypass and cleanup k^4 remainders together.
  have hc0 : 1000 * (129 * k + 77) ≤ 395920 * k := by omega
  have hc1 := Nat.mul_le_mul_left (505 * k) (Nat.pow_le_pow_left hL 2)
  have hc2 : 1000 * (129 * k + 77) ≤ 505 * k * L ^ 2 := by
    nlinarith only [hc0, hc1]
  have hc3 := Nat.mul_le_mul_right (k ^ 4 * s) hc2
  have hc4 := Nat.mul_le_mul_left (k ^ 4 * s * L) hcap
  have hc : 1000 * (129 * k ^ 5 * s + 77 * k ^ 4 * s) ≤
      1 * (k ^ 4 * s ^ 2 * L) := by nlinarith only [hc3, hc4]
  -- Linear corridor terms cost less than one thousandth of Y.
  have hnL : 23630000 ≤ k * s * L := by nlinarith
  have hr := Nat.mul_le_mul_left (k ^ 3 * s) hnL
  -- Finish, the blank's normalization and quadratic hop terms fit in 0.002 X.
  have hf1 : k ^ 2 * s ≤ (k * s) ^ 2 := by nlinarith
  have hf2 : k ^ 2 ≤ (k * s) ^ 2 := by nlinarith
  have hf3 : k * s ≤ (k * s) ^ 2 := by nlinarith
  have hf4 := Nat.mul_le_mul_left ((k * s) ^ 2) hs
  have hf : 1000 * (1913 * (k * s) ^ 2 + 1582 * k ^ 2 * s +
      4796 * k ^ 2 + 106 * (k * s)) ≤ 2 * ((k * s) ^ 2 * s) := by
    nlinarith only [hf1, hf2, hf3, hf4, Nat.zero_le ((k * s) ^ 2)]
  nlinarith only [hCcost, hRcost, hx, hy, hq', hc, hr, hf]

end SlidingPuzzle.Hub
