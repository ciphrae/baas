import SlidingPuzzle.Hub.Transport

/-! # Combined accounting on large grids

Keep transport and cleanup in one polynomial, using capacity before
rounding. Coefficients are in thousandths so the final real bound can
round only once. -/
set_option maxRecDepth 4096

namespace SlidingPuzzle.Hub

/-- Numerators of the large-grid coefficients, with denominator `1000`. -/
def hubScaledKX : ℕ := 182186
def hubScaledKY : ℕ := 167700

set_option maxHeartbeats 1600000 in
/-- Combined transport, cleanup, and Finish accounting using the actual capacity. -/
theorem hubBound_le_scaled {k s : ℕ} (hk : 112 ≤ k)
    (hL : 27 ≤ Nat.log 2 (k * s) + 1)
    (hcap : 169 * k * (Nat.log 2 (k * s) + 1) ≤ s) :
    1000 * hubBound (k * s) k s ≤ hubScaledKX * ((k * s) ^ 2 * s) +
      hubScaledKY * (k ^ 2 * (k * s) ^ 2 * (Nat.log 2 (k * s) + 1)) := by
  have hC : sqCorridor k s ≤ 2 * (k * s) := by
    unfold sqCorridor
    have h1 := Nat.mul_le_mul_right s (Nat.sub_le k 1)
    have h2 := Nat.mul_le_mul (Nat.sub_le k 1) (Nat.sub_le s k)
    omega
  have hCcost := Nat.mul_le_mul_left (26 * (k * s) * k ^ 2) hC
  have hRcost := Nat.mul_le_mul_left
    ((s + 3) * (39 * k + 15) * k ^ 2 + 52 * (k * s) * k ^ 2) (Rhub_upper (k * s))
  unfold hubBound transportBound misplacedBound hubScaledKX hubScaledKY
  generalize Rhub (k * s) = R at *
  generalize sqCorridor k s = C at *
  generalize Nat.log 2 (k * s) + 1 = L at *
  have hs : 511056 ≤ s := by
    have h := Nat.mul_le_mul (Nat.mul_le_mul_left 169 hk) hL
    omega
  have hn : 1000000 ≤ k * s := by nlinarith
  -- Local relocation overhead: (132 + 30/k)/k ≤ 1.181.
  have hx0 : 132000 * k + 30000 ≤ 1181 * k ^ 2 := by nlinarith
  have hx := Nat.mul_le_mul_right (s ^ 3) hx0
  -- Bypass leading overhead: 23.2005/k ≤ 0.208.
  have hy0 : 23201 ≤ 208 * k := by omega
  have hy := Nat.mul_le_mul_right (k ^ 3 * s ^ 2 * L) hy0
  -- All unlogged quadratic corridor terms are added before division by L.
  have hq := Nat.mul_le_mul_left (k ^ 4 * s ^ 2) hL
  have hq0 : 213514 ≤ 1924 * k := by omega
  have hq1 := Nat.mul_le_mul_right (k ^ 3 * s ^ 2) hq0
  have hq' : 718652 * (k ^ 4 * s ^ 2) + 213514 * (k ^ 3 * s ^ 2) ≤
      26688 * (k ^ 4 * s ^ 2 * L) := by
    nlinarith only [hq, hq1, Nat.zero_le (k ^ 4 * s ^ 2)]
  -- Capacity controls the bypass and cleanup `k⁵ s` remainders.
  have hc1 := Nat.mul_le_mul_left 169 (Nat.pow_le_pow_left hL 2)
  have hc2 : 188352 ≤ 2 * (169 * L ^ 2) := by omega
  have hc3 := Nat.mul_le_mul_right (k ^ 5 * s) hc2
  have hc4 := Nat.mul_le_mul_left (k ^ 4 * s * L) hcap
  have hc : 188352 * (k ^ 5 * s) ≤ 2 * (k ^ 4 * s ^ 2 * L) := by
    have e1 : 2 * (169 * L ^ 2) * (k ^ 5 * s) = 2 * (k ^ 4 * s * L * (169 * k * L)) := by ring
    have e2 : k ^ 4 * s * L * s = k ^ 4 * s ^ 2 * L := by ring
    nlinarith only [hc3, hc4, e1, e2]
  have hk5 : 112 * (k ^ 4 * s) ≤ k ^ 5 * s := by
    have := Nat.mul_le_mul_right (k ^ 4 * s) hk
    have e : k * (k ^ 4 * s) = k ^ 5 * s := by ring
    linarith
  have hk5' : k ^ 5 ≤ k ^ 5 * s := Nat.le_mul_of_pos_right _ (by omega)
  have hk4 : 112 * k ^ 4 ≤ k ^ 5 := by
    have := Nat.mul_le_mul_right (k ^ 4) hk
    have e : k * k ^ 4 = k ^ 5 := by ring
    linarith
  -- Remaining corridor terms with a factor `k⁴ s L`, `k³ s L` or `k³ s` cost at most `Y`.
  have hcL : 1000 * (182 * (k ^ 4 * s * L)) ≤ k ^ 4 * s ^ 2 * L := by
    have h1 := Nat.mul_le_mul_left (k ^ 4 * s * L) hs
    calc 1000 * (182 * (k ^ 4 * s * L)) = 182000 * (k ^ 4 * s * L) := by ring
      _ ≤ 511056 * (k ^ 4 * s * L) := Nat.mul_le_mul_right _ (by norm_num)
      _ = k ^ 4 * s * L * 511056 := by ring
      _ ≤ k ^ 4 * s * L * s := h1
      _ = k ^ 4 * s ^ 2 * L := by ring
  have hr2 : 1000 * (70 * (k ^ 3 * s * L)) ≤ k ^ 4 * s ^ 2 * L := by
    have h1 := Nat.mul_le_mul_left (k ^ 3 * s * L) hn
    calc 1000 * (70 * (k ^ 3 * s * L)) = 70000 * (k ^ 3 * s * L) := by ring
      _ ≤ 1000000 * (k ^ 3 * s * L) := Nat.mul_le_mul_right _ (by norm_num)
      _ = k ^ 3 * s * L * 1000000 := by ring
      _ ≤ k ^ 3 * s * L * (k * s) := h1
      _ = k ^ 4 * s ^ 2 * L := by ring
  have hnL : 27000000 ≤ k * s * L := by nlinarith
  have hr := Nat.mul_le_mul_left (k ^ 3 * s) hnL
  -- Finish, the blank's normalization and quadratic hop terms fit in 0.004 X.
  have hn2 : (k * s) ^ 2 = k ^ 2 * s * s := by ring
  have hf1 : 511056 * (k ^ 2 * s) ≤ (k * s) ^ 2 := by
    rw [hn2]; have := Nat.mul_le_mul_left (k ^ 2 * s) hs; linarith
  have hf5 : 112 * (k * s ^ 2) ≤ (k * s) ^ 2 := by
    have := Nat.mul_le_mul_right (s ^ 2) (Nat.mul_le_mul_right k hk)
    have e : (k * s) ^ 2 = k * k * s ^ 2 := by ring
    rw [e]; linarith
  have hf6 : 12544 * s ^ 2 ≤ (k * s) ^ 2 := by
    have h1 : 12544 ≤ k ^ 2 := by nlinarith
    have := Nat.mul_le_mul_right (s ^ 2) h1
    have e : (k * s) ^ 2 = k ^ 2 * s ^ 2 := by ring
    rw [e]; linarith
  have hk3 : k ^ 3 ≤ k ^ 2 * s := by
    have : k ≤ s := by nlinarith
    have := Nat.mul_le_mul_left (k ^ 2) this
    have e : k ^ 3 = k ^ 2 * k := by ring
    rw [e]; exact this
  have hk2s : k ^ 2 ≤ k ^ 2 * s := Nat.le_mul_of_pos_right _ (by omega)
  have hks : k * s ≤ k ^ 2 * s := by
    have := Nat.mul_le_mul_right s (show k ≤ k ^ 2 from Nat.le_self_pow (by norm_num) k)
    exact this
  have hf4 := Nat.mul_le_mul_left ((k * s) ^ 2) hs
  have hf : 1000 * (1920 * (k * s) ^ 2 + 1600 * k ^ 2 * s + 5000 * k ^ 2 + 200 * (k * s) +
      400 * (k * s ^ 2) + 100 * s ^ 2 + 400 * k ^ 3) ≤ 4 * ((k * s) ^ 2 * s) := by
    nlinarith only [hf1, hf5, hf6, hk3, hk2s, hks, hf4, Nat.zero_le ((k * s) ^ 2)]
  nlinarith only [hCcost, hRcost, hx, hy, hq', hc, hk5, hk5', hk4, hcL, hr, hr2, hf, Nat.zero_le R,
    Nat.zero_le (k ^ 4 * s * L)]

end SlidingPuzzle.Hub
