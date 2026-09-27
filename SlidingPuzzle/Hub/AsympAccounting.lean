import SlidingPuzzle.Hub.Transport

/-! # Combined accounting

Keep transport, cleanup and Finish in one polynomial, using capacity before
rounding. Coefficients are in thousandths so the final real bound can
round only once. -/
set_option maxRecDepth 4096

namespace SlidingPuzzle.Hub

/-- Numerators of the coefficients without the logarithm, with denominator `1000`. -/
def hubLinKX : ℕ := 182340
def hubLinKW : ℕ := 776300

set_option maxHeartbeats 1600000 in
/-- Combined accounting against `X = n²s` and `W = k²n²`: the in-flight budget is
linear in `n`, so no logarithm remains. -/
theorem hubBound_le_lin {k s : ℕ} (hk : 100 ≤ k)
    (hL : 24 ≤ Nat.log 2 (k * s) + 1)
    (hcap : 48 * k * (Nat.log 2 (k * s) + 1) ≤ s) :
    1000 * hubBound (k * s) k s ≤ hubLinKX * ((k * s) ^ 2 * s) +
      hubLinKW * (k ^ 2 * (k * s) ^ 2) := by
  have hC : sqCorridor k s ≤ 2 * (k * s) := by
    unfold sqCorridor
    have h1 := Nat.mul_le_mul_right s (Nat.sub_le k 1)
    have h2 := Nat.mul_le_mul (Nat.sub_le k 1) (Nat.sub_le s k)
    omega
  have hCcost := Nat.mul_le_mul_left (26 * (k * s) * k ^ 2) hC
  have hRcost := Nat.mul_le_mul_left
    ((s + 3) * (39 * k + 15) * k ^ 2 + 52 * (k * s) * k ^ 2) (Rhub_upper (k * s))
  unfold hubBound transportBound misplacedBound hubLinKX hubLinKW
  generalize Rhub (k * s) = R at *
  generalize sqCorridor k s = C at *
  generalize Nat.log 2 (k * s) + 1 = L at *
  have hs : 115200 ≤ s := by
    have h := Nat.mul_le_mul (Nat.mul_le_mul_left 48 hk) hL
    omega
  have hn : 11520000 ≤ k * s := by nlinarith
  -- Local relocation overhead: `(132 + 30/k)/k ≤ 1.323`.
  have hx0 : 132000 * k + 30000 ≤ 1323 * k ^ 2 := by nlinarith
  have hx := Nat.mul_le_mul_right (s ^ 3) hx0
  -- Corridor terms with a factor `k³ s²`: `222.634/k ≤ 2.227`.
  have hy0 : 222634 ≤ 2227 * k := by omega
  have hy := Nat.mul_le_mul_right (k ^ 3 * s ^ 2) hy0
  -- Capacity: `k⁵ s ≤ W / (48 L)`.
  have hc1 := Nat.mul_le_mul_left (k ^ 4 * s) hcap
  have hc : 1152 * (k ^ 5 * s) ≤ k ^ 4 * s ^ 2 := by
    have e1 : k ^ 4 * s * (48 * k * L) = 48 * L * (k ^ 5 * s) := by ring
    have e2 : k ^ 4 * s * s = k ^ 4 * s ^ 2 := by ring
    have h24 := Nat.mul_le_mul_right (k ^ 5 * s) (show 1152 ≤ 48 * L by omega)
    nlinarith only [hc1, e1, e2, h24]
  have hk5 : k ^ 5 ≤ k ^ 5 * s := Nat.le_mul_of_pos_right _ (by omega)
  have hk4 : 100 * k ^ 4 ≤ k ^ 5 := by
    have := Nat.mul_le_mul_right (k ^ 4) hk
    have e : k * k ^ 4 = k ^ 5 := by ring
    linarith
  have hk4s : 115200 * (k ^ 4 * s) ≤ k ^ 4 * s ^ 2 := by
    have := Nat.mul_le_mul_left (k ^ 4 * s) hs
    have e : k ^ 4 * s * s = k ^ 4 * s ^ 2 := by ring
    linarith
  have hk3s : 11520000 * (k ^ 3 * s) ≤ k ^ 4 * s ^ 2 := by
    have := Nat.mul_le_mul_left (k ^ 3 * s) hn
    have e : k ^ 3 * s * (k * s) = k ^ 4 * s ^ 2 := by ring
    linarith
  -- Finish, the blank's normalization and quadratic hop terms fit in `17 X`.
  have hn2 : (k * s) ^ 2 = k ^ 2 * s * s := by ring
  have hf1 : 115200 * (k ^ 2 * s) ≤ (k * s) ^ 2 := by
    rw [hn2]; have := Nat.mul_le_mul_left (k ^ 2 * s) hs; linarith
  have hf5 : 100 * (k * s ^ 2) ≤ (k * s) ^ 2 := by
    have := Nat.mul_le_mul_right (s ^ 2) (Nat.mul_le_mul_right k hk)
    have e : (k * s) ^ 2 = k * k * s ^ 2 := by ring
    rw [e]; linarith
  have hf6 : 10000 * s ^ 2 ≤ (k * s) ^ 2 := by
    have h1 : 10000 ≤ k ^ 2 := by nlinarith
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
  have hf : 1915000 * (k * s) ^ 2 + 1550000 * (k ^ 2 * s) + 4931000 * k ^ 2 +
      132000 * (k * s) + 396000 * (k * s ^ 2) + 90000 * s ^ 2 + 351000 * k ^ 3 ≤
      17 * ((k * s) ^ 2 * s) := by
    nlinarith only [hf1, hf5, hf6, hk3, hk2s, hks, hf4, Nat.zero_le ((k * s) ^ 2)]
  nlinarith only [hCcost, hRcost, hx, hy, hc, hk5, hk4, hk4s, hk3s, hf, Nat.zero_le R,
    Nat.zero_le (k ^ 4 * s)]

end SlidingPuzzle.Hub
