import SlidingPuzzle.Tree.Transport
import SlidingPuzzle.Tree.Hier

/-! # Simple sufficient conditions for the tree proof's probabilistic events -/
namespace SlidingPuzzle.Tree
open Finset

/-- The upper event count is at most n³ once 8kq≤s. Both families therefore
fit under the existing cubic power-of-two slack. -/
theorem event_bounds {n k s q : ℕ} (td : TDims n k s q) (hwide : 8 * k * q ≤ s) :
    2 * (4 * k ^ 2 * q * k * s ^ 2) ≤ 2 ^ GroupedOrder.lamN n ∧
    2 * (4 * k ^ 2 * q * k ^ 2 * s ^ 2) < 2 ^ GroupedOrder.lamN n := by
  have hk : 1 ≤ k := by have := td.hd.two_le; omega
  have h1 : 2 * (4 * k ^ 2 * q * k ^ 2 * s ^ 2) ≤ n ^ 3 := by
    rw [← td.mul]
    nlinarith only [Nat.mul_le_mul_left (k ^ 3 * s ^ 2) hwide]
  have hn : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by decide) n
  have hp := Nat.pow_lt_pow_left hn (by decide : (3 : ℕ) ≠ 0)
  have h2 : n ^ 3 < 2 ^ GroupedOrder.lamN n := by
    unfold GroupedOrder.lamN
    rw [mul_comm, pow_mul]
    exact hp
  have h3 : 2 * (4 * k ^ 2 * q * k * s ^ 2) ≤
      2 * (4 * k ^ 2 * q * k ^ 2 * s ^ 2) := by
    have hk2 : k ≤ k ^ 2 := by nlinarith
    nlinarith only [Nat.mul_le_mul_left (8 * k ^ 2 * q * s ^ 2) hk2]
  exact ⟨h3.trans (h1.trans h2.le), h1.trans_lt h2⟩

/-- A coarse logarithm bound using only the upper grid bracket. -/
theorem log_slack_le {n b D : ℕ} (hb : 1 ≤ b) (hn : n ≤ (2 * b) ^ D) :
    GroupedOrder.lamN n ≤ 10 * (D + 1) * b := by
  have hbpow : b ≤ 2 ^ b := (Nat.lt_two_pow_self).le
  have h2b : 2 * b ≤ 2 ^ (b + 1) := by
    rw [pow_succ]
    nlinarith
  have hn2 : n ≤ 2 ^ ((b + 1) * D) := by
    calc n ≤ (2 * b) ^ D := hn
      _ ≤ (2 ^ (b + 1)) ^ D := Nat.pow_le_pow_left h2b D
      _ = _ := (pow_mul _ _ _).symm
  have hlog := Nat.log_mono_right (b := 2) hn2
  rw [Nat.log_pow (by decide : 1 < 2)] at hlog
  unfold GroupedOrder.lamN
  nlinarith

/-- The number of offsets is no greater than the number of fine blocks. -/
theorem offsets_le_grid {b : ℕ} (hb : 2 ≤ b) : ∀ h : ℕ, 0 < h → h * b ≤ b ^ h
  | 0, hh => by omega
  | 1, _ => by simp
  | h + 2, _ => by
    have ih := offsets_le_grid hb (h + 1) (by omega)
    have ht0 : h + 2 ≤ b * (h + 1) := by
      nlinarith [Nat.mul_le_mul_right (h + 1) hb]
    have ht : (h + 2) * b ≤ b * ((h + 1) * b) := by
      nlinarith only [Nat.mul_le_mul_right b ht0]
    calc (h + 2) * b ≤ b * ((h + 1) * b) := ht
      _ ≤ b * b ^ (h + 1) := Nat.mul_le_mul_left b ih
      _ = b ^ (h + 2) := by rw [pow_succ]; ring

end SlidingPuzzle.Tree
