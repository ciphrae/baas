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

namespace SlidingPuzzle.Tree

theorem log_linear_le : ∀ L : ℕ, 8 ≤ L → 24 * L + 54 ≤ 2 ^ L
  | 8, _ => by norm_num
  | L + 9, _ => by
    have ih := log_linear_le (L + 8) (by omega)
    rw [pow_succ]
    have : 24 ≤ 2 ^ (L + 8) := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 8 ≤ L + 8 by omega))
    omega

/-- The logarithmic slack against the lane offsets: `2 λ ≤ h b` for `b ≥ 256`. -/
theorem log_slack_fine {m b h : ℕ} (hh : 1 ≤ h) (hb : 256 ≤ b) (hm : m ≤ (2 * b) ^ (2 * h + 2)) :
    2 * GroupedOrder.lamN m ≤ h * b := by
  set L := Nat.log 2 b with hL
  have hbL : b < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by decide) b
  have hL8 : 8 ≤ L := by
    rw [hL]
    exact Nat.le_log_of_pow_le (by decide) (le_trans (by norm_num) hb)
  have hLb : 24 * L + 54 ≤ b :=
    (log_linear_le L hL8).trans (Nat.pow_log_le_self 2 (by omega))
  have h2b : 2 * b < 2 ^ (L + 2) := by rw [pow_succ]; omega
  have hm2 : m < 2 ^ ((L + 2) * (2 * h + 2)) := by
    calc m ≤ (2 * b) ^ (2 * h + 2) := hm
      _ < (2 ^ (L + 2)) ^ (2 * h + 2) := Nat.pow_lt_pow_left h2b (by omega)
      _ = _ := (pow_mul _ _ _).symm
  have hlog : Nat.log 2 m < (L + 2) * (2 * h + 2) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    exact Nat.log_lt_of_lt_pow (by omega) hm2
  unfold GroupedOrder.lamN
  have h1 : (L + 2) * (2 * h + 2) ≤ 4 * h * (L + 2) := by nlinarith
  have h2 : h * (24 * L + 54) ≤ h * b := Nat.mul_le_mul_left h hLb
  nlinarith

end SlidingPuzzle.Tree
