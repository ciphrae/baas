import SlidingPuzzle.Asymptotics

/-! The choice `k = ⌊c*n^(1/4)⌋` of the grid size for a board of side `n`, for a
rational constant `c`.
No puzzle-solving or protected-placement claim is made in this module. -/
namespace SlidingPuzzle

/-- Integer fourth root, expressed using two integer square roots. -/
def fourthRoot (n : ℕ) : ℕ := Nat.sqrt (Nat.sqrt n)

theorem le_fourthRoot_iff (k n : ℕ) : k ≤ fourthRoot n ↔ k ^ 4 ≤ n := by
  unfold fourthRoot
  rw [Nat.le_sqrt', Nat.le_sqrt']
  norm_num [← pow_mul]

theorem fourthRoot_pow_le (n : ℕ) : fourthRoot n ^ 4 ≤ n :=
  (le_fourthRoot_iff _ _).mp le_rfl

theorem lt_fourthRoot_add_one_pow (n : ℕ) : n < (fourthRoot n + 1) ^ 4 := by
  have h := le_fourthRoot_iff (fourthRoot n + 1) n
  omega

/-- The grid size `k = ⌊(a/b)^(1/4)*n^(1/4)⌋`: `b*k⁴ ≤ a*n < b*(k+1)⁴`. -/
theorem exists_scaled_dimension {n : ℕ} (a b : ℕ) (hb : 0 < b) (hn : 16 * b ≤ a * n) :
    ∃ k : ℕ, 2 ≤ k ∧ b * k ^ 4 ≤ a * n ∧ a * n < b * (k + 1) ^ 4 := by
  refine ⟨fourthRoot (a * n / b), ?_, ?_, ?_⟩
  · apply (le_fourthRoot_iff 2 _).mpr
    apply (Nat.le_div_iff_mul_le hb).mpr
    norm_num; omega
  · rw [mul_comm]
    exact (Nat.le_div_iff_mul_le hb).mp (fourthRoot_pow_le _)
  · have h := lt_fourthRoot_add_one_pow (a * n / b)
    have h2 := Nat.lt_mul_div_succ (a * n) hb
    calc a * n < b * (a * n / b + 1) := h2
      _ ≤ b * (fourthRoot (a * n / b) + 1) ^ 4 := Nat.mul_le_mul_left _ h

end SlidingPuzzle
