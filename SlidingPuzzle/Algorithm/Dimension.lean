import SlidingPuzzle.Asymptotics

/-! The choice `k = ⌊(3/5)*n^(1/4)⌋` of the grid size for a board of side `n`.
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

/-- The grid size `k = ⌊(3/5)*n^(1/4)⌋`, which balances the two leading
monomials of `Admissible.exists_admissible_solution`. -/
theorem exists_scaled_dimension {n : ℕ} (hn : 10000 ≤ n) :
    ∃ k : ℕ, 2 ≤ k ∧ 625 * k ^ 4 ≤ 81 * n ∧ 81 * n < 625 * (k + 1) ^ 4 := by
  refine ⟨fourthRoot (81 * n / 625), ?_, ?_, ?_⟩
  · apply (le_fourthRoot_iff 2 _).mpr
    apply (Nat.le_div_iff_mul_le (by norm_num)).mpr
    omega
  · rw [mul_comm]
    exact (Nat.le_div_iff_mul_le (by norm_num)).mp (fourthRoot_pow_le _)
  · have h := lt_fourthRoot_add_one_pow (81 * n / 625)
    omega

end SlidingPuzzle
