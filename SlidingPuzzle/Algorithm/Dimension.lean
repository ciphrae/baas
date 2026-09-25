import SlidingPuzzle.Asymptotics

/-! The choice `k = ⌊n^(1/4)⌋` of the grid size for a board of side `n`.
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

theorem two_le_fourthRoot {n : ℕ} (hn : 16 ≤ n) : 2 ≤ fourthRoot n := by
  apply (le_fourthRoot_iff 2 n).mpr
  norm_num
  exact hn

/-- Concrete dimension choice with all validity and gap requirements. -/
theorem exists_fourth_power_dimension {n : ℕ} (hn : 16 ≤ n) :
    ∃ k : ℕ, 2 ≤ k ∧ k ^ 4 ≤ n ∧ n < (k + 1) ^ 4 ∧ n - k ^ 4 ≤ 15 * k ^ 3 := by
  refine ⟨fourthRoot n, two_le_fourthRoot hn, fourthRoot_pow_le n,
    lt_fourthRoot_add_one_pow n, ?_⟩
  apply fourth_power_gap_le (by have := two_le_fourthRoot hn; omega)
  exact lt_fourthRoot_add_one_pow n

end SlidingPuzzle
