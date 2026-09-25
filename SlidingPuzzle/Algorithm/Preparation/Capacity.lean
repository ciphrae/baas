import SlidingPuzzle.Algorithm.Cardinalities

/-! Quantitative room in a target group and its reservoir during preparation. -/
namespace SlidingPuzzle.Partition
open Classical

private theorem reservoir_capacity_eq {n k : ℕ} (hk : Dims n k) :
    (side n k-2*k)*(side n k-k^2) + (2*n+k^2*(side n k-2*k)) = side n k^2 := by
  obtain ⟨hk2, h2, h3, hs3, hks⟩ := hk.facts
  have h1 : 2*k ≤ side n k := by nlinarith
  have h2 : k^2 ≤ side n k := by nlinarith
  have hks' : (k : ℤ) * (side n k : ℤ) = n := by exact_mod_cast hks
  zify [h1, h2]
  linear_combination -2*hks'

/-- Each reservoir has room for a representative from every target group. -/
theorem reservoir_capacity_ge_square {n k : ℕ} (hk : Dims n k) :
    k^2 ≤ (side n k-2*k)*(side n k-k^2) := by
  obtain ⟨hk2, h2, h3, hs3, -⟩ := hk.facts
  have hsq := hk.sq_add_le
  have hkk : k ≤ k^2 := by nlinarith
  have h2k : 2*k ≤ k^2 := by nlinarith
  have hleft : k ≤ side n k-2*k := by omega
  have hright : k ≤ side n k-k^2 := by omega
  calc
    k^2 = k*k := by ring
    _ ≤ (side n k-2*k)*(side n k-k^2) := Nat.mul_le_mul hleft hright

private theorem targetGroup_card_room {n k : ℕ} [NeZero n] (hk : Dims n k) (j : GroupIndex k) :
    2*n + k^2*(side n k-2*k) + 1 ≤
      (targetGroup (n := n) j).card + (if square j (blank (target n)) then 1 else 0) := by
  have hcap := reservoir_capacity_eq hk
  have hres := reservoir_capacity_ge_square hk
  have hres_one : 1 ≤ (side n k-2*k)*(side n k-k^2) := by
    have := hk.two_le
    exact le_trans (by nlinarith) hres
  have hgroup := card_targetGroup hk j
  omega

/-- Every target group contains the labels needed to clear all corridors. -/
theorem card_targetGroup_ge_corridor_quota {n k : ℕ} [NeZero n]
    (hk : Dims n k) (j : GroupIndex k) :
    2*n + k^2*(side n k-2*k) ≤ (targetGroup (n := n) j).card := by
  have h := targetGroup_card_room hk j
  split_ifs at h <;> omega

/-- A non-final target group has one label beyond the corridor quota. -/
theorem card_targetGroup_ge_corridor_quota_add_one_of_ne_last {n k : ℕ} [NeZero n]
    (hk : Dims n k) (j : GroupIndex k) (hj : j ≠ lastGroup k hk) :
    2*n + k^2*(side n k-2*k) + 1 ≤ (targetGroup (n := n) j).card := by
  have h := targetGroup_card_room hk j
  have hsq : ¬ square j (blank (target n)) := fun hs => hj ((square_target_blank hk j).mp hs)
  simp only [hsq, if_false, Nat.add_zero] at h
  exact h

end SlidingPuzzle.Partition
