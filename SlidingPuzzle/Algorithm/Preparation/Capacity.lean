import SlidingPuzzle.Algorithm.Cardinalities

/-! Quantitative room in a target group and its reservoir during preparation. -/
namespace SlidingPuzzle.Partition

private theorem reservoir_capacity_eq {k : ℕ} (hk : 2 ≤ k) :
    (k^3-k)*(k^3-k^2) + (k^4+k^2*(k^3-k)) = k^6 := by
  have hk2 : k ≤ k^2 := by nlinarith
  have hk3 : k^2 ≤ k^3 := by nlinarith [Nat.mul_le_mul_left k hk2]
  have h1 : k^3-k+k=k^3 := Nat.sub_add_cancel (hk2.trans hk3)
  have h2 : k^3-k^2+k^2=k^3 := Nat.sub_add_cancel hk3
  nlinarith [sq_nonneg (k^3), Nat.mul_sub_left_distrib (k^3-k) (k^3) (k^2)]

/-- Each reservoir has room for a representative from every target group. -/
theorem reservoir_capacity_ge_square {k : ℕ} (hk : 2 ≤ k) :
    k^2 ≤ (k^3-k)*(k^3-k^2) := by
  have hk2 : k ≤ k^2 := by nlinarith
  have hk3 : k^2 ≤ k^3 := by nlinarith [Nat.mul_le_mul_left k hk2]
  have hleft : k ≤ k^3-k := by
    have htwo : 2*k ≤ k^3 := by
      calc
        2*k = k*2 := by ring
        _ ≤ k*k := Nat.mul_le_mul_left k hk
        _ = k^2 := by ring
        _ ≤ k^3 := hk3
    omega
  have hright : k ≤ k^3-k^2 := by
    have hkm : 1 ≤ k-1 := by omega
    have he : k^3-k^2 = k^2*(k-1) := by
      calc
        k^3-k^2 = k^2*k-k^2*1 := by rw [show k^3 = k^2*k by ring]; simp
        _ = k^2*(k-1) := (Nat.mul_sub_left_distrib _ _ _).symm
    rw [he]
    exact hk2.trans (Nat.le_mul_of_pos_right _ (by omega))
  calc
    k^2 = k*k := by ring
    _ ≤ (k^3-k)*(k^3-k^2) := Nat.mul_le_mul hleft hright

/-- Every target group contains the labels needed to clear all corridors. -/
theorem card_targetGroup_ge_corridor_quota {n k : ℕ} [NeZero n]
    (hk : 2 ≤ k) (hn : n = k^4) (j : GroupIndex k) :
    n + k^2*(k^3-k) ≤ (targetGroup (n := n) j).card := by
  subst n
  have hcap := reservoir_capacity_eq hk
  have hres := reservoir_capacity_ge_square hk
  have hres_one : 1 ≤ (k^3-k)*(k^3-k^2) := by
    apply Nat.succ_le_of_lt
    exact lt_of_lt_of_le (pow_pos (by omega) _) hres
  have hgroup := card_targetGroup (n := k^4) rfl j
  have hblank := square_target_blank (n := k^4) hk rfl j
  by_cases hj : j = lastGroup k hk
  · have hsq : square j (blank (target (k^4))) := hblank.mpr hj
    simp only [hsq, if_true] at hgroup
    have hroom : k^4 + k^2*(k^3-k) + 1 ≤
        (k^3-k)*(k^3-k^2) + (k^4 + k^2*(k^3-k)) := by omega
    rw [hcap, ← hgroup] at hroom
    exact Nat.le_of_succ_le_succ (by simpa [Nat.succ_eq_add_one] using hroom)
  · have hsq : ¬ square j (blank (target (k^4))) := fun h => hj (hblank.mp h)
    simp only [hsq, if_false, Nat.add_zero] at hgroup
    have hroom : k^4 + k^2*(k^3-k) + 1 ≤
        (k^3-k)*(k^3-k^2) + (k^4 + k^2*(k^3-k)) := by omega
    rw [hcap, ← hgroup] at hroom
    exact (Nat.le_succ _).trans hroom

/-- A non-final target group has one label beyond the corridor quota. -/
theorem card_targetGroup_ge_corridor_quota_add_one_of_ne_last {n k : ℕ} [NeZero n]
    (hk : 2 ≤ k) (hn : n = k^4) (j : GroupIndex k) (hj : j ≠ lastGroup k hk) :
    n + k^2*(k^3-k) + 1 ≤ (targetGroup (n := n) j).card := by
  subst n
  have hcap := reservoir_capacity_eq hk
  have hres := reservoir_capacity_ge_square hk
  have hres_one : 1 ≤ (k^3-k)*(k^3-k^2) := by
    apply Nat.succ_le_of_lt
    exact lt_of_lt_of_le (pow_pos (by omega) _) hres
  have hgroup := card_targetGroup (n := k^4) rfl j
  have hblank := square_target_blank (n := k^4) hk rfl j
  have hsq : ¬ square j (blank (target (k^4))) := fun h => hj (hblank.mp h)
  simp only [hsq, if_false, Nat.add_zero] at hgroup
  have hroom : k^4 + k^2*(k^3-k) + 1 ≤
      (k^3-k)*(k^3-k^2) + (k^4 + k^2*(k^3-k)) := by omega
  rw [hcap, ← hgroup] at hroom
  exact hroom

end SlidingPuzzle.Partition
