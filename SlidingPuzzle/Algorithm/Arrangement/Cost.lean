import SlidingPuzzle.Algorithm.Partition

/-! The total travel of Arrangement's vertical exchanges. Square coordinates of
two groups differ on average by `k/3`: `3*∑_{a,b<k} |a-b| = k³-k`. -/
namespace SlidingPuzzle.Partition

private theorem two_mul_sum_sub (k : ℕ) : 2*∑ i ∈ Finset.range k, (k-i) = k*(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have e : ∑ i ∈ Finset.range k, (k+1-i) = ∑ i ∈ Finset.range k, (k-i) + k := by
      have e' : ∑ i ∈ Finset.range k, (k+1-i) = ∑ i ∈ Finset.range k, ((k-i)+1) :=
        Finset.sum_congr rfl (fun i hi => by simp at hi; omega)
      rw [e', Finset.sum_add_distrib]; simp
    rw [e, show k+1-k = 1 by omega]; nlinarith [ih]

theorem three_mul_sum_dist (k : ℕ) :
    3*∑ a : Fin k, ∑ b : Fin k, Nat.dist a.val b.val = k^3-k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    have hrow : ∀ a : Fin k, Nat.dist a.val k = k-a.val := by
      intro a; have := a.isLt; simp [Nat.dist] <;> omega
    have hcol : ∑ b : Fin k, Nat.dist k b.val = ∑ b : Fin k, (k-b.val) := by
      apply Finset.sum_congr rfl; intro b _; have := b.isLt; simp [Nat.dist] <;> omega
    have hsum : 2*∑ b : Fin k, (k-b.val) = k*(k+1) := by
      rw [Finset.sum_range (fun i => k-i) |>.symm]
      exact two_mul_sum_sub k
    simp only [Finset.sum_add_distrib, hrow, Nat.dist_self, add_zero, hcol]
    have hk : k ≤ k^3 := by
      rcases Nat.eq_zero_or_pos k with h | h
      · simp [h]
      · calc k = k^1 := (pow_one k).symm
          _ ≤ k^3 := Nat.pow_le_pow_right h (by norm_num)
    have hk1 : k+1 ≤ (k+1)^3 := by
      calc k+1 = (k+1)^1 := (pow_one _).symm
        _ ≤ (k+1)^3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have e3 : (k+1)^3-(k+1) = (k^3-k)+3*(k*(k+1)) := by
      zify [hk, hk1]; ring
    rw [e3, ← ih, ← hsum]
    ring

/-- Summing a function of square coordinates over pairs of groups. -/
private theorem sum_pairs_coord {k : ℕ} (f : Fin k → Fin k → ℕ) (π : GroupIndex k → Fin k)
    (hπ : π = groupRow ∨ π = groupCol) :
    ∑ i : GroupIndex k, ∑ j : GroupIndex k, f (π i) (π j) =
      k^2*∑ a : Fin k, ∑ b : Fin k, f a b := by
  have hsplit : ∀ g : GroupIndex k → ℕ, ∑ i, g i =
      ∑ a : Fin k, ∑ b : Fin k, g (finProdFinEquiv (a, b)) := by
    intro g
    rw [← (finProdFinEquiv (m := k) (n := k)).sum_comp, Fintype.sum_prod_type]
  rcases hπ with rfl | rfl
  · simp only [hsplit, groupRow, Equiv.symm_apply_apply, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]
    ring
  · simp only [hsplit, groupCol, Equiv.symm_apply_apply, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]
    ring

theorem sum_groupCol_dist (k : ℕ) :
    3*∑ i : GroupIndex k, ∑ j : GroupIndex k, Nat.dist (groupCol i).val (groupCol j).val =
      k^2*(k^3-k) := by
  rw [sum_pairs_coord (fun a b => Nat.dist a.val b.val) groupCol (Or.inr rfl),
    ← three_mul_sum_dist]
  ring

theorem sum_groupRow_dist (k : ℕ) :
    3*∑ i : GroupIndex k, ∑ j : GroupIndex k, Nat.dist (groupRow i).val (groupRow j).val =
      k^2*(k^3-k) := by
  rw [sum_pairs_coord (fun a b => Nat.dist a.val b.val) groupRow (Or.inl rfl),
    ← three_mul_sum_dist]
  ring

end SlidingPuzzle.Partition
