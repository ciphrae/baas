import SlidingPuzzle.Algorithm.Parberry.RowPrefix

/-! Summing the symmetric column allowances gives the `15/2` quadratic
coefficient needed for a Parberry layer. All bounds are over naturals. -/
namespace SlidingPuzzle.Parberry

/-- Total distance of the column indices from their nearer endpoint. -/
def columnSavings (n : ℕ) : ℕ := ∑ j ∈ Finset.range (n+1), min j (n-j)

theorem columnSavings_add_two (n : ℕ) :
    columnSavings (n+2)=columnSavings n+n+1 := by
  unfold columnSavings
  rw [Finset.sum_range_succ']
  simp only [Nat.zero_min,Nat.add_zero]
  rw [Finset.sum_range_succ]
  simp only [Nat.add_assoc,Nat.sub_self,Nat.min_zero,Nat.add_zero]
  have hh : ∑ j ∈ Finset.range (n+1), min (j+1) (n+2-(j+1)) =
      ∑ j ∈ Finset.range (n+1), (min j (n-j)+1) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjn := Finset.mem_range.mp hj
    rw [show n+2-(j+1)=n-j+1 by omega,min_add_add_right]
  rw [hh,Finset.sum_add_distrib]
  simp

/-- The floor in `n²/4` costs at most one after multiplication by four. -/
theorem columnSavings_quadratic (n : ℕ) :
    4*columnSavings n ≤ n^2 ∧ n^2 ≤ 4*columnSavings n+1 := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [columnSavings]
  | one => norm_num [columnSavings,Finset.sum_range_succ]
  | more n ih _ =>
      rw [columnSavings_add_two]
      constructor <;> nlinarith [ih.1,ih.2]

/-- A column allowance plus its savings is exactly `8n`. -/
theorem rowStepBudget_balance {n j : ℕ} (hn : 1 ≤ n) (hj : j ≤ n) :
    rowStepBudget n j+2*min j (n-j)+7=8*n := by
  unfold rowStepBudget
  have h1 := min_le_left j (n-j)
  have h2 := min_le_right j (n-j)
  omega

/-- The sum of all column allowances has quadratic leading coefficient `15/2`.
The actual ordinary prefix omits boundary columns and is smaller still. -/
theorem rowPrefixBudget_quadratic {n d : ℕ} (hn : 2 ≤ n) (hd : d+1 ≤ n) :
    2*rowPrefixBudget n d+14*n ≤ 15*n^2+1 := by
  let full := ∑ j ∈ Finset.range n, rowStepBudget n j
  have hsmall : rowPrefixBudget n d ≤ full := by
    have hsub : Finset.range d ⊆ Finset.range (n-1) := Finset.range_mono (by omega)
    have hh := Finset.sum_le_sum_of_subset (f := fun j => rowStepBudget n (j+1)) hsub
    have he : full=(∑ j ∈ Finset.range (n-1), rowStepBudget n (j+1))+rowStepBudget n 0 := by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
        (Finset.sum_range_succ' (fun j => rowStepBudget n j) (n-1))
    dsimp [rowPrefixBudget]
    omega
  have hs : ∑ j ∈ Finset.range n, min j (n-j) = columnSavings n := by
    simp only [columnSavings,Finset.sum_range_succ,Nat.sub_self,Nat.min_zero,Nat.add_zero]
  have hbal : full+2*columnSavings n+7*n=8*n^2 := by
    have hh := Finset.sum_congr (s₁ := Finset.range n) (s₂ := Finset.range n) rfl
      (fun j hj => rowStepBudget_balance (by omega : 1 ≤ n) (by have := Finset.mem_range.mp hj; omega : j ≤ n))
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
      Finset.card_range,smul_eq_mul,hs] at hh
    dsimp [full]
    nlinarith [hh]
  have hsave := (columnSavings_quadratic n).2
  nlinarith

/-- The checked ordinary prefix itself has the desired quadratic leading term. -/
theorem exists_row_prefix_quadratic {n : ℕ} [NeZero n] (B : Board n)
    (a d : ℕ) (ha2 : a+2 < n) (hd : d+2 ≤ n)
    (hblank : blank B=((⟨a+1,by omega⟩ : Fin n),(⟨0,by omega⟩ : Fin n)))
    (hfixed : ∀ z : Cell n, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<1) → B z=target n z) :
    ∃ C : Board n, ∃ p : Path B C,
      2*p.length+14*n ≤ 15*n^2+1 ∧
      blank C=((⟨a+1,by omega⟩ : Fin n),(⟨d,by omega⟩ : Fin n)) ∧
      ∀ z : Cell n, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<d+1) → C z=target n z := by
  obtain ⟨C,p,hp,hblankC,hC⟩ := exists_row_prefix B a d ha2 hd hblank hfixed
  have hcost := rowPrefixBudget_quadratic (by omega : 2 ≤ n) (by omega : d+1 ≤ n)
  exact ⟨C,p,by omega,hblankC,hC⟩

end SlidingPuzzle.Parberry
