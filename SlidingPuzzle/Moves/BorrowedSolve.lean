import SlidingPuzzle.Basic

/-! Solve a blank-free square by borrowing and returning the global blank. -/
namespace SlidingPuzzle
noncomputable section
variable {m n : ℕ} [NeZero m] [NeZero n]

/-- Replace the corner's target label by zero to make a local puzzle alphabet. -/
def borrowedLabels (ι : Cell m ↪ Cell n) (T : Board n)
    (hzero : ∀ c, T (ι c) ≠ 0) : Tile m ↪ Tile n where
  toFun t := if t=0 then 0 else T (ι ((target m).symm t))
  inj' := by
    intro a b h
    by_cases ha : a=0 <;> by_cases hb : b=0
    · exact ha.trans hb.symm
    · simp only [ha,hb,if_true,if_false] at h
      exact False.elim (hzero _ h.symm)
    · simp only [ha,hb,if_true,if_false] at h
      exact False.elim (hzero _ h)
    · simp only [ha,hb,if_false] at h
      exact (target m).symm.injective (ι.injective (T.injective h))

@[simp] theorem borrowedLabels_zero (ι : Cell m ↪ Cell n) (T : Board n)
    (hzero : ∀ c, T (ι c) ≠ 0) : borrowedLabels ι T hzero 0 = 0 := by
  change (if (0 : Tile m)=0 then 0 else T (ι ((target m).symm 0))) = 0
  simp

theorem borrowedLabels_target (ι : Cell m ↪ Cell n) (T : Board n)
    (hzero : ∀ c, T (ι c) ≠ 0) (c : Cell m) (hc : c ≠ blank (target m)) :
    borrowedLabels ι T hzero (target m c) = T (ι c) := by
  have h : target m c ≠ 0 := by
    intro h
    exact hc ((target m).injective (h.trans ((target m).apply_symm_apply 0).symm))
  change (if target m c=0 then 0 else T (ι ((target m).symm (target m c)))) = T (ι c)
  simp [h]

end
end SlidingPuzzle
