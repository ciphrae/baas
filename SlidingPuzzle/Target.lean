import SlidingPuzzle.Basic

/-! Verification of the numeric convention for the standard target. -/
namespace SlidingPuzzle

theorem target_apply_val {n : ℕ} [NeZero n] (c : Cell n) :
    (target n c).val = (c.2.val + n * c.1.val + 1) % (n*n) := by
  simp [target, Equiv.trans_apply, finProdFinEquiv, Fin.val_add]

theorem target_bottomRight (n : ℕ) [NeZero n] :
    target n (⟨n-1, Nat.sub_lt (NeZero.pos n) (by omega)⟩,
      ⟨n-1, Nat.sub_lt (NeZero.pos n) (by omega)⟩) = 0 := by
  apply Fin.ext
  rw [target_apply_val]
  change (n - 1 + n * (n - 1) + 1) % (n*n) = 0
  have hn := NeZero.pos n
  have h : n - 1 + n * (n - 1) + 1 = n*n := by
    have h' : n - 1 + 1 = n := by omega
    nlinarith
  rw [h, Nat.mod_self]

end SlidingPuzzle
