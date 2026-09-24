import SlidingPuzzle.Algorithm.Residual
import SlidingPuzzle.Bridge.Reachability

/-! Reachability of a residual board after a solved outer prefix. -/
namespace SlidingPuzzle

noncomputable section
variable {m n : ℕ} [NeZero m] [NeZero n]

omit [NeZero m] [NeZero n] in
private theorem boardSign_residual (d : ℕ) (hd : d + m = n) (B : Board n)
    (hB : ∀ x y : Fin n, x.val < d ∨ y.val < d → B (x, y) = target n (x, y))
    (A : Board m) (hA : ∀ c, B (cornerEmbedding d hd c) = cornerLabels d hd (A c)) :
    boardSign B = boardSign A := by
  let p : Equiv.Perm (Cell m) := A.trans (target m).symm
  have hperm : B.trans (target n).symm = p.viaFintypeEmbedding (cornerEmbedding d hd) := by
    apply Equiv.ext
    intro x
    by_cases hx : x ∈ Set.range (cornerEmbedding d hd)
    · obtain ⟨c, rfl⟩ := hx
      simp only [Equiv.trans_apply, Equiv.Perm.viaFintypeEmbedding_apply_image, p]
      rw [hA]
      simp [cornerLabels]
    · rw [Equiv.Perm.viaFintypeEmbedding_apply_notMem_range p (cornerEmbedding d hd) hx]
      change (target n).symm (B x) = x
      rw [hB x.1 x.2]
      · exact (target n).symm_apply_apply x
      · by_contra hsmall
        push Not at hsmall
        apply hx
        refine ⟨(⟨x.1.val - d, by have := x.1.isLt; omega⟩,
          ⟨x.2.val - d, by have := x.2.isLt; omega⟩), ?_⟩
        apply Prod.ext <;> apply Fin.ext <;> change d + (_ - d) = _ <;> omega
  unfold boardSign
  rw [hperm, Equiv.Perm.viaFintypeEmbedding_sign]

omit [NeZero m] [NeZero n] in
private theorem colorSign_cornerEmbedding (d : ℕ) (hd : d + m = n) (c : Cell m) :
    colorSign (cornerEmbedding d hd c) = colorSign c := by
  unfold colorSign cornerEmbedding
  change (-1 : ℤˣ) ^ ((d + c.1.val) + (d + c.2.val)) =
    (-1 : ℤˣ) ^ (c.1.val + c.2.val)
  rw [show (d + c.1.val) + (d + c.2.val) = 2 * d + (c.1.val + c.2.val) by omega,
    pow_add]
  simp [pow_mul]

private theorem colorSign_blank_target (k : ℕ) [NeZero k] :
    colorSign (blank (target k)) = 1 := by
  have hblank : blank (target k) =
      (⟨k - 1, Nat.sub_lt (NeZero.pos k) (by omega)⟩,
        ⟨k - 1, Nat.sub_lt (NeZero.pos k) (by omega)⟩) := by
    apply (target k).injective
    rw [target_bottomRight]
    exact (target k).apply_symm_apply 0
  rw [hblank]
  unfold colorSign
  change (-1 : ℤˣ) ^ ((k - 1) + (k - 1)) = 1
  apply Even.neg_one_pow
  exact ⟨k - 1, by omega⟩

/-- A reachable board whose outer prefix is solved has a reachable residual board. -/
theorem residual_reachable (hm : 2 ≤ m) (d : ℕ) (hd : d + m = n) (B : Board n)
    (hB : ∀ x y : Fin n, x.val < d ∨ y.val < d → B (x, y) = target n (x, y))
    (A : Board m) (hA : ∀ c, B (cornerEmbedding d hd c) = cornerLabels d hd (A c))
    (hreach : Reachable B) :
    Reachable A := by
  apply (reachable_iff_parityInvariant hm A).mpr
  have hblank : blank B = cornerEmbedding d hd (blank A) :=
    blank_of_embedded_board (cornerEmbedding d hd) (cornerLabels d hd)
      (cornerLabels_zero d hd) A B hA
  have hparity := reachable_parityInvariant B hreach
  rw [parityInvariant, boardSign_residual d hd B hB A hA, hblank,
    colorSign_cornerEmbedding] at hparity
  rw [colorSign_blank_target n] at hparity
  rw [parityInvariant, colorSign_blank_target m]
  exact hparity

end
end SlidingPuzzle
