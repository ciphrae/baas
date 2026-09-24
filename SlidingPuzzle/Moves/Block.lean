import SlidingPuzzle.Target
import SlidingPuzzle.Moves.LocalSolve
import SlidingPuzzle.Moves.BlankAccess
import SlidingPuzzle.Moves.Conjugation

/-! Square subboards and blank access from the global target corner. -/
namespace SlidingPuzzle
variable {m n : ℕ} [NeZero m] [NeZero n]

/-- The standard blank is the bottom-right corner. -/
theorem blank_target_eq (n : ℕ) [NeZero n] : blank (target n) =
    (⟨n-1,by have := NeZero.pos n; omega⟩,⟨n-1,by have := NeZero.pos n; omega⟩) := by
  apply (target n).injective
  rw [target_bottomRight]
  exact (target n).apply_symm_apply 0

/-- Coordinates of a square subboard at an arbitrary offset. -/
def blockEmbedding (ro co : ℕ) (hr : ro+m ≤ n) (hc : co+m ≤ n) : Cell m ↪ Cell n where
  toFun c := (⟨ro+c.1.val,by have := c.1.isLt; omega⟩,
    ⟨co+c.2.val,by have := c.2.isLt; omega⟩)
  inj' := by
    intro a b h
    have hx := congrArg (fun c : Cell n => c.1.val) h
    have hy := congrArg (fun c : Cell n => c.2.val) h
    apply Prod.ext <;> apply Fin.ext <;> simp only at hx hy <;> omega

omit [NeZero m] [NeZero n] in
theorem blockEmbedding_distance (ro co : ℕ) (hr : ro+m ≤ n) (hc : co+m ≤ n)
    (a b : Cell m) : gridDistance (blockEmbedding ro co hr hc a)
      (blockEmbedding ro co hr hc b) = gridDistance a b := by
  change Nat.dist (ro+a.1.val) (ro+b.1.val) + Nat.dist (co+a.2.val) (co+b.2.val) = _
  simp only [gridDistance,Nat.dist]
  omega

omit [NeZero m] [NeZero n] in
theorem mem_range_blockEmbedding (ro co : ℕ) (hr : ro+m ≤ n) (hc : co+m ≤ n)
    (x : Cell n) : x ∈ Set.range (blockEmbedding ro co hr hc) ↔
      ro ≤ x.1.val ∧ x.1.val < ro+m ∧ co ≤ x.2.val ∧ x.2.val < co+m := by
  constructor
  · rintro ⟨c,rfl⟩
    change ro ≤ ro+c.1.val ∧ ro+c.1.val < ro+m ∧ co ≤ co+c.2.val ∧ co+c.2.val < co+m
    have := c.1.isLt
    have := c.2.isLt
    omega
  · rintro ⟨hxl,hxh,hyl,hyh⟩
    refine ⟨(⟨x.1.val-ro,by omega⟩,⟨x.2.val-co,by omega⟩),?_⟩
    apply Prod.ext <;> apply Fin.ext
    · change ro+(x.1.val-ro)=x.1.val; omega
    · change co+(x.2.val-co)=x.2.val; omega

/-- Access to the local bottom-right corner fixes every other cell of the block. -/
theorem exists_block_corner_access (B : Board n) (hb : blank B = blank (target n))
    (ro co : ℕ) (hr : ro+m ≤ n) (hc : co+m ≤ n) :
    ∃ C : Board n, ∃ p : Path B C, p.length ≤ 2*n ∧
      blank C = blockEmbedding ro co hr hc (blank (target m)) ∧
      ∀ c : Cell m, c ≠ blank (target m) →
        C (blockEmbedding ro co hr hc c) = B (blockEmbedding ro co hr hc c) := by
  let ι := blockEmbedding ro co hr hc
  obtain ⟨C,p,hbC,hp,hfix⟩ := exists_blank_access_path_preserving B (ι (blank (target m)))
  refine ⟨C,p,?_,hbC,?_⟩
  · apply hp.trans
    have hx := (blank B).1.isLt
    have hy := (blank B).2.isLt
    have hx' := (ι (blank (target m))).1.isLt
    have hy' := (ι (blank (target m))).2.isLt
    unfold gridDistance Nat.dist
    omega
  · intro c hne
    apply hfix
    rw [hb,blank_target_eq,blank_target_eq]
    change ro+c.1.val < min (n-1) (ro+(m-1)) ∨
      max (n-1) (ro+(m-1)) < ro+c.1.val ∨
      co+c.2.val < min (n-1) (co+(m-1)) ∨
      max (n-1) (co+(m-1)) < co+c.2.val
    have hm := NeZero.pos m
    have hx := c.1.isLt
    have hy := c.2.isLt
    have hnot : c.1.val ≠ m-1 ∨ c.2.val ≠ m-1 := by
      by_contra h
      push Not at h
      apply hne
      rw [blank_target_eq]
      exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
    omega
end SlidingPuzzle
