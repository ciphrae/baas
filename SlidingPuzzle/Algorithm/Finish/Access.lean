import SlidingPuzzle.Algorithm.Finish.SquareGeometry

/-! Normalize the blank within the final square before direct block solving. -/
namespace SlidingPuzzle.Partition
variable {n k : ℕ} [NeZero n]

/-- Permuting only one square preserves square membership, even for the square
containing the blank. -/
theorem squaresSorted_of_fixed_other_squares (hk : Dims n k) (B C : Board n)
    (hB : SquaresSorted (k := k) B) (j : GroupIndex k)
    (hfix : ∀ i : GroupIndex k, i ≠ j → ∀ x, square i x → C x=B x) :
    SquaresSorted (k := k) C := by
  intro i x hx hnonzero
  by_cases hij : i=j
  · subst i
    let y := B.symm (C x)
    obtain ⟨l,hl⟩ := square_covers hk y
    have hly : l=j := by
      by_contra hlj
      have he : y=x := C.injective ((hfix l hlj y hl).trans (B.apply_symm_apply (C x)))
      rw [he] at hl
      exact hlj (square_unique hk hl hx)
    have hh := hB j y (hly ▸ hl) (by simpa [y] using hnonzero)
    simpa [y] using hh
  · rw [hfix i hij x hx] at hnonzero ⊢
    exact hB i x hx hnonzero

/-- Move the blank to its target corner entirely inside the final square. -/
theorem exists_finish_blank_access (hk : Dims n k) (B : Board n)
    (hB : SquaresSorted (k := k) B) (hb : square (lastGroup k hk) (blank B)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 2*n ∧ blank C = blank (target n) ∧ SquaresSorted (k := k) C := by
  obtain ⟨C,p,hbC,hp,hfix⟩ := exists_blank_access_path_preserving B (blank (target n))
  have ht : square (lastGroup k hk) (blank (target n)) :=
    (square_target_blank hk _).mpr rfl
  have hout (i : GroupIndex k) (hi : i ≠ lastGroup k hk) (x : Cell n)
      (hx : square i x) : C x=B x := by
    apply hfix
    by_contra h
    push Not at h
    have hlast : square (lastGroup k hk) x := by
      unfold square at hb ht ⊢
      omega
    exact hi (square_unique hk hx hlast)
  refine ⟨C,p,?_,hbC,squaresSorted_of_fixed_other_squares hk B C hB _ hout⟩
  apply hp.trans
  unfold gridDistance Nat.dist
  have := (blank B).1.isLt
  have := (blank B).2.isLt
  have := (blank (target n)).1.isLt
  have := (blank (target n)).2.isLt
  omega

/-- Two distinct nonblank positions in the final square absorb parity repairs. -/
theorem exists_finish_buffers (hk : Dims n k) :
    ∃ u v : Cell n, u ≠ v ∧
      square (lastGroup k hk) u ∧ square (lastGroup k hk) v ∧
      u ≠ blank (target n) ∧ v ≠ blank (target n) := by
  have hm : 4 ≤ side n k := by have := hk.k_add_two_le; have := hk.two_le; omega
  let a : Cell (side n k) := (⟨0,by omega⟩,⟨0,by omega⟩)
  let b : Cell (side n k) := (⟨0,by omega⟩,⟨1,by omega⟩)
  let ι := squareEmbedding (n := n) (lastGroup k hk)
  have hab : a ≠ b := by simp [a,b,Fin.ext_iff]
  have he : (k-1)*side n k+side n k=n := by
    have h := Nat.sub_add_cancel (by have := hk.two_le; omega : 1 ≤ k)
    calc
      (k-1)*side n k+side n k = (k-1+1)*side n k := by ring
      _ = n := by rw [h]; exact hk.mul_side
  have hrow (c : Cell (side n k)) (hc : c.1.val=0) : ι c ≠ blank (target n) := by
    intro h
    have hh := congrArg (fun x : Cell n => x.1.val) h
    rw [blank_target_eq] at hh
    change (groupRow (lastGroup k hk)).val*side n k+c.1.val=n-1 at hh
    simp only [groupRow,lastGroup,Equiv.symm_apply_apply] at hh
    rw [hc] at hh
    omega
  exact ⟨ι a,ι b,ι.injective.ne hab,squareEmbedding_mem hk _ a,squareEmbedding_mem hk _ b,
    hrow a rfl,hrow b rfl⟩
end SlidingPuzzle.Partition
