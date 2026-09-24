import SlidingPuzzle.Algorithm.Finish.SquareGeometry

/-! Normalize the blank within the final square before direct block solving. -/
namespace SlidingPuzzle.Partition
variable {k : ℕ} [NeZero (k^4)]

/-- Permuting only one square preserves square membership, even for the square
containing the blank. -/
theorem squaresSorted_of_fixed_other_squares (hk : 2 ≤ k) (B C : Board (k^4))
    (hB : SquaresSorted (k := k) B) (j : GroupIndex k)
    (hfix : ∀ i : GroupIndex k, i ≠ j → ∀ x, square i x → C x=B x) :
    SquaresSorted (k := k) C := by
  intro i x hx hnonzero
  by_cases hij : i=j
  · subst i
    let y := B.symm (C x)
    obtain ⟨l,hl⟩ := square_covers hk rfl y
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
theorem exists_finish_blank_access (hk : 2 ≤ k) (B : Board (k^4))
    (hB : SquaresSorted (k := k) B) (hb : square (lastGroup k hk) (blank B)) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ 2*k^4 ∧ blank C = blank (target (k^4)) ∧ SquaresSorted (k := k) C := by
  obtain ⟨C,p,hbC,hp,hfix⟩ := exists_blank_access_path_preserving B (blank (target (k^4)))
  have ht : square (lastGroup k hk) (blank (target (k^4))) :=
    (square_target_blank hk rfl _).mpr rfl
  have hout (i : GroupIndex k) (hi : i ≠ lastGroup k hk) (x : Cell (k^4))
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
  have := (blank (target (k^4))).1.isLt
  have := (blank (target (k^4))).2.isLt
  omega

/-- Two distinct nonblank positions in the final square absorb parity repairs. -/
theorem exists_finish_buffers (hk : 2 ≤ k) :
    ∃ u v : Cell (k^4), u ≠ v ∧
      square (lastGroup k hk) u ∧ square (lastGroup k hk) v ∧
      u ≠ blank (target (k^4)) ∧ v ≠ blank (target (k^4)) := by
  have hm : 4 ≤ k^3 := by nlinarith [Nat.pow_le_pow_left hk 3]
  let a : Cell (k^3) := (⟨0,by omega⟩,⟨0,by omega⟩)
  let b : Cell (k^3) := (⟨0,by omega⟩,⟨1,by omega⟩)
  let ι := squareEmbedding (lastGroup k hk)
  have hab : a ≠ b := by simp [a,b,Fin.ext_iff]
  have he : (k-1)*k^3+k^3=k^4 := by
    have h := Nat.sub_add_cancel (by omega : 1 ≤ k)
    calc
      (k-1)*k^3+k^3 = (k-1+1)*k^3 := by ring
      _ = k^4 := by rw [h]; ring
  have hrow (c : Cell (k^3)) (hc : c.1.val=0) : ι c ≠ blank (target (k^4)) := by
    intro h
    have hh := congrArg (fun x : Cell (k^4) => x.1.val) h
    rw [blank_target_eq] at hh
    change (groupRow (lastGroup k hk)).val*k^3+c.1.val=k^4-1 at hh
    simp only [groupRow,lastGroup,Equiv.symm_apply_apply] at hh
    rw [hc] at hh
    omega
  exact ⟨ι a,ι b,ι.injective.ne hab,squareEmbedding_mem hk _ a,squareEmbedding_mem hk _ b,
    hrow a rfl,hrow b rfl⟩
end SlidingPuzzle.Partition
