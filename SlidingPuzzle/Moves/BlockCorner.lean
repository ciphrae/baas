import SlidingPuzzle.Moves.ThreeCycle

/-! Correct a block's corner before borrowing the blank. -/
namespace SlidingPuzzle
variable {m n : ℕ} [NeZero m] [NeZero n]

omit [NeZero m] in
/-- Correct the chosen corner by an even permutation within the block. -/
theorem exists_correct_block_corner (B T : Board n) (hn : 4 ≤ n)
    (ι : Cell m ↪ Cell n) (z a b : Cell m)
    (hza : z ≠ a) (hzb : z ≠ b) (hab : a ≠ b)
    (hzero : ∀ c, T (ι c) ≠ 0)
    (hlabels : ∀ c, ∃ d, B (ι c) = T (ι d)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 3022*n ∧ blank C = blank B ∧ C (ι z) = T (ι z) ∧
      (∀ c, ∃ d, C (ι c) = T (ι d)) ∧
      (∀ x, x ∉ Set.range ι → C x = B x) := by
  classical
  by_cases hz : B (ι z) = T (ι z)
  · exact ⟨B,Path.nil B,by simp,rfl,hz,hlabels,fun _ _ => rfl⟩
  choose f hf using hlabels
  have hfinj : Function.Injective f := by
    intro c d h
    exact ι.injective (B.injective (by rw [hf c,hf d,h]))
  obtain ⟨c,hc⟩ := (Finite.surjective_of_injective hfinj) z
  have hcz : c ≠ z := by
    intro h
    subst c
    exact hz (by rw [hf z,hc])
  let d := if c=a then b else a
  have hdz : d ≠ z := by
    dsimp [d]
    split
    · exact hzb.symm
    · exact hza.symm
  have hcd : c ≠ d := by
    dsimp [d]
    split
    · next h => rw [h]; exact hab
    · assumption
  have hBzero (x : Cell m) : B (ι x) ≠ 0 := by rw [hf x]; exact hzero _
  obtain ⟨C,p,hp,hbC,hCz,hCc,hCd,hfix⟩ := exists_three_cycle B hn (ι z) (ι c) (ι d)
    (ι.injective.ne hcz.symm) (ι.injective.ne hdz.symm) (ι.injective.ne hcd)
    (hBzero z) (hBzero c) (hBzero d)
  refine ⟨C,p,hp,hbC,by rw [hCz,hf c,hc],?_,?_⟩
  · intro x
    by_cases hxz : x=z
    · subst x; exact ⟨f c,hCz.trans (hf c)⟩
    by_cases hxc : x=c
    · subst x; exact ⟨f d,hCc.trans (hf d)⟩
    by_cases hxd : x=d
    · subst x; exact ⟨f z,hCd.trans (hf z)⟩
    exact ⟨f x,(hfix _ (ι.injective.ne hxz) (ι.injective.ne hxc) (ι.injective.ne hxd)).trans (hf x)⟩
  · intro x hx
    exact hfix x (fun h => hx ⟨z,h.symm⟩) (fun h => hx ⟨c,h.symm⟩) (fun h => hx ⟨d,h.symm⟩)
end SlidingPuzzle
