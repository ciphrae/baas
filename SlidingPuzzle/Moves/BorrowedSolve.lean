import SlidingPuzzle.Moves.Block

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

/-- With its corner already correct, a closed block can be solved up to a
specified local transposition. Blank access is undone and all outside cells
are restored, including the global blank. -/
theorem exists_borrowed_solution_of_solver {K : ℕ} (hsolver : CubicSolverBound K)
    (B T : Board n) (hm : 8 ≤ m)
    (ro co : ℕ) (hr : ro+m ≤ n) (hc : co+m ≤ n)
    (hb : blank B = blank (target n))
    (hzero : ∀ c, T (blockEmbedding ro co hr hc c) ≠ 0)
    (hlabels : ∀ c, ∃ d, B (blockEmbedding ro co hr hc c) = T (blockEmbedding ro co hr hc d))
    (hcorner : B (blockEmbedding ro co hr hc (blank (target m))) =
      T (blockEmbedding ro co hr hc (blank (target m))))
    (a b : Cell m) (hab : a ≠ b) (ha : a ≠ blank (target m)) (hb' : b ≠ blank (target m)) :
    ∃ F : Board n, ∃ r : Path B F,
      r.length ≤ K*m^3+4*n ∧ blank F = blank B ∧
      ((∀ c, F (blockEmbedding ro co hr hc c) = T (blockEmbedding ro co hr hc c)) ∨
       (∀ c, F (blockEmbedding ro co hr hc c) =
         T (blockEmbedding ro co hr hc (Equiv.swap a b c)))) ∧
      (∀ x, x ∉ Set.range (blockEmbedding ro co hr hc) → F x = B x) := by
  classical
  let ι := blockEmbedding ro co hr hc
  let z := blank (target m)
  let η := borrowedLabels ι T hzero
  obtain ⟨C,p,hp,hbC,hC⟩ := exists_block_corner_access B hb ro co hr hc
  have hCzero : C (ι z) = 0 := by rw [← hbC]; exact C.apply_symm_apply 0
  have hCη : ∀ c, C (ι c) ∈ Set.range η := by
    intro c
    by_cases hcz : c=z
    · subst c
      exact ⟨0,by simpa [η] using hCzero.symm⟩
    · obtain ⟨d,hd⟩ := hlabels c
      have hdz : d ≠ z := by
        intro he
        apply hcz
        apply ι.injective
        apply B.injective
        exact hd.trans (by rw [he]; exact hcorner.symm)
      exact ⟨target m d,by rw [borrowedLabels_target ι T hzero d hdz,hC c hcz]; exact hd.symm⟩
  obtain ⟨A,hA⟩ := exists_board_of_embedded_labels ι η C hCη
  have hAz : blank A = z := by
    apply ι.injective
    exact (blank_of_embedded_board ι η (borrowedLabels_zero _ _ _) A C hA).symm.trans hbC
  have hta : target m a ≠ 0 := by
    intro h
    exact ha ((target m).injective (h.trans ((target m).apply_symm_apply 0).symm))
  have htb : target m b ≠ 0 := by
    intro h
    exact hb' ((target m).injective (h.trans ((target m).apply_symm_apply 0).symm))
  obtain ⟨D,q,hq,hD⟩ := exists_solution_cubic_up_to_swap_of_solver hsolver A hm a b hab hta htb
  have hDz : blank D = z := by
    rcases hD with rfl | rfl
    · rfl
    · change Equiv.swap a b z = z
      exact Equiv.swap_apply_of_ne_of_ne ha.symm hb'.symm
  obtain ⟨E,s,hs,hE,hfix⟩ := q.exists_embedded ι
    (fun x y h => by rw [blockEmbedding_distance]; exact h) η (borrowedLabels_zero _ _ _) C hA
  have hbE : blank E = blank C := by
    rw [blank_of_embedded_board ι η (borrowedLabels_zero _ _ _) D E hE,hDz,hbC]
  let S : Set (Cell n) := {x | ∃ c, c ≠ z ∧ ι c=x}
  have haccess (x : Cell n) (hx : x ∈ S) : C x = B x := by
    obtain ⟨c,hc,rfl⟩ := hx
    exact hC c hc
  have hlocal (x : Cell n) (hx : x ∉ S) : E x = C x := by
    by_cases hin : x ∈ Set.range ι
    · obtain ⟨c,rfl⟩ := hin
      have he : c=z := by by_contra h; exact hx ⟨c,h,rfl⟩
      subst c
      have hez : E (ι z) = 0 := by rw [← hbC,← hbE]; exact E.apply_symm_apply 0
      exact hez.trans hCzero.symm
    · exact hfix x hin
  obtain ⟨F,r,hlen,hbF,hF,hFfix⟩ := p.exists_conjugated s hbE S haccess hlocal
  have hFcorner : F (ι z) = T (ι z) := by
    rw [hFfix]
    · exact hcorner
    · rintro ⟨c,hc,he⟩
      exact hc (ι.injective he)
  have hFn (c : Cell m) (hc : c ≠ z) : F (ι c) = η (D c) := by
    rw [hF _ ⟨c,hc,rfl⟩,hE]
  refine ⟨F,r,by omega,hbF,?_,?_⟩
  · rcases hD with rfl | rfl
    · left
      intro c
      by_cases hcz : c=z
      · subst c; exact hFcorner
      · rw [hFn c hcz,borrowedLabels_target ι T hzero c hcz]
    · right
      intro c
      have hswapz : Equiv.swap a b z=z := Equiv.swap_apply_of_ne_of_ne ha.symm hb'.symm
      by_cases hcz : c=z
      · subst c; rw [hswapz]; exact hFcorner
      · have hsc : Equiv.swap a b c ≠ z := by
          intro he
          exact hcz ((Equiv.swap a b).injective (he.trans hswapz.symm))
        rw [hFn c hcz]
        exact borrowedLabels_target ι T hzero (Equiv.swap a b c) hsc
  · intro x hx
    apply hFfix
    rintro ⟨c,_,he⟩
    exact hx ⟨c,he⟩

/-- Specialize the solver-parametric construction to the checked cubic solver. -/
theorem exists_borrowed_solution (B T : Board n) (hm : 8 ≤ m)
    (ro co : ℕ) (hr : ro+m ≤ n) (hc : co+m ≤ n)
    (hb : blank B = blank (target n))
    (hzero : ∀ c, T (blockEmbedding ro co hr hc c) ≠ 0)
    (hlabels : ∀ c, ∃ d, B (blockEmbedding ro co hr hc c) = T (blockEmbedding ro co hr hc d))
    (hcorner : B (blockEmbedding ro co hr hc (blank (target m))) =
      T (blockEmbedding ro co hr hc (blank (target m))))
    (a b : Cell m) (hab : a ≠ b) (ha : a ≠ blank (target m)) (hb' : b ≠ blank (target m)) :
    ∃ F : Board n, ∃ r : Path B F,
      r.length ≤ 527*m^3+4*n ∧ blank F = blank B ∧
      ((∀ c, F (blockEmbedding ro co hr hc c) = T (blockEmbedding ro co hr hc c)) ∨
       (∀ c, F (blockEmbedding ro co hr hc c) =
         T (blockEmbedding ro co hr hc (Equiv.swap a b c)))) ∧
      (∀ x, x ∉ Set.range (blockEmbedding ro co hr hc) → F x = B x) := by
  exact exists_borrowed_solution_of_solver cubicSolverBound_current B T hm ro co hr hc hb hzero hlabels hcorner a b hab ha hb'

end
end SlidingPuzzle
