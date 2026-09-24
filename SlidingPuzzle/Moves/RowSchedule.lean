import SlidingPuzzle.Moves.ProtectedTranslation

/-! A descending schedule of protected row translations. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

/-- Spread the first `L` row segments to increasing destinations. Descending
execution preserves every unprocessed source and every completed destination. -/
theorem exists_descending_row_schedule (B : Board n) (co M L : ℕ)
    (hc : co+M ≤ n) (hM : 1 < M) (d : ℕ → ℕ) (hmono : StrictMono d)
    (hd : ∀ i < L, i ≤ d i ∧ d i+2 ≤ (blank B).1.val) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 12*n^2*L ∧ blank C = blank B ∧
      (∀ (i : ℕ) (hi : i < L) (j : Fin M),
        C (⟨d i,by have := hd i hi; have := (blank B).1.isLt; omega⟩,
          ⟨co+j.val,by omega⟩) =
        B (⟨i,by have := hd i hi; have := (blank B).1.isLt; omega⟩,
          ⟨co+j.val,by omega⟩)) ∧
      (∀ x : Cell n, (∀ i < L, d i < x.1.val) ∨
        x.2.val < co ∨ co+M ≤ x.2.val → C x = B x) := by
  induction L generalizing B with
  | zero =>
    refine ⟨B,Path.nil B,by simp,rfl,?_,fun _ _ => rfl⟩
    intro i hi
    omega
  | succ L ih =>
    have hdL := hd L (by omega)
    have hbound := (blank B).1.isLt
    obtain ⟨D,p,hp,hbD,hrowD,hfixD⟩ := exists_protected_row_translation B L co M
      (d L-L) (by omega) hc hM (by omega)
    have hDL : L+(d L-L) = d L := by omega
    obtain ⟨E,q,hq,hbE,hrowE,hfixE⟩ := ih D (by
      intro i hi
      rw [hbD]
      exact hd i (by omega))
    refine ⟨E,p.append q,?_,hbE.trans hbD,?_,?_⟩
    · have hp' : p.length ≤ 12*n^2 := by
        calc
          p.length ≤ 12*n*(d L-L) := hp
          _ ≤ 12*n*n := Nat.mul_le_mul_left _ (by omega)
          _ = 12*n^2 := by ring
      rw [Path.length_append]
      calc
        p.length+q.length ≤ 12*n^2+12*n^2*L := Nat.add_le_add hp' hq
        _ = 12*n^2*(L+1) := by ring
    · intro i hi j
      by_cases hil : i < L
      · rw [hrowE i hil j]
        apply hfixD
        left
        exact hil
      · have hiL : i = L := by omega
        subst i
        rw [hfixE _ (Or.inl (by
          intro i hi
          exact hmono hi))]
        simpa only [hDL] using hrowD j
    · intro x hx
      rw [hfixE x (by
        rcases hx with hx | hx
        · exact Or.inl (fun i hi => hx i (by omega))
        · exact Or.inr hx)]
      apply hfixD
      rcases hx with hx | hx
      · exact Or.inr (Or.inl (by have := hx L (by omega); omega))
      · exact Or.inr (Or.inr hx)

end SlidingPuzzle
