import SlidingPuzzle.Moves.ColumnTranslation

/-! A descending schedule of chunked column translations in a fixed row band. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

/-- Spread a row band's compressed columns into increasing destination columns,
restoring the blank and every cell outside the band. -/
theorem exists_descending_column_schedule (B : Board n) (ro H L m q : ℕ)
    (hr0 : 0 < ro) (hr : ro+H ≤ n) (hH : 1 < H)
    (d : ℕ → ℕ) (hmono : StrictMono d)
    (hd : ∀ i < L, i ≤ d i ∧ d i+3 ≤ n ∧ d i < (blank B).2.val ∧ d i-i ≤ q*m) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ L*(q*(4*n+m*(2*m+6*H+8))) ∧ blank C = blank B ∧
      (∀ (i : ℕ) (hi : i < L) (j : Fin H),
        C (⟨ro+j.val,by omega⟩,⟨d i,by have := hd i hi; omega⟩) =
        B (⟨ro+j.val,by omega⟩,⟨i,by have := hd i hi; omega⟩)) ∧
      (∀ x : Cell n, x.1.val < ro ∨ ro+H ≤ x.1.val ∨
        (∀ i < L, d i < x.2.val) → C x = B x) := by
  induction L generalizing B with
  | zero =>
    refine ⟨B,Path.nil B,by simp,rfl,?_,fun _ _ => rfl⟩
    intro i hi
    omega
  | succ L ih =>
    have hdL := hd L (by omega)
    obtain ⟨D,p,hp,hbD,hcolD,hfixD⟩ := exists_chunked_column_translation B ro L H
      (d L-L) m q hr0 hr (by omega) hH (by omega) hdL.2.2.2
    have hDL : L+(d L-L) = d L := by omega
    obtain ⟨E,s,hs,hbE,hcolE,hfixE⟩ := ih D (by
      intro i hi
      rw [hbD]
      exact hd i (by omega))
    refine ⟨E,p.append s,?_,hbE.trans hbD,?_,?_⟩
    · rw [Path.length_append]
      calc
        p.length+s.length ≤ (q*(4*n+m*(2*m+6*H+8)))+L*(q*(4*n+m*(2*m+6*H+8))) :=
          Nat.add_le_add hp hs
        _ = (L+1)*(q*(4*n+m*(2*m+6*H+8))) := by ring
    · intro i hi j
      by_cases hil : i < L
      · rw [hcolE i hil j]
        exact hfixD _ (Or.inr (Or.inr (Or.inl hil)))
      · have hiL : i = L := by omega
        subst i
        rw [hfixE _ (Or.inr (Or.inr (by intro i hi; exact hmono hi)))]
        simpa only [hDL] using hcolD j
    · intro x hx
      rw [hfixE x (by
        rcases hx with hx | hx | hx
        · exact Or.inl hx
        · exact Or.inr (Or.inl hx)
        · exact Or.inr (Or.inr (fun i hi => hx i (by omega))))]
      apply hfixD
      rcases hx with hx | hx | hx
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr (Or.inr (by have := hx L (by omega); omega)))

/-- The same schedule with a separate chunk count for each column, so each
column pays only for its own translation distance. -/
theorem exists_descending_column_schedule_var (B : Board n) (ro H L m : ℕ) (q : ℕ → ℕ)
    (hr0 : 0 < ro) (hr : ro+H ≤ n) (hH : 1 < H)
    (d : ℕ → ℕ) (hmono : StrictMono d)
    (hd : ∀ i < L, i ≤ d i ∧ d i+3 ≤ n ∧ d i < (blank B).2.val ∧ d i-i ≤ q i*m) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ (∑ i ∈ Finset.range L, q i)*(4*n+m*(2*m+6*H+8)) ∧ blank C = blank B ∧
      (∀ (i : ℕ) (hi : i < L) (j : Fin H),
        C (⟨ro+j.val,by omega⟩,⟨d i,by have := hd i hi; omega⟩) =
        B (⟨ro+j.val,by omega⟩,⟨i,by have := hd i hi; omega⟩)) ∧
      (∀ x : Cell n, x.1.val < ro ∨ ro+H ≤ x.1.val ∨
        (∀ i < L, d i < x.2.val) → C x = B x) := by
  induction L generalizing B with
  | zero =>
    refine ⟨B,Path.nil B,by simp,rfl,?_,fun _ _ => rfl⟩
    intro i hi
    omega
  | succ L ih =>
    have hdL := hd L (by omega)
    obtain ⟨D,p,hp,hbD,hcolD,hfixD⟩ := exists_chunked_column_translation B ro L H
      (d L-L) m (q L) hr0 hr (by omega) hH (by omega) hdL.2.2.2
    have hDL : L+(d L-L) = d L := by omega
    obtain ⟨E,s,hs,hbE,hcolE,hfixE⟩ := ih D (by
      intro i hi
      rw [hbD]
      exact hd i (by omega))
    refine ⟨E,p.append s,?_,hbE.trans hbD,?_,?_⟩
    · rw [Path.length_append, Finset.sum_range_succ]
      calc
        p.length+s.length ≤ q L*(4*n+m*(2*m+6*H+8))+
            (∑ i ∈ Finset.range L, q i)*(4*n+m*(2*m+6*H+8)) :=
          Nat.add_le_add hp hs
        _ = ((∑ i ∈ Finset.range L, q i)+q L)*(4*n+m*(2*m+6*H+8)) := by ring
    · intro i hi j
      by_cases hil : i < L
      · rw [hcolE i hil j]
        exact hfixD _ (Or.inr (Or.inr (Or.inl hil)))
      · have hiL : i = L := by omega
        subst i
        rw [hfixE _ (Or.inr (Or.inr (by intro i hi; exact hmono hi)))]
        simpa only [hDL] using hcolD j
    · intro x hx
      rw [hfixE x (by
        rcases hx with hx | hx | hx
        · exact Or.inl hx
        · exact Or.inr (Or.inl hx)
        · exact Or.inr (Or.inr (fun i hi => hx i (by omega))))]
      apply hfixD
      rcases hx with hx | hx | hx
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr (Or.inr (by have := hx L (by omega); omega)))

end SlidingPuzzle
