import SlidingPuzzle.Moves.Local

/-! Walking the blank along a line of cells. Every tile on the line moves back
by one cell; nothing else changes. -/
namespace SlidingPuzzle

variable {n : ℕ} [NeZero n]

/-- Walk the blank from `f a` to `f (a+d)` along consecutive adjacent cells. -/
theorem exists_line_walk (f : ℕ → Cell n) (a d : ℕ)
    (hadj : ∀ t, t < d → gridDistance (f (a+t)) (f (a+t+1)) = 1)
    (hinj : ∀ t t', t ≤ d → t' ≤ d → f (a+t) = f (a+t') → t = t')
    (B : Board n) (hb : blank B = f a) :
    ∃ C : Board n, ∃ p : Path B C, p.length = d ∧ blank C = f (a+d) ∧
      (∀ t, t < d → C (f (a+t)) = B (f (a+t+1))) ∧
      (∀ x, (∀ t, t ≤ d → x ≠ f (a+t)) → C x = B x) := by
  induction d generalizing a B with
  | zero =>
    exact ⟨B, .nil B, rfl, by simpa using hb, fun t ht => by omega, fun _ _ => rfl⟩
  | succ d ih =>
    have h₁ : gridDistance (blank B) (f (a+1)) = 1 := by
      rw [hb]; simpa using hadj 0 (by omega)
    let B' := swapCells B (blank B) (f (a+1))
    have hb' : blank B' = f (a+1) := blank_swapCells B _
    obtain ⟨C, p, hp, hbC, hC, hfix⟩ := ih (a+1)
      (fun t ht => by
        have := hadj (t+1) (by omega)
        rwa [show a+(t+1) = a+1+t by ring] at this)
      (fun t t' ht ht' h => by
        have := hinj (t+1) (t'+1) (by omega) (by omega)
          (by rwa [show a+(t+1) = a+1+t by ring, show a+(t'+1) = a+1+t' by ring])
        omega)
      B' hb'
    have hne : ∀ t, 1 ≤ t → t ≤ d+1 → f (a+t) ≠ f a := fun t h1 h2 h => by
      have := hinj t 0 h2 (by omega) (by simpa using h); omega
    have hB' : ∀ x, x ≠ f a → x ≠ f (a+1) → B' x = B x := fun x h1 h2 =>
      swapCells_preserves B (by rw [hb]; exact h1) h2
    refine ⟨C, (movePath B (f (a+1)) h₁).append p, by simp [hp]; ring, ?_, ?_, ?_⟩
    · rw [hbC]; congr 1; ring
    · intro t ht
      rcases Nat.eq_zero_or_pos t with rfl | ht0
      · have hfa : C (f a) = B' (f a) := by
          apply hfix
          intro t' ht' h
          have := hinj 0 (t'+1) (by omega) (by omega)
            (by rw [show a+(t'+1) = a+1+t' by ring]; simpa using h)
          omega
        rw [show a+0 = a by ring, hfa]
        change swapCells B (blank B) _ _ = _
        rw [← hb, swapCells_at_left]
      · have h := hC (t-1) (by omega)
        rw [show a+1+(t-1) = a+t by omega] at h
        rw [h]
        apply hB'
        · exact hne (t+1) (by omega) (by omega)
        · intro h'
          have := hinj (t+1) 1 (by omega) (by omega) (by rw [show a+(t+1) = a+t+1 by ring]; exact h')
          omega
    · intro x hx
      rw [hfix x (fun t ht h => hx (t+1) (by omega)
        (by rw [show a+(t+1) = a+1+t by ring]; exact h))]
      exact hB' x (by simpa using hx 0 (by omega)) (hx 1 (by omega))

/-- Walk the blank right along row `r` from column `c` to `c+d`. -/
theorem exists_row_walk_right (B : Board n) (r : Fin n) (c d : ℕ) (hcd : c+d < n)
    (hb : blank B = (r, ⟨c, by omega⟩)) :
    ∃ C : Board n, ∃ p : Path B C, p.length = d ∧ blank C = (r, ⟨c+d, hcd⟩) ∧
      (∀ t (ht : t < d), C (r, ⟨c+t, by omega⟩) = B (r, ⟨c+t+1, by omega⟩)) ∧
      (∀ x : Cell n, (x.1 ≠ r ∨ x.2.val < c ∨ c+d < x.2.val) → C x = B x) := by
  let f : ℕ → Cell n := fun t => (r, ⟨min (c+t) (n-1), by omega⟩)
  have hfv : ∀ t (ht : t ≤ d), f t = (r, ⟨t+c, by omega⟩) := by
    intro t ht; simp only [f]; congr 2; omega
  obtain ⟨C, p, hp, hbC, hC, hfix⟩ := exists_line_walk f 0 d
    (fun t ht => by
      rw [zero_add, hfv t (by omega), hfv (t+1) (by omega)]
      simp [gridDistance, Nat.dist]; omega)
    (fun t t' ht ht' h => by
      rw [zero_add, zero_add, hfv t ht, hfv t' ht'] at h
      have := congrArg (fun x : Cell n => x.2.val) h
      simp at this; omega)
    B (by rw [hb, hfv 0 (by omega)]; congr 2; omega)
  refine ⟨C, p, hp, ?_, ?_, ?_⟩
  · rw [hbC, zero_add, hfv d le_rfl]; congr 2; omega
  · intro t ht
    have h := hC t ht
    rw [zero_add, hfv t (by omega), hfv (t+1) (by omega)] at h
    convert h using 3 <;> simp <;> omega
  · intro x hx
    apply hfix
    intro t ht h
    rw [zero_add, hfv t ht] at h
    subst h
    simp at hx; omega

/-- Walk the blank left along row `r` from column `c+d` to `c`. -/
theorem exists_row_walk_left (B : Board n) (r : Fin n) (c d : ℕ) (hcd : c+d < n)
    (hb : blank B = (r, ⟨c+d, hcd⟩)) :
    ∃ C : Board n, ∃ p : Path B C, p.length = d ∧ blank C = (r, ⟨c, by omega⟩) ∧
      (∀ t (ht : t < d), C (r, ⟨c+t+1, by omega⟩) = B (r, ⟨c+t, by omega⟩)) ∧
      (∀ x : Cell n, (x.1 ≠ r ∨ x.2.val < c ∨ c+d < x.2.val) → C x = B x) := by
  let f : ℕ → Cell n := fun t => (r, ⟨c+d-t, by omega⟩)
  obtain ⟨C, p, hp, hbC, hC, hfix⟩ := exists_line_walk f 0 d
    (fun t ht => by simp [f, gridDistance, Nat.dist]; omega)
    (fun t t' ht ht' h => by
      have := congrArg (fun x : Cell n => x.2.val) h
      simp [f] at this; omega)
    B (by rw [hb]; simp [f])
  refine ⟨C, p, hp, ?_, ?_, ?_⟩
  · rw [hbC]; simp [f]
  · intro t ht
    have h := hC (d-1-t) (by omega)
    simp only [f] at h
    convert h using 3 <;> simp <;> omega
  · intro x hx
    apply hfix
    intro t ht h
    subst h
    simp [f] at hx; omega

end SlidingPuzzle
