import SlidingPuzzle.Moves.LineWalk

/-! Moving a row segment along its own row. The blank walks through the segment,
shifting it by one cell, and returns along an adjacent lane row. One cell of
travel costs `2m+3` moves for a segment of `m` tiles, against `6m` for moving a
segment sideways. -/
namespace SlidingPuzzle

variable {n : ℕ} [NeZero n]

/-- One conveyor step: the segment at columns `e+2..e+m+1` of row `r` moves to
`e+1..e+m`, the blank from `(r, e+1)` to `(r, e)`. Only rows `r` and `r'`,
columns `e..e+m+1`, change. -/
theorem exists_conveyor_step (B : Board n) (r r' : Fin n) (hrr : Nat.dist r.val r'.val = 1)
    (e m : ℕ) (hm : e+m+1 < n) (hb : blank B = (r, ⟨e+1, by omega⟩)) :
    ∃ C : Board n, ∃ p : Path B C, p.length = 2*m+3 ∧ blank C = (r, ⟨e, by omega⟩) ∧
      (∀ t (ht : t < m), C (r, ⟨e+1+t, by omega⟩) = B (r, ⟨e+2+t, by omega⟩)) ∧
      (∀ x : Cell n, (x.1 ≠ r ∧ x.1 ≠ r') ∨ x.2.val < e ∨ e+m+1 < x.2.val → C x = B x) := by
  have hrr' : r ≠ r' := by intro h; subst h; simp at hrr
  -- 1. Walk right through the segment.
  obtain ⟨C₁, p₁, hp₁, hb₁, hC₁, hf₁⟩ := exists_row_walk_right B r (e+1) m (by omega) hb
  -- 2. Step onto the lane.
  have hd₂ : gridDistance (blank C₁) (r', ⟨e+1+m, by omega⟩) = 1 := by
    rw [hb₁]; simp [gridDistance, hrr]
  let C₂ := swapCells C₁ (blank C₁) (r', ⟨e+1+m, by omega⟩)
  have hb₂ : blank C₂ = (r', ⟨e+1+m, by omega⟩) := blank_swapCells _ _
  -- 3. Walk left along the lane.
  obtain ⟨C₃, p₃, hp₃, hb₃, -, hf₃⟩ := exists_row_walk_left C₂ r' e (m+1) (by omega)
    (by rw [hb₂]; exact Prod.ext rfl (Fin.ext (by simp; omega)))
  -- 4. Step back onto the segment's row.
  have hd₄ : gridDistance (blank C₃) (r, ⟨e, by omega⟩) = 1 := by
    rw [hb₃]; simp [gridDistance, Nat.dist_comm r'.val, hrr]
  let C := swapCells C₃ (blank C₃) (r, ⟨e, by omega⟩)
  refine ⟨C, p₁.append ((movePath C₁ _ hd₂).append (p₃.append (movePath C₃ _ hd₄))),
    by simp [hp₁, hp₃]; ring, blank_swapCells _ _, ?_, ?_⟩
  · intro t ht
    have hC : C (r, ⟨e+1+t, by omega⟩) = C₃ (r, ⟨e+1+t, by omega⟩) := by
      apply swapCells_preserves
      · rw [hb₃]; intro h; exact hrr' (congrArg Prod.fst h)
      · intro h; have := congrArg (fun x : Cell n => x.2.val) h; simp at this; omega
    rw [hC, hf₃ _ (Or.inl (by simp [hrr']))]
    have h2 : C₂ (r, ⟨e+1+t, by omega⟩) = C₁ (r, ⟨e+1+t, by omega⟩) := by
      apply swapCells_preserves
      · rw [hb₁]; intro h; have := congrArg (fun x : Cell n => x.2.val) h; simp at this; omega
      · intro h; exact hrr' (congrArg Prod.fst h)
    rw [h2, hC₁ t ht]
    congr 3; omega
  · intro x hx
    have hx1 : x ≠ (r, ⟨e, by omega⟩) := by
      rintro rfl; simp at hx; omega
    have hx2 : x ≠ blank C₃ := by
      rw [hb₃]; rintro rfl; simp at hx; omega
    have hx3 : x ≠ blank C₁ := by
      rw [hb₁]; rintro rfl; simp at hx; omega
    have hx4 : x ≠ (r', ⟨e+1+m, by omega⟩) := by
      rintro rfl; simp [hrr'.symm] at hx; omega
    have h3 : x.1 ≠ r' ∨ x.2.val < e ∨ e+(m+1) < x.2.val := by
      rcases hx with h | h | h
      · exact Or.inl h.2
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by omega))
    have h1 : x.1 ≠ r ∨ x.2.val < e+1 ∨ e+1+m < x.2.val := by
      rcases hx with h | h | h
      · exact Or.inl h.1
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega))
    change swapCells C₃ (blank C₃) _ x = _
    rw [swapCells_preserves C₃ hx2 hx1, hf₃ x h3]
    change swapCells C₁ (blank C₁) _ x = _
    rw [swapCells_preserves C₁ hx3 hx4]
    exact hf₁ x h1

/-- `D` conveyor steps: the segment at columns `e+D+1..e+D+m` of row `r`
moves to `e+1..e+m`, the blank from `(r, e+D)` to `(r, e)`. -/
theorem exists_conveyor (B : Board n) (r r' : Fin n) (hrr : Nat.dist r.val r'.val = 1)
    (e m D : ℕ) (hm : e+D+m < n) (hb : blank B = (r, ⟨e+D, by omega⟩)) :
    ∃ C : Board n, ∃ p : Path B C, p.length = D*(2*m+3) ∧ blank C = (r, ⟨e, by omega⟩) ∧
      (∀ t (ht : t < m), C (r, ⟨e+1+t, by omega⟩) = B (r, ⟨e+D+1+t, by omega⟩)) ∧
      (∀ x : Cell n, (x.1 ≠ r ∧ x.1 ≠ r') ∨ x.2.val < e ∨ e+D+m < x.2.val → C x = B x) := by
  induction D generalizing B with
  | zero => exact ⟨B, .nil B, by simp, by simpa using hb, fun t ht => rfl, fun _ _ => rfl⟩
  | succ D ih =>
    obtain ⟨C₁, p₁, hp₁, hb₁, hC₁, hf₁⟩ := exists_conveyor_step B r r' hrr (e+D) m (by omega)
      (by rw [hb]; congr 2)
    obtain ⟨C, p, hp, hbC, hC, hf⟩ := ih C₁ (by omega) hb₁
    refine ⟨C, p₁.append p, by simp [hp₁, hp]; ring, hbC, ?_, ?_⟩
    · intro t ht
      rw [hC t ht, hC₁ t ht]
      congr 3 <;> omega
    · intro x hx
      have h1 : (x.1 ≠ r ∧ x.1 ≠ r') ∨ x.2.val < e ∨ e+D+m < x.2.val := by
        rcases hx with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (by omega))
      have h2 : (x.1 ≠ r ∧ x.1 ≠ r') ∨ x.2.val < e+D ∨ e+D+m+1 < x.2.val := by
        rcases hx with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (by omega))
      rw [hf x h1]
      exact hf₁ x h2

end SlidingPuzzle
