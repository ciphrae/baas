import SlidingPuzzle.Paths

/-! The Manhattan potential under legal moves. Each move changes it by exactly
one, so `length + M(end) = M(start) + 2*inefficientMoves` for every path, and
`M(B) ≤ OPT(B)`. -/

namespace SlidingPuzzle

/-- Moving one grid unit changes distance to a fixed cell by exactly one. -/
theorem gridDistance_step_delta {n : ℕ} {a b : Cell n}
    (h : gridDistance a b = 1) (c : Cell n) :
    gridDistance a c + 1 = gridDistance b c ∨
      gridDistance b c + 1 = gridDistance a c := by
  simp only [gridDistance, Nat.dist] at *
  omega

private def contribution {n : ℕ} (B : Board n) (t : Tile n) : ℕ :=
  if t.val = 0 then 0 else gridDistance (position B t) (position (target n) t)

/-- A blank/tile transposition changes only the moved tile's contribution.
The cells need not be adjacent; this identity does not assert legality. -/
theorem manhattan_blank_swap_balance {n : ℕ} [NeZero n] (B : Board n)
    (c : Cell n) (hcb : c ≠ blank B) :
    manhattan (swapCells B (blank B) c) +
        gridDistance c (position (target n) (B c)) =
      manhattan B + gridDistance (blank B) (position (target n) (B c)) := by
  have ht : B c ≠ 0 := by
    intro heq
    apply hcb
    simpa [blank, position] using congrArg B.symm heq
  have htv : (B c).val ≠ 0 := by
    intro heq
    apply ht
    exact Fin.ext heq
  have hrest : ∀ t ∈ (Finset.univ : Finset (Tile n)).erase (B c),
      contribution (swapCells B (blank B) c) t = contribution B t := by
    intro t hmem
    have htc : t ≠ B c := (Finset.mem_erase.mp hmem).1
    unfold contribution
    split_ifs with ht0
    · rfl
    · congr 1
      rw [position_swapCells]
      apply Equiv.swap_apply_of_ne_of_ne
      · intro heq
        apply ht0
        have heq' := congrArg B heq
        simpa [position, blank] using congrArg Fin.val heq'
      · intro heq
        apply htc
        simpa [position] using congrArg B heq
  have hsum : (∑ t ∈ (Finset.univ : Finset (Tile n)).erase (B c),
        contribution (swapCells B (blank B) c) t) =
      ∑ t ∈ (Finset.univ : Finset (Tile n)).erase (B c), contribution B t :=
    Finset.sum_congr rfl hrest
  have hB := Finset.sum_erase_add (Finset.univ : Finset (Tile n))
    (contribution B) (Finset.mem_univ (B c))
  have hC := Finset.sum_erase_add (Finset.univ : Finset (Tile n))
    (contribution (swapCells B (blank B) c)) (Finset.mem_univ (B c))
  have hconB : contribution B (B c) = gridDistance c (position (target n) (B c)) := by
    simp only [contribution, htv, ↓reduceIte, position, Equiv.symm_apply_apply]
  have hconC : contribution (swapCells B (blank B) c) (B c) =
      gridDistance (blank B) (position (target n) (B c)) := by
    simp only [contribution, htv, ↓reduceIte, position_swapCells]
    simp only [position, Equiv.symm_apply_apply, Equiv.swap_apply_right]
  rw [hconB] at hB
  rw [hconC] at hC
  change _ = manhattan B at hB
  change _ = manhattan (swapCells B (blank B) c) at hC
  omega

/-- A legal move changes the distance potential by precisely one. -/
theorem Step.manhattan_delta {n : ℕ} [NeZero n] {B C : Board n} (h : Step B C) :
    manhattan B + 1 = manhattan C ∨ manhattan C + 1 = manhattan B := by
  obtain ⟨c, hc, rfl⟩ := h
  have hcb : c ≠ blank B := by
    intro heq
    subst c
    simp at hc
  have hbalance := manhattan_blank_swap_balance B c hcb
  have hd := gridDistance_step_delta hc (position (target n) (B c))
  omega

/-- The potential can decrease by at most one in one move. -/
theorem Step.manhattan_le {n : ℕ} [NeZero n] {B C : Board n} (h : Step B C) :
    manhattan B ≤ manhattan C + 1 := by
  have hd := h.manhattan_delta
  omega

namespace Path

variable {n : ℕ} [NeZero n] {A B : Board n}

/-- Every walk bounds the possible decrease in Manhattan distance. -/
theorem manhattan_le (p : Path A B) : manhattan A ≤ p.length + manhattan B := by
  induction p with
  | nil => simp
  | cons h p ih =>
      have hs := h.manhattan_le
      simp only [length_cons]
      omega

/-- Count moves which increase the Manhattan potential. -/
def inefficientMoves {A B : Board n} : Path A B → ℕ
  | .nil _ => 0
  | .cons (B := C) _ p => p.inefficientMoves + if manhattan A < manhattan C then 1 else 0

/-- Each inefficient move costs exactly two moves beyond the net potential decrease. -/
theorem length_add_manhattan (p : Path A B) :
    p.length + manhattan B = manhattan A + 2 * p.inefficientMoves := by
  induction p with
  | nil => simp [inefficientMoves]
  | @cons A B C h p ih =>
      have hd := h.manhattan_delta
      simp only [length_cons, inefficientMoves]
      split_ifs <;> omega

theorem manhattan_le_solution_length (p : Path A (target n)) : manhattan A ≤ p.length := by
  simpa using p.manhattan_le

theorem solution_length (p : Path A (target n)) :
    p.length = manhattan A + 2 * p.inefficientMoves := by
  simpa using p.length_add_manhattan

end Path

/-- Manhattan distance is a lower bound for the shortest legal solution. -/
theorem manhattan_le_optimalLength {n : ℕ} [NeZero n] (B : ReachableBoard n) :
    manhattan B.val ≤ optimalLength B := by
  obtain ⟨p, hp⟩ := shortest_witness B
  simpa [hp] using p.manhattan_le_solution_length

end SlidingPuzzle
