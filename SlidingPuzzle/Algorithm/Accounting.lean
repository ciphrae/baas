import SlidingPuzzle.Manhattan

/-! Finite accounting for the phase decomposition and the general-size prefix.
These lemmas do not assume or assert the existence of the paper's algorithm. -/
namespace SlidingPuzzle
namespace Path

variable {n : ℕ} [NeZero n] {A B C : Board n}

@[simp] theorem inefficientMoves_append (p : Path A B) (q : Path B C) :
    (p.append q).inefficientMoves = p.inefficientMoves + q.inefficientMoves := by
  induction p with
  | nil => simp [append, inefficientMoves]
  | cons h p ih =>
      simp [append, inefficientMoves, ih, Nat.add_assoc, Nat.add_comm]

theorem inefficientMoves_le_length (p : Path A B) : p.inefficientMoves ≤ p.length := by
  induction p with
  | nil => simp [inefficientMoves]
  | cons h p ih =>
      simp only [inefficientMoves, length_cons]
      split_ifs <;> omega

/-- A solution spends at most half its moves increasing the potential. -/
theorem inefficientMoves_le_half_length (p : Path A (target n)) :
    2 * p.inefficientMoves ≤ p.length := by
  rw [p.solution_length]
  omega

/-- The potential can increase by at most the prefix length. -/
theorem manhattan_end_le (p : Path A B) : manhattan B ≤ manhattan A + p.length := by
  simpa [Nat.add_comm] using p.reverse.manhattan_le

/-- A prefix can contribute twice its length to the additive solution overhead. -/
theorem prefix_solution_bound (p : Path A B) (q : Path B (target n))
    {E : ℕ} (hq : q.length ≤ manhattan B + E) :
    (p.append q).length ≤ manhattan A + 2 * p.length + E := by
  have hpot := p.manhattan_end_le
  rw [length_append]
  omega

/-- A path whose net effect exchanges the blank with one tile changes the
potential by at most the exchange distance, so at most about half its moves
are inefficient. This halves the charge of long restoring jump words. -/
theorem two_inefficientMoves_le_of_blank_swap {c : Cell n}
    (p : Path A (swapCells A (blank A) c)) :
    2 * p.inefficientMoves ≤ p.length + gridDistance (blank A) c := by
  have hp := p.length_add_manhattan
  by_cases hc : c = blank A
  · subst hc
    have hA : swapCells A (blank A) (blank A) = A := by ext x; simp
    have hm : manhattan (swapCells A (blank A) (blank A)) = manhattan A := by rw [hA]
    omega
  · have hbal := manhattan_blank_swap_balance A c hc
    have htri : gridDistance (blank A) (position (target n) (A c)) ≤
        gridDistance (blank A) c + gridDistance c (position (target n) (A c)) := by
      simp only [gridDistance, Nat.dist]
      omega
    omega

end Path

/-- Convert an actual residual solution and a legal prefix into an OPT bound. -/
theorem optimalLength_le_prefix_solution {n : ℕ} [NeZero n]
    (A : ReachableBoard n) {B : Board n} (p : Path A.val B)
    (q : Path B (target n)) {E : ℕ} (hq : q.length ≤ manhattan B + E) :
    optimalLength A ≤ manhattan A.val + 2 * p.length + E :=
  (optimalLength_le_path_length A (p.append q)).trans (p.prefix_solution_bound q hq)

end SlidingPuzzle
