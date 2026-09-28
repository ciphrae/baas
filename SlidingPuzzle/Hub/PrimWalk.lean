import SlidingPuzzle.Moves.Jump
import SlidingPuzzle.Moves.Local
import SlidingPuzzle.Algorithm.Accounting

/-! # Swap walks with an inefficiency count

A *swap walk* moves the blank along cells `f 0, f 1, …, f d`, where every step
is a blank/tile swap realized by some path (a single move or a jump). Every
tile on the line moves back by one cell and nothing else changes. The
inefficient moves are bounded step by step, by a cost depending on the tile
moved in that step. -/
namespace SlidingPuzzle.Hub

variable {n : ℕ} [NeZero n]

/-- The cost of one move from `x` to `y` (the blank goes to `y`, the tile `T`
goes to `x`): `0` if `T` gets closer to its target, else `1`. -/
noncomputable def moveCost (x y : Cell n) (T : Tile n) : ℕ :=
  if gridDistance x (position (target n) T) + 1 = gridDistance y (position (target n) T)
  then 0 else 1

omit [NeZero n] in
theorem moveCost_le_one (x y : Cell n) (T : Tile n) : moveCost x y T ≤ 1 := by
  unfold moveCost; split_ifs <;> omega

/-- A single move, with its inefficiency given by `moveCost`. -/
theorem exists_move_step (B : Board n) (y : Cell n) (hy : gridDistance (blank B) y = 1) :
    ∃ p : Path B (swapCells B (blank B) y),
      p.inefficientMoves ≤ moveCost (blank B) y (B y) := by
  refine ⟨movePath B y hy, ?_⟩
  have hne : y ≠ blank B := by
    intro h; rw [h] at hy; simp at hy
  have hbal := manhattan_blank_swap_balance B y hne
  simp only [movePath, Step.toPath, Path.inefficientMoves]
  unfold moveCost
  split_ifs <;> omega

/-- A vertical jump moves one tile, so at most about half its `13(d+1)` moves
are inefficient. -/
theorem exists_vjump_step (hn : 2 ≤ n) (B : Board n) (y : Cell n)
    (hcol : Nat.dist (blank B).2.val y.2.val ≤ 1)
    (hcolor : ((blank B).1.val + (blank B).2.val + y.1.val + y.2.val) % 2 = 1) :
    ∃ p : Path B (swapCells B (blank B) y),
      p.inefficientMoves ≤ 7 * (Nat.dist (blank B).1.val y.1.val + 1) := by
  obtain ⟨p, hp⟩ := exists_vertical_jump hn B y hcol hcolor
  have h := p.two_inefficientMoves_le_of_blank_swap
  have hg : gridDistance (blank B) y ≤ Nat.dist (blank B).1.val y.1.val + 1 := by
    unfold gridDistance; omega
  exact ⟨p, by omega⟩

/-- A horizontal jump moves one tile, so at most about half its `13(d+1)` moves
are inefficient. -/
theorem exists_hjump_step (hn : 2 ≤ n) (B : Board n) (y : Cell n)
    (hrow : Nat.dist (blank B).1.val y.1.val ≤ 1)
    (hcolor : ((blank B).1.val + (blank B).2.val + y.1.val + y.2.val) % 2 = 1) :
    ∃ p : Path B (swapCells B (blank B) y),
      p.inefficientMoves ≤ 7 * (Nat.dist (blank B).2.val y.2.val + 1) := by
  obtain ⟨p, hp⟩ := exists_horizontal_jump hn B y hrow hcolor
  have h := p.two_inefficientMoves_le_of_blank_swap
  have hg : gridDistance (blank B) y ≤ Nat.dist (blank B).2.val y.2.val + 1 := by
    unfold gridDistance; omega
  exact ⟨p, by omega⟩

/-- Swap walk along `f 0, …, f d`. -/
theorem exists_swap_walk (d : ℕ) (f : ℕ → Cell n) (cost : ℕ → Tile n → ℕ)
    (hinj : ∀ t t', t ≤ d → t' ≤ d → f t = f t' → t = t')
    (hstep : ∀ t, t < d → ∀ B' : Board n, blank B' = f t →
      ∃ p : Path B' (swapCells B' (blank B') (f (t+1))),
        p.inefficientMoves ≤ cost t (B' (f (t+1))))
    (B : Board n) (hb : blank B = f 0) :
    ∃ C : Board n, ∃ p : Path B C, blank C = f d ∧
      (∀ t, t < d → C (f t) = B (f (t+1))) ∧
      (∀ x, (∀ t, t ≤ d → x ≠ f t) → C x = B x) ∧
      p.inefficientMoves ≤ ∑ t ∈ Finset.range d, cost t (B (f (t+1))) := by
  induction d generalizing f cost B with
  | zero =>
    exact ⟨B, .nil B, hb, fun t ht => by omega, fun _ _ => rfl,
      by simp [Path.inefficientMoves]⟩
  | succ d ih =>
    obtain ⟨p1, hp1⟩ := hstep 0 (by omega) B hb
    let B1 := swapCells B (blank B) (f 1)
    have hb1 : blank B1 = f (0+1) := blank_swapCells B _
    obtain ⟨C, q, hbC, hC, hfix, hq⟩ := ih (fun t => f (t+1)) (fun t => cost (t+1))
      (fun t t' ht ht' h => by have := hinj (t+1) (t'+1) (by omega) (by omega) h; omega)
      (fun t ht B' hB' => hstep (t+1) (by omega) B' hB') B1 hb1
    have hne : ∀ t, 1 ≤ t → t ≤ d+1 → f t ≠ f 0 := fun t h1 h2 h => by
      have := hinj t 0 h2 (by omega) h; omega
    have hB1 : ∀ x, x ≠ f 0 → x ≠ f 1 → B1 x = B x := fun x h1 h2 =>
      swapCells_preserves B (by rw [hb]; exact h1) h2
    refine ⟨C, p1.append q, hbC, ?_, ?_, ?_⟩
    · intro t ht
      rcases Nat.eq_zero_or_pos t with rfl | ht0
      · have : C (f 0) = B1 (f 0) := hfix (f 0) (fun t' ht' h => hne (t'+1) (by omega)
          (by omega) h.symm)
        rw [this]
        change swapCells B (blank B) (f 1) (f 0) = _
        rw [← hb, swapCells_at_left]
      · have h := hC (t-1) (by omega)
        simp only [show t - 1 + 1 = t by omega] at h
        rw [h]
        apply hB1
        · exact hne (t+1) (by omega) (by omega)
        · intro h'
          have := hinj (t+1) 1 (by omega) (by omega) h'
          omega
    · intro x hx
      rw [hfix x (fun t ht h => hx (t+1) (by omega) h)]
      exact hB1 x (hx 0 (by omega)) (hx 1 (by omega))
    · rw [Path.inefficientMoves_append, Finset.sum_range_succ']
      have hsum : ∑ t ∈ Finset.range d, cost (t+1) (B1 (f (t+1+1))) =
          ∑ t ∈ Finset.range d, cost (t+1) (B (f (t+1+1))) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.mem_range] at ht
        rw [hB1 _ (hne (t+2) (by omega) (by omega))
          (fun h => by have := hinj (t+2) 1 (by omega) (by omega) h; omega)]
      have hp1' : p1.inefficientMoves ≤ cost 0 (B (f (0+1))) := hp1
      rw [hsum] at hq
      omega

end SlidingPuzzle.Hub
