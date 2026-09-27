import SlidingPuzzle.Hub.Simulate
import SlidingPuzzle.Hub.Run
import SlidingPuzzle.Hub.Cleanup
import SlidingPuzzle.Hub.FinishGen

/-! # The hub algorithm on a board of side `k*s`

Normalize the blank, run the abstract transport on the board's abstraction
and realize it, clean up, and finish every square with Parberry's solver. -/
namespace SlidingPuzzle.Hub

variable {n k s : ℕ}

/-- The bound of the whole algorithm on a board of side `n = k*s`. -/
def hubBound (n k s : ℕ) : ℕ :=
  2 * n + transportBound n k s +
    508 * n * (k ^ 2 * sqCorridor k s + misplacedBound n k + 2 * n + 1) +
    (k ^ 2 * (5 * s ^ 3 + 1509 * s ^ 2 + 1505 * s + 4796) + 9354 * k ^ 2 * n)

theorem exists_hub_solution (hd : HDims n k s) [NeZero n]
    (hP1 : 25 * k * (Nat.log 2 n + 1) ≤ s) (hsk : s ≤ k ^ 3) (B : Board n) (hB : Reachable B) :
    ∃ p : Path B (target n), p.inefficientMoves ≤ hubBound n k s := by
  obtain ⟨B1, p1, hb1, hp1⟩ := exists_normalize hd B
  have hR1 := rel_absState hd B1 hb1
  obtain ⟨es, hv, hcost, hoff⟩ := exists_valid_run hd hP1 hsk (absState hd B1)
    (absState_regionTotal hd B1 hb1) (absState_classTotal hd B1 hb1)
  obtain ⟨B2, p2, hR2, hp2⟩ := simulate_run hd hR1 hv
  have hmis := misplaced_le_of_rel hd hR2
  obtain ⟨B3, p3, hsorted, hlast, hp3⟩ := exists_cleanup hd B2
  have hreach : Reachable B3 := by
    obtain ⟨q⟩ := hB
    exact ⟨((q.append p1).append p2).append p3⟩
  obtain ⟨p4, hp4⟩ := exists_finish hd parberrySolverCost B3 hreach hsorted hlast
  refine ⟨((p1.append p2).append p3).append p4, ?_⟩
  simp only [Path.inefficientMoves_append]
  have h3 : p3.inefficientMoves ≤
      508 * n * (k ^ 2 * sqCorridor k s + misplacedBound n k + 2 * n + 1) := by
    refine hp3.trans (Nat.mul_le_mul_left _ ?_)
    omega
  unfold hubBound
  omega

end SlidingPuzzle.Hub
