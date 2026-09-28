import SlidingPuzzle.Hub.Simulate
import SlidingPuzzle.Hub.Run
import SlidingPuzzle.Hub.Cleanup
import SlidingPuzzle.Hub.FinishGen

/-! # The hub algorithm on a board of side `k*s`

Normalize the blank, run the abstract transport on the board's abstraction
and realize it, clean up, and finish every square with Parberry's solver. Cleanup
and Finish together end at the target, so at most half of their moves are
inefficient. -/
namespace SlidingPuzzle.Hub

variable {n k s : ℕ}

/-- The bound of the whole algorithm on a board of side `n = k*s`. Cleanup and
Finish end at the target, so they are charged half their length. -/
def hubBound (n k s : ℕ) : ℕ :=
  2 * n + transportBound n k s +
    (26 * n * (k ^ 2 * sqCorridor k s + misplacedBound n k + 2 * n + 5) +
      (k ^ 2 * (5 * s ^ 3 + 1509 * s ^ 2 + 1505 * s + 4796) + 9354 * k ^ 2 * n)) / 2

theorem exists_hub_solution (hd : HDims n k s) [NeZero n]
    (hk50 : 50 ≤ k) (hP1 : 76 * k * lamA k s ≤ 5 * s) (B : Board n) (hB : Reachable B) :
    ∃ p : Path B (target n), p.inefficientMoves ≤ hubBound n k s := by
  obtain ⟨B1, p1, hb1, hp1⟩ := exists_normalize hd B
  have hR1 := rel_absState hd B1 hb1
  obtain ⟨es, hv, hcost, hoff⟩ := exists_valid_run hd hk50 hP1 (absState hd B1)
    (absState_regionTotal hd B1 hb1) (absState_classTotal hd B1 hb1)
  obtain ⟨B2, p2, hR2, hp2⟩ := simulate_run hd hR1 hv
  have hmis := misplaced_le_of_rel hd hR2
  obtain ⟨B3, p3, hsorted, hlast, hp3⟩ := exists_cleanup hd B2
  have hreach : Reachable B3 := by
    obtain ⟨q⟩ := hB
    exact ⟨((q.append p1).append p2).append p3⟩
  obtain ⟨p4, hp4⟩ := exists_finish hd parberrySolverCost B3 hreach hsorted hlast
  refine ⟨(p1.append p2).append (p3.append p4), ?_⟩
  simp only [Path.inefficientMoves_append]
  have h3 : p3.length ≤
      26 * n * (k ^ 2 * sqCorridor k s + misplacedBound n k + 2 * n + 5) := by
    refine hp3.trans (Nat.mul_le_mul_left _ ?_)
    omega
  have h34 := (p3.append p4).inefficientMoves_le_half_length
  rw [Path.length_append, Path.inefficientMoves_append] at h34
  have hhalf : p3.inefficientMoves + p4.inefficientMoves ≤
      (26 * n * (k ^ 2 * sqCorridor k s + misplacedBound n k + 2 * n + 5) +
        (k ^ 2 * (5 * s ^ 3 + 1509 * s ^ 2 + 1505 * s + 4796) + 9354 * k ^ 2 * n)) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    omega
  unfold hubBound
  omega

end SlidingPuzzle.Hub
