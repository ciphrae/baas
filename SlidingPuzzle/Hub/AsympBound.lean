import SlidingPuzzle.Hub.AsympAccounting
import SlidingPuzzle.Algorithm.ResidualPotential
import SlidingPuzzle.Algorithm.ResidualReachability
import SlidingPuzzle.Parberry.Prefix

/-! # The hub algorithm on a board of arbitrary side

For a board of side `n` and a grid `k`, the Parberry prefix solves the outer
`n - k*⌊n/k⌋ < k` rows and columns, and `exists_hub_solution` solves the
`k*⌊n/k⌋` residual board (`optimalLength_le_hub_residual`). The residual board
is reachable and its Manhattan distance equals the original board's after the
prefix. The choice of the grid is in `Hub/LinBound.lean`. -/
set_option maxRecDepth 4096

namespace SlidingPuzzle.Hub

open SlidingPuzzle

/-- The smallest side covered by the explicit bounds. -/
def hubN : ℕ := 4096

/-- Prefix plus hub on the residual board. -/
theorem optimalLength_le_hub_residual {n k : ℕ} [NeZero n] (B : ReachableBoard n)
    (hd : HDims (k * (n / k)) k (n / k))
    (hP1 : 48 * k * (Nat.log 2 (k * (n / k)) + 1) ≤ n / k) (hks2 : 8 * k ^ 2 ≤ n / k) :
    optimalLength B ≤ manhattan B.val + 2 * ((15 * n ^ 2 + 3002 * n + 1) * (n - k * (n / k))) +
      2 * hubBound (k * (n / k)) k (n / k) := by
  have hmn : k * (n / k) ≤ n := Nat.mul_div_le n k
  have hroom := hd.room
  have hk2 := hd.two_le
  have hm4 : 4 ≤ k * (n / k) := by
    calc 4 ≤ n / k := by omega
      _ ≤ k * (n / k) := Nat.le_mul_of_pos_left _ (by omega)
  let : NeZero (k * (n / k)) := ⟨by omega⟩
  obtain ⟨C, p, hp, hC⟩ := Parberry.exists_prefix B.val (n - k * (n / k)) (by omega)
  have hdn : n - k * (n / k) + k * (n / k) = n := Nat.sub_add_cancel hmn
  obtain ⟨A, hA⟩ := exists_residual_board (n - k * (n / k)) hdn C hC
  have hreachC : Reachable C := by
    obtain ⟨r⟩ := B.property
    exact ⟨r.append p⟩
  have hreachA : Reachable A :=
    residual_reachable (by omega : 2 ≤ k * (n / k)) (n - k * (n / k)) hdn C hC A hA hreachC
  obtain ⟨q, hq⟩ := exists_hub_solution hd hP1 hks2 A hreachA
  have hlen := q.solution_length
  have hq' : q.length ≤ manhattan A + 2 * hubBound (k * (n / k)) k (n / k) := by omega
  have h := optimalLength_le_prefix_residual_solution B (n - k * (n / k)) hdn C p hC A hA q hq'
  omega

end SlidingPuzzle.Hub
