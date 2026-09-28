import SlidingPuzzle.Tree.Transport
import SlidingPuzzle.Algorithm.ResidualPotential
import SlidingPuzzle.Algorithm.ResidualReachability
import SlidingPuzzle.Parberry.Prefix

/-! # The tree algorithm on a board of arbitrary side

Use Parberry's prefix to reduce an arbitrary side `n` to the largest multiple
`k * (n / k)`, then run the tree construction on that residual board. -/
set_option maxRecDepth 4096

namespace SlidingPuzzle.Tree

open SlidingPuzzle

/-- Prefix plus tree construction on the residual board. The tree hypotheses
are all stated at the residual side `k * (n / k)` and grid side `k`. -/
theorem optimalLength_le_tree_residual {n k q la : ℕ} [NeZero n]
    (L : LaneSys k q)
    (td : TDims (k * (n / k)) k (n / k) q)
    (hfit : ∀ Q, resv L (k * (n / k)) (n / k) Q + 2 ≤ ((n / k) - q) * ((n / k) - q))
    (hcap : 76 * k * la ≤ 5 * (n / k))
    (hcA : 2 * (4 * k ^ 2 * q * k * (n / k) ^ 2) ≤ 2 ^ la)
    (hcB : 2 * (4 * k ^ 2 * q * k ^ 2 * (n / k) ^ 2) <
      2 ^ GroupedOrder.lamN (k * (n / k)))
    (B : ReachableBoard n) :
    optimalLength B ≤ manhattan B.val +
      2 * ((15 * n ^ 2 + 3002 * n + 1) * (n - k * (n / k))) +
      2 * treeBound L (k * (n / k)) (n / k) := by
  have hmn : k * (n / k) ≤ n := Nat.mul_div_le n k
  have hroom := td.hd.room
  have hk2 := td.hd.two_le
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
  obtain ⟨qpath, hq⟩ := exists_tree_solution L td hfit hcap hcA hcB A hreachA
  have hlen := qpath.length_add_manhattan
  have hzero : manhattan (target (k * (n / k))) = 0 := by simp [manhattan]
  have hq' : qpath.length ≤ manhattan A + 2 * treeBound L (k * (n / k)) (n / k) := by
    omega
  have h := optimalLength_le_prefix_residual_solution B (n - k * (n / k)) hdn C p hC A hA qpath hq'
  omega

end SlidingPuzzle.Tree
