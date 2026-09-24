import SlidingPuzzle.Algorithm.Parberry.ConstructedPrefix
import SlidingPuzzle.Algorithm.PreparationVertical
import SlidingPuzzle.Algorithm.PhaseStates
import SlidingPuzzle.Algorithm.Accounting
import SlidingPuzzle.Algorithm.ResidualPotential
import SlidingPuzzle.Algorithm.ResidualReachability
import SlidingPuzzle.Moves.Relabel
import SlidingPuzzle.Algorithm.Dimension
import SlidingPuzzle.Proposition9Reduction
import SlidingPuzzle.Algorithm.ArrangementVertical
import SlidingPuzzle.Algorithm.ArrangementHorizontal
import SlidingPuzzle.Moves.BorrowedSolve
import SlidingPuzzle.Moves.BlockCorner
import SlidingPuzzle.Moves.Exchange
import SlidingPuzzle.Algorithm.SquareGeometry
import SlidingPuzzle.Algorithm.FinishAccess
import SlidingPuzzle.Algorithm.Transport
import SlidingPuzzle.Moves.Placement
import Zhong.Algorithm.TwoByTwo

/-! Unconditional approximation bounds using the constructed Parberry solver
and protected prefix. These retain their explicit lower-order costs; they do
not invoke the stronger conditional coefficient-five contracts. -/
namespace SlidingPuzzle.Algorithm
open SlidingPuzzle.Partition

/-- The size-reduction prefix has leading inefficiency coefficient sixty.
Its boundary costs have strictly smaller exponents. -/
theorem parberry_reduction_budget {n k : ℕ} (hlo : k^4 ≤ n) (hhi : n < (k+1)^4) :
    ((15*n^2+3002*n+1)*(n-k^4) : ℕ) ≤
      (60*Real.rpow (n : ℝ) (11/4 : ℝ)+
        12008*Real.rpow (n : ℝ) (7/4 : ℝ)+4*Real.rpow (n : ℝ) (3/4 : ℝ) : ℝ) := by
  have hwidth := outer_layer_width_le_rpow hlo hhi
  have hmul := mul_le_mul_of_nonneg_left hwidth
    (by positivity : (0 : ℝ) ≤ 15*(n : ℝ)^2+3002*n+1)
  have h2 : Real.rpow (n : ℝ) (3/4 : ℝ)*(n : ℝ)^2 =
      Real.rpow (n : ℝ) (11/4 : ℝ) := by
    convert (Real.rpow_add_of_nonneg (Nat.cast_nonneg n)
      (by norm_num : (0 : ℝ) ≤ 3/4) (by norm_num : (0 : ℝ) ≤ 2)).symm using 1 <;>
      norm_num [Real.rpow_natCast]
  have h1 : Real.rpow (n : ℝ) (3/4 : ℝ)*(n : ℝ) =
      Real.rpow (n : ℝ) (7/4 : ℝ) := by
    convert (Real.rpow_add_of_nonneg (Nat.cast_nonneg n)
      (by norm_num : (0 : ℝ) ≤ 3/4) (by norm_num : (0 : ℝ) ≤ 1)).symm using 1 <;>
      norm_num
  push_cast
  nlinarith [h1,h2]

end SlidingPuzzle.Algorithm
