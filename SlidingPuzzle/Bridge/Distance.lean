import SlidingPuzzle.Basic
import Zhong.Manhattan

/-! The two developments use definitionally identical cells, boards, and target.
The potential differs only in whether the blank is removed by a filter or an `if`.
This module proves the exact equality before imported distance estimates are used. -/
namespace SlidingPuzzle

variable {n : ℕ} [NeZero n]

theorem manhattan_eq_zhong_D (B : Board n) : manhattan B = Zhong.D B := by
  unfold manhattan Zhong.D Zhong.tileSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : t = 0
  · simp [ht]
  · have hval : t.val ≠ 0 := by
      intro h
      apply ht
      exact Fin.ext h
    simp [ht, hval, gridDistance, Zhong.cellDist, position, Zhong.posOf, target, Zhong.target]

end SlidingPuzzle
