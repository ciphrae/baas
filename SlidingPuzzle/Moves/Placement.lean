import SlidingPuzzle.Bridge.Words
import Zhong.Algorithm.Strip2

namespace SlidingPuzzle

variable {n : ℕ} [NeZero n]

private theorem zhong_square_neZero : NeZero (n * n) :=
  ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne n)⟩

private theorem zhong_solveBoard_exact (n : ℕ) (hn : 4 ≤ n) :
    (n - 2) * (n * (251 * (n + n))) + (n * (600 * (n + n)) + 6) =
      502 * n^3 + 196 * n^2 + 6 := by
  have hsub : n - 2 + 2 = n := Nat.sub_add_cancel (by omega)
  have hmul := congrArg (fun t : ℕ => t * (n * (251 * (n + n)))) hsub
  nlinarith [hmul]

/-- Exact polynomial cost of the checked row-by-row solver. -/
theorem exists_solution_cubic_exact (B : ReachableBoard n) (hn : 4 ≤ n) :
    ∃ p : Path B.val (target n),
      p.length ≤ 502 * n^3 + 196 * n^2 + 6 := by
  have : NeZero (n * n) := zhong_square_neZero
  change ∃ p : Path B.val (Zhong.target n n),
    p.length ≤ 502 * n^3 + 196 * n^2 + 6
  obtain ⟨p⟩ := exists_solution B
  obtain ⟨σ, hσ, hlen⟩ := Zhong.solveBoard B.val (by omega) hn
    (zhong_reachable_of_path p)
  have hex : ∃ q : Path B.val (Zhong.target n n), q.length ≤ σ.length := by
    have hx := path_of_zhong_word B.val σ
    rw [hσ] at hx
    exact hx
  obtain ⟨q, hq⟩ := hex
  exact ⟨q, hq.trans (hlen.trans_eq (zhong_solveBoard_exact n hn))⟩

end SlidingPuzzle
