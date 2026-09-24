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

/-- Every reachable board of side at least four has a concrete solution of cubic length. -/
theorem exists_solution_cubic (B : ReachableBoard n) (hn : 4 ≤ n) :
    ∃ p : Path B.val (target n), p.length ≤ 552 * n^3 := by
  obtain ⟨p,hp⟩ := exists_solution_cubic_exact B hn
  refine ⟨p, hp.trans ?_⟩
  have hcube : 4 * n^2 ≤ n^3 := by nlinarith [Nat.mul_le_mul_right (n^2) hn]
  have hpos : 6 ≤ n^3 := by nlinarith [Nat.pow_le_pow_left hn 3]
  nlinarith

/-- On local blocks of side at least eight, the same checked solver has a smaller budget. -/
theorem exists_solution_cubic_large (B : ReachableBoard n) (hn : 8 ≤ n) :
    ∃ p : Path B.val (target n), p.length ≤ 527 * n^3 := by
  obtain ⟨p,hp⟩ := exists_solution_cubic_exact B (by omega)
  refine ⟨p, hp.trans ?_⟩
  have hcube : 8 * n^2 ≤ n^3 := by nlinarith [Nat.mul_le_mul_right (n^2) hn]
  nlinarith

/-- A genuine local solver hypothesis: legal solutions for every reachable
board of side at least eight, with a uniform cubic coefficient. -/
def CubicSolverBound (K : ℕ) : Prop :=
  ∀ {m : ℕ} [NeZero m], 8 ≤ m → ∀ B : ReachableBoard m,
    ∃ p : Path B.val (target m), p.length ≤ K*m^3

/-- The currently implemented solver supplies this instance of the interface. -/
theorem cubicSolverBound_current : CubicSolverBound 527 := by
  intro m _ hm B
  exact exists_solution_cubic_large B hm

/-- The shortest solution of a reachable board of side at least four is cubic. -/
theorem optimalLength_le_cubic (B : ReachableBoard n) (hn : 4 ≤ n) :
    optimalLength B ≤ 552 * n^3 := by
  obtain ⟨p, hp⟩ := exists_solution_cubic B hn
  exact (optimalLength_le_path_length B p).trans hp

/-- A row-placement word becomes a legal path and keeps the already-correct prefix fixed. -/
theorem exists_protected_row_path
    (r : ℕ) (hr : r + 1 < n) (hr2 : r + 2 < n) (hm : 4 ≤ n)
    (lo : ℕ) (hlo : lo + 4 ≤ n) (B : Board n)
    (habove : ∀ (x y : Fin n), x.val < r → B (x, y) = target n (x, y))
    (hcol : ∀ (x y : Fin n), y.val < lo → B (x, y) = target n (x, y)) :
    ∃ (C : Board n) (p : Path B C),
      p.length ≤ (n - lo) * (251 * (n + n)) ∧
      (∀ (x y : Fin n), x.val < r → C (x, y) = B (x, y)) ∧
      (∀ (x y : Fin n), y.val < lo → C (x, y) = B (x, y)) ∧
      (∀ y : Fin n, C ((⟨r, by omega⟩ : Fin n), y) = target n ((⟨r, by omega⟩ : Fin n), y)) := by
  have : NeZero (n * n) := zhong_square_neZero
  obtain ⟨σ, habove', hcol', hrow, hlen⟩ := Zhong.solveRow r hr hr2 hm lo hlo B habove hcol
  obtain ⟨p, hp⟩ := path_of_zhong_word B σ
  refine ⟨Zhong.actSeq B σ, p, hp.trans hlen, ?_, ?_, ?_⟩
  · intro x y hx
    exact (habove' x y hx).trans (habove x y hx).symm
  · intro x y hy
    exact (hcol' x y hy).trans (hcol x y hy).symm
  · exact hrow

/-- A column-placement word becomes a legal path and keeps the already-correct prefix fixed. -/
theorem exists_protected_column_path
    (k : ℕ) (hk : k + 2 < n) (hlo6 : k + 4 ≤ n) (B : Board n)
    (habove : ∀ (x y : Fin n), x.val < k → B (x, y) = target n (x, y))
    (hcol : ∀ (x y : Fin n), y.val < k → B (x, y) = target n (x, y)) :
    ∃ (C : Board n) (p : Path B C),
      p.length ≤ (n - k) * (251 * (n + n)) ∧
      (∀ (x y : Fin n), x.val < k → C (x, y) = B (x, y)) ∧
      (∀ (x y : Fin n), y.val < k → C (x, y) = B (x, y)) ∧
      (∀ x : Fin n, C (x, (⟨k, by omega⟩ : Fin n)) = target n (x, (⟨k, by omega⟩ : Fin n))) := by
  have : NeZero (n * n) := zhong_square_neZero
  obtain ⟨σ, habove', hcol', hcolumn, hlen⟩ := Zhong.solveCol k hk hlo6 B habove hcol
  obtain ⟨p, hp⟩ := path_of_zhong_word B σ
  refine ⟨Zhong.actSeq B σ, p, hp.trans hlen, ?_, ?_, ?_⟩
  · intro x y hx
    exact (habove' x y hx).trans (habove x y hx).symm
  · intro x y hy
    exact (hcol' x y hy).trans (hcol x y hy).symm
  · exact hcolumn

end SlidingPuzzle
