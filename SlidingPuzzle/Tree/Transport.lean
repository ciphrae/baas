import SlidingPuzzle.Tree.RunMain
import SlidingPuzzle.Tree.Preload
import SlidingPuzzle.Hub.Cleanup
import SlidingPuzzle.Hub.FinishGen

/-! # The tree algorithm on a board of side `k*s`

Normalize the blank, preload the home tiles every square needs as reserve, run
the abstract transport on the board's abstraction and realize it, clean up, and
finish every square with Parberry's solver. -/
namespace SlidingPuzzle.Tree
open Finset
open SlidingPuzzle.Hub (Sq sqOf classOf reservoir misplaced exists_normalize exists_cleanup
  exists_finish)

variable {n k s q : ℕ} (L : LaneSys k q)

/-- The reserve of every square. -/
noncomputable def resv (n s : ℕ) : Sq k → ℕ :=
  Rneed L s (GroupedOrder.lamN n) (regionSize (n := n) L s)

/-- The bound of the whole algorithm on a board of side `n = k*s`. -/
noncomputable def treeBound (n s : ℕ) : ℕ :=
  2 * n + 52 * n * (∑ Q, resv L n s Q) +
    runCost n k q s L.depth (laneCells L s) (∑ v, needAt L s (GroupedOrder.lamN n) v) +
    (26 * n * ((laneCells L s + ((∑ v, needAt L s (GroupedOrder.lamN n) v) +
      ((∑ Q, resv L n s Q) + laneCells L s))) + 2 * n + 5) +
      (k ^ 2 * (5 * s ^ 3 + 1509 * s ^ 2 + 1505 * s + 4796) + 9354 * k ^ 2 * n)) / 2

theorem regionSize_le (td : TDims n k s q) (Q : Sq k) : regionSize (n := n) L s Q ≤ s ^ 2 := by
  classical
  have h := Hub.LayoutFacts.card_square (n := n) td.hd Q (fun _ _ => True)
  rw [filter_true_of_mem (fun _ _ => trivial), card_product, card_range] at h
  unfold regionSize
  rw [sq, ← h]
  apply card_le_card
  intro x hx
  simp only [mem_filter, mem_univ, true_and] at hx ⊢
  exact ⟨hx.1, hx.2.1, trivial⟩

theorem sum_regionSize [NeZero n] (td : TDims n k s q) :
    ∑ Q, (s ^ 2 - regionSize (n := n) L s Q) = laneCells L s := by
  classical
  have hc := count_decomp L td (fun _ : Cell n => True)
  have hn : #(univ : Finset (Cell n)) = k ^ 2 * s ^ 2 := by
    rw [card_univ, Fintype.card_prod, Fintype.card_fin, ← td.mul]; ring
  have hU : (univ.filter fun _ : Cell n => True) = univ := by ext; simp
  rw [hU, hn] at hc
  simp only [and_true] at hc
  have hrow : ∀ H : LaneI k q, #((range (rowLen L s H)).filter fun _ => True) = rowLen L s H := by
    intro H; simp
  have hcol : ∀ V : LaneI k q, #((range (colLen L s V)).filter fun _ => True) = colLen L s V := by
    intro V; simp
  simp only [hrow, hcol] at hc
  have hle := fun Q => regionSize_le L td Q
  have e1 : ∑ Q : Sq k, (s ^ 2 - regionSize (n := n) L s Q) + ∑ Q : Sq k, regionSize (n := n) L s Q =
      k ^ 2 * s ^ 2 := by
    rw [← sum_add_distrib]
    rw [Finset.sum_congr rfl fun Q _ => Nat.sub_add_cancel (hle Q)]
    simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul]; ring
  unfold laneCells
  unfold regionSize at e1 ⊢
  omega

theorem exists_tree_solution [NeZero n] (td : TDims n k s q)
    (hfit : ∀ Q, resv L n s Q + 2 ≤ (s - q) * (s - q))
    {la : ℕ} (hcap : 76 * k * la ≤ 5 * s)
    (hcA : 2 * (4 * k ^ 2 * q * k * s ^ 2) ≤ 2 ^ la)
    (hcB : 2 * (4 * k ^ 2 * q * k ^ 2 * s ^ 2) < 2 ^ GroupedOrder.lamN n)
    (B : Board n) (hB : Reachable B) :
    ∃ p : Path B (target n), p.inefficientMoves ≤ treeBound L n s := by
  obtain ⟨B1, p1, hb1, hp1⟩ := exists_normalize td.hd B
  set R := resv L n s with hRdef
  obtain ⟨B2, p2, hbl2, hR2, hp2⟩ := exists_preload L td R hfit (deficit L td R B1) B1 rfl hb1
  have hb2 : reservoir k s (sqOf td.hd (blank B2)) (blank B2) := by rw [hbl2]; exact hb1
  have hdef : deficit L td R B1 ≤ ∑ Q, R Q := sum_le_sum fun Q _ => Nat.sub_le _ _
  have hR1 := rel_absState L td B2 hb2
  obtain ⟨es, hv, hcost, hoff⟩ := exists_valid_run L td (absState L td.hd B2) (regionSize L s)
    (absState_regionTotal L td B2 hb2) (absState_classTotal L td B2 hb2)
    (regionSize_le L td) (le_of_eq (sum_regionSize L td)) R (fun Q => hR2 Q) (fun Q => le_rfl)
    hcap hcA hcB
  obtain ⟨B3, p3, hR3, hp3⟩ := simulate_run L td hR1 hv
  have hmis := misplaced_le_of_rel L td hR3
  obtain ⟨B4, p4, hsorted, hlast, hp4⟩ := exists_cleanup td.hd B3
  have hreach : Reachable B4 := by
    obtain ⟨p⟩ := hB
    exact ⟨(((p.append p1).append p2).append p3).append p4⟩
  obtain ⟨p5, hp5⟩ := exists_finish td.hd parberrySolverCost B4 hreach hsorted hlast
  refine ⟨((p1.append p2).append p3).append (p4.append p5), ?_⟩
  simp only [Path.inefficientMoves_append]
  have h2 : p2.inefficientMoves ≤ 52 * n * ∑ Q, R Q :=
    p2.inefficientMoves_le_length.trans (hp2.trans (Nat.mul_le_mul_left _ hdef))
  have h4 : p4.length ≤ 26 * n * ((laneCells L s + ((∑ v, needAt L s (GroupedOrder.lamN n) v) +
      ((∑ Q, R Q) + laneCells L s))) + 2 * n + 5) := by
    refine hp4.trans (Nat.mul_le_mul_left _ ?_)
    omega
  have h45 := (p4.append p5).inefficientMoves_le_half_length
  rw [Path.length_append, Path.inefficientMoves_append] at h45
  have hhalf : p4.inefficientMoves + p5.inefficientMoves ≤
      (26 * n * ((laneCells L s + ((∑ v, needAt L s (GroupedOrder.lamN n) v) +
        ((∑ Q, R Q) + laneCells L s))) + 2 * n + 5) +
        (k ^ 2 * (5 * s ^ 3 + 1509 * s ^ 2 + 1505 * s + 4796) + 9354 * k ^ 2 * n)) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    omega
  unfold treeBound
  rw [← hRdef]
  omega

end SlidingPuzzle.Tree
