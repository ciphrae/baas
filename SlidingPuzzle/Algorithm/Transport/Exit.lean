import SlidingPuzzle.Algorithm.Accounting
import SlidingPuzzle.Algorithm.Transport.Labels
import SlidingPuzzle.Moves.Jump

/-! Exit a vertical corridor into the selected source reservoir. A single
vertical move, when needed, supplies the parity required by the final jump. -/
namespace SlidingPuzzle.Partition
noncomputable section
open Classical

theorem exists_transport_exit_cell {n k : ℕ} (hk : Dims n k)
    (i j jc : GroupIndex k) (hrowj : groupRow jc = groupRow j) (a b : Cell n)
    (ha : vertical jc i a) (hb : reservoir j b) (hrow : a.1 = b.1) :
    ∃ c : Cell n, vertical jc i c ∧ c.2 = a.2 ∧
      gridDistance a c ≤ 1 ∧
      (c.1.val+c.2.val+b.1.val+b.2.val)%2 = 1 ∧
      Nat.dist c.1.val b.1.val ≤ 1 := by
  have hk3 : k+2 ≤ side n k := hk.k_add_two_le
  let lo := (groupRow j).val*side n k+k
  let hi := ((groupRow j).val+1)*side n k
  have hwidth : lo+2 ≤ hi := by dsimp [lo, hi]; nlinarith
  have har : lo ≤ a.1.val ∧ a.1.val < hi := by
    have h1 := ha.1; have h2 := ha.2.1; rw [hrowj] at h1 h2; exact ⟨h1, h2⟩
  let r := if (a.1.val+a.2.val+b.1.val+b.2.val)%2 = 1 then a.1.val
    else if a.1.val+1 < hi then a.1.val+1 else a.1.val-1
  have hr : lo ≤ r ∧ r < hi ∧ Nat.dist a.1.val r ≤ 1 := by
    dsimp [r, Nat.dist]; split_ifs <;> omega
  have hrn : r < n := by
    dsimp [r]; split_ifs with hp hu
    · exact a.1.isLt
    · have hbrow := b.1.isLt
      have hnhi : hi ≤ n := by
        calc
          hi ≤ k*side n k := Nat.mul_le_mul_right _ (groupRow j).isLt
          _ = n := hk.mul_side
      omega
    · have := a.1.isLt; omega
  let c : Cell n := (⟨r, hrn⟩, a.2)
  refine ⟨c, ⟨by rw [hrowj]; exact hr.1, by rw [hrowj]; exact hr.2.1, ha.2.2⟩, rfl, ?_, ?_, ?_⟩
  · simpa [c, gridDistance] using hr.2.2
  · dsimp [c, r]; split_ifs <;> omega
  · have hv := congrArg Fin.val hrow
    dsimp [c, Nat.dist] at *; omega

/-- After vertical travel reaches the source tile's row, the parity adjustment
and exit jump preserve the transport invariant. The restoring jump is charged
at half its length, so the cost is governed by the column distance. -/
theorem exists_transport_exit_path {n k : ℕ} [NeZero n]
    (hk : Dims n k) (A B : Board n) (hA : Clear (k := k) A)
    (i j : GroupIndex k) (hAB : GroupEquivalent i A B)
    (b : Cell n) (hb : reservoir j b) (ht : A b ∈ targetGroup i) {jc : GroupIndex k}
    (hrowj : groupRow jc = groupRow j)
    (hblank : vertical jc i (blank B)) (hrow : (blank B).1 = b.1) :
    ∃ D : Board n, ∃ p : Path B D,
      blank D = b ∧ GroupEquivalent i A D ∧
      p.inefficientMoves ≤ 13*(Nat.dist (blank B).2.val b.2.val+1)+1 := by
  have hk3 : 1 ≤ side n k := hk.side_pos
  have hn2 : 2 ≤ n := by have := hk.two_le_n; omega
  obtain ⟨c, hc, hcol, hdist, hparity, hrows⟩ :=
    exists_transport_exit_cell hk i j jc hrowj (blank B) b hblank hb hrow
  have hadjust : ∃ C : Board n, ∃ p : Path B C,
      blank C = c ∧ GroupEquivalent i A C ∧ p.length ≤ 1 := by
    by_cases heq : c = blank B
    · exact ⟨B, .nil B, heq.symm, hAB, by simp⟩
    · have hd : gridDistance (blank B) c = 1 := by
        have hz : gridDistance (blank B) c ≠ 0 := by
          intro hz
          have hcell : blank B = c := by
            apply Prod.ext <;> apply Fin.ext <;>
              simp only [gridDistance, Nat.dist] at hz <;> omega
          exact heq hcell.symm
        omega
      refine ⟨swapCells B (blank B) c, movePath B c hd, blank_swapCells B c,
        hAB.trans (groupEquivalent_swap hk B i c ?_), by simp⟩
      exact hAB.mem_targetGroup (hA.2 jc i c hc) heq
  obtain ⟨C, p, hC, hAC, hp⟩ := hadjust
  obtain ⟨q, hq⟩ := exists_horizontal_jump hn2 C b (by simpa [hC] using hrows)
    (by simpa [hC] using hparity)
  have htile : C b ∈ targetGroup i := by
    apply hAC.mem_targetGroup ht
    intro heq
    have hbc : b = c := heq.trans hC
    have hv : vertical jc i b := hbc.symm ▸ hc
    exact vertical_not_reservoir hk hv hb
  refine ⟨swapCells C (blank C) b, p.append q, blank_swapCells C b,
    hAC.trans (groupEquivalent_swap hk C i b htile), ?_⟩
  rw [Path.inefficientMoves_append]
  have hp' := p.inefficientMoves_le_length
  have hcc : (blank C).2 = (blank B).2 := by rw [hC, hcol]
  rw [hcc] at hq
  have hhalf := q.two_inefficientMoves_le_of_blank_swap
  have hd : gridDistance (blank C) b ≤ Nat.dist (blank B).2.val b.2.val+1 := by
    have hr : Nat.dist (blank C).1.val b.1.val ≤ 1 := by rw [hC]; exact hrows
    simp only [gridDistance]
    rw [hcc]
    omega
  omega

end
end SlidingPuzzle.Partition
