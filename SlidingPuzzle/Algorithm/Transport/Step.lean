import SlidingPuzzle.Algorithm.Transport.Entry
import SlidingPuzzle.Algorithm.Transport.Realization
import SlidingPuzzle.Algorithm.Transport.Carry

/-! One transfer of Algorithm 4: slide the blank to the top of its reservoir,
enter the horizontal corridor, travel to the vertical corridor, travel
vertically (an explicit parameter, supplied in `Transport.lean`), and exit into
the source reservoir. -/
namespace SlidingPuzzle.Partition
noncomputable section

/-- The vertical stage: start in H_i at the selected source block's
vertical-corridor column, and reach the source tile's row within V_(j,i).
Intermediate boards retain the filled-blank group invariant, not Clear. -/
def VerticalTransportBound {n k : ℕ} [NeZero n] (_hk : Dims n k) (E : ℕ) : Prop :=
  ∀ A B : Board n, Clear (k := k) A → ∀ i j : GroupIndex k,
    GroupEquivalent i A B → horizontal i (blank B) →
    (blank B).2.val = (groupCol j).val*side n k+i.val →
    ∀ b : Cell n, reservoir j b →
    ∃ D : Board n, ∃ p : Path B D,
      vertical j i (blank D) ∧ (blank D).1 = b.1 ∧
      GroupEquivalent i A D ∧ p.inefficientMoves ≤ E

/-- The vertical routing budget `E` adds to `5*s+75*k²+13*k+189`, plus `3*s`
for sources in the rightmost column of squares. The blank first slides to the
top of its own reservoir, which preserves all counts; the entry jump then
crosses only the horizontal corridor rows. The blank descends the vertical
corridor on the nearer side of the source tile: its own square's, or that of the
square to the right. The exit carries the tile to that side of its reservoir, so
it costs at most `3*s` except in the rightmost column. -/
theorem transportStepBound_of_vertical_bound {n k E : ℕ} [NeZero n]
    (hk : Dims n k)
    (hvertical : VerticalTransportBound (n := n) hk E) :
    TransportStepBound (n := n) hk (fun r => 5*side n k+E+75*k^2+13*k+189+
      if (groupCol (transportIndex k hk r)).val+1 = k then 3*side n k else 0) := by
  intro A₀ hA₀ i j hi₀ hchoice₀
  obtain ⟨A, p₀, hA, hi, htop, _, hmat₀, hlen₀⟩ :=
    exists_reservoir_top_path hk A₀ hA₀ _ hi₀
  have hchoice : TransportCounts.Chooses (boardMatrix hk A) i j := by
    rw [hmat₀]; exact hchoice₀
  obtain ⟨b, hb, ht, _hclearSwap, hmatrixSwap⟩ := boardMatrix_choice_endpoint hk A hA i j hi hchoice
  set I := transportIndex k hk i with hI
  set J := transportIndex k hk j with hJ
  have hk2 : k ≤ k^2 := by have := hk.two_le; nlinarith
  have hk3 : k^2 ≤ side n k := by have := hk.sq_add_le; omega
  have hindex : I.val < side n k := (by simpa [pow_two] using I.isLt : I.val < k^2).trans_le hk3
  have hn2 : 2 ≤ n := by have := hk.two_le_n; omega
  -- The exit through a given corridor square, after horizontal and vertical travel.
  have hroute : ∀ (jc : GroupIndex k) (bc : Cell n), reservoir jc bc → bc.1 = b.1 →
      ∀ X : ℕ, (∀ C : Board n, ∀ q : Path A C, GroupEquivalent I A C →
        vertical jc I (blank C) → (blank C).1 = b.1 →
        ∃ D : Board n, ∃ s : Path C D, Clear (k := k) D ∧ reservoir J (blank D) ∧
          boardMatrix hk D = boardMatrix hk (swapCells A (blank A) b) ∧
          s.inefficientMoves ≤ X) →
      ∃ D : Board n, ∃ p : Path A D, Clear (k := k) D ∧ reservoir J (blank D) ∧
        boardMatrix hk D = boardMatrix hk (swapCells A (blank A) b) ∧
        2*p.inefficientMoves ≤ 2*side n k+26*(k+1)+2*E+2*X := by
    intro jc bc hbc hbcrow X hexit
    have hend : ((groupCol jc).val+1)*side n k ≤ n := by
      calc
        _ ≤ k*side n k := Nat.mul_le_mul_right _ (groupCol jc).isLt
        _ = n := hk.mul_side
    let column : Fin n := ⟨(groupCol jc).val*side n k+I.val, by nlinarith⟩
    obtain ⟨B, p, hBH, hcol, hAB, hp⟩ :=
      exists_transport_horizontal_path hk hn2 A hA I hi column
    obtain ⟨C, q, hCV, hrow, hAC, hq⟩ := hvertical A B hA I jc hAB hBH
      (by rw [hcol]) bc hbc
    obtain ⟨D, s, hD, hbD, hmD, hs⟩ := hexit C (p.append q) hAC hCV (hrow.trans hbcrow)
    refine ⟨D, p.append (q.append s), hD, hbD, hmD, ?_⟩
    simp only [Path.inefficientMoves_append]
    have hhi := hi.2.1
    rw [Nat.add_mul, Nat.one_mul] at hhi
    have hgc := (groupCol I).isLt
    have htop' : (blank A).1.val-((groupRow I).val*side n k+(groupCol I).val)+1 ≤ k+1 := by
      omega
    omega
  have hb' := hb
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb'
  simp only [Nat.add_mul, Nat.one_mul] at hb2 hb4
  -- Choose the nearer side.
  have hmain : ∃ D : Board n, ∃ p : Path A D, Clear (k := k) D ∧ reservoir J (blank D) ∧
      boardMatrix hk D = boardMatrix hk (swapCells A (blank A) b) ∧
      2*p.inefficientMoves ≤ 2*side n k+26*(k+1)+2*E+2*(75*k^2+176)+
        6*side n k+(if (groupCol J).val+1 = k then 6*side n k else 0) := by
    by_cases hright : (groupCol J).val+1 < k ∧
        (groupCol J).val*side n k+side n k-b.2.val < b.2.val-(groupCol J).val*side n k
    · let J' : GroupIndex k := finProdFinEquiv (groupRow J, ⟨(groupCol J).val+1, hright.1⟩)
      have hrowJ : groupRow J' = groupRow J := by simp [J', groupRow]
      have hcolJ : (groupCol J').val = (groupCol J).val+1 := by simp [J', groupCol]
      have hend : ((groupCol J').val+1)*side n k ≤ n := by
        calc
          _ ≤ k*side n k := Nat.mul_le_mul_right _ (groupCol J').isLt
          _ = n := hk.mul_side
      simp only [Nat.add_mul, Nat.one_mul] at hend
      let bc : Cell n := (b.1, ⟨(groupCol J').val*side n k+k^2, by omega⟩)
      have hbc : reservoir J' bc := by
        refine ⟨by rw [hrowJ]; exact hb1, by rw [hrowJ, Nat.add_mul, Nat.one_mul]; exact hb2,
          le_rfl, by simp only [bc, Nat.add_mul, Nat.one_mul]; omega⟩
      obtain ⟨D, p, hD, hbD, hmD, hp⟩ := hroute J' bc hbc rfl
        (6*(((groupCol J).val+1)*side n k-b.2.val)+75*k^2+176) (by
          intro C q hAC hCV hrow
          exact exists_transport_exit_right hk A C hA I J J' hrowJ hcolJ hAC b hb ht hCV hrow)
      refine ⟨D, p, hD, hbD, hmD, ?_⟩
      have h6 : 2*(6*(((groupCol J).val+1)*side n k-b.2.val)) ≤ 6*side n k := by
        rw [Nat.add_mul, Nat.one_mul]; omega
      split_ifs <;> omega
    · obtain ⟨D, p, hD, hbD, hmD, hp⟩ := hroute J b hb rfl
        (6*(b.2.val-(groupCol J).val*side n k)+75*k^2+176) (by
          intro C q hAC hCV hrow
          exact exists_transport_exit_left hk A C hA I J hAC b hb ht hCV hrow)
      refine ⟨D, p, hD, hbD, hmD, ?_⟩
      have hgc := (groupCol J).isLt
      split_ifs with hlast
      · omega
      · have h6 : 2*(6*(b.2.val-(groupCol J).val*side n k)) ≤ 6*side n k := by
          have : (groupCol J).val+1 < k := by omega
          have := not_and.mp hright this
          omega
        omega
  obtain ⟨D, p, hD, hblankD, hmD, hp⟩ := hmain
  refine ⟨D, p₀.append p, hD, hblankD, ?_, ?_⟩
  · rw [hmD, hmatrixSwap, hmat₀]
  · simp only [Path.inefficientMoves_append]
    have h₀ := p₀.inefficientMoves_le_length
    have hs := hk.side_pos
    have hres := hi₀.2.1
    have hres' := hi.1
    rw [Nat.add_mul, Nat.one_mul] at hres
    have hrow0 : (groupRow I).val*side n k+k ≤ (blank A).1.val := hi.1
    change p₀.inefficientMoves+p.inefficientMoves ≤ 5*side n k+E+75*k^2+13*k+189+
      (if (groupCol J).val+1 = k then 3*side n k else 0)
    split_ifs at hp ⊢ <;> omega

end
end SlidingPuzzle.Partition

