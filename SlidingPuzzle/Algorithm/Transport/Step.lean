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

/-- The vertical routing budget E adds to `8*k³+69*k²+13*k+189`. The blank
first slides to the top of its own reservoir, which preserves all counts; the
entry jump then crosses only the horizontal corridor rows. The exit carries the
source tile to the corridor side of its reservoir; only short jumps remain. -/
theorem transportStepBound_of_vertical_bound {n k E : ℕ} [NeZero n]
    (hk : Dims n k)
    (hvertical : VerticalTransportBound (n := n) hk E) :
    TransportStepBound (n := n) hk (8*side n k+E+69*k^2+13*k+189) := by
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
  have hend : ((groupCol J).val+1)*side n k ≤ n := by
    calc
      _ ≤ k*side n k := Nat.mul_le_mul_right _ (groupCol J).isLt
      _ = n := hk.mul_side
  let column : Fin n := ⟨(groupCol J).val*side n k+I.val, by nlinarith⟩
  have hn2 : 2 ≤ n := by have := hk.two_le_n; omega
  obtain ⟨B, p, hBH, hcol, hAB, hp⟩ :=
    exists_transport_horizontal_path hk hn2 A hA I hi column
  obtain ⟨C, q, hCV, hrow, hAC, hq⟩ := hvertical A B hA I J hAB hBH
    (by rw [hcol]) b hb
  obtain ⟨D, s, hD, hblankD, hmD, hs⟩ :=
    exists_transport_exit_count hk A C hA I J hAC b hb ht hCV hrow
  refine ⟨D, p₀.append (p.append (q.append s)), hD, hblankD, ?_, ?_⟩
  · rw [hmD, hmatrixSwap, hmat₀]
  · simp only [Path.inefficientMoves_append]
    have h₀ := p₀.inefficientMoves_le_length
    have hhi := hi₀.2.1
    rw [Nat.add_mul, Nat.one_mul] at hhi
    have hgc := (groupCol I).isLt
    have htop' : (blank A).1.val-((groupRow I).val*side n k+(groupCol I).val)+1 ≤ k+1 := by
      omega
    omega

end
end SlidingPuzzle.Partition

