import SlidingPuzzle.Algorithm.TransportExit
import SlidingPuzzle.Algorithm.TransportRealization
import SlidingPuzzle.Algorithm.ReservoirSlide
import SlidingPuzzle.Algorithm.TransportCarry

/-! Assemble entry, horizontal, and exit paths around a vertical routing bound.
The concrete vertical construction is supplied in `Transport.lean`. -/
namespace SlidingPuzzle.Partition
noncomputable section

/-- The vertical stage: start in H_i at the selected source block's
vertical-corridor column, and reach the source tile's row within V_(j,i).
Intermediate boards retain the filled-blank group invariant, not Clear. -/
def VerticalTransportBound {n k : ℕ} [NeZero n] (_hk : 2 ≤ k) (E : ℕ) : Prop :=
  ∀ A B : Board n, Clear (k := k) A → ∀ i j : GroupIndex k,
    GroupEquivalent i A B → horizontal i (blank B) →
    (blank B).2.val = (groupCol j).val*k^3+i.val →
    ∀ b : Cell n, reservoir j b →
    ∃ D : Board n, ∃ p : Path B D,
      vertical j i (blank D) ∧ (blank D).1 = b.1 ∧
      GroupEquivalent i A D ∧ p.inefficientMoves ≤ E

/-- The vertical routing budget E adds to `8*k³+69*k²+13*k+189`. The blank
first slides to the top of its own reservoir, which preserves all counts; the
entry jump then crosses only the horizontal corridor rows. The exit carries the
source tile to the corridor side of its reservoir; only short jumps remain. -/
theorem transportStepBound_of_vertical_bound {n k E : ℕ} [NeZero n]
    (hk : 2 ≤ k) (hn : n = k^4)
    (hvertical : VerticalTransportBound (n := n) hk E) :
    TransportStepBound (n := n) hk (8*k^3+E+69*k^2+13*k+189) := by
  intro A₀ hA₀ i j hi₀ hchoice₀
  obtain ⟨A, p₀, hA, hi, htop, _, hmat₀, hlen₀⟩ :=
    exists_reservoir_top_path hk A₀ hA₀ _ hi₀
  have hchoice : TransportCounts.Chooses (boardMatrix hk A) i j := by
    rw [hmat₀]; exact hchoice₀
  obtain ⟨b, hb, ht, _hclearSwap, hmatrixSwap⟩ := boardMatrix_choice_endpoint hk A hA i j hi hchoice
  set I := transportIndex k hk i with hI
  set J := transportIndex k hk j with hJ
  have hk2 : k ≤ k^2 := by nlinarith
  have hk3 : k^2 ≤ k^3 := by nlinarith [Nat.mul_le_mul_left k hk2]
  have hindex : I.val < k^3 := (by simpa [pow_two] using I.isLt : I.val < k^2).trans_le hk3
  have hend : ((groupCol J).val+1)*k^3 ≤ n := by
    calc
      _ ≤ k*k^3 := Nat.mul_le_mul_right _ (groupCol J).isLt
      _ = n := by rw [hn]; ring
  let column : Fin n := ⟨(groupCol J).val*k^3+I.val, by nlinarith⟩
  have hn2 : 2 ≤ n := by rw [hn]; nlinarith [Nat.pow_le_pow_left hk 4]
  obtain ⟨B, p, hBH, hcol, hAB, hp⟩ :=
    exists_transport_horizontal_path hk hn2 A hA I hi column
  obtain ⟨C, q, hCV, hrow, hAC, hq⟩ := hvertical A B hA I J hAB hBH
    (by rw [hcol]) b hb
  obtain ⟨D, s, hD, hblankD, hmD, hs⟩ :=
    exists_transport_exit_count hk hn A C hA I J hAC b hb ht hCV hrow
  refine ⟨D, p₀.append (p.append (q.append s)), hD, hblankD, ?_, ?_⟩
  · rw [hmD, hmatrixSwap, hmat₀]
  · simp only [Path.inefficientMoves_append]
    have h₀ := p₀.inefficientMoves_le_length
    have hhi := hi₀.2.1
    rw [Nat.add_mul, Nat.one_mul] at hhi
    have hgc := (groupCol I).isLt
    have htop' : (blank A).1.val-((groupRow I).val*k^3+(groupCol I).val)+1 ≤ k+1 := by
      omega
    omega

/-- The jump-only realization, without normalizing the blank inside its
reservoir: entry and exit are single restoring jumps charged at half length.
Its lower-order terms are smaller, so it serves the legacy uniform contracts. -/
theorem transportStepBound_of_vertical_bound_jump {n k E : ℕ} [NeZero n]
    (hk : 2 ≤ k) (hn : n = k^4)
    (hvertical : VerticalTransportBound (n := n) hk E) :
    TransportStepBound (n := n) hk (27*k^3+E+1) := by
  intro A hA i j hi hchoice
  obtain ⟨b, hb, ht, _hclearSwap, hmatrixSwap⟩ := boardMatrix_choice_endpoint hk A hA i j hi hchoice
  set I := transportIndex k hk i with hI
  set J := transportIndex k hk j with hJ
  have hk2 : k ≤ k^2 := by nlinarith
  have hk3 : k^2 ≤ k^3 := by nlinarith [Nat.mul_le_mul_left k hk2]
  have hindex : I.val < k^3 := (by simpa [pow_two] using I.isLt : I.val < k^2).trans_le hk3
  have hend : ((groupCol J).val+1)*k^3 ≤ n := by
    calc
      _ ≤ k*k^3 := Nat.mul_le_mul_right _ (groupCol J).isLt
      _ = n := by rw [hn]; ring
  let column : Fin n := ⟨(groupCol J).val*k^3+I.val, by nlinarith⟩
  have hn2 : 2 ≤ n := by rw [hn]; nlinarith [Nat.pow_le_pow_left hk 4]
  obtain ⟨B, p, hBH, hcol, hAB, hp⟩ := exists_transport_horizontal_path hk hn2 A hA I hi column
  obtain ⟨C, q, hCV, hrow, hAC, hq⟩ := hvertical A B hA I J hAB hBH
    (by rw [hcol]) b hb
  obtain ⟨D, s, hD, hAD, hs⟩ := exists_transport_exit_path hk hn A C hA I J hAC b hb ht hCV hrow
  have hblankD : reservoir J (blank D) := by rwa [hD]
  refine ⟨D, p.append (q.append s), hAD.clear hk hA hblankD, hblankD, ?_, ?_⟩
  · rw [hAD.boardMatrix_eq_swap hk I A D b ht hD]
    exact hmatrixSwap
  · simp only [Path.inefficientMoves_append]
    have hhi := hi.2.1
    rw [Nat.add_mul, Nat.one_mul] at hhi
    have hrowd : (blank A).1.val-((groupRow I).val*k^3+(groupCol I).val)+1 ≤ k^3 := by
      omega
    have hccol : (blank C).2.val = (groupCol J).val*k^3+I.val := hCV.2.2
    have hb4 := hb.2.2.2
    have hb3 := hb.2.2.1
    rw [Nat.add_mul, Nat.one_mul] at hb4
    have hcold : Nat.dist (blank C).2.val b.2.val+1 ≤ k^3 := by
      simp only [Nat.dist]; omega
    omega

end
end SlidingPuzzle.Partition

namespace SlidingPuzzle.Algorithm
open SlidingPuzzle.Partition

/-- A uniform vertical-stage bound completes Transport with the already
constructed entry/horizontal/exit overhead. The vertical bound remains an
explicit hypothesis. -/
theorem transportContract_of_vertical_bound (C : ℕ)
    (hvertical : ∀ k : ℕ, ∀ hk : 2 ≤ k,
      letI : NeZero (k^4) := ⟨by positivity⟩
      VerticalTransportBound (n := k^4) hk (C*k^3)) : TransportContract (70+C) := by
  apply transportContract_of_step_bound
  intro k hk
  let : NeZero (k^4) := ⟨by positivity⟩
  have hstep := transportStepBound_of_vertical_bound hk rfl (hvertical k hk)
  apply hstep.mono hk
  have hk3 : 4*k ≤ k^3 := by nlinarith [Nat.mul_le_mul_right k (Nat.pow_le_pow_left hk 2)]
  have hk2 : 2*k^2 ≤ k^3 := by nlinarith [Nat.mul_le_mul_right (k^2) hk]
  have hk8 : 8 ≤ k^3 := by nlinarith [Nat.pow_le_pow_left hk 3]
  nlinarith

end SlidingPuzzle.Algorithm
