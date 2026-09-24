import SlidingPuzzle.Algorithm.TransportVerticalSchedule
import SlidingPuzzle.Algorithm.TransportStep

/-! Concrete vertical transport in both directions and the completed Transport
contract. Only the initial good interval can incur inefficient ordinary slides;
the intervening horizontal bands are crossed by bounded group-preserving jumps. -/

namespace SlidingPuzzle.Partition
noncomputable section
open Classical

private theorem rev_sum {m : ℕ} (x : Fin m) : x.val+x.rev.val+1 = m := by
  simp only [Fin.val_rev]
  omega

private theorem vertical_of_rank {n k : ℕ} (_hk : 2 ≤ k) (hn : n = k*k^3)
    (i j : GroupIndex k) (backwards : Bool) (column x : Fin n)
    (hcol : column.val = (groupCol j).val*k^3+i.val) (r : Fin k)
    (hlo : r.val*k^3+(if backwards then 0 else k) ≤ x.val)
    (hhi : x.val < (r.val+1)*k^3-(if backwards then k else 0)) :
    ∃ l : GroupIndex k, vertical l i (corridorCell true backwards column x) := by
  let row := if backwards then r.rev else r
  refine ⟨finProdFinEquiv (row, groupCol j), ?_, ?_, ?_⟩
  all_goals simp only [groupRow, groupCol, Equiv.symm_apply_apply]
  · have hr : r.val*k^3+r.rev.val*k^3+k^3 = n := by
      calc
        _ = (r.val+r.rev.val+1)*k^3 := by ring
        _ = n := by rw [rev_sum, hn]
    have hx := rev_sum x
    cases backwards <;>
      simp only [row, corridorCell, ↓reduceIte, Bool.false_eq_true, Nat.add_zero,
        Nat.sub_zero, Nat.add_mul, Nat.one_mul] at hlo hhi ⊢ <;> omega
  · have hr : r.val*k^3+r.rev.val*k^3+k^3 = n := by
      calc
        _ = (r.val+r.rev.val+1)*k^3 := by ring
        _ = n := by rw [rev_sum, hn]
    have hx := rev_sum x
    cases backwards <;>
      simp only [row, corridorCell, ↓reduceIte, Bool.false_eq_true, Nat.add_zero,
        Nat.sub_zero, Nat.add_mul, Nat.one_mul] at hlo hhi ⊢ <;> omega
  · simpa [corridorCell, groupCol] using hcol

/-- The complete vertical stage, including entry into the first vertical band,
efficient corridor slides, and parity-adjusted jumps across horizontal bands. -/
theorem verticalTransportBound {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hn : n = k^4) :
    VerticalTransportBound (n := n) hk
      (26*(k+2)+k^3+(k-1)*(26*(k+3))) := by
  intro A B hA i j hAB hH hcol b hb
  have hsize : n = k*k^3 := by rw [hn]; ring
  have hn2 : 2 ≤ n := by rw [hn]; nlinarith [Nat.pow_le_pow_left hk 4]
  have hk2 : k ≤ k^2 := by nlinarith
  have hk3 : k^2 ≤ k^3 := by nlinarith [Nat.mul_le_mul_left k hk2]
  have hwidth : k+2 ≤ k^3 := by nlinarith [Nat.mul_le_mul_left k hk2]
  let back : Bool := decide (groupRow j < groupRow i)
  let d : Fin k := if back then (groupRow i).rev else groupRow i
  let t : Fin k := if back then (groupRow j).rev else groupRow j
  let sVal := if back then d.val+1 else d.val
  have hst : sVal ≤ t.val := by
    by_cases hd : groupRow j < groupRow i <;>
      simp [sVal, d, t, back, hd, Fin.val_rev] <;> omega
  let s : Fin k := ⟨sVal, lt_of_le_of_lt hst t.isLt⟩
  let L := if back then 0 else k
  let U := if back then k else 0
  have hLU : L+U = k := by cases hback : back <;> simp [L, U, hback]
  have hL : L ≤ k := by omega
  have hsbound : (s.val+1)*k^3 ≤ n := by
    rw [hsize]
    exact Nat.mul_le_mul_right _ s.isLt
  let a : Fin n := ⟨s.val*k^3+L, by
    simp only [Nat.add_mul, Nat.one_mul] at hsbound
    omega⟩
  let z : Fin n := if back then b.1.rev else b.1
  let column := (blank B).2
  let line := corridorCell true back column
  let cap := if back then n-(groupRow i).val*k^3 else ((groupRow i).val+1)*k^3
  have hiMul : (groupRow i).val*k^3+(groupRow i).rev.val*k^3+k^3 = n := by
    calc
      _ = ((groupRow i).val+(groupRow i).rev.val+1)*k^3 := by ring
      _ = n := by rw [rev_sum, hsize]
  have hjMul : (groupRow j).val*k^3+(groupRow j).rev.val*k^3+k^3 = n := by
    calc
      _ = ((groupRow j).val+(groupRow j).rev.val+1)*k^3 := by ring
      _ = n := by rw [rev_sum, hsize]
  have hz : t.val*k^3+L ≤ z.val ∧ z.val < (t.val+1)*k^3-U := by
    have hb' := rev_sum b.1
    have hblo := hb.1
    have hbhi := hb.2.1
    simp only [Nat.add_mul, Nat.one_mul] at hbhi
    cases hback : back <;>
      simp only [t, z, L, U, hback, ↓reduceIte, Bool.false_eq_true, Nat.add_zero,
        Nat.sub_zero, Nat.add_mul, Nat.one_mul] <;> omega
  have hcap : cap ≤ (s.val+1)*k^3 := by
    cases hback : back <;>
      simp only [cap, s, sVal, d, hback, ↓reduceIte, Bool.false_eq_true,
        Nat.add_mul, Nat.one_mul] <;> omega
  have hbudget : cap-a.val ≤ k^3 := by
    change cap-(s.val*k^3+L) ≤ k^3
    simp only [Nat.add_mul, Nat.one_mul] at hcap
    omega
  have hafirst : a.val < (s.val+1)*k^3-U := by
    dsimp [a]
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  have hfamily : ∀ (r : Fin k) (x : Fin n), r.val*k^3+L ≤ x.val →
      x.val < (r.val+1)*k^3-U → A (line x) ∈ targetGroup i := by
    intro r x hxlo hxhi
    obtain ⟨l, hl⟩ := vertical_of_rank hk hsize i j back column x hcol r hxlo hxhi
    exact hA.2 l i _ hl
  have hefficient : ∀ (x y : Fin n) (tile : Tile n), x.val+1 = y.val → cap ≤ x.val →
      tile ∈ targetGroup i → gridDistance (line x) (position (target n) tile)+1 =
        gridDistance (line y) (position (target n) tile) := by
    intro x y tile hxy hcap ht
    have ht' := (mem_targetGroup i tile).mp ht |>.2
    have hlo := ht'.1
    have hhi := ht'.2.1
    cases hback : back <;>
      simp only [line, cap, corridorCell, hback, ↓reduceIte, Bool.false_eq_true,
        gridDistance, Fin.rev, Nat.dist] at hcap ⊢ <;> omega
  obtain ⟨l, hfirst⟩ := vertical_of_rank hk hsize i j back column a hcol s le_rfl hafirst
  change vertical l i (line a) at hfirst
  have hane : line a ≠ blank B := fun h => horizontal_not_vertical hk hH (h ▸ hfirst)
  let uc : Fin n := if h : column.val+1 < n then ⟨column.val+1, h⟩
    else ⟨column.val-1, by have := column.isLt; omega⟩
  let u : Cell n := ((blank B).1, uc)
  have huadj : gridDistance (blank B) u = 1 := by
    dsimp [u, uc, gridDistance, column]
    split_ifs <;> simp only [Nat.dist_self, Nat.zero_add, Nat.dist] <;> omega
  have hune : u ≠ blank B := by
    intro h; rw [h, gridDistance_self] at huadj; omega
  have huH : horizontal i u := hH
  obtain ⟨C, p, hC, hBC, hp⟩ := exists_group_vertical_jump hk hn2 B i (line a) u
    (hAB.mem_targetGroup (hfamily s a le_rfl hafirst) hane)
    (hAB.mem_targetGroup (hA.1 i u huH) hune) (by simp [line, corridorCell, column]) huadj
  have hgap : Nat.dist (blank B).1.val (line a).1.val ≤ k := by
    have hgc := (groupCol i).isLt
    have haSum := rev_sum a
    change (blank B).1.val = (groupRow i).val*k^3+(groupCol i).val at hH
    cases hback : back
    · have haval : a.val = (groupRow i).val*k^3+k := by
        simp [a, s, sVal, d, L, hback]
      simp only [line, corridorCell, hback, ↓reduceIte, Bool.false_eq_true]
      rw [haval]
      simp only [Nat.dist]
      omega
    · have haval : a.val = (groupRow i).rev.val*k^3+k^3 := by
        simp [a, s, sVal, d, L, hback, Nat.add_mul]
      rw [haval] at haSum
      have har : a.rev.val+1 = (groupRow i).val*k^3 := by omega
      simp only [line, corridorCell, hback, ↓reduceIte, Nat.dist]
      omega
  have hp' : p.inefficientMoves ≤ 26*(k+2) :=
    p.inefficientMoves_le_length.trans (hp.trans (Nat.mul_le_mul_left 26 (by omega)))
  obtain ⟨D, q, hD, hAD, hq⟩ := exists_banded_vertical_route hk hn2 (k^3) L U hsize
    (by omega) i back column cap hefficient A hfamily s t hst a z rfl hz hcap C
    (hAB.trans hBC) hC
  change blank D = line z at hD
  have hzcell : line z = (b.1, column) := by cases hback : back <;> simp [line, z, corridorCell, hback]
  have hv : vertical j i (blank D) := by
    rw [hD, hzcell]
    exact ⟨hb.1, hb.2.1, hcol⟩
  refine ⟨D, p.append q, hv, ?_, hAD, ?_⟩
  · rw [hD, hzcell]
  · rw [Path.inefficientMoves_append]
    have htbound : t.val-s.val ≤ k-1 := by have := t.isLt; omega
    have hq' : q.inefficientMoves ≤ k^3+(k-1)*(26*(k+3)) := by
      rw [hLU] at hq
      exact hq.trans (Nat.add_le_add hbudget (Nat.mul_le_mul_right _ htbound))
    omega

end
end SlidingPuzzle.Partition

namespace SlidingPuzzle.Algorithm

/-- The concrete transport phase with a uniform inefficient-move bound. -/
theorem transportContract : TransportContract 82 := by
  apply transportContract_of_step_bound 82
  intro k hk
  let : NeZero (k^4) := ⟨by positivity⟩
  have hstep := Partition.transportStepBound_of_vertical_bound_jump hk rfl
    (Partition.verticalTransportBound hk rfl)
  apply hstep.mono hk
  have hcount : k-1+1=k := Nat.sub_add_cancel (by omega)
  have hprod : (k-1)*(k+3)+(k+3)=k*(k+3) := by
    calc
      _ = ((k-1)+1)*(k+3) := by ring
      _ = k*(k+3) := by rw [hcount]
  have hprod' : (k+3)+(k-1)*(k+3)=k*(k+3) := by omega
  have hvertical :
      26*(k+2)+k^3+(k-1)*(26*(k+3))+26 = k^3+26*k^2+78*k := by
    calc
      _ = k^3+26*((k+2)+(k-1)*(k+3)+1) := by ring
      _ = k^3+26*((k+3)+(k-1)*(k+3)) := by congr 1 <;> omega
      _ = k^3+26*(k*(k+3)) := by rw [hprod']
      _ = k^3+26*k^2+78*k := by ring
  have hfactor : 0 ≤ ((k:ℤ)-2)*(30*(k:ℤ)^2+34*(k:ℤ)-10) :=
    mul_nonneg (by omega) (by nlinarith)
  have hbudgetInt : 26*(k:ℤ)^2+78*(k:ℤ) ≤ 30*(k:ℤ)^3+25 := by
    nlinarith [hfactor]
  have hbudget : 26*k^2+78*k ≤ 30*k^3+25 := by exact_mod_cast hbudgetInt
  nlinarith [hvertical, hbudget]

end SlidingPuzzle.Algorithm
