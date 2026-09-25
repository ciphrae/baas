import SlidingPuzzle.Algorithm.Transport.VerticalSchedule
import SlidingPuzzle.Algorithm.Transport.Step

/-! Phase II (Transport): vertical travel in both directions, and the complete
transport phase. Only the initial good interval can incur inefficient ordinary slides;
the intervening horizontal bands are crossed by bounded group-preserving jumps. -/

namespace SlidingPuzzle.Partition
noncomputable section
open Classical

private theorem rev_sum {m : ℕ} (x : Fin m) : x.val+x.rev.val+1 = m := by
  simp only [Fin.val_rev]
  omega

private theorem vertical_of_rank {n k : ℕ} (hk : Dims n k)
    (i j : GroupIndex k) (backwards : Bool) (column x : Fin n)
    (hcol : column.val = (groupCol j).val*side n k+i.val) (r : Fin k)
    (hlo : r.val*side n k+(if backwards then 0 else k) ≤ x.val)
    (hhi : x.val < (r.val+1)*side n k-(if backwards then k else 0)) :
    ∃ l : GroupIndex k, vertical l i (corridorCell true backwards column x) := by
  let row := if backwards then r.rev else r
  refine ⟨finProdFinEquiv (row, groupCol j), ?_, ?_, ?_⟩
  all_goals simp only [groupRow, groupCol, Equiv.symm_apply_apply]
  · have hr : r.val*side n k+r.rev.val*side n k+side n k = n := by
      calc
        _ = (r.val+r.rev.val+1)*side n k := by ring
        _ = n := by rw [rev_sum]; exact hk.mul_side
    have hx := rev_sum x
    cases backwards <;>
      simp only [row, corridorCell, ↓reduceIte, Bool.false_eq_true, Nat.add_zero,
        Nat.sub_zero, Nat.add_mul, Nat.one_mul] at hlo hhi ⊢ <;> omega
  · have hr : r.val*side n k+r.rev.val*side n k+side n k = n := by
      calc
        _ = (r.val+r.rev.val+1)*side n k := by ring
        _ = n := by rw [rev_sum]; exact hk.mul_side
    have hx := rev_sum x
    cases backwards <;>
      simp only [row, corridorCell, ↓reduceIte, Bool.false_eq_true, Nat.add_zero,
        Nat.sub_zero, Nat.add_mul, Nat.one_mul] at hlo hhi ⊢ <;> omega
  · simpa [corridorCell, groupCol] using hcol

/-- The complete vertical stage, including entry into the first vertical band,
efficient corridor slides, and parity-adjusted jumps across horizontal bands. -/
theorem verticalTransportBound {n k : ℕ} [NeZero n] (hk : Dims n k) :
    VerticalTransportBound (n := n) hk
      (26*(k+2)+side n k+(k-1)*(26*(k+3))) := by
  intro A B hA i j hAB hH hcol b hb
  have hn2 : 2 ≤ n := by have := hk.two_le_n; omega
  have hk2 : k ≤ k^2 := by have := hk.two_le; nlinarith
  have hk3 : k^2 ≤ side n k := by have := hk.sq_add_le; omega
  have hwidth : k+2 ≤ side n k := hk.k_add_two_le
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
  have hsbound : (s.val+1)*side n k ≤ n := hk.block_le s
  let a : Fin n := ⟨s.val*side n k+L, by
    simp only [Nat.add_mul, Nat.one_mul] at hsbound
    omega⟩
  let z : Fin n := if back then b.1.rev else b.1
  let column := (blank B).2
  let line := corridorCell true back column
  let cap := if back then n-(groupRow i).val*side n k else ((groupRow i).val+1)*side n k
  have hiMul : (groupRow i).val*side n k+(groupRow i).rev.val*side n k+side n k = n := by
    calc
      _ = ((groupRow i).val+(groupRow i).rev.val+1)*side n k := by ring
      _ = n := by rw [rev_sum]; exact hk.mul_side
  have hjMul : (groupRow j).val*side n k+(groupRow j).rev.val*side n k+side n k = n := by
    calc
      _ = ((groupRow j).val+(groupRow j).rev.val+1)*side n k := by ring
      _ = n := by rw [rev_sum]; exact hk.mul_side
  have hz : t.val*side n k+L ≤ z.val ∧ z.val < (t.val+1)*side n k-U := by
    have hb' := rev_sum b.1
    have hblo := hb.1
    have hbhi := hb.2.1
    simp only [Nat.add_mul, Nat.one_mul] at hbhi
    cases hback : back <;>
      simp only [t, z, L, U, hback, ↓reduceIte, Bool.false_eq_true, Nat.add_zero,
        Nat.sub_zero, Nat.add_mul, Nat.one_mul] <;> omega
  have hcap : cap ≤ (s.val+1)*side n k := by
    cases hback : back <;>
      simp only [cap, s, sVal, d, hback, ↓reduceIte, Bool.false_eq_true,
        Nat.add_mul, Nat.one_mul] <;> omega
  have hbudget : cap-a.val ≤ side n k := by
    change cap-(s.val*side n k+L) ≤ side n k
    simp only [Nat.add_mul, Nat.one_mul] at hcap
    omega
  have hafirst : a.val < (s.val+1)*side n k-U := by
    dsimp [a]
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  have hfamily : ∀ (r : Fin k) (x : Fin n), r.val*side n k+L ≤ x.val →
      x.val < (r.val+1)*side n k-U → A (line x) ∈ targetGroup i := by
    intro r x hxlo hxhi
    obtain ⟨l, hl⟩ := vertical_of_rank hk i j back column x hcol r hxlo hxhi
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
  obtain ⟨l, hfirst⟩ := vertical_of_rank hk i j back column a hcol s le_rfl hafirst
  change vertical l i (line a) at hfirst
  have hane : line a ≠ blank B := fun h => horizontal_not_vertical hk hH (h ▸ hfirst)
  let uc : Fin n := if h : column.val+1 < n then ⟨column.val+1, h⟩
    else ⟨column.val-1, by have := column.isLt; omega⟩
  let u : Cell n := ((blank B).1, uc)
  have huadj : gridDistance (blank B) u = 1 := by
    dsimp [u, uc, gridDistance, column]
    split_ifs <;> simp only [Nat.dist] <;> omega
  have hune : u ≠ blank B := by
    intro h; rw [h, gridDistance_self] at huadj; omega
  have huH : horizontal i u := hH
  obtain ⟨C, p, hC, hBC, hp⟩ := exists_group_vertical_jump hk hn2 B i (line a) u
    (hAB.mem_targetGroup (hfamily s a le_rfl hafirst) hane)
    (hAB.mem_targetGroup (hA.1 i u huH) hune) (by simp [line, corridorCell, column]) huadj
  have hgap : Nat.dist (blank B).1.val (line a).1.val ≤ k := by
    have hgc := (groupCol i).isLt
    have haSum := rev_sum a
    change (blank B).1.val = (groupRow i).val*side n k+(groupCol i).val at hH
    cases hback : back
    · have haval : a.val = (groupRow i).val*side n k+k := by
        simp [a, s, sVal, d, L, hback]
      simp only [line, corridorCell, hback, ↓reduceIte, Bool.false_eq_true]
      rw [haval]
      simp only [Nat.dist]
      omega
    · have haval : a.val = (groupRow i).rev.val*side n k+side n k := by
        simp [a, s, sVal, d, L, hback, Nat.add_mul]
      rw [haval] at haSum
      have har : a.rev.val+1 = (groupRow i).val*side n k := by omega
      simp only [line, corridorCell, hback, ↓reduceIte, Nat.dist]
      omega
  have hp' : p.inefficientMoves ≤ 26*(k+2) :=
    p.inefficientMoves_le_length.trans (hp.trans (Nat.mul_le_mul_left 26 (by omega)))
  obtain ⟨D, q, hD, hAD, hq⟩ := exists_banded_vertical_route hk hn2 (side n k) L U hk.mul_side.symm
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
    have hq' : q.inefficientMoves ≤ side n k+(k-1)*(26*(k+3)) := by
      rw [hLU] at hq
      exact hq.trans (Nat.add_le_add hbudget (Nat.mul_le_mul_right _ htbound))
    omega

end
end SlidingPuzzle.Partition

