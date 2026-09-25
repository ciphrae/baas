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

/-- Along the vertical line of `V(·,i)` in the column of squares of `j`, the
route coordinate `x` lies in a vertical corridor when it is in the band `r`
at least `2k` after its start (forwards) or before its end (backwards). -/
private theorem vertical_of_rank {n k : ℕ} (hk : Dims n k)
    (i j : GroupIndex k) (backwards : Bool) (column x : Fin n)
    (hcol : column.val = (groupCol j).val*side n k+i.val) (r : Fin k)
    (hlo : r.val*side n k+(if backwards then 0 else 2*k) ≤ x.val)
    (hhi : x.val+(if backwards then 2*k else 0) < (r.val+1)*side n k) :
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
      simp only [row, corridorCell, ↓reduceIte, Bool.false_eq_true, Nat.add_mul,
        Nat.one_mul] at hlo hhi ⊢ <;> omega
  · have hr : r.val*side n k+r.rev.val*side n k+side n k = n := by
      calc
        _ = (r.val+r.rev.val+1)*side n k := by ring
        _ = n := by rw [rev_sum]; exact hk.mul_side
    have hx := rev_sum x
    cases backwards <;>
      simp only [row, corridorCell, ↓reduceIte, Bool.false_eq_true, Nat.add_mul,
        Nat.one_mul] at hlo hhi ⊢ <;> omega
  · simpa [corridorCell, groupCol] using hcol

set_option maxHeartbeats 4000000 in
/-- The complete vertical stage, including entry into the first vertical band,
efficient corridor slides, and parity-adjusted jumps across horizontal bands.
The blank starts on either row of `H_i`. Toward another band it leaves through
the side of that row and all its ordinary slides are efficient; within the band
of `i` it pays `verticalCost`. -/
theorem verticalTransportBound {n k : ℕ} [NeZero n] (hk : Dims n k) :
    VerticalTransportBound (n := n) hk
      (26*(2*k+2)+(k-1)*(26*(2*k+3))) := by
  intro A B hA i j hAB low hlowd hlowk hrowB hcol b hb
  have hn2 : 2 ≤ n := by have := hk.two_le_n; omega
  have hk2 : k ≤ k^2 := by have := hk.two_le; nlinarith
  have hk3 : k^2+k+2 ≤ side n k := hk.sq_add_le
  have h2k : 2*k ≤ k^2 := by nlinarith [hk.two_le]
  set s := side n k with hs
  obtain ⟨a, ha⟩ : ∃ a, (groupRow i).val = a := ⟨_, rfl⟩
  obtain ⟨aJ, haJ⟩ : ∃ a, (groupRow j).val = a := ⟨_, rfl⟩
  have hak : a < k := by rw [← ha]; exact (groupRow i).isLt
  have haJk : aJ < k := by rw [← haJ]; exact (groupRow j).isLt
  rw [ha, haJ] at hlowd
  rw [ha] at hlowk
  have hnk : n = k*s := hk.mul_side.symm
  have hmulA : a*s+s ≤ n := by
    rw [hnk]; have := Nat.mul_le_mul_right s (show a+1 ≤ k by omega); simpa [Nat.add_mul] using this
  have hmulJ : aJ*s+s ≤ n := by
    rw [hnk]; have := Nat.mul_le_mul_right s (show aJ+1 ≤ k by omega); simpa [Nat.add_mul] using this
  have hrevA : (k-1-a)*s+a*s+s = n := by
    rw [hnk]; rw [← Nat.add_mul, ← Nat.succ_mul]; congr 1; omega
  have hrevJ : (k-1-aJ)*s+aJ*s+s = n := by
    rw [hnk]; rw [← Nat.add_mul, ← Nat.succ_mul]; congr 1; omega
  have hgap : ∀ u v : ℕ, u < v → u*s+s ≤ v*s := by
    intro u v h
    have := Nat.mul_le_mul_right s (show u+1 ≤ v by omega)
    simpa [Nat.add_mul] using this
  have hgc := (groupCol i).isLt
  -- The start row.
  have hrow0 : (blank B).1.val = if low then a*s+s+k+(groupCol i).val
      else a*s+(groupCol i).val := by
    rw [hrowB]; unfold corridorRow
    cases hl : low
    · simp only [Bool.false_eq_true, ↓reduceIte, ha, ← hs]
    · have hnb : nextBand k a = a+1 := Nat.mod_eq_of_lt (hlowk hl)
      simp only [↓reduceIte, ha, hnb, Nat.add_mul, Nat.one_mul, ← hs]
  -- Direction, bands and thresholds in route coordinates: backwards (upwards)
  -- from the upper row toward a source above, forwards from the lower row
  -- toward a source below, and within the band from either row.
  obtain ⟨back, dV, tV, sV, L, U, hvals⟩ : ∃ (back : Bool) (dV tV sV L U : ℕ),
      (aJ < a ∧ low = false ∧ back = true ∧ dV = k-1-a ∧ tV = k-1-aJ ∧ sV = k-a ∧
        L = 0 ∧ U = 2*k) ∨
      (a < aJ ∧ low = true ∧ back = false ∧ dV = a ∧ tV = aJ ∧ sV = a+1 ∧
        L = 2*k ∧ U = 0) ∨
      (a = aJ ∧ low = false ∧ back = false ∧ dV = a ∧ tV = a ∧ sV = a ∧
        L = 2*k ∧ U = 0) ∨
      (a = aJ ∧ low = true ∧ back = true ∧ dV = k-1-a ∧ tV = k-1-a ∧ sV = k-1-a ∧
        L = 0 ∧ U = 2*k) := by
    rcases lt_trichotomy aJ a with h | h | h
    · have hl : low = false := by simpa [show ¬ a < aJ by omega] using hlowd (by omega)
      exact ⟨_, _, _, _, _, _, Or.inl ⟨h, hl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    · cases hl : low
      · exact ⟨_, _, _, _, _, _, Or.inr (Or.inr (Or.inl ⟨h.symm, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))⟩
      · exact ⟨true, k-1-a, k-1-a, k-1-a, 0, 2*k,
          Or.inr (Or.inr (Or.inr ⟨h.symm, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))⟩
    · have hl : low = true := by simpa [h] using hlowd (by omega)
      exact ⟨_, _, _, _, _, _, Or.inr (Or.inl ⟨h, hl, rfl, rfl, rfl, rfl, rfl, rfl⟩)⟩
  have hLU : L+U = 2*k := by rcases hvals with h | h | h | h <;> omega
  have hst : sV ≤ tV ∧ tV < k := by
    rcases hvals with h | h | h | h
    · have := hlowk; omega
    · have := hlowk h.2.1; omega
    · omega
    · have := hlowk h.2.1; omega
  have hdV : dV < k := by rcases hvals with h | h | h | h <;> omega
  let sB : Fin k := ⟨sV, by omega⟩
  let t : Fin k := ⟨tV, hst.2⟩
  have hsB : sV*s+s ≤ n := by
    rw [hnk]; have := Nat.mul_le_mul_right s (show sV+1 ≤ k by omega); simpa [Nat.add_mul] using this
  have hL : L ≤ 2*k := by omega
  let aF : Fin n := ⟨sV*s+L, by omega⟩
  let z : Fin n := if back then b.1.rev else b.1
  let column := (blank B).2
  let line := corridorCell true back column
  let cap := (dV+1)*s
  have hb1 : aJ*s+2*k ≤ b.1.val := by have := hb.1; rwa [haJ] at this
  have hb2 : b.1.val < aJ*s+s := by
    have := hb.2.1; rwa [haJ, Nat.add_mul, Nat.one_mul] at this
  have hbn := b.1.isLt
  have hzv : z.val = if back then n-1-b.1.val else b.1.val := by
    dsimp [z]; split_ifs <;> simp [Fin.val_rev] <;> omega
  -- Band products in each case.
  have hprod : (back = true → (k-1-aJ)*s+aJ*s+s = n ∧ (k-1-a)*s+a*s+s = n) := by
    intro _; exact ⟨hrevJ, hrevA⟩
  have hz : tV*s+L ≤ z.val ∧ z.val < (tV+1)*s-U := by
    rw [hzv]
    rcases hvals with ⟨h1, -, h3, -, h5, -, h7, h8⟩ | ⟨h1, -, h3, -, h5, -, h7, h8⟩ |
        ⟨h1, -, h3, -, h5, -, h7, h8⟩ | ⟨h1, -, h3, -, h5, -, h7, h8⟩ <;>
      subst h3 h5 h7 h8 <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_mul, Nat.one_mul]
    · omega
    · omega
    · subst h1; omega
    · subst h1; omega
  have hcap : cap ≤ (sB.val+1)*s := by
    apply Nat.mul_le_mul_right
    change dV+1 ≤ sV+1
    rcases hvals with h | h | h | h <;> omega
  have hlineRow : ∀ x : Fin n, (line x).1.val = if back then n-1-x.val else x.val := by
    intro x
    cases back <;> simp [line, corridorCell, Fin.val_rev] <;> omega
  have hlineCol : ∀ x : Fin n, (line x).2 = column := by
    intro x; cases back <;> simp [line, corridorCell]
  have hbackL : (back = true → L = 0 ∧ U = 2*k) ∧ (back = false → L = 2*k ∧ U = 0) := by
    rcases hvals with ⟨-, -, h3, -, -, -, h7, h8⟩ | ⟨-, -, h3, -, -, -, h7, h8⟩ |
        ⟨-, -, h3, -, -, -, h7, h8⟩ | ⟨-, -, h3, -, -, -, h7, h8⟩ <;> subst h3 <;> simp [h7, h8]
  have hrank : ∀ (r : Fin k) (x : Fin n), r.val*s+L ≤ x.val →
      x.val < (r.val+1)*s-U → ∃ l : GroupIndex k, vertical l i (line x) := by
    intro r x hxlo hxhi
    have hr := Nat.mul_le_mul_right s (show r.val+1 ≤ k by omega)
    rw [← hnk, Nat.add_mul, Nat.one_mul] at hr
    have h2ks : 2*k ≤ r.val*s+s := by omega
    exact vertical_of_rank hk i j back column x hcol r
      (by cases hb' : back
          · rw [(hbackL.2 hb').1] at hxlo; simpa [hs] using hxlo
          · rw [(hbackL.1 hb').1] at hxlo; simpa [hs] using hxlo)
      (by cases hb' : back
          · rw [(hbackL.2 hb').2] at hxhi; simp only [Bool.false_eq_true, ↓reduceIte, ← hs]
            omega
          · rw [(hbackL.1 hb').2, Nat.add_mul, Nat.one_mul] at hxhi
            simp only [↓reduceIte, ← hs, Nat.add_mul, Nat.one_mul]
            omega)
  have hfamily : ∀ (r : Fin k) (x : Fin n), r.val*s+L ≤ x.val →
      x.val < (r.val+1)*s-U → A (line x) ∈ targetGroup i := by
    intro r x hxlo hxhi
    obtain ⟨l, hl⟩ := hrank r x hxlo hxhi
    exact hA.2 l i _ hl
  have hefficient : ∀ (x y : Fin n) (tile : Tile n), x.val+1 = y.val → cap ≤ x.val →
      tile ∈ targetGroup i → gridDistance (line x) (position (target n) tile)+1 =
        gridDistance (line y) (position (target n) tile) := by
    intro x y tile hxy hcap' ht
    have ht' := (mem_targetGroup i tile).mp ht |>.2
    have hlo := ht'.1
    have hhi := ht'.2.1
    rw [ha, ← hs] at hlo hhi
    rw [Nat.add_mul, Nat.one_mul] at hhi
    have hl1 := hlineRow x
    have hl2 := hlineRow y
    have hyn := y.isLt
    simp only [gridDistance, hlineCol x, hlineCol y, Nat.dist]
    simp only [cap] at hcap'
    have hdv : (back = true → dV = k-1-a) ∧ (back = false → dV = a) := by
      rcases hvals with ⟨-, -, h3, h4, -⟩ | ⟨-, -, h3, h4, -⟩ | ⟨-, -, h3, h4, -⟩ |
          ⟨-, -, h3, h4, -⟩ <;> subst h3 <;> simp [h4]
    cases hb' : back <;> simp only [hb', Bool.false_eq_true, ↓reduceIte] at hl1 hl2
    · rw [hdv.2 hb', Nat.add_mul, Nat.one_mul] at hcap'; omega
    · rw [hdv.1 hb', Nat.add_mul, Nat.one_mul] at hcap'; omega
  -- The start of the route, and the jump to it.
  have haF : sB.val*s+L ≤ aF.val ∧ aF.val < (sB.val+1)*s-U := by
    change sV*s+L ≤ sV*s+L ∧ sV*s+L < (sV+1)*s-U
    rw [Nat.add_mul, Nat.one_mul]; omega
  obtain ⟨l, hfirst⟩ := hrank sB aF haF.1 haF.2
  have hH : horizontal i (blank B) := horizontal_of_corridorRow low hrowB
  have hane : line aF ≠ blank B := fun h => horizontal_not_vertical hk hH (h ▸ hfirst)
  let uc : Fin n := if h : column.val+1 < n then ⟨column.val+1, h⟩
    else ⟨column.val-1, by have := column.isLt; omega⟩
  let u : Cell n := ((blank B).1, uc)
  have huadj : gridDistance (blank B) u = 1 := by
    dsimp [u, uc, gridDistance, column]
    split_ifs <;> simp only [Nat.dist] <;> omega
  have hune : u ≠ blank B := by
    intro h; rw [h, gridDistance_self] at huadj; omega
  have huH : horizontal i u := horizontal_of_corridorRow low hrowB
  obtain ⟨C, p, hC, hBC, hp⟩ := exists_group_vertical_jump hk hn2 B i (line aF) u
    (hAB.mem_targetGroup (hfamily sB aF haF.1 haF.2) hane)
    (hAB.mem_targetGroup (hA.1 i u huH) hune) (hlineCol aF) huadj
  have hjump : Nat.dist (blank B).1.val (line aF).1.val ≤ 2*k := by
    rw [hlineRow aF, hrow0]
    change Nat.dist _ (if back then n-1-(sV*s+L) else sV*s+L) ≤ 2*k
    rcases hvals with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ | ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ |
        ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ | ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ <;>
      subst h2 h3 h6 h7 <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.dist]
    · have e : (k-a)*s = (k-1-a)*s+s := by
        rw [show k-a = (k-1-a)+1 by omega, Nat.add_mul, Nat.one_mul]
      rw [e]; omega
    · rw [Nat.add_mul, Nat.one_mul]; omega
    · omega
    · omega
  have hp' : p.inefficientMoves ≤ 26*(2*k+2) :=
    p.inefficientMoves_le_length.trans (hp.trans (Nat.mul_le_mul_left 26 (by omega)))
  obtain ⟨D, q, hD, hAD, hq, hqsame⟩ := exists_banded_vertical_route hk hn2 s L U
    hnk (by omega) i back column cap hefficient A hfamily sB t (by
      change sV ≤ tV; exact hst.1) aF z rfl hz hcap C (hAB.trans hBC) hC
  change blank D = line z at hD
  have hzcell : line z = (b.1, column) := by
    cases hback : back <;> simp [line, z, corridorCell, hback]
  have hv : vertical j i (blank D) := by
    rw [hD, hzcell]
    exact ⟨hb.1, hb.2.1, hcol⟩
  refine ⟨D, p.append q, hv, ?_, hAD, ?_⟩
  · rw [hD, hzcell]
  · rw [Path.inefficientMoves_append]
    have htbound : t.val-sB.val ≤ k-1 := by have := t.isLt; omega
    have hcross : (t.val-sB.val)*(26*(L+U+3)) ≤ (k-1)*(26*(2*k+3)) := by
      rw [hLU]; exact Nat.mul_le_mul_right _ htbound
    have hq' : q.inefficientMoves ≤ (dV+1)*s-(sV*s+L)+(tV-sV)*(26*(L+U+3)) := hq
    have hsame : sV = tV → q.inefficientMoves ≤ (if back then n-1-b.1.val else b.1.val)-(sV*s+L) := by
      intro h
      have := hqsame (Fin.ext h)
      rw [hzv] at this
      exact this
    rw [hLU] at hq' hcross
    have hts : t.val-sB.val = tV-sV := rfl
    rw [hts] at hcross
    have hbudget : q.inefficientMoves ≤ verticalCost (n := n) i j low b.1.val+
        (tV-sV)*(26*(2*k+3)) := by
      unfold verticalCost
      rw [ha, haJ, ← hs]
      rcases hvals with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ | ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ |
          ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ | ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
      · rw [if_neg (by omega)]
        have e : (dV+1)*s-(sV*s+L) = 0 := by
          rw [h4, h6, h7, show k-1-a+1 = k-a by omega]; simp
        omega
      · rw [if_neg (by omega)]
        have e : (dV+1)*s-(sV*s+L) = 0 := by rw [h4, h6]; omega
        omega
      · rw [if_pos h1, h2]
        have h := hsame (by omega)
        rw [h3, h6, h7] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        omega
      · rw [if_pos h1, h2]
        have h := hsame (by omega)
        rw [h3, h6, h7] at h
        simp only [↓reduceIte] at h ⊢
        rw [Nat.add_mul, Nat.one_mul]
        omega
    omega

end
end SlidingPuzzle.Partition
