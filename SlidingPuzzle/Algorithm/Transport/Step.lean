import SlidingPuzzle.Algorithm.Transport.Entry
import SlidingPuzzle.Algorithm.Transport.Realization
import SlidingPuzzle.Algorithm.Transport.Carry

/-! One transfer of Algorithm 4: slide the blank to the top of its reservoir,
enter the horizontal corridor, travel to the vertical corridor, travel
vertically (an explicit parameter, supplied in `Transport.lean`), and exit into
the source reservoir. -/
namespace SlidingPuzzle.Partition
noncomputable section

/-- The inefficiency of vertical travel from the row `low` of `H_i` to the
source square `j` and its tile's row `x`. Leaving the band of `i` is free: the
upper row lies above the band's reservoirs and the lower row below them. Inside
the band, it is the distance from the row's side of the reservoirs. -/
def verticalCost {n k : ℕ} (i j : GroupIndex k) (low : Bool) (x : ℕ) : ℕ :=
  if (groupRow i).val = (groupRow j).val then
    (if low then ((groupRow i).val+1)*side n k-1-x else x-((groupRow i).val*side n k+2*k))
  else 0

/-- The vertical stage: start on the row `low` of H_i at the selected source
block's vertical-corridor column, and reach the source tile's row within V_(j,i).
The lower row is used only toward a source below, or within the band, and not
from the last band, whose lower row lies at the top of the board.
Intermediate boards retain the filled-blank group invariant, not Clear. -/
def VerticalTransportBound {n k : ℕ} [NeZero n] (_hk : Dims n k) (E : ℕ) : Prop :=
  ∀ A B : Board n, Clear (k := k) A → ∀ i j : GroupIndex k,
    GroupEquivalent i A B → ∀ low : Bool,
    ((groupRow i).val ≠ (groupRow j).val → low = decide ((groupRow i).val < (groupRow j).val)) →
    (low = true → (groupRow i).val+1 < k) →
    (blank B).1.val = corridorRow (n := n) i low →
    (blank B).2.val = (groupCol j).val*side n k+i.val →
    ∀ b : Cell n, reservoir j b →
    ∃ D : Board n, ∃ p : Path B D,
      vertical j i (blank D) ∧ (blank D).1 = b.1 ∧
      GroupEquivalent i A D ∧ p.inefficientMoves ≤ E+verticalCost (n := n) i j low b.1.val

set_option maxHeartbeats 2000000 in
/-- The transfer step. The blank slides to the top or bottom of its reservoir,
enters the upper or lower row of `H_i`, travels to a vertical corridor next to
the source square, descends, and exits through the side of the source square
nearer to the tile, ending on the tile's cell with the source reservoir
otherwise unchanged. The horizontal travel is paid by the blank's weight and
the exit by the tile's weight in `transportPotential`; slide, entry and vertical
travel cost `2*s`, and `2*s` more from the last band, which has no lower row
within reach. -/
theorem transportStepBoundAmortized_of_vertical_bound {n k E : ℕ} [NeZero n]
    (hk : Dims n k)
    (hvertical : VerticalTransportBound (n := n) hk E) :
    TransportStepBoundAmortized (n := n) hk (fun r => 2*side n k+2*E+160*k^2+60*k+800+
      (if (groupRow (transportIndex k hk r)).val+1 = k then 2*side n k else 0))
      (transportPotential (k := k)) := by
  classical
  intro A₀ hA₀ i j hi₀ hchoice₀
  set I := transportIndex k hk i with hI
  set J := transportIndex k hk j with hJ
  set s := side n k with hs
  obtain ⟨b, hb, ht₀, -, -⟩ := boardMatrix_choice_endpoint hk A₀ hA₀ i j hi₀ hchoice₀
  change reservoir J b at hb
  change A₀ b ∈ targetGroup I at ht₀
  have hIJ' : I ≠ J := fun h => hchoice₀.1 ((transportIndex k hk).injective h.symm)
  -- The row of `H_I` to leave from: the side facing the source, or within the
  -- band, the one nearer to both the blank and the source tile.
  have hsq0 := hk.sq_add_le
  have h2k0 : 2*k ≤ k^2 := by nlinarith [hk.two_le]
  have hs3 : 3*k+2 ≤ s := by omega
  obtain ⟨x, hx⟩ : ∃ x, (blank A₀).1.val = x := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, (groupRow I).val = a := ⟨_, rfl⟩
  obtain ⟨aJ, haJ⟩ : ∃ a, (groupRow J).val = a := ⟨_, rfl⟩
  have haJk : aJ < k := by rw [← haJ]; exact (groupRow J).isLt
  have hx1 : a*s+2*k ≤ x := by have := hi₀.1; rw [hx, ha] at this; exact this
  have hx2 : x < a*s+s := by
    have := hi₀.2.1; rw [hx, ha, Nat.add_mul, Nat.one_mul] at this; exact this
  have hb1 : aJ*s+2*k ≤ b.1.val := by have := hb.1; rw [haJ] at this; exact this
  have hb2 : b.1.val < aJ*s+s := by
    have := hb.2.1; rw [haJ, Nat.add_mul, Nat.one_mul] at this; exact this
  let low : Bool := if a < aJ then true else if aJ < a then false
    else if a+1 < k then
      decide ((a*s+s-1-x)+(a*s+s-1-b.1.val) ≤ (x-(a*s+2*k))+(b.1.val-(a*s+2*k)))
    else false
  have hlowk : low = true → a+1 < k := by
    intro h
    by_cases h1 : a < aJ
    · omega
    · by_cases h2 : aJ < a
      · simp [low, h1, h2] at h
      · by_cases h3 : a+1 < k
        · exact h3
        · simp [low, h1, h2, h3] at h
  have hlowd : a ≠ aJ → low = decide (a < aJ) := by
    intro h
    by_cases h1 : a < aJ
    · simp [low, h1]
    · have h2 : aJ < a := by omega
      simp [low, h1, h2]
  have hy : (groupRow I).val*s+2*k ≤ (if low then a*s+s-1 else a*s+2*k) ∧
      (if low then a*s+s-1 else a*s+2*k) < ((groupRow I).val+1)*s := by
    rw [ha, Nat.add_mul, Nat.one_mul]; split_ifs <;> omega
  obtain ⟨A, p₀, hA, hi, hyA, hcolA, hmat₀, hpot₀, hlen₀, hfixA⟩ :=
    exists_reservoir_slide_path hk A₀ hA₀ I hi₀ _ hy.1 hy.2
  have ht : A b ∈ targetGroup I := by
    rw [hfixA b (fun h => hIJ' (reservoir_unique hk h hb))]; exact ht₀
  have hmatrixSwap : boardMatrix hk (swapCells A (blank A) b) =
      TransportCounts.move (boardMatrix hk A) i j :=
    boardMatrix_swap_endpoint hk A i j hchoice₀.1 hi b hb ht
  set vc := verticalCost (n := n) I J low b.1.val with hvcdef
  have hvc : p₀.length+vc ≤ s+(if aJ+1 = k then s else 0) := by
    rw [hlen₀, hvcdef, hx]
    unfold verticalCost
    rw [ha, haJ, ← hs]
    by_cases h1 : a < aJ
    · have hl : low = true := by simp [low, h1]
      simp only [hl, ↓reduceIte, Nat.dist]
      rw [if_neg (by omega)]
      split_ifs <;> omega
    · by_cases h2 : aJ < a
      · have hl : low = false := by simp [low, h1, h2]
        simp only [hl, Bool.false_eq_true, ↓reduceIte, Nat.dist]
        rw [if_neg (by omega)]
        split_ifs <;> omega
      · have he : a = aJ := by omega
        rw [if_pos he]
        subst he
        by_cases h3 : a+1 < k
        · have hl : low = decide ((a*s+s-1-x)+(a*s+s-1-b.1.val) ≤
              (x-(a*s+2*k))+(b.1.val-(a*s+2*k))) := by
            simp [low, h3]
          rw [if_neg (show ¬ (a+1 = k) by omega)]
          cases hlv : low
          · rw [hlv] at hl
            have := of_decide_eq_false hl.symm
            simp only [Bool.false_eq_true, ↓reduceIte, Nat.dist, Nat.add_mul, Nat.one_mul]
            omega
          · rw [hlv] at hl
            have := of_decide_eq_true hl.symm
            simp only [↓reduceIte, Nat.dist, Nat.add_mul, Nat.one_mul]
            omega
        · have hl : low = false := by simp [low, h3]
          rw [if_pos (show a+1 = k by omega)]
          simp only [hl, Bool.false_eq_true, ↓reduceIte, Nat.dist]
          omega
  have hk2 : k ≤ k^2 := by have := hk.two_le; nlinarith
  have hk3 : k^2 ≤ s := by have := hk.sq_add_le; omega
  have hsq := hk.sq_add_le
  have hindex : I.val < k^2 := by simpa [pow_two] using I.isLt
  have hn2 : 2 ≤ n := by have := hk.two_le_n; omega
  set c := (blank A).2.val with hc
  have hcI : (groupCol I).val*s+k^2 ≤ c ∧ c < (groupCol I).val*s+s := by
    have h1 := hi.2.2.1; have h2 := hi.2.2.2
    simp only [Nat.add_mul, Nat.one_mul] at h2
    exact ⟨h1, h2⟩
  set bwI := blankWeight (n := n) I c with hbwI
  have hbwI' : bwI = 2*(s-min (c-(groupCol I).val*s) (s-(c-(groupCol I).val*s)))+2 := by
    rw [hbwI]; rfl
  -- Route to a vertical corridor of `jc` and exit.
  have hroute : ∀ (jc : GroupIndex k) (bc : Cell n), groupRow jc = groupRow J →
      reservoir jc bc → bc.1 = b.1 → ∀ X : ℕ, (∀ C : Board n, GroupEquivalent I A C →
        vertical jc I (blank C) → (blank C).1 = b.1 →
        ∃ D : Board n, ∃ q : Path C D, GroupEquivalent I A D ∧ blank D = b ∧
          q.inefficientMoves ≤ X) →
      ∃ D : Board n, ∃ p : Path A D, GroupEquivalent I A D ∧ blank D = b ∧
        2*p.inefficientMoves ≤ bwI+26*(2*k+1)+2*E+2*vc+2*X := by
    intro jc bc hjc hbc hbcrow X hexit
    have hend : ((groupCol jc).val+1)*s ≤ n := by
      calc
        _ ≤ k*s := Nat.mul_le_mul_right _ (groupCol jc).isLt
        _ = n := hk.mul_side
    let column : Fin n := ⟨(groupCol jc).val*s+I.val, by nlinarith⟩
    obtain ⟨B, p, -, hBr, hcol, hAB, -, hpr, hpl⟩ :=
      exists_transport_horizontal_path hk hn2 A hA I low hi column
    obtain ⟨C, q, hCV, hrow, hAC, hq⟩ := hvertical A B hA I jc hAB low
      (by rw [hjc, ha, haJ]; exact hlowd) (by rw [ha]; exact hlowk) hBr
      (by rw [hcol]) bc hbc
    have hvq : verticalCost (n := n) I jc low bc.1.val = vc := by
      rw [hvcdef]; unfold verticalCost; rw [hjc, hbcrow]
    rw [hvq] at hq
    obtain ⟨D, r, hAD, hbD, hr⟩ := hexit C hAC hCV (hrow.trans hbcrow)
    have htop' : Nat.dist (blank A).1.val (corridorRow (n := n) I low)+1 ≤ 2*k+1 := by
      rw [hyA]; unfold corridorRow
      rw [ha, ← hs]
      cases hlv : low
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.dist]; omega
      · have hak := hlowk hlv
        have hnb : nextBand k a = a+1 := Nat.mod_eq_of_lt hak
        simp only [↓reduceIte, Nat.dist, hnb, Nat.add_mul, Nat.one_mul]; omega
    have hh : 2*p.inefficientMoves ≤ bwI+26*(2*k+1) := by
      rw [hbwI']
      by_cases h : c ≤ column.val
      · have := hpr h; rw [← hc, ← hs] at this; omega
      · have := hpl (not_le.mp h); rw [← hc, ← hs] at this; omega
    refine ⟨D, p.append (q.append r), hAD, hbD, ?_⟩
    simp only [Path.inefficientMoves_append]
    omega
  have hb' := hb
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb'
  simp only [Nat.add_mul, Nat.one_mul, ← hs] at hb1 hb2 hb3 hb4
  have hgcJ := (groupCol J).isLt
  -- Exit through the nearer side, which is the left one in the last column.
  set o := b.2.val-(groupCol J).val*s with ho
  have hmain : ∃ D : Board n, ∃ p : Path A D, GroupEquivalent I A D ∧ blank D = b ∧
      2*p.inefficientMoves ≤ bwI+26*(2*k+1)+2*E+2*vc+150*k^2+600+
        (if (groupCol J).val+1 < k then 8*min o (s-o) else 8*o) := by
    by_cases hright : (groupCol J).val+1 < k ∧ s-o < o
    · let J' : GroupIndex k := finProdFinEquiv (groupRow J, ⟨(groupCol J).val+1, hright.1⟩)
      have hrowJ : groupRow J' = groupRow J := by simp [J', groupRow]
      have hcolJ : (groupCol J').val = (groupCol J).val+1 := by simp [J', groupCol]
      have hend : ((groupCol J').val+1)*s ≤ n := by
        calc
          _ ≤ k*s := Nat.mul_le_mul_right _ (groupCol J').isLt
          _ = n := hk.mul_side
      simp only [Nat.add_mul, Nat.one_mul] at hend
      let bc : Cell n := (b.1, ⟨(groupCol J').val*s+k^2, by omega⟩)
      have hbc : reservoir J' bc := by
        refine ⟨by rw [hrowJ]; exact hb1, by rw [hrowJ, Nat.add_mul, Nat.one_mul]; exact hb2,
          le_rfl, by simp only [bc, Nat.add_mul, Nat.one_mul, ← hs]; omega⟩
      obtain ⟨D, p, hD, hbD, hp⟩ := hroute J' bc hrowJ hbc rfl
        (4*(((groupCol J).val+1)*s-b.2.val)+75*k^2+300) (fun C hAC hCV hrow =>
          exists_transport_exit_right hk A C hA I J J' hrowJ hcolJ hAC b hb ht hCV hrow)
      refine ⟨D, p, hD, hbD, ?_⟩
      rw [if_pos hright.1]
      simp only [Nat.add_mul, Nat.one_mul] at hp
      omega
    · obtain ⟨D, p, hD, hbD, hp⟩ := hroute J b rfl hb rfl
        (4*(b.2.val-(groupCol J).val*s)+75*k^2+300) (fun C hAC hCV hrow =>
          exists_transport_exit_left hk A C hA I J hAC b hb ht hCV hrow)
      refine ⟨D, p, hD, hbD, ?_⟩
      split_ifs with h
      · have : o ≤ s-o := by omega
        omega
      · omega
  obtain ⟨D, p, hAD, hbD, hp⟩ := hmain
  have hbDJ : reservoir J (blank D) := by rw [hbD]; exact hb
  have hIJ : I ≠ J := hIJ'
  refine ⟨D, p₀.append p, hAD.clear hk hA hbDJ, hbDJ, ?_, ?_⟩
  · rw [hAD.boardMatrix_eq_swap hk I A D b ht hbD, hmatrixSwap, hmat₀]
  · have hwD := wrongPotential_transfer hk hAD hi hbD hb hIJ ht
    have hbD' := blankPotential_eq (k := k) hk hbDJ
    have hbA := blankPotential_eq (k := k) hk hi₀
    unfold transportPotential
    have hcc : (blank A₀).2.val = c := by rw [hc, hcolA]
    rw [hbD', hbA, ← hpot₀, hbD, hcc, ← hbwI]
    have hew : exitWeight (n := n) J b.2.val = blankWeight (n := n) J b.2.val+
        (if (groupCol J).val+1 < k then 8*min o (s-o) else 8*o) := rfl
    simp only [Path.inefficientMoves_append]
    have h₀ := p₀.inefficientMoves_le_length
    change 2*(p₀.inefficientMoves+p.inefficientMoves)+_ ≤
      2*s+2*E+160*k^2+60*k+800+(if (groupRow J).val+1 = k then 2*s else 0)+_
    rw [haJ]
    rw [hew] at hwD
    split_ifs at hvc ⊢ <;> omega

end
end SlidingPuzzle.Partition
