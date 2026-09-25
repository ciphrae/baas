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

set_option maxHeartbeats 2000000 in
/-- The transfer step with look-ahead. The blank slides to the top of its
reservoir, enters `H_i`, travels to a vertical corridor next to the source
square, descends and exits. The exit side, left through the source square's own
corridor or right through its neighbour's, is chosen against both the tile's
position and the direction of the next transfer, which the count run already
determines. With the state potential (`transferPotential`), doubled horizontal
travel and exit together cost at most `6*s` on average; the rightmost column of
squares, which has no right side, pays `4*s` more. -/
theorem transportStepBoundAmortized_of_vertical_bound {n k E : ℕ} [NeZero n]
    (hk : Dims n k)
    (hvertical : VerticalTransportBound (n := n) hk E) :
    TransportStepBoundAmortized (n := n) hk (fun r => 4*side n k+E+80*k^2+13*k+200+
      if (groupCol (transportIndex k hk r)).val+1 = k then 4*side n k else 0) := by
  classical
  intro A₀ hA₀ i j hi₀ hchoice₀
  obtain ⟨A, p₀, hA, hi, htop, hcolA, hmat₀, hlen₀⟩ :=
    exists_reservoir_top_path hk A₀ hA₀ _ hi₀
  have hchoice : TransportCounts.Chooses (boardMatrix hk A) i j := by
    rw [hmat₀]; exact hchoice₀
  obtain ⟨b, hb, ht, _hclearSwap, hmatrixSwap⟩ := boardMatrix_choice_endpoint hk A hA i j hi hchoice
  set I := transportIndex k hk i with hI
  set J := transportIndex k hk j with hJ
  set s := side n k with hs
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
  -- The next transfer, determined by the count run.
  set M' := TransportCounts.move (boardMatrix hk A₀) i j with hM'
  set ex := ∃ j₂, TransportCounts.Chooses M' j j₂ with hex
  let g : ℕ := if h : ex then (groupCol (transportIndex k hk h.choose)).val else 0
  have hPn : ∀ D : Board n, boardMatrix hk D = M' → reservoir J (blank D) →
      statePotential hk D (boardMatrix hk D) j ≤
        if ex then (if (groupCol J).val < g then
            2*((groupCol J).val*s+s+1-(blank D).2.val)
          else if g < (groupCol J).val then 2*((blank D).2.val+1-(groupCol J).val*s)
          else s) else 0 := by
    intro D hD _
    rw [hD]
    unfold statePotential
    by_cases hx : ex
    · rw [dif_pos hx, if_pos hx]
      simp only [g, dif_pos hx, transferPotential]
      exact le_refl _
    · rw [dif_neg hx, if_neg hx]
  -- Route to a vertical corridor of `jc` and exit.
  have hroute : ∀ (jc : GroupIndex k) (bc : Cell n), reservoir jc bc → bc.1 = b.1 →
      ∀ (X : ℕ) (Q : ℕ → Prop), (∀ C : Board n, GroupEquivalent I A C →
        vertical jc I (blank C) → (blank C).1 = b.1 →
        ∃ D : Board n, ∃ q : Path C D, Clear (k := k) D ∧ reservoir J (blank D) ∧
          boardMatrix hk D = boardMatrix hk (swapCells A (blank A) b) ∧
          q.inefficientMoves ≤ X ∧ Q (blank D).2.val) →
      ∃ D : Board n, ∃ p : Path A D, Clear (k := k) D ∧ reservoir J (blank D) ∧
        boardMatrix hk D = boardMatrix hk (swapCells A (blank A) b) ∧ Q (blank D).2.val ∧
        (c ≤ (groupCol jc).val*s+I.val → 2*p.inefficientMoves ≤
          2*((groupCol I).val*s+s+1-c)+26*(k+1)+2*E+2*X) ∧
        ((groupCol jc).val*s+I.val < c → 2*p.inefficientMoves ≤
          2*(c+1-(groupCol I).val*s)+26*(k+1)+2*E+2*X) := by
    intro jc bc hbc hbcrow X Q hexit
    have hend : ((groupCol jc).val+1)*s ≤ n := by
      calc
        _ ≤ k*s := Nat.mul_le_mul_right _ (groupCol jc).isLt
        _ = n := hk.mul_side
    let column : Fin n := ⟨(groupCol jc).val*s+I.val, by nlinarith⟩
    obtain ⟨B, p, hBH, hcol, hAB, -, hpr, hpl⟩ :=
      exists_transport_horizontal_path hk hn2 A hA I hi column
    obtain ⟨C, q, hCV, hrow, hAC, hq⟩ := hvertical A B hA I jc hAB hBH
      (by rw [hcol]) bc hbc
    obtain ⟨D, r, hD, hbD, hmD, hr, hQ⟩ := hexit C hAC hCV (hrow.trans hbcrow)
    have hhi := hi.2.1
    rw [Nat.add_mul, Nat.one_mul] at hhi
    have hgc := (groupCol I).isLt
    have htop' : (blank A).1.val-((groupRow I).val*s+(groupCol I).val)+1 ≤ k+1 := by
      omega
    refine ⟨D, p.append (q.append r), hD, hbD, hmD, hQ, ?_, ?_⟩
    · intro h
      have := hpr h
      simp only [Path.inefficientMoves_append]
      nlinarith
    · intro h
      have := hpl h
      simp only [Path.inefficientMoves_append]
      nlinarith
  have hb' := hb
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb'
  simp only [Nat.add_mul, Nat.one_mul, ← hs] at hb1 hb2 hb3 hb4
  have hgcJ := (groupCol J).isLt
  have hgcI := (groupCol I).isLt
  -- Products of square coordinates with the side.
  have hgap : ∀ a b : ℕ, a < b → a*s+s ≤ b*s := by
    intro a b h
    have := Nat.mul_le_mul_right s (show a+1 ≤ b by omega)
    simpa [Nat.add_mul] using this
  have hIJ : (groupCol I).val < (groupCol J).val ∨ (groupCol J).val < (groupCol I).val ∨
      (groupCol I).val*s = (groupCol J).val*s := by
    rcases lt_trichotomy (groupCol I).val (groupCol J).val with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (by rw [h]))
    · exact Or.inr (Or.inl h)
  -- The bound on the next potential after each exit side.
  let PL : ℕ := if ex then
    (if (groupCol J).val < g then 2*s else if g < (groupCol J).val then 2*k^2+6 else s) else 0
  let PR : ℕ := if ex then
    (if (groupCol J).val < g then 8 else if g < (groupCol J).val then 2*s else s) else 0
  have hPL : ∀ D : Board n, boardMatrix hk D = M' → reservoir J (blank D) →
      (blank D).2.val ≤ (groupCol J).val*s+k^2+2 → statePotential hk D (boardMatrix hk D) j ≤ PL := by
    intro D hD hres hcD
    refine (hPn D hD hres).trans ?_
    have h1 := hres.2.2.1
    simp only [← hs] at h1
    simp only [PL]
    split_ifs <;> omega
  have hPR : ∀ D : Board n, boardMatrix hk D = M' → reservoir J (blank D) →
      ((groupCol J).val+1)*s ≤ (blank D).2.val+3 →
      statePotential hk D (boardMatrix hk D) j ≤ PR := by
    intro D hD hres hcD
    refine (hPn D hD hres).trans ?_
    have h2 := hres.2.2.2
    simp only [Nat.add_mul, Nat.one_mul, ← hs] at h2 hcD
    simp only [PR]
    split_ifs <;> omega
  have hPLR : PL+PR ≤ 2*s+2*k^2+8 := by
    simp only [PL, PR]; split_ifs <;> omega
  -- Horizontal costs of the two sides, and the current potential.
  set colL := (groupCol J).val*s+I.val with hcolL
  set colR := ((groupCol J).val+1)*s+I.val with hcolR
  have hcolR' : colR = (groupCol J).val*s+s+I.val := by rw [hcolR]; ring
  let HL : ℕ := if c ≤ colL then 2*((groupCol I).val*s+s+1-c) else 2*(c+1-(groupCol I).val*s)
  let HR : ℕ := if c ≤ colR then 2*((groupCol I).val*s+s+1-c) else 2*(c+1-(groupCol I).val*s)
  set Ψ := transferPotential (n := n) (blank A₀).2.val I J with hΨ
  have hΨ' : Ψ = if (groupCol I).val < (groupCol J).val then 2*((groupCol I).val*s+s+1-c)
      else if (groupCol J).val < (groupCol I).val then 2*(c+1-(groupCol I).val*s) else s := by
    rw [hΨ, hc, ← hcolA]; rfl
  set dL := b.2.val-(groupCol J).val*s with hdL
  set dR := (groupCol J).val*s+s-b.2.val with hdR
  have hPLs : PL ≤ 2*s+2*k^2+6 := by simp only [PL]; split_ifs <;> omega
  have hHsum : HL+10*dL+PL+(HR+10*dR+PR) ≤ 12*s+2*Ψ+2*k^2+12 := by
    rcases lt_trichotomy (groupCol I).val (groupCol J).val with h | h | h
    · have hg := hgap _ _ h
      have hL : c ≤ colL := by omega
      have hR : c ≤ colR := by omega
      simp only [HL, HR, if_pos hL, if_pos hR, hΨ', if_pos h]; omega
    · have hg : (groupCol I).val*s = (groupCol J).val*s := by rw [h]
      have hL : ¬ c ≤ colL := by omega
      have hR : c ≤ colR := by omega
      simp only [HL, HR, if_neg hL, if_pos hR, hΨ', h, lt_irrefl, if_false]; omega
    · have hg := hgap _ _ h
      have hL : ¬ c ≤ colL := by omega
      have hR : ¬ c ≤ colR := by omega
      simp only [HL, HR, if_neg hL, if_neg hR, hΨ', if_neg (not_lt.mpr h.le), if_pos h]; omega
  have hHL : HL+10*dL+PL ≤ 13*s+Ψ+2*k^2+12 := by
    rcases lt_trichotomy (groupCol I).val (groupCol J).val with h | h | h
    · have hg := hgap _ _ h
      have hL : c ≤ colL := by omega
      simp only [HL, if_pos hL, hΨ', if_pos h]; omega
    · have hg : (groupCol I).val*s = (groupCol J).val*s := by rw [h]
      have hL : ¬ c ≤ colL := by omega
      simp only [HL, if_neg hL, hΨ', h, lt_irrefl, if_false]; omega
    · have hg := hgap _ _ h
      have hL : ¬ c ≤ colL := by omega
      simp only [HL, if_neg hL, hΨ', if_neg (not_lt.mpr h.le), if_pos h]; omega
  -- Choose the side.
  have hmain : ∃ D : Board n, ∃ p : Path A D, Clear (k := k) D ∧ reservoir J (blank D) ∧
      boardMatrix hk D = boardMatrix hk (swapCells A (blank A) b) ∧
      2*p.inefficientMoves+statePotential hk D (boardMatrix hk D) j ≤
        26*(k+1)+2*E+2*(75*k^2+177)+6*s+Ψ+k^2+6+
          (if (groupCol J).val+1 = k then 8*s else 0) := by
    have hMD : ∀ D : Board n, boardMatrix hk D = boardMatrix hk (swapCells A (blank A) b) →
        boardMatrix hk D = M' := by
      intro D h; rw [h, hmatrixSwap, hmat₀]
    by_cases hright : (groupCol J).val+1 < k ∧ HR+10*dR+PR ≤ HL+10*dL+PL
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
      obtain ⟨D, p, hD, hbD, hmD, hQ, hpr, hpl⟩ := hroute J' bc hbc rfl
        (5*dR+75*k^2+177) (fun c' => ((groupCol J).val+1)*s ≤ c'+3) (by
          intro C hAC hCV hrow
          obtain ⟨D, q, h1, h2, h3, h4, h5⟩ :=
            exists_transport_exit_right hk A C hA I J J' hrowJ hcolJ hAC b hb ht hCV hrow
          refine ⟨D, q, h1, h2, h3, ?_, h5⟩
          simp only [hdR, Nat.add_mul, Nat.one_mul, ← hs] at h4 ⊢; omega)
      refine ⟨D, p, hD, hbD, hmD, ?_⟩
      have hP := hPR D (hMD D hmD) hbD hQ
      rw [hcolJ, ← hcolR] at hpr hpl
      have hsum := hHsum
      have hle := hright.2
      simp only [HR] at hle hsum
      split_ifs at hle hsum with h1 <;>
        [have := hpr h1; have := hpl (not_le.mp h1)] <;> split_ifs <;> omega
    · obtain ⟨D, p, hD, hbD, hmD, hQ, hpr, hpl⟩ := hroute J b hb rfl
        (5*dL+75*k^2+177) (fun c' => c' ≤ (groupCol J).val*s+k^2+2) (by
          intro C hAC hCV hrow
          obtain ⟨D, q, h1, h2, h3, h4, h5⟩ :=
            exists_transport_exit_left hk A C hA I J hAC b hb ht hCV hrow
          exact ⟨D, q, h1, h2, h3, h4, h5⟩)
      refine ⟨D, p, hD, hbD, hmD, ?_⟩
      have hP := hPL D (hMD D hmD) hbD hQ
      rw [← hcolL] at hpr hpl
      have hsum := hHsum
      have hone := hHL
      simp only [HL] at hsum hone hright
      by_cases hlast : (groupCol J).val+1 = k
      · rw [if_pos hlast]
        split_ifs at hsum hone with h1 <;>
          [have := hpr h1; have := hpl (not_le.mp h1)] <;> omega
      · rw [if_neg hlast]
        have hlt : (groupCol J).val+1 < k := by omega
        have hle := not_le.mp (fun h => hright ⟨hlt, h⟩)
        split_ifs at hsum hone hle with h1 <;>
          [have := hpr h1; have := hpl (not_le.mp h1)] <;> omega
  obtain ⟨D, p, hD, hblankD, hmD, hp⟩ := hmain
  refine ⟨D, p₀.append p, hD, hblankD, ?_, ?_⟩
  · rw [hmD, hmatrixSwap, hmat₀]
  · simp only [Path.inefficientMoves_append]
    have h₀ := p₀.inefficientMoves_le_length
    have hres := hi₀.2.1
    have hres' := hi.1
    rw [Nat.add_mul, Nat.one_mul] at hres
    have hrow0 : (groupRow I).val*s+k ≤ (blank A).1.val := hi.1
    change 2*(p₀.inefficientMoves+p.inefficientMoves)+_ ≤
      2*(4*s+E+80*k^2+13*k+200+(if (groupCol J).val+1 = k then 4*s else 0))+Ψ
    split_ifs at hp ⊢ <;> omega

end
end SlidingPuzzle.Partition

