import SlidingPuzzle.Algorithm.Transport.Labels

/-! The transport potential, charged per reservoir cell.

The exit restores the source reservoir (`exists_restore_carry`), and the blank's
slide inside its own reservoir stays in one column. So a misplaced reservoir
tile never changes column before it is transported, and each can be charged,
once, according to its column: the exit through the nearer side of its square
and the next transfer's horizontal travel from its cell (`exitWeight`). The
blank's own column pays for the horizontal travel of the transfer about to
start (`blankWeight`). Averaged over the columns of a square, the weight is
`3.5*s`, against `5*s` per transfer for the look-ahead charge it replaces. -/
namespace SlidingPuzzle.Partition
noncomputable section
open Classical

variable {n k : ℕ} [NeZero n]

/-- The position of column `c` inside the column of squares of `J`. -/
def offset (J : GroupIndex k) (c : ℕ) : ℕ := c-(groupCol J).val*side n k

/-- Horizontal travel from column `c` to either side of the square `J`,
doubled: at most `2*max(o, s-o)+2` for the offset `o`. -/
def blankWeight (J : GroupIndex k) (c : ℕ) : ℕ :=
  2*(side n k-min (offset (n := n) J c) (side n k-offset (n := n) J c))+2

/-- The doubled charge of a misplaced tile in column `c` of the reservoir `J`:
the horizontal travel of the next transfer from its cell, and its exit through
the nearer side, the left one in the last column of squares (four inefficient
moves per cell). -/
def exitWeight (J : GroupIndex k) (c : ℕ) : ℕ :=
  blankWeight (n := n) J c+(if (groupCol J).val+1 < k then
    8*min (offset (n := n) J c) (side n k-offset (n := n) J c) else 8*offset (n := n) J c)

/-- The charge of the tile `t` in the cell `x`: its exit weight if `x` lies in
a reservoir whose group `t` does not belong to. -/
def cellWeight (x : Cell n) (t : Tile n) : ℕ :=
  ∑ J : GroupIndex k, if reservoir J x ∧ t ≠ 0 ∧ t ∉ targetGroup J then
    exitWeight (n := n) J x.2.val else 0

/-- The total charge of the misplaced reservoir tiles. -/
def wrongPotential (B : Board n) : ℕ := ∑ x, cellWeight (k := k) x (B x)

/-- The blank's charge in its reservoir. -/
def blankPotential (B : Board n) : ℕ :=
  ∑ J : GroupIndex k, if reservoir J (blank B) then blankWeight (n := n) J (blank B).2.val else 0

/-- The transport potential. -/
def transportPotential (B : Board n) : ℕ :=
  wrongPotential (k := k) B+blankPotential (k := k) B

theorem cellWeight_of_reservoir (hk : Dims n k) {I : GroupIndex k} {x : Cell n}
    (hx : reservoir I x) (t : Tile n) :
    cellWeight (k := k) x t =
      if t ≠ 0 ∧ t ∉ targetGroup I then exitWeight (n := n) I x.2.val else 0 := by
  unfold cellWeight
  rw [Finset.sum_eq_single I]
  · simp [hx]
  · intro J _ hJ
    rw [if_neg]
    exact fun h => hJ (reservoir_unique hk h.1 hx)
  · simp

theorem cellWeight_zero (x : Cell n) : cellWeight (k := k) x 0 = 0 := by
  simp [cellWeight]

theorem blankPotential_eq (hk : Dims n k) {B : Board n} {I : GroupIndex k}
    (h : reservoir I (blank B)) :
    blankPotential (k := k) B = blankWeight (n := n) I (blank B).2.val := by
  unfold blankPotential
  rw [Finset.sum_eq_single I]
  · simp [h]
  · intro J _ hJ
    rw [if_neg]
    exact fun h' => hJ (reservoir_unique hk h' h)
  · simp

theorem blankPotential_le (hk : Dims n k) (B : Board n) :
    blankPotential (k := k) B ≤ 2*side n k+2 := by
  by_cases h : ∃ J : GroupIndex k, reservoir J (blank B)
  · obtain ⟨I, hI⟩ := h
    rw [blankPotential_eq hk hI]
    unfold blankWeight; omega
  · push Not at h
    simp [blankPotential, h]

/-- Exchanging two cells of one reservoir column keeps the charge. -/
theorem wrongPotential_swap_same (hk : Dims n k) (B : Board n) {I : GroupIndex k}
    {a c : Cell n} (ha : reservoir I a) (hc : reservoir I c) (hcol : a.2 = c.2) :
    wrongPotential (k := k) (swapCells B a c) = wrongPotential (k := k) B := by
  have hF : ∀ x t, cellWeight (k := k) (Equiv.swap a c x) t = cellWeight (k := k) x t := by
    intro x t
    rcases eq_or_ne x a with rfl | hxa
    · rw [Equiv.swap_apply_left, cellWeight_of_reservoir hk hc, cellWeight_of_reservoir hk ha, hcol]
    rcases eq_or_ne x c with rfl | hxc
    · rw [Equiv.swap_apply_right, cellWeight_of_reservoir hk hc, cellWeight_of_reservoir hk ha, hcol]
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxc]
  unfold wrongPotential
  refine Fintype.sum_equiv (Equiv.swap a c) _ _ (fun x => ?_)
  rw [swapCells_apply]
  exact (hF x _).symm

/-- A transfer from the reservoir `I` removes the charge of the transported
tile, the blank ending on its cell `b`; the tile brought into `I` is not
misplaced. Nothing else changes membership. -/
theorem wrongPotential_transfer (hk : Dims n k) {A D : Board n} {I J : GroupIndex k}
    (hAD : GroupEquivalent I A D) (hA : reservoir I (blank A)) {b : Cell n}
    (hD : blank D = b) (hb : reservoir J b) (hIJ : I ≠ J) (ht : A b ∈ targetGroup I) :
    wrongPotential (k := k) D+exitWeight (n := n) J b.2.val ≤ wrongPotential (k := k) A := by
  have hpt : ∀ x, cellWeight (k := k) x (D x)+(if x = b then exitWeight (n := n) J b.2.val else 0) ≤
      cellWeight (k := k) x (A x) := by
    intro x
    by_cases hxb : x = b
    · subst hxb
      rw [if_pos rfl, ← hD, show D (blank D) = 0 from D.apply_symm_apply 0, cellWeight_zero, hD,
        cellWeight_of_reservoir hk hb]
      have hA0 : A x ≠ 0 := fun h => by rw [h] at ht; exact zero_not_mem_targetGroup I ht
      have hnot : A x ∉ targetGroup J := fun h =>
        hIJ ((targetGroup_membership_iff hk ht J).mp h).symm
      simp [hA0, hnot]
    · rw [if_neg hxb, add_zero]
      by_cases hxa : x = blank A
      · have hDx : D x ∈ targetGroup I := by
          rcases (hAD x I).mp (Or.inr ⟨hxa, rfl⟩) with h | h
          · exact h
          · exact absurd (h.1.trans hD) hxb
        rw [hxa] at hDx ⊢
        rw [cellWeight_of_reservoir hk hA, cellWeight_of_reservoir hk hA]
        simp [hDx]
      · have hxD : x ≠ blank D := by rw [hD]; exact hxb
        have hiff : ∀ j : GroupIndex k, A x ∈ targetGroup j ↔ D x ∈ targetGroup j := by
          intro j; simpa [hxa, hxD] using hAD x j
        have hA0 : A x ≠ 0 := fun h => hxa (by simp [blank, position, ← h])
        have hD0 : D x ≠ 0 := fun h => hxD (by simp [blank, position, ← h])
        unfold cellWeight
        apply le_of_eq
        apply Finset.sum_congr rfl
        intro j _
        simp [hiff j, hA0, hD0]
  calc wrongPotential (k := k) D+exitWeight (n := n) J b.2.val =
        ∑ x, (cellWeight (k := k) x (D x)+(if x = b then exitWeight (n := n) J b.2.val else 0)) := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq']; simp [wrongPotential]
    _ ≤ ∑ x, cellWeight (k := k) x (A x) := Finset.sum_le_sum (fun x _ => hpt x)

/-- The sum of `min(o, s-o)` over a row of `s` columns is at most `s²/4`. -/
theorem four_sum_min_le (s : ℕ) : 4*∑ o ∈ Finset.range s, min o (s-o) ≤ s^2 := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    rcases s with _ | _ | s
    · simp
    · simp
    · have hstep : ∑ o ∈ Finset.range (s+2), min o (s+2-o) =
          ∑ o ∈ Finset.range s, min o (s-o)+(s+1) := by
        rw [Finset.sum_range_succ']
        have h1 : ∑ o ∈ Finset.range (s+1), min (o+1) (s+2-(o+1)) =
            ∑ o ∈ Finset.range (s+1), (min o (s-o)+1) := by
          apply Finset.sum_congr rfl
          intro o ho
          have := Finset.mem_range.mp ho
          omega
        rw [h1, Finset.sum_add_distrib, Finset.sum_range_succ]
        simp
      have := ih s (by omega)
      rw [show s+1+1 = s+2 by ring, hstep]
      nlinarith

/-- Sums over the cells of `Fin N` in an interval `[a, a+s)`. -/
theorem sum_fin_interval_le (N a s : ℕ) (g : ℕ → ℕ) :
    ∑ c : Fin N, (if a ≤ c.val ∧ c.val < a+s then g c.val else 0) ≤
      ∑ o ∈ Finset.range s, g (a+o) := by
  have hr : ∑ o ∈ Finset.range s, g (a+o) = ∑ c ∈ Finset.Ico a (a+s), g c := by
    rw [Finset.sum_Ico_eq_sum_range]; simp
  rw [Fin.sum_univ_eq_sum_range (fun c => if a ≤ c ∧ c < a+s then g c else 0),
    ← Finset.sum_filter, hr]
  apply Finset.sum_le_sum_of_subset
  intro c hc
  simp only [Finset.mem_filter, Finset.mem_range] at hc
  simp only [Finset.mem_Ico]
  omega

omit [NeZero n] in
/-- Each reservoir holds at most `s` rows of its square's columns. -/
theorem sum_reservoir_le (J : GroupIndex k) (f : ℕ → ℕ) :
    ∑ x : Cell n, (if reservoir J x then f x.2.val else 0) ≤
      side n k*∑ o ∈ Finset.range (side n k), f ((groupCol J).val*side n k+o) := by
  calc ∑ x : Cell n, (if reservoir J x then f x.2.val else 0)
      ≤ ∑ x : Cell n, (if (groupRow J).val*side n k ≤ x.1.val ∧
            x.1.val < (groupRow J).val*side n k+side n k then 1 else 0)*
          (if (groupCol J).val*side n k ≤ x.2.val ∧
            x.2.val < (groupCol J).val*side n k+side n k then f x.2.val else 0) := by
        apply Finset.sum_le_sum
        intro x _
        by_cases h : reservoir J x
        · obtain ⟨h1, h2, h3, h4⟩ := h
          simp only [Nat.add_mul, Nat.one_mul] at h2 h4
          rw [if_pos ⟨h1, by simpa [Nat.add_mul] using h2, h3, by simpa [Nat.add_mul] using h4⟩,
            if_pos ⟨by omega, h2⟩, if_pos ⟨by omega, h4⟩, one_mul]
        · rw [if_neg h]; exact Nat.zero_le _
    _ = (∑ r : Fin n, (if (groupRow J).val*side n k ≤ r.val ∧
            r.val < (groupRow J).val*side n k+side n k then 1 else 0))*
          ∑ c : Fin n, (if (groupCol J).val*side n k ≤ c.val ∧
            c.val < (groupCol J).val*side n k+side n k then f c.val else 0) := by
        rw [Fintype.sum_prod_type, Finset.sum_mul]
        simp only [Finset.mul_sum]
    _ ≤ side n k*∑ o ∈ Finset.range (side n k), f ((groupCol J).val*side n k+o) := by
        apply Nat.mul_le_mul
        · simpa using sum_fin_interval_le n ((groupRow J).val*side n k) (side n k) (fun _ => 1)
        · exact sum_fin_interval_le n _ _ f

omit [NeZero n] in
/-- The charge of one reservoir: `3.5*s³` up to lower order, and `6*s³` in the
last column of squares. -/
theorem four_sum_exitWeight_le (J : GroupIndex k) :
    4*∑ o ∈ Finset.range (side n k), exitWeight (n := n) J ((groupCol J).val*side n k+o) ≤
      14*side n k^2+8*side n k+(if (groupCol J).val+1 < k then 0 else 10*side n k^2) := by
  have hoff : ∀ o, offset (n := n) J ((groupCol J).val*side n k+o) = o := by
    intro o; unfold offset; omega
  unfold exitWeight blankWeight
  simp only [hoff]
  generalize side n k = s
  have hmin := four_sum_min_le s
  have hid := Finset.sum_range_id_mul_two s
  split_ifs with h
  · have hpt : ∀ o ∈ Finset.range s,
        2*(s-min o (s-o))+2+8*min o (s-o) = 2*s+2+6*min o (s-o) := by
      intro o ho; have := Finset.mem_range.mp ho; omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      ← Finset.mul_sum]
    simp only [smul_eq_mul]
    nlinarith
  · have hpt : ∀ o ∈ Finset.range s,
        2*(s-min o (s-o))+2+8*o ≤ 2*s+2+8*o := by
      intro o _; omega
    refine (Nat.mul_le_mul_left 4 (Finset.sum_le_sum hpt)).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum]
    simp only [smul_eq_mul]
    have hs : (s-1)*s ≤ s^2 := by
      calc (s-1)*s ≤ s*s := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
        _ = s^2 := (sq s).symm
    nlinarith

/-- The initial charge: `3.5*k²s³` up to lower order. -/
theorem four_wrongPotential_le (hk : Dims n k) (B : Board n) :
    4*wrongPotential (k := k) B ≤
      14*(k^2*side n k^3)+8*(k^2*side n k^2)+10*(k*side n k^3) := by
  set s := side n k
  have hcell : ∀ x : Cell n, cellWeight (k := k) x (B x) ≤
      ∑ J : GroupIndex k, (if reservoir J x then exitWeight (n := n) J x.2.val else 0) := by
    intro x
    apply Finset.sum_le_sum
    intro J _
    split_ifs with h1 h2 <;> first | exact le_rfl | exact Nat.zero_le _ | exact absurd h1.1 h2
  have hsum : 4*wrongPotential (k := k) B ≤ ∑ J : GroupIndex k,
      s*(14*s^2+8*s+(if (groupCol J).val+1 < k then 0 else 10*s^2)) := by
    calc 4*wrongPotential (k := k) B
        ≤ 4*∑ x : Cell n, ∑ J : GroupIndex k,
            (if reservoir J x then exitWeight (n := n) J x.2.val else 0) :=
          Nat.mul_le_mul_left 4 (Finset.sum_le_sum (fun x _ => hcell x))
      _ = ∑ J : GroupIndex k, 4*∑ x : Cell n,
            (if reservoir J x then exitWeight (n := n) J x.2.val else 0) := by
          rw [Finset.sum_comm, Finset.mul_sum]
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro J _
          have h1 := sum_reservoir_le (n := n) J (exitWeight (n := n) J)
          have h2 := four_sum_exitWeight_le (n := n) J
          calc 4*∑ x : Cell n, (if reservoir J x then exitWeight (n := n) J x.2.val else 0)
              ≤ 4*(s*∑ o ∈ Finset.range s, exitWeight (n := n) J ((groupCol J).val*s+o)) :=
                Nat.mul_le_mul_left 4 h1
            _ = s*(4*∑ o ∈ Finset.range s, exitWeight (n := n) J ((groupCol J).val*s+o)) := by
                ring
            _ ≤ _ := Nat.mul_le_mul_left s h2
  refine hsum.trans (le_of_eq ?_)
  have hsplit : ∀ J : GroupIndex k, s*(14*s^2+8*s+(if (groupCol J).val+1 < k then 0 else 10*s^2)) =
      (14*s^3+8*s^2)+(if (groupCol J).val+1 = k then 10*s^3 else 0) := by
    intro J
    have := (groupCol J).isLt
    by_cases h : (groupCol J).val+1 = k
    · rw [if_neg (by omega), if_pos h]; ring
    · rw [if_pos (by omega), if_neg h]; ring
  rw [Finset.sum_congr rfl (fun J _ => hsplit J), Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ]
  have hlast : ∑ J : GroupIndex k, (if (groupCol J).val+1 = k then 10*s^3 else 0) = k*(10*s^3) := by
    rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    simp only [groupCol, Equiv.symm_apply_apply]
    have hk0 : 0 < k := by have := hk.two_le; omega
    have hinner : ∑ b : Fin k, (if b.val+1 = k then 10*s^3 else 0) = 10*s^3 := by
      rw [Finset.sum_eq_single ⟨k-1, by omega⟩]
      · simp; omega
      · intro b _ hb
        rw [if_neg]
        intro h
        exact hb (Fin.ext (by simp; omega))
      · simp
    simp only [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [hlast]
  simp only [Fintype.card_fin, smul_eq_mul]
  ring

end
end SlidingPuzzle.Partition
