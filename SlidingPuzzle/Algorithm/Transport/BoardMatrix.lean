import SlidingPuzzle.Algorithm.Transport.CountSwap
import SlidingPuzzle.Algorithm.Transport.Counts

/-! The transport matrix margins instantiated by actual clear boards. -/
namespace SlidingPuzzle.Partition
noncomputable section
open Classical

def transportIndex (k : ℕ) (hk : 2 ≤ k) : Fin (k*k-1+1) ≃ GroupIndex k :=
  finCongr (Nat.sub_add_cancel (by nlinarith))

@[simp] theorem transportIndex_last (k : ℕ) (hk : 2 ≤ k) :
    transportIndex k hk (Fin.last (k*k-1)) = lastGroup k hk := by
  apply Fin.ext
  exact (lastGroup_val k hk).symm

def boardMatrix {n k : ℕ} (hk : Dims n k) (B : Board n) :
    TransportCounts.CountMatrix (k*k-1) :=
  fun i j => reservoirCount B (transportIndex k hk i) (transportIndex k hk j)

theorem boardMatrix_margins {n k : ℕ} [NeZero n] (hk : Dims n k)
    (B : Board n) (hB : Clear (k := k) B) (b : Fin (k*k-1+1))
    (hb : reservoir (transportIndex k hk b) (blank B)) :
    TransportCounts.Margins (boardMatrix hk B) b ((side n k-2*k)*(side n k-k^2)) := by
  constructor
  · intro r
    have he : reservoir (transportIndex k hk r) (blank B) ↔ r=b :=
      ⟨fun h => (transportIndex k hk).injective (reservoir_unique hk h hb), fun h => h ▸ hb⟩
    have h := reservoirCount_row hk B (transportIndex k hk r)
    simpa only [TransportCounts.rowSum,boardMatrix,Equiv.sum_comp,he] using h
  · intro c
    have he : square (transportIndex k hk c) (blank (target n)) ↔ c=Fin.last (k*k-1) := by
      rw [square_target_blank hk, ← transportIndex_last k hk]
      exact (transportIndex k hk).injective.eq_iff
    have h := reservoirCount_column hk B hB (transportIndex k hk c)
    unfold TransportCounts.colSum boardMatrix
    rw [(transportIndex k hk).sum_comp (fun r => reservoirCount B r (transportIndex k hk c))]
    simpa only [he] using h

/-- A clear board with last-reservoir representatives supplies all hypotheses
of the count-only transport termination theorem. -/
theorem clear_board_has_sorted_count_run {n k : ℕ} [NeZero n]
    (hk : Dims n k) (B : Board n) (hB : Clear (k := k) B)
    (hrep : ∀ j : GroupIndex k, j ≠ lastGroup k hk →
      0 < reservoirCount B (lastGroup k hk) j) :
    ∃ b D j t, reservoir (transportIndex k hk b) (blank B) ∧
      TransportCounts.Run (boardMatrix hk B) b D j t ∧
      t ≤ TransportCounts.offdiagMass (boardMatrix hk B) ∧
      j = Fin.last (k*k-1) ∧ TransportCounts.offdiagMass D = 0 := by
  obtain ⟨i,hi⟩ := blank_in_reservoir hk B hB
  let b := (transportIndex k hk).symm i
  have hb : reservoir (transportIndex k hk b) (blank B) := by simpa [b] using hi
  have hpos : ∀ c, c ≠ Fin.last (k*k-1) →
      0 < boardMatrix hk B (Fin.last (k*k-1)) c := by
    intro c hc
    simp only [boardMatrix,transportIndex_last]
    apply hrep
    intro he
    exact hc ((transportIndex k hk).injective (he.trans (transportIndex_last k hk).symm))
  obtain ⟨D,j,t,hrun,ht,hj,hD⟩ := TransportCounts.exists_sorted_run
    (boardMatrix hk B) b ((side n k-2*k)*(side n k-k^2)) (boardMatrix_margins hk B hB b hb)
    (TransportCounts.lastInvariant_of_last_row_positive _ hpos)
  exact ⟨b,D,j,t,hb,hrun,ht,hj,hD⟩
/-- No more than the board's number of cells can be transported. -/
theorem boardMatrix_mass_le {n k : ℕ} [NeZero n] (hk : Dims n k)
    (B : Board n) : TransportCounts.offdiagMass (boardMatrix hk B) ≤ n^2 := by
  have hr (r : Fin (k*k-1+1)) : (∑ c, boardMatrix hk B r c) ≤ (side n k-2*k)*(side n k-k^2) := by
    have h := reservoirCount_row hk B (transportIndex k hk r)
    unfold boardMatrix
    rw [(transportIndex k hk).sum_comp]
    omega
  calc
    _ ≤ ∑ r : Fin (k*k-1+1), ∑ c, boardMatrix hk B r c := by
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro c _
      split_ifs <;> omega
    _ ≤ ∑ _r : Fin (k*k-1+1), (side n k-2*k)*(side n k-k^2) :=
      Finset.sum_le_sum (fun r _ => hr r)
    _ = k^2*((side n k-2*k)*(side n k-k^2)) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
      have hk2 := hk.two_le
      rw [Nat.sub_add_cancel (by nlinarith : 1 ≤ k*k)]
      ring
    _ ≤ k^2*(side n k*side n k) := by gcongr <;> omega
    _ = (k*side n k)^2 := by ring
    _ = n^2 := by rw [hk.mul_side]

/-- Weighted off-diagonal mass for a cost that is `E₀` per transfer plus `X`
for transfers out of the rightmost column of squares. Those reservoirs are only
`k` of `k²`, so the surcharge totals at most `k*s²*X`. -/
theorem weighted_boardMatrix_le {n k : ℕ} [NeZero n] (hk : Dims n k) (B : Board n)
    (E₀ X : ℕ) :
    ∑ r, TransportCounts.rowOff (boardMatrix hk B) r *
        (E₀+if (groupCol (transportIndex k hk r)).val+1 = k then X else 0) ≤
      n^2*E₀+k*(side n k)^2*X := by
  have hrow (r : Fin (k*k-1+1)) : TransportCounts.rowOff (boardMatrix hk B) r ≤ side n k^2 := by
    refine (TransportCounts.rowOff_le_rowSum _ r).trans ?_
    have h := reservoirCount_row hk B (transportIndex k hk r)
    unfold TransportCounts.rowSum boardMatrix
    rw [(transportIndex k hk).sum_comp (fun c => reservoirCount B (transportIndex k hk r) c)]
    have : (side n k-2*k)*(side n k-k^2) ≤ side n k^2 :=
      calc _ ≤ side n k*side n k := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
        _ = side n k^2 := (sq _).symm
    split_ifs at h <;> omega
  let P : GroupIndex k → Prop := fun g => (groupCol g).val+1 = k
  have hsplit : ∑ r, TransportCounts.rowOff (boardMatrix hk B) r *
      (E₀+if P (transportIndex k hk r) then X else 0) =
      TransportCounts.offdiagMass (boardMatrix hk B)*E₀ +
        ∑ r, TransportCounts.rowOff (boardMatrix hk B) r *
          (if P (transportIndex k hk r) then X else 0) := by
    rw [TransportCounts.offdiagMass_eq_sum_rowOff, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    ring
  have hsurcharge : ∑ r, TransportCounts.rowOff (boardMatrix hk B) r *
      (if P (transportIndex k hk r) then X else 0) ≤ k*(side n k)^2*X := by
    calc
      _ ≤ ∑ r, (fun g => if P g then side n k^2*X else 0) (transportIndex k hk r) := by
        apply Finset.sum_le_sum
        intro r _
        dsimp only
        split_ifs
        · exact Nat.mul_le_mul_right _ (hrow r)
        · simp
      _ = ∑ g : GroupIndex k, (if P g then side n k^2*X else 0) :=
        (transportIndex k hk).sum_comp (fun g => if P g then side n k^2*X else 0)
      _ = ∑ q : Fin k × Fin k, (if P (finProdFinEquiv q) then side n k^2*X else 0) :=
        (finProdFinEquiv.sum_comp (fun g => if P g then side n k^2*X else 0)).symm
      _ = ∑ a : Fin k, ∑ b : Fin k, (if b.val+1 = k then side n k^2*X else 0) := by
        rw [Fintype.sum_prod_type]
        simp only [P, groupCol, Equiv.symm_apply_apply]
      _ = k*(side n k)^2*X := by
        have hk0 : 0 < k := by have := hk.two_le; omega
        have hinner : ∑ b : Fin k, (if b.val+1 = k then side n k^2*X else 0) =
            side n k^2*X := by
          rw [Finset.sum_eq_single ⟨k-1, by omega⟩]
          · simp; omega
          · intro b _ hb
            rw [if_neg]
            intro h
            exact hb (Fin.ext (by simp; omega))
          · simp
        simp only [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        ring
  change ∑ r, TransportCounts.rowOff (boardMatrix hk B) r *
      (E₀+if P (transportIndex k hk r) then X else 0) ≤ _
  rw [hsplit]
  have hmass := boardMatrix_mass_le hk B
  have := Nat.mul_le_mul_right E₀ hmass
  omega

/-- The surcharge of the last band of squares is paid at most `k*s²` times. -/
theorem weighted_boardMatrix_le₂ {n k : ℕ} [NeZero n] (hk : Dims n k) (B : Board n)
    (E₀ X Y : ℕ) :
    ∑ r, TransportCounts.rowOff (boardMatrix hk B) r *
        (E₀+(if (groupCol (transportIndex k hk r)).val+1 = k then X else 0)+
          (if (groupRow (transportIndex k hk r)).val+1 = k then Y else 0)) ≤
      n^2*E₀+k*(side n k)^2*X+k*(side n k)^2*Y := by
  have h1 := weighted_boardMatrix_le hk B E₀ X
  have hrow (r : Fin (k*k-1+1)) : TransportCounts.rowOff (boardMatrix hk B) r ≤ side n k^2 := by
    refine (TransportCounts.rowOff_le_rowSum _ r).trans ?_
    have h := reservoirCount_row hk B (transportIndex k hk r)
    unfold TransportCounts.rowSum boardMatrix
    rw [(transportIndex k hk).sum_comp (fun c => reservoirCount B (transportIndex k hk r) c)]
    have : (side n k-2*k)*(side n k-k^2) ≤ side n k^2 :=
      calc _ ≤ side n k*side n k := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
        _ = side n k^2 := (sq _).symm
    split_ifs at h <;> omega
  let P : GroupIndex k → Prop := fun g => (groupRow g).val+1 = k
  have h2 : ∑ r, TransportCounts.rowOff (boardMatrix hk B) r *
      (if P (transportIndex k hk r) then Y else 0) ≤ k*(side n k)^2*Y := by
    calc
      _ ≤ ∑ r, (fun g => if P g then side n k^2*Y else 0) (transportIndex k hk r) := by
        apply Finset.sum_le_sum
        intro r _
        dsimp only
        split_ifs
        · exact Nat.mul_le_mul_right _ (hrow r)
        · simp
      _ = ∑ g : GroupIndex k, (if P g then side n k^2*Y else 0) :=
        (transportIndex k hk).sum_comp (fun g => if P g then side n k^2*Y else 0)
      _ = ∑ q : Fin k × Fin k, (if P (finProdFinEquiv q) then side n k^2*Y else 0) :=
        (finProdFinEquiv.sum_comp (fun g => if P g then side n k^2*Y else 0)).symm
      _ = ∑ a : Fin k, ∑ _b : Fin k, (if a.val+1 = k then side n k^2*Y else 0) := by
        rw [Fintype.sum_prod_type]
        simp only [P, groupRow, Equiv.symm_apply_apply]
      _ = k*(side n k)^2*Y := by
        have hk0 : 0 < k := by have := hk.two_le; omega
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        rw [Finset.sum_eq_single ⟨k-1, by omega⟩]
        · simp only [show k-1+1 = k by omega, if_true]; ring
        · intro b _ hb
          rw [if_neg, Nat.mul_zero]
          intro h
          exact hb (Fin.ext (by simp; omega))
        · simp
  have hsplit : ∑ r, TransportCounts.rowOff (boardMatrix hk B) r *
      (E₀+(if (groupCol (transportIndex k hk r)).val+1 = k then X else 0)+
        (if (groupRow (transportIndex k hk r)).val+1 = k then Y else 0)) =
      ∑ r, TransportCounts.rowOff (boardMatrix hk B) r *
        (E₀+if (groupCol (transportIndex k hk r)).val+1 = k then X else 0) +
      ∑ r, TransportCounts.rowOff (boardMatrix hk B) r *
        (if P (transportIndex k hk r) then Y else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hsplit]
  omega

/-- The count run from a prepared board has at most `n²` transfers. -/
theorem clear_board_count_run_quadratic {n k : ℕ} [NeZero n]
    (hk : Dims n k) (B : Board n) (hB : Clear (k := k) B)
    (hrep : ∀ j : GroupIndex k, j ≠ lastGroup k hk →
      0 < reservoirCount B (lastGroup k hk) j) :
    ∃ b D j t, reservoir (transportIndex k hk b) (blank B) ∧
      TransportCounts.Run (boardMatrix hk B) b D j t ∧
      t ≤ n^2 ∧ j = Fin.last (k*k-1) ∧ TransportCounts.offdiagMass D = 0 := by
  obtain ⟨b,D,j,t,hb,hrun,ht,hj,hD⟩ := clear_board_has_sorted_count_run hk B hB hrep
  exact ⟨b,D,j,t,hb,hrun,ht.trans (boardMatrix_mass_le hk B),hj,hD⟩

/-- Exchanging the blank with any selected source tile gives the matrix update. -/
theorem boardMatrix_swap_endpoint {n k : ℕ} [NeZero n]
    (hk : Dims n k) (B : Board n) (i j : Fin (k*k-1+1)) (hji : j ≠ i)
    (hi : reservoir (transportIndex k hk i) (blank B)) (b : Cell n)
    (hb : reservoir (transportIndex k hk j) b)
    (ht : B b ∈ targetGroup (transportIndex k hk i)) :
    boardMatrix hk (swapCells B (blank B) b) =
      TransportCounts.move (boardMatrix hk B) i j := by
  funext r c
  have hji : transportIndex k hk j ≠ transportIndex k hk i :=
    fun h => hji ((transportIndex k hk).injective h)
  have h := reservoirCount_transport_swap hk B hi hb hji rfl ht
    (transportIndex k hk r) (transportIndex k hk c)
  simpa only [boardMatrix,TransportCounts.move,Equiv.apply_eq_iff_eq] using h

/-- The endpoint transposition realizing one incoming transfer has exactly the
matrix update and preserves Clear. Legality and path cost remain separate. -/
theorem boardMatrix_choice_endpoint {n k : ℕ} [NeZero n]
    (hk : Dims n k) (B : Board n) (hB : Clear (k := k) B)
    (i j : Fin (k*k-1+1))
    (hi : reservoir (transportIndex k hk i) (blank B))
    (hchoice : TransportCounts.Chooses (boardMatrix hk B) i j) :
    ∃ b : Cell n, reservoir (transportIndex k hk j) b ∧
      B b ∈ targetGroup (transportIndex k hk i) ∧
      Clear (k := k) (swapCells B (blank B) b) ∧
      boardMatrix hk (swapCells B (blank B) b) =
        TransportCounts.move (boardMatrix hk B) i j := by
  obtain ⟨b,hb,ht⟩ := (reservoirCount_pos_iff B _ _).mp hchoice.2.1
  refine ⟨b,hb,ht,clear_swap_reservoirs hk B hB hi hb,?_⟩
  funext r c
  have hji : transportIndex k hk j ≠ transportIndex k hk i :=
    fun h => hchoice.1 ((transportIndex k hk).injective h)
  have h := reservoirCount_transport_swap hk B hi hb hji rfl ht
    (transportIndex k hk r) (transportIndex k hk c)
  simpa only [boardMatrix,TransportCounts.move,Equiv.apply_eq_iff_eq] using h

end
end SlidingPuzzle.Partition
