import SlidingPuzzle.Algorithm.Transport.ReservoirSlide
import SlidingPuzzle.Algorithm.Transport.Exit
import SlidingPuzzle.Moves.RestoreCarry

/-! The exit from a vertical corridor into the source reservoir. Instead of one
long restoring jump to the selected tile (cost `25` per cell), the blank enters
the reservoir by a short jump next to the corridor, carries the tile to the
reservoir's corridor side with the three-row shift carry, jumps it into the
corridor, and walks back to the tile's old cell (`exists_restore_carry`: length
`7` and at most `4` inefficient moves per cell). The walk back undoes the carry,
so the whole exit exchanges the blank with the tile and nothing else in the
reservoir moves: the tiles left behind keep their columns. -/
namespace SlidingPuzzle.Partition
noncomputable section
open Classical

variable {n k : ℕ}

/-- Three consecutive rows of a reservoir band, the last being `O`. -/
theorem exists_carry_rows (hk : Dims n k) (j : GroupIndex k) (O : Fin n)
    (hO : (groupRow j).val*side n k+2*k ≤ O.val ∧ O.val < (groupRow j).val*side n k+side n k) :
    ∃ row : ℕ → Fin n, StripCol row 2 ∧ row 2 = O ∧ ∀ r ≤ 2,
      (groupRow j).val*side n k+2*k ≤ (row r).val ∧
        (row r).val < (groupRow j).val*side n k+side n k := by
  have hkk : k^2+k+2 ≤ side n k := hk.sq_add_le
  have hk2 : k ≤ k^2 := by have := hk.two_le; nlinarith
  have hblock := hk.block_le (groupRow j)
  simp only [Nat.add_mul, Nat.one_mul] at hblock
  have hOn := O.isLt
  have h4 : 4 ≤ k^2 := hk.facts.2.1
  have h2k : 2*k ≤ k^2 := by nlinarith [hk.two_le]
  by_cases h : O.val+2 < (groupRow j).val*side n k+side n k
  · refine ⟨fun r => ⟨min (O.val+2-r) (n-1), by omega⟩, ?_, ?_, ?_⟩
    · intro a b ha hb; dsimp only; simp only [Nat.dist]; omega
    · ext; dsimp only; omega
    · intro r hr; dsimp only; omega
  · refine ⟨fun r => ⟨min (O.val-2+r) (n-1), by omega⟩, ?_, ?_, ?_⟩
    · intro a b ha hb; dsimp only; simp only [Nat.dist]; omega
    · ext; dsimp only; omega
    · intro r hr; dsimp only; omega

open Strip in
/-- The restoring carry exit, for a column parametrization `col` running from
the entry column `col 0` next to the corridor to the tile's column `col (m+1)`,
with `m` odd. The blank steps to an adjacent row of the corridor when the
parity requires it, and runs `exists_restore_carry`. The net effect is a chain
of group-`i` exchanges ending with the blank on the tile's cell. -/
theorem exists_transport_restore_exit [NeZero n] (hk : Dims n k)
    (A S : Board n) (hA : Clear (k := k) A) (i j jc : GroupIndex k)
    (hrowj : groupRow jc = groupRow j)
    (hAS : GroupEquivalent i A S) (b : Cell n) (hb : reservoir j b)
    (ht : A b ∈ targetGroup i) (hblank : vertical jc i (blank S))
    (hrow : (blank S).1 = b.1) (col : ℕ → Fin n) (m : ℕ) (hm : m % 2 = 1)
    (hcol : StripCol col (m+1))
    (hres : ∀ c ≤ m+1, ∀ x : Cell n, (groupRow j).val*side n k+2*k ≤ x.1.val →
      x.1.val < (groupRow j).val*side n k+side n k → x.2 = col c → reservoir j x)
    (hbcol : b.2 = col (m+1)) (hnear : Nat.dist (blank S).2.val (col 0).val ≤ k^2+2) :
    ∃ D : Board n, ∃ p : Path S D, GroupEquivalent i A D ∧ blank D = b ∧
      p.inefficientMoves ≤ 4*m+75*k^2+300 := by
  have hn2 : 2 ≤ n := by have := hk.two_le_n; omega
  have hbv := hb
  obtain ⟨hb1, hb2, -, -⟩ := hbv
  simp only [Nat.add_mul, Nat.one_mul] at hb2
  obtain ⟨row, hrowS, hrow2, hrowin⟩ := exists_carry_rows hk j b.1 ⟨hb1, hb2⟩
  obtain ⟨v, hv⟩ : ∃ v, blank S = v := ⟨_, rfl⟩
  rw [hv] at hblank hrow hnear
  have hband : ∀ r ≤ 2, (groupRow jc).val*side n k+2*k ≤ (row r).val ∧
      (row r).val < ((groupRow jc).val+1)*side n k := by
    intro r hr; rw [hrowj, Nat.add_mul, Nat.one_mul]; exact hrowin r hr
  let u : Cell n := (row 1, v.2)
  have hvu : vertical jc i u := ⟨(hband 1 (by omega)).1, (hband 1 (by omega)).2, hblank.2.2⟩
  have h21 : Nat.dist v.1.val (row 1).val = 1 := by
    have := hrowS 2 1 (by omega) (by omega)
    rw [hrow, ← hrow2, this]; rfl
  have hduv : gridDistance v u = 1 := by
    simp only [gridDistance, u, Nat.dist_self, add_zero]; exact h21
  have hstrip : ∀ q, region 2 (m+1) q → reservoir j (emb row col q) := fun q hq =>
    hres q.2 hq.2 _ (hrowin q.1 hq.1).1 (hrowin q.1 hq.1).2 rfl
  have hnotv : ∀ q, region 2 (m+1) q → emb row col q ≠ v := fun q hq h =>
    vertical_not_reservoir hk hblank (h ▸ hstrip q hq)
  have hnotu : ∀ q, region 2 (m+1) q → emb row col q ≠ u := fun q hq h =>
    vertical_not_reservoir hk hvu (h ▸ hstrip q hq)
  have hbeq : (row 2, col (m+1)) = b := Prod.ext hrow2 hbcol.symm
  have hcol01 := hcol 0 1 (by omega) (by omega)
  have hcol0m := hcol 0 (m+1) (by omega) (by omega)
  simp only [Nat.dist] at hcol01 hcol0m h21 hnear
  have hrow1 : (row 1).val = v.1.val+1 ∨ (row 1).val+1 = v.1.val := by omega
  have hvb : Nat.dist v.2.val b.2.val ≤ k^2+m+3 := by
    rw [hbcol]; simp only [Nat.dist]; omega
  have hSu : S u ∈ targetGroup i := hAS.mem_targetGroup (hA.2 jc i u hvu)
    (fun h => by rw [hv] at h; rw [h, gridDistance_self] at hduv; omega)
  have hbv : b ≠ v := fun h => vertical_not_reservoir hk hblank (h ▸ hb)
  have hbu : b ≠ u := fun h => vertical_not_reservoir hk hvu (h ▸ hb)
  have hSb : S b ∈ targetGroup i := hAS.mem_targetGroup ht (by rw [hv]; exact hbv)
  by_cases hpar : (v.2.val+(col 0).val) % 2 = 1
  · -- Step to `u` first; the carry runs from `u` and the tile lands on `v`.
    let S' := swapCells S (blank S) u
    have hbS' : blank S' = u := blank_swapCells S u
    have hAS' : GroupEquivalent i A S' := hAS.trans (groupEquivalent_swap hk S i u hSu)
    have hS'v : S' v = S u := by
      change swapCells S (blank S) u v = _; rw [hv, swapCells_at_left]
    obtain ⟨p, hp⟩ := exists_restore_carry hn2 row col m hrowS hcol hm S' u v hnotu hnotv
      (by rw [gridDistance_comm]; exact hduv) hbS' (by simp [u, Nat.dist])
      (by simp only [u]; omega) (by simp only [Nat.dist]; omega) (by omega) b hbeq
    let S'' := swapCells S' u v
    have hS''b : S'' b = S b := by
      change swapCells S' u v b = _
      rw [swapCells_preserves S' hbu hbv]
      change swapCells S (blank S) u b = _
      rw [swapCells_preserves S (by rw [hv]; exact hbv) hbu]
    have hA'' : GroupEquivalent i A S'' := by
      refine hAS'.trans ?_
      have := groupEquivalent_swap hk S' i v (by rw [hS'v]; exact hSu)
      rwa [hbS'] at this
    have hbS'' : blank S'' = v := by
      change blank (swapCells S' u v) = v; rw [← hbS', blank_swapCells]
    refine ⟨_, (movePath S u (by rw [hv]; exact hduv)).append p, ?_, ?_, ?_⟩
    · refine hA''.trans ?_
      have := groupEquivalent_swap hk S'' i b (by rw [hS''b]; exact hSb)
      rwa [hbS''] at this
    · have := blank_swapCells S'' b; rwa [hbS''] at this
    · have hM1 := manhattan_swapCells_blank_le S u
      have hM2 := manhattan_swapCells_blank_le S' v
      have hM3 := manhattan_swapCells_blank_le S'' b
      rw [hbS'] at hM2
      rw [hbS''] at hM3
      have hbal := ((movePath S u (by rw [hv]; exact hduv)).append p).length_add_manhattan
      rw [Path.length_append, movePath_length] at hbal
      have hdu : gridDistance u v = 1 := by rw [gridDistance_comm]; exact hduv
      have hdvb : gridDistance v b ≤ k^2+m+3 := by
        simp only [gridDistance, hrow, Nat.dist_self, zero_add]; exact hvb
      have hg : gridDistance (blank S) u = 1 := by rw [hv]; exact hduv
      rw [hg] at hM1
      change manhattan S' ≤ _ at hM1
      change manhattan (swapCells S' u v) ≤ manhattan S' + _ at hM2
      change manhattan (swapCells (swapCells S' u v) v b) ≤ manhattan (swapCells S' u v) + _ at hM3
      simp only [u, Nat.dist] at hp hdvb
      rw [hdu] at hM2
      omega
  · -- Enter from `v`; the tile lands on `u`.
    obtain ⟨p, hp⟩ := exists_restore_carry hn2 row col m hrowS hcol hm S v u hnotv hnotu
      hduv hv (by simp only [Nat.dist]; omega) (by omega) (by simp [u, Nat.dist])
      (by simp only [u]; omega) b hbeq
    let S'' := swapCells S v u
    have hS''b : S'' b = S b := swapCells_preserves S hbv hbu
    have hA'' : GroupEquivalent i A S'' := by
      refine hAS.trans ?_
      have := groupEquivalent_swap hk S i u hSu
      rwa [hv] at this
    have hbS'' : blank S'' = u := by
      change blank (swapCells S v u) = u; rw [← hv, blank_swapCells]
    refine ⟨_, p, ?_, ?_, ?_⟩
    · refine hA''.trans ?_
      have := groupEquivalent_swap hk S'' i b (by rw [hS''b]; exact hSb)
      rwa [hbS''] at this
    · have := blank_swapCells S'' b; rwa [hbS''] at this
    · have hM2 := manhattan_swapCells_blank_le S u
      have hM3 := manhattan_swapCells_blank_le S'' b
      rw [hv] at hM2
      rw [hbS''] at hM3
      have hbal := p.length_add_manhattan
      have hdub : gridDistance u b ≤ k^2+m+4 := by
        have := hvb
        simp only [gridDistance, u, ← hrow, Nat.dist] at this ⊢; omega
      change manhattan (swapCells S v u) ≤ _ at hM2
      change manhattan (swapCells (swapCells S v u) u b) ≤ manhattan (swapCells S v u) + _ at hM3
      rw [hduv] at hM2
      simp only [u, Nat.dist] at hp
      omega

/-- Exit to the left through a tile carry. The selected source tile lies at
least two columns into its reservoir. -/
theorem exists_transport_carry_exit [NeZero n] (hk : Dims n k)
    (A S : Board n) (hA : Clear (k := k) A) (i j : GroupIndex k)
    (hAS : GroupEquivalent i A S) (b : Cell n) (hb : reservoir j b)
    (ht : A b ∈ targetGroup i) (hblank : vertical j i (blank S))
    (hrow : (blank S).1 = b.1)
    (hx : (groupCol j).val*side n k+k^2+2 ≤ b.2.val) :
    ∃ D : Board n, ∃ p : Path S D, GroupEquivalent i A D ∧ blank D = b ∧
      p.inefficientMoves ≤ 4*(b.2.val-(groupCol j).val*side n k)+75*k^2+300 := by
  have hiLt : i.val < k^2 := by simp [pow_two]
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  simp only [Nat.add_mul, Nat.one_mul] at hb2 hb4
  have hv3 := hblank.2.2
  let L := (groupCol j).val*side n k+k^2
  let δ := if (b.2.val-1-L) % 2 = 1 then 0 else 1
  let w := L+δ
  have hw : w+1 ≤ b.2.val := by dsimp [w, L, δ]; split_ifs <;> omega
  have hm : (b.2.val-1-w) % 2 = 1 := by dsimp [w, L, δ]; split_ifs <;> omega
  have hbn := b.2.isLt
  let col : ℕ → Fin n := fun c => ⟨min (w+c) (n-1), by omega⟩
  have hcolv : ∀ c, c ≤ b.2.val-1-w+1 → (col c).val = w+c := by
    intro c hc; simp only [col]; omega
  have hcol : StripCol col (b.2.val-1-w+1) := by
    intro a a' ha ha'
    rw [hcolv a ha, hcolv a' ha']
    simp only [Nat.dist]; omega
  have hb' : reservoir j b := ⟨hb1, by simp only [Nat.add_mul, Nat.one_mul]; exact hb2, hb3,
    by simp only [Nat.add_mul, Nat.one_mul]; exact hb4⟩
  obtain ⟨D, p, hD, hbD, hi⟩ := exists_transport_restore_exit hk A S hA i j j rfl hAS b
    hb' ht hblank hrow col (b.2.val-1-w) hm hcol
    (by
      intro c hc x hx1 hx2 hxc
      have := hcolv c hc
      refine ⟨hx1, by simp only [Nat.add_mul, Nat.one_mul]; exact hx2, ?_, ?_⟩ <;>
        rw [hxc] <;> dsimp [w, L] at this ⊢ <;> [omega; (simp only [Nat.add_mul, Nat.one_mul]; omega)])
    (Fin.ext (by rw [hcolv _ le_rfl]; omega))
    (by rw [hcolv 0 (by omega)]; simp only [Nat.dist]; dsimp [w, L, δ]; split_ifs <;> omega)
  exact ⟨D, p, hD, hbD, by omega⟩

/-- Exit to the right: the blank descends the vertical corridor `V(j',i)` of the
square `j'` right of the source square `j`, and the tile is carried rightwards. -/
theorem exists_transport_carry_exit_right [NeZero n] (hk : Dims n k)
    (A S : Board n) (hA : Clear (k := k) A) (i j j' : GroupIndex k)
    (hrowj : groupRow j' = groupRow j) (hcolj : (groupCol j').val = (groupCol j).val+1)
    (hAS : GroupEquivalent i A S) (b : Cell n) (hb : reservoir j b)
    (ht : A b ∈ targetGroup i) (hblank : vertical j' i (blank S))
    (hrow : (blank S).1 = b.1)
    (hx : b.2.val+3 ≤ ((groupCol j).val+1)*side n k) :
    ∃ D : Board n, ∃ p : Path S D, GroupEquivalent i A D ∧ blank D = b ∧
      p.inefficientMoves ≤ 4*(((groupCol j).val+1)*side n k-b.2.val)+75*k^2+300 := by
  have hiLt : i.val < k^2 := by simp [pow_two]
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  simp only [Nat.add_mul, Nat.one_mul] at hb2 hb4 hx
  have hv3 := hblank.2.2
  rw [hcolj] at hv3
  simp only [Nat.add_mul, Nat.one_mul] at hv3
  let E := (groupCol j).val*side n k+side n k-1
  let δ := if (E-1-b.2.val) % 2 = 1 then 0 else 1
  let w := E-δ
  have hw : b.2.val+1 ≤ w := by dsimp [w, E, δ]; split_ifs <;> omega
  have hm : (w-1-b.2.val) % 2 = 1 := by dsimp [w, E, δ]; split_ifs <;> omega
  have hwn : w < n := by have := (blank S).2.isLt; dsimp [w, E]; omega
  let col : ℕ → Fin n := fun c => ⟨w-c, by omega⟩
  have hcolv : ∀ c, (col c).val = w-c := fun c => rfl
  have hcol : StripCol col (w-1-b.2.val+1) := by
    intro a a' ha ha'
    rw [hcolv, hcolv]
    simp only [Nat.dist]; omega
  have hb' : reservoir j b := ⟨hb1, by simp only [Nat.add_mul, Nat.one_mul]; exact hb2, hb3,
    by simp only [Nat.add_mul, Nat.one_mul]; exact hb4⟩
  obtain ⟨D, p, hD, hbD, hi⟩ := exists_transport_restore_exit hk A S hA i j j' hrowj hAS b
    hb' ht hblank hrow col (w-1-b.2.val) hm hcol
    (by
      intro c hc x hx1 hx2 hxc
      refine ⟨hx1, by simp only [Nat.add_mul, Nat.one_mul]; exact hx2, ?_, ?_⟩ <;>
        rw [hxc, hcolv] <;> dsimp [w, E] <;> (try simp only [Nat.add_mul, Nat.one_mul]) <;>
        omega)
    (Fin.ext (by rw [hcolv]; omega))
    (by rw [hcolv]; simp only [Nat.dist]; dsimp [w, E, δ]; split_ifs <;> omega)
  simp only [Nat.add_mul, Nat.one_mul]
  exact ⟨D, p, hD, hbD, by dsimp [w, E] at hi; omega⟩

/-- The exit through the source square's own vertical corridor: carry the tile
when it lies deep in its reservoir, and jump directly when it is already next
to the corridors. The cost grows with the tile's distance from the left edge. -/
theorem exists_transport_exit_left [NeZero n] (hk : Dims n k)
    (A S : Board n) (hA : Clear (k := k) A) (i j : GroupIndex k)
    (hAS : GroupEquivalent i A S) (b : Cell n) (hb : reservoir j b)
    (ht : A b ∈ targetGroup i) (hblank : vertical j i (blank S))
    (hrow : (blank S).1 = b.1) :
    ∃ D : Board n, ∃ p : Path S D, GroupEquivalent i A D ∧ blank D = b ∧
      p.inefficientMoves ≤ 4*(b.2.val-(groupCol j).val*side n k)+75*k^2+300 := by
  by_cases hx : (groupCol j).val*side n k+k^2+2 ≤ b.2.val
  · exact exists_transport_carry_exit hk A S hA i j hAS b hb ht hblank hrow hx
  · obtain ⟨D, p, hD, hAD, hp⟩ :=
      exists_transport_exit_path hk A S hA i j hAS b hb ht rfl hblank hrow
    refine ⟨D, p, hAD, hD, ?_⟩
    have hiLt : i.val < k^2 := by simp [pow_two]
    have hcol := hblank.2.2
    have hb3 := hb.2.2.1
    have hdist : Nat.dist (blank S).2.val b.2.val ≤ k^2+1 := by
      simp only [Nat.dist]; omega
    omega

/-- The exit through the vertical corridor of the square `j'` right of the
source square `j`. The cost grows with the tile's distance from the right edge. -/
theorem exists_transport_exit_right [NeZero n] (hk : Dims n k)
    (A S : Board n) (hA : Clear (k := k) A) (i j j' : GroupIndex k)
    (hrowj : groupRow j' = groupRow j) (hcolj : (groupCol j').val = (groupCol j).val+1)
    (hAS : GroupEquivalent i A S) (b : Cell n) (hb : reservoir j b)
    (ht : A b ∈ targetGroup i) (hblank : vertical j' i (blank S))
    (hrow : (blank S).1 = b.1) :
    ∃ D : Board n, ∃ p : Path S D, GroupEquivalent i A D ∧ blank D = b ∧
      p.inefficientMoves ≤ 4*(((groupCol j).val+1)*side n k-b.2.val)+75*k^2+300 := by
  by_cases hx : b.2.val+3 ≤ ((groupCol j).val+1)*side n k
  · exact exists_transport_carry_exit_right hk A S hA i j j' hrowj hcolj hAS b hb ht hblank hrow hx
  · obtain ⟨D, p, hD, hAD, hp⟩ :=
      exists_transport_exit_path hk A S hA i j hAS b hb ht hrowj hblank hrow
    refine ⟨D, p, hAD, hD, ?_⟩
    have hiLt : i.val < k^2 := by simp [pow_two]
    have hcol := hblank.2.2
    rw [hcolj] at hcol
    have hb4 := hb.2.2.2
    simp only [Nat.add_mul, Nat.one_mul] at hcol hb4 hx
    have hdist : Nat.dist (blank S).2.val b.2.val ≤ k^2+2 := by
      simp only [Nat.dist]; omega
    omega

end
end SlidingPuzzle.Partition
