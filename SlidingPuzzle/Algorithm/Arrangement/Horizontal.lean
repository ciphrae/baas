import SlidingPuzzle.Algorithm.Cardinalities
import SlidingPuzzle.Moves.BulkExchangeSchedule

/-! Arrangement's second schedule: sort the horizontal corridor rows into their
squares.

A *slot* is one corridor row inside one column block: `(low, x, o, d)` is row
`x*s + o` (upper rows, `low = false`) or `x*s + k + o` (lower rows) of band `x`,
in column block `d`. It lies in square `(x, d)`. Initially an upper slot holds
group `(x, o)` and a lower slot group `(x-1, o)`, since the lower row of `H_i`
lies in the band below `i`'s. Two rounds of pairwise exchanges sort them:
the first transposes `o` and `d` and reflects the band of lower slots,
`x ↦ -x`; the second reflects the band of lower slots again, `x ↦ k-1-x`.
Together the lower slots move up one band. -/
namespace SlidingPuzzle.Partition
variable {k : ℕ}

abbrev Slot (k : ℕ) := Bool × Fin k × Fin k × Fin k

/-- The board row of a slot. -/
def slotRow (s k : ℕ) (j : Slot k) : ℕ :=
  j.2.1.val*s + (if j.1 then k else 0) + j.2.2.1.val

/-- The cells of a slot. -/
def slotCells {n : ℕ} (j : Slot k) : Finset (Cell n) := by
  classical
  exact Finset.univ.filter fun c => c.1.val = slotRow (side n k) k j ∧
    j.2.2.2.val*side n k ≤ c.2.val ∧ c.2.val < (j.2.2.2.val+1)*side n k

@[simp] theorem mem_slotCells {n : ℕ} (j : Slot k) (c : Cell n) :
    c ∈ slotCells j ↔ c.1.val = slotRow (side n k) k j ∧
      j.2.2.2.val*side n k ≤ c.2.val ∧ c.2.val < (j.2.2.2.val+1)*side n k := by
  classical
  simp [slotCells]

/-- The square containing a slot. -/
def slotGroup (j : Slot k) : GroupIndex k := finProdFinEquiv (j.2.1, j.2.2.2)

/-- The band above, cyclically. -/
def prevBand (x : Fin k) : Fin k := ⟨(x.val+k-1) % k, Nat.mod_lt _ x.pos⟩

/-- The reflection `x ↦ -x` of the bands. -/
def bandRefl (x : Fin k) : Fin k := ⟨(k-x.val) % k, Nat.mod_lt _ x.pos⟩

/-- The group whose corridor row contains a slot. -/
def initGroup (j : Slot k) : GroupIndex k :=
  finProdFinEquiv (if j.1 then prevBand j.2.1 else j.2.1, j.2.2.1)

/-- The first round. -/
def slotSwapA (j : Slot k) : Slot k :=
  (j.1, if j.1 then bandRefl j.2.1 else j.2.1, j.2.2.2, j.2.2.1)

/-- The second round. -/
def slotSwapB (j : Slot k) : Slot k :=
  if j.1 then (true, Fin.rev j.2.1, j.2.2.1, j.2.2.2) else j

theorem bandRefl_bandRefl (x : Fin k) : bandRefl (bandRefl x) = x := by
  have hx := x.isLt
  apply Fin.ext
  simp only [bandRefl]
  rcases Nat.eq_zero_or_pos x.val with h | h
  · rw [h, Nat.sub_zero, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
  · rw [Nat.mod_eq_of_lt (by omega : k-x.val < k), show k-(k-x.val) = x.val by omega,
      Nat.mod_eq_of_lt hx]

theorem slotSwapA_involutive : Function.Involutive (slotSwapA (k := k)) := by
  rintro ⟨l, x, o, d⟩
  cases l <;> simp [slotSwapA, bandRefl_bandRefl]

theorem slotSwapB_involutive : Function.Involutive (slotSwapB (k := k)) := by
  rintro ⟨l, x, o, d⟩
  cases l <;> simp [slotSwapB]

theorem prevBand_bandRefl (x : Fin k) : prevBand (bandRefl x) = Fin.rev x := by
  have hx := x.isLt
  apply Fin.ext
  simp only [prevBand, bandRefl, Fin.val_rev]
  rcases Nat.eq_zero_or_pos x.val with h | h
  · rw [h, Nat.sub_zero, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega : k-x.val < k),
      show k-x.val+k-1 = (k-x.val-1)+k by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    omega

/-- Two rounds bring every slot's group into the slot's square. -/
theorem initGroup_slotSwapA (j : Slot k) : initGroup (slotSwapA j) = slotGroup (slotSwapB j) := by
  obtain ⟨l, x, o, d⟩ := j
  cases l <;> simp [initGroup, slotSwapA, slotSwapB, slotGroup, prevBand_bandRefl]

theorem nextBand_prevBand (x : Fin k) : nextBand k (prevBand x).val = x.val := by
  have hx := x.isLt
  simp only [nextBand, prevBand]
  rw [Nat.mod_add_mod, show x.val+k-1+1 = x.val+k by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt hx]

theorem slotRow_lt {n : ℕ} (hk : Dims n k) (j : Slot k) :
    slotRow (side n k) k j < n := by
  have h2k : 2*k+2 ≤ side n k := by have := hk.sq_add_le; nlinarith
  have hb := hk.block_le j.2.1
  have ho := j.2.2.1.isLt
  simp only [Nat.add_mul, Nat.one_mul] at hb
  unfold slotRow
  split_ifs <;> omega

theorem card_slotCells {n : ℕ} (hk : Dims n k) (j : Slot k) :
    (slotCells (n := n) j).card = side n k := by
  classical
  have he : slotCells (n := n) j = Finset.univ.filter fun c : Cell n =>
      slotRow (side n k) k j ≤ c.1.val ∧ c.1.val < slotRow (side n k) k j+1 ∧
      j.2.2.2.val*side n k ≤ c.2.val ∧ c.2.val < (j.2.2.2.val+1)*side n k := by
    ext c
    simp only [mem_slotCells, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [he, card_rectangle _ _ _ _ (slotRow_lt hk j) (hk.block_le j.2.2.2)]
  simp [Nat.add_mul]

/-- The row of a slot, split into band and offset. -/
private theorem slotRow_divmod {n : ℕ} (hk : Dims n k) (j : Slot k) :
    slotRow (side n k) k j / side n k = j.2.1.val ∧
      slotRow (side n k) k j % side n k = (if j.1 then k else 0) + j.2.2.1.val := by
  have h2k : 2*k+2 ≤ side n k := by have := hk.sq_add_le; nlinarith
  have ho := j.2.2.1.isLt
  have hoff : (if j.1 then k else 0) + j.2.2.1.val < side n k := by split_ifs <;> omega
  unfold slotRow
  rw [Nat.add_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hoff,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff]
  simp

theorem slotCells_disjoint {n : ℕ} (hk : Dims n k) (j j' : Slot k) (hjj : j ≠ j') :
    Disjoint (slotCells (n := n) j) (slotCells j') := by
  apply Finset.disjoint_left.mpr
  intro c h h'
  obtain ⟨hr, hlo, hhi⟩ := (mem_slotCells _ _).mp h
  obtain ⟨hr', hlo', hhi'⟩ := (mem_slotCells _ _).mp h'
  obtain ⟨l, x, o, d⟩ := j
  obtain ⟨l', x', o', d'⟩ := j'
  have ⟨h1, h2⟩ := slotRow_divmod hk (l, x, o, d)
  have ⟨h1', h2'⟩ := slotRow_divmod hk (l', x', o', d')
  rw [← hr] at h1 h2
  rw [← hr'] at h1' h2'
  have hd : d = d' := Fin.ext ((Nat.div_eq_of_lt_le hlo hhi).symm.trans
    (Nat.div_eq_of_lt_le hlo' hhi'))
  have hx : x = x' := Fin.ext (h1.symm.trans h1')
  have ho := o.isLt
  have ho' := o'.isLt
  simp only at h2 h2'
  apply hjj
  cases l <;> cases l' <;> simp only [Bool.false_eq_true, ↓reduceIte] at h2 h2'
  · rw [hx, hd, show o = o' from Fin.ext (by omega)]
  · omega
  · omega
  · rw [hx, hd, show o = o' from Fin.ext (by omega)]

theorem slotCells_subset_square {n : ℕ} (hk : Dims n k) (j : Slot k) {c : Cell n}
    (hc : c ∈ slotCells j) : square (slotGroup j) c := by
  obtain ⟨hr, hlo, hhi⟩ := (mem_slotCells _ _).mp hc
  have h2k : 2*k+2 ≤ side n k := by have := hk.sq_add_le; nlinarith
  have ho := j.2.2.1.isLt
  simp only [square, slotGroup, groupRow, groupCol, Equiv.symm_apply_apply]
  refine ⟨?_, ?_, hlo, hhi⟩
  · rw [hr]; unfold slotRow; omega
  · rw [hr]; unfold slotRow; rw [Nat.add_mul, Nat.one_mul]; split_ifs <;> omega

theorem slotCells_horizontal {n : ℕ} (j : Slot k) {c : Cell n}
    (hc : c ∈ slotCells j) : horizontal (initGroup j) c := by
  obtain ⟨hr, -, -⟩ := (mem_slotCells _ _).mp hc
  obtain ⟨l, x, o, d⟩ := j
  unfold horizontal corridorRow
  simp only [initGroup, groupRow, groupCol, Equiv.symm_apply_apply]
  cases l
  · left; simpa [slotRow] using hr
  · right; simp only [↓reduceIte]; rw [nextBand_prevBand]; simpa [slotRow] using hr

/-- Every corridor cell lies in a slot. -/
theorem exists_slot_of_horizontal {n : ℕ} (hk : Dims n k) {i : GroupIndex k} {c : Cell n}
    (h : horizontal i c) : ∃ j : Slot k, c ∈ slotCells j := by
  have hm := horizontal_mod hk h
  have hs := hk.side_pos
  have hxd := Nat.div_add_mod' c.1.val (side n k)
  have hyd := Nat.div_add_mod' c.2.val (side n k)
  have hy := Nat.mod_lt c.2.val hs
  have hxk : c.1.val / side n k < k :=
    (Nat.div_lt_iff_lt_mul hs).mpr (by
      have := c.1.isLt; have := hk.mul_side; linarith [Nat.mul_comm k (side n k)])
  have hyk : c.2.val / side n k < k :=
    (Nat.div_lt_iff_lt_mul hs).mpr (by
      have := c.2.isLt; have := hk.mul_side; linarith [Nat.mul_comm k (side n k)])
  let l : Bool := decide (k ≤ c.1.val % side n k)
  refine ⟨(l, ⟨_, hxk⟩, ⟨c.1.val % side n k - (if l then k else 0), ?_⟩, ⟨_, hyk⟩), ?_⟩
  · by_cases hl : k ≤ c.1.val % side n k <;> simp [l, hl] <;> omega
  · simp only [mem_slotCells, slotRow]
    refine ⟨?_, ?_, ?_⟩
    · by_cases hl : k ≤ c.1.val % side n k <;> simp [l, hl] <;> omega
    · omega
    · rw [Nat.add_mul, Nat.one_mul]; omega

/-- Sort all horizontal corridor rows into their squares, restoring every
vertical corridor and reservoir. -/
theorem exists_horizontal_arrangement_path {n : ℕ} [NeZero n] (hk : Dims n k) (B : Board n)
    (hH : ∀ (i : GroupIndex k) x, horizontal i x → B x ∈ targetGroup i) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ (24*side n k+2032)*(4*k^3)*n ∧ blank C = blank B ∧
      (∀ (j : Slot k) x, x ∈ slotCells j → C x ∈ targetGroup (slotGroup j)) ∧
      (∀ (i j : GroupIndex k) x, vertical i j x → C x = B x) ∧
      (∀ (i : GroupIndex k) x, reservoir i x → C x = B x) := by
  classical
  have hn : 4 ≤ n := hk.two_le_n
  let S : Slot k → Finset (Cell n) := fun j => slotCells j
  have hsize : ∀ j, 2 ≤ (S j).card ∧ (S j).card ≤ side n k := by
    intro j
    dsimp [S]
    rw [card_slotCells hk]
    exact ⟨by have := hk.k_add_two_le; omega, le_rfl⟩
  have hsmall : 2*side n k ≤ n := by
    have hh := Nat.mul_le_mul_right (side n k) hk.two_le; have := hk.mul_side; omega
  have hactive : ∀ τ : Slot k → Slot k,
      ((Finset.univ : Finset (Slot k)).filter (fun j => τ j ≠ j)).card ≤ 2*k^3 := by
    intro τ
    calc
      _ ≤ (Finset.univ : Finset (Slot k)).card := Finset.card_filter_le _ _
      _ = 2*k^3 := by simp [Slot]; ring
  have hcard : ∀ τ : Slot k → Slot k, ∀ j, (S j).card = (S (τ j)).card := by
    intro τ j
    dsimp [S]
    rw [card_slotCells hk, card_slotCells hk]
  have hzero : ∀ j x, x ∈ S j → B x ≠ 0 := by
    intro j x hx hz
    have hh := hH _ x (slotCells_horizontal j hx)
    exact zero_not_mem_targetGroup _ (hz ▸ hh)
  obtain ⟨D, p, hp, hbD, hD, hfixD⟩ := exists_bulk_involution_region_path_active B hn S slotSwapA
    slotSwapA_involutive (slotCells_disjoint hk) (side n k) hsmall hsize (hcard _) hzero
    (fun j t => t ∈ targetGroup (initGroup (slotSwapA j))) Finset.univ (by simp)
    (by
      intro j _ x hx
      rw [slotSwapA_involutive j]
      exact hH _ x (slotCells_horizontal j hx))
  have hzeroD : ∀ j x, x ∈ S j → D x ≠ 0 := by
    intro j x hx hz
    have hh := hD j (Finset.mem_univ _) x hx
    exact zero_not_mem_targetGroup _ (hz ▸ hh)
  obtain ⟨C, q, hq, hbC, hC, hfixC⟩ := exists_bulk_involution_region_path_active D hn S slotSwapB
    slotSwapB_involutive (slotCells_disjoint hk) (side n k) hsmall hsize (hcard _) hzeroD
    (fun j t => t ∈ targetGroup (slotGroup j)) Finset.univ (by simp)
    (by
      intro j _ x hx
      have hh := hD j (Finset.mem_univ _) x hx
      rwa [initGroup_slotSwapA] at hh)
  have hfix : ∀ x : Cell n, (∀ j : Slot k, x ∉ slotCells j) → C x = B x := by
    intro x hx
    rw [hfixC x (fun j _ => hx j), hfixD x (fun j _ => hx j)]
  refine ⟨C, p.append q, ?_, hbC.trans hbD, ?_, ?_, ?_⟩
  · rw [Path.length_append]
    have h1 := Nat.mul_le_mul_right n (Nat.mul_le_mul_left (24*side n k+2032) (hactive slotSwapA))
    have h2 := Nat.mul_le_mul_right n (Nat.mul_le_mul_left (24*side n k+2032) (hactive slotSwapB))
    have he : (24*side n k+2032)*(4*k^3)*n =
        (24*side n k+2032)*(2*k^3)*n+(24*side n k+2032)*(2*k^3)*n := by ring
    omega
  · intro j x hx
    exact hC j (Finset.mem_univ _) x hx
  · intro i j x hx
    apply hfix
    intro a ha
    exact horizontal_not_vertical hk (slotCells_horizontal a ha) hx
  · intro i x hx
    apply hfix
    intro a ha
    exact horizontal_not_reservoir hk (slotCells_horizontal a ha) hx

end SlidingPuzzle.Partition
