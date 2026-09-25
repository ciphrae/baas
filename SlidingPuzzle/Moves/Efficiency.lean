import SlidingPuzzle.Manhattan
import SlidingPuzzle.Moves.Relabel
import SlidingPuzzle.Moves.Embedding

/-! Manhattan distance as a sum over cells, and inefficiency under relabeling
and embedding. Relabeling two tiles changes the potential by a bounded amount;
embedding a local board with target-compatible labels preserves the potential
change of every move, hence the inefficiency of every path. -/
namespace SlidingPuzzle

section
variable {n : ℕ}

/-- The potential contributed by the tile in one cell. -/
def cellCost (B : Board n) (x : Cell n) : ℕ :=
  if (B x).val = 0 then 0 else gridDistance x (position (target n) (B x))

theorem manhattan_eq_sum_cellCost (B : Board n) : manhattan B = ∑ x, cellCost B x := by
  unfold manhattan cellCost
  rw [← Equiv.sum_comp B]
  apply Finset.sum_congr rfl
  intro x _
  simp [position]

/-- Changing a board on a set `U` raises the potential by at most the new
contributions of `U`. -/
theorem manhattan_le_of_agree (B C : Board n) (U : Finset (Cell n))
    (h : ∀ x, x ∉ U → C x = B x) :
    manhattan C ≤ manhattan B + ∑ x ∈ U, cellCost C x := by
  rw [manhattan_eq_sum_cellCost, manhattan_eq_sum_cellCost,
    ← Finset.sum_add_sum_compl U (cellCost C), ← Finset.sum_add_sum_compl U (cellCost B)]
  have hc : ∑ x ∈ Uᶜ, cellCost C x = ∑ x ∈ Uᶜ, cellCost B x := by
    apply Finset.sum_congr rfl
    intro x hx
    simp only [cellCost, h x (by simpa using hx)]
  omega

/-- A board obtained by moving tiles within `U` has potential at most the old
one plus the total distance the tiles of `U` moved. -/
theorem manhattan_le_of_displacement (B C : Board n) (U : Finset (Cell n))
    (h : ∀ x, x ∉ U → C x = B x) :
    manhattan C ≤ manhattan B + ∑ x ∈ U, gridDistance x (position B (C x)) := by
  rw [manhattan_eq_sum_cellCost, manhattan_eq_sum_cellCost]
  have hpt : ∀ x, cellCost C x ≤
      cellCost B (position B (C x)) + gridDistance x (position B (C x)) := by
    intro x
    have hB : B (position B (C x)) = C x := by simp [position]
    unfold cellCost
    rw [hB]
    split_ifs
    · omega
    · simp only [gridDistance, Nat.dist]; omega
  have hsum : ∑ x, gridDistance x (position B (C x)) =
      ∑ x ∈ U, gridDistance x (position B (C x)) := by
    rw [← Finset.sum_subset (Finset.subset_univ U)]
    intro x _ hx
    rw [h x hx]; simp [position]
  calc ∑ x, cellCost C x
      ≤ ∑ x, (cellCost B (position B (C x)) + gridDistance x (position B (C x))) :=
        Finset.sum_le_sum (fun x _ => hpt x)
    _ = ∑ x, cellCost B x + ∑ x ∈ U, gridDistance x (position B (C x)) := by
        rw [Finset.sum_add_distrib, ← hsum]
        congr 1
        exact Equiv.sum_comp (C.trans B.symm) (cellCost B)

/-- Exchanging two tile names changes the potential by at most twice the
distance between their targets. -/
theorem manhattan_relabel_swap_le (X : Board n) (a b : Tile n) (ha : a.val ≠ 0)
    (hb : b.val ≠ 0) :
    manhattan (relabel X (Equiv.swap a b)) ≤
      manhattan X+2*gridDistance (position (target n) a) (position (target n) b) := by
  set D := gridDistance (position (target n) a) (position (target n) b)
  rw [manhattan_eq_sum_cellCost, manhattan_eq_sum_cellCost]
  have hpt : ∀ x, cellCost (relabel X (Equiv.swap a b)) x ≤
      cellCost X x+((if X x = a then D else 0)+(if X x = b then D else 0)) := by
    intro x
    simp only [cellCost, relabel_apply]
    by_cases hxa : X x = a
    · have htri := (show gridDistance x (position (target n) b) ≤
          gridDistance x (position (target n) a) + D by
        simp only [D, gridDistance, Nat.dist]; omega)
      simp only [hxa, Equiv.swap_apply_left, ↓reduceIte]
      split_ifs <;> omega
    by_cases hxb : X x = b
    · have htri := (show gridDistance x (position (target n) a) ≤
          gridDistance x (position (target n) b) + D by
        simp only [D, gridDistance, Nat.dist]; omega)
      simp only [hxb, Equiv.swap_apply_right, ↓reduceIte]
      split_ifs <;> omega
    · simp only [Equiv.swap_apply_of_ne_of_ne hxa hxb, hxa, hxb, ↓reduceIte]
      omega
  have hsum : ∑ x, ((if X x = a then D else 0)+(if X x = b then D else 0)) = 2*D := by
    rw [Finset.sum_add_distrib]
    have ha : ∑ x, (if X x = a then D else 0) = D := by
      rw [Finset.sum_eq_single (X.symm a)]
      · simp
      · intro x _ hx; rw [if_neg]; intro h; exact hx (by rw [← h]; simp)
      · simp
    have hb : ∑ x, (if X x = b then D else 0) = D := by
      rw [Finset.sum_eq_single (X.symm b)]
      · simp
      · intro x _ hx; rw [if_neg]; intro h; exact hx (by rw [← h]; simp)
      · simp
    omega
  calc ∑ x, cellCost (relabel X (Equiv.swap a b)) x
      ≤ ∑ x, (cellCost X x+((if X x = a then D else 0)+(if X x = b then D else 0))) :=
        Finset.sum_le_sum (fun x _ => hpt x)
    _ = ∑ x, cellCost X x+2*D := by rw [Finset.sum_add_distrib, hsum]

end

section
variable {n : ℕ} [NeZero n]

/-- Relabeling a path by a swap of two tile names changes its inefficiency by
at most twice the distance between their targets. -/
theorem Path.inefficientMoves_relabel_swap_le {B C : Board n} (p : Path B C)
    (a b : Tile n) (ha : a.val ≠ 0) (hb : b.val ≠ 0) (he : Equiv.swap a b 0 = 0) :
    (p.relabel (Equiv.swap a b) he).inefficientMoves ≤
      p.inefficientMoves+2*gridDistance (position (target n) a) (position (target n) b) := by
  have h₁ := (p.relabel (Equiv.swap a b) he).length_add_manhattan
  have h₂ := p.length_add_manhattan
  rw [Path.length_relabel] at h₁
  have hC := manhattan_relabel_swap_le C a b ha hb
  have hB := manhattan_relabel_swap_le (_root_.SlidingPuzzle.relabel B (Equiv.swap a b)) a b ha hb
  rw [show _root_.SlidingPuzzle.relabel (_root_.SlidingPuzzle.relabel B (Equiv.swap a b))
    (Equiv.swap a b) = B by ext x; simp [_root_.SlidingPuzzle.relabel]] at hB
  omega

end

section
variable {m n : ℕ} [NeZero m] [NeZero n]

omit [NeZero m] in
private theorem swap_embedding' (ι : Cell m ↪ Cell n) (a b c : Cell m) :
    Equiv.swap (ι a) (ι b) (ι c)=ι (Equiv.swap a b c) := by
  by_cases ha : c=a
  · subst c; simp
  by_cases hb : c=b
  · subst c; simp
  rw [Equiv.swap_apply_of_ne_of_ne (fun h => ha (ι.injective h))
    (fun h => hb (ι.injective h)), Equiv.swap_apply_of_ne_of_ne ha hb]

/-- Lifting a local path with target-compatible labels through a
distance-preserving embedding preserves its inefficiency. -/
theorem Path.exists_embedded_efficient {A D : Board m} (p : Path A D)
    (ι : Cell m ↪ Cell n) (hι : ∀ a b, gridDistance (ι a) (ι b) = gridDistance a b)
    (η : Tile m ↪ Tile n) (hη : η 0=0)
    (htgt : ∀ l : Tile m, l ≠ 0 → position (target n) (η l) = ι (position (target m) l))
    (B : Board n) (hB : ∀ c, B (ι c)=η (A c)) :
    ∃ C : Board n, ∃ q : Path B C, q.length=p.length ∧
      q.inefficientMoves=p.inefficientMoves ∧
      (∀ c, C (ι c)=η (D c)) ∧
      (∀ c : Cell n, c ∉ Set.range ι → C c=B c) := by
  induction p generalizing B with
  | nil A => exact ⟨B,Path.nil B,rfl,rfl,hB,fun _ _ => rfl⟩
  | @cons A A' D hstep p ih =>
      obtain ⟨c,hc,rfl⟩ := hstep
      have hb := blank_of_embedded_board ι η hη A B hB
      let B' := swapCells B (ι (blank A)) (ι c)
      have hB' (x : Cell m) : B' (ι x)=η (swapCells A (blank A) c x) := by
        simp only [B',swapCells_apply,swap_embedding',hB]
      obtain ⟨C,q,hq,hqi,hC,hfix⟩ := ih B' hB'
      have hstep : Step B B' := ⟨ι c,by rw [hb, hι]; exact hc,by rw [hb]⟩
      have hcA : c ≠ blank A := by
        intro h; rw [h, gridDistance_self] at hc; omega
      have hAc : A c ≠ 0 := by
        intro h
        apply hcA
        simp [blank, position, ← h]
      have hcB : ι c ≠ blank B := by
        rw [hb]; exact fun h => hcA (ι.injective h)
      have hglobal := manhattan_blank_swap_balance B (ι c) hcB
      have hlocal := manhattan_blank_swap_balance A c hcA
      rw [hB c, htgt _ hAc, hb, hι, hι] at hglobal
      change manhattan B' + _ = _ at hglobal
      refine ⟨C,Path.cons hstep q,?_,?_,hC,?_⟩
      · simp [Path.length,hq]
      · simp only [Path.inefficientMoves, hqi]
        congr 1
        by_cases h : manhattan A < manhattan (swapCells A (blank A) c)
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)]
      · intro x hx
        rw [hfix x hx]
        exact swapCells_preserves B
          (fun h => hx ⟨blank A,h.symm⟩) (fun h => hx ⟨c,h.symm⟩)

end
end SlidingPuzzle
