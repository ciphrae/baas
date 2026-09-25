import SlidingPuzzle.Moves.StripTrace

/-! A three-row carry that moves a tile along a reservoir row at four
inefficient moves per cell.

Strip rows `0, 1, 2`; the tile starts at `(2, m+1)` and the blank at `(1, 0)`.
The blank walks along row `0` to the tile, lifts it into row `1`, and carries it
back to `(1, 1)`. The carries return the blank alternately through rows `2`
and `0`, so each return through row `0` undoes the walk's shift there. The net
effect (`shiftEffect`) is a rotation: row `2` shifts one cell right, the tile
of `(1, 1)` drops into row `2`, and the carried tile lands on `(1, 1)`. The word
has length at most `6m+6` and moves tiles a total distance `2m+4`, so at most
`4m+5` of its moves are inefficient, against `5m` for carries that always
return through the same row. -/
namespace SlidingPuzzle
namespace Strip

/-- Push the tile at `(1, a+2)` to `(1, a+1)`, and return the blank round row `r`
to `(1, a)`. -/
def carry (r a : ℕ) : List SCell := [(1,a+2), (r,a+2), (r,a+1), (r,a), (1,a)]

/-- From `(0, a)`: walk along row `0` and carry the tile at `(2, a+2j+2)` to
`(1, a+1)`, returning alternately through rows `2` and `0`. -/
def pairs : ℕ → ℕ → List SCell
  | a, 0 => [(0,a+1), (0,a+2), (1,a+2), (2,a+2), (2,a+1), (1,a+1)] ++ carry 0 a
  | a, j+1 => [(0,a+1), (0,a+2)] ++ pairs (a+2) j ++ carry 2 (a+1) ++ carry 0 a

/-- The trace of `pairs a j`, with `m = 2j+1`. -/
def pairsEffect (a m : ℕ) (x : SCell) : SCell :=
  if x = (0,a) then (1,a) else if x = (1,a) then (0,a)
  else if x = (1,a+1) then (2,a+m+1)
  else if x = (2,a+1) then (1,a+1)
  else if x.1 = 2 ∧ a+2 ≤ x.2 ∧ x.2 ≤ a+m+1 then (2, x.2-1)
  else x

theorem last_pairs (a j : ℕ) (b : SCell) : last b (pairs a j) = (1,a) := by
  cases j <;> simp [pairs, last_append, carry, last]

theorem trace_pairs (a j : ℕ) (x : SCell) :
    trace (0,a) (pairs a j) x = pairsEffect a (2*j+1) x := by
  induction j generalizing a x with
  | zero =>
    by_cases hx : x ∈ [(0,a),(0,a+1),(0,a+2),(1,a),(1,a+1),(1,a+2),(2,a+1),(2,a+2)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [pairs, carry, trace, swap, pairsEffect]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      rw [trace_of_not_mem _ _ _ hx.1 (by simp [pairs, carry]; tauto)]
      obtain ⟨r, c⟩ := x
      simp only [pairsEffect, Prod.mk.injEq] at hx ⊢
      split_ifs <;> simp_all <;> omega
  | succ j ih =>
    simp only [pairs, trace_append, last_append, last_pairs,
      show last (1, a+2) (carry 2 (a+1)) = (1,a+1) by simp [carry, last],
      show last (0, a) [(0,a+1),(0,a+2)] = (0,a+2) by simp [last], ih]
    by_cases hx : x ∈ [(0,a),(0,a+1),(0,a+2),(1,a),(1,a+1),(1,a+2),(1,a+3),(2,a+1),
      (2,a+2),(2,a+3)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp +arith [carry, trace, swap, pairsEffect]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      rw [trace_of_not_mem (1,a+1) (carry 0 a) x hx.2.2.2.2.1 (by simp [carry]; tauto),
        trace_of_not_mem (1,a+2) (carry 2 (a+1)) x hx.2.2.2.2.2.1 (by simp [carry]; tauto)]
      obtain ⟨r, c⟩ := x
      simp only [Prod.mk.injEq] at hx
      by_cases hr : r = 2 ∧ a+4 ≤ c ∧ c ≤ a+2*(j+1)+2
      · have h1 : pairsEffect (a+2) (2*j+1) (r,c) = (2,c-1) := by
          simp only [pairsEffect, Prod.mk.injEq]; split_ifs <;> simp_all <;> omega
        have h2 : pairsEffect a (2*(j+1)+1) (r,c) = (2,c-1) := by
          simp only [pairsEffect, Prod.mk.injEq]; split_ifs <;> simp_all <;> omega
        rw [h1, h2]; simp [trace, swap]
      · have h1 : pairsEffect (a+2) (2*j+1) (r,c) = (r,c) := by
          simp only [pairsEffect, Prod.mk.injEq]; split_ifs <;> simp_all <;> omega
        have h2 : pairsEffect a (2*(j+1)+1) (r,c) = (r,c) := by
          simp only [pairsEffect, Prod.mk.injEq]; split_ifs <;> simp_all <;> omega
        rw [h1, h2]; simp only [trace, swap, Prod.mk.injEq]; split_ifs <;> simp_all

/-- From `(1, 0)`: carry the tile at `(2, m+1)` to `(1, 1)`. -/
def shiftWord (m : ℕ) : List SCell :=
  if m % 2 = 1 then (0,0) :: pairs 0 (m/2)
  else if m = 0 then [(1,1), (2,1), (2,0), (1,0)]
  else [(1,1), (0,1)] ++ pairs 1 (m/2-1) ++ carry 2 0

/-- The effect of `shiftWord m`: a rotation through row `2` starting at column
`s = m % 2`. -/
def shiftEffect (m : ℕ) (x : SCell) : SCell :=
  if x = (1,1) then (2,m+1)
  else if x = (2, m % 2) then (1,1)
  else if x.1 = 2 ∧ m % 2 < x.2 ∧ x.2 ≤ m+1 then (2, x.2-1)
  else x

theorem trace_shiftWord (m : ℕ) (x : SCell) : trace (1,0) (shiftWord m) x = shiftEffect m x := by
  obtain ⟨r, c⟩ := x
  unfold shiftWord
  split_ifs with hodd hzero
  · have hm : 2*(m/2)+1 = m := by omega
    simp only [trace, trace_pairs, hm, pairsEffect, shiftEffect, swap, hodd, Prod.mk.injEq]
    split_ifs <;> simp_all <;> omega
  · subst hzero
    by_cases hx : (r,c) ∈ [(1,0),(1,1),(2,1),(2,0)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h|h|h|h <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h <;>
        simp [trace, swap, shiftEffect]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      rw [trace_of_not_mem _ _ _ hx.1 (by simp only [Prod.mk.injEq] at hx; simp; omega)]
      simp only [shiftEffect, Prod.mk.injEq] at hx ⊢
      split_ifs <;> simp_all <;> omega
  · have hm : 2*(m/2-1)+1 = m-1 := by omega
    have hev : m % 2 = 0 := by omega
    simp only [trace_append, show last (1,0) [(1,1),(0,1)] = (0,1) by simp [last],
      show last (1,0) ([(1,1),(0,1)] ++ pairs 1 (m/2-1)) = (1,1) by
        simp [last_append, last_pairs, last], trace_pairs, hm, shiftEffect, hev]
    by_cases hx : (r,c) ∈ [(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h|h|h|h|h|h|h <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h <;>
        simp [carry, trace, swap, pairsEffect] <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      rw [trace_of_not_mem _ _ _ hx.2.2.1 (by simp only [Prod.mk.injEq] at hx; simp [carry]; omega)]
      simp only [Prod.mk.injEq] at hx
      by_cases hr : r = 2 ∧ 3 ≤ c ∧ c ≤ m+1
      · have h1 : pairsEffect 1 (m-1) (r,c) = (2,c-1) := by
          simp only [pairsEffect, Prod.mk.injEq]; split_ifs <;> simp_all <;> omega
        rw [h1]; simp only [trace, swap, Prod.mk.injEq]; split_ifs <;> simp_all <;> omega
      · have h1 : pairsEffect 1 (m-1) (r,c) = (r,c) := by
          simp only [pairsEffect, Prod.mk.injEq]; split_ifs <;> simp_all <;> omega
        rw [h1]; simp only [trace, swap, Prod.mk.injEq]; split_ifs <;> simp_all <;> omega

theorem length_pairs (a j : ℕ) : (pairs a j).length = 12*j+11 := by
  induction j generalizing a with
  | zero => rfl
  | succ j ih => simp [pairs, carry, ih]; ring

theorem walk_pairs (a j : ℕ) : Walk (0,a) (pairs a j) := by
  induction j generalizing a with
  | zero => simp [pairs, carry, Walk, sdist, Nat.dist]
  | succ j ih =>
    simp only [pairs, walk_append, last_append, last_pairs,
      show last (0, a) [(0,a+1),(0,a+2)] = (0,a+2) by simp [last], ih]
    simp [carry, Walk, sdist, Nat.dist, last]

theorem mem_pairs (a j : ℕ) (x : SCell) (hx : x ∈ pairs a j) :
    x.1 ≤ 2 ∧ a ≤ x.2 ∧ x.2 ≤ a+2*j+2 := by
  induction j generalizing a with
  | zero =>
    simp only [pairs, carry, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  | succ j ih =>
    simp only [pairs, List.mem_append] at hx
    rcases hx with ((hx|hx)|hx)|hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl|rfl <;> simp <;> omega
    · have := ih (a+2) hx; omega
    · simp only [carry, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl <;> simp <;> omega
    · simp only [carry, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl <;> simp <;> omega

theorem length_shiftWord (m : ℕ) : (shiftWord m).length ≤ 6*m+6 := by
  unfold shiftWord
  split_ifs with h1 h2
  · simp [length_pairs]; omega
  · simp
  · simp [length_pairs, carry]; omega

theorem last_shiftWord (m : ℕ) : last (1,0) (shiftWord m) = (1,0) := by
  unfold shiftWord
  split_ifs <;> simp [last, last_append, last_pairs, carry]

theorem walk_shiftWord (m : ℕ) : Walk (1,0) (shiftWord m) := by
  unfold shiftWord
  split_ifs
  · simp only [Walk]; exact ⟨by simp [sdist, Nat.dist], walk_pairs 0 _⟩
  · simp [Walk, sdist, Nat.dist]
  · simp only [walk_append, last_append, last_pairs]
    refine ⟨⟨by simp [Walk, sdist, Nat.dist], ?_⟩, by simp [carry, Walk, sdist, Nat.dist, last]⟩
    simp only [show last (1,0) [(1,1),(0,1)] = (0,1) by simp [last]]
    exact walk_pairs 1 _

theorem mem_shiftWord (m : ℕ) (x : SCell) (hx : x ∈ shiftWord m) : region 2 (m+1) x := by
  unfold shiftWord at hx
  split_ifs at hx with h1 h2
  · simp only [List.mem_cons] at hx
    rcases hx with rfl | h
    · simp [region]
    · have := mem_pairs 0 _ x h; exact ⟨this.1, by omega⟩
  · subst h2; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl <;> simp [region]
  · simp only [List.mem_append] at hx
    rcases hx with (hx|hx)|hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl|rfl <;> simp [region]
    · have := mem_pairs 1 _ x hx; exact ⟨this.1, by omega⟩
    · simp only [carry, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl <;> simp [region] <;> omega

/-- The rotation moves tiles a total distance `2m+4`. -/
theorem sum_sdist_shiftEffect (m : ℕ) :
    ∑ q ∈ Finset.range 3 ×ˢ Finset.range (m+2), sdist q (shiftEffect m q) ≤ 2*m+4 := by
  let g : SCell → ℕ := fun q =>
    if q = (1,1) then m+1 else if q = (2,0) then 2 else if q.1 = 2 then 1 else 0
  have hpt : ∀ q, sdist q (shiftEffect m q) ≤ g q := by
    rintro ⟨r, c⟩
    simp only [sdist, shiftEffect, g, Prod.mk.injEq, Nat.dist]
    split_ifs <;> simp_all <;> omega
  refine (Finset.sum_le_sum (fun q _ => hpt q)).trans (le_of_eq ?_)
  rw [Finset.sum_product, show Finset.range 3 = {0, 1, 2} by rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [g, Prod.mk.injEq]
  have h1 : ∑ c ∈ Finset.range (m+2), (if c = 1 then m+1 else 0) = m+1 := by
    rw [Finset.sum_ite_eq']; simp
  have h2 : ∑ c ∈ Finset.range (m+2), (if c = 0 then 2 else 1) = m+3 := by
    rw [Finset.sum_range_succ']; simp
  simp [h1, h2]
  omega

end Strip

open Strip in
/-- The three-row carry on a board: rows `row 0, row 1, row 2` and columns
`col 0..col (m+1)`. The tile at `(row 2, col (m+1))` reaches `(row 1, col 1)`
and the blank returns to `(row 1, col 0)`, with at most `6m+6` moves and a
potential rise of at most `2m+4`. -/
theorem exists_shiftWord {n : ℕ} [NeZero n] (row col : ℕ → Fin n) (m : ℕ)
    (hrow : StripCol row 2) (hcol : StripCol col (m+1)) (X : Board n)
    (hX : blank X = (row 1, col 0)) :
    ∃ Y : Board n, ∃ cs : List (Cell n), Executes X cs Y ∧ cs.length ≤ 6*m+6 ∧
      manhattan Y ≤ manhattan X+(2*m+4) ∧ blank Y = (row 1, col 0) ∧
      Y (row 1, col 1) = X (row 2, col (m+1)) ∧
      ∀ x ∈ cs, ∃ r c, r ≤ 2 ∧ c ≤ m+1 ∧ x = (row r, col c) := by
  have hb : region 2 (m+1) (1,0) := by simp [region]
  obtain ⟨Y, hE, hY⟩ := exists_executes_trace hrow hcol (1,0) (shiftWord m) hb
    (mem_shiftWord m) (walk_shiftWord m) X hX
  have hM := manhattan_le_trace hrow hcol (1,0) (shiftWord m) hb (mem_shiftWord m) X Y hX hE hY
  simp only [trace_shiftWord] at hM hY
  refine ⟨Y, _, hE, by simp [length_shiftWord m], hM.trans
    (Nat.add_le_add_left (sum_sdist_shiftEffect m) _), ?_, ?_, ?_⟩
  · have h0 : Y (row 1, col 0) = 0 := by
      have := hY (1,0) hb
      simp only [emb, shiftEffect] at this
      rw [this]; simpa [← hX, blank, position]
    simp only [blank, position, Equiv.symm_apply_eq, h0]
  · have := hY (1,1) (by simp [region])
    simpa [emb, shiftEffect] using this
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    exact ⟨c.1, c.2, (mem_shiftWord m c hc).1, (mem_shiftWord m c hc).2, rfl⟩

open Strip in
/-- `exists_shiftWord` with its exact effect: the rotation `shiftEffect` on the
strip; nothing outside the strip changes. -/
theorem exists_shiftWord_trace {n : ℕ} [NeZero n] (row col : ℕ → Fin n) (m : ℕ)
    (hrow : StripCol row 2) (hcol : StripCol col (m+1)) (X : Board n)
    (hX : blank X = (row 1, col 0)) :
    ∃ Y : Board n, ∃ cs : List (Cell n), Executes X cs Y ∧ cs.length ≤ 6*m+6 ∧
      (∀ q, region 2 (m+1) q → Y (emb row col q) = X (emb row col (shiftEffect m q))) ∧
      (∀ x, (∀ q, region 2 (m+1) q → x ≠ emb row col q) → Y x = X x) := by
  have hb : region 2 (m+1) (1,0) := by simp [region]
  obtain ⟨Y, hE, hY⟩ := exists_executes_trace hrow hcol (1,0) (shiftWord m) hb
    (mem_shiftWord m) (walk_shiftWord m) X hX
  refine ⟨Y, _, hE, by simp [length_shiftWord m],
    fun q hq => by rw [hY q hq, trace_shiftWord], ?_⟩
  intro x hx
  apply hE.preserves
  · rw [hX]; exact hx (1,0) hb
  · intro h
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
    exact hx c (mem_shiftWord m c hc) rfl

end SlidingPuzzle
