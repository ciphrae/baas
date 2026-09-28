import SlidingPuzzle.Tree.Abs

/-! # Routes of squares

A tile of class `x` in square `v` first hops along row lanes of its band until
its block column is `x.2`, then along column lanes of that block column until
its band is `x.1`. `stage v x` is the lane of the next hop (an axis flag and a
`LaneI`) with the source coordinate, `nxt v x` the square it lands in, and
`rank v x` the number of hops left. -/
namespace SlidingPuzzle.Tree
open SlidingPuzzle.Hub (Sq)

variable {k q : ℕ} (L : LaneSys k q)

/-- A lane of either axis: `false` for row lanes, `true` for column lanes. -/
abbrev Ln (k q : ℕ) := Bool × LaneI k q

/-- The landing square of a lane. -/
def land (l : Ln k q) : Sq k := if l.1 then colLand l.2 else rowLand l.2

/-- A tile of class `z` on lane `l` moves toward its target. -/
def lgood (l : Ln k q) (z : Sq k) : Prop := if l.1 then colGood l.2 z else rowGood l.2 z

instance (l : Ln k q) (z : Sq k) : Decidable (lgood l z) := by unfold lgood; split <;> infer_instance

/-- Length of a lane in cells. -/
def llen (s : ℕ) (l : Ln k q) : ℕ := if l.1 then colLen L s l.2 else rowLen L s l.2

/-- Cells per block of a lane. -/
def lstep (s : ℕ) (l : Ln k q) : ℕ := if l.1 then s - q else s

/-- Offset of the insertion position inside its block. -/
def loff (k s : ℕ) (l : Ln k q) : ℕ :=
  if l.1 then (if l.2.side then k - q else 0) else (if l.2.side then s - 1 else s - 1 - k)

/-- Insertion position of a hop from block (or band) `J`. -/
def lpos (k s : ℕ) (l : Ln k q) (J : Fin k) : ℕ :=
  if l.1 then colPos k s q l.2 J else rowPos k s l.2 J

/-- The next lane from `v` toward `x`, with the source coordinate. -/
def LaneSys.stage (v x : Sq k) : Ln k q × Fin k :=
  if v.2 ≠ x.2 then
    ((false, ⟨v.1, (L.hop v.2 x.2).1, (L.hop v.2 x.2).2, decide (x.2 < v.2)⟩), v.2)
  else ((true, ⟨v.2, (L.hop v.1 x.1).1, (L.hop v.1 x.1).2, decide (x.1 < v.1)⟩), v.1)

/-- The square reached by the next hop. -/
def LaneSys.nxt (v x : Sq k) : Sq k := land (L.stage v x).1

/-- Hops left from `v` to `x`. -/
def LaneSys.srank (v x : Sq k) : ℕ := L.rank v.2 x.2 + L.rank v.1 x.1

/-- The resolved operation of a hop along lane `l` from source coordinate `J`. -/
def hopEv (l : Ln k q) (J : Fin k) (y : Sq k) : REvent k q :=
  if l.1 then .hopC l.2 J y else .hopR l.2 J y

/-- The source square of a hop along lane `l` from coordinate `J`. -/
def src (l : Ln k q) (J : Fin k) : Sq k := if l.1 then (J, l.2.b) else (l.2.b, J)

theorem lpos_eq (k s : ℕ) (l : Ln k q) (J : Fin k) :
    lpos k s l J = LaneSys.pdist l.2.t.val J.val * lstep s l + loff k s l := by
  unfold lpos lstep loff colPos rowPos
  split_ifs <;> rfl

section facts

variable {L}

theorem stage_src {v x : Sq k} (h : v ≠ x) : src (L.stage v x).1 (L.stage v x).2 = v := by
  by_cases h1 : v.2 = x.2
  · simp [LaneSys.stage, h1, src]; exact Prod.ext rfl h1.symm
  · simp [LaneSys.stage, h1, src]

theorem stage_in {v x : Sq k} (h : v ≠ x) : LIn L (L.stage v x).1.2 (L.stage v x).2 := by
  by_cases h1 : v.2 = x.2
  · have h2 : v.1 ≠ x.1 := fun e => h (Prod.ext e h1)
    simp only [LaneSys.stage, h1, ne_eq, not_true_eq_false, if_false, LIn, blen]
    exact L.hop_in v.1 x.1 h2
  · simp only [LaneSys.stage, h1, ne_eq, not_false_eq_true, if_true, LIn, blen]
    exact L.hop_in v.2 x.2 h1

theorem stage_good {v x : Sq k} (h : v ≠ x) : lgood (L.stage v x).1 x := by
  by_cases h1 : v.2 = x.2
  · have h2 : v.1 ≠ x.1 := fun e => h (Prod.ext e h1)
    simp only [LaneSys.stage, h1, ne_eq, not_true_eq_false, if_false, lgood, if_true, colGood]
    by_cases h3 : x.1 < v.1
    · simp only [h3, decide_true, if_true]; exact L.hop_ge _ _ h3
    · simp only [h3, decide_false, Bool.false_eq_true, if_false]
      exact L.hop_le _ _ (lt_of_le_of_ne (not_lt.mp h3) h2)
  · simp only [LaneSys.stage, h1, ne_eq, not_false_eq_true, if_true, lgood,
      Bool.false_eq_true, if_false, rowGood]
    by_cases h3 : x.2 < v.2
    · simp only [h3, decide_true, if_true]; exact L.hop_ge _ _ h3
    · simp only [h3, decide_false, Bool.false_eq_true, if_false]
      exact L.hop_le _ _ (lt_of_le_of_ne (not_lt.mp h3) h1)

theorem srank_self (x : Sq k) : L.srank x x = 0 := by
  unfold LaneSys.srank; rw [LaneSys.rank_self, LaneSys.rank_self]

theorem srank_nxt {v x : Sq k} (h : v ≠ x) : L.srank v x = L.srank (L.nxt v x) x + 1 := by
  by_cases h1 : v.2 = x.2
  · have h2 : v.1 ≠ x.1 := fun e => h (Prod.ext e h1)
    simp only [LaneSys.srank, LaneSys.nxt, LaneSys.stage, h1, ne_eq, not_true_eq_false, if_false,
      land, if_true, colLand]
    rw [LaneSys.rank_hop L v.1 x.1 h2]; ring
  · simp only [LaneSys.srank, LaneSys.nxt, LaneSys.stage, h1, ne_eq, not_false_eq_true, if_true,
      land, Bool.false_eq_true, if_false, rowLand]
    rw [LaneSys.rank_hop L v.2 x.2 h1]; ring

theorem srank_le (v x : Sq k) : L.srank v x ≤ 2 * L.depth := by
  unfold LaneSys.srank
  have := LaneSys.rank_le L v.2 x.2
  have := LaneSys.rank_le L v.1 x.1
  omega

theorem srank_pos {v x : Sq k} (h : v ≠ x) : 0 < L.srank v x := by
  rw [srank_nxt h]; omega

theorem srank_eq_zero {v x : Sq k} (h : L.srank v x = 0) : v = x := by
  by_contra hne; have := srank_pos (L := L) hne; omega

end facts

end SlidingPuzzle.Tree
