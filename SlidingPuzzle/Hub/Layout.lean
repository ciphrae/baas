import SlidingPuzzle.Hub.Interface
import SlidingPuzzle.Paths
import SlidingPuzzle.Algorithm.Accounting

/-! # The hub layout on boards

Cells, squares, classes, corridor cells and regions for a board of side
`n = k*s` (`HDims n k s`), the relation `Rel` between a board and an `IState`,
and the count of misplaced tiles that Cleanup pays for. -/
namespace SlidingPuzzle.Hub

variable {n k s : ℕ}

theorem HDims.div_lt (hd : HDims n k s) (x : Fin n) : x.val / s < k := by
  have hs : 0 < s := by have := hd.room; omega
  apply (Nat.div_lt_iff_lt_mul hs).mpr
  calc x.val < n := x.isLt
    _ = k * s := hd.mul.symm

/-- The square containing a cell. -/
def sqOf (hd : HDims n k s) (x : Cell n) : Sq k :=
  (⟨x.1.val / s, hd.div_lt x.1⟩, ⟨x.2.val / s, hd.div_lt x.2⟩)

/-- The class of a tile: the square of its target cell. -/
def classOf (hd : HDims n k s) (t : Tile n) : Sq k := sqOf hd (position (target n) t)

/-- Cell of a board from natural coordinates (reduced mod `n`; exact in range). -/
def mkCell (n : ℕ) [NeZero n] (r c : ℕ) : Cell n := (Fin.ofNat n r, Fin.ofNat n c)

/-- Position `q` of the row half `H = (b, c, right)`: row `b*s + c`, column
`(c+1)*s + q` (right) or `c*s - 1 - q` (left). -/
def rowCell (k s : ℕ) [NeZero n] (H : RowH k) (q : ℕ) : Cell n :=
  mkCell n (H.1.val * s + H.2.1.val)
    (if H.2.2 then (H.2.1.val + 1) * s + q else H.2.1.val * s - 1 - q)

/-- Position `q` of the column half `V = (c, a, lower)`: column `c*s + a`; with
`m = s - k`, band `a+1+q/m` at row offset `k + q%m` (lower) or band `a-1-q/m`
at row offset `s-1-q%m` (upper). -/
def colCell (k s : ℕ) [NeZero n] (V : ColH k) (q : ℕ) : Cell n :=
  mkCell n
    (if V.2.2 then (V.2.1.val + 1 + q / (s - k)) * s + (k + q % (s - k))
      else (V.2.1.val - 1 - q / (s - k)) * s + (s - 1 - q % (s - k)))
    (V.1.val * s + V.2.1.val)

/-- The region of square `Q`: its reservoir (row and column offsets `≥ k`), its
landing strip (row offset `Q.2`) and its own column piece (row offset `≥ k`,
column offset `Q.1`). -/
def region (k s : ℕ) (Q : Sq k) (x : Cell n) : Prop :=
  x.1.val / s = Q.1.val ∧ x.2.val / s = Q.2.val ∧
    (x.1.val % s = Q.2.val ∨
      (k ≤ x.1.val % s ∧ (k ≤ x.2.val % s ∨ x.2.val % s = Q.1.val)))

instance (k s : ℕ) (Q : Sq k) (x : Cell n) : Decidable (region k s Q x) := by
  unfold region; infer_instance

/-- The reservoir rectangle of square `Q`. -/
def reservoir (k s : ℕ) (Q : Sq k) (x : Cell n) : Prop :=
  x.1.val / s = Q.1.val ∧ x.2.val / s = Q.2.val ∧ k ≤ x.1.val % s ∧ k ≤ x.2.val % s

instance (k s : ℕ) (Q : Sq k) (x : Cell n) : Decidable (reservoir k s Q x) := by
  unfold reservoir; infer_instance

/-- Nonblank tiles of class `y` in the region of `Q`. -/
noncomputable def regionCount (hd : HDims n k s) (B : Board n) (Q y : Sq k) : ℕ := by
  classical
  exact (Finset.univ.filter fun x : Cell n =>
    region k s Q x ∧ (B x).val ≠ 0 ∧ classOf hd (B x) = y).card

/-- A board realizes an `IState`: corridor positions hold nonblank tiles of the
recorded classes, region counts agree, and the blank is in the reservoir of
the recorded square. -/
def Rel (hd : HDims n k s) [NeZero n] (B : Board n) (σ : IState k) : Prop :=
  (∀ H q, q < rowLen k s H →
    (B (rowCell k s H q)).val ≠ 0 ∧ classOf hd (B (rowCell k s H q)) = σ.row H q) ∧
  (∀ V q, q < colLen k s V →
    (B (colCell k s V q)).val ≠ 0 ∧ classOf hd (B (colCell k s V q)) = σ.col V q) ∧
  (∀ Q y, regionCount hd B Q y = σ.cnt Q y) ∧
  reservoir k s σ.blank (blank B)

/-- Nonblank tiles outside the square of their target. -/
noncomputable def misplaced (hd : HDims n k s) (B : Board n) : ℕ := by
  classical
  exact (Finset.univ.filter fun x : Cell n =>
    (B x).val ≠ 0 ∧ classOf hd (B x) ≠ sqOf hd x).card

/-- The `IState` read off a board. -/
noncomputable def absState (hd : HDims n k s) [NeZero n] (B : Board n) : IState k where
  row H q := classOf hd (B (rowCell k s H q))
  col V q := classOf hd (B (colCell k s V q))
  cnt := regionCount hd B
  blank := sqOf hd (blank B)

/-! ## Facts about the layout (to be proved in `Hub/LayoutFacts.lean`) -/

/-- A board with its blank in a reservoir realizes its own abstraction. -/
theorem rel_absState (hd : HDims n k s) [NeZero n] (B : Board n)
    (hb : reservoir k s (sqOf hd (blank B)) (blank B)) : Rel hd B (absState hd B) := by
  sorry

/-- Every region has `regionSize` cells, one of them possibly the blank. -/
theorem absState_regionTotal (hd : HDims n k s) [NeZero n] (B : Board n)
    (hb : reservoir k s (sqOf hd (blank B)) (blank B)) (Q : Sq k) :
    (∑ y, (absState hd B).cnt Q y) + (if (absState hd B).blank = Q then 1 else 0) =
      regionSize k s := by
  sorry

/-- Every class has `s²` tiles, the last one `s² - 1` besides the blank. -/
theorem absState_classTotal (hd : HDims n k s) [NeZero n] (B : Board n)
    (hb : reservoir k s (sqOf hd (blank B)) (blank B)) (y : Sq k) :
    (∑ Q, (absState hd B).cnt Q y) + (absState hd B).corrCount s y =
      s ^ 2 - (if IsLast y then 1 else 0) := by
  sorry

/-- Misplaced tiles lie in corridors or are counted by `offCount`. -/
theorem misplaced_le_of_rel (hd : HDims n k s) [NeZero n] {B : Board n} {σ : IState k}
    (hR : Rel hd B σ) : misplaced hd B ≤ k ^ 2 * sqCorridor k s + σ.offCount := by
  sorry

/-- The blank can be brought into a reservoir cheaply. -/
theorem exists_normalize (hd : HDims n k s) [NeZero n] (B : Board n) :
    ∃ C : Board n, ∃ p : Path B C,
      reservoir k s (sqOf hd (blank C)) (blank C) ∧ p.inefficientMoves ≤ 2 * n := by
  sorry

end SlidingPuzzle.Hub
