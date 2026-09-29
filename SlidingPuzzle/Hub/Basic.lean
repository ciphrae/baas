import Mathlib

/-! # Hub transport: index types and the arithmetic of the layout

The board of side `n = k*s` is cut into `k × k` squares of side `s`. A square is
`(band, block column)`, and a tile's *class* is the square of its target cell.

In every band the top `k` rows (row offsets `c < k`) are the row corridors:
row offset `c` of band `b` is `R(b,c)`, which carries tiles whose target block
column is `c`. Inside block column `c` that row is the *landing strip* of the
hub square `(b,c)`; left and right of block `c` it forms two *row halves*,
whose position `0` is next to block `c`.

Below the row group (row offsets `≥ k`), column offset `a < k` of block column
`c` is the column corridor `C(c,a)`, carrying class `(a,c)`; it is present in
every band except band `a`, where that column piece belongs to square `(a,c)`.
Above and below band `a` it forms two *column halves*, whose position `0` is
next to band `a`. Everything else (row offsets `≥ k` and column offsets `≥ k`,
the landing strip and the own column piece) is the *region* of the square.

Everything in this file is plain arithmetic on indices; cells and boards come
in `Hub/Layout.lean`. -/
namespace SlidingPuzzle.Hub

/-- Squares and tile classes: `(band, block column)`. -/
abbrev Sq (k : ℕ) := Fin k × Fin k

/-- Dimensions of the hub layout: `k × k` squares of side `s`, `n = k*s`. `k` is
even so that a column corridor crosses a row group (`k` rows) by an odd jump.
The side is large against `k` (`big`), so that the corner terms of local
three-cycles stay below one unit of `s`. -/
structure HDims (n k s : ℕ) : Prop where
  two_le : 2 ≤ k
  even : Even k
  room : 4 * k + 4 ≤ s
  mul : k * s = n
  big : 600 * k + 2000 ≤ s

/-- Distance between squares in the `k × k` grid. -/
def sqDist {k : ℕ} (P Q : Sq k) : ℕ := Nat.dist P.1.val Q.1.val + Nat.dist P.2.val Q.2.val

/-- The class of the target square of the blank. -/
def IsLast {k : ℕ} (y : Sq k) : Prop := y.1.val = k - 1 ∧ y.2.val = k - 1

instance {k : ℕ} (y : Sq k) : Decidable (IsLast y) := by unfold IsLast; infer_instance

/-- Row halves `(b, c, right)`: the right (`true`) or left half of `R(b,c)`. -/
abbrev RowH (k : ℕ) := Fin k × Fin k × Bool

/-- Column halves `(c, a, lower)`: the part of `C(c,a)` below (`true`) or
above band `a`. -/
abbrev ColH (k : ℕ) := Fin k × Fin k × Bool

/-- Length of a row half: right `(k-1-c)*s` cells, left `c*s` cells. -/
def rowLen (k s : ℕ) (H : RowH k) : ℕ :=
  if H.2.2 then (k - 1 - H.2.1.val) * s else H.2.1.val * s

/-- Length of a column half: `s-k` cells per band passed. -/
def colLen (k s : ℕ) (V : ColH k) : ℕ :=
  if V.2.2 then (k - 1 - V.2.1.val) * (s - k) else V.2.1.val * (s - k)

/-- Insertion position of a hop1 from block distance `d` (number of blocks
strictly between source and hub): the source block's reservoir column farthest
from the hub (column offset `s-1` on right halves, `k` on left halves). -/
def insPos (k s : ℕ) (H : RowH k) (d : ℕ) : ℕ :=
  if H.2.2 then (d + 1) * s - 1 else (d + 1) * s - 1 - k

/-- The row half used by a hop1 from `S` into the hub `h` (same band). -/
def hop1Half {k : ℕ} (S h : Sq k) : RowH k := (h.1, h.2, decide (h.2 < S.2))

/-- Block distance of a hop1. -/
def hop1Dist {k : ℕ} (S h : Sq k) : ℕ := Nat.dist S.2.val h.2.val - 1

/-- Insertion position of a hop1 from `S` into `h`. -/
def hop1Pos {k : ℕ} (s : ℕ) (S h : Sq k) : ℕ := insPos k s (hop1Half S h) (hop1Dist S h)

/-- The column half used by a hop2 from the hub `h` into `D` (same block column). -/
def hop2Half {k : ℕ} (h D : Sq k) : ColH k := (D.2, D.1, decide (D.1 < h.1))

/-- Insertion position of a hop2: the first cell in the hub's band. -/
def hop2Pos {k : ℕ} (s : ℕ) (h D : Sq k) : ℕ := (Nat.dist h.1.val D.1.val - 1) * (s - k)

/-- Cells of a square outside its region: `(k-1)` corridor rows of length `s`
and `(k-1)` corridor columns of length `s-k`. -/
def sqCorridor (k s : ℕ) : ℕ := (k - 1) * s + (k - 1) * (s - k)

/-- Cells of the region of a square. -/
def regionSize (k s : ℕ) : ℕ := s ^ 2 - sqCorridor k s

/-- Insert `v` at position `p`: positions `1..p` move one step toward position
`0`, the old position `0` leaves, positions beyond `p` stay. -/
def shiftIn {α : Type*} (f : ℕ → α) (p : ℕ) (v : α) : ℕ → α :=
  fun q => if q < p then f (q + 1) else if q = p then v else f q

end SlidingPuzzle.Hub
