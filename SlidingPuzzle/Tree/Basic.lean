import SlidingPuzzle.Tree.LaneSys
import SlidingPuzzle.Hub.Interface

/-! # Tree lanes: indices and the abstract interface

The board of side `n = k*s` is cut into `k × k` squares as in `Hub`. A lane
system `L : LaneSys k q` is used on both axes. In band `b` the row offset
`o < q` carries the *row lanes* `(b, o, t, side)`: the piece of offset `o`
landing at block column `t`, a truncated `Hub` row half. In block column `c`
the column offset `o < q` (row offsets `≥ q`) carries the *column lanes*
`(c, o, t, side)` landing at band `t`. Position `0` of a lane is next to its
landing block.

An `IState` records the class at every lane position, the class counts of every
region and the square of the blank; `REvent` has the three operations `hopR`,
`hopC`, `jump`. -/
namespace SlidingPuzzle.Tree

open SlidingPuzzle.Hub (Sq HDims sqDist shiftIn incCnt decCnt IsLast)

/-- A lane: `b` is the band (row lanes) or the block column (column lanes), `o`
the offset, `t` the landing block, `side` whether the lane lies after `t`. -/
structure LaneI (k q : ℕ) where
  b : Fin k
  o : Fin q
  t : Fin k
  side : Bool
  deriving DecidableEq, Fintype

variable {k q : ℕ}

/-- Dimensions: the `Hub` dimensions (squares, reservoirs at offsets `≥ k`) and
`q ≤ k` lane offsets, `q` even so that crossing a row group of `q` rows is an odd
jump. -/
structure TDims (n k s q : ℕ) : Prop where
  hd : HDims n k s
  two_le_q : 2 ≤ q
  even_q : Even q
  q_le : q ≤ k

/-- Blocks of a lane. -/
def blen (L : LaneSys k q) (H : LaneI k q) : ℕ := L.len H.o H.t H.side

/-- Length of a row lane: `s` cells per block. -/
def rowLen (L : LaneSys k q) (s : ℕ) (H : LaneI k q) : ℕ := blen L H * s

/-- Length of a column lane: `s - q` cells per band. -/
def colLen (L : LaneSys k q) (s : ℕ) (V : LaneI k q) : ℕ := blen L V * (s - q)

/-- The lane of `L`'s pieces contains block `J`. -/
def LIn (L : LaneSys k q) (H : LaneI k q) (J : Fin k) : Prop :=
  InPiece (blen L H) H.t.val H.side J.val

instance (L : LaneSys k q) (H : LaneI k q) (J : Fin k) : Decidable (LIn L H J) := by
  unfold LIn; infer_instance

/-- Insertion position of a row hop from block `J`: the block's column farthest
from the landing block (offset `s - 1` after `t`, `k` before it). -/
def rowPos (k s : ℕ) (H : LaneI k q) (J : Fin k) : ℕ :=
  LaneSys.pdist H.t.val J.val * s + (if H.side then s - 1 else s - 1 - k)

/-- Insertion position of a column hop from band `I`: the cell of that band at
row offset `k` (after `t`) or `s - 1` (before it). -/
def colPos (k s q : ℕ) (V : LaneI k q) (I : Fin k) : ℕ :=
  LaneSys.pdist V.t.val I.val * (s - q) + (if V.side then k - q else 0)

/-- The abstraction of a board. -/
structure IState (k q : ℕ) where
  row : LaneI k q → ℕ → Sq k
  col : LaneI k q → ℕ → Sq k
  cnt : Sq k → Sq k → ℕ
  blank : Sq k

/-- Resolved operations. -/
inductive REvent (k q : ℕ) where
  | hopR (H : LaneI k q) (J : Fin k) (y : Sq k)
  | hopC (V : LaneI k q) (I : Fin k) (y : Sq k)
  | jump (E Z y : Sq k)
  deriving DecidableEq

/-- Landing square of a row lane. -/
def rowLand (H : LaneI k q) : Sq k := (H.b, H.t)

/-- Landing square of a column lane. -/
def colLand (V : LaneI k q) : Sq k := (V.t, V.b)

/-- A tile of class `z` on row lane `H` moves toward its target block column. -/
def rowGood (H : LaneI k q) (z : Sq k) : Prop :=
  if H.side then z.2 ≤ H.t else H.t ≤ z.2

instance (H : LaneI k q) (z : Sq k) : Decidable (rowGood H z) := by
  unfold rowGood; split <;> infer_instance

/-- A tile of class `z` on column lane `V` moves toward its target band. -/
def colGood (V : LaneI k q) (z : Sq k) : Prop :=
  if V.side then z.1 ≤ V.t else V.t ≤ z.1

instance (V : LaneI k q) (z : Sq k) : Decidable (colGood V z) := by
  unfold colGood; split <;> infer_instance

namespace IState

variable (L : LaneSys k q)

/-- Preconditions. -/
def Pre (σ : IState k q) : REvent k q → Prop
  | .hopR H J y => σ.blank = rowLand H ∧ LIn L H J ∧ 1 ≤ σ.cnt (H.b, J) y
  | .hopC V I y => σ.blank = colLand V ∧ LIn L V I ∧ 1 ≤ σ.cnt (I, V.b) y
  | .jump E Z y => σ.blank = E ∧ E ≠ Z ∧ (E.1 = Z.1 ∨ E.2 = Z.2) ∧ 1 ≤ σ.cnt Z y

/-- Effects. -/
def step (s : ℕ) (σ : IState k q) : REvent k q → IState k q
  | .hopR H J y =>
    { row := Function.update σ.row H (shiftIn (σ.row H) (rowPos k s H J) y)
      col := σ.col
      cnt := incCnt (decCnt σ.cnt (H.b, J) y) (rowLand H) (σ.row H 0)
      blank := (H.b, J) }
  | .hopC V I y =>
    { row := σ.row
      col := Function.update σ.col V (shiftIn (σ.col V) (colPos k s q V I) y)
      cnt := incCnt (decCnt σ.cnt (I, V.b) y) (colLand V) (σ.col V 0)
      blank := (I, V.b) }
  | .jump E Z y =>
    { row := σ.row
      col := σ.col
      cnt := incCnt (decCnt σ.cnt Z y) E y
      blank := Z }

/-- Positions `0..p` of a row lane holding a tile that does not move toward its
target. -/
def junkRow (σ : IState k q) (H : LaneI k q) (p : ℕ) : ℕ :=
  ((Finset.range (p + 1)).filter fun r => ¬ rowGood H (σ.row H r)).card

/-- Positions `0..p` of a column lane holding a tile that does not move toward
its target. -/
def junkCol (σ : IState k q) (V : LaneI k q) (p : ℕ) : ℕ :=
  ((Finset.range (p + 1)).filter fun r => ¬ colGood V (σ.col V r)).card

/-- Inefficiency budgets. -/
def cost (s : ℕ) (σ : IState k q) : REvent k q → ℕ
  | .hopR H J _ => 20 * s + 600 * k + 2000 + σ.junkRow H (rowPos k s H J)
  | .hopC V I _ => 20 * s + 20 * k * (q + 2) + 600 * k + 2000 + σ.junkCol V (colPos k s q V I)
  | .jump E Z _ => (s + 3) * (13 + 21 * sqDist E Z)

def run (s : ℕ) : IState k q → List (REvent k q) → IState k q
  | σ, [] => σ
  | σ, e :: es => run s (σ.step s e) es

def Valid (s : ℕ) : IState k q → List (REvent k q) → Prop
  | _, [] => True
  | σ, e :: es => σ.Pre L e ∧ Valid s (σ.step s e) es

def totalCost (s : ℕ) : IState k q → List (REvent k q) → ℕ
  | _, [] => 0
  | σ, e :: es => σ.cost s e + totalCost s (σ.step s e) es

/-- Region tiles outside their own square. -/
def offCount (σ : IState k q) : ℕ :=
  ∑ Q : Sq k, ∑ y : Sq k, if y = Q then 0 else σ.cnt Q y

/-- Lane positions holding class `y`. -/
def corrCount (s : ℕ) (σ : IState k q) (y : Sq k) : ℕ :=
  (∑ H, ((Finset.range (rowLen L s H)).filter fun r => σ.row H r = y).card) +
  (∑ V, ((Finset.range (colLen L s V)).filter fun r => σ.col V r = y).card)

end IState

end SlidingPuzzle.Tree
