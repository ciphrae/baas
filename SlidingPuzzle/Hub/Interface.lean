import SlidingPuzzle.Hub.Basic

/-! # The interface between the abstract run and the board

An `IState` is what the board-level operations need to know about a board:
the class of the tile at every position of every corridor half, the number of
tiles of every class in every square's region, and the square whose reservoir
holds the blank. Resolved events (`REvent`) are the three board operations:

* `hop1 S h y`: the blank goes from the hub `h` along the row `R(h)` to the
  source square `S` (same band); `S` inserts a class-`y` tile into the row half
  at `hop1Pos`, and the half's position-`0` tile drops into the region of `h`.
* `hop2 h D y`: the blank goes from `D` along the column `C(D)` to the hub `h`
  (same block column); `h` inserts a class-`y` tile into the column half at
  `hop2Pos`, and the half's position-`0` tile drops into the region of `D`.
* `jump E Z y`: the blank goes from `E` to `Z` (same band or block column), and
  a class-`y` tile of `Z` moves to the region of `E`.

`cost` bounds the inefficient moves of each operation. The board side proves
that a valid event list is realized by a path of at most `totalCost`
inefficient moves (`Hub/Simulate.lean`); the abstract side constructs a valid
list with small total cost (`Hub/Run.lean`). -/
namespace SlidingPuzzle.Hub

/-- The abstraction of a board used by the operations. -/
structure IState (k : ℕ) where
  row : RowH k → ℕ → Sq k
  col : ColH k → ℕ → Sq k
  cnt : Sq k → Sq k → ℕ
  blank : Sq k

/-- Resolved operations. -/
inductive REvent (k : ℕ) where
  | hop1 (S h y : Sq k)
  | hop2 (h D y : Sq k)
  | jump (E Z y : Sq k)
  deriving DecidableEq

/-- Add one tile of class `y` to the region of `Q`. -/
def incCnt {k : ℕ} (c : Sq k → Sq k → ℕ) (Q y : Sq k) : Sq k → Sq k → ℕ :=
  fun Q' y' => if Q' = Q ∧ y' = y then c Q' y' + 1 else c Q' y'

/-- Remove one tile of class `y` from the region of `Q`. -/
def decCnt {k : ℕ} (c : Sq k → Sq k → ℕ) (Q y : Sq k) : Sq k → Sq k → ℕ :=
  fun Q' y' => if Q' = Q ∧ y' = y then c Q' y' - 1 else c Q' y'

namespace IState

variable {k : ℕ}

/-- Preconditions of the operations. -/
def Pre (σ : IState k) : REvent k → Prop
  | .hop1 S h y => σ.blank = h ∧ S.1 = h.1 ∧ S.2 ≠ h.2 ∧ 1 ≤ σ.cnt S y
  | .hop2 h D y => σ.blank = D ∧ h.2 = D.2 ∧ h.1 ≠ D.1 ∧ 1 ≤ σ.cnt h y
  | .jump E Z y => σ.blank = E ∧ E ≠ Z ∧ (E.1 = Z.1 ∨ E.2 = Z.2) ∧ 1 ≤ σ.cnt Z y

/-- Effect of the operations. -/
def step (s : ℕ) (σ : IState k) : REvent k → IState k
  | .hop1 S h y =>
    { row := Function.update σ.row (hop1Half S h)
        (shiftIn (σ.row (hop1Half S h)) (hop1Pos s S h) y)
      col := σ.col
      cnt := incCnt (decCnt σ.cnt S y) h (σ.row (hop1Half S h) 0)
      blank := S }
  | .hop2 h D y =>
    { row := σ.row
      col := Function.update σ.col (hop2Half h D)
        (shiftIn (σ.col (hop2Half h D)) (hop2Pos s h D) y)
      cnt := incCnt (decCnt σ.cnt h y) D (σ.col (hop2Half h D) 0)
      blank := h }
  | .jump E Z y =>
    { row := σ.row
      col := σ.col
      cnt := incCnt (decCnt σ.cnt Z y) E y
      blank := Z }

/-- Positions `0..p` of a row half holding a tile of another target block column. -/
def junkRow (σ : IState k) (H : RowH k) (p : ℕ) : ℕ :=
  ((Finset.range (p + 1)).filter fun q => (σ.row H q).2 ≠ H.2.1).card

/-- Positions `0..p` of a column half holding a tile of another class. -/
def junkCol (σ : IState k) (V : ColH k) (p : ℕ) : ℕ :=
  ((Finset.range (p + 1)).filter fun q => σ.col V q ≠ (V.2.1, V.1)).card

/-- Inefficient-move budget of each operation. -/
def cost (s : ℕ) (σ : IState k) : REvent k → ℕ
  | .hop1 S h _ => 288 * s + σ.junkRow (hop1Half S h) (hop1Pos s S h)
  | .hop2 h D _ => 288 * s + 30 * k ^ 2 + σ.junkCol (hop2Half h D) (hop2Pos s h D)
  | .jump E Z _ => 288 * s * (1 + sqDist E Z)

/-- The state after a list of operations. -/
def run (s : ℕ) : IState k → List (REvent k) → IState k
  | σ, [] => σ
  | σ, e :: es => run s (σ.step s e) es

/-- Every operation of the list meets its precondition. -/
def Valid (s : ℕ) : IState k → List (REvent k) → Prop
  | _, [] => True
  | σ, e :: es => σ.Pre e ∧ Valid s (σ.step s e) es

/-- The summed budgets of a list of operations. -/
def totalCost (s : ℕ) : IState k → List (REvent k) → ℕ
  | _, [] => 0
  | σ, e :: es => σ.cost s e + totalCost s (σ.step s e) es

/-- Region tiles outside their own square. -/
def offCount (σ : IState k) : ℕ :=
  ∑ Q : Sq k, ∑ y : Sq k, if y = Q then 0 else σ.cnt Q y

/-- Corridor positions holding class `y`. -/
def corrCount (s : ℕ) (σ : IState k) (y : Sq k) : ℕ :=
  (∑ H : RowH k, ((Finset.range (rowLen k s H)).filter fun q => σ.row H q = y).card) +
  (∑ V : ColH k, ((Finset.range (colLen k s V)).filter fun q => σ.col V q = y).card)

end IState

end SlidingPuzzle.Hub
