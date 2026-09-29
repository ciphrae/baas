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

`cost` bounds the inefficient moves of each operation. These definitions come
from the hub algorithm (now in git history); the tree algorithm reuses the
squares, classes and counts, with its own operations (`Tree/RunDefs.lean`). -/
namespace SlidingPuzzle.Hub

/-- The abstraction of a board used by the operations. `des Q b` is the class
of the tile on the designated cell `b` of `Q`'s reservoir when it is recorded. -/
structure IState (k : ℕ) where
  row : RowH k → ℕ → Sq k
  col : ColH k → ℕ → Sq k
  cnt : Sq k → Sq k → ℕ
  blank : Sq k
  des : Sq k → Bool → Option (Sq k)

/-- Resolved operations. -/
inductive REvent (k : ℕ) where
  | hop1 (S h y : Sq k)
  | hop2 (h D y : Sq k)
  | jump (E Z y : Sq k)
  | rjump (E Z : Sq k) (a : Bool) (y : Sq k)
  | restore (Z : Sq k) (c : Bool) (y : Sq k)
  deriving DecidableEq

/-- The designated cell of `Z` on which a jump from the designated cell `a` of
`E` lands: the one that makes the jump odd. -/
def landB {k : ℕ} (s : ℕ) (E Z : Sq k) (a : Bool) : Bool :=
  decide (((E.1.val + E.2.val + Z.1.val + Z.2.val) * s + (if a then 1 else 0)) % 2 = 0)

/-- Add one tile of class `y` to the region of `Q`. -/
def incCnt {k : ℕ} (c : Sq k → Sq k → ℕ) (Q y : Sq k) : Sq k → Sq k → ℕ :=
  fun Q' y' => if Q' = Q ∧ y' = y then c Q' y' + 1 else c Q' y'

/-- Remove one tile of class `y` from the region of `Q`. -/
def decCnt {k : ℕ} (c : Sq k → Sq k → ℕ) (Q y : Sq k) : Sq k → Sq k → ℕ :=
  fun Q' y' => if Q' = Q ∧ y' = y then c Q' y' - 1 else c Q' y'

namespace IState

variable {k : ℕ}

/-- Recorded designated tiles of class `y` in `Q`. -/
def dcnt (σ : IState k) (Q y : Sq k) : ℕ :=
  (if σ.des Q false = some y then 1 else 0) + (if σ.des Q true = some y then 1 else 0)

/-- Preconditions of the operations: the moved tile is not a recorded designated
tile; a designated jump lands on a recorded designated tile; a restore fills an
unrecorded designated cell. -/
def Pre (s : ℕ) (σ : IState k) : REvent k → Prop
  | .hop1 S h y => σ.blank = h ∧ S.1 = h.1 ∧ S.2 ≠ h.2 ∧ σ.dcnt S y + 1 ≤ σ.cnt S y
  | .hop2 h D y => σ.blank = D ∧ h.2 = D.2 ∧ h.1 ≠ D.1 ∧ σ.dcnt h y + 1 ≤ σ.cnt h y
  | .jump E Z y =>
    σ.blank = E ∧ E ≠ Z ∧ (E.1 = Z.1 ∨ E.2 = Z.2) ∧ σ.dcnt Z y + 1 ≤ σ.cnt Z y
  | .rjump E Z a y =>
    σ.blank = E ∧ E ≠ Z ∧ (E.1 = Z.1 ∨ E.2 = Z.2) ∧ σ.des Z (landB s E Z a) = some y
  | .restore Z c y => σ.blank = Z ∧ σ.des Z c = none ∧ σ.dcnt Z y + 1 ≤ σ.cnt Z y

/-- Effect of the operations. -/
def step (s : ℕ) (σ : IState k) : REvent k → IState k
  | .hop1 S h y =>
    { row := Function.update σ.row (hop1Half S h)
        (shiftIn (σ.row (hop1Half S h)) (hop1Pos s S h) y)
      col := σ.col
      cnt := incCnt (decCnt σ.cnt S y) h (σ.row (hop1Half S h) 0)
      blank := S
      des := σ.des }
  | .hop2 h D y =>
    { row := σ.row
      col := Function.update σ.col (hop2Half h D)
        (shiftIn (σ.col (hop2Half h D)) (hop2Pos s h D) y)
      cnt := incCnt (decCnt σ.cnt h y) D (σ.col (hop2Half h D) 0)
      blank := h
      des := σ.des }
  | .jump E Z y =>
    { row := σ.row
      col := σ.col
      cnt := incCnt (decCnt σ.cnt Z y) E y
      blank := Z
      des := σ.des }
  | .rjump E Z a y =>
    { row := σ.row
      col := σ.col
      cnt := incCnt (decCnt σ.cnt Z y) E y
      blank := Z
      des := fun Q c => if Q = Z ∧ c = landB s E Z a then none
        else if Q = E ∧ c = a then some y else σ.des Q c }
  | .restore Z c y =>
    { σ with des := fun Q c' => if Q = Z ∧ c' = c then some y else σ.des Q c' }

/-- The operations other than designated jumps and restores keep the designated
record. -/
def KeepsDes {k : ℕ} : REvent k → Prop
  | .hop1 _ _ _ => True
  | .hop2 _ _ _ => True
  | .jump _ _ _ => True
  | .rjump _ _ _ _ => False
  | .restore _ _ _ => False

theorem des_step (s : ℕ) (σ : IState k) (e : REvent k) (he : KeepsDes e) :
    (σ.step s e).des = σ.des := by
  cases e <;> first | rfl | exact absurd he id

theorem dcnt_step (s : ℕ) (σ : IState k) (e : REvent k) (he : KeepsDes e) :
    (σ.step s e).dcnt = σ.dcnt := by
  unfold dcnt; rw [des_step s σ e he]

/-- At most two recorded designated tiles per square. -/
theorem sum_dcnt_le (σ : IState k) (Q : Sq k) : ∑ y, σ.dcnt Q y ≤ 2 := by
  classical
  unfold dcnt
  rw [Finset.sum_add_distrib]
  have h : ∀ o : Option (Sq k), (∑ y : Sq k, if o = some y then 1 else 0) ≤ 1 := by
    intro o
    cases o with
    | none => simp
    | some z => simp
  have := h (σ.des Q false); have := h (σ.des Q true)
  omega

/-- Positions `0..p` of a row half holding a tile of another target block column. -/
def junkRow (σ : IState k) (H : RowH k) (p : ℕ) : ℕ :=
  ((Finset.range (p + 1)).filter fun q => (σ.row H q).2 ≠ H.2.1).card

/-- Positions `0..p` of a column half holding a tile of another class. -/
def junkCol (σ : IState k) (V : ColH k) (p : ℕ) : ℕ :=
  ((Finset.range (p + 1)).filter fun q => σ.col V q ≠ (V.2.1, V.1)).card

/-- Inefficient-move budget of each operation. -/
def cost (s : ℕ) (σ : IState k) : REvent k → ℕ
  | .hop1 S h _ => 13 * s + 506 * k + 1024 + σ.junkRow (hop1Half S h) (hop1Pos s S h)
  | .hop2 h D _ => 12 * s + 7 * k ^ 2 + 527 * k + 1052 + σ.junkCol (hop2Half h D) (hop2Pos s h D)
  | .jump E Z _ => (s + 3) * (13 + 21 * sqDist E Z)
  | .rjump E Z _ _ => (s + 3) * (3 + 7 * sqDist E Z)
  | .restore _ _ _ => 13 * s

/-- The state after a list of operations. -/
def run (s : ℕ) : IState k → List (REvent k) → IState k
  | σ, [] => σ
  | σ, e :: es => run s (σ.step s e) es

/-- Every operation of the list meets its precondition. -/
def Valid (s : ℕ) : IState k → List (REvent k) → Prop
  | _, [] => True
  | σ, e :: es => σ.Pre s e ∧ Valid s (σ.step s e) es

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
