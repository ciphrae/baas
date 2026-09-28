import SlidingPuzzle.Tree.Basic
import SlidingPuzzle.Hub.PrimRes

/-! # The tree layout on boards

Row lane `H` (band `H.b`): row `H.b*s + H.o`; position `p` is column
`(t+1)*s + p` (`side`) or `t*s - 1 - p`. Column lane `V` (block column `V.b`):
column `V.b*s + V.o`, `m = s - q` cells per band at row offsets `q, …, s-1`.
A cell of the square `Q` is a *lane cell* if its row offset `ro < q` is the
offset of a piece covering its block column, or `ro ≥ q` and its column offset
`co < q` is the offset of a piece covering its band. All other cells form the
*region* of `Q`; in particular the reservoir (offsets `≥ k`), the landing
strips and the own column pieces. -/
namespace SlidingPuzzle.Tree

open SlidingPuzzle.Hub (Sq HDims sqOf classOf mkCell reservoir misplaced)
open SlidingPuzzle.Hub.LayoutAux

variable {n k s q : ℕ}

section defs

variable (L : LaneSys k q)

/-- Block `J` is covered by a piece of offset `o`. -/
def Covered (o : Fin q) (J : ℕ) : Prop := ∃ t : Fin k, ∃ side : Bool, InPiece (L.len o t side) t side J

open Classical in
noncomputable instance (o : Fin q) (J : ℕ) : Decidable (Covered L o J) := inferInstance

/-- The cell is a lane cell. -/
def LaneCell (s : ℕ) (x : Cell n) : Prop :=
  (∃ h : x.1.val % s < q, Covered L ⟨_, h⟩ (x.2.val / s)) ∨
    (q ≤ x.1.val % s ∧ ∃ h : x.2.val % s < q, Covered L ⟨_, h⟩ (x.1.val / s))

/-- The region of `Q`: its cells that are not lane cells. -/
def region (s : ℕ) (Q : Sq k) (x : Cell n) : Prop :=
  x.1.val / s = Q.1.val ∧ x.2.val / s = Q.2.val ∧ ¬ LaneCell L s x

open Classical in
noncomputable instance (s : ℕ) (x : Cell n) : Decidable (LaneCell L s x) := inferInstance

open Classical in
noncomputable instance (s : ℕ) (Q : Sq k) (x : Cell n) : Decidable (region L s Q x) :=
  inferInstance

/-- Position `p` of a row lane. -/
def rowCell (s : ℕ) [NeZero n] (H : LaneI k q) (p : ℕ) : Cell n :=
  mkCell n (H.b.val * s + H.o.val) (if H.side then (H.t.val + 1) * s + p else H.t.val * s - 1 - p)

/-- Band of position `p` of a column lane. -/
def cBand (s q : ℕ) (V : LaneI k q) (p : ℕ) : ℕ :=
  if V.side then V.t.val + 1 + p / (s - q) else V.t.val - 1 - p / (s - q)

/-- Row offset of position `p` of a column lane. -/
def cOff (s q : ℕ) (V : LaneI k q) (p : ℕ) : ℕ :=
  if V.side then q + p % (s - q) else s - 1 - p % (s - q)

/-- Position `p` of a column lane. -/
def colCell (s : ℕ) [NeZero n] (V : LaneI k q) (p : ℕ) : Cell n :=
  mkCell n (cBand s q V p * s + cOff s q V p) (V.b.val * s + V.o.val)

end defs

variable (L : LaneSys k q)

open Classical in
/-- The region containing a cell, if any. -/
noncomputable def key (hd : HDims n k s) (x : Cell n) : Option (Sq k) :=
  if region L s (sqOf hd x) x then some (sqOf hd x) else none

open Classical in
/-- Nonblank tiles of class `y` in the region of `Q`. -/
noncomputable def regionCount (hd : HDims n k s) (B : Board n) (Q y : Sq k) : ℕ :=
  (Finset.univ.filter fun x : Cell n =>
    region L s Q x ∧ (B x).val ≠ 0 ∧ classOf hd (B x) = y).card

/-- A board realizes an `IState`. -/
def Rel (hd : HDims n k s) [NeZero n] (B : Board n) (σ : IState k q) : Prop :=
  (∀ H p, p < rowLen L s H →
    (B (rowCell s H p)).val ≠ 0 ∧ classOf hd (B (rowCell s H p)) = σ.row H p) ∧
  (∀ V p, p < colLen L s V →
    (B (colCell s V p)).val ≠ 0 ∧ classOf hd (B (colCell s V p)) = σ.col V p) ∧
  (∀ Q y, regionCount L hd B Q y = σ.cnt Q y) ∧
  reservoir k s σ.blank (blank B)

/-- The `IState` read off a board. -/
noncomputable def absState (hd : HDims n k s) [NeZero n] (B : Board n) : IState k q where
  row H p := classOf hd (B (rowCell s H p))
  col V p := classOf hd (B (colCell s V p))
  cnt := regionCount L hd B
  blank := sqOf hd (blank B)

end SlidingPuzzle.Tree
