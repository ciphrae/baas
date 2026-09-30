import SlidingPuzzle.Port.Layout
import SlidingPuzzle.Tree.RunDefs

/-! # The abstract state with ports, and its events

`PState` refines the tree abstraction: besides the lane contents and the region
counts `cnt` of every square (ports included), it records the exact class counts
`pc Q pt` of every port and the port `bp` of the blank's square that holds the
blank (the blank is always parked in a port box).

Events:
* `hop l J y m`: the blank walks from the port of lane `l` in its landing square
  along the lane to the insertion position of block `J` (the lane head drops into
  that port) and inserts a class-`y` tile. With `m = cheap` the tile comes from the
  source's port of `l`; with `m = imp p z` it comes from part `p` of the source,
  and a class-`z` tile of the port goes to part `p` in exchange. The blank ends in
  the source's port of `l`.
* `xfer pt c`: the blank moves to port `pt` of its square; a class-`c` tile of
  `pt` goes to the blank's former port.
* `leg Z y p z`: the blank moves to the same port of the aligned square `Z`; a
  class-`y` tile from part `p` of `Z` goes to the blank's former port, and, unless
  `p` is that port, a class-`z` tile of `Z`'s port goes to part `p`. -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle.Hub (Sq shiftIn incCnt decCnt sqDist)
open SlidingPuzzle.Tree

variable {k q : ℕ}

/-! ## Insertion positions and the port of a lane -/

/-- Insertion position of a column hop from band `I`: row offset `s - 1` of that band
(lanes after the landing band) or `k` (before it), the row where the heads of the
lanes of that side land. -/
def colPosP (k s q : ℕ) (V : LaneI k q) (I : Fin k) : ℕ :=
  LaneSys.pdist V.t.val I.val * (s - q) + (if V.side then s - 1 - q else s - 1 - k)

/-- Offset of the insertion position inside its block. -/
def loffP (k s : ℕ) (l : Ln k q) : ℕ :=
  if l.1 then (if l.2.side then s - 1 - q else s - 1 - k) else (if l.2.side then s - 1 else s - 1 - k)

/-- Insertion position of a hop from block (or band) `J`. -/
def lposP (k s : ℕ) (l : Ln k q) (J : Fin k) : ℕ :=
  if l.1 then colPosP k s q l.2 J else rowPos k s l.2 J

theorem lposP_eq (k s : ℕ) (l : Ln k q) (J : Fin k) :
    lposP k s l J = LaneSys.pdist l.2.t.val J.val * lstep s l + loffP k s l := by
  unfold lposP lstep loffP colPosP rowPos
  split_ifs <;> rfl

/-- The port where the heads of lane `l` land and from which its gateways insert. -/
def lport (l : Ln k q) : Pt :=
  if l.1 then (if l.2.side then .bl else .tl) else (if l.2.side then .tr else .tl)

/-! ## The state -/

/-- Insertion mode of a hop. -/
inductive Mode (k : ℕ) where
  | cheap
  | imp (p : Part) (z : Sq k)
  deriving DecidableEq

/-- The abstraction of a board with ports. -/
structure PState (k q : ℕ) where
  row : LaneI k q → ℕ → Sq k
  col : LaneI k q → ℕ → Sq k
  cnt : Sq k → Sq k → ℕ
  pc : Sq k → Pt → Sq k → ℕ
  blank : Sq k
  bp : Pt

/-- Resolved operations. -/
inductive PEvent (k q : ℕ) where
  | hop (l : Ln k q) (J : Fin k) (y : Sq k) (m : Mode k)
  | xfer (pt : Pt) (c : Sq k)
  | leg (Z y : Sq k) (p : Part) (z : Sq k)

/-- Add one to a port count. -/
def incP (f : Sq k → Pt → Sq k → ℕ) (Q : Sq k) (pt : Pt) (z : Sq k) : Sq k → Pt → Sq k → ℕ :=
  fun Q' pt' z' => f Q' pt' z' + (if Q' = Q ∧ pt' = pt ∧ z' = z then 1 else 0)

/-- Remove one from a port count. -/
def decP (f : Sq k → Pt → Sq k → ℕ) (Q : Sq k) (pt : Pt) (z : Sq k) : Sq k → Pt → Sq k → ℕ :=
  fun Q' pt' z' => f Q' pt' z' - (if Q' = Q ∧ pt' = pt ∧ z' = z then 1 else 0)

namespace PState

variable (L : LaneSys k q)

/-- The content of a lane of either axis. -/
def lane (σ : PState k q) (l : Ln k q) : ℕ → Sq k := if l.1 then σ.col l.2 else σ.row l.2

/-- Class-`y` tiles in the main part of `Q`'s region. -/
def mcnt (σ : PState k q) (Q y : Sq k) : ℕ := σ.cnt Q y - ∑ pt, σ.pc Q pt y

/-- Class-`y` tiles in part `p` of `Q`. -/
def partCnt (σ : PState k q) (Q : Sq k) : Part → Sq k → ℕ
  | none, y => σ.mcnt Q y
  | some pt, y => σ.pc Q pt y

/-- The insertion mode can be carried out: the tile, and the tile given in exchange. -/
def ModeOK (σ : PState k q) (S : Sq k) (pt : Pt) (y : Sq k) : Mode k → Prop
  | .cheap => 1 ≤ σ.pc S pt y
  | .imp p z => p ≠ some pt ∧ 1 ≤ σ.partCnt S p y ∧ 1 ≤ σ.pc S pt z

/-- Port counts after the source's side of a hop. -/
def srcPc (f : Sq k → Pt → Sq k → ℕ) (S : Sq k) (pt : Pt) (y : Sq k) :
    Mode k → Sq k → Pt → Sq k → ℕ
  | .cheap => decP f S pt y
  | .imp none z => decP f S pt z
  | .imp (some p) z => decP (incP (decP f S p y) S p z) S pt z

/-- Port counts after the far side of a leg: `y` leaves part `p` of `Z`, and unless `p` is
the port `b`, `z` goes from port `b` to part `p`. -/
def legPc (f : Sq k → Pt → Sq k → ℕ) (Z : Sq k) (b : Pt) (y : Sq k) :
    Part → Sq k → Sq k → Pt → Sq k → ℕ
  | none, z => decP f Z b z
  | some p, z => if p = b then decP f Z b y else decP (incP (decP f Z p y) Z p z) Z b z

/-- Preconditions. -/
def Pre (σ : PState k q) : PEvent k q → Prop
  | .hop l J y m => σ.blank = land l ∧ σ.bp = lport l ∧ LIn L l.2 J ∧
      σ.ModeOK (src l J) (lport l) y m
  | .xfer pt c => σ.bp ≠ pt ∧ (σ.bp = .tl ∨ pt = .tl) ∧ 1 ≤ σ.pc σ.blank pt c
  | .leg Z y p z => σ.blank ≠ Z ∧ (σ.blank.1 = Z.1 ∨ σ.blank.2 = Z.2) ∧
      1 ≤ σ.partCnt Z p y ∧ (p ≠ some σ.bp → 1 ≤ σ.pc Z σ.bp z)

/-- Effects. -/
def step (s : ℕ) (σ : PState k q) : PEvent k q → PState k q
  | .hop l J y m =>
    { row := if l.1 then σ.row else Function.update σ.row l.2 (shiftIn (σ.row l.2) (lposP k s l J) y)
      col := if l.1 then Function.update σ.col l.2 (shiftIn (σ.col l.2) (lposP k s l J) y) else σ.col
      cnt := incCnt (decCnt σ.cnt (src l J) y) (land l) (σ.lane l 0)
      pc := srcPc (incP σ.pc (land l) (lport l) (σ.lane l 0)) (src l J) (lport l) y m
      blank := src l J
      bp := lport l }
  | .xfer pt c =>
    { σ with pc := incP (decP σ.pc σ.blank pt c) σ.blank σ.bp c, bp := pt }
  | .leg Z y p z =>
    { σ with
      cnt := incCnt (decCnt σ.cnt Z y) σ.blank y
      pc := legPc (incP σ.pc σ.blank σ.bp y) Z σ.bp y p z
      blank := Z }

/-- Junk positions `0..p` of a lane. -/
def ljunk (σ : PState k q) (l : Ln k q) (p : ℕ) : ℕ :=
  ((range (p + 1)).filter fun r => ¬ lgood l (σ.lane l r)).card

/-- The junk potential. -/
def pot (s : ℕ) (σ : PState k q) : ℕ :=
  ∑ l : Ln k q, ∑ r ∈ (range (llen L s l)).filter (fun r => ¬ lgood l (σ.lane l r)), (r + 1)

end PState

/-! ## Budgets -/

/-- The fixed part of a cheap hop: landing from the port, insertion by a three-cycle in the
port's corner. -/
def hopKc (k σ : ℕ) : ℕ := 12 * σ + 526 * k + 1535

/-- The crossings of row groups by a hop along `l` from block `J`: per block travelled. -/
def crossK (q : ℕ) (l : Ln k q) (J : Fin k) : ℕ := 7 * (q + 2) * LaneSys.pdist l.2.t.val J.val

/-- The extra part of an importing hop: a three-cycle in the whole square. -/
def hopKi (k s σ : ℕ) : ℕ := 10 * s + 10 * σ + 882 * k + 2500

/-- A transfer between two ports of a square. -/
def xferK (k s σ : ℕ) : ℕ := 21 * (s + 1) + 12 * σ + 600 * k + 2000

/-- A leg between aligned squares at distance `d`. -/
def legK (k s σ d : ℕ) : ℕ := 21 * (d * s + 5) + 10 * s + 12 * σ + 1200 * k + 6000

namespace PState

/-- Inefficiency budgets. -/
def cost (s σ' : ℕ) (σ : PState k q) : PEvent k q → ℕ
  | .hop l J _ m => hopKc k σ' + crossK q l J + σ.ljunk l (lposP k s l J) +
      (match m with | .cheap => 0 | .imp _ _ => hopKi k s σ')
  | .xfer _ _ => xferK k s σ'
  | .leg Z _ _ _ => legK k s σ' (sqDist σ.blank Z)

variable (L : LaneSys k q)

def run (s : ℕ) : PState k q → List (PEvent k q) → PState k q
  | σ, [] => σ
  | σ, e :: es => run s (σ.step s e) es

def Valid (s : ℕ) : PState k q → List (PEvent k q) → Prop
  | _, [] => True
  | σ, e :: es => σ.Pre L e ∧ Valid s (σ.step s e) es

def totalCost (s σ' : ℕ) : PState k q → List (PEvent k q) → ℕ
  | _, [] => 0
  | σ, e :: es => σ.cost s σ' e + totalCost s σ' (σ.step s e) es

theorem run_append (s : ℕ) (σ : PState k q) (l₁ l₂ : List (PEvent k q)) :
    run s σ (l₁ ++ l₂) = run s (run s σ l₁) l₂ := by
  induction l₁ generalizing σ with
  | nil => rfl
  | cons e es ih => exact ih _

theorem valid_append (s : ℕ) (σ : PState k q) (l₁ l₂ : List (PEvent k q)) :
    Valid L s σ (l₁ ++ l₂) ↔ Valid L s σ l₁ ∧ Valid L s (run s σ l₁) l₂ := by
  induction l₁ generalizing σ with
  | nil => simp [Valid, run]
  | cons e es ih =>
    simp only [List.cons_append, Valid, run, ih]
    tauto

theorem totalCost_append (s σ' : ℕ) (σ : PState k q) (l₁ l₂ : List (PEvent k q)) :
    totalCost s σ' σ (l₁ ++ l₂) = totalCost s σ' σ l₁ + totalCost s σ' (run s σ l₁) l₂ := by
  induction l₁ generalizing σ with
  | nil => simp [totalCost, run]
  | cons e es ih =>
    simp only [List.cons_append, totalCost, run, ih]
    ring

/-- Region tiles outside their own square. -/
def offCount (σ : PState k q) : ℕ :=
  ∑ Q : Sq k, ∑ y : Sq k, if y = Q then 0 else σ.cnt Q y

end PState

end SlidingPuzzle.Port
