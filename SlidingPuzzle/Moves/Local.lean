import SlidingPuzzle.Paths

/-! Single moves as paths, and `Executes`: an explicit list of blank
destinations with its legality, length, and preservation of unvisited cells. -/

namespace SlidingPuzzle

variable {n : ℕ} [NeZero n]

/-- A single legal move as a path with exactly one edge. -/
def Step.toPath {B C : Board n} (h : Step B C) : Path B C := .cons h (.nil _)

@[simp] theorem Step.toPath_length {B C : Board n} (h : Step B C) :
    h.toPath.length = 1 := rfl

/-- Move the blank to the specified adjacent cell. -/
def movePath (B : Board n) (c : Cell n) (h : gridDistance (blank B) c = 1) :
    Path B (swapCells B (blank B) c) :=
  Step.toPath ⟨c, h, rfl⟩

@[simp] theorem movePath_length (B : Board n) (c : Cell n)
    (h : gridDistance (blank B) c = 1) : (movePath B c h).length = 1 := rfl

omit [NeZero n] in
theorem swapCells_preserves (B : Board n) {a b c : Cell n}
    (ha : c ≠ a) (hb : c ≠ b) : swapCells B a b c = B c := by
  simp [Equiv.swap_apply_of_ne_of_ne ha hb]

omit [NeZero n] in
@[simp] theorem swapCells_at_left (B : Board n) (a b : Cell n) :
    swapCells B a b a = B b := by simp

omit [NeZero n] in
@[simp] theorem swapCells_at_right (B : Board n) (a b : Cell n) :
    swapCells B a b b = B a := by simp

/-- A list of successive blank destinations is executable if each move is adjacent. -/
inductive Executes : Board n → List (Cell n) → Board n → Prop
  | nil (B : Board n) : Executes B [] B
  | cons {B C : Board n} {c : Cell n} {cs : List (Cell n)}
      (adjacent : gridDistance (blank B) c = 1)
      (rest : Executes (swapCells B (blank B) c) cs C) : Executes B (c :: cs) C

namespace Executes

/-- Every executable word has a legal path of precisely the word's length. -/
theorem exists_path {B C : Board n} {cs : List (Cell n)} (h : Executes B cs C) :
    ∃ p : Path B C, p.length = cs.length := by
  induction h with
  | nil B => exact ⟨.nil B, rfl⟩
  | @cons B C c cs adj rest ih =>
      obtain ⟨p, hp⟩ := ih
      exact ⟨.cons ⟨c, adj, rfl⟩ p, by change p.length + 1 = cs.length + 1; rw [hp]⟩

/-- Protected cells are unaffected by a word which never visits them. -/
theorem preserves {B C : Board n} {cs : List (Cell n)} (h : Executes B cs C)
    {x : Cell n} (hblank : x ≠ blank B) (hword : x ∉ cs) : C x = B x := by
  induction h with
  | nil => rfl
  | @cons B C c cs adj rest ih =>
      have hc : x ≠ c := by intro heq; apply hword; simp [heq]
      have ht : x ∉ cs := by intro hm; apply hword; simp [hm]
      rw [ih (by simpa using hc) ht]
      exact swapCells_preserves B hblank hc

/-- Consecutive words concatenate without changing their move count. -/
theorem append {A B C : Board n} {xs ys : List (Cell n)}
    (h : Executes A xs B) (k : Executes B ys C) : Executes A (xs ++ ys) C := by
  induction h with
  | nil => exact k
  | cons adj rest ih => exact .cons adj (ih k)

end Executes

end SlidingPuzzle
