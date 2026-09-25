import SlidingPuzzle.Moves.Carry
import SlidingPuzzle.Moves.Efficiency

/-! Blank words on an abstract strip `ℕ × ℕ` (row, column), and their transfer
to boards. A word is described by its `trace`: the cell each position's content
came from. Traces are computed by case analysis on natural numbers; embedding
the strip isometrically into a board turns them into exact board effects and
bounds on the Manhattan potential. -/
namespace SlidingPuzzle

/-- A strip parametrization: `col` is isometric on `0..N`. -/
def StripCol {n : ℕ} (col : ℕ → Fin n) (N : ℕ) : Prop :=
  ∀ a b, a ≤ N → b ≤ N → Nat.dist (col a).val (col b).val = Nat.dist a b

namespace Strip

abbrev SCell := ℕ × ℕ

/-- The distance between strip cells. -/
def sdist (p q : SCell) : ℕ := Nat.dist p.1 q.1 + Nat.dist p.2 q.2

/-- The transposition of two strip cells. -/
def swap (p q x : SCell) : SCell := if x = p then q else if x = q then p else x

/-- After the blank, starting at `b`, visits `w`, the content of `x` came from
`trace b w x`. -/
def trace : SCell → List SCell → SCell → SCell
  | _, [], x => x
  | b, c :: cs, x => swap b c (trace c cs x)

/-- The blank's final cell. -/
def last : SCell → List SCell → SCell
  | b, [] => b
  | _, c :: cs => last c cs

/-- Every move of the word is to an adjacent cell. -/
def Walk : SCell → List SCell → Prop
  | _, [] => True
  | b, c :: cs => sdist b c = 1 ∧ Walk c cs

theorem trace_append (b : SCell) (xs ys : List SCell) (x : SCell) :
    trace b (xs ++ ys) x = trace b xs (trace (last b xs) ys x) := by
  induction xs generalizing b with
  | nil => rfl
  | cons c cs ih => simp [trace, last, ih]

theorem last_append (b : SCell) (xs ys : List SCell) :
    last b (xs ++ ys) = last (last b xs) ys := by
  induction xs generalizing b with
  | nil => rfl
  | cons c cs ih => simp [last, ih]

theorem walk_append (b : SCell) (xs ys : List SCell) :
    Walk b (xs ++ ys) ↔ Walk b xs ∧ Walk (last b xs) ys := by
  induction xs generalizing b with
  | nil => simp [Walk, last]
  | cons c cs ih => simp [Walk, last, ih, and_assoc]

/-- A cell the word never visits keeps its content. -/
theorem trace_of_not_mem (b : SCell) (w : List SCell) (x : SCell) (hb : x ≠ b)
    (hw : x ∉ w) : trace b w x = x := by
  induction w generalizing b with
  | nil => rfl
  | cons c cs ih =>
    have hc : x ≠ c := fun h => hw (h ▸ List.mem_cons_self ..)
    simp only [trace]
    rw [ih c hc (fun h => hw (List.mem_cons_of_mem _ h))]
    simp [swap, hb, hc]

/-- The cells with row at most `R` and column at most `N`. -/
def region (R N : ℕ) (p : SCell) : Prop := p.1 ≤ R ∧ p.2 ≤ N

theorem swap_mem_region {R N : ℕ} {p q x : SCell} (hp : region R N p) (hq : region R N q)
    (hx : region R N x) : region R N (swap p q x) := by
  unfold swap; split_ifs <;> assumption

theorem trace_mem_region {R N : ℕ} (b : SCell) (w : List SCell) (hb : region R N b)
    (hw : ∀ c ∈ w, region R N c) (x : SCell) (hx : region R N x) :
    region R N (trace b w x) := by
  induction w generalizing b with
  | nil => exact hx
  | cons c cs ih =>
    have hc := hw c List.mem_cons_self
    exact swap_mem_region hb hc (ih c hc (fun d hd => hw d (List.mem_cons_of_mem _ hd)))

section Board
variable {n : ℕ}

/-- The embedding of the strip into a board, by row and column parametrizations. -/
def emb (row col : ℕ → Fin n) (p : SCell) : Cell n := (row p.1, col p.2)

variable {row col : ℕ → Fin n} {R N : ℕ}

theorem emb_dist (hrow : StripCol row R) (hcol : StripCol col N) {p q : SCell}
    (hp : region R N p) (hq : region R N q) :
    gridDistance (emb row col p) (emb row col q) = sdist p q := by
  simp only [gridDistance, emb, sdist, hrow p.1 q.1 hp.1 hq.1, hcol p.2 q.2 hp.2 hq.2]

theorem emb_inj (hrow : StripCol row R) (hcol : StripCol col N) {p q : SCell}
    (hp : region R N p) (hq : region R N q) (h : emb row col p = emb row col q) : p = q := by
  have hd := emb_dist hrow hcol hp hq
  rw [h, gridDistance_self] at hd
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  simp only [sdist, Nat.dist] at hd
  simp only [Prod.mk.injEq]; omega

theorem emb_swap (hrow : StripCol row R) (hcol : StripCol col N) {p q x : SCell}
    (hp : region R N p) (hq : region R N q) (hx : region R N x) :
    Equiv.swap (emb row col p) (emb row col q) (emb row col x) = emb row col (swap p q x) := by
  have inj := fun {u v : SCell} (hu : region R N u) (hv : region R N v) =>
    (emb_inj hrow hcol hu hv : emb row col u = emb row col v → u = v)
  unfold swap
  by_cases h1 : x = p
  · subst h1; simp
  by_cases h2 : x = q
  · subst h2; simp [h1]
  rw [if_neg h1, if_neg h2, Equiv.swap_apply_of_ne_of_ne (fun h => h1 (inj hx hp h))
    (fun h => h2 (inj hx hq h))]

variable [NeZero n]

/-- A strip word executes on the board, with the effect given by its trace. -/
theorem exists_executes_trace (hrow : StripCol row R) (hcol : StripCol col N)
    (b : SCell) (w : List SCell) (hb : region R N b) (hw : ∀ c ∈ w, region R N c)
    (hwalk : Walk b w) (X : Board n) (hX : blank X = emb row col b) :
    ∃ Y : Board n, Executes X (w.map (emb row col)) Y ∧
      ∀ q, region R N q → Y (emb row col q) = X (emb row col (trace b w q)) := by
  induction w generalizing b X with
  | nil => exact ⟨X, .nil X, fun q _ => rfl⟩
  | cons c cs ih =>
    have hc := hw c List.mem_cons_self
    have hcs : ∀ d ∈ cs, region R N d := fun d hd => hw d (List.mem_cons_of_mem _ hd)
    have hadj : gridDistance (blank X) (emb row col c) = 1 := by
      rw [hX, emb_dist hrow hcol hb hc]; exact hwalk.1
    obtain ⟨Y, hE, hY⟩ := ih c hc hcs hwalk.2 (swapCells X (blank X) (emb row col c))
      (blank_swapCells X _)
    refine ⟨Y, .cons hadj hE, fun q hq => ?_⟩
    rw [hY q hq]
    simp only [swapCells_apply, hX, trace]
    rw [emb_swap hrow hcol hb hc (trace_mem_region c cs hc hcs q hq)]

/-- The potential rises by at most the total displacement of the trace. -/
theorem manhattan_le_trace (hrow : StripCol row R) (hcol : StripCol col N)
    (b : SCell) (w : List SCell) (hb : region R N b) (hw : ∀ c ∈ w, region R N c)
    (X Y : Board n) (hX : blank X = emb row col b) (hE : Executes X (w.map (emb row col)) Y)
    (hY : ∀ q, region R N q → Y (emb row col q) = X (emb row col (trace b w q))) :
    manhattan Y ≤ manhattan X+
      ∑ q ∈ Finset.range (R+1) ×ˢ Finset.range (N+1), sdist q (trace b w q) := by
  set S := Finset.range (R+1) ×ˢ Finset.range (N+1)
  have hS : ∀ q, q ∈ S ↔ region R N q := by
    intro q; simp [S, region]
  have hoff : ∀ x, x ∉ S.image (emb row col) → Y x = X x := by
    intro x hx
    apply hE.preserves
    · rw [hX]; intro h; exact hx (Finset.mem_image.mpr ⟨b, (hS b).mpr hb, h.symm⟩)
    · intro h
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
      exact hx (Finset.mem_image.mpr ⟨c, (hS c).mpr (hw c hc), rfl⟩)
  refine (manhattan_le_of_displacement X Y _ hoff).trans (Nat.add_le_add_left (le_of_eq ?_) _)
  rw [Finset.sum_image (fun p hp q hq h => emb_inj hrow hcol ((hS p).mp hp) ((hS q).mp hq) h)]
  apply Finset.sum_congr rfl
  intro q hq
  have hqr := (hS q).mp hq
  rw [hY q hqr, show position X (X (emb row col (trace b w q))) = emb row col (trace b w q) by
    simp [position]]
  exact emb_dist hrow hcol hqr (trace_mem_region b w hb hw q hqr)

end Board

end Strip
end SlidingPuzzle
