import SlidingPuzzle.Basic

/-! Legal paths, reachability from the target, and the optimal solution length
`optimalLength` with a shortest witness. -/

namespace SlidingPuzzle

variable {n : ℕ} [NeZero n]

/-- A finite legal walk, with endpoints in its type. -/
inductive Path : Board n → Board n → Type
  | nil (B : Board n) : Path B B
  | cons {A B C : Board n} (step : Step A B) (tail : Path B C) : Path A C

namespace Path

variable {A B C : Board n}

def length {A B : Board n} : Path A B → ℕ
  | .nil _ => 0
  | .cons _ p => p.length + 1

@[simp] theorem length_nil (B : Board n) : (nil B).length = 0 := rfl
@[simp] theorem length_cons {A B C : Board n} (h : Step A B) (p : Path B C) :
    (cons h p).length = p.length + 1 := rfl

def append {A B C : Board n} (p : Path A B) (q : Path B C) : Path A C :=
  match p with
  | .nil _ => q
  | .cons h p => .cons h (p.append q)

@[simp] theorem length_append (p : Path A B) (q : Path B C) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | nil => simp [append]
  | cons h p ih => simp [append, ih, Nat.add_assoc, Nat.add_comm]

def reverse {A B : Board n} (p : Path A B) : Path B A :=
  match p with
  | .nil _ => .nil _
  | .cons h p => p.reverse.append (.cons h.symm (.nil _))

@[simp] theorem length_reverse (p : Path A B) : p.reverse.length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [reverse, ih]

end Path

/-- The orbit is defined by actual paths, not a distance default on disconnected states. -/
def Reachable (B : Board n) : Prop := Nonempty (Path (target n) B)

abbrev ReachableBoard (n : ℕ) [NeZero n] := {B : Board n // Reachable B}

noncomputable instance : Fintype (ReachableBoard n) := Fintype.ofFinite _

def targetBoard (n : ℕ) [NeZero n] : ReachableBoard n := ⟨target n, ⟨Path.nil _⟩⟩

instance : Nonempty (ReachableBoard n) := ⟨targetBoard n⟩

theorem exists_solution (B : ReachableBoard n) : Nonempty (Path B.val (target n)) := by
  obtain ⟨p⟩ := B.property
  exact ⟨p.reverse⟩

private theorem exists_solution_length (B : ReachableBoard n) :
    ∃ k : ℕ, ∃ p : Path B.val (target n), p.length = k := by
  obtain ⟨p⟩ := exists_solution B
  exact ⟨p.length, p, rfl⟩

/-- Minimum length among legal solutions of a reachable board. -/
noncomputable def optimalLength (B : ReachableBoard n) : ℕ :=
  by classical exact Nat.find (exists_solution_length B)

theorem shortest_witness (B : ReachableBoard n) :
    ∃ p : Path B.val (target n), p.length = optimalLength B :=
  by classical exact Nat.find_spec (exists_solution_length B)

theorem optimalLength_le_path_length (B : ReachableBoard n) (p : Path B.val (target n)) :
    optimalLength B ≤ p.length :=
  by classical exact Nat.find_min' (exists_solution_length B) ⟨p, rfl⟩

@[simp] theorem optimalLength_target (n : ℕ) [NeZero n] :
    optimalLength (targetBoard n) = 0 := by
  exact Nat.eq_zero_of_le_zero (optimalLength_le_path_length (targetBoard n) (Path.nil (target n)))

end SlidingPuzzle
