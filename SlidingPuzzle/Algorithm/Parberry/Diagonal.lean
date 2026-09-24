import SlidingPuzzle.Bridge.Words
import Zhong.Algorithm.Parberry

/-! The six-move diagonal primitive in Parberry's reduction-of-order solver.
Coordinates increase downwards and to the right; Zhong's direction names refer
to the tile motion, so `U` moves the blank down and `R` moves it left. -/
namespace SlidingPuzzle.Parberry
open Zhong
variable {n m : ℕ}
local notation "c(" a "," b ")" => ((⟨a, by omega⟩ : Fin n), (⟨b, by omega⟩ : Fin m))

/-- Move the distinguished tile northwest, leaving the blank above it again. -/
def diagonalWord : List Dir := [.U,.R,.D,.L,.D,.R]

/-- The diagonal word is legal, moves the tile and blank as claimed, and stays
inside its three-row/two-column rectangle. -/
theorem diagonalWord_spec (a b : ℕ) (ha : a+2 < n) (hb : b+1 < m) :
    ApplicableFrom c(a+1,b+1) diagonalWord ∧
    trace c(a+1,b+1) diagonalWord = c(a,b) ∧
    permOf c(a+1,b+1) diagonalWord c(a+1,b) = c(a+2,b+1) ∧
    ∀ z ∈ traceSet c(a+1,b+1) diagonalWord,
      a ≤ z.1.val ∧ z.1.val ≤ a+2 ∧ b ≤ z.2.val ∧ z.2.val ≤ b+1 := by
  have h1 : neighbor? c(a+1,b+1) Dir.U = some c(a+2,b+1) := by
    simpa using (nb_U (n := n) (m := m) (a+1) (b+1) (by omega) hb)
  have h2 : neighbor? c(a+2,b+1) Dir.R = some c(a+2,b) := by
    simpa using (nb_R (n := n) (m := m) (a+2) (b+1) (by omega) ha hb)
  have h3 : neighbor? c(a+2,b) Dir.D = some c(a+1,b) := by
    simpa using (nb_D (n := n) (m := m) (a+2) b (by omega) ha (by omega))
  have h4 : neighbor? c(a+1,b) Dir.L = some c(a+1,b+1) :=
    nb_L (a+1) b hb (by omega)
  have h5 : neighbor? c(a+1,b+1) Dir.D = some c(a,b+1) := by
    simpa using (nb_D (n := n) (m := m) (a+1) (b+1) (by omega) (by omega) hb)
  have h6 : neighbor? c(a,b+1) Dir.R = some c(a,b) := by
    simpa using (nb_R (n := n) (m := m) a (b+1) (by omega) (by omega) hb)
  refine ⟨?_,?_,?_,?_⟩
  · simp only [diagonalWord, applicableFrom_cons_of_neighbor? h1,
      applicableFrom_cons_of_neighbor? h2, applicableFrom_cons_of_neighbor? h3,
      applicableFrom_cons_of_neighbor? h4, applicableFrom_cons_of_neighbor? h5,
      applicableFrom_cons_of_neighbor? h6]
    trivial
  · simp only [diagonalWord, trace_cons_of_neighbor? h1, trace_cons_of_neighbor? h2,
      trace_cons_of_neighbor? h3, trace_cons_of_neighbor? h4,
      trace_cons_of_neighbor? h5, trace_cons_of_neighbor? h6, trace_nil]
  · simp only [diagonalWord, permOf_cons_of_neighbor? h1, permOf_cons_of_neighbor? h2,
      permOf_cons_of_neighbor? h3, permOf_cons_of_neighbor? h4,
      permOf_cons_of_neighbor? h5, permOf_cons_of_neighbor? h6, permOf_nil,
      Equiv.Perm.mul_apply, Equiv.refl_apply]
    simp [Equiv.swap_apply_def, Prod.ext_iff, Fin.ext_iff]
  · intro z hz
    simp only [diagonalWord, traceSet_cons_of_neighbor? h1, traceSet_cons_of_neighbor? h2,
      traceSet_cons_of_neighbor? h3, traceSet_cons_of_neighbor? h4,
      traceSet_cons_of_neighbor? h5, traceSet_cons_of_neighbor? h6,
      traceSet_nil, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega

/-- Repeat diagonal transport without routing the blank afresh. -/
def diagonalRun : ℕ → List Dir
  | 0 => []
  | d+1 => diagonalWord ++ diagonalRun d

@[simp] theorem diagonalRun_length (d : ℕ) : (diagonalRun d).length = 6*d := by
  induction d with
  | zero => rfl
  | succ d ih => simp [diagonalRun, diagonalWord, ih]; omega

/-- A diagonal run pays exactly six moves per diagonal unit, preserves every
cell outside its bounding rectangle, and keeps the blank above the moved tile. -/
theorem diagonalRun_spec (d a b : ℕ) (ha : a+d+1 < n) (hb : b+d < m) :
    ApplicableFrom c(a+d,b+d) (diagonalRun d) ∧
    trace c(a+d,b+d) (diagonalRun d) = c(a,b) ∧
    permOf c(a+d,b+d) (diagonalRun d) c(a+1,b) = c(a+d+1,b+d) ∧
    ∀ z ∈ traceSet c(a+d,b+d) (diagonalRun d),
      a ≤ z.1.val ∧ z.1.val ≤ a+d+1 ∧ b ≤ z.2.val ∧ z.2.val ≤ b+d := by
  induction d with
  | zero =>
      simp only [diagonalRun, Nat.add_zero, ApplicableFrom, trace_nil, permOf_nil,
        Equiv.Perm.one_apply, true_and, traceSet_nil, Finset.mem_singleton]
      intro z hz
      subst z
      simp
  | succ d ih =>
      obtain ⟨happ,ht,hp,hs⟩ := diagonalWord_spec (n := n) (m := m) (a+d) (b+d)
        (by omega) (by omega)
      obtain ⟨ihapp,iht,ihp,ihs⟩ := ih (by omega) (by omega)
      simp only [Nat.add_assoc] at happ ht hp hs
      have he : a+(d+1)+1 = a+d+2 := by omega
      refine ⟨?_,?_,?_,?_⟩
      · simpa only [diagonalRun, Nat.add_assoc, applicableFrom_append, ht] using
          (And.intro happ ihapp)
      · simpa only [diagonalRun, Nat.add_assoc, trace_append, ht] using iht
      · simpa only [diagonalRun, Nat.add_assoc, permOf_append, ht,
          Equiv.Perm.mul_apply, ihp, he] using hp
      · intro z hz
        rw [diagonalRun, traceSet_append] at hz
        rw [ht] at hz
        rcases Finset.mem_union.mp hz with hz | hz
        · have hh := hs z hz
          omega
        · have hh := ihs z hz
          omega

end SlidingPuzzle.Parberry
