import Zhong.Group

/-! Short placements next to the target. All routes avoid the solved prefix. -/
namespace SlidingPuzzle.Parberry
open Zhong
variable {n m : ℕ}
local notation "c(" a "," b ")" => ((⟨a, by omega⟩ : Fin n), (⟨b, by omega⟩ : Fin m))

/-- Place the tile at `(1, 1)` relative to the row origin, and park below it. -/
def adjacentBelowWord : List Dir := [.U,.L,.L,.D,.D,.R,.U]

theorem adjacentBelowWord_spec (a b : ℕ) (ha : a+2 < n) (hb : b+2 < m) :
    ApplicableFrom c(a+1,b) adjacentBelowWord ∧
    trace c(a+1,b) adjacentBelowWord=c(a+1,b+1) ∧
    permOf c(a+1,b) adjacentBelowWord c(a,b+1)=c(a+1,b+1) ∧
    ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
      permOf c(a+1,b) adjacentBelowWord z=z := by
  have h1 : neighbor? c(a+1,b) Dir.U=some c(a+2,b) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h2 : neighbor? c(a+2,b) Dir.L=some c(a+2,b+1) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h3 : neighbor? c(a+2,b+1) Dir.L=some c(a+2,b+2) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h4 : neighbor? c(a+2,b+2) Dir.D=some c(a+1,b+2) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h5 : neighbor? c(a+1,b+2) Dir.D=some c(a,b+2) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h6 : neighbor? c(a,b+2) Dir.R=some c(a,b+1) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h7 : neighbor? c(a,b+1) Dir.U=some c(a+1,b+1) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  refine ⟨?_,?_,?_,?_⟩
  · simp only [adjacentBelowWord,applicableFrom_cons_of_neighbor? h1,applicableFrom_cons_of_neighbor? h2,
      applicableFrom_cons_of_neighbor? h3,applicableFrom_cons_of_neighbor? h4,
      applicableFrom_cons_of_neighbor? h5,applicableFrom_cons_of_neighbor? h6,
      applicableFrom_cons_of_neighbor? h7]
    trivial
  · simp only [adjacentBelowWord,trace_cons_of_neighbor? h1,trace_cons_of_neighbor? h2,
      trace_cons_of_neighbor? h3,trace_cons_of_neighbor? h4,trace_cons_of_neighbor? h5,
      trace_cons_of_neighbor? h6,trace_cons_of_neighbor? h7,trace_nil]
  · simp only [adjacentBelowWord,permOf_cons_of_neighbor? h1,permOf_cons_of_neighbor? h2,
      permOf_cons_of_neighbor? h3,permOf_cons_of_neighbor? h4,permOf_cons_of_neighbor? h5,
      permOf_cons_of_neighbor? h6,permOf_cons_of_neighbor? h7,permOf_nil,Equiv.Perm.mul_apply]
    simp [Equiv.swap_apply_def,Prod.ext_iff,Fin.ext_iff]
  · intro z hz
    apply permOf_apply_of_not_mem_traceSet
    intro hmem
    simp only [adjacentBelowWord,traceSet_cons_of_neighbor? h1,traceSet_cons_of_neighbor? h2,
      traceSet_cons_of_neighbor? h3,traceSet_cons_of_neighbor? h4,traceSet_cons_of_neighbor? h5,
      traceSet_cons_of_neighbor? h6,traceSet_cons_of_neighbor? h7,
      traceSet_nil,Finset.mem_insert,Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Fin.val_mk] at hz <;> omega

/-- Place the tile at `(1, 2)` relative to the row origin, and park below it. -/
def adjacentDiagonalWord : List Dir := [.L,.D,.L,.U,.R,.D,.L,.U,.R]

theorem adjacentDiagonalWord_spec (a b : ℕ) (ha : a+1 < n) (hb : b+2 < m) :
    ApplicableFrom c(a+1,b) adjacentDiagonalWord ∧
    trace c(a+1,b) adjacentDiagonalWord=c(a+1,b+1) ∧
    permOf c(a+1,b) adjacentDiagonalWord c(a,b+1)=c(a+1,b+2) ∧
    ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
      permOf c(a+1,b) adjacentDiagonalWord z=z := by
  have h1 : neighbor? c(a+1,b) Dir.L=some c(a+1,b+1) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h2 : neighbor? c(a+1,b+1) Dir.D=some c(a,b+1) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h3 : neighbor? c(a,b+1) Dir.L=some c(a,b+2) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h4 : neighbor? c(a,b+2) Dir.U=some c(a+1,b+2) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h5 : neighbor? c(a+1,b+2) Dir.R=some c(a+1,b+1) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h6 : neighbor? c(a+1,b+1) Dir.D=some c(a,b+1) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h7 : neighbor? c(a,b+1) Dir.L=some c(a,b+2) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h8 : neighbor? c(a,b+2) Dir.U=some c(a+1,b+2) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h9 : neighbor? c(a+1,b+2) Dir.R=some c(a+1,b+1) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  refine ⟨?_,?_,?_,?_⟩
  · simp only [adjacentDiagonalWord,applicableFrom_cons_of_neighbor? h1,applicableFrom_cons_of_neighbor? h2,
      applicableFrom_cons_of_neighbor? h3,applicableFrom_cons_of_neighbor? h4,
      applicableFrom_cons_of_neighbor? h5,applicableFrom_cons_of_neighbor? h6,
      applicableFrom_cons_of_neighbor? h7,applicableFrom_cons_of_neighbor? h8,
      applicableFrom_cons_of_neighbor? h9]
    trivial
  · simp only [adjacentDiagonalWord,trace_cons_of_neighbor? h1,trace_cons_of_neighbor? h2,
      trace_cons_of_neighbor? h3,trace_cons_of_neighbor? h4,trace_cons_of_neighbor? h5,
      trace_cons_of_neighbor? h6,trace_cons_of_neighbor? h7,trace_cons_of_neighbor? h8,
      trace_cons_of_neighbor? h9,trace_nil]
  · simp only [adjacentDiagonalWord,permOf_cons_of_neighbor? h1,permOf_cons_of_neighbor? h2,
      permOf_cons_of_neighbor? h3,permOf_cons_of_neighbor? h4,permOf_cons_of_neighbor? h5,
      permOf_cons_of_neighbor? h6,permOf_cons_of_neighbor? h7,permOf_cons_of_neighbor? h8,
      permOf_cons_of_neighbor? h9,permOf_nil,Equiv.Perm.mul_apply]
    simp [Equiv.swap_apply_def,Prod.ext_iff,Fin.ext_iff]
  · intro z hz
    apply permOf_apply_of_not_mem_traceSet
    intro hmem
    simp only [adjacentDiagonalWord,traceSet_cons_of_neighbor? h1,traceSet_cons_of_neighbor? h2,
      traceSet_cons_of_neighbor? h3,traceSet_cons_of_neighbor? h4,traceSet_cons_of_neighbor? h5,
      traceSet_cons_of_neighbor? h6,traceSet_cons_of_neighbor? h7,traceSet_cons_of_neighbor? h8,
      traceSet_cons_of_neighbor? h9,
      traceSet_nil,Finset.mem_insert,Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Fin.val_mk] at hz <;> omega

/-- Place the tile at `(2, 0)` relative to the row origin, and park below it. -/
def adjacentWestWord : List Dir := [.U,.L,.D,.R,.U,.L,.L,.D,.D,.R,.U]

theorem adjacentWestWord_spec (a b : ℕ) (ha : a+2 < n) (hb : b+2 < m) :
    ApplicableFrom c(a+1,b) adjacentWestWord ∧
    trace c(a+1,b) adjacentWestWord=c(a+1,b+1) ∧
    permOf c(a+1,b) adjacentWestWord c(a,b+1)=c(a+2,b) ∧
    ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
      permOf c(a+1,b) adjacentWestWord z=z := by
  have h1 : neighbor? c(a+1,b) Dir.U=some c(a+2,b) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h2 : neighbor? c(a+2,b) Dir.L=some c(a+2,b+1) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h3 : neighbor? c(a+2,b+1) Dir.D=some c(a+1,b+1) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h4 : neighbor? c(a+1,b+1) Dir.R=some c(a+1,b) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h5 : neighbor? c(a+1,b) Dir.U=some c(a+2,b) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h6 : neighbor? c(a+2,b) Dir.L=some c(a+2,b+1) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h7 : neighbor? c(a+2,b+1) Dir.L=some c(a+2,b+2) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h8 : neighbor? c(a+2,b+2) Dir.D=some c(a+1,b+2) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h9 : neighbor? c(a+1,b+2) Dir.D=some c(a,b+2) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h10 : neighbor? c(a,b+2) Dir.R=some c(a,b+1) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h11 : neighbor? c(a,b+1) Dir.U=some c(a+1,b+1) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  refine ⟨?_,?_,?_,?_⟩
  · simp only [adjacentWestWord,applicableFrom_cons_of_neighbor? h1,applicableFrom_cons_of_neighbor? h2,
      applicableFrom_cons_of_neighbor? h3,applicableFrom_cons_of_neighbor? h4,
      applicableFrom_cons_of_neighbor? h5,applicableFrom_cons_of_neighbor? h6,
      applicableFrom_cons_of_neighbor? h7,applicableFrom_cons_of_neighbor? h8,
      applicableFrom_cons_of_neighbor? h9,applicableFrom_cons_of_neighbor? h10,
      applicableFrom_cons_of_neighbor? h11]
    trivial
  · simp only [adjacentWestWord,trace_cons_of_neighbor? h1,trace_cons_of_neighbor? h2,
      trace_cons_of_neighbor? h3,trace_cons_of_neighbor? h4,trace_cons_of_neighbor? h5,
      trace_cons_of_neighbor? h6,trace_cons_of_neighbor? h7,trace_cons_of_neighbor? h8,
      trace_cons_of_neighbor? h9,trace_cons_of_neighbor? h10,trace_cons_of_neighbor? h11,trace_nil]
  · simp only [adjacentWestWord,permOf_cons_of_neighbor? h1,permOf_cons_of_neighbor? h2,
      permOf_cons_of_neighbor? h3,permOf_cons_of_neighbor? h4,permOf_cons_of_neighbor? h5,
      permOf_cons_of_neighbor? h6,permOf_cons_of_neighbor? h7,permOf_cons_of_neighbor? h8,
      permOf_cons_of_neighbor? h9,permOf_cons_of_neighbor? h10,permOf_cons_of_neighbor? h11,permOf_nil,
      Equiv.Perm.mul_apply]
    simp [Equiv.swap_apply_def,Prod.ext_iff,Fin.ext_iff]
  · intro z hz
    apply permOf_apply_of_not_mem_traceSet
    intro hmem
    simp only [adjacentWestWord,traceSet_cons_of_neighbor? h1,traceSet_cons_of_neighbor? h2,
      traceSet_cons_of_neighbor? h3,traceSet_cons_of_neighbor? h4,traceSet_cons_of_neighbor? h5,
      traceSet_cons_of_neighbor? h6,traceSet_cons_of_neighbor? h7,traceSet_cons_of_neighbor? h8,
      traceSet_cons_of_neighbor? h9,traceSet_cons_of_neighbor? h10,traceSet_cons_of_neighbor? h11,
      traceSet_nil,Finset.mem_insert,Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Fin.val_mk] at hz <;> omega

/-- Place the tile at `(1, 1)` relative to the row origin, and park below it. -/
def lowerInsertionWord : List Dir := [.R,.D,.U,.L,.L,.D,.D,.R,.U]

theorem lowerInsertionWord_spec (a b : ℕ) (ha : a+2 < n) (hb : b+2 < m) :
    ApplicableFrom c(a+2,b+1) lowerInsertionWord ∧
    trace c(a+2,b+1) lowerInsertionWord=c(a+1,b+1) ∧
    permOf c(a+2,b+1) lowerInsertionWord c(a,b+1)=c(a+1,b+1) ∧
    ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
      permOf c(a+2,b+1) lowerInsertionWord z=z := by
  have h1 : neighbor? c(a+2,b+1) Dir.R=some c(a+2,b) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h2 : neighbor? c(a+2,b) Dir.D=some c(a+1,b) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h3 : neighbor? c(a+1,b) Dir.U=some c(a+2,b) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h4 : neighbor? c(a+2,b) Dir.L=some c(a+2,b+1) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h5 : neighbor? c(a+2,b+1) Dir.L=some c(a+2,b+2) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h6 : neighbor? c(a+2,b+2) Dir.D=some c(a+1,b+2) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h7 : neighbor? c(a+1,b+2) Dir.D=some c(a,b+2) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h8 : neighbor? c(a,b+2) Dir.R=some c(a,b+1) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  have h9 : neighbor? c(a,b+1) Dir.U=some c(a+1,b+1) := by
    simp [neighbor?,Prod.ext_iff,Fin.ext_iff] <;> omega
  refine ⟨?_,?_,?_,?_⟩
  · simp only [lowerInsertionWord,applicableFrom_cons_of_neighbor? h1,applicableFrom_cons_of_neighbor? h2,
      applicableFrom_cons_of_neighbor? h3,applicableFrom_cons_of_neighbor? h4,
      applicableFrom_cons_of_neighbor? h5,applicableFrom_cons_of_neighbor? h6,
      applicableFrom_cons_of_neighbor? h7,applicableFrom_cons_of_neighbor? h8,
      applicableFrom_cons_of_neighbor? h9]
    trivial
  · simp only [lowerInsertionWord,trace_cons_of_neighbor? h1,trace_cons_of_neighbor? h2,
      trace_cons_of_neighbor? h3,trace_cons_of_neighbor? h4,trace_cons_of_neighbor? h5,
      trace_cons_of_neighbor? h6,trace_cons_of_neighbor? h7,trace_cons_of_neighbor? h8,
      trace_cons_of_neighbor? h9,trace_nil]
  · simp only [lowerInsertionWord,permOf_cons_of_neighbor? h1,permOf_cons_of_neighbor? h2,
      permOf_cons_of_neighbor? h3,permOf_cons_of_neighbor? h4,permOf_cons_of_neighbor? h5,
      permOf_cons_of_neighbor? h6,permOf_cons_of_neighbor? h7,permOf_cons_of_neighbor? h8,
      permOf_cons_of_neighbor? h9,permOf_nil,Equiv.Perm.mul_apply]
    simp [Equiv.swap_apply_def,Prod.ext_iff,Fin.ext_iff]
  · intro z hz
    apply permOf_apply_of_not_mem_traceSet
    intro hmem
    simp only [lowerInsertionWord,traceSet_cons_of_neighbor? h1,traceSet_cons_of_neighbor? h2,
      traceSet_cons_of_neighbor? h3,traceSet_cons_of_neighbor? h4,traceSet_cons_of_neighbor? h5,
      traceSet_cons_of_neighbor? h6,traceSet_cons_of_neighbor? h7,traceSet_cons_of_neighbor? h8,
      traceSet_cons_of_neighbor? h9,
      traceSet_nil,Finset.mem_insert,Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Fin.val_mk] at hz <;> omega

end SlidingPuzzle.Parberry
