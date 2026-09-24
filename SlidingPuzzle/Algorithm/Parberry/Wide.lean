import SlidingPuzzle.Algorithm.Parberry.Transport

/-! Horizontally dominant southeast placements. Transposition is applied to
transport only; the initial blank route is kept below the protected row. -/
namespace SlidingPuzzle.Parberry
open Zhong
variable {n m : ℕ}
local notation "c(" a "," b ")" => ((⟨a, by omega⟩ : Fin n), (⟨b, by omega⟩ : Fin m))

/-- Transposed diagonal/straight transport, ending with the blank below the tile. -/
def horizontalWord (a b d v : ℕ) : List Dir :=
  (transportWord b a d v).map transDir

@[simp] theorem horizontalWord_length (a b d v : ℕ) :
    (horizontalWord a b d v).length = 6*d+5*v+3 := by
  simp [horizontalWord]

theorem horizontalWord_spec (a b d v : ℕ) (ha : a+d < n)
    (ha1 : a+1 < n) (hb : b+v+d+1 < m) :
    ApplicableFrom c(a+d,b+v+d) (horizontalWord a b d v) ∧
    trace c(a+d,b+v+d) (horizontalWord a b d v)=c(a+1,b) ∧
    permOf c(a+d,b+v+d) (horizontalWord a b d v) c(a,b)=c(a+d,b+v+d+1) ∧
    ∀ z : Zhong.Cell n m, z.1.val<a ∨ z.2.val<b →
      permOf c(a+d,b+v+d) (horizontalWord a b d v) z=z := by
  obtain ⟨happ,ht,hp,hfix⟩ := transportWord_spec (n := m) (m := n) b a d v hb ha ha1
  have hstep : ∀ (c : Zhong.Cell m n) δ c', neighbor? c δ=some c' →
      neighbor? (transEquiv m n c) (transDir δ)=some (transEquiv m n c') := by
    intro c δ c' h
    rw [neighbor?_transEquiv,h,Option.map_some]
  refine ⟨applicableFrom_map_of_neighbor_map hstep happ,?_,?_,?_⟩
  · exact (trace_map_of_neighbor_map hstep _ _ happ).trans (congrArg (transEquiv m n) ht)
  · exact (permOf_map_apply_of_neighbor_map (transEquiv m n).injective hstep _ _ happ _).trans
      (congrArg (transEquiv m n) hp)
  · intro z hz
    have h := permOf_map_apply_of_neighbor_map (transEquiv m n).injective hstep _ _ happ (z.2,z.1)
    rw [hfix _ (by simpa using hz.symm)] at h
    exact h

/-- Route the blank to the left of a tile below and strictly to the right of the
northwest diagonal, then transport the tile and park the blank below its target. -/
def widePlacementWord (a b d v : ℕ) : List Dir :=
  moveToWord (a+1) b (a+d+1) (b+v+d+2) ++ horizontalWord a (b+1) (d+1) v

@[simp] theorem widePlacementWord_length (a b d v : ℕ) :
    (widePlacementWord a b d v).length=8*d+6*v+11 := by
  simp only [widePlacementWord,List.length_append,length_moveToWord,horizontalWord_length,Nat.dist]
  omega

theorem widePlacementWord_spec (a b d v : ℕ)
    (ha : a+d+1 < n) (hb : b+v+d+3 < m) :
    ApplicableFrom c(a+1,b) (widePlacementWord a b d v) ∧
    trace c(a+1,b) (widePlacementWord a b d v)=c(a+1,b+1) ∧
    permOf c(a+1,b) (widePlacementWord a b d v) c(a,b+1)=c(a+d+1,b+v+d+3) ∧
    ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
      permOf c(a+1,b) (widePlacementWord a b d v) z=z := by
  have hna := applicableFrom_moveToWord (a+1) b (a+d+1) (b+v+d+2)
    ha (by omega : b+v+d+2 < m) (by omega) (by omega)
  have hnt := trace_moveToWord (a+1) b (a+d+1) (b+v+d+2)
    ha (by omega : b+v+d+2 < m) (by omega) (by omega)
  have hnp : permOf c(a+1,b) (moveToWord (a+1) b (a+d+1) (b+v+d+2))
      c(a+d+1,b+v+d+3)=c(a+d+1,b+v+d+3) := by
    apply permOf_apply_of_not_mem_traceSet
    intro hmem
    have hh := moveToWord_traceSet_col (a+1) b (a+d+1) (b+v+d+2)
      ha (by omega : b+v+d+2 < m) (by omega) (by omega) _ hmem
    simp only [Fin.val_mk] at hh
    omega
  have hnfix := moveToWord_fixes_of_row_lt (lo := a+1) ha
    (by omega : b+v+d+2 < m) (by omega : a+1 < n) (by omega : b < m)
    (by omega) (by omega)
  obtain ⟨hta,htt,htp,htfix⟩ := horizontalWord_spec (n := n) (m := m)
    a (b+1) (d+1) v (by omega) (by omega) (by omega)
  have hx : a+(d+1)=a+d+1 := by omega
  have hy : b+1+v+(d+1)=b+v+d+2 := by omega
  have hy1 : b+1+v+(d+1)+1=b+v+d+3 := by omega
  simp only [hx,hy,hy1] at hta htt htp htfix
  refine ⟨?_,?_,?_,?_⟩
  · rw [widePlacementWord,applicableFrom_append,hnt]
    exact ⟨hna,hta⟩
  · rw [widePlacementWord,trace_append,hnt,htt]
  · rw [widePlacementWord,permOf_append,hnt,Equiv.Perm.mul_apply,htp,hnp]
  · intro z hz
    rw [widePlacementWord,permOf_append,hnt,Equiv.Perm.mul_apply,
      htfix z (by omega),hnfix z (by omega)]

/-- This entire placement, including initial routing, meets the row budget. -/
theorem widePlacementWord_budget (a b d v n : ℕ) (hb : b+v+d+3 < n) :
    (widePlacementWord a b d v).length+2*(b+1)+7 ≤ 8*n := by
  rw [widePlacementWord_length]
  omega

end SlidingPuzzle.Parberry
