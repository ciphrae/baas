import SlidingPuzzle.Parberry.Wide

/-! Placement of a tile already in the unfinished part of the target row. -/
namespace SlidingPuzzle.Parberry
open Zhong
variable {n m : ℕ}
local notation "c(" a "," b ")" => ((⟨a, by omega⟩ : Fin n), (⟨b, by omega⟩ : Fin m))

def topPlacementWord (a b v : ℕ) : List Dir :=
  moveToWord (a+1) b (a+1) (b+v+1) ++ [.D] ++ horizontalWord a (b+1) 0 v

@[simp] theorem topPlacementWord_length (a b v : ℕ) :
    (topPlacementWord a b v).length=6*v+5 := by
  simp only [topPlacementWord,List.length_append,length_moveToWord,
    horizontalWord_length,List.length_cons,List.length_nil,Nat.dist]
  omega

theorem topPlacementWord_spec (a b v : ℕ) (ha : a+1 < n) (hb : b+v+2 < m) :
    ApplicableFrom c(a+1,b) (topPlacementWord a b v) ∧
    trace c(a+1,b) (topPlacementWord a b v)=c(a+1,b+1) ∧
    permOf c(a+1,b) (topPlacementWord a b v) c(a,b+1)=c(a,b+v+2) ∧
    ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
      permOf c(a+1,b) (topPlacementWord a b v) z=z := by
  have hna := applicableFrom_moveToWord (a+1) b (a+1) (b+v+1)
    ha (by omega : b+v+1 < m) ha (by omega)
  have hnt := trace_moveToWord (a+1) b (a+1) (b+v+1)
    ha (by omega : b+v+1 < m) ha (by omega)
  have hnfix := moveToWord_fixes_of_row_lt (lo := a+1) ha
    (by omega : b+v+1 < m) ha (by omega : b < m) (by omega) (by omega)
  have hstep : neighbor? c(a+1,b+v+1) Dir.D=some c(a,b+v+1) := by
    simp
  obtain ⟨hta,htt,htp,htfix⟩ := horizontalWord_spec (n := n) (m := m)
    a (b+1) 0 v (by omega) ha (by omega)
  have hy : b+1+v=b+v+1 := by omega
  have hy1 : b+1+v+1=b+v+2 := by omega
  simp only [Nat.add_zero,hy] at hta htt htp htfix
  have htfix' : ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
      Equiv.swap c(a+1,b+v+1) c(a,b+v+1) z=z := by
    intro z hz
    apply Equiv.swap_apply_of_ne_of_ne <;> intro he <;> subst z <;>
      simp only at hz <;> omega
  have htilet : Equiv.swap c(a+1,b+v+1) c(a,b+v+1) c(a,b+v+2)=c(a,b+v+2) := by
    simp [Equiv.swap_apply_def,Prod.ext_iff,Fin.ext_iff]
  refine ⟨?_,?_,?_,?_⟩
  · simp only [topPlacementWord,applicableFrom_append,trace_append,hnt,
      applicableFrom_cons_of_neighbor? hstep,trace_cons_of_neighbor? hstep,trace_nil]
    exact ⟨⟨hna,trivial⟩,hta⟩
  · simp only [topPlacementWord,trace_append,hnt,trace_cons_of_neighbor? hstep,trace_nil,htt]
  · rw [topPlacementWord,permOf_append,trace_append,hnt,trace_cons_of_neighbor? hstep,
      trace_nil,Equiv.Perm.mul_apply,htp,permOf_append,hnt,Equiv.Perm.mul_apply,
      permOf_cons_of_neighbor? hstep,permOf_nil,Equiv.Perm.mul_apply,Equiv.Perm.one_apply,
      htilet,hnfix _ (by simp)]
  · intro z hz
    rw [topPlacementWord,permOf_append,trace_append,hnt,trace_cons_of_neighbor? hstep,
      trace_nil,Equiv.Perm.mul_apply,htfix z (by omega),permOf_append,hnt,
      Equiv.Perm.mul_apply,permOf_cons_of_neighbor? hstep,permOf_nil,
      Equiv.Perm.mul_apply,Equiv.Perm.one_apply,htfix' z hz,hnfix z (by omega)]

theorem topPlacementWord_budget (a b v n : ℕ) (hb : b+v+2 < n) :
    (topPlacementWord a b v).length+2*(b+1)+7 ≤ 8*n := by
  rw [topPlacementWord_length]
  omega

end SlidingPuzzle.Parberry
