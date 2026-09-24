import SlidingPuzzle.Algorithm.Parberry.TopRow

/-! Complete placement on the right side of the destination, including tiles
already in the target row. The same contract covers all displacement cases. -/
namespace SlidingPuzzle.Parberry
open Zhong
variable {n : ℕ}
local notation "c(" a "," b ")" => ((⟨a, by omega⟩ : Fin n), (⟨b, by omega⟩ : Fin n))

/-- If the tile is already placed, move the blank one column right below it. -/
theorem skipPlacementWord_spec (a b : ℕ) (ha : a+1 < n) (hb : b+1 < n) :
    ApplicableFrom c(a+1,b) [.L] ∧ trace c(a+1,b) [.L]=c(a+1,b+1) ∧
    permOf c(a+1,b) [.L] c(a,b+1)=c(a,b+1) ∧
    ∀ z : Zhong.Cell n n, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
      permOf c(a+1,b) [.L] z=z := by
  have hs : neighbor? c(a+1,b) Dir.L=some c(a+1,b+1) := nb_L (a+1) b hb ha
  refine ⟨?_,?_,?_,?_⟩
  · simp only [applicableFrom_cons_of_neighbor? hs]; trivial
  · simp only [trace_cons_of_neighbor? hs,trace_nil]
  · simp only [permOf_cons_of_neighbor? hs,permOf_nil,Equiv.Perm.mul_apply,Equiv.Perm.one_apply]
    simp [Equiv.swap_apply_def,Prod.ext_iff,Fin.ext_iff]
  · intro z hz
    apply permOf_apply_of_not_mem_traceSet
    intro hmem
    simp only [traceSet_cons_of_neighbor? hs,traceSet_nil,
      Finset.mem_insert,Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl <;> simp only [Fin.val_mk] at hz <;> omega

/-- Every tile on or to the right of its destination admits a complete bounded
row-placement step. The two-row margin is used only by the adjacent-below case. -/
theorem exists_rightPlacementWord (a b i j : ℕ)
    (ha : a+i < n) (hb : b+j+1 < n) (ha2 : a+2 < n) (hb2 : b+2 < n) :
    ∃ σ : List Dir, σ.length+2*(b+1)+7 ≤ 8*n ∧
      ApplicableFrom c(a+1,b) σ ∧ trace c(a+1,b) σ=c(a+1,b+1) ∧
      permOf c(a+1,b) σ c(a,b+1)=c(a+i,b+j+1) ∧
      ∀ z : Zhong.Cell n n, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
        permOf c(a+1,b) σ z=z := by
  by_cases hi : i=0
  · subst i
    cases j with
    | zero =>
        refine ⟨[.L],by simp; omega,?_⟩
        simpa only [Nat.add_zero] using skipPlacementWord_spec a b (by omega : a+1 < n) (by omega)
    | succ v =>
        refine ⟨topPlacementWord a b v,topPlacementWord_budget a b v n (by omega),?_⟩
        simpa only [Nat.add_zero,Nat.add_assoc] using topPlacementWord_spec a b v
          (by omega : a+1 < n) (by omega : b+v+2 < n)
  by_cases htall : j+2 ≤ i
  · let v := i-j-2
    have hx : a+v+j+2=a+i := by dsimp [v]; omega
    refine ⟨southeastPlacementWord a b j v,
      southeastPlacementWord_budget a b j v n (by omega) hb,?_⟩
    simpa only [hx] using southeastPlacementWord_spec a b j v
      (by omega : a+v+j+2 < n) hb hb2
  by_cases hnear : i=j+1
  · cases j with
    | zero =>
        have hi1 : i=1 := by omega
        refine ⟨adjacentBelowWord,by simp [adjacentBelowWord]; omega,?_⟩
        simpa only [hi1,Nat.zero_add,Nat.add_zero] using adjacentBelowWord_spec a b ha2 hb2
    | succ d =>
        have hx : a+d+2=a+i := by omega
        have hy : b+(d+1)+1=b+d+2 := by omega
        refine ⟨nearPlacementWord a b d,nearPlacementWord_budget a b d n (by omega),?_⟩
        simpa only [hx,hy] using nearPlacementWord_spec a b d (by omega : a+d+2 < n)
          (by omega : b+d+2 < n)
  by_cases heq : i=j
  · by_cases hj1 : j=1
    · have hi1 : i=1 := by omega
      refine ⟨adjacentDiagonalWord,by simp [adjacentDiagonalWord]; omega,?_⟩
      simpa only [hi1,hj1] using adjacentDiagonalWord_spec a b (by omega : a+1 < n) hb2
    · let d := j-2
      have hx : a+d+2=a+i := by dsimp [d]; omega
      have hy : b+d+3=b+j+1 := by dsimp [d]; omega
      refine ⟨equalPlacementWord a b d,equalPlacementWord_budget a b d n (by omega),?_⟩
      simpa only [hx,hy] using equalPlacementWord_spec a b d (by omega : a+d+2 < n)
        (by omega : b+d+3 < n)
  · let d := i-1
    let v := j-i-1
    have hx : a+d+1=a+i := by dsimp [d]; omega
    have hy : b+v+d+3=b+j+1 := by dsimp [d,v]; omega
    refine ⟨widePlacementWord a b d v,widePlacementWord_budget a b d v n (by omega),?_⟩
    simpa only [hx,hy] using widePlacementWord_spec a b d v (by omega : a+d+1 < n)
      (by omega : b+v+d+3 < n)

end SlidingPuzzle.Parberry
