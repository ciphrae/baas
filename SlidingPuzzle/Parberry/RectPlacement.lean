import SlidingPuzzle.Parberry.NearDiagonal
import SlidingPuzzle.Parberry.TopRow
import SlidingPuzzle.Parberry.West

/-! Rectangular forms of the placement construction. The height bounds the
width, as needed when transposing the board after removing its solved row. -/
namespace SlidingPuzzle.Parberry.Rect
open Zhong
variable {n m : ℕ}
local notation "c(" a "," b ")" => ((⟨a, by omega⟩ : Fin n), (⟨b, by omega⟩ : Fin m))

/-- If the tile is already placed, move the blank one column right below it. -/
theorem skipPlacementWord_spec (a b : ℕ) (ha : a+1 < n) (hb : b+1 < m) :
    ApplicableFrom c(a+1,b) [.L] ∧ trace c(a+1,b) [.L]=c(a+1,b+1) ∧
    permOf c(a+1,b) [.L] c(a,b+1)=c(a,b+1) ∧
    ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
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
theorem exists_rightPlacementWord (a b i j : ℕ) (hm : m ≤ n)
    (ha : a+i < n) (hb : b+j+1 < m) (ha2 : a+2 < n) (hb2 : b+2 < m) :
    ∃ σ : List Dir, σ.length+2*(b+1)+7 ≤ 8*n ∧
      ApplicableFrom c(a+1,b) σ ∧ trace c(a+1,b) σ=c(a+1,b+1) ∧
      permOf c(a+1,b) σ c(a,b+1)=c(a+i,b+j+1) ∧
      ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
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
          (by omega : a+1 < n) (by omega : b+v+2 < m)
  by_cases htall : j+2 ≤ i
  · let v := i-j-2
    have hx : a+v+j+2=a+i := by dsimp [v]; omega
    refine ⟨southeastPlacementWord a b j v,
      southeastPlacementWord_budget a b j v n (by omega) (by omega),?_⟩
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
          (by omega : b+d+2 < m)
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
        (by omega : b+d+3 < m)
  · let d := i-1
    let v := j-i-1
    have hx : a+d+1=a+i := by dsimp [d]; omega
    have hy : b+v+d+3=b+j+1 := by dsimp [d,v]; omega
    refine ⟨widePlacementWord a b d v,widePlacementWord_budget a b d v n (by omega),?_⟩
    simpa only [hx,hy] using widePlacementWord_spec a b d v (by omega : a+d+1 < n)
      (by omega : b+v+d+3 < m)

theorem exists_leftPlacementWord (a b i d : ℕ) (hm : m ≤ n)
    (ha : a+i < n) (hi : 1 ≤ i) (hd : d ≤ b)
    (ha2 : a+2 < n) (hb2 : b+2 < m) (hne : i≠1 ∨ d≠0) :
    ∃ σ : List Dir, σ.length+2*(n-(b+1))+7 ≤ 8*n ∧
      ApplicableFrom c(a+1,b) σ ∧ trace c(a+1,b) σ=c(a+1,b+1) ∧
      permOf c(a+1,b) σ c(a,b+1)=c(a+i,b-d) ∧
      ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
        permOf c(a+1,b) σ z=z := by
  by_cases htall : d+3 ≤ i
  · let v := i-d-3
    have hx : a+v+d+3=a+i := by dsimp [v]; omega
    refine ⟨westTallWord m a b d v,by
      rw [westTallWord_length m a b d v hd]
      omega,?_⟩
    simpa only [hx] using westTallWord_spec a b d v (by omega : a+v+d+3 < n) hb2 hd
  by_cases hnear : i=d+2
  · have hx : a+d+2=a+i := by omega
    refine ⟨westNearWord a b d,westNearWord_budget a b d n (by omega) hd,?_⟩
    simpa only [hx] using westNearWord_spec a b d (by omega : a+d+2 < n) hb2 hd
  · let e := i-1
    let v := d+1-i
    have he : v+e=d := by dsimp [v,e]; omega
    have hpos : 1 ≤ v+e := by omega
    have hx : a+e+1=a+i := by dsimp [e]; omega
    have hy : b-v-e=b-d := by omega
    refine ⟨westWideWord m a b e v,by
      rw [westWideWord_length m a b e v (by omega) hpos]
      omega,?_⟩
    simpa only [hx,hy] using westWideWord_spec a b e v (by omega : a+e+1 < n)
      ha2 hb2 (by omega) hpos

/-- Complete ordinary placement: the source may be anywhere outside the solved
prefix, except at the blank itself. No positional case is left as a hypothesis. -/
theorem exists_placementWord (a b : ℕ) (x : Fin n) (y : Fin m) (hm : m ≤ n)
    (hfree : a<x.val ∨ (a=x.val ∧ b+1≤y.val))
    (ha2 : a+2 < n) (hb2 : b+2 < m) (hne : (x,y)≠c(a+1,b)) :
    ∃ σ : List Dir, σ.length+2*min (b+1) (n-(b+1))+7 ≤ 8*n ∧
      ApplicableFrom c(a+1,b) σ ∧ trace c(a+1,b) σ=c(a+1,b+1) ∧
      permOf c(a+1,b) σ c(a,b+1)=(x,y) ∧
      ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
        permOf c(a+1,b) σ z=z := by
  by_cases hy : b+1≤y.val
  · obtain ⟨σ,hlen,hs⟩ := exists_rightPlacementWord a b (x.val-a) (y.val-b-1) hm
      (by omega : a+(x.val-a) < n) (by omega : b+(y.val-b-1)+1 < m) ha2 hb2
    have he : (c(a+(x.val-a),b+(y.val-b-1)+1) : Zhong.Cell n m)=(x,y) := by
      apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega
    refine ⟨σ,?_,?_⟩
    · have := min_le_left (b+1) (n-(b+1)); omega
    · simpa only [he] using hs
  · have hni : x.val-a≠1 ∨ b-y.val≠0 := by
      by_contra hh
      apply hne
      apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega
    obtain ⟨σ,hlen,hs⟩ := exists_leftPlacementWord a b (x.val-a) (b-y.val) hm
      (by omega : a+(x.val-a) < n) (by omega) (by omega) ha2 hb2 hni
    have he : (c(a+(x.val-a),b-(b-y.val)) : Zhong.Cell n m)=(x,y) := by
      apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega
    refine ⟨σ,?_,?_⟩
    · have := min_le_right (b+1) (n-(b+1)); omega
    · simpa only [he] using hs

end SlidingPuzzle.Parberry.Rect
