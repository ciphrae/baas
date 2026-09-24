import SlidingPuzzle.Parberry.Transport

/-! The southeast cases on or immediately below the diagonal. -/
namespace SlidingPuzzle.Parberry
open Zhong
variable {n m : ℕ}
local notation "c(" a "," b ")" => ((⟨a, by omega⟩ : Fin n), (⟨b, by omega⟩ : Fin m))

/-- The final diagonal unit uses the target row but no row above it. -/
def diagonalEndWord : List Dir := [.U,.R,.D,.L,.U,.R]

theorem diagonalEndWord_spec (a b : ℕ) (ha : a+1 < n) (hb : b+1 < m) :
    ApplicableFrom c(a,b+1) diagonalEndWord ∧
    trace c(a,b+1) diagonalEndWord=c(a+1,b) ∧
    permOf c(a,b+1) diagonalEndWord c(a,b)=c(a+1,b+1) ∧
    ∀ z : Zhong.Cell n m, z.1.val<a ∨ z.2.val<b →
      permOf c(a,b+1) diagonalEndWord z=z := by
  have h1 : neighbor? c(a,b+1) Dir.U=some c(a+1,b+1) := nb_U a (b+1) ha hb
  have h2 : neighbor? c(a+1,b+1) Dir.R=some c(a+1,b) := by
    simp
  have h3 : neighbor? c(a+1,b) Dir.D=some c(a,b) := by
    simp
  have h4 : neighbor? c(a,b) Dir.L=some c(a,b+1) := nb_L a b hb (by omega)
  refine ⟨?_,?_,?_,?_⟩
  · simp only [diagonalEndWord,applicableFrom_cons_of_neighbor? h1,
      applicableFrom_cons_of_neighbor? h2,applicableFrom_cons_of_neighbor? h3,
      applicableFrom_cons_of_neighbor? h4]
    trivial
  · simp only [diagonalEndWord,trace_cons_of_neighbor? h1,trace_cons_of_neighbor? h2,
      trace_cons_of_neighbor? h3,trace_cons_of_neighbor? h4,trace_nil]
  · simp only [diagonalEndWord,permOf_cons_of_neighbor? h1,permOf_cons_of_neighbor? h2,
      permOf_cons_of_neighbor? h3,permOf_cons_of_neighbor? h4,permOf_nil,Equiv.Perm.mul_apply]
    simp [Equiv.swap_apply_def,Prod.ext_iff,Fin.ext_iff]
  · intro z hz
    apply permOf_apply_of_not_mem_traceSet
    intro hmem
    simp only [diagonalEndWord,traceSet_cons_of_neighbor? h1,traceSet_cons_of_neighbor? h2,
      traceSet_cons_of_neighbor? h3,traceSet_cons_of_neighbor? h4,
      traceSet_nil,Finset.mem_insert,Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only at hz <;> omega

/-- Initial routing and a diagonal run, including the special last unit. -/
def equalPlacementWord (a b d : ℕ) : List Dir :=
  moveToWord (a+1) b (a+d+1) (b+d+3) ++ diagonalRun (d+1) ++ diagonalEndWord

@[simp] theorem equalPlacementWord_length (a b d : ℕ) :
    (equalPlacementWord a b d).length=8*d+15 := by
  simp only [equalPlacementWord,List.length_append,length_moveToWord,
    diagonalRun_length,diagonalEndWord,List.length_cons,List.length_nil,Nat.dist]
  omega

theorem equalPlacementWord_spec (a b d : ℕ)
    (ha : a+d+2 < n) (hb : b+d+3 < m) :
    ApplicableFrom c(a+1,b) (equalPlacementWord a b d) ∧
    trace c(a+1,b) (equalPlacementWord a b d)=c(a+1,b+1) ∧
    permOf c(a+1,b) (equalPlacementWord a b d) c(a,b+1)=c(a+d+2,b+d+3) ∧
    ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
      permOf c(a+1,b) (equalPlacementWord a b d) z=z := by
  obtain ⟨hna,hnt,hnp,hnfix,_⟩ := navToAbove (n := n) (m := m)
    a (a+1) b (a+d+2) (b+d+3) ha (by omega) hb (by omega)
    (by omega) (by omega) (Or.inl (by omega))
  have hsub : a+d+2-1=a+d+1 := by omega
  simp only [hsub] at hna hnt hnp hnfix
  obtain ⟨hda,hdt,hdp,hds⟩ := diagonalRun_spec (n := n) (m := m)
    (d+1) a (b+2) (by omega) (by omega)
  have hx : a+(d+1)=a+d+1 := by omega
  have hx1 : a+(d+1)+1=a+d+2 := by omega
  have hy : b+2+(d+1)=b+d+3 := by omega
  simp only [hx,hy] at hda hdt hdp hds
  obtain ⟨hea,het,hep,hefix⟩ := diagonalEndWord_spec (n := n) (m := m) a (b+1) (by omega) (by omega)
  have hy1 : b+1+1=b+2 := by omega
  simp only [hy1] at hea het hep hefix
  refine ⟨?_,?_,?_,?_⟩
  · simp only [equalPlacementWord,applicableFrom_append,trace_append,hnt,hdt]
    exact ⟨⟨hna,hda⟩,hea⟩
  · rw [equalPlacementWord,trace_append,trace_append,hnt,hdt,het]
  · rw [equalPlacementWord,permOf_append,trace_append,hnt,hdt,
      Equiv.Perm.mul_apply,hep,permOf_append,hnt,Equiv.Perm.mul_apply,hdp,hnp]
  · intro z hz
    have hdfix : permOf c(a+d+1,b+d+3) (diagonalRun (d+1)) z=z := by
      apply permOf_apply_of_not_mem_traceSet
      intro hmem
      have hh := hds z hmem
      omega
    rw [equalPlacementWord,permOf_append,trace_append,hnt,hdt,Equiv.Perm.mul_apply,
      hefix z (by omega),permOf_append,hnt,Equiv.Perm.mul_apply,hdfix,hnfix z (by omega)]

/-- One more vertical unit than horizontal units, with at least one diagonal. -/
def nearPlacementWord (a b d : ℕ) : List Dir :=
  moveToWord (a+1) b (a+d+1) (b+d+2) ++ transportWord a (b+1) (d+1) 0 ++ parkWord

@[simp] theorem nearPlacementWord_length (a b d : ℕ) :
    (nearPlacementWord a b d).length=8*d+13 := by
  simp only [nearPlacementWord,List.length_append,length_moveToWord,
    transportWord_length,parkWord,List.length_cons,List.length_nil,Nat.dist]
  omega

theorem nearPlacementWord_spec (a b d : ℕ)
    (ha : a+d+2 < n) (hb : b+d+2 < m) :
    ApplicableFrom c(a+1,b) (nearPlacementWord a b d) ∧
    trace c(a+1,b) (nearPlacementWord a b d)=c(a+1,b+1) ∧
    permOf c(a+1,b) (nearPlacementWord a b d) c(a,b+1)=c(a+d+2,b+d+2) ∧
    ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
      permOf c(a+1,b) (nearPlacementWord a b d) z=z := by
  obtain ⟨hna,hnt,hnp,hnfix,_⟩ := navToAbove (n := n) (m := m)
    a (a+1) b (a+d+2) (b+d+2) ha (by omega) hb (by omega)
    (by omega) (by omega) (Or.inl (by omega))
  have hsub : a+d+2-1=a+d+1 := by omega
  simp only [hsub] at hna hnt hnp hnfix
  obtain ⟨hta,htt,htp,htfix⟩ := transportWord_spec (n := n) (m := m)
    a (b+1) (d+1) 0 (by omega) (by omega) (by omega)
  have hx : a+(d+1)=a+d+1 := by omega
  have hx1 : a+(d+1)+1=a+d+2 := by omega
  have hy : b+1+(d+1)=b+d+2 := by omega
  have hy1 : b+1+1=b+2 := by omega
  simp only [Nat.add_zero,hx,hy,hy1] at hta htt htp htfix
  obtain ⟨hpa,hpt,hpfix⟩ := parkWord_spec (n := n) (m := m) a b (by omega) (by omega)
  refine ⟨?_,?_,?_,?_⟩
  · simp only [nearPlacementWord,applicableFrom_append,trace_append,hnt,htt]
    exact ⟨⟨hna,hta⟩,hpa⟩
  · rw [nearPlacementWord,trace_append,trace_append,hnt,htt,hpt]
  · rw [nearPlacementWord,permOf_append,trace_append,hnt,htt,Equiv.Perm.mul_apply,
      hpfix _ (by simp),permOf_append,hnt,Equiv.Perm.mul_apply,htp,hnp]
  · intro z hz
    rw [nearPlacementWord,permOf_append,trace_append,hnt,htt,Equiv.Perm.mul_apply,
      hpfix z (by omega),permOf_append,hnt,Equiv.Perm.mul_apply,
      htfix z (by omega),hnfix z (by omega)]

theorem equalPlacementWord_budget (a b d n : ℕ) (hb : b+d+3 < n) :
    (equalPlacementWord a b d).length+2*(b+1)+7 ≤ 8*n := by
  rw [equalPlacementWord_length]
  omega

theorem nearPlacementWord_budget (a b d n : ℕ) (hb : b+d+2 < n) :
    (nearPlacementWord a b d).length+2*(b+1)+7 ≤ 8*n := by
  rw [nearPlacementWord_length]
  omega

end SlidingPuzzle.Parberry
