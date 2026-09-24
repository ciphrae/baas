import SlidingPuzzle.Parberry.Diagonal

/-! Combine Parberry's six-move diagonals with the checked five-move straight
walk. No repeated blank navigation is charged between these two stages. -/
namespace SlidingPuzzle.Parberry
open Zhong
variable {n m : ℕ}
local notation "c(" a "," b ")" => ((⟨a, by omega⟩ : Fin n), (⟨b, by omega⟩ : Fin m))

/-- Diagonal travel followed by the remaining vertical travel. -/
def transportWord (a b d v : ℕ) : List Dir :=
  diagonalRun d ++ walkAuxR (a+v) b v

@[simp] theorem transportWord_length (a b d v : ℕ) :
    (transportWord a b d v).length = 6*d+5*v+3 := by
  simp [transportWord,walkAuxR_length,Nat.add_assoc]

/-- The route places the tile at `(a,b)` and parks the blank just to its right.
Rows above `a` and columns left of `b` remain fixed. -/
theorem transportWord_spec (a b d v : ℕ) (ha : a+v+d+1 < n)
    (hb : b+d < m) (hb1 : b+1 < m) :
    ApplicableFrom c(a+v+d,b+d) (transportWord a b d v) ∧
    trace c(a+v+d,b+d) (transportWord a b d v) = c(a,b+1) ∧
    permOf c(a+v+d,b+d) (transportWord a b d v) c(a,b) = c(a+v+d+1,b+d) ∧
    ∀ z : Zhong.Cell n m, z.1.val<a ∨ z.2.val<b →
      permOf c(a+v+d,b+d) (transportWord a b d v) z = z := by
  obtain ⟨hda,hdt,hdp,hds⟩ := diagonalRun_spec d (a+v) b ha hb
  obtain ⟨hva,hvt,hvf,hvp⟩ := walkAuxR_spec (n := n) (m := m) (a+v) b v (by omega) (by omega) hb1
  simp only [Nat.add_sub_cancel] at hvt hvp
  refine ⟨?_,?_,?_,?_⟩
  · rw [transportWord,applicableFrom_append,hdt]
    exact ⟨hda,hva⟩
  · rw [transportWord,trace_append,hdt,hvt]
  · rw [transportWord,permOf_append,hdt,Equiv.Perm.mul_apply,hvp,hdp]
  · intro z hz
    rw [transportWord,permOf_append,hdt,Equiv.Perm.mul_apply]
    have hvfix : permOf c(a+v,b) (walkAuxR (a+v) b v) z = z := by
      rcases hz with hz | hz
      · exact hvf z (by omega)
      · apply permOf_apply_of_not_mem_traceSet
        intro hmem
        have hh := walkAuxR_traceSet_col (n := n) (m := m) (a+v) b v (by omega) (by omega) hb1 z hmem
        omega
    rw [hvfix]
    apply permOf_apply_of_not_mem_traceSet
    intro hmem
    have hh := hds z hmem
    omega

/-- Navigate from the preceding row position and then place a tile from the
southeast sector where its vertical displacement dominates. -/
def southeastWord (a b d v : ℕ) : List Dir :=
  moveToWord (a+1) b (a+v+d+1) (b+d+1) ++ transportWord a (b+1) d (v+1)

@[simp] theorem southeastWord_length (a b d v : ℕ) :
    (southeastWord a b d v).length = 8*d+6*v+9 := by
  simp only [southeastWord,List.length_append,length_moveToWord,transportWord_length,Nat.dist]
  omega

/-- The actual blank navigation leaves the distinguished tile untouched and
preserves all completed rows and the completed prefix of the current row. -/
theorem southeastWord_spec (a b d v : ℕ)
    (ha : a+v+d+2 < n) (hb : b+d+1 < m) (hb2 : b+2 < m) :
    ApplicableFrom c(a+1,b) (southeastWord a b d v) ∧
    trace c(a+1,b) (southeastWord a b d v) = c(a,b+2) ∧
    permOf c(a+1,b) (southeastWord a b d v) c(a,b+1) = c(a+v+d+2,b+d+1) ∧
    ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
      permOf c(a+1,b) (southeastWord a b d v) z = z := by
  obtain ⟨hna,hnt,hnp,hnfix,_⟩ := navToAbove (n := n) (m := m)
    a (a+1) b (a+v+d+2) (b+d+1) ha (by omega) hb (by omega)
    (by omega) (by omega) (Or.inl (by omega))
  have hsub : a+v+d+2-1=a+v+d+1 := by omega
  simp only [hsub] at hna hnt hnp hnfix
  obtain ⟨hta,htt,htp,htfix⟩ := transportWord_spec (n := n) (m := m)
    a (b+1) d (v+1) (by omega) (by omega) hb2
  have hc : a+(v+1)+d=a+v+d+1 := by omega
  have hy : b+1+d=b+d+1 := by omega
  have hx : a+(v+1)+d+1=a+v+d+2 := by omega
  simp only [hc,hy] at htp
  simp only [hc,hy] at hta htt htfix
  refine ⟨?_,?_,?_,?_⟩
  · rw [southeastWord,applicableFrom_append,hnt]
    exact ⟨hna,hta⟩
  · rw [southeastWord,trace_append,hnt,htt]
  · rw [southeastWord,permOf_append,hnt,Equiv.Perm.mul_apply,htp,hnp]
  · intro z hz
    rw [southeastWord,permOf_append,hnt,Equiv.Perm.mul_apply,
      htfix z (by omega),hnfix z (by omega)]

/-- Park the blank beneath a placed tile so the next row placement starts
in its required position. -/
def parkWord : List Dir := [.U,.R]

theorem parkWord_spec (a b : ℕ) (ha : a+1 < n) (hb : b+2 < m) :
    ApplicableFrom c(a,b+2) parkWord ∧
    trace c(a,b+2) parkWord=c(a+1,b+1) ∧
    ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+2) →
      permOf c(a,b+2) parkWord z=z := by
  have h1 : neighbor? c(a,b+2) Dir.U=some c(a+1,b+2) := nb_U a (b+2) ha hb
  have h2 : neighbor? c(a+1,b+2) Dir.R=some c(a+1,b+1) := by
    simp
  refine ⟨?_,?_,?_⟩
  · simp only [parkWord,applicableFrom_cons_of_neighbor? h1,
      applicableFrom_cons_of_neighbor? h2]
    trivial
  · simp only [parkWord,trace_cons_of_neighbor? h1,trace_cons_of_neighbor? h2,trace_nil]
  · intro z hz
    have hz0 : z≠c(a,b+2) := by intro he; subst z; simp only at hz; omega
    have hz1 : z≠c(a+1,b+2) := by intro he; subst z; simp only at hz; omega
    have hz2 : z≠c(a+1,b+1) := by intro he; subst z; simp only at hz; omega
    simp only [parkWord,permOf_cons_of_neighbor? h1,permOf_cons_of_neighbor? h2,
      permOf_nil,Equiv.Perm.mul_apply,Equiv.Perm.one_apply,
      Equiv.swap_apply_of_ne_of_ne hz1 hz2,Equiv.swap_apply_of_ne_of_ne hz0 hz1]

/-- Complete the placement and establish the starting blank position for the
next column, still paying only six moves per diagonal unit. -/
def southeastPlacementWord (a b d v : ℕ) : List Dir := southeastWord a b d v ++ parkWord

@[simp] theorem southeastPlacementWord_length (a b d v : ℕ) :
    (southeastPlacementWord a b d v).length=8*d+6*v+11 := by
  simp [southeastPlacementWord,parkWord]

theorem southeastPlacementWord_spec (a b d v : ℕ)
    (ha : a+v+d+2 < n) (hb : b+d+1 < m) (hb2 : b+2 < m) :
    ApplicableFrom c(a+1,b) (southeastPlacementWord a b d v) ∧
    trace c(a+1,b) (southeastPlacementWord a b d v)=c(a+1,b+1) ∧
    permOf c(a+1,b) (southeastPlacementWord a b d v) c(a,b+1)=c(a+v+d+2,b+d+1) ∧
    ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
      permOf c(a+1,b) (southeastPlacementWord a b d v) z=z := by
  obtain ⟨hsa,hst,hsp,hsfix⟩ := southeastWord_spec a b d v ha hb hb2
  obtain ⟨hpa,hpt,hpfix⟩ := parkWord_spec (n := n) (m := m) a b (by omega) hb2
  refine ⟨?_,?_,?_,?_⟩
  · rw [southeastPlacementWord,applicableFrom_append,hst]
    exact ⟨hsa,hpa⟩
  · rw [southeastPlacementWord,trace_append,hst,hpt]
  · rw [southeastPlacementWord,permOf_append,hst,Equiv.Perm.mul_apply,
      hpfix _ (by simp),hsp]
  · intro z hz
    rw [southeastPlacementWord,permOf_append,hst,Equiv.Perm.mul_apply,
      hpfix z (by omega),hsfix z hz]

/-- This sector meets the paper's per-tile budget after including blank parking. -/
theorem southeastPlacementWord_budget (a b d v n : ℕ)
    (ha : a+v+d+2 < n) (hb : b+d+1 < n) :
    (southeastPlacementWord a b d v).length+2*(b+1)+7 ≤ 8*n := by
  rw [southeastPlacementWord_length]
  omega

end SlidingPuzzle.Parberry
