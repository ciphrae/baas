import SlidingPuzzle.Algorithm.Parberry.Reflection

/-! Left-of-target placements use northeast transport below the protected row,
followed by a short insertion. -/
namespace SlidingPuzzle.Parberry
open Zhong
variable {n m : ℕ}
local notation "c(" a "," b ")" => ((⟨a, by omega⟩ : Fin n), (⟨b, by omega⟩ : Fin m))

def westTallWord (m a b d v : ℕ) : List Dir :=
  moveToWord (a+1) b (a+v+d+2) (b-d) ++
    eastTransportWord m (a+1) (b+1) (d+1) v ++ adjacentBelowWord

@[simp] theorem westTallWord_length (m a b d v : ℕ) (hd : d ≤ b) :
    (westTallWord m a b d v).length=8*d+6*v+17 := by
  simp only [westTallWord,List.length_append,length_moveToWord,
    eastTransportWord_length,adjacentBelowWord,List.length_cons,List.length_nil,Nat.dist]
  omega

theorem westTallWord_spec (a b d v : ℕ) (ha : a+v+d+3 < n)
    (hb : b+2 < m) (hd : d ≤ b) :
    ApplicableFrom c(a+1,b) (westTallWord m a b d v) ∧
    trace c(a+1,b) (westTallWord m a b d v)=c(a+1,b+1) ∧
    permOf c(a+1,b) (westTallWord m a b d v) c(a,b+1)=c(a+v+d+3,b-d) ∧
    ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
      permOf c(a+1,b) (westTallWord m a b d v) z=z := by
  obtain ⟨hna,hnt,hnp,hnfix,_⟩ := navToAbove (n := n) (m := m)
    a (a+1) b (a+v+d+3) (b-d) ha (by omega) (by omega) (by omega)
    (by omega) (by omega) (Or.inr (by omega))
  have hsub : a+v+d+3-1=a+v+d+2 := by omega
  simp only [hsub] at hna hnt hnp hnfix
  obtain ⟨hta,htt,htp,htfix⟩ := eastTransportWord_spec (n := n) (m := m)
    (a+1) (b+1) (d+1) v (by omega) (by omega) (by omega) (by omega)
  have hx : a+1+v+(d+1)=a+v+d+2 := by omega
  have hx1 : a+1+v+(d+1)+1=a+v+d+3 := by omega
  have hy : b+1-(d+1)=b-d := by omega
  simp only [hx,hx1,hy,Nat.add_sub_cancel] at hta htt htp htfix
  obtain ⟨hea,het,hep,hefix⟩ := adjacentBelowWord_spec (n := n) (m := m) a b (by omega) hb
  refine ⟨?_,?_,?_,?_⟩
  · simp only [westTallWord,applicableFrom_append,trace_append,hnt,htt]
    exact ⟨⟨hna,hta⟩,hea⟩
  · rw [westTallWord,trace_append,trace_append,hnt,htt,het]
  · rw [westTallWord,permOf_append,trace_append,hnt,htt,Equiv.Perm.mul_apply,
      hep,permOf_append,hnt,Equiv.Perm.mul_apply,htp,hnp]
  · intro z hz
    rw [westTallWord,permOf_append,trace_append,hnt,htt,Equiv.Perm.mul_apply,
      hefix z hz,permOf_append,hnt,Equiv.Perm.mul_apply,
      htfix z (by omega),hnfix z (by omega)]

theorem westTallWord_budget (a b d v n : ℕ) (ha : a+v+d+3 < n)
    (hb : b+2 < n) (hd : d ≤ b) :
    (westTallWord n a b d v).length+2*(n-(b+1))+7 ≤ 8*n := by
  rw [westTallWord_length n a b d v hd]
  omega

/-- The initial route stops to the right of the tile and never crosses it. -/
def westWideWord (m a b d v : ℕ) : List Dir :=
  moveToWord (a+1) b (a+d+1) (b+1-v-d) ++
    eastHorizontalWord m (a+1) (b+1) d v ++ lowerInsertionWord

@[simp] theorem westWideWord_length (m a b d v : ℕ)
    (hd : v+d ≤ b) (hpos : 1 ≤ v+d) :
    (westWideWord m a b d v).length=8*d+6*v+11 := by
  simp only [westWideWord,List.length_append,length_moveToWord,
    eastHorizontalWord_length,lowerInsertionWord,List.length_cons,List.length_nil,Nat.dist]
  omega

theorem westWideWord_spec (a b d v : ℕ) (ha : a+d+1 < n) (ha2 : a+2 < n)
    (hb : b+2 < m) (hd : v+d ≤ b) (hpos : 1 ≤ v+d) :
    ApplicableFrom c(a+1,b) (westWideWord m a b d v) ∧
    trace c(a+1,b) (westWideWord m a b d v)=c(a+1,b+1) ∧
    permOf c(a+1,b) (westWideWord m a b d v) c(a,b+1)=c(a+d+1,b-v-d) ∧
    ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
      permOf c(a+1,b) (westWideWord m a b d v) z=z := by
  have hna := applicableFrom_moveToWord (a+1) b (a+d+1) (b+1-v-d)
    ha (by omega : b+1-v-d < m) (by omega) (by omega)
  have hnt := trace_moveToWord (a+1) b (a+d+1) (b+1-v-d)
    ha (by omega : b+1-v-d < m) (by omega) (by omega)
  have hnp : permOf c(a+1,b) (moveToWord (a+1) b (a+d+1) (b+1-v-d))
      c(a+d+1,b-v-d)=c(a+d+1,b-v-d) := by
    apply permOf_apply_of_not_mem_traceSet
    intro hmem
    have hh := moveToWord_traceSet_col (a+1) b (a+d+1) (b+1-v-d)
      ha (by omega : b+1-v-d < m) (by omega) (by omega) _ hmem
    simp only [Fin.val_mk] at hh
    omega
  have hnfix := moveToWord_fixes_of_row_lt (lo := a+1) ha
    (by omega : b+1-v-d < m) (by omega : a+1 < n) (by omega : b < m)
    (by omega) (by omega)
  obtain ⟨hta,htt,htp,htfix⟩ := eastHorizontalWord_spec (n := n) (m := m)
    (a+1) (b+1) d v (by omega) (by omega) (by omega) (by omega)
  have hx : a+1+d=a+d+1 := by omega
  have hy : b+1-v-d-1=b-v-d := by omega
  simp only [hx,hy] at hta htt htp htfix
  obtain ⟨hea,het,hep,hefix⟩ := lowerInsertionWord_spec (n := n) (m := m) a b ha2 hb
  refine ⟨?_,?_,?_,?_⟩
  · simp only [westWideWord,applicableFrom_append,trace_append,hnt,htt]
    exact ⟨⟨hna,hta⟩,hea⟩
  · rw [westWideWord,trace_append,trace_append,hnt,htt,het]
  · rw [westWideWord,permOf_append,trace_append,hnt,htt,Equiv.Perm.mul_apply,
      hep,permOf_append,hnt,Equiv.Perm.mul_apply,htp,hnp]
  · intro z hz
    rw [westWideWord,permOf_append,trace_append,hnt,htt,Equiv.Perm.mul_apply,
      hefix z hz,permOf_append,hnt,Equiv.Perm.mul_apply,
      htfix z (by omega),hnfix z (by omega)]

theorem westWideWord_budget (a b d v n : ℕ) (hb : b+2 < n)
    (hd : v+d ≤ b) (hpos : 1 ≤ v+d) :
    (westWideWord n a b d v).length+2*(n-(b+1))+7 ≤ 8*n := by
  rw [westWideWord_length n a b d v hd hpos]
  omega

/-- The near-diagonal west case finishes its last diagonal below the target row. -/
def westNearWord (a b d : ℕ) : List Dir :=
  moveToWord (a+1) b (a+d+1) (b-d) ++ (diagonalRun d).map reflDir ++ adjacentWestWord

@[simp] theorem westNearWord_length (a b d : ℕ) (hd : d ≤ b) :
    (westNearWord a b d).length=8*d+11 := by
  simp only [westNearWord,List.length_append,length_moveToWord,
    List.length_map,diagonalRun_length,adjacentWestWord,List.length_cons,List.length_nil,Nat.dist]
  omega

theorem westNearWord_spec (a b d : ℕ) (ha : a+d+2 < n)
    (hb : b+2 < m) (hd : d ≤ b) :
    ApplicableFrom c(a+1,b) (westNearWord a b d) ∧
    trace c(a+1,b) (westNearWord a b d)=c(a+1,b+1) ∧
    permOf c(a+1,b) (westNearWord a b d) c(a,b+1)=c(a+d+2,b-d) ∧
    ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
      permOf c(a+1,b) (westNearWord a b d) z=z := by
  obtain ⟨hna,hnt,hnp,hnfix,_⟩ := navToAbove (n := n) (m := m)
    a (a+1) b (a+d+2) (b-d) ha (by omega) (by omega) (by omega)
    (by omega) (by omega) (Or.inr (by omega))
  have hsub : a+d+2-1=a+d+1 := by omega
  simp only [hsub] at hna hnt hnp hnfix
  obtain ⟨hda,hdt,hdp,hdfix⟩ := eastDiagonalRun_spec (n := n) (m := m)
    d (a+1) b (by omega) (by omega) hd
  have hx : a+1+d=a+d+1 := by omega
  have hx1 : a+1+d+1=a+d+2 := by omega
  simp only [hx,hx1] at hda hdt hdp hdfix
  obtain ⟨hea,het,hep,hefix⟩ := adjacentWestWord_spec (n := n) (m := m) a b (by omega) hb
  refine ⟨?_,?_,?_,?_⟩
  · simp only [westNearWord,applicableFrom_append,trace_append,hnt,hdt]
    exact ⟨⟨hna,hda⟩,hea⟩
  · rw [westNearWord,trace_append,trace_append,hnt,hdt,het]
  · rw [westNearWord,permOf_append,trace_append,hnt,hdt,Equiv.Perm.mul_apply,
      hep,permOf_append,hnt,Equiv.Perm.mul_apply,hdp,hnp]
  · intro z hz
    rw [westNearWord,permOf_append,trace_append,hnt,hdt,Equiv.Perm.mul_apply,
      hefix z hz,permOf_append,hnt,Equiv.Perm.mul_apply,
      hdfix z (by omega),hnfix z (by omega)]

theorem westNearWord_budget (a b d n : ℕ) (hb : b+2 < n) (hd : d ≤ b) :
    (westNearWord a b d).length+2*(n-(b+1))+7 ≤ 8*n := by
  rw [westNearWord_length a b d hd]
  omega

end SlidingPuzzle.Parberry
