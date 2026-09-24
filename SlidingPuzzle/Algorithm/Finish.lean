import SlidingPuzzle.Algorithm.FinishBlocks
import SlidingPuzzle.Algorithm.FinishAccess
import SlidingPuzzle.Algorithm.ResidualReachability
import SlidingPuzzle.Algorithm.PhaseContracts

/-! Finish without recursive subdivision: one cubic solve per partition square. -/
namespace SlidingPuzzle.Partition
variable {k : ℕ} [NeZero (k^4)]

/-- Solve an arranged board by direct cubic block solvers. Local parity defects
are moved to the final square, whose reachability follows from global reachability
once every other square is solved. -/
theorem exists_finish_path_of_solver {K : ℕ} (hsolver : CubicSolverBound K)
    (hk : 2 ≤ k) (B : Board (k^4)) (hB : Arranged hk B) :
    ∃ p : Path B (target (k^4)), p.length ≤ (K+220)*k^11 := by
  let : NeZero (k^3) := ⟨by positivity⟩
  have hm : 8 ≤ k^3 := by nlinarith [Nat.pow_le_pow_left hk 3]
  obtain ⟨A,p,hp,hbA,hA⟩ := exists_finish_blank_access hk B hB.sorted hB.blank_last
  obtain ⟨u,v,huv,hu,hv,hu0,hv0⟩ := exists_finish_buffers hk
  obtain ⟨D,q,hq,hbD,hD,hsolved⟩ := exists_finish_square_schedule_of_solver hsolver hk A hA hbA
    u v huv hu hv hu0 hv0
  let d := (k-1)*k^3
  have hd : d+k^3=k^4 := by
    dsimp [d]
    have h := Nat.sub_add_cancel (by omega : 1 ≤ k)
    calc
      (k-1)*k^3+k^3 = (k-1+1)*k^3 := by ring
      _ = k^4 := by rw [h]; ring
  have hprefix : ∀ x y : Fin (k^4), x.val<d ∨ y.val<d → D (x,y)=target (k^4) (x,y) := by
    intro x y hxy
    obtain ⟨i,hi⟩ := square_covers hk rfl (x,y)
    apply hsolved i _ (x,y) hi
    intro he
    rw [he] at hi
    simp only [square,lastGroup,groupRow,groupCol,Equiv.symm_apply_apply] at hi
    dsimp [d] at hxy
    omega
  have hreach : Reachable D := by
    obtain ⟨r⟩ := hB.reachable
    exact ⟨(r.append p).append q⟩
  obtain ⟨R,hR⟩ := exists_residual_board d hd D hprefix
  have hrR : Reachable R := residual_reachable (by omega) d hd D hprefix R hR hreach
  obtain ⟨r,hr⟩ := hsolver hm ⟨R,hrR⟩
  obtain ⟨s,hs⟩ := residual_solution_lifts d hd D hprefix R hR r
  refine ⟨(p.append q).append s,?_⟩
  simp only [Path.length_append,hs]
  have hrr : r.length ≤ K*k^9 := by simpa [← pow_mul] using hr
  have hcount : k*k-1+1 = k*k := Nat.sub_add_cancel (by nlinarith)
  have htotal : q.length+r.length ≤ K*k^11+9352*(k*k-1)*k^4 := by
    calc
      q.length+r.length ≤ (k*k-1)*(K*k^9+9352*k^4)+K*k^9 :=
        Nat.add_le_add hq hrr
      _ = K*(k*k-1+1)*k^9+9352*(k*k-1)*k^4 := by ring
      _ = K*k^11+9352*(k*k-1)*k^4 := by rw [hcount]; ring
  have hsmall : 9352*(k*k-1)*k^4+2*k^4 ≤ 220*k^11 := by
    by_cases hk3 : k = 2
    · subst k
      norm_num
    · have hk3' : 3 ≤ k := by omega
      have hk46 : k^4 ≤ k^6 := by nlinarith [Nat.pow_le_pow_left hk 2]
      have hlow : 9352*(k*k-1)*k^4+2*k^4 ≤ 9354*k^6 := by
        have hsub : k*k-1 ≤ k*k := Nat.sub_le _ _
        have hpart : 9352*(k*k-1)*k^4 ≤ 9352*(k*k)*k^4 := by
          calc
            _ = 9352*((k*k-1)*k^4) := by ring
            _ ≤ 9352*((k*k)*k^4) :=
              Nat.mul_le_mul_left 9352 (Nat.mul_le_mul_right (k^4) hsub)
            _ = _ := by ring
        calc
          9352*(k*k-1)*k^4+2*k^4 ≤ 9352*(k*k)*k^4+2*k^6 := by
            exact Nat.add_le_add hpart (Nat.mul_le_mul_left 2 hk46)
          _ = 9354*k^6 := by ring
      have hk5 : 243 ≤ k^5 := by nlinarith [Nat.pow_le_pow_left hk3' 5]
      calc
        9352*(k*k-1)*k^4+2*k^4 ≤ 9354*k^6 := hlow
        _ ≤ 220*k^11 := by
          calc
            9354*k^6 ≤ 53460*k^6 := Nat.mul_le_mul_right _ (by omega)
            _ = (220*243)*k^6 := by ring
            _ ≤ (220*k^5)*k^6 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hk5)
            _ = 220*k^11 := by ring
  have hcombined : 9352*(k*k-1)*k^4+p.length ≤ 220*k^11 := by
    have hp' : p.length ≤ 2*k^4 := hp
    omega
  nlinarith

/-- Specialize the solver-parametric construction to the checked cubic solver. -/
theorem exists_finish_path (hk : 2 ≤ k) (B : Board (k^4)) (hB : Arranged hk B) :
    ∃ p : Path B (target (k^4)), p.length ≤ 747*k^11 := by
  exact exists_finish_path_of_solver cubicSolverBound_current hk B hB

end SlidingPuzzle.Partition

namespace SlidingPuzzle.Algorithm
open SlidingPuzzle.Partition

/-- Finish has at most half as many inefficient moves as total moves, since its
endpoint is the target. Local square solvability is established in the construction. -/
theorem finishContract : FinishContract 374 := by
  intro k hk
  let : NeZero (k^4) := ⟨by positivity⟩
  intro B hB
  obtain ⟨p,hp⟩ := exists_finish_path hk B hB
  refine ⟨target (k^4),p,rfl,?_⟩
  have h := p.inefficientMoves_le_half_length
  omega
end SlidingPuzzle.Algorithm
