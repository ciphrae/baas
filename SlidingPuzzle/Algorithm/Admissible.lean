import SlidingPuzzle.Algorithm.Preparation.MixedStaging
import SlidingPuzzle.Algorithm.Preparation
import SlidingPuzzle.Algorithm.Arrangement
import SlidingPuzzle.Algorithm.Finish
import SlidingPuzzle.Algorithm.Transport

/-! # The algorithm on admissible boards

Composes the four phases of Section 4 into a solution of every reachable board
of side `n = k*s` with `s = side n k ≥ k³` (`Dims n k`). The paper's case is
`n = k⁴`, `s = k³`. Costs are tracked as `A*k²s³ + B*k*s³` (`LeadingBudget`):
`k²s³` is the paper's `k¹¹`, and `B` is a deliberately loose envelope for all
lower-order terms, each of which is at most `k*s³` because `s ≥ k³`.

Preparation and Transport are charged by inefficient moves (`CostedPhase`
bounds *twice* that count, so half-integer coefficients are exact).
Arrangement and Finish end at the target, so they are charged by length and
halved once at the end (`CostedPhase.exists_solution`).

| phase | bound | leading inefficiency |
| --- | --- | --- |
| Preparation | `2*ineff ≤ 23*k²s³ + 9100*k*s³` | 11.5 |
| Transport | `2*ineff ≤ 18*k²s³ + 900*k*s³` | 9 |
| Arrangement | `length ≤ 24*k²s³ + 4100*k*s³` | 12 |
| Finish | `length ≤ 5*k²s³ + 17164*k*s³` | 2.5 |

Total: `2*ineff ≤ 70*k²s³ + 31264*k*s³` (`exists_admissible_solution`). -/
namespace SlidingPuzzle.Algorithm
open SlidingPuzzle.Partition

/-- A budget `leading*k²s³ + remainder*k*s³`. -/
structure LeadingBudget where
  leading : ℕ
  remainder : ℕ

/-- The value of a budget for grid size `k` and square side `s`. -/
def LeadingBudget.eval (b : LeadingBudget) (k s : ℕ) : ℕ :=
  b.leading*(k^2*s^3)+b.remainder*(k*s^3)

/-- Budgets add coefficientwise. -/
def LeadingBudget.add (a b : LeadingBudget) : LeadingBudget :=
  ⟨a.leading+b.leading,a.remainder+b.remainder⟩

/-- A phase from boards satisfying `pre` to boards satisfying `post`, realized
by legal paths whose inefficient moves, doubled, fit in `budget`. -/
def CostedPhase {n : ℕ} [NeZero n] (k : ℕ) (budget : LeadingBudget)
    (pre post : Board n → Prop) : Prop :=
  ∀ B, pre B → ∃ C : Board n, ∃ p : Path B C,
    post C ∧ 2*p.inefficientMoves ≤ budget.eval k (side n k)

theorem CostedPhase.comp {n k : ℕ} [NeZero n] {a b : LeadingBudget}
    {pre mid post : Board n → Prop}
    (h₁ : CostedPhase k a pre mid) (h₂ : CostedPhase k b mid post) :
    CostedPhase k (a.add b) pre post := by
  intro B hB
  obtain ⟨C,p,hC,hp⟩ := h₁ B hB
  obtain ⟨D,q,hD,hq⟩ := h₂ C hC
  refine ⟨D,p.append q,hD,?_⟩
  rw [Path.inefficientMoves_append]
  dsimp [LeadingBudget.eval,LeadingBudget.add] at *
  nlinarith

/-- Append a solving suffix of bounded length. A path ending at the target has
at most half of its moves inefficient, so the suffix is charged at half its
length. -/
theorem CostedPhase.exists_solution {n k : ℕ} [NeZero n] {a b : LeadingBudget}
    {pre mid : Board n → Prop} (h : CostedPhase k a pre mid)
    (hfinish : ∀ C, mid C → ∃ q : Path C (target n), q.length ≤ b.eval k (side n k))
    (B : Board n) (hB : pre B) :
    ∃ p : Path B (target n),
      2*p.inefficientMoves ≤ a.eval k (side n k)+b.eval k (side n k) ∧
      p.length ≤ manhattan B+a.eval k (side n k)+b.eval k (side n k) := by
  obtain ⟨C,p,hC,hp⟩ := h B hB
  obtain ⟨q,hq⟩ := hfinish C hC
  have hhalf := q.inefficientMoves_le_half_length
  have hi : 2*(p.append q).inefficientMoves ≤ a.eval k (side n k)+b.eval k (side n k) := by
    rw [Path.inefficientMoves_append]
    omega
  refine ⟨p.append q,hi,?_⟩
  rw [Path.solution_length]
  omega

/-- Monomials below `k²s³` are at most `k*s³` when `s ≥ k³`. -/
private theorem monomials {k s : ℕ} (hk : 2 ≤ k) (hs : k^3 ≤ s) :
    k^5*s^2 ≤ k^2*s^3 ∧ k^4*s^2 ≤ k*s^3 ∧ k^3*s^2 ≤ k*s^3 ∧ k^2*s^2 ≤ k*s^3 ∧
    k^6*s ≤ k*s^3 ∧ k^5*s ≤ k*s^3 ∧ k^4*s ≤ k*s^3 ∧ k^3*s ≤ k*s^3 ∧
    k^2*s ≤ k*s^3 ∧ k*s ≤ k*s^3 ∧ k^3 ≤ k*s^3 ∧ k^2 ≤ k*s^3 ∧ 1 ≤ k*s^3 := by
  have hk1 : 1 ≤ k := by omega
  have hk2 : k ≤ k^2 := by nlinarith
  have hk3 : k^2 ≤ k^3 := by nlinarith [Nat.mul_le_mul_left k hk2]
  have hks : k ≤ s := by nlinarith
  have hk2s : k^2 ≤ s := by nlinarith
  have hs1 : 1 ≤ s := by nlinarith
  have hss : s ≤ s^2 := by nlinarith
  have hs23 : s^2 ≤ s^3 := by nlinarith [Nat.mul_le_mul_left s hss]
  have hk6 : k^6 ≤ s^2 := by
    have h := Nat.mul_le_mul hs hs
    calc k^6 = k^3*k^3 := by ring
      _ ≤ s*s := h
      _ = s^2 := by ring
  have hk5 : k^5 ≤ s^2 := le_trans (Nat.pow_le_pow_right (by omega) (by omega)) hk6
  have hk4 : k^4 ≤ s^2 := le_trans (Nat.pow_le_pow_right (by omega) (by omega)) hk6
  have hk3' : k^3 ≤ s^2 := le_trans hs hss
  have hk2' : k^2 ≤ s^2 := le_trans hk2s hss
  have hk1' : k ≤ s^2 := le_trans hks hss
  have hks3 : k^2 ≤ s^3 := le_trans hk2' hs23
  have hk13 : k ≤ s^3 := le_trans hk1' hs23
  have hs3 : s ≤ s^3 := le_trans hss hs23
  have h1s3 : 1 ≤ s^3 := le_trans hs1 hs3
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · calc k^5*s^2 = k^2*s^2*k^3 := by ring
      _ ≤ k^2*s^2*s := Nat.mul_le_mul_left _ hs
      _ = k^2*s^3 := by ring
  · calc k^4*s^2 = k*s^2*k^3 := by ring
      _ ≤ k*s^2*s := Nat.mul_le_mul_left _ hs
      _ = k*s^3 := by ring
  · calc k^3*s^2 = k*s^2*k^2 := by ring
      _ ≤ k*s^2*s := Nat.mul_le_mul_left _ hk2s
      _ = k*s^3 := by ring
  · calc k^2*s^2 = k*s^2*k := by ring
      _ ≤ k*s^2*s := Nat.mul_le_mul_left _ hks
      _ = k*s^3 := by ring
  · calc k^6*s = k*s*k^5 := by ring
      _ ≤ k*s*s^2 := Nat.mul_le_mul_left _ hk5
      _ = k*s^3 := by ring
  · calc k^5*s = k*s*k^4 := by ring
      _ ≤ k*s*s^2 := Nat.mul_le_mul_left _ hk4
      _ = k*s^3 := by ring
  · calc k^4*s = k*s*k^3 := by ring
      _ ≤ k*s*s^2 := Nat.mul_le_mul_left _ hk3'
      _ = k*s^3 := by ring
  · calc k^3*s = k*s*k^2 := by ring
      _ ≤ k*s*s^2 := Nat.mul_le_mul_left _ hk2'
      _ = k*s^3 := by ring
  · calc k^2*s = k*s*k := by ring
      _ ≤ k*s*s^2 := Nat.mul_le_mul_left _ hk1'
      _ = k*s^3 := by ring
  · exact Nat.mul_le_mul_left _ hs3
  · calc k^3 = k*k^2 := by ring
      _ ≤ k*s^3 := Nat.mul_le_mul_left _ hks3
  · calc k^2 = k*k := by ring
      _ ≤ k*s^3 := Nat.mul_le_mul_left _ hk13
  · calc 1 ≤ 1*1 := le_refl _
      _ ≤ k*s^3 := Nat.mul_le_mul hk1 h1s3

private theorem preparation_arith {k s : ℕ} (hk : 2 ≤ k) (hs : k^3 ≤ s) :
    (k^3+(k^2+1))*(15*(k*s)^2+3002*(k*s)+1)+18*k^2*(k*s)+24*k^2*(k*s)^2+
      k^5*(8*s^2+4*(k*s)+8*s) ≤ 23*(k^2*s^3)+9100*(k*s^3) := by
  obtain ⟨m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13⟩ := monomials hk hs
  have hexp : (k^3+(k^2+1))*(15*(k*s)^2+3002*(k*s)+1)+18*k^2*(k*s)+24*k^2*(k*s)^2+
      k^5*(8*s^2+4*(k*s)+8*s) =
      23*(k^5*s^2)+39*(k^4*s^2)+15*(k^2*s^2)+3002*(k^4*s)+3020*(k^3*s)+3002*(k*s)+
        4*(k^6*s)+8*(k^5*s)+k^3+k^2+1 := by ring
  rw [hexp]
  omega

private theorem transport_arith {k s : ℕ} (hk : 2 ≤ k) (hs : k^3 ≤ s) :
    2*((k*s)^2*(8*s+(26*(k+2)+s+(k-1)*(26*(k+3)))+69*k^2+13*k+189)) ≤
      18*(k^2*s^3)+900*(k*s^3) := by
  obtain ⟨m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13⟩ := monomials hk hs
  have hcount : k-1+1=k := Nat.sub_add_cancel (by omega)
  have hv : (k-1)*(26*(k+3)) ≤ 26*k^2+52*k := by
    have heq : (k-1)*(k+3)+(k+3)=k*(k+3) := by
      calc (k-1)*(k+3)+(k+3) = (k-1+1)*(k+3) := by ring
        _ = k*(k+3) := by rw [hcount]
    nlinarith
  have he : 8*s+(26*(k+2)+s+(k-1)*(26*(k+3)))+69*k^2+13*k+189 ≤
      9*s+95*k^2+91*k+241 := by omega
  have hmul := Nat.mul_le_mul_left ((k*s)^2) he
  have hexp : (k*s)^2*(9*s+95*k^2+91*k+241) =
      9*(k^2*s^3)+95*(k^4*s^2)+91*(k^3*s^2)+241*(k^2*s^2) := by ring
  rw [hexp] at hmul
  omega

private theorem arrangement_arith {k s : ℕ} (hk : 2 ≤ k) (hs : k^3 ≤ s) :
    (24*(s-k)+2032)*(k^4-k^2)*(k*s)+(24*s+2032)*(k^3-k^2)*(k*s) ≤
      24*(k^2*s^3)+4100*(k*s^3) := by
  obtain ⟨m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13⟩ := monomials hk hs
  have h₁ : (24*(s-k)+2032)*(k^4-k^2)*(k*s) ≤ (24*s+2032)*k^4*(k*s) := by
    gcongr <;> exact Nat.sub_le _ _
  have h₂ : (24*s+2032)*(k^3-k^2)*(k*s) ≤ (24*s+2032)*k^3*(k*s) := by
    gcongr; exact Nat.sub_le _ _
  have hexp : (24*s+2032)*k^4*(k*s)+(24*s+2032)*k^3*(k*s) =
      24*(k^5*s^2)+2032*(k^5*s)+24*(k^4*s^2)+2032*(k^4*s) := by ring
  omega

private theorem finish_arith {k s : ℕ} (hk : 2 ≤ k) (hs : k^3 ≤ s) :
    k^2*(5*s^3+1509*s^2+1505*s+4796)+9354*k^2*(k*s) ≤ 5*(k^2*s^3)+17164*(k*s^3) := by
  obtain ⟨m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13⟩ := monomials hk hs
  have hexp : k^2*(5*s^3+1509*s^2+1505*s+4796)+9354*k^2*(k*s) =
      5*(k^2*s^3)+1509*(k^2*s^2)+1505*(k^2*s)+4796*k^2+9354*(k^3*s) := by ring
  rw [hexp]
  omega

/-- Preparation: staging `7.5*k²s³`, vertical spreading `4*k²s³`. -/
theorem preparation_phase {n k : ℕ} (hk : Dims n k) [NeZero n] :
    CostedPhase (n := n) k ⟨23,9100⟩ Reachable (Prepared hk) := by
  intro B hB
  obtain ⟨C,p,hp,hclear,hrep⟩ := exists_preparation_path hk (representativeStaging_mixed hk) B
  refine ⟨C,p,Prepared.of_path hB p hclear hrep,?_⟩
  have h := preparation_arith hk.two_le hk.cube_le
  rw [hk.mul_side] at h
  have hle := p.inefficientMoves_le_length
  dsimp [LeadingBudget.eval]
  omega

/-- Transport: at most `n²` transfers of `9*s + O(k²)` inefficient moves. -/
theorem transport_phase {n k : ℕ} (hk : Dims n k) [NeZero n] :
    CostedPhase (n := n) k ⟨18,900⟩ (Prepared hk) (Transported hk) := by
  intro B hB
  have hstep := transportStepBound_of_vertical_bound hk (verticalTransportBound hk)
  obtain ⟨D,p,hD,hp⟩ := exists_transport_path_of_step_bound hk hstep B hB
  refine ⟨D,p,hD,?_⟩
  have h := transport_arith hk.two_le hk.cube_le
  rw [hk.mul_side] at h
  dsimp [LeadingBudget.eval]
  omega

/-- Arrangement: two exchange schedules of total length `24*k²s³ + O(k*s³)`. -/
theorem arrangement_bound {n k : ℕ} (hk : Dims n k) [NeZero n]
    (B : Board n) (hB : Transported hk B) :
    ∃ C : Board n, ∃ p : Path B C, Arranged hk C ∧
      p.length ≤ (LeadingBudget.mk 24 4100).eval k (side n k) := by
  obtain ⟨C,p,hp,hblank,hsorted,_⟩ := exists_arrangement_path hk B hB.clear hB.sorted
  refine ⟨C,p,Arranged.of_path hB.reachable p hsorted (by
    rw [hblank]; exact reservoir_subset_square hB.blank_last),?_⟩
  have h := arrangement_arith hk.two_le hk.cube_le
  rw [hk.mul_side] at h
  dsimp [LeadingBudget.eval]
  omega

/-- Finish: `k²` local solves of side `s` with the Parberry solver,
`5*k²s³ + O(k*s³)` moves including access and parity repair. -/
theorem finish_bound {n k : ℕ} (hk : Dims n k) [NeZero n]
    (B : Board n) (hB : Arranged hk B) :
    ∃ p : Path B (target n), p.length ≤ (LeadingBudget.mk 5 17164).eval k (side n k) := by
  obtain ⟨p,hp⟩ := exists_finish_path parberrySolverCost hk B hB
  refine ⟨p,?_⟩
  have h := finish_arith hk.two_le hk.cube_le
  rw [hk.mul_side] at h
  dsimp [LeadingBudget.eval] at *
  omega

/-- Every reachable board of admissible dimensions has a solution with at most
`35*k²s³ + 15632*k*s³` inefficient moves, where `s = side n k`. -/
theorem exists_admissible_solution {n k : ℕ} (hk : Dims n k) [NeZero n]
    (B : Board n) (hB : Reachable B) :
    ∃ p : Path B (target n),
      2*p.inefficientMoves ≤ 70*(k^2*side n k^3)+31264*(k*side n k^3) ∧
      p.length ≤ manhattan B+70*(k^2*side n k^3)+31264*(k*side n k^3) := by
  have hfinish (C : Board n) (hC : Transported hk C) :
      ∃ q : Path C (target n), q.length ≤ (LeadingBudget.mk 29 21264).eval k (side n k) := by
    obtain ⟨D,p,hD,hp⟩ := arrangement_bound hk C hC
    obtain ⟨q,hq⟩ := finish_bound hk D hD
    refine ⟨p.append q,?_⟩
    rw [Path.length_append]
    dsimp [LeadingBudget.eval] at *
    omega
  obtain ⟨p,hi,hl⟩ := ((preparation_phase hk).comp (transport_phase hk)).exists_solution
    hfinish B hB
  refine ⟨p,?_,?_⟩ <;> dsimp [LeadingBudget.eval,LeadingBudget.add] at * <;> omega

end SlidingPuzzle.Algorithm
