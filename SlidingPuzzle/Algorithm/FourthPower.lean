import SlidingPuzzle.Algorithm.Preparation.MixedStaging
import SlidingPuzzle.Algorithm.Preparation
import SlidingPuzzle.Algorithm.Arrangement
import SlidingPuzzle.Algorithm.Finish
import SlidingPuzzle.Algorithm.Transport

/-! # The algorithm on boards of side `k⁴`

Composes the four phases of Section 4 into a solution of every reachable
`k⁴ × k⁴` board. Costs are tracked as `A*k¹¹ + B*k¹⁰` (`LeadingBudget`); the
leading coefficient `A` is the quantity of interest and `B` is a deliberately
loose envelope for all lower-order terms.

Preparation and Transport are charged by inefficient moves (`CostedPhase`
bounds *twice* that count, so half-integer coefficients are exact).
Arrangement and Finish end at the target, so they are charged by length and
halved once at the end (`CostedPhase.exists_solution`).

| phase | bound | leading inefficiency |
| --- | --- | --- |
| Preparation | `2*ineff ≤ 23*k¹¹ + 700*k¹⁰` | 11.5 |
| Transport | `2*ineff ≤ 18*k¹¹ + 380*k¹⁰` | 9 |
| Arrangement | `length ≤ 24*k¹¹ + 786*k¹⁰` | 12 |
| Finish | `length ≤ 5*k¹¹ + 17164*k¹⁰` | 2.5 |

Total: `2*ineff ≤ 70*k¹¹ + 19030*k¹⁰` (`exists_fourth_power_solution`). -/
namespace SlidingPuzzle.Algorithm
open SlidingPuzzle.Partition

/-- A budget `leading*k¹¹ + remainder*k¹⁰`. -/
structure LeadingBudget where
  leading : ℕ
  remainder : ℕ

/-- The value of a budget at `k`. -/
def LeadingBudget.eval (b : LeadingBudget) (k : ℕ) : ℕ :=
  b.leading*k^11+b.remainder*k^10

/-- Budgets add coefficientwise. -/
def LeadingBudget.add (a b : LeadingBudget) : LeadingBudget :=
  ⟨a.leading+b.leading,a.remainder+b.remainder⟩

/-- A phase from boards satisfying `pre` to boards satisfying `post`, realized
by legal paths whose inefficient moves, doubled, fit in `budget`. -/
def CostedPhase {n : ℕ} [NeZero n] (k : ℕ) (budget : LeadingBudget)
    (pre post : Board n → Prop) : Prop :=
  ∀ B, pre B → ∃ C : Board n, ∃ p : Path B C,
    post C ∧ 2*p.inefficientMoves ≤ budget.eval k

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
    (hfinish : ∀ C, mid C → ∃ q : Path C (target n), q.length ≤ b.eval k)
    (B : Board n) (hB : pre B) :
    ∃ p : Path B (target n),
      2*p.inefficientMoves ≤ a.eval k+b.eval k ∧
      p.length ≤ manhattan B+a.eval k+b.eval k := by
  obtain ⟨C,p,hC,hp⟩ := h B hB
  obtain ⟨q,hq⟩ := hfinish C hC
  have hhalf := q.inefficientMoves_le_half_length
  have hi : 2*(p.append q).inefficientMoves ≤ a.eval k+b.eval k := by
    rw [Path.inefficientMoves_append]
    omega
  refine ⟨p.append q,hi,?_⟩
  rw [Path.solution_length]
  omega

/-- The mixed-prefix staging has leading length `7.5*k¹¹` and vertical spreading
`4*k¹¹`, so twice the inefficiency is at most `23*k¹¹` plus lower order.
Representative access and horizontal spreading are lower order. -/
theorem preparation_phase (k : ℕ) (hk : 2 ≤ k) [NeZero (k^4)] :
    CostedPhase (n := k^4) k ⟨23,700⟩ Reachable (Prepared hk) := by
  intro B hB
  obtain ⟨C,p,hp,hclear,hrep⟩ := exists_preparation_path hk (representativeStaging_mixed hk) B
  refine ⟨C,p,Prepared.of_path hB p hclear hrep,?_⟩
  have hk2 : 4 ≤ k^2 := by nlinarith
  have h9 : 2*k^9 ≤ k^10 := by
    have := Nat.mul_le_mul_left (k^9) hk; nlinarith [show k^9*k = k^10 by ring]
  have h8 : 4*k^8 ≤ k^10 := by
    have := Nat.mul_le_mul_left (k^8) hk2; nlinarith [show k^8*k^2 = k^10 by ring]
  have h7 : 8*k^7 ≤ k^10 := by
    have := Nat.mul_le_mul_left (k^7) (Nat.pow_le_pow_left hk 3)
    nlinarith [show k^7*k^3 = k^10 by ring]
  have h6 : 16*k^6 ≤ k^10 := by
    have := Nat.mul_le_mul_left (k^6) (Nat.pow_le_pow_left hk 4)
    nlinarith [show k^6*k^4 = k^10 by ring]
  have h4 : 64*k^4 ≤ k^10 := by
    have := Nat.mul_le_mul_left (k^4) (Nat.pow_le_pow_left hk 6)
    nlinarith [show k^4*k^6 = k^10 by ring]
  have h3 : k^3 ≤ k^10 := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : k^2 ≤ k^10 := Nat.pow_le_pow_right (by omega) (by omega)
  have h0 : 1 ≤ k^10 := Nat.one_le_pow _ _ (by omega)
  have hexp : (k^3+(k^2+1))*(15*(k^4)^2+3002*k^4+1) =
      15*k^11+15*k^10+15*k^8+3002*k^7+3002*k^6+3002*k^4+k^3+k^2+1 := by ring
  have hle := p.inefficientMoves_le_length
  dsimp [LeadingBudget.eval]
  omega

/-- The exact transfer cost retains its quadratic and linear terms. Entry
starts from the top of the reservoir and the exit carries the source tile, so
each transfer has leading cost `9*k³`: one unit each for the reservoir slide,
horizontal and vertical travel, and six for the exit walk and carry. -/
theorem transport_phase (k : ℕ) (hk : 2 ≤ k) [NeZero (k^4)] :
    CostedPhase (n := k^4) k ⟨18,380⟩ (Prepared hk) (Transported hk) := by
  intro B hB
  have hstep := transportStepBound_of_vertical_bound hk rfl (verticalTransportBound hk rfl)
  obtain ⟨D,p,hD,hp⟩ := exists_transport_path_of_step_bound hk rfl hstep B hB
  refine ⟨D,p,hD,?_⟩
  have hcount : k-1+1=k := Nat.sub_add_cancel (by omega)
  have heq : (k-1)*(k+3)+(k+3)=k*(k+3) := by nlinarith [hcount]
  have hvertical : 26*(k+2)+k^3+(k-1)*(26*(k+3))+26 = k^3+26*k^2+78*k := by
    nlinarith [heq]
  have h9 : 2*k^9 ≤ k^10 := by
    nlinarith [Nat.mul_le_mul_right (k^9) hk, show k^10 = k*k^9 by ring]
  have h8 : 4*k^8 ≤ k^10 := by
    nlinarith [Nat.mul_le_mul_right (k^8) (Nat.pow_le_pow_left hk 2), show k^10 = k^2*k^8 by ring]
  dsimp [LeadingBudget.eval]
  have he : 8*k^3+(26*(k+2)+k^3+(k-1)*(26*(k+3)))+69*k^2+13*k+189 ≤
      9*k^3+95*k^2+91*k+163 := by omega
  have hmul := Nat.mul_le_mul_left ((k^4)^2) he
  have hexp : (k^4)^2*(9*k^3+95*k^2+91*k+163) = 9*k^11+95*k^10+91*k^9+163*k^8 := by ring
  nlinarith

/-- Arrangement: two exchange schedules of total length `24*k¹¹ + O(k¹⁰)`. -/
theorem arrangement_bound (k : ℕ) (hk : 2 ≤ k) [NeZero (k^4)]
    (B : Board (k^4)) (hB : Transported hk B) :
    ∃ C : Board (k^4), ∃ p : Path B C, Arranged hk C ∧
      p.length ≤ (LeadingBudget.mk 24 786).eval k := by
  obtain ⟨C,p,hp,hblank,hsorted,_⟩ := exists_arrangement_path hk B hB.clear hB.sorted
  refine ⟨C,p,Arranged.of_path hB.reachable p hsorted (by
    rw [hblank]; exact reservoir_subset_square hB.blank_last),?_⟩
  have h₁ : (24*(k^3-k)+2032)*(k^4-k^2)*k^4 ≤ (24*k^3+2032)*k^4*k^4 := by
    gcongr <;> exact Nat.sub_le _ _
  have h₂ : (24*k^3+2032)*(k^3-k^2)*k^4 ≤ (24*k^3+2032)*k^3*k^4 := by
    gcongr; exact Nat.sub_le _ _
  have h8 : 4*k^8 ≤ k^10 := by nlinarith [Nat.mul_le_mul_right (k^8) (Nat.pow_le_pow_left hk 2)]
  have h7 : 8*k^7 ≤ k^10 := by nlinarith [Nat.mul_le_mul_right (k^7) (Nat.pow_le_pow_left hk 3)]
  have hsum := hp.trans (Nat.add_le_add h₁ h₂)
  apply hsum.trans
  dsimp [LeadingBudget.eval]
  nlinarith only [h8,h7]

/-- Finish: `k²` local solves of side `k³` with the Parberry solver,
`5*k¹¹ + O(k¹⁰)` moves including access and parity repair. -/
theorem finish_bound (k : ℕ) (hk : 2 ≤ k) [NeZero (k^4)]
    (B : Board (k^4)) (hB : Arranged hk B) :
    ∃ p : Path B (target (k^4)), p.length ≤ (LeadingBudget.mk 5 17164).eval k := by
  obtain ⟨p,hp⟩ := exists_finish_path parberrySolverCost hk B hB
  refine ⟨p,?_⟩
  have h8 : k^8 ≤ k^10 := Nat.pow_le_pow_right (by omega) (by omega)
  have h5 : k^5 ≤ k^10 := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : k^2 ≤ k^10 := Nat.pow_le_pow_right (by omega) (by omega)
  have h6 : k^6 ≤ k^10 := Nat.pow_le_pow_right (by omega) (by omega)
  dsimp [LeadingBudget.eval] at *
  nlinarith

/-- Every reachable `k⁴ × k⁴` board, `k ≥ 2`, has a solution with at most
`35*k¹¹ + 9515*k¹⁰` inefficient moves. -/
theorem exists_fourth_power_solution (k : ℕ) (hk : 2 ≤ k) [NeZero (k^4)]
    (B : Board (k^4)) (hB : Reachable B) :
    ∃ p : Path B (target (k^4)),
      2*p.inefficientMoves ≤ 70*k^11+19030*k^10 ∧
      p.length ≤ manhattan B+70*k^11+19030*k^10 := by
  have hfinish (C : Board (k^4)) (hC : Transported hk C) :
      ∃ q : Path C (target (k^4)), q.length ≤ (LeadingBudget.mk 29 17950).eval k := by
    obtain ⟨D,p,hD,hp⟩ := arrangement_bound k hk C hC
    obtain ⟨q,hq⟩ := finish_bound k hk D hD
    refine ⟨p.append q,?_⟩
    rw [Path.length_append]
    dsimp [LeadingBudget.eval] at *
    omega
  obtain ⟨p,hi,hl⟩ := ((preparation_phase k hk).comp (transport_phase k hk)).exists_solution
    hfinish B hB
  refine ⟨p,?_,?_⟩ <;> dsimp [LeadingBudget.eval,LeadingBudget.add] at * <;> omega

end SlidingPuzzle.Algorithm
