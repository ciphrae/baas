import SlidingPuzzle.Algorithm.Preparation.MixedStaging
import SlidingPuzzle.Algorithm.Preparation
import SlidingPuzzle.Algorithm.Arrangement
import SlidingPuzzle.Algorithm.Finish
import SlidingPuzzle.Algorithm.Transport
import SlidingPuzzle.Algorithm.BoardCounts

/-! # The algorithm on admissible boards

Composes the four phases of Section 4 into a solution of every reachable board
of side `n = k*s` with `s = side n k ≥ k³` (`Dims n k`). The paper's case is
`n = k⁴`, `s = k³`. Costs are tracked as `A*k²s³ + C*k⁵s² + B*k*s³`
(`LeadingBudget`). Both `k²s³ = n³/k` and `k⁵s² = k³n²` are the paper's `k¹¹`
when `s = k³`; they are kept apart so that `GeneralSize` can balance them by
the choice of `k`. `B` is a deliberately loose envelope for all lower-order
terms, each of which is at most `k*s³` because `s ≥ k³`.

Preparation and Transport are charged by inefficient moves (`CostedPhase`
bounds *twice* that count, so half-integer coefficients are exact).
Arrangement and Finish end at the target, so they are charged by length and
halved once at the end (`CostedPhase.exists_solution`).

| phase | bound |
| --- | --- |
| Preparation | `2*ineff ≤ 23*k⁵s² + 9100*k*s³` |
| Transport | `2*ineff ≤ 11*k²s³ + 900*k*s³` |
| Arrangement | `length ≤ 24*k⁵s² + 4100*k*s³` |
| Finish | `length ≤ 5*k²s³ + 17164*k*s³` |

Total: `2*ineff ≤ 16*k²s³ + 47*k⁵s² + 31264*k*s³` (`exists_admissible_solution`). -/
namespace SlidingPuzzle.Algorithm
open SlidingPuzzle.Partition

/-- A budget `cubic*k²s³ + corridor*k⁵s² + remainder*k*s³`. -/
structure LeadingBudget where
  cubic : ℕ
  corridor : ℕ
  remainder : ℕ

/-- The value of a budget for grid size `k` and square side `s`. -/
def LeadingBudget.eval (b : LeadingBudget) (k s : ℕ) : ℕ :=
  b.cubic*(k^2*s^3)+b.corridor*(k^5*s^2)+b.remainder*(k*s^3)

/-- Budgets add coefficientwise. -/
def LeadingBudget.add (a b : LeadingBudget) : LeadingBudget :=
  ⟨a.cubic+b.cubic,a.corridor+b.corridor,a.remainder+b.remainder⟩

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
theorem CostedPhase.exists_solution {n k : ℕ} [NeZero n] {a : LeadingBudget}
    {pre mid : Board n → Prop} (h : CostedPhase k a pre mid) {F : ℕ}
    (hfinish : ∀ C, mid C → ∃ q : Path C (target n), q.length ≤ F)
    (B : Board n) (hB : pre B) :
    ∃ p : Path B (target n),
      2*p.inefficientMoves ≤ a.eval k (side n k)+F ∧
      p.length ≤ manhattan B+a.eval k (side n k)+F := by
  obtain ⟨C,p,hC,hp⟩ := h B hB
  obtain ⟨q,hq⟩ := hfinish C hC
  have hhalf := q.inefficientMoves_le_half_length
  have hi : 2*(p.append q).inefficientMoves ≤ a.eval k (side n k)+F := by
    rw [Path.inefficientMoves_append]
    omega
  refine ⟨p.append q,hi,?_⟩
  rw [Path.solution_length]
  omega

/-- Lower-order monomials are at most `k*s³` when `s ≥ k³`. -/
private theorem monomials {k s : ℕ} (hk : 2 ≤ k) (hs : k^3 ≤ s) :
    k^4*s^2 ≤ k*s^3 ∧ k^3*s^2 ≤ k*s^3 ∧ k^2*s^2 ≤ k*s^3 ∧
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
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
      k^5*(8*s^2+4*(k*s)+8*s) ≤ 23*(k^5*s^2)+9100*(k*s^3) := by
  obtain ⟨m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13⟩ := monomials hk hs
  have hexp : (k^3+(k^2+1))*(15*(k*s)^2+3002*(k*s)+1)+18*k^2*(k*s)+24*k^2*(k*s)^2+
      k^5*(8*s^2+4*(k*s)+8*s) =
      23*(k^5*s^2)+39*(k^4*s^2)+15*(k^2*s^2)+3002*(k^4*s)+3020*(k^3*s)+3002*(k*s)+
        4*(k^6*s)+8*(k^5*s)+k^3+k^2+1 := by ring
  rw [hexp]
  omega

private theorem transport_arith {k s : ℕ} (hk : 2 ≤ k) (hs : k^3 ≤ s) :
    2*((k*s)^2*(4*s+(s+1)/2+(26*(k+2)+s+(k-1)*(26*(k+3)))+75*k^2+13*k+190)+k*s^2*(3*s)) ≤
      11*(k^2*s^3)+900*(k*s^3) := by
  obtain ⟨m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13⟩ := monomials hk hs
  have hcount : k-1+1=k := Nat.sub_add_cancel (by omega)
  have hv : (k-1)*(26*(k+3)) ≤ 26*k^2+52*k := by
    have heq : (k-1)*(k+3)+(k+3)=k*(k+3) := by
      calc (k-1)*(k+3)+(k+3) = (k-1+1)*(k+3) := by ring
        _ = k*(k+3) := by rw [hcount]
    nlinarith
  have he : 2*(4*s+(s+1)/2+(26*(k+2)+s+(k-1)*(26*(k+3)))+75*k^2+13*k+190) ≤
      11*s+202*k^2+182*k+485 := by omega
  have hmul := Nat.mul_le_mul_left ((k*s)^2) he
  have hexp : (k*s)^2*(11*s+202*k^2+182*k+485) =
      11*(k^2*s^3)+202*(k^4*s^2)+182*(k^3*s^2)+485*(k^2*s^2) := by ring
  have hexp' : k*s^2*(3*s) = 3*(k*s^3) := by ring
  have hdist : 2*((k*s)^2*(4*s+(s+1)/2+(26*(k+2)+s+(k-1)*(26*(k+3)))+75*k^2+13*k+190)) =
      (k*s)^2*(2*(4*s+(s+1)/2+(26*(k+2)+s+(k-1)*(26*(k+3)))+75*k^2+13*k+190)) := by ring
  rw [hexp] at hmul
  omega

private theorem arrangement_arith {k s : ℕ} (hk : 2 ≤ k) (hs : k^3 ≤ s) :
    (24*(s-k)+2032)*(k^4-k^2)*(k*s)+(24*s+2032)*(k^3-k^2)*(k*s) ≤
      24*(k^5*s^2)+4100*(k*s^3) := by
  obtain ⟨m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13⟩ := monomials hk hs
  have h₁ : (24*(s-k)+2032)*(k^4-k^2)*(k*s) ≤ (24*s+2032)*k^4*(k*s) := by
    gcongr <;> exact Nat.sub_le _ _
  have h₂ : (24*s+2032)*(k^3-k^2)*(k*s) ≤ (24*s+2032)*k^3*(k*s) := by
    gcongr; exact Nat.sub_le _ _
  have hexp : (24*s+2032)*k^4*(k*s)+(24*s+2032)*k^3*(k*s) =
      24*(k^5*s^2)+2032*(k^5*s)+24*(k^4*s^2)+2032*(k^4*s) := by ring
  omega

private theorem finish_arith {k s : ℕ} (hk : 2 ≤ k) (hs : k^3 ≤ s) :
    k^2*(5*s^3+1509*s^2+1505*s+4796)+9354*k^2*(k*s) ≤ 5*(k^2*s^3)+17164*(k*s^3) := by
  obtain ⟨m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13⟩ := monomials hk hs
  have hexp : k^2*(5*s^3+1509*s^2+1505*s+4796)+9354*k^2*(k*s) =
      5*(k^2*s^3)+1509*(k^2*s^2)+1505*(k^2*s)+4796*k^2+9354*(k^3*s) := by ring
  rw [hexp]
  omega

/-- Preparation: staging `7.5*k⁵s²`, vertical spreading `4*k⁵s²`. -/
theorem preparation_phase {n k : ℕ} (hk : Dims n k) [NeZero n] :
    CostedPhase (n := n) k ⟨0,23,9100⟩ Reachable (Prepared hk) := by
  intro B hB
  obtain ⟨C,p,hp,hclear,hrep⟩ := exists_preparation_path hk (representativeStaging_mixed hk) B
  refine ⟨C,p,Prepared.of_path hB p hclear hrep,?_⟩
  have h := preparation_arith hk.two_le hk.cube_le
  rw [hk.mul_side] at h
  have hle := p.inefficientMoves_le_length
  dsimp [LeadingBudget.eval]
  omega

/-- Transport: at most `n²` transfers of `5.5*s + O(k²)` inefficient moves, plus
`3*s` for each of the at most `k*s²` transfers out of the rightmost column. -/
theorem transport_phase {n k : ℕ} (hk : Dims n k) [NeZero n] :
    CostedPhase (n := n) k ⟨11,0,900⟩ (Prepared hk) (Transported hk) := by
  intro B hB
  have hstep := transportStepBound_of_vertical_bound hk (verticalTransportBound hk)
  obtain ⟨D,p,hD,hp⟩ := exists_transport_path_of_step_bound hk hstep B hB
  refine ⟨D,p,hD,?_⟩
  have hw := weighted_boardMatrix_le hk B
    (4*side n k+(side n k+1)/2+(26*(k+2)+side n k+(k-1)*(26*(k+3)))+75*k^2+13*k+190)
    (3*side n k)
  have hp' := hp.trans hw
  have h := transport_arith hk.two_le hk.cube_le
  rw [hk.mul_side] at h
  dsimp [LeadingBudget.eval]
  omega

/-- Arrangement: two exchange schedules of total length `24*k⁵s² + O(k*s³)`. -/
theorem arrangement_bound {n k : ℕ} (hk : Dims n k) [NeZero n]
    (B : Board n) (hB : Transported hk B) :
    ∃ C : Board n, ∃ p : Path B C, Arranged hk C ∧
      p.length ≤ (LeadingBudget.mk 0 24 4100).eval k (side n k) := by
  obtain ⟨C,p,hp,hblank,hsorted,_⟩ := exists_arrangement_path hk B hB.clear hB.sorted
  refine ⟨C,p,Arranged.of_path hB.reachable p hsorted (by
    rw [hblank]; exact reservoir_subset_square hB.blank_last),?_⟩
  have h := arrangement_arith hk.two_le hk.cube_le
  rw [hk.mul_side] at h
  dsimp [LeadingBudget.eval]
  omega

/-- Preparation followed by Transport. -/
theorem preparation_transport_phase {n k : ℕ} (hk : Dims n k) [NeZero n] :
    CostedPhase (n := n) k ⟨11,23,10000⟩ Reachable (Transported hk) :=
  (preparation_phase hk).comp (transport_phase hk)

/-- Finish: `k²` local solves of side `s` with the Parberry solver,
`5*k²s³ + O(k*s³)` moves including access and parity repair. -/
theorem finish_bound {n k : ℕ} (hk : Dims n k) [NeZero n]
    (B : Board n) (hB : Arranged hk B) :
    ∃ p : Path B (target n), p.length ≤ (LeadingBudget.mk 5 0 17164).eval k (side n k) := by
  obtain ⟨p,hp⟩ := exists_finish_path parberrySolverCost hk B hB
  refine ⟨p,?_⟩
  have h := finish_arith hk.two_le hk.cube_le
  rw [hk.mul_side] at h
  dsimp [LeadingBudget.eval] at *
  omega

/-- Every reachable board of admissible dimensions has a solution with at most
`(16*k²s³ + 47*k⁵s²)/2 + 15632*k*s³` inefficient moves, where `s = side n k`. -/
theorem exists_admissible_solution {n k : ℕ} (hk : Dims n k) [NeZero n]
    (B : Board n) (hB : Reachable B) :
    ∃ p : Path B (target n),
      2*p.inefficientMoves ≤ 16*(k^2*side n k^3)+47*(k^5*side n k^2)+31264*(k*side n k^3) ∧
      p.length ≤ manhattan B+16*(k^2*side n k^3)+47*(k^5*side n k^2)+
        31264*(k*side n k^3) := by
  have hfinish (C : Board n) (hC : Transported hk C) :
      ∃ q : Path C (target n), q.length ≤ (LeadingBudget.mk 5 24 21264).eval k (side n k) := by
    obtain ⟨D,p,hD,hp⟩ := arrangement_bound hk C hC
    obtain ⟨q,hq⟩ := finish_bound hk D hD
    refine ⟨p.append q,?_⟩
    rw [Path.length_append]
    dsimp [LeadingBudget.eval] at *
    omega
  obtain ⟨p,hi,hl⟩ := (preparation_transport_phase hk).exists_solution hfinish B hB
  refine ⟨p,?_,?_⟩ <;> dsimp [LeadingBudget.eval,LeadingBudget.add] at * <;> omega

/-- Two cells of one square are at most `2s` apart. -/
private theorem square_gridDistance_le {n k : ℕ} {i : GroupIndex k} {a b : Cell n}
    (ha : square i a) (hb : square i b) : gridDistance a b ≤ 2*side n k := by
  obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  simp only [Nat.add_mul, Nat.one_mul] at ha2 ha4 hb2 hb4
  simp only [gridDistance, Nat.dist]
  omega

/-- Arrangement raises the potential by little: reservoirs are unchanged, and
every tile of a sorted board is within `2s` of its target. -/
theorem arrangement_manhattan {n k : ℕ} (hk : Dims n k) (B C : Board n)
    (hres : ∀ (i : GroupIndex k) x, reservoir i x → C x = B x)
    (hsorted : SquaresSorted (k := k) C) :
    manhattan C ≤ manhattan B+(2*k^2*n*side n k+2*k^4*side n k^2) := by
  have hcell : ∀ x, cellCost C x ≤ 2*side n k := by
    intro x
    obtain ⟨j, hj⟩ := square_covers hk x
    unfold cellCost
    split_ifs with h0
    · omega
    · have hg := (mem_targetGroup j (C x)).mp (hsorted j x hj h0)
      exact square_gridDistance_le hj hg.2
  rw [manhattan_eq_sum_cellCost C, manhattan_eq_sum_cellCost B,
    sum_regions hk (cellCost C), sum_regions hk (cellCost B)]
  have hR : ∑ i : GroupIndex k, ∑ c ∈ reservoirCells i, cellCost C c =
      ∑ i : GroupIndex k, ∑ c ∈ reservoirCells i, cellCost B c := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro c hc
    simp only [cellCost, hres i c ((mem_reservoirCells i c).mp hc)]
  have hH : ∑ i : GroupIndex k, ∑ c ∈ horizontalCells i, cellCost C c ≤
      k^2*n*(2*side n k) := by
    calc _ ≤ ∑ _i : GroupIndex k, n*(2*side n k) := by
          apply Finset.sum_le_sum
          intro i _
          calc _ ≤ ∑ _c ∈ horizontalCells (n := n) i, 2*side n k :=
                Finset.sum_le_sum (fun c _ => hcell c)
            _ = n*(2*side n k) := by simp [card_horizontal hk i]
      _ = k^2*n*(2*side n k) := by simp [Finset.card_univ, pow_two]; ring
  have hV : ∑ i : GroupIndex k, ∑ j : GroupIndex k, ∑ c ∈ verticalCells i j, cellCost C c ≤
      k^4*side n k*(2*side n k) := by
    calc _ ≤ ∑ _i : GroupIndex k, ∑ _j : GroupIndex k, side n k*(2*side n k) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          calc _ ≤ ∑ _c ∈ verticalCells (n := n) i j, 2*side n k :=
                Finset.sum_le_sum (fun c _ => hcell c)
            _ = (side n k-k)*(2*side n k) := by simp [card_vertical hk i j]
            _ ≤ side n k*(2*side n k) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ = k^4*side n k*(2*side n k) := by simp [Finset.card_univ]; ring
  have e1 : k^2*n*(2*side n k) = 2*k^2*n*side n k := by ring
  have e2 : k^4*side n k*(2*side n k) = 2*k^4*side n k^2 := by ring
  omega

/-- The whole suffix charged by inefficiency: Arrangement by its length plus
its small potential increase (`arrangement_manhattan`), Finish by the local
solver's inefficiency. Twice the inefficiency is at most
`11*k²s³ + 47*k⁵s² + 32812*k*s³ + 2*k²*ineff s`. -/
theorem exists_admissible_solution_of_solver_ineff {cost ineff : ℕ → ℕ}
    (hsolver : SolverBound cost ineff)
    {n k : ℕ} (hk : Dims n k) [NeZero n] (B : Board n) (hB : Reachable B) :
    ∃ p : Path B (target n),
      p.length ≤ manhattan B+11*(k^2*side n k^3)+47*(k^5*side n k^2)+32812*(k*side n k^3)+
        2*(k^2*ineff (side n k)) := by
  obtain ⟨C,p,hC,hp⟩ := preparation_transport_phase hk B hB
  obtain ⟨D,q,hq,hblank,hsorted,hres⟩ := exists_arrangement_path hk C hC.clear hC.sorted
  have hD : Arranged hk D := Arranged.of_path hC.reachable q hsorted (by
    rw [hblank]; exact reservoir_subset_square hC.blank_last)
  obtain ⟨r,-,hri⟩ := exists_finish_path hsolver hk D hD
  have hM := arrangement_manhattan hk C D hres hsorted
  have hqbal := q.length_add_manhattan
  have ha := arrangement_arith hk.two_le hk.cube_le
  rw [hk.mul_side] at ha
  obtain ⟨m2,m3,-,-,-,-,m8,-,-,-,-,-⟩ := monomials hk.two_le hk.cube_le
  have e1 : 2*k^2*n*side n k = 2*(k^3*side n k^2) := by
    have h := hk.mul_side
    generalize side n k = s at h ⊢
    subst h; ring
  have e2 : 9354*k^2*n = 9354*(k^3*side n k) := by
    have h := hk.mul_side
    generalize side n k = s at h ⊢
    subst h; ring
  have e3 : 2*k^4*side n k^2 = 2*(k^4*side n k^2) := by ring
  rw [e1, e3] at hM
  rw [e2] at hri
  refine ⟨p.append (q.append r),?_⟩
  rw [Path.solution_length]
  simp only [Path.inefficientMoves_append]
  dsimp [LeadingBudget.eval] at hp
  omega

end SlidingPuzzle.Algorithm
