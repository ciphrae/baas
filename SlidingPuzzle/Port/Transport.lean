import SlidingPuzzle.Port.Board
import SlidingPuzzle.Tree.Transport

/-! # The port algorithm on a board of side `k*s`

Normalize the blank, walk it into the `tl` box of its square, preload the reserves,
run the abstract port transport and realize it, clean up, and finish every square with
Parberry's solver. -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle.Hub (Sq sqOf classOf reservoir misplaced exists_normalize exists_cleanup
  exists_finish exists_reservoir_walk)
open SlidingPuzzle.Tree

variable {n k s q σ : ℕ} (L : LaneSys k q)

theorem toI_offCount (ρ : PState k q) : ρ.toI.offCount = ρ.offCount := rfl

/-- The relocation weight bound of the run. -/
def relocW (k s lc : ℕ) : ℕ := s ^ 2 * (15 * k ^ 2 + 30 * k + 18) + (14 * k + 18) * (lc + k ^ 2)

/-- The bound of the whole port algorithm on a board of side `n = k*s`. -/
noncomputable def portBound (n s σ : ℕ) : ℕ :=
  2 * n + 2 * s + 52 * n * (∑ Q, resv L n s Q) +
    prunCost n k q s σ L.depth (laneCells L s) (∑ v, needAt L s (GroupedOrder.lamN n) v)
      (relocW k s (laneCells L s)) +
    (26 * n * ((laneCells L s + ((∑ v, needAt L s (GroupedOrder.lamN n) v) +
      ((∑ Q, resv L n s Q) + laneCells L s))) + 2 * n + 5) +
      (k ^ 2 * (5 * s ^ 3 + 1509 * s ^ 2 + 1505 * s + 4796) + 9354 * k ^ 2 * n)) / 2

theorem exists_port_solution [NeZero n] (pd : PDims n k s q σ) (h8 : 8 ≤ σ)
    (hσ2 : ∀ Q, needAt L s (GroupedOrder.lamN n) Q + 2 ≤ σ ^ 2)
    (hfit : ∀ Q, resv L n s Q + 2 ≤ (s - q) * (s - q))
    {la : ℕ} (hcap : 76 * k * la ≤ 5 * s)
    (hcA : 2 * (4 * k ^ 2 * q * k * s ^ 2) ≤ 2 ^ la)
    (hcB : 2 * (4 * k ^ 2 * q * k ^ 2 * s ^ 2) < 2 ^ GroupedOrder.lamN n)
    (B : Board n) (hB : Reachable B) :
    ∃ p : Path B (target n), p.inefficientMoves ≤ portBound L n s σ := by
  have td := pd.td
  obtain ⟨B1, p1, hb1, hp1⟩ := exists_normalize td.hd B
  -- the blank into the `tl` box
  set Q1 := sqOf td.hd (blank B1) with hQ1
  have hbb := box_bounds pd .tl
  have hin : inBox k s σ .tl (k + 1) (k + 1) := by
    simp only [inBox]; omega
  set e : Cell n := lc s Q1 (k + 1) (k + 1) with he
  have heb : InBoxOf s σ Q1 .tl e := inBoxOf_lc pd Q1 hin
  have her : reservoir k s Q1 e := reservoir_of_inBoxOf pd heb
  obtain ⟨B1', pw, hbw, hpw, -, -⟩ := exists_reservoir_walk td.hd B1 hb1 her
  have hsq : sqOf td.hd e = Q1 := by
    obtain ⟨d1, -, d3, -⟩ := lc_div (n := n) td.hd Q1 (r := k + 1) (c := k + 1) (by omega)
      (by omega)
    exact Prod.ext (Fin.ext d1) (Fin.ext d3)
  have hb1' : reservoir k s (sqOf td.hd (blank B1')) (blank B1') := by rw [hbw, hsq]; exact her
  -- preload
  set R := resv L n s with hRdef
  obtain ⟨B2, p2, hbl2, hR2, hp2⟩ := exists_preload L td R hfit (deficit L td R B1') B1' rfl hb1'
  have hbox : InBoxOf s σ (sqOf td.hd (blank B2)) .tl (blank B2) := by
    rw [hbl2, hbw, hsq]; exact heb
  have hb2 : reservoir k s (sqOf td.hd (blank B2)) (blank B2) := reservoir_of_inBoxOf pd hbox
  have hdef : deficit L td R B1' ≤ ∑ Q, R Q := sum_le_sum fun Q _ => Nat.sub_le _ _
  -- the abstract run
  set σ0 := absPState L pd B2 .tl with hσ0
  have hpsz : ∀ Q pt, needAt L s (GroupedOrder.lamN n) Q + 1 < psz σ0 Q pt := by
    intro Q pt
    have h1 : σ ^ 2 ≤ psz σ0 Q pt := psz_ge L pd B2 hbox Q pt
    have := hσ2 Q
    omega
  obtain ⟨es, hv, hcost, hoff⟩ := exists_valid_prun L td σ σ0 (regionSize L s)
    (absState_regionTotal L td B2 hb2) (absState_classTotal L td B2 hb2)
    (regionSize_le L td) (le_of_eq (sum_regionSize L td)) R (fun Q => hR2 Q) (fun Q => le_rfl)
    (sum_pc_le L pd B2 .tl) hpsz hcap hcA hcB
  obtain ⟨B3, p3, hR3, hp3⟩ := simulate_prun L pd h8 (prel_absPState L pd B2 hbox) hv
  rw [← hσ0] at hR3 hp3
  have hmis := misplaced_le_of_rel L td (rel_of_prel L pd hR3)
  rw [toI_offCount] at hmis
  obtain ⟨B4, p4, hsorted, hlast, hp4⟩ := exists_cleanup td.hd B3
  have hreach : Reachable B4 := by
    obtain ⟨p⟩ := hB
    exact ⟨((((p.append p1).append pw).append p2).append p3).append p4⟩
  obtain ⟨p5, hp5⟩ := exists_finish td.hd parberrySolverCost B4 hreach hsorted hlast
  refine ⟨(((p1.append pw).append p2).append p3).append (p4.append p5), ?_⟩
  simp only [Path.inefficientMoves_append]
  have hw : pw.inefficientMoves ≤ 2 * s := pw.inefficientMoves_le_length.trans hpw
  have h2 : p2.inefficientMoves ≤ 52 * n * ∑ Q, R Q :=
    p2.inefficientMoves_le_length.trans (hp2.trans (Nat.mul_le_mul_left _ hdef))
  have h4 : p4.length ≤ 26 * n * ((laneCells L s + ((∑ v, needAt L s (GroupedOrder.lamN n) v) +
      ((∑ Q, R Q) + laneCells L s))) + 2 * n + 5) := by
    refine hp4.trans (Nat.mul_le_mul_left _ ?_)
    omega
  have h45 := (p4.append p5).inefficientMoves_le_half_length
  rw [Path.length_append, Path.inefficientMoves_append] at h45
  have hhalf : p4.inefficientMoves + p5.inefficientMoves ≤
      (26 * n * ((laneCells L s + ((∑ v, needAt L s (GroupedOrder.lamN n) v) +
        ((∑ Q, R Q) + laneCells L s))) + 2 * n + 5) +
        (k ^ 2 * (5 * s ^ 3 + 1509 * s ^ 2 + 1505 * s + 4796) + 9354 * k ^ 2 * n)) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    omega
  unfold portBound relocW
  rw [← hRdef]
  omega

end SlidingPuzzle.Port
