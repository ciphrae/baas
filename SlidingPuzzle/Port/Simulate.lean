import SlidingPuzzle.Port.LegSim

/-! # Realizing port events on boards -/
namespace SlidingPuzzle.Port
open SlidingPuzzle.Tree

variable {n k s q σ : ℕ} [NeZero n] (L : LaneSys k q)

theorem simulate_pstep (pd : PDims n k s q σ) (h8 : 8 ≤ σ) {B : Board n} {ρ : PState k q}
    (hR : PRel L pd B ρ) {e : PEvent k q} (he : ρ.Pre L e) :
    ∃ C : Board n, ∃ p : Path B C, PRel L pd C (ρ.step s e) ∧
      p.inefficientMoves ≤ ρ.cost s σ e := by
  cases e with
  | hop l J y m => exact simulate_hop L pd (by omega) hR he
  | xfer pt c => exact simulate_xfer L pd (by omega) hR he
  | leg Z y p z => exact simulate_leg L pd h8 hR he

theorem simulate_prun (pd : PDims n k s q σ) (h8 : 8 ≤ σ) {B : Board n} {ρ : PState k q}
    (hR : PRel L pd B ρ) {es : List (PEvent k q)} (hv : ρ.Valid L s es) :
    ∃ C : Board n, ∃ p : Path B C,
      PRel L pd C (ρ.run s es) ∧ p.inefficientMoves ≤ ρ.totalCost s σ es := by
  induction es generalizing B ρ with
  | nil => exact ⟨B, .nil B, hR, by simp [Path.inefficientMoves, PState.totalCost]⟩
  | cons e es ih =>
    obtain ⟨hpre, hrest⟩ := hv
    obtain ⟨C, p, hC, hp⟩ := simulate_pstep L pd h8 hR hpre
    obtain ⟨D, q, hD, hq⟩ := ih hC hrest
    refine ⟨D, p.append q, hD, ?_⟩
    rw [Path.inefficientMoves_append]
    simp only [PState.totalCost]
    omega

end SlidingPuzzle.Port
