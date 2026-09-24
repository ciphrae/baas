import SlidingPuzzle.Moves.BulkExchange
import SlidingPuzzle.Moves.ExchangeSchedule

/-! Whole-family exchanges in the shared involution schedule. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

theorem exists_bulk_involution_region_path_active {α : Type*} [DecidableEq α]
    (B : Board n) (hn : 4 ≤ n) (S : α → Finset (Cell n))
    (τ : α → α) (hτ : Function.Involutive τ)
    (hdis : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (M : ℕ) (hsmall : 2*M ≤ n) (hsize : ∀ i, 2 ≤ (S i).card ∧ (S i).card ≤ M)
    (hcard : ∀ i, (S i).card = (S (τ i)).card)
    (hzero : ∀ i x, x ∈ S i → B x ≠ 0)
    (P : α → Tile n → Prop) (s : Finset α)
    (hclosed : ∀ i ∈ s, τ i ∈ s)
    (hinit : ∀ i ∈ s, ∀ x ∈ S i, P (τ i) (B x)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ (24*M+2032)*(s.filter (fun i => τ i ≠ i)).card*n ∧
      blank C = blank B ∧
      (∀ i ∈ s, ∀ x ∈ S i, P i (C x)) ∧
      (∀ x, (∀ i ∈ s, x ∉ S i) → C x = B x) := by
  have hexchange : SetExchangeBound n M (24*M+2032) := by
    intro D s t hdis hcard hs hM hs0 ht0 P Q hP hQ
    obtain ⟨C,p,hp,hb,hC,hD,hfix⟩ := exists_bulk_set_exchange D hn s t hdis hcard hs
      (by omega) hs0 ht0 P Q hP hQ
    refine ⟨C,p,?_,hb,hC,hD,hfix⟩
    calc
      p.length ≤ (48*M+4064)*n := hp.trans (by gcongr)
      _ = 2*(24*M+2032)*n := by ring
  exact exists_involution_region_path_active_of_exchange B hn S τ hτ hdis M hsize hcard hzero
    (24*M+2032) hexchange P s hclosed hinit

end SlidingPuzzle
