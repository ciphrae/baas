import SlidingPuzzle.Tree.RunPlan
import SlidingPuzzle.Hub.RunInit

/-! # Budgets of the run

`laneBud` is the in-flight budget of a lane (the residence bound in natural
numbers), `Rneed v` the reserve a square needs: the budgets and tag supports of
the lanes landing in `v`, plus its possible dummy out-edges. -/
namespace SlidingPuzzle.Tree
open Finset
open SlidingPuzzle.Hub (Sq Round idleRound)

variable {k q : ℕ} (L : LaneSys k q)

/-- In-flight budget of a lane. -/
def laneBud (s lam : ℕ) (l : Ln k q) : ℕ :=
  2 * blen L l.2 * s + 2 * k * (blen L l.2 + 1) + 15 * lam * (Xs L l).card

/-- Budget plus tag support, summed over the lanes landing at `v`. -/
def needAt (s lam : ℕ) (v : Sq k) : ℕ :=
  ∑ l ∈ univ.filter (fun l : Ln k q => land l = v), (laneBud L s lam l + (Xs L l).card)

/-- The reserve a square needs. -/
def Rneed (s lam : ℕ) (rsz : Sq k → ℕ) (v : Sq k) : ℕ :=
  needAt L s lam v + (s ^ 2 - rsz v) + 6

theorem sum_needAt (s lam : ℕ) :
    ∑ v, needAt L s lam v = ∑ l : Ln k q, (laneBud L s lam l + (Xs L l).card) := by
  unfold needAt
  rw [Finset.sum_fiberwise (g := fun l => land l)]

theorem card_Ln : Fintype.card (Ln k q) = 4 * k ^ 2 * q := by
  have : Fintype.card (LaneI k q) = k * q * k * 2 := by
    have e : LaneI k q ≃ Fin k × Fin q × Fin k × Bool :=
      ⟨fun H => (H.b, H.o, H.t, H.side), fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩,
        fun _ => rfl, fun _ => rfl⟩
    rw [Fintype.card_congr e]; simp; ring
  simp [Ln, this]; ring

/-- Active tags of a square are tags of lanes landing there. -/
theorem card_act_le (v : Sq k) :
    ∑ x, (if L.Act v x then 1 else 0) ≤ ∑ l ∈ univ.filter (fun l : Ln k q => land l = v),
      (Xs L l).card := by
  classical
  rw [← card_filter]
  refine le_trans (card_le_card ?_) card_biUnion_le
  intro x hx
  simp only [mem_filter, mem_univ, true_and] at hx
  obtain ⟨u, hux, hv⟩ := hx
  simp only [mem_biUnion, mem_filter, mem_univ, true_and]
  exact ⟨(L.stage u x).1, hv, (stRec_supp L hux).2⟩

/-- Rounds in the order `σo`, idle beyond `Δ0`. -/
def ordR {Δ0 : ℕ} (rs0 : Fin Δ0 → Round k) (σo : Equiv.Perm (Fin Δ0)) (τ : ℕ) : Round k :=
  if h : τ < Δ0 then rs0 (σo ⟨τ, h⟩) else idleRound

theorem sum_ordR {Δ0 : ℕ} (rs0 : Fin Δ0 → Round k) (σo : Equiv.Perm (Fin Δ0))
    (f : Round k → ℕ) : ∑ τ ∈ range Δ0, f (ordR rs0 σo τ) = ∑ j : Fin Δ0, f (rs0 j) := by
  rw [← Fin.sum_univ_eq_sum_range]
  have h1 : ∀ i : Fin Δ0, f (ordR rs0 σo i) = f (rs0 (σo i)) := by
    intro i; simp [ordR, i.isLt]
  simp only [h1]
  exact Equiv.sum_comp σo (fun i => f (rs0 i))

end SlidingPuzzle.Tree
