import SlidingPuzzle.Tree.RunOuter

/-! # Placeholders in total

Placeholders of `v` for `x` exceed the dirty arrivals at `v` by at most
`c v x`, and dirty arrivals at `v` come from placeholders of the squares whose
next hop toward `x` lands in `v`, which have one more hop to go. Summing by the
number of hops left gives `Σ B ≤ (2 depth + 1) Σ c`. -/
namespace SlidingPuzzle.Tree
open Finset
open SlidingPuzzle.Hub (Sq)

variable {k q : ℕ} (L : LaneSys k q)

theorem sum_B_le (B dA c : Sq k → Sq k → ℕ) (x : Sq k)
    (h1 : ∀ v, B v x ≤ dA v x + c v x)
    (h2 : ∀ v, dA v x ≤ ∑ u ∈ univ.filter (fun u => u ≠ x ∧ L.nxt u x = v), B u x) :
    ∑ v, B v x ≤ (2 * L.depth + 1) * ∑ v, c v x := by
  classical
  -- `T r`: placeholders of the squares with `r` hops left
  set T : ℕ → ℕ := fun r => ∑ v ∈ univ.filter (fun v => L.srank v x = r), B v x with hT
  set C : ℕ → ℕ := fun r => ∑ v ∈ univ.filter (fun v => L.srank v x = r), c v x with hC
  have hrec : ∀ r, T r ≤ C r + T (r + 1) := by
    intro r
    have hA : ∑ v ∈ univ.filter (fun v => L.srank v x = r), dA v x ≤ T (r + 1) := by
      calc ∑ v ∈ univ.filter (fun v => L.srank v x = r), dA v x
          ≤ ∑ v ∈ univ.filter (fun v => L.srank v x = r),
              ∑ u ∈ univ.filter (fun u => u ≠ x ∧ L.nxt u x = v), B u x :=
            sum_le_sum fun v _ => h2 v
        _ = ∑ u ∈ univ.filter (fun u => u ≠ x ∧ L.srank (L.nxt u x) x = r), B u x := by
            rw [Finset.sum_comm' (t' := univ.filter (fun u => u ≠ x ∧ L.srank (L.nxt u x) x = r))
              (s' := fun u => {L.nxt u x})]
            · refine sum_congr rfl fun u _ => by simp
            · intro v u
              simp only [mem_filter, mem_univ, true_and, mem_singleton]
              aesop
        _ ≤ T (r + 1) := by
            apply sum_le_sum_of_subset_of_nonneg
            · intro u hu
              simp only [mem_filter, mem_univ, true_and] at hu ⊢
              rw [srank_nxt (L := L) hu.1, hu.2]
            · intros; exact Nat.zero_le _
    have hB : T r ≤ ∑ v ∈ univ.filter (fun v => L.srank v x = r), dA v x + C r := by
      rw [hT, hC, ← sum_add_distrib]
      exact sum_le_sum fun v _ => h1 v
    omega
  have hzero : ∀ r, 2 * L.depth < r → T r = 0 := by
    intro r hr
    apply Finset.sum_eq_zero
    intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    have := srank_le (L := L) v x
    omega
  -- downward induction
  have hdown : ∀ j r, r + j = 2 * L.depth + 1 → T r ≤ ∑ i ∈ Finset.Ico r (2 * L.depth + 1), C i := by
    intro j
    induction j with
    | zero => intro r hr; rw [hzero r (by omega)]; exact Nat.zero_le _
    | succ j ih =>
      intro r hr
      have := ih (r + 1) (by omega)
      have e : Finset.Ico r (2 * L.depth + 1) = insert r (Finset.Ico (r + 1) (2 * L.depth + 1)) := by
        ext i; simp only [mem_Ico, mem_insert]; omega
      rw [e, sum_insert (by simp)]
      have := hrec r
      omega
  have hCsum : ∑ i ∈ range (2 * L.depth + 1), C i = ∑ v, c v x := by
    rw [hC]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun v => L.srank v x) (t := range (2 * L.depth + 1))]
    intro v _; simp only [mem_range]; have := srank_le (L := L) v x; omega
  have hTsum : ∑ v, B v x = ∑ i ∈ range (2 * L.depth + 1), T i := by
    rw [hT]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun v => L.srank v x) (t := range (2 * L.depth + 1))]
    intro v _; simp only [mem_range]; have := srank_le (L := L) v x; omega
  rw [hTsum]
  calc ∑ i ∈ range (2 * L.depth + 1), T i
      ≤ ∑ _i ∈ range (2 * L.depth + 1), ∑ v, c v x := by
        refine sum_le_sum fun i hi => ?_
        rw [← hCsum]
        refine (hdown (2 * L.depth + 1 - i) i (by simp at hi; omega)).trans ?_
        apply sum_le_sum_of_subset_of_nonneg
        · intro j hj; simp only [mem_Ico, mem_range] at hj ⊢; omega
        · intros; exact Nat.zero_le _
    _ = (2 * L.depth + 1) * ∑ v, c v x := by simp

end SlidingPuzzle.Tree
