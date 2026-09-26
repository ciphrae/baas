import SlidingPuzzle.Hub.GeomHop1
import SlidingPuzzle.Hub.OpInsert

/-! # hop1: along the row, into the hub

Phase 1: the blank walks inside the hub's reservoir, jumps into the landing
strip and walks along the row `R(h)` through the strip into the half up to the
insertion position `p`; the half's positions `1..p` move one step toward the
hub and the head drops into the strip. Phase 2 (`insert_by_cycle`) jumps into
the source's reservoir and places the inserted tile at `p`. -/
namespace SlidingPuzzle.Hub
open Classical

variable {n k s : ℕ} [NeZero n]

/-- Phase 1 of hop1. -/
theorem hop1_phase1 (hd : HDims n k s) (B : Board n) {S h : Sq k}
    (hbl : reservoir k s h (blank B)) (hne : S.2 ≠ h.2) :
    ∃ C : Board n, ∃ p : Path B C,
      blank C = rowCell k s (hop1Half S h) (hop1Pos s S h) ∧
      (∀ x, keyOf hd x = none → (∀ q, q ≤ hop1Pos s S h → x ≠ rowCell k s (hop1Half S h) q) →
        C x = B x) ∧
      (∀ q, q < hop1Pos s S h →
        C (rowCell k s (hop1Half S h) q) = B (rowCell k s (hop1Half S h) (q + 1))) ∧
      (∀ x, keyOf hd x ≠ none → keyOf hd x ≠ some h → C x = B x) ∧
      KeepKey hd B C {B (rowCell k s (hop1Half S h) 0)} ∧
      keyOf hd (position C (B (rowCell k s (hop1Half S h) 0))) = some h ∧
      p.inefficientMoves ≤ 3 * s + 25 * (k + 1) +
        ((Finset.range (hop1Pos s S h + 1)).filter fun q =>
          (classOf hd (B (rowCell k s (hop1Half S h) q))).2 ≠ h.2).card := by
  set H := hop1Half S h with hH
  set p := hop1Pos s S h with hp
  obtain ⟨hpl, -⟩ := hop1_geom hd hne
  rw [← hH, ← hp] at hpl
  have hH1 : H.1 = h.1 := rfl
  have hH2 : H.2.1 = h.2 := rfl
  have hHh : ((H.1, H.2.1) : Sq k) = h := rfl
  have hks := hd.k_lt_s
  have hroom := hd.room
  have hc := h.2.isLt
  have hb1 := hd.band_le h.1.isLt
  have hb2 := hd.band_le h.2.isLt
  -- A: walk to the reservoir corner
  let e0 : Cell n := mkCell n (h.1.val * s + k) (h.2.val * s + k)
  have e0f : e0.1.val = h.1.val * s + k := mkCell_fst (by omega)
  have e0s : e0.2.val = h.2.val * s + k := mkCell_snd (by omega)
  have he0 : reservoir k s h e0 := (reservoir_iff hd).mpr (by omega)
  obtain ⟨B1, p1, hbB1, hl1, hf1⟩ := exists_reservoir_walk hd B hbl he0
  -- B: jump into the landing strip
  obtain ⟨jp, hjp1, hjp2⟩ : ∃ jp, jp ≤ 1 ∧ (k + h.2.val + jp) % 2 = 1 :=
    ⟨if (k + h.2.val) % 2 = 1 then 0 else 1, by split_ifs <;> omega,
      by split_ifs <;> omega⟩
  obtain ⟨u0, hu0s, hu0c⟩ : ∃ u0, u0 + 1 ≤ s ∧ lineCol s H u0 = h.2.val * s + k + jp :=
    ⟨if H.2.2 then k + jp else s - 1 - k - jp, by split_ifs <;> omega, by
      unfold lineCol; rw [hH2]; split_ifs <;> omega⟩
  have hlen : ∀ t, u0 + t ≤ s + p → u0 + t < s + rowLen k s H := fun t ht => by omega
  let f : ℕ → Cell n := fun t => lineCell k s H (u0 + t)
  have zf : (f 0).1.val = h.1.val * s + h.2.val := lineCell_fst hd H _
  have zs : (f 0).2.val = h.2.val * s + k + jp := by
    rw [lineCell_snd hd H _ (by omega)]; exact hu0c
  obtain ⟨p2, hp2⟩ := exists_vjump_step hd.two_le_n B1 (f 0)
    (by rw [hbB1, e0s, zs]; simp only [Nat.dist]; omega)
    (by rw [hbB1, e0f, e0s, zf, zs]; omega)
  let B2 := swapCells B1 (blank B1) (f 0)
  have hbB2 : blank B2 = f 0 := blank_swapCells B1 _
  -- keys of the line
  have kstrip : ∀ t, u0 + t < s → keyOf hd (f t) = some h := fun t ht => by
    rw [← hHh]; exact keyOf_lineCell_strip hd H _ ht
  have frow : ∀ t, s ≤ u0 + t → u0 + t ≤ s + p → f t = rowCell k s H (u0 + t - s) := by
    intro t h1 h2
    change lineCell k s H (u0 + t) = _
    rw [← lineCell_rowCell hd H _ (by omega)]
    congr 1; omega
  have kline : ∀ t, s ≤ u0 + t → u0 + t ≤ s + p → keyOf hd (f t) = none := by
    intro t h1 h2
    rw [frow t h1 h2]; exact keyOf_rowCell hd H _ (by omega)
  -- B2 agrees with B away from the hub's reservoir and the strip cell
  have hB2 : ∀ x, ¬ reservoir k s h x → x ≠ f 0 → B2 x = B x := by
    intro x h1 h2
    change swapCells B1 (blank B1) (f 0) x = B x
    rw [swapCells_preserves B1 (by rw [hbB1]; exact fun e => h1 (e ▸ he0)) h2, hf1 x h1]
  have hB2c : ∀ x, keyOf hd x = none → B2 x = B x := by
    intro x hx
    apply hB2
    · exact fun hr => by rw [keyOf_reservoir hd hr] at hx; cases hx
    · exact ne_of_keyOf (by rw [hx, kstrip 0 (by omega)]; simp)
  -- C: the line walk
  set d := s + p - u0 with hd'
  obtain ⟨B3, p3, hbB3, hC3, hfix3, hi3⟩ := exists_swap_walk d f
    (fun t T => moveCost (f t) (f (t + 1)) T)
    (fun t t' ht ht' e => by
      have := lineCell_inj hd H (hlen t (by omega)) (hlen t' (by omega)) e
      omega)
    (fun t ht B' hB' => by
      obtain ⟨q, hq⟩ := exists_move_step B' (f (t + 1)) (by
        rw [hB']
        have := lineCell_adj (n := n) hd H (u0 + t) (by omega)
        rwa [show u0 + t + 1 = u0 + (t + 1) by ring] at this)
      exact ⟨q, hq.trans (by rw [hB'])⟩)
    B2 hbB2
  have hfd : f d = rowCell k s H p := by rw [frow d (by omega) (by omega)]; congr 1; omega
  -- off the line
  have offline : ∀ x, keyOf hd x ≠ some h → (∀ q, q ≤ p → x ≠ rowCell k s H q) →
      ∀ t, t ≤ d → x ≠ f t := by
    intro x h1 h2 t ht e
    by_cases hts : u0 + t < s
    · exact h1 (by rw [e]; exact kstrip t hts)
    · exact h2 (u0 + t - s) (by omega) (by rw [e, frow t (by omega) (by omega)])
  have hB3 : ∀ x, keyOf hd x ≠ some h → (∀ q, q ≤ p → x ≠ rowCell k s H q) →
      B3 x = B2 x := fun x h1 h2 => hfix3 x (offline x h1 h2)
  -- the head step
  set j := s - 1 - u0 with hj
  have hfj1 : f (j + 1) = rowCell k s H 0 := by
    rw [frow (j + 1) (by omega) (by omega)]; congr 1; omega
  refine ⟨B3, (p1.append p2).append p3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbB3, hfd]
  · intro x hx hq
    rw [hB3 x (by rw [hx]; simp) hq, hB2c x hx]
  · intro q hq
    have e1 : rowCell k s H q = f (s + q - u0) := by
      rw [frow _ (by omega) (by omega)]; congr 1; omega
    rw [e1, hC3 _ (by omega), frow _ (by omega) (by omega),
      show u0 + (s + q - u0 + 1) - s = q + 1 by omega]
    exact hB2c _ (keyOf_rowCell hd H _ (by omega))
  · intro x h1 h2
    rw [hB3 x h2 (fun q _ e => h1 (by rw [e]; exact keyOf_rowCell hd H _ (by omega)))]
    apply hB2
    · exact fun hr => h2 (keyOf_reservoir hd hr)
    · exact fun e => h2 (by rw [e]; exact kstrip 0 (by omega))
  · have K1 : KeepKey hd B B1 ∅ := keepKey_of_agree hd (reservoir k s h)
      (fun x y hx hy => by rw [keyOf_reservoir hd hx, keyOf_reservoir hd hy]) hf1
    have K2 : KeepKey hd B1 B2 ∅ := keepKey_of_agree hd (fun x => x = e0 ∨ x = f 0)
      (fun x y hx hy => by
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
          simp only [keyOf_reservoir hd he0, kstrip 0 (by omega)])
      (fun x hx => by
        simp only [not_or] at hx
        exact swapCells_preserves B1 (by rw [hbB1]; exact hx.1) hx.2)
    have K3 := keepKey_of_walk hd f d j hbB2
      (fun t ht htj => by
        by_cases h1 : u0 + t + 1 < s
        · rw [kstrip t (by omega), kstrip (t + 1) (by omega)]
        · rw [kline t (by omega) (by omega), kline (t + 1) (by omega) (by omega)])
      hC3 hfix3
    rw [hfj1, hB2c _ (keyOf_rowCell hd H _ (by omega))] at K3
    simpa using (K1.trans K2).trans K3
  · have e := hC3 j (by omega)
    rw [hfj1, hB2c _ (keyOf_rowCell hd H _ (by omega))] at e
    rw [position_eq_of_apply e]
    exact kstrip j (by omega)
  · -- cost
    rw [Path.inefficientMoves_append, Path.inefficientMoves_append]
    have c1 := p1.inefficientMoves_le_length
    have c2 : 25 * (Nat.dist (blank B1).1.val (f 0).1.val + 1) ≤ 25 * (k + 1) := by
      rw [hbB1, e0f, zf]; simp only [Nat.dist]; omega
    have hdsplit : d = j + (p + 1) := by omega
    rw [hdsplit, Finset.sum_range_add] at hi3
    have s1 : ∑ t ∈ Finset.range j, moveCost (f t) (f (t + 1)) (B2 (f (t + 1))) ≤ s := by
      calc _ ≤ ∑ t ∈ Finset.range j, 1 := Finset.sum_le_sum fun t _ => moveCost_le_one _ _ _
        _ ≤ s := by simp; omega
    have s2 : ∑ q ∈ Finset.range (p + 1), moveCost (f (j + q)) (f (j + q + 1)) (B2 (f (j + q + 1)))
        ≤ ((Finset.range (p + 1)).filter fun q =>
          (classOf hd (B (rowCell k s H q))).2 ≠ h.2).card := by
      rw [Finset.card_filter]
      apply Finset.sum_le_sum
      intro q hq
      rw [Finset.mem_range] at hq
      have ej : f (j + q) = lineCell k s H (s - 1 + q) := by
        show lineCell k s H _ = _; congr 1; omega
      have ef : f (j + q + 1) = lineCell k s H (s - 1 + q + 1) := by
        show lineCell k s H _ = _; congr 1; omega
      have et : lineCell (n := n) k s H (s - 1 + q + 1) = rowCell k s H q := by
        rw [← lineCell_rowCell hd H q (by omega)]; congr 1; omega
      have htile : B2 (lineCell k s H (s - 1 + q + 1)) = B (rowCell k s H q) := by
        rw [et]; exact hB2c _ (keyOf_rowCell hd H _ (by omega))
      rw [ej, ef, htile]
      split_ifs with hjunk
      · exact moveCost_le_one _ _ _
      · push Not at hjunk
        rw [moveCost_lineCell (n := n) hd H (s - 1 + q) (by omega) (by omega) _ hjunk]
    omega

end SlidingPuzzle.Hub
