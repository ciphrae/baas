import SlidingPuzzle.Hub.InFlightOrder
import SlidingPuzzle.Hub.InFlightSum

/-! # Tiles in flight in the row halves

A row half behaves like a delay line: an insertion at position `p` moves
positions `1..p` one step toward the hub and outputs position `0`. Insertions
from block distance `d` go to `insPos d`, which increases with `d`. With the
plan's rounds in a suitable order (a uniformly random one works, by a Chernoff
bound for sampling without replacement), the number of inserted tiles of each
class present in a half stays small, summed over the classes
(`exists_good_order`; `PROOF.md`, Lemmas 2-4).

The definitions (`InsRec`, `Ghost`, `ghostRun`, `newCnt`, `roundIns`,
`Consistent`) are in `Hub/InFlightDefs.lean`. The proof:
* `Hub/ChernoffMaclaurin.lean`, `Hub/ChernoffPerm.lean`: Maclaurin's inequality
  and Chernoff bounds for a random permutation restricted to a window;
* `Hub/InFlightPush.lean`, `Hub/InFlightWindow.lean`: the push lemma and the
  deterministic bound from window properties of the order;
* `Hub/InFlightRound.lean`: insertions of a round, window parameters;
* `Hub/InFlightOrder.lean`: a good order exists (union bound);
* `Hub/InFlightSum.lean`: summing the bounds (harmonic numbers). -/
namespace SlidingPuzzle.Hub

open Finset

/-- Integer upper rounding of the fractional in-flight estimate. -/
def Rhub (n : ℕ) : ℕ := (28 * n * (Nat.log 2 n + 1) + 22 * n) / 5 + 1

theorem Rhub_lower (n : ℕ) :
    28 * n * (Nat.log 2 n + 1) + 22 * n ≤ 5 * Rhub n := by
  have := Nat.mod_add_div (28 * n * (Nat.log 2 n + 1) + 22 * n) 5
  have := Nat.mod_lt (28 * n * (Nat.log 2 n + 1) + 22 * n) (by norm_num : 0 < 5)
  unfold Rhub
  omega

theorem Rhub_upper (n : ℕ) :
    5 * Rhub n ≤ 28 * n * (Nat.log 2 n + 1) + 22 * n + 5 := by
  have := Nat.mod_add_div (28 * n * (Nat.log 2 n + 1) + 22 * n) 5
  unfold Rhub
  omega

/-- Compatibility estimate for the generic run budgets. -/
theorem Rhub_le_seven {n : ℕ} (hn : 1 ≤ n) (hL : 10 ≤ Nat.log 2 n + 1) :
    Rhub n ≤ 7 * n * (Nat.log 2 n + 1) := by
  have h := Rhub_upper n
  have hlog := Nat.mul_le_mul_left n hL
  nlinarith only [h, hlog, hn]

/-- The capacity condition already forces large squares and a logarithm of
at least ten; retain these facts in the later cost estimates. -/
theorem capacity_lower_bounds {n k s : ℕ} (hd : HDims n k s)
    (hP1 : 25 * k * (Nat.log 2 n + 1) ≤ s) :
    10 ≤ Nat.log 2 n + 1 ∧ 500 ≤ s ∧ 1000 ≤ n := by
  have hk := hd.two_le
  have hroom := hd.room
  have hn := hd.mul
  have hn16 : 16 ≤ n := by nlinarith
  have hlog4 : 4 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hs250 : 250 ≤ s := by nlinarith
  have hn500 : 500 ≤ n := by nlinarith
  have hlog8 : 8 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hs450 : 450 ≤ s := by nlinarith
  have hn900 : 900 ≤ n := by nlinarith
  have hlog9 : 9 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hs500 : 500 ≤ s := by nlinarith
  exact ⟨by omega, hs500, by nlinarith⟩

/-- The number of window events is below `2^λ`. -/
theorem card_events_lt {n k s Δ : ℕ} (hd : HDims n k s) (hΔ : Δ ≤ s ^ 2 + 1) :
    Fintype.card (RowH k × Fin k × Fin Δ) + Fintype.card (RowH k × Fin k × Sq k × Fin Δ) <
      2 ^ lamN n := by
  have hk : 2 ≤ k := hd.two_le
  have hs : 1 ≤ s := by have := hd.room; omega
  have hn : n = k * s := hd.mul.symm
  have hcard : Fintype.card (RowH k × Fin k × Fin Δ) +
      Fintype.card (RowH k × Fin k × Sq k × Fin Δ) = 2 * k ^ 3 * Δ + 2 * k ^ 5 * Δ := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; ring
  rw [hcard]
  have h1 : k ^ 3 ≤ k ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : Δ ≤ 2 * s ^ 2 := by nlinarith
  have hroom := hd.room
  have hsmall : 8 * k ≤ s ^ 2 := by nlinarith
  have h4 : 8 * (k ^ 5 * s ^ 2) ≤ n ^ 4 := by
    have := Nat.mul_le_mul_left (k ^ 4 * s ^ 2) hsmall
    rw [hn]
    nlinarith only [this]
  have h5 : n ^ 4 < (n + 1) ^ 4 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have h6 : (n + 1) ^ 4 ≤ 2 ^ lamN n := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    rw [lamN, mul_comm, pow_mul]
    exact Nat.pow_le_pow_left this 4
  calc 2 * k ^ 3 * Δ + 2 * k ^ 5 * Δ ≤ 4 * k ^ 5 * Δ := by nlinarith
    _ ≤ 4 * k ^ 5 * (2 * s ^ 2) := Nat.mul_le_mul_left _ h2
    _ = 8 * (k ^ 5 * s ^ 2) := by ring
    _ ≤ n ^ 4 := h4
    _ < _ := lt_of_lt_of_le h5 h6

/-- `log (k Δ) ≤ (7/5) (log₂ n + 1)`. -/
theorem log_kΔ_le {n k s Δ : ℕ} (hd : HDims n k s) (hΔ : Δ ≤ s ^ 2 + 1) :
    Real.log ((k : ℝ) * Δ) ≤ (7 / 5 : ℝ) * ((Nat.log 2 n : ℝ) + 1) := by
  have hk : 2 ≤ k := hd.two_le
  have hs : 1 ≤ s := by have := hd.room; omega
  have hn : n = k * s := hd.mul.symm
  have hkn : k * Δ ≤ n ^ 2 := by
    rw [hn]
    have h1 : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ hs
    calc k * Δ ≤ k * (s ^ 2 + 1) := Nat.mul_le_mul_left _ hΔ
      _ ≤ k * (s ^ 2 + s ^ 2) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * k * s ^ 2 := by ring
      _ ≤ k * k * s ^ 2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hk)
      _ = (k * s) ^ 2 := by ring
  have hnpos : 0 < n := by rw [hn]; positivity
  have hlogn : Real.log n ≤ (7 / 10 : ℝ) * ((Nat.log 2 n : ℝ) + 1) := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    have h' : (n : ℝ) ≤ 2 ^ (Nat.log 2 n + 1) := by exact_mod_cast h.le
    calc Real.log n ≤ Real.log (2 ^ (Nat.log 2 n + 1)) :=
          Real.log_le_log (by exact_mod_cast hnpos) h'
      _ = (Nat.log 2 n + 1 : ℕ) * Real.log 2 := Real.log_pow _ _
      _ ≤ (7 / 10 : ℝ) * (Nat.log 2 n + 1 : ℕ) := by
          have := Real.log_two_lt_d9
          have : (0 : ℝ) ≤ (Nat.log 2 n + 1 : ℕ) := Nat.cast_nonneg _
          nlinarith
      _ = _ := by push_cast; ring
  rcases Nat.eq_zero_or_pos (k * Δ) with h0 | hpos
  · have : (k : ℝ) * Δ = 0 := by exact_mod_cast h0
    rw [this, Real.log_zero]; positivity
  · calc Real.log ((k : ℝ) * Δ) ≤ Real.log ((n : ℝ) ^ 2) := by
          apply Real.log_le_log (by exact_mod_cast hpos); exact_mod_cast hkn
      _ = 2 * Real.log n := by rw [Real.log_pow]; push_cast; ring
      _ ≤ _ := by linarith

/-- Some order of the rounds keeps every hub's in-flight maxima small. -/
theorem exists_good_order {n k s : ℕ} (hd : HDims n k s)
    (hP1 : 25 * k * (Nat.log 2 n + 1) ≤ s) {Δ : ℕ} (hΔ : Δ ≤ s ^ 2 + 1)
    (rs : Fin Δ → Round k) :
    ∃ σ : Equiv.Perm (Fin Δ), ∀ L : List (InsRec k), Consistent rs σ L →
      ∃ N : Sq k → Sq k → ℕ, (∀ h, ∑ x, N h x ≤ Rhub n) ∧
        ∀ m h x, newCnt s (ghostRun s (fun _ _ => none) (L.take m)) h x ≤ N h x := by
  have hk2 : 2 ≤ k := hd.two_le
  have hk : 0 < k := by omega
  have hs : 1 ≤ s := by have := hd.room; omega
  have hn : n = k * s := hd.mul.symm
  set ℓ := Nat.log 2 n + 1 with hℓ
  have hlam : 6 * k * lamN n ≤ s - k := by
    have e1 : 6 * k * lamN n = 24 * (k * ℓ) := by rw [lamN]; ring
    have e2 : 25 * k * ℓ = 25 * (k * ℓ) := by ring
    have e3 : k ≤ k * ℓ := Nat.le_mul_of_pos_right k (by omega)
    omega
  obtain ⟨σ, hσ⟩ := exists_goodOrder s rs n hk hlam (card_events_lt hd hΔ)
  refine ⟨σ, fun L hL => ?_⟩
  let r0 : InsRec k := ⟨0, (⟨0, hk⟩, ⟨0, hk⟩, true), 0, (⟨0, hk⟩, ⟨0, hk⟩)⟩
  refine ⟨fun h x => ∑ side : Bool, ∑ d ∈ range k, Nb s rs n (h.1, h.2, side) d x, ?_, ?_⟩
  · intro h
    have hsum : ∑ x, ∑ side : Bool, ∑ d ∈ range k, (Nb s rs n (h.1, h.2, side) d x : ℝ) ≤
        ∑ side : Bool, (4 * rowLen k s (h.1, h.2, side) * (1 + Real.log (k * Δ)) + 4 * k +
          k * k * lamN n) := by
      rw [sum_comm]
      apply sum_le_sum; intro side _
      rw [sum_comm]
      exact sum_half_le s rs hs n _
    have hlen : (rowLen k s (h.1, h.2, true) : ℝ) + rowLen k s (h.1, h.2, false) ≤ n := by
      have hc := h.2.isLt
      have : rowLen k s (h.1, h.2, true) + rowLen k s (h.1, h.2, false) ≤ n := by
        simp only [rowLen, if_true, Bool.false_eq_true, if_false]
        rw [hn, ← add_mul]
        exact Nat.mul_le_mul_right _ (by omega)
      exact_mod_cast this
    have hlog := log_kΔ_le hd hΔ
    have hkk : (k : ℝ) * k ≤ n := by
      have : k * k ≤ n := by
        rw [hn]; apply Nat.mul_le_mul_left
        have := hd.room; omega
      exact_mod_cast this
    have hkn : (k : ℝ) ≤ n := by
      have : k ≤ n := by rw [hn]; exact Nat.le_mul_of_pos_right k (by omega)
      exact_mod_cast this
    have hstock : 25 * (k : ℝ) * k * ℓ ≤ n := by
      have h := Nat.mul_le_mul_left k hP1
      rw [hd.mul] at h
      have h' : 25 * k * k * ℓ ≤ n := by
        simpa only [← hℓ, mul_assoc, mul_left_comm, mul_comm] using h
      exact_mod_cast h'
    have hsmall : 500 * (k : ℝ) ≤ n := by
      have hs500 : 500 ≤ s := (capacity_lower_bounds hd hP1).2.1
      have h := Nat.mul_le_mul_left k hs500
      rw [hd.mul] at h
      exact_mod_cast (show 500 * k ≤ n by omega)
    have hn16 : 16 ≤ n := by have := hd.room; have := hd.two_le; nlinarith [hd.mul]
    have hlog4 : 4 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
    have hℓR : (5 : ℝ) ≤ ℓ := by exact_mod_cast (show 5 ≤ ℓ by omega)
    have hlamR : (lamN n : ℝ) = 4 * ℓ := by simp only [lamN, hℓ]; push_cast; ring
    have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hℓdef : ((Nat.log 2 n : ℕ) : ℝ) + 1 = ℓ := by rw [hℓ]; push_cast; ring
    rw [hℓdef] at hlog
    have hfin : ∑ x, ∑ side : Bool, ∑ d ∈ range k, (Nb s rs n (h.1, h.2, side) d x : ℝ) ≤
        (Rhub n : ℝ) := by
      refine hsum.trans ?_
      rw [Fintype.sum_bool, hlamR]
      have hR : 28 * (n : ℝ) * ℓ + 22 * n ≤ 5 * (Rhub n : ℝ) := by
        have h := Rhub_lower n
        rw [← hℓdef]
        exact_mod_cast h
      have hl0 : (0 : ℝ) ≤ rowLen k s (h.1, h.2, true) := Nat.cast_nonneg _
      have hl1 : (0 : ℝ) ≤ rowLen k s (h.1, h.2, false) := Nat.cast_nonneg _
      have hlg : 1 + Real.log (k * Δ) ≤ 1 + (7 / 5 : ℝ) * ℓ := by linarith
      have hA : (4 * (rowLen k s (h.1, h.2, true) : ℝ)) * (1 + Real.log (k * Δ)) +
          4 * (rowLen k s (h.1, h.2, false) : ℝ) * (1 + Real.log (k * Δ)) ≤ 4 * n * (1 + (7 / 5 : ℝ) * ℓ) := by
        have hlpos : 0 ≤ 1 + Real.log (k * Δ) := by
          rcases Nat.eq_zero_or_pos (k * Δ) with h0 | hpos
          · have : (k : ℝ) * Δ = 0 := by exact_mod_cast h0
            rw [this, Real.log_zero]; norm_num
          · have : (1 : ℝ) ≤ k * Δ := by exact_mod_cast hpos
            have := Real.log_nonneg this; linarith
        nlinarith
      nlinarith
    exact_mod_cast hfin
  · intro m h x
    exact newCnt_le_of_windows s (w := win s rs) (Nb := Nb s rs n) (R := rnd rs σ) (T := Δ)
      r0 hL.1 hL.2.1 (consistent_rnd rs hL)
      (fun τ p hp => by obtain ⟨j, hj⟩ := mem_rnd rs hp; exact dist_lt_of_mem hj)
      hσ.A hσ.B m h x

end SlidingPuzzle.Hub
