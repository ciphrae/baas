import SlidingPuzzle.Hub.InFlightOrder
import SlidingPuzzle.Hub.InFlightSum
import SlidingPuzzle.Hub.InFlightSegment

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
* `Hub/InFlightPush.lean`, `Hub/InFlightWindow.lean`: the push lemma and
  window bookkeeping;
* `Hub/InFlightSegment.lean`: segmented residence, the deterministic bound
  from window properties of the order;
* `Hub/InFlightRound.lean`: insertions of a round, window parameters;
* `Hub/InFlightOrder.lean`: a good order exists (union bound);
* `Hub/InFlightSum.lean`: summing the bounds (the windows telescope).

The resulting budget `Rhub n` is linear in `n`: a hub holds `O(n)` tiles in
flight, not `O(n log n)`. -/
namespace SlidingPuzzle.Hub

open Finset

/-- Integer upper rounding of the in-flight estimate `1.5616 n` per hub. -/
def Rhub (n : ℕ) : ℕ := 15616 * n / 10000 + 1

theorem Rhub_lower (n : ℕ) : 15616 * n ≤ 10000 * Rhub n := by
  have := Nat.mod_add_div (15616 * n) 10000
  have := Nat.mod_lt (15616 * n) (by norm_num : 0 < 10000)
  unfold Rhub
  omega

theorem Rhub_upper (n : ℕ) : 10000 * Rhub n ≤ 15616 * n + 10000 := by
  have := Nat.mod_add_div (15616 * n) 10000
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
    (hP1 : 169 * k * (Nat.log 2 n + 1) ≤ s) :
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

/-- Some order of the rounds keeps every hub's in-flight maxima small. -/
theorem exists_good_order {n k s : ℕ} (hd : HDims n k s)
    (hP1 : 169 * k * (Nat.log 2 n + 1) ≤ s) (hsk : s ≤ k ^ 3) {Δ : ℕ} (hΔ : Δ ≤ s ^ 2 + 1)
    (rs : Fin Δ → Round k) :
    ∃ σ : Equiv.Perm (Fin Δ), ∀ L : List (InsRec k), Consistent rs σ L →
      ∃ N : Sq k → Sq k → ℕ, (∀ h, ∑ x, N h x ≤ Rhub n) ∧
        ∀ m h x, newCnt s (ghostRun s (fun _ _ => none) (L.take m)) h x ≤ N h x := by
  have hk2 : 2 ≤ k := hd.two_le
  have hk : 0 < k := by omega
  have hs : 1 ≤ s := by have := hd.room; omega
  have hn : n = k * s := hd.mul.symm
  set ℓ := Nat.log 2 n + 1 with hℓ
  have hlam : 42 * k * lamN n ≤ s := by
    have e1 : 42 * k * lamN n = 168 * (k * ℓ) := by rw [lamN]; ring
    have e2 : 169 * k * ℓ = 169 * (k * ℓ) := by ring
    omega
  obtain ⟨σ, hσ⟩ := exists_goodOrder s rs n hk hlam (card_events_lt hd hΔ)
  refine ⟨σ, fun L hL => ?_⟩
  let r0 : InsRec k := ⟨0, (⟨0, hk⟩, ⟨0, hk⟩, true), 0, (⟨0, hk⟩, ⟨0, hk⟩)⟩
  have hroom := hd.room
  have hks : k + 1 ≤ s := by omega
  refine ⟨fun h x => ∑ side : Bool, ∑ d ∈ range k, Nb s rs n (h.1, h.2, side) d x, ?_, ?_⟩
  · intro h
    have hsum : ∑ x, ∑ side : Bool, ∑ d ∈ range k, (Nb s rs n (h.1, h.2, side) d x : ℝ) ≤
        ∑ side : Bool, ((51 / 40 : ℝ) * ((rowLen k s (h.1, h.2, side) : ℝ) + k) +
          17 / 16 * ((k : ℝ) * (k + 1)) + (k : ℝ) * k * (6 * (lamN n : ℝ))) := by
      rw [sum_comm]
      apply sum_le_sum; intro side _
      rw [sum_comm]
      exact sum_half_le s rs hks n _
    have hlen : (rowLen k s (h.1, h.2, true) : ℝ) + rowLen k s (h.1, h.2, false) + 2 * k ≤ n := by
      have hc := h.2.isLt
      have : rowLen k s (h.1, h.2, true) + rowLen k s (h.1, h.2, false) + 2 * k ≤ n := by
        simp only [rowLen, if_true, Bool.false_eq_true, if_false]
        rw [hn, ← add_mul]
        have h1 := Nat.mul_le_mul_right s (show k - 1 - h.2.val + h.2.val + 1 ≤ k by omega)
        rw [add_mul, one_mul] at h1
        omega
      exact_mod_cast this
    have hℓ10 : 10 ≤ ℓ := (capacity_lower_bounds hd hP1).1
    have hstock : 169 * (k : ℝ) * k * ℓ ≤ n := by
      have h := Nat.mul_le_mul_left k hP1
      rw [hd.mul] at h
      have h' : 169 * k * k * ℓ ≤ n := by
        simpa only [← hℓ, mul_assoc, mul_left_comm, mul_comm] using h
      exact_mod_cast h'
    have hℓR : (10 : ℝ) ≤ ℓ := by exact_mod_cast hℓ10
    have hkk : 1690 * ((k : ℝ) * k) ≤ n := by
      have : 0 ≤ (k : ℝ) * k := by positivity
      nlinarith
    have hk1 : (k : ℝ) ≤ k * k := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      nlinarith
    have hlamR : (lamN n : ℝ) = 4 * ℓ := by simp only [lamN, hℓ]; push_cast; ring
    have hfin : ∑ x, ∑ side : Bool, ∑ d ∈ range k, (Nb s rs n (h.1, h.2, side) d x : ℝ) ≤
        (Rhub n : ℝ) := by
      refine hsum.trans ?_
      rw [Fintype.sum_bool, hlamR]
      have hR : 15616 * (n : ℝ) ≤ 10000 * (Rhub n : ℝ) := by exact_mod_cast Rhub_lower n
      nlinarith
    exact_mod_cast hfin
  · intro m h x
    exact newCnt_le_of_segments s (w := win s rs) (Nb := Nb s rs n) (R := rnd rs σ) (T := Δ)
      r0 hL.1 hL.2.1 (consistent_rnd rs hL)
      (fun τ p hp => by obtain ⟨j, hj⟩ := mem_rnd rs hp; exact dist_lt_of_mem hj)
      (fun H j hj => insPos_sub_prev k s H hks hj) (fun H => insPos_zero_lt k s H hks)
      hσ.A hσ.B m h x

end SlidingPuzzle.Hub
