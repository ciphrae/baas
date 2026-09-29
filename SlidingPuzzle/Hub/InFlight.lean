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
(`exists_good_order`).

The definitions (`InsRec`, `Ghost`, `ghostRun`, `newCnt`, `roundIns`,
`Consistent`) are in `Hub/InFlightDefs.lean`. The proof:
* `Hub/ChernoffMaclaurin.lean`, `Hub/ChernoffPerm.lean`, `Hub/ChernoffChain.lean`:
  Maclaurin's inequality and Chernoff bounds for a random permutation, the upper
  tail for position-dependent nested sets;
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

/-- Integer upper rounding of the in-flight estimate `1.376 n` per hub. -/
def Rhub (n : ℕ) : ℕ := 1376 * n / 1000 + 1

theorem Rhub_lower (n : ℕ) : 1376 * n ≤ 1000 * Rhub n := by
  have := Nat.mod_add_div (1376 * n) 1000
  have := Nat.mod_lt (1376 * n) (by norm_num : 0 < 1000)
  unfold Rhub
  omega

theorem Rhub_upper (n : ℕ) : 1000 * Rhub n ≤ 1376 * n + 1000 := by
  have := Nat.mod_add_div (1376 * n) 1000
  unfold Rhub
  omega

/-- `λ_A` is at least `2 log₂ n + 4`. -/
theorem lamA_ge (k s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) : 2 * Nat.log 2 (k * s) + 4 ≤ lamA k s := by
  unfold lamA
  have h1 : 2 ^ (2 * Nat.log 2 (k * s)) ≤ k ^ 3 * s ^ 2 := by
    have hp := Nat.pow_log_le_self 2 (show k * s ≠ 0 by positivity)
    calc 2 ^ (2 * Nat.log 2 (k * s)) = (2 ^ Nat.log 2 (k * s)) ^ 2 := by rw [pow_mul']
      _ ≤ (k * s) ^ 2 := Nat.pow_le_pow_left hp 2
      _ = k ^ 2 * s ^ 2 := by ring
      _ ≤ k ^ 3 * s ^ 2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hk (by norm_num))
  have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) h1
  omega

/-- The capacity condition forces large squares and a large logarithm. -/
theorem capacity_lower_bounds {n k s : ℕ} (hd : HDims n k s) (hk : 500 ≤ k)
    (hP1 : 76 * k * lamA k s ≤ 5 * s) :
    27 ≤ Nat.log 2 n ∧ 58 ≤ lamA k s ∧ 440800 ≤ s ∧ 500 * s ≤ n := by
  have hn := hd.mul
  have hs1 : 1 ≤ s := by have := hd.room; omega
  have hge := lamA_ge k s (by omega) hs1
  rw [hn] at hge
  have hns : 500 * s ≤ n := by rw [← hn]; exact Nat.mul_le_mul_right s hk
  have hsl : 7600 * lamA k s ≤ s := by nlinarith
  have hlog23 : 23 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hlog27 : 27 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  exact ⟨hlog27, by omega, by omega, hns⟩

/-- Lower-tail events: `2 · #events ≤ 2^λ_A`. -/
theorem card_eventsA_le {n k s Δ : ℕ} (hd : HDims n k s) (hΔ : Δ ≤ s ^ 2 + 1) :
    2 * Fintype.card (RowH k × Fin k × Fin Δ) ≤ 2 ^ lamA k s := by
  have hk : 2 ≤ k := hd.two_le
  have hs : 1 ≤ s := by have := hd.room; omega
  have hcard : Fintype.card (RowH k × Fin k × Fin Δ) = 2 * k ^ 3 * Δ := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; ring
  rw [hcard]
  have h2 : Δ ≤ 2 * s ^ 2 := by nlinarith
  have hpos : k ^ 3 * s ^ 2 ≠ 0 := by positivity
  have h3 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (k ^ 3 * s ^ 2)
  unfold lamA
  rw [show Nat.log 2 (k ^ 3 * s ^ 2) + 4 = (Nat.log 2 (k ^ 3 * s ^ 2) + 1) + 3 by ring, pow_add]
  calc 2 * (2 * k ^ 3 * Δ) ≤ 2 * (2 * k ^ 3 * (2 * s ^ 2)) := by gcongr
    _ = 8 * (k ^ 3 * s ^ 2) := by ring
    _ ≤ 2 ^ (Nat.log 2 (k ^ 3 * s ^ 2) + 1) * 2 ^ 3 := by rw [mul_comm]; gcongr; norm_num

/-- Upper-tail events: `2 · #events < 2^λ`. -/
theorem card_eventsB_lt {n k s Δ : ℕ} (hd : HDims n k s) (hks : 8 * k ≤ s)
    (hΔ : Δ ≤ s ^ 2 + 1) :
    2 * Fintype.card (RowH k × Sq k × Fin Δ) < 2 ^ lamN n := by
  have hk : 2 ≤ k := hd.two_le
  have hs : 1 ≤ s := by have := hd.room; omega
  have hn : n = k * s := hd.mul.symm
  have hcard : Fintype.card (RowH k × Sq k × Fin Δ) = 2 * k ^ 4 * Δ := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; ring
  rw [hcard]
  have h2 : Δ ≤ 2 * s ^ 2 := by nlinarith
  have h4 : 8 * (k ^ 4 * s ^ 2) ≤ n ^ 3 := by
    have := Nat.mul_le_mul_left (k ^ 3 * s ^ 2) hks
    rw [hn]
    nlinarith only [this]
  have h5 : n ^ 3 < (n + 1) ^ 3 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have h6 : (n + 1) ^ 3 ≤ 2 ^ lamN n := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    rw [lamN, mul_comm, pow_mul]
    exact Nat.pow_le_pow_left this 3
  calc 2 * (2 * k ^ 4 * Δ) ≤ 2 * (2 * k ^ 4 * (2 * s ^ 2)) := by gcongr
    _ = 8 * (k ^ 4 * s ^ 2) := by ring
    _ ≤ n ^ 3 := h4
    _ < _ := lt_of_lt_of_le h5 h6

/-- Some order of the rounds keeps every hub's in-flight maxima small. -/
theorem exists_good_order {n k s : ℕ} (hd : HDims n k s) (hk500 : 500 ≤ k)
    (hP1 : 76 * k * lamA k s ≤ 5 * s) {Δ : ℕ} (hΔ : Δ ≤ s ^ 2 + 1)
    (rs : Fin Δ → Round k) :
    ∃ σ : Equiv.Perm (Fin Δ), ∀ L : List (InsRec k), Consistent rs σ L →
      ∃ N : Sq k → Sq k → ℕ, (∀ h, ∑ x, N h x ≤ Rhub n) ∧
        ∀ m h x, newCnt s (ghostRun s (fun _ _ => none) (L.take m)) h x ≤ N h x := by
  have hk2 : 2 ≤ k := hd.two_le
  have hk : 0 < k := by omega
  have hs : 1 ≤ s := by have := hd.room; omega
  have hn : n = k * s := hd.mul.symm
  obtain ⟨hlog27, hlam58, hs440, hns⟩ := capacity_lower_bounds hd hk500 hP1
  have hks8 : 8 * k ≤ s := by nlinarith
  obtain ⟨σ, hσ⟩ := exists_goodOrder s rs n hk hP1 (card_eventsA_le hd hΔ)
    (card_eventsB_lt hd hks8 hΔ)
  refine ⟨σ, fun L hL => ?_⟩
  let r0 : InsRec k := ⟨0, (⟨0, hk⟩, ⟨0, hk⟩, true), 0, (⟨0, hk⟩, ⟨0, hk⟩)⟩
  have hroom := hd.room
  have hks : k + 1 ≤ s := by omega
  refine ⟨fun h x => ∑ side : Bool, Nbx s rs n (h.1, h.2, side) x, ?_, ?_⟩
  · intro h
    have hsum : ∑ x, ∑ side : Bool, (Nbx s rs n (h.1, h.2, side) x : ℝ) ≤
        ∑ side : Bool, ((41 / 30 : ℝ) * ((rowLen k s (h.1, h.2, side) : ℝ) + k) +
          41 / 40 * ((k : ℝ) * (k + 1)) + (k : ℝ) * (15 * (lamN n : ℝ))) := by
      rw [sum_comm]
      apply sum_le_sum; intro side _
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
    -- `2 log₂ n + 4 ≤ λ_A`, so `152 k (log₂ n + 1) ≤ 5 s`
    have hge := lamA_ge k s (by omega) hs
    rw [← hn] at hge
    have hkl : 152 * (k * (Nat.log 2 n + 1)) ≤ 5 * s := by
      have := Nat.mul_le_mul_left (76 * k) hge
      nlinarith
    have hkk : 4408 * (k * k) ≤ 5 * n := by
      have := Nat.mul_le_mul_left (76 * k) hlam58
      rw [hn]; nlinarith
    have hklR : 152 * ((k : ℝ) * (Nat.log 2 n + 1)) ≤ 5 * s := by exact_mod_cast hkl
    have hkkR : 4408 * ((k : ℝ) * k) ≤ 5 * n := by exact_mod_cast hkk
    have hnsR : 500 * (s : ℝ) ≤ n := by exact_mod_cast hns
    have hkn : 440800 * (k : ℝ) ≤ n := by
      have : 440800 * k ≤ n := by rw [hn]; nlinarith
      exact_mod_cast this
    have hlamR : (lamN n : ℝ) = 3 * ((Nat.log 2 n : ℝ) + 1) := by
      simp only [lamN]; push_cast; ring
    have hfin : ∑ x, ∑ side : Bool, (Nbx s rs n (h.1, h.2, side) x : ℝ) ≤ (Rhub n : ℝ) := by
      refine hsum.trans ?_
      rw [Fintype.sum_bool, hlamR]
      have hR : 1376 * (n : ℝ) ≤ 1000 * (Rhub n : ℝ) := by exact_mod_cast Rhub_lower n
      nlinarith
    exact_mod_cast hfin
  · intro m h x
    exact newCnt_le_of_segments s (w := win s rs) (Nb := Nbx s rs n) (R := rnd rs σ) (T := Δ)
      r0 hL.1 hL.2.1 (consistent_rnd rs hL)
      (fun τ p hp => by obtain ⟨j, hj⟩ := mem_rnd rs hp; exact dist_lt_of_mem hj)
      (fun H j hj => insPos_sub_prev k s H hks hj) (fun H => insPos_zero_lt k s H hks)
      hσ.A hσ.B m h x

end SlidingPuzzle.Hub
