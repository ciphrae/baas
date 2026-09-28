import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Conditional hierarchy accounting

Research only: no grouped puzzle routing construction is assumed to exist.
The hypotheses below expose the missing resource estimates. These lemmas
check their consequences, including slack in choosing an integer grid.
-/
set_option autoImplicit false

namespace SlidingPuzzle.HierarchyResearch

open Finset

/-- Local failure bounds propagate additively down a layered route network.
`A j` includes the classwise in-flight maxima and one unit per active class.
The routing construction still has to establish the recurrence. -/
theorem shortage_prefix (B A : ℕ → ℝ) (hzero : B 0 = 0)
    (hstep : ∀ j, B (j + 1) ≤ B j + A j) (h : ℕ) :
    B h ≤ ∑ j ∈ range h, A j := by
  induction h with
  | zero => simp [hzero]
  | succ h ih =>
    rw [sum_range_succ]
    exact (hstep h).trans (by linarith)

/-- Summing all layers loses at most another depth factor. -/
theorem shortage_total (B A : ℕ → ℝ) (hzero : B 0 = 0)
    (hstep : ∀ j, B (j + 1) ≤ B j + A j)
    (hA : ∀ j, 0 ≤ A j) (h : ℕ) :
    (∑ j ∈ range h, B (j + 1)) ≤ (h : ℝ) * ∑ j ∈ range h, A j := by
  calc
    _ ≤ ∑ _j ∈ range h, ∑ i ∈ range h, A i := by
      apply sum_le_sum
      intro j hj
      exact (shortage_prefix B A hzero hstep (j + 1)).trans
        (sum_le_sum_of_subset_of_nonneg (range_mono (by simpa using hj))
          (fun i _ _ => hA i))
    _ = _ := by simp

/-- Quantitative projection of a one-level extension contract. It says nothing
about the existence or correctness of a physical routing implementation. -/
structure AdditiveExtension (resource : ℕ → ℝ) (increment : ℝ) : Prop where
  zero : resource 0 = 0
  step : ∀ j, resource (j + 1) ≤ resource j + increment

theorem AdditiveExtension.bound {resource : ℕ → ℝ} {increment : ℝ}
    (law : AdditiveExtension resource increment) (h : ℕ) :
    resource h ≤ (h : ℝ) * increment := by
  simpa using shortage_prefix resource (fun _ => increment) law.zero law.step h

/-- Per-level increments, for branching `b`, outer grid `k`, and board side `n`.
Absolute constants may be handled by scaling the recorded resources. -/
structure LevelExtensionBudgets (n k b : ℝ)
    (width span rounding classes : ℕ → ℝ) : Prop where
  width_law : AdditiveExtension width b
  span_law : AdditiveExtension span (k * n * b)
  rounding_law : AdditiveExtension rounding (k ^ 3 * b)
  class_law : AdditiveExtension classes (k ^ 3)

theorem level_extension_bounds {n k b : ℝ}
    {width span rounding classes : ℕ → ℝ}
    (law : LevelExtensionBudgets n k b width span rounding classes) (h : ℕ) :
    width h ≤ h * b ∧ span h ≤ h * (k * n * b) ∧
    rounding h ≤ h * (k ^ 3 * b) ∧ classes h ≤ h * k ^ 3 :=
  ⟨law.width_law.bound h, law.span_law.bound h,
   law.rounding_law.bound h, law.class_law.bound h⟩

/-- A bounded per-stage charge gives quadratic, rather than exponential,
depth dependence in the total number of shortages. -/
theorem shortage_uniform (B : ℕ → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hzero : B 0 = 0) (hstep : ∀ j, B (j + 1) ≤ B j + A) (h : ℕ) :
    (∑ j ∈ range h, B (j + 1)) ≤ (h : ℝ) ^ 2 * A := by
  have ht := shortage_total B (fun _ => A) hzero hstep (fun _ => hA) h
  simpa [pow_two, mul_assoc] using ht

noncomputable def gridPower (h : ℝ) : ℝ := h / (2 * h + 1)
noncomputable def errorPower (h : ℝ) : ℝ := (5 * h + 3) / (2 * h + 1)
noncomputable def slackGap (h : ℝ) : ℝ := 2 / (2 * h + 1)

theorem exponent_identities {h : ℝ} (hh : 0 < h) :
    3 - gridPower h = errorPower h ∧
    gridPower h * (1 + 1 / h) + 2 = errorPower h ∧
    1 + gridPower h * 3 + slackGap h = errorPower h ∧
    errorPower h = 5 / 2 + 1 / (4 * h + 2) := by
  have hd : 2 * h + 1 ≠ 0 := by positivity
  have hd' : 4 * h + 2 ≠ 0 := by positivity
  unfold gridPower errorPower slackGap
  constructor
  · field_simp; ring
  constructor
  · field_simp; ring
  constructor <;> field_simp <;> ring

/-- Conditional analytic estimate. `Q` is the loss in rounding the grid down.
No routing hypothesis is concealed: this only bounds the displayed budget. -/
theorem balanced_budget {n k h Q : ℝ}
    (hn : 1 ≤ n) (hh : 0 < h) (hQ : 0 < Q) (hk : 0 < k)
    (hlo : n ^ gridPower h / Q ≤ k) (hhi : k ≤ n ^ gridPower h) :
    n ^ (3 : ℕ) / k + k ^ (1 + 1 / h) * n ^ (2 : ℕ) +
        n * k ^ (3 : ℕ) * Real.log n ≤
      (Q + 1 + 1 / slackGap h) * n ^ errorPower h := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have ha : 0 < n ^ gridPower h := Real.rpow_pos_of_pos hn0 _
  have he := exponent_identities hh
  have hg : 0 < slackGap h := by unfold slackGap; positivity
  have hfirst : n ^ (3 : ℕ) / k ≤ Q * n ^ errorPower h := by
    have hd := div_le_div_of_nonneg_left (show 0 ≤ n ^ (3 : ℕ) by positivity)
      (div_pos ha hQ) hlo
    have hid : n ^ (3 : ℕ) / (n ^ gridPower h / Q) = Q * n ^ errorPower h := by
      rw [← he.1, Real.rpow_sub hn0]
      norm_num
      field_simp
    exact hd.trans_eq hid
  have hsecond : k ^ (1 + 1 / h) * n ^ (2 : ℕ) ≤ n ^ errorPower h := by
    calc
      _ ≤ (n ^ gridPower h) ^ (1 + 1 / h) * n ^ (2 : ℕ) := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hk.le hhi (by positivity)) (by positivity)
      _ = n ^ errorPower h := by
        rw [← Real.rpow_mul hn0.le, ← Real.rpow_natCast n 2,
          ← Real.rpow_add hn0]
        norm_num
        simpa only [one_div] using congrArg (fun z : ℝ => n ^ z) he.2.1
  have hthird : n * k ^ (3 : ℕ) * Real.log n ≤
      (1 / slackGap h) * n ^ errorPower h := by
    calc
      _ ≤ n * (n ^ gridPower h) ^ (3 : ℕ) * (n ^ slackGap h / slackGap h) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk.le hhi 3) hn0.le
        · exact Real.log_le_rpow_div hn0.le hg
        · exact Real.log_nonneg hn
        · positivity
      _ = (1 / slackGap h) * n ^ errorPower h := by
        rw [← Real.rpow_natCast (n ^ gridPower h) 3, ← Real.rpow_mul hn0.le]
        have hid : n * n ^ (gridPower h * 3) * n ^ slackGap h = n ^ errorPower h := by
          conv_lhs => lhs; lhs; rw [← Real.rpow_one n]
          rw [← Real.rpow_add hn0, ← Real.rpow_add hn0, he.2.2.1]
        calc
          _ = (1 / slackGap h) * (n * n ^ (gridPower h * 3) * n ^ slackGap h) := by ring
          _ = _ := by rw [hid]
  linarith

/-- The additional per-round rounding inventory `k^3 b` is absorbed by
`k b n` whenever `k^2 ≤ n`; multiplying by cleanup cost `n` preserves this. -/
theorem rounding_inventory_absorbed {n k b : ℝ}
    (hn : 0 ≤ n) (hk : 0 ≤ k) (hb : 0 ≤ b) (hcap : k ^ 2 ≤ n) :
    n * k ^ 3 * b ≤ k * b * n ^ 2 := by
  nlinarith [mul_le_mul_of_nonneg_left hcap (show 0 ≤ n * k * b by positivity)]

/-- Genuine integer branching realizes the balanced grid up to `2^h`.
The routing hypothesis must additionally cover boundary remainders of the board. -/
theorem exists_integer_branching {n : ℝ} (hn : 1 ≤ n) (h : ℕ) (hh : 0 < h) :
    ∃ b : ℕ, 1 ≤ b ∧
      n ^ gridPower h / (2 : ℝ) ^ h ≤ (b : ℝ) ^ h ∧
      (b : ℝ) ^ h ≤ n ^ gridPower h := by
  let x : ℝ := n ^ (1 / (2 * (h : ℝ) + 1))
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hx : 1 ≤ x := Real.one_le_rpow hn (by positivity)
  have hf : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
  have hf' : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hf
  have hlo : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one x
    linarith
  have hhi : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hid : x ^ h = n ^ gridPower h := by
    dsimp [x]
    rw [← Real.rpow_natCast _ h, ← Real.rpow_mul hn0.le]
    congr 1
    unfold gridPower
    ring
  refine ⟨⌊x⌋₊, hf, ?_, ?_⟩
  · have hp := pow_le_pow_left₀ (show 0 ≤ x / 2 by positivity) hlo h
    rwa [div_pow, hid] at hp
  · exact (pow_le_pow_left₀ (by positivity) hhi h).trans_eq hid

/-- Arbitrarily large fixed depths approach exponent `5/2` from above. -/
theorem exists_depth {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℕ, 0 < h ∧ errorPower h ≤ 5 / 2 + ε := by
  obtain ⟨h, hh⟩ := exists_nat_gt (1 / ε + 1)
  have hi : 0 < 1 / ε := by positivity
  have hpos : 0 < (h : ℝ) := by linarith
  have hd : 0 < 4 * (h : ℝ) + 2 := by positivity
  refine ⟨h, by exact_mod_cast hpos, ?_⟩
  rw [(exponent_identities hpos).2.2.2]
  have hx : 1 < (h : ℝ) * ε := (div_lt_iff₀ hε).mp (by linarith : 1 / ε < (h : ℝ))
  have : 1 / (4 * (h : ℝ) + 2) ≤ ε := (div_le_iff₀ hd).mpr (by nlinarith)
  linarith

/-- A conditional all-sizes consequence. The premise must come from a routing
construction; this file does not establish it for sliding puzzles. -/
theorem fixed_depth_implies_epsilon (E : ℕ → ℝ)
    (hfixed : ∀ h : ℕ, 0 < h → ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → E n ≤ C * (n : ℝ) ^ errorPower h)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      E n ≤ C * (n : ℝ) ^ (5 / 2 + ε) := by
  obtain ⟨h, hh, hp⟩ := exists_depth hε
  obtain ⟨C, hC, N, hN⟩ := hfixed h hh
  refine ⟨C, hC, max N 1, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_right N 1).trans hn
  exact (hN n ((le_max_left N 1).trans hn)).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hp) hC)

/-- An explicit missing algorithmic hypothesis. For each fixed depth, the
construction must work for all sufficiently large board sizes and every
balanced integer branching choice, INCLUDING nondivisible boundary strips.
This is not asserted for the existing solver. -/
def HierarchyBudget (E : ℕ → ℝ) : Prop :=
  ∀ h : ℕ, 0 < h → ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n → 1 ≤ n → ∀ b : ℕ, 1 ≤ b →
      (n : ℝ) ^ gridPower h / (2 : ℝ) ^ h ≤ (b : ℝ) ^ h →
      (b : ℝ) ^ h ≤ (n : ℝ) ^ gridPower h →
      E n ≤ C * ((n : ℝ) ^ (3 : ℕ) / (b : ℝ) ^ h +
        ((b : ℝ) ^ h) ^ (1 + 1 / (h : ℝ)) * (n : ℝ) ^ (2 : ℕ) +
        (n : ℝ) * ((b : ℝ) ^ h) ^ (3 : ℕ) * Real.log n)

/-- The full conditional implication uses an integer branching choice for
EVERY sufficiently large n, not just the subsequence n = t^(2h+1). -/
theorem hierarchy_budget_implies_fixed_depth {E : ℕ → ℝ} (hbudget : HierarchyBudget E)
    (h : ℕ) (hh : 0 < h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      E n ≤ C * (n : ℝ) ^ errorPower h := by
  obtain ⟨C, hC, N, hN⟩ := hbudget h hh
  have hh' : 0 < (h : ℝ) := by exact_mod_cast hh
  have hg : 0 < slackGap h := by unfold slackGap; positivity
  refine ⟨C * ((2 : ℝ) ^ h + 1 + 1 / slackGap h), by positivity, max N 1, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  obtain ⟨b, hb, hlo, hhi⟩ := exists_integer_branching hn' h hh
  have hb' : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have he := hN n ((le_max_left N 1).trans hn) hn1 b hb hlo hhi
  have ha := balanced_budget hn' hh' (show (0 : ℝ) < 2 ^ h by positivity)
    (show (0 : ℝ) < (b : ℝ) ^ h by positivity) hlo hhi
  exact he.trans ((mul_le_mul_of_nonneg_left ha hC).trans_eq (by ring))

theorem hierarchy_budget_implies_epsilon {E : ℕ → ℝ} (hbudget : HierarchyBudget E)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      E n ≤ C * (n : ℝ) ^ (5 / 2 + ε) :=
  fixed_depth_implies_epsilon E (hierarchy_budget_implies_fixed_depth hbudget) hε

end SlidingPuzzle.HierarchyResearch
