import SlidingPuzzle.Hub.InFlightRound
import SlidingPuzzle.Hub.ChernoffChain

/-! # A good order of the rounds exists

(A) For every half `H`, band `d < k` and start time `τ0`, the orders with fewer
than `s` pushes in `(τ0, τ0 + w_d]` are at most a `2^(-λ_A)` fraction of all
orders (`card_badA`, lower tail, capacity `76kλ_A ≤ 5s`).

(B) For every half `H`, class `x` and time `τl`, the orders with more than
`Nbx H x` class-`x` insertions counted over all distances `d`, each in its own
window `[τl - W_d, τl]`, are at most a `2^(-λ)` fraction (`card_badB`). The
windows end at `τl`, so the rounds counted at a position form a chain, and the
nested-set upper tail of `Hub/ChernoffChain.lean` applies with a single slack
per class.

Both families of events are small against `2^λ_A` and `2^λ`, so some order
avoids all of them (`exists_goodOrder`). -/
namespace SlidingPuzzle.Hub

open Finset

variable {k Δ : ℕ} (s : ℕ) (rs : Fin Δ → Round k)

/-- The times `(τ0, τ0 + w]`. -/
def winA (Δ τ0 w : ℕ) : Finset (Fin Δ) := univ.filter fun τ => τ.val ∈ Ioc τ0 (τ0 + w)

theorem card_winA {τ0 w : ℕ} (h : τ0 + w < Δ) : (winA Δ τ0 w).card = w := by
  rw [winA, card_fin_filter_mem, filter_true_of_mem (fun i hi => by rw [mem_Ioc] at hi; omega),
    Nat.card_Ioc]
  omega

/-- Orders violating (A) at `(H, d, τ0)`. -/
noncomputable def badA (H : RowH k) (d : ℕ) (τ0 : Fin Δ) : Finset (Equiv.Perm (Fin Δ)) :=
  univ.filter fun σ => τ0.val + win s rs H d < Δ ∧
    ∑ τ ∈ winA Δ τ0.val (win s rs H d), gcnt rs H d (σ τ) < s

/-- Rounds that insert class `x` into `H` from a distance `d` whose window
`[τl - W_d, τl]` contains the position `τ`. Since the windows end at `τl`,
these sets grow with `τ` up to `τl` and are empty after it: a chain. -/
noncomputable def chainSet (H : RowH k) (x : Sq k) (τl : ℕ) (τ : Fin Δ) : Finset (Fin Δ) :=
  univ.filter fun j => ∃ d ∈ range k, τl - wsum s rs H d ≤ τ.val ∧ τ.val ≤ τl ∧
    acnt rs H d x j ≠ 0

/-- Class-`x` insertions into `H` from distance `d` in the window `[τl - W_d, τl]`,
summed over `d`. -/
noncomputable def mcnt (H : RowH k) (x : Sq k) (τl : ℕ) (σ : Equiv.Perm (Fin Δ)) : ℕ :=
  ∑ d ∈ range k, ∑ τ ∈ univ.filter (fun τ : Fin Δ => τ.val ∈ Icc (τl - wsum s rs H d) τl),
    acnt rs H d x (σ τ)

/-- Orders violating (B) at `(H, x, τl)`. -/
noncomputable def badB (n : ℕ) (H : RowH k) (x : Sq k) (τl : Fin Δ) :
    Finset (Equiv.Perm (Fin Δ)) :=
  univ.filter fun σ => Nbx s rs n H x < mcnt s rs H x τl.val σ

/-- `x < (x / b + 1) * b` as reals. -/
theorem nat_div_add_one_gt (x b : ℕ) (hb : 0 < b) : (x : ℝ) / b < ((x / b : ℕ) : ℝ) + 1 := by
  have h := Nat.lt_div_mul_add (a := x) hb
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_lt_iff₀ hbR]
  have : (x : ℝ) < ((x / b : ℕ) : ℝ) * b + b := by exact_mod_cast h
  linarith

theorem card_badA {lam : ℕ} (hk : 0 < k) (hlam : 76 * k * lam ≤ 5 * s) (H : RowH k) (d : ℕ)
    (τ0 : Fin Δ) : (badA s rs H d τ0).card * 2 ^ lam ≤ Δ.factorial := by
  set w := win s rs H d with hw
  set B := Btot rs H d with hB
  -- trivial cases: the window does not fit
  by_cases hfit : τ0.val + w < Δ
  swap
  · have : badA s rs H d τ0 = ∅ := by
      rw [badA, filter_eq_empty_iff]; intro σ _ h; exact hfit h.1
    rw [this]; simp
  have hB0 : B ≠ 0 := by
    intro h0
    have : w = Δ := by rw [hw, win, if_pos h0]
    omega
  have hwdef : w = 4 * s * Δ / (3 * B) + 1 := by
    have : w = min Δ (4 * s * Δ / (3 * B) + 1) := by rw [hw, win, if_neg hB0]
    rw [this] at hfit ⊢
    rcases min_choice Δ (4 * s * Δ / (3 * B) + 1) with h | h
    · rw [h] at hfit; omega
    · exact h
  have hΔ : 0 < Δ := Nat.lt_of_le_of_lt (Nat.zero_le _) τ0.isLt
  have hBpos : 0 < B := Nat.pos_of_ne_zero hB0
  have hkey : 4 * s * Δ < w * (3 * B) := by
    rw [hwdef, add_mul, one_mul]; exact Nat.lt_div_mul_add (by omega)
  -- Chernoff
  set g : Fin Δ → ℝ := fun j => (gcnt rs H d j : ℝ) with hg
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hg0 : ∀ j, 0 ≤ g j := fun j => Nat.cast_nonneg _
  have hgK : ∀ j, g j ≤ k := fun j => by
    simp only [hg]; exact_mod_cast countP_half_le (rs j) H (fun p => d ≤ p.2.1)
  have hcard : (Fintype.card (Fin Δ)) = Δ := Fintype.card_fin Δ
  have hT := card_winA (Δ := Δ) hfit
  have hsumg : ∑ j, g j = B := by simp only [hg, hB, Btot]; push_cast; rfl
  have hch := card_lower_tail_log (winA Δ τ0.val w) g hkR hg0 hgK (by rw [hcard]; exact hΔ)
  rw [hT, hsumg, hcard] at hch
  set μ : ℝ := (w : ℝ) * B / Δ with hμ
  have hΔR : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  have hμgt : 4 * (s : ℝ) < 3 * μ := by
    rw [hμ, mul_div_assoc', lt_div_iff₀ hΔR]
    have : ((4 * s * Δ : ℕ) : ℝ) < ((w * (3 * B) : ℕ) : ℝ) := by exact_mod_cast hkey
    push_cast at this; linarith
  have hsub : badA s rs H d τ0 ⊆ univ.filter fun σ : Equiv.Perm (Fin Δ) =>
      ∑ τ ∈ winA Δ τ0.val w, g (σ τ) ≤ 3 / 4 * μ := by
    intro σ hσ
    simp only [badA, mem_filter, mem_univ, true_and] at hσ ⊢
    have h1 : ∑ τ ∈ winA Δ τ0.val w, g (σ τ) + 1 ≤ s := by
      simp only [hg]; exact_mod_cast hσ.2
    linarith
  have hc1 : ((badA s rs H d τ0).card : ℝ) ≤ Δ.factorial * Real.exp (-(3423 * μ) / (100000 * k)) :=
    (Nat.cast_le.mpr (card_le_card hsub)).trans hch
  -- `2^λ ≤ exp(3423μ / (100000 k))`
  have hlamR : 76 * (k : ℝ) * lam ≤ 5 * s := by exact_mod_cast hlam
  have h2lam : (2 : ℝ) ^ lam ≤ Real.exp (3423 * μ / (100000 * k)) := by
    have hlog : Real.log 2 ≤ 6931471808 / 10000000000 := by linarith [Real.log_two_lt_d9]
    calc (2 : ℝ) ^ lam = Real.exp (lam * Real.log 2) := by
          rw [Real.exp_nat_mul, Real.exp_log two_pos]
      _ ≤ Real.exp (3423 * μ / (100000 * k)) := by
          apply Real.exp_le_exp.mpr
          rw [le_div_iff₀ (by positivity)]
          have : (lam : ℝ) * Real.log 2 ≤ 6931471808 / 10000000000 * lam := by
            have := Nat.cast_nonneg (α := ℝ) lam
            nlinarith
          nlinarith
  have hfin : ((badA s rs H d τ0).card : ℝ) * 2 ^ lam ≤ Δ.factorial := by
    calc ((badA s rs H d τ0).card : ℝ) * 2 ^ lam
        ≤ Δ.factorial * Real.exp (-(3423 * μ) / (100000 * k)) *
            Real.exp (3423 * μ / (100000 * k)) := by
          gcongr
      _ = Δ.factorial := by
          rw [mul_assoc, ← Real.exp_add]; simp [neg_div]
  exact_mod_cast hfin

omit s rs in
theorem sum_ite_le_ite_exists {K : ℕ} (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℕ)
    (hf : ∑ d ∈ range K, f d ≤ 1) :
    ∑ d ∈ range K, (if P d then f d else 0) ≤ if ∃ d ∈ range K, P d ∧ f d ≠ 0 then 1 else 0 := by
  split_ifs with h
  · exact (sum_le_sum fun d _ => by split_ifs <;> simp).trans hf
  · push Not at h
    apply le_of_eq
    refine sum_eq_zero fun d hd => ?_
    split_ifs with hP
    · exact h d hd hP
    · rfl

omit s rs in
theorem ite_exists_le_sum_ite {K : ℕ} (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℕ) :
    (if ∃ d ∈ range K, P d ∧ f d ≠ 0 then 1 else 0) ≤ ∑ d ∈ range K, (if P d then f d else 0) := by
  split_ifs with h
  · obtain ⟨d, hd, hP, hf⟩ := h
    calc 1 ≤ (if P d then f d else 0) := by rw [if_pos hP]; omega
      _ ≤ _ := single_le_sum (f := fun d => if P d then f d else 0) (fun _ _ => Nat.zero_le _) hd
  · exact Nat.zero_le _

theorem chainSet_chain (H : RowH k) (x : Sq k) (τl : ℕ) (τ τ' : Fin Δ) :
    chainSet s rs H x τl τ ⊆ chainSet s rs H x τl τ' ∨
      chainSet s rs H x τl τ' ⊆ chainSet s rs H x τl τ := by
  have key : ∀ a b : Fin Δ, a.val ≤ b.val →
      chainSet s rs H x τl a ⊆ chainSet s rs H x τl b ∨
        chainSet s rs H x τl b ⊆ chainSet s rs H x τl a := by
    intro a b hab
    by_cases hb : b.val ≤ τl
    · left
      intro j hj
      simp only [chainSet, mem_filter, mem_univ, true_and] at hj ⊢
      obtain ⟨d, hd, h1, h2, h3⟩ := hj
      exact ⟨d, hd, by omega, hb, h3⟩
    · right
      intro j hj
      simp only [chainSet, mem_filter, mem_univ, true_and] at hj
      obtain ⟨d, -, -, h2, -⟩ := hj
      omega
  rcases le_total τ.val τ'.val with h | h
  · exact key τ τ' h
  · exact (key τ' τ h).symm

/-- The merged count is at most the number of positions in their chain sets. -/
theorem mcnt_le_card (H : RowH k) (x : Sq k) (τl : ℕ) (σ : Equiv.Perm (Fin Δ)) :
    mcnt s rs H x τl σ ≤ (univ.filter fun τ => σ τ ∈ chainSet s rs H x τl τ).card := by
  unfold mcnt
  simp_rw [sum_filter]
  rw [sum_comm, card_filter]
  refine sum_le_sum fun τ _ => ?_
  have h := sum_ite_le_ite_exists (K := k) (fun d => τ.val ∈ Icc (τl - wsum s rs H d) τl)
    (fun d => acnt rs H d x (σ τ)) (sum_count_roundIns_le_one _ H x)
  refine h.trans (le_of_eq ?_)
  congr 1
  simp only [chainSet, mem_filter, mem_univ, true_and, mem_Icc]
  apply propext
  constructor
  · rintro ⟨d, hd, ⟨h1, h2⟩, h3⟩; exact ⟨d, hd, h1, h2, h3⟩
  · rintro ⟨d, hd, h1, h2, h3⟩; exact ⟨d, hd, ⟨h1, h2⟩, h3⟩

/-- The chain sets have total size at most `Mtot`. -/
theorem sum_card_chainSet_le (H : RowH k) (x : Sq k) (τl : ℕ) :
    ∑ τ, (chainSet s rs H x τl τ).card ≤ Mtot s rs H x := by
  have h1 : ∀ τ : Fin Δ, (chainSet s rs H x τl τ).card ≤
      ∑ j, ∑ d ∈ range k, (if τ.val ∈ Icc (τl - wsum s rs H d) τl then acnt rs H d x j else 0) := by
    intro τ
    rw [chainSet, card_filter]
    refine sum_le_sum fun j _ => ?_
    refine le_trans (le_of_eq ?_) (ite_exists_le_sum_ite (K := k)
      (fun d => τ.val ∈ Icc (τl - wsum s rs H d) τl) (fun d => acnt rs H d x j))
    congr 1
    simp only [mem_Icc]
    apply propext
    constructor
    · rintro ⟨d, hd, h1, h2, h3⟩; exact ⟨d, hd, ⟨h1, h2⟩, h3⟩
    · rintro ⟨d, hd, ⟨h1, h2⟩, h3⟩; exact ⟨d, hd, h1, h2, h3⟩
  have h2 : ∑ τ : Fin Δ, ∑ j, ∑ d ∈ range k,
      (if τ.val ∈ Icc (τl - wsum s rs H d) τl then acnt rs H d x j else 0) =
      ∑ d ∈ range k, ∑ τ : Fin Δ,
        (if τ.val ∈ Icc (τl - wsum s rs H d) τl then Atot rs H d x else 0) := by
    rw [sum_congr rfl fun τ _ => sum_comm, sum_comm]
    refine sum_congr rfl fun d _ => sum_congr rfl fun τ _ => ?_
    split_ifs <;> simp [Atot]
  refine (sum_le_sum fun τ _ => h1 τ).trans (h2.trans_le (sum_le_sum fun d _ => ?_))
  rw [← sum_filter, sum_const, smul_eq_mul, mul_comm]
  have hw : (univ.filter fun τ : Fin Δ => τ.val ∈ Icc (τl - wsum s rs H d) τl).card ≤
      wsum s rs H d + 1 := by
    rw [card_fin_filter_mem]
    exact (card_filter_le _ _).trans (by rw [Nat.card_Icc]; omega)
  exact Nat.mul_le_mul_left _ hw

theorem card_badB (n : ℕ) (H : RowH k) (x : Sq k) (τl : Fin Δ) :
    (badB s rs n H x τl).card * 2 ^ lamN n ≤ Δ.factorial := by
  have hΔ : 0 < Δ := Nat.lt_of_le_of_lt (Nat.zero_le _) τl.isLt
  have hΔR : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  have hcard : Fintype.card (Fin Δ) = Δ := Fintype.card_fin Δ
  obtain ⟨A, hA⟩ : ∃ A, A = chainSet s rs H x τl.val := ⟨_, rfl⟩
  have hch := card_upper_tail_chain (univ : Finset (Fin Δ)) A
    (hA ▸ chainSet_chain s rs H x τl.val) (15 * lamN n) (by rw [hcard]; exact hΔ)
  rw [hcard] at hch
  have hμN : ∑ τ, (A τ).card ≤ Mtot s rs H x := hA ▸ sum_card_chainSet_le s rs H x τl.val
  have hμ : (∑ τ, ((A τ).card : ℝ)) ≤ Mtot s rs H x := by exact_mod_cast hμN
  have hsub : badB s rs n H x τl ⊆ univ.filter fun σ : Equiv.Perm (Fin Δ) =>
      41 / 40 * ((∑ τ, ((A τ).card : ℝ)) / Δ) + ((15 * lamN n : ℕ) : ℝ) ≤
        ((univ.filter fun τ => σ τ ∈ A τ).card : ℝ) := by
    intro σ hσ
    simp only [badB, mem_filter, mem_univ, true_and] at hσ ⊢
    have hm : mcnt s rs H x τl.val σ ≤ (univ.filter fun τ => σ τ ∈ A τ).card :=
      hA ▸ mcnt_le_card s rs H x τl.val σ
    by_cases hM : Mtot s rs H x = 0
    · rw [Nbx, if_pos hM] at hσ
      have h0 : ∑ τ, (A τ).card = 0 := by omega
      have : (univ.filter fun τ => σ τ ∈ A τ).card = 0 := by
        rw [card_eq_zero, filter_eq_empty_iff]
        intro τ _ hτ
        have := (sum_eq_zero_iff.mp h0) τ (mem_univ _)
        rw [card_eq_zero] at this
        rw [this] at hτ; simp at hτ
      omega
    · rw [Nbx, if_neg hM] at hσ
      have h1 : ((41 * Mtot s rs H x / (40 * Δ) : ℕ) : ℝ) + ((15 * lamN n : ℕ) : ℝ) + 1 ≤
          ((univ.filter fun τ => σ τ ∈ A τ).card : ℝ) := by exact_mod_cast (by omega :
            41 * Mtot s rs H x / (40 * Δ) + 15 * lamN n + 1 ≤
              (univ.filter fun τ => σ τ ∈ A τ).card)
      have h2 := nat_div_add_one_gt (41 * Mtot s rs H x) (40 * Δ) (by omega)
      have h3 : 41 / 40 * ((∑ τ, ((A τ).card : ℝ)) / Δ) ≤
          ((41 * Mtot s rs H x : ℕ) : ℝ) / ((40 * Δ : ℕ) : ℝ) := by
        push_cast
        rw [show (41 : ℝ) / 40 * ((∑ τ, ((A τ).card : ℝ)) / Δ) =
          41 * (∑ τ, ((A τ).card : ℝ)) / (40 * Δ) by field_simp]
        rw [div_le_div_iff_of_pos_right (by positivity)]
        linarith
      linarith
  have h2 : (2 : ℝ) ^ lamN n ≤ (21 / 20) ^ (15 * lamN n) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hfin : ((badB s rs n H x τl).card : ℝ) * 2 ^ lamN n ≤ Δ.factorial :=
    (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)).trans
      ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card hsub)) (by positivity)).trans
        hch)
  exact_mod_cast hfin

/-- The window properties (A) and (B), for times as natural numbers. -/
structure GoodOrder (n : ℕ) (σ : Equiv.Perm (Fin Δ)) : Prop where
  A : ∀ H d, d < k → ∀ τ0, τ0 + win s rs H d < Δ → s ≤
    ∑ τ ∈ Ioc τ0 (τ0 + win s rs H d),
      (rnd rs σ τ).countP (fun p => decide (p.1 = H ∧ d ≤ p.2.1))
  B : ∀ H x τl, τl < Δ →
    ∑ d ∈ range k, ∑ τ ∈ Icc (τl - wsum s rs H d) τl,
      (rnd rs σ τ).countP (fun p => decide (p = (H, d, x))) ≤ Nbx s rs n H x

theorem goodOrder_of_not_bad (n : ℕ) (σ : Equiv.Perm (Fin Δ))
    (hA : ∀ H (d : Fin k) τ0, σ ∉ badA s rs H d τ0)
    (hB : ∀ H x τl, σ ∉ badB s rs n H x τl) : GoodOrder s rs n σ := by
  constructor
  · intro H d hd τ0 hfit
    rw [sum_rnd rs σ _ (fun l => l.countP (fun p => decide (p.1 = H ∧ d ≤ p.2.1))) rfl]
    have := hA H ⟨d, hd⟩ ⟨τ0, by omega⟩
    simp only [badA, mem_filter, mem_univ, true_and, not_and, not_lt] at this
    exact this hfit
  · intro H x τl hτl
    have e : ∀ d, ∑ τ ∈ Icc (τl - wsum s rs H d) τl,
        (rnd rs σ τ).countP (fun p => decide (p = (H, d, x))) =
          ∑ τ ∈ univ.filter (fun τ : Fin Δ => τ.val ∈ Icc (τl - wsum s rs H d) τl),
            acnt rs H d x (σ τ) := fun d =>
      sum_rnd rs σ _ (fun l => l.countP (fun p => decide (p = (H, d, x)))) rfl
    simp_rw [e]
    have := hB H x ⟨τl, hτl⟩
    simp only [badB, mem_filter, mem_univ, true_and, not_lt] at this
    exact this

/-- Union bound: some order avoids every bad event. -/
theorem exists_goodOrder (n : ℕ) (hk : 0 < k) {la : ℕ} (hlam : 76 * k * la ≤ 5 * s)
    (hcA : 2 * Fintype.card (RowH k × Fin k × Fin Δ) ≤ 2 ^ la)
    (hcB : 2 * Fintype.card (RowH k × Sq k × Fin Δ) < 2 ^ lamN n) :
    ∃ σ, GoodOrder s rs n σ := by
  set BadA : Finset (Equiv.Perm (Fin Δ)) :=
    (univ : Finset (RowH k × Fin k × Fin Δ)).biUnion (fun e => badA s rs e.1 e.2.1 e.2.2)
  set BadB : Finset (Equiv.Perm (Fin Δ)) :=
    (univ : Finset (RowH k × Sq k × Fin Δ)).biUnion (fun e => badB s rs n e.1 e.2.1 e.2.2)
  have hf : 0 < Δ.factorial := Nat.factorial_pos Δ
  have hA : 2 * BadA.card ≤ Δ.factorial := by
    have h1 : BadA.card * 2 ^ la ≤ Fintype.card (RowH k × Fin k × Fin Δ) * Δ.factorial := by
      calc BadA.card * 2 ^ la
          ≤ (∑ e : RowH k × Fin k × Fin Δ, (badA s rs e.1 e.2.1 e.2.2).card) * 2 ^ la :=
            Nat.mul_le_mul_right _ card_biUnion_le
        _ = ∑ e : RowH k × Fin k × Fin Δ, (badA s rs e.1 e.2.1 e.2.2).card * 2 ^ la := sum_mul ..
        _ ≤ ∑ _e : RowH k × Fin k × Fin Δ, Δ.factorial :=
            sum_le_sum fun e _ => card_badA s rs hk hlam _ _ _
        _ = _ := by simp
    have h2 := Nat.mul_le_mul_right Δ.factorial hcA
    have h3 : 2 * BadA.card * 2 ^ la ≤ 2 ^ la * Δ.factorial := by nlinarith
    rw [mul_comm (2 ^ la)] at h3
    exact Nat.le_of_mul_le_mul_right h3 (by positivity)
  have hB : 2 * BadB.card < Δ.factorial := by
    have h1 : BadB.card * 2 ^ lamN n ≤ Fintype.card (RowH k × Sq k × Fin Δ) * Δ.factorial := by
      calc BadB.card * 2 ^ lamN n
          ≤ (∑ e : RowH k × Sq k × Fin Δ, (badB s rs n e.1 e.2.1 e.2.2).card) * 2 ^ lamN n :=
            Nat.mul_le_mul_right _ card_biUnion_le
        _ = ∑ e : RowH k × Sq k × Fin Δ, (badB s rs n e.1 e.2.1 e.2.2).card * 2 ^ lamN n :=
            sum_mul ..
        _ ≤ ∑ _e : RowH k × Sq k × Fin Δ, Δ.factorial :=
            sum_le_sum fun e _ => card_badB s rs n _ _ _
        _ = _ := by simp
    have h2 := Nat.mul_lt_mul_of_pos_right hcB hf
    have h3 : 2 * BadB.card * 2 ^ lamN n < 2 ^ lamN n * Δ.factorial := by nlinarith
    rw [mul_comm (2 ^ lamN n)] at h3
    exact Nat.lt_of_mul_lt_mul_right h3
  have hlt : (BadA ∪ BadB).card < (univ : Finset (Equiv.Perm (Fin Δ))).card := by
    rw [card_univ, Fintype.card_perm, Fintype.card_fin]
    have := card_union_le BadA BadB
    omega
  obtain ⟨σ, -, hσ⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨σ, goodOrder_of_not_bad s rs n σ ?_ ?_⟩
  · intro H d τ0 h
    exact hσ (mem_union_left _ (mem_biUnion.mpr ⟨(H, d, τ0), mem_univ _, h⟩))
  · intro H x τl h
    exact hσ (mem_union_right _ (mem_biUnion.mpr ⟨(H, x, τl), mem_univ _, h⟩))

end SlidingPuzzle.Hub
