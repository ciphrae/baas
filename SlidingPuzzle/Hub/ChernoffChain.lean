import SlidingPuzzle.Hub.ChernoffPerm

/-! # An upper tail for position-dependent nested sets

Let every position `τ` of a random permutation carry a set `A τ`, the sets
forming a chain under inclusion. The number `Y(σ)` of positions with
`σ τ ∈ A τ` has the moment bound of independent indicators:
`Σ_σ Π_τ (1 + c·[σ τ ∈ A τ]) ≤ n! · Π_τ (1 + c|A τ|/n)` (`sum_perm_prod_chain_le`).
The count behind it (`card_goodSet_mul_le`) removes the position with the
largest set: every other constrained position already takes a value inside it,
and swapping positions outside the constraints shows that all remaining values
are equally likely (`card_goodSet_insert_mul`). Markov's inequality then gives
`Y ≤ (41/40) μ + λ` except on a `(21/20)^(-λ)` fraction (`card_upper_tail_chain`).

This bounds the tiles of one class present in a row half with a single slack
term, although tiles from different distances stay for different times. -/
namespace SlidingPuzzle.Hub

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
/-- In a chain, some set of `S` contains all the others. -/
theorem exists_max_chain (S : Finset α) (hS : S.Nonempty) (A : α → Finset α)
    (hA : ∀ τ τ', A τ ⊆ A τ' ∨ A τ' ⊆ A τ) :
    ∃ τ ∈ S, ∀ τ' ∈ S, A τ' ⊆ A τ := by
  obtain ⟨τ, hτ, hmax⟩ := S.exists_max_image (fun τ => (A τ).card) hS
  refine ⟨τ, hτ, fun τ' hτ' => ?_⟩
  rcases hA τ' τ with h | h
  · exact h
  · rw [Finset.eq_of_subset_of_card_le h (hmax τ' hτ')]

/-- Permutations meeting the constraints `σ τ ∈ A τ` for `τ ∈ S`. -/
def goodSet (S : Finset α) (A : α → Finset α) : Finset (Equiv.Perm α) :=
  univ.filter fun σ => ∀ τ ∈ S, σ τ ∈ A τ

theorem goodSet_empty (A : α → Finset α) : goodSet ∅ A = univ := by
  simp [goodSet]

theorem goodSet_insert (S : Finset α) (A : α → Finset α) (t : α) :
    goodSet (insert t S) A = (goodSet S A).filter fun σ => σ t ∈ A t := by
  ext σ
  simp only [goodSet, mem_filter, mem_univ, true_and, forall_mem_insert]
  tauto

/-- Swapping two unconstrained positions. -/
theorem card_goodSet_swap (S : Finset α) (A : α → Finset α) (B : Finset α) {u v : α}
    (hu : u ∉ S) (hv : v ∉ S) :
    ((goodSet S A).filter fun σ => σ u ∈ B).card = ((goodSet S A).filter fun σ => σ v ∈ B).card := by
  have hfix : ∀ σ : Equiv.Perm α, ∀ τ ∈ S, (σ * Equiv.swap u v) τ = σ τ := by
    intro σ τ hτ
    rw [Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.swap_apply_of_ne_of_ne (ne_of_mem_of_not_mem hτ hu) (ne_of_mem_of_not_mem hτ hv)]
  refine Finset.card_bij' (fun σ _ => σ * Equiv.swap u v) (fun σ _ => σ * Equiv.swap u v)
    ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [goodSet, mem_filter, mem_univ, true_and] at hσ ⊢
    refine ⟨fun τ hτ => by rw [hfix σ τ hτ]; exact hσ.1 τ hτ, ?_⟩
    rw [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_right]; exact hσ.2
  · intro σ hσ
    simp only [goodSet, mem_filter, mem_univ, true_and] at hσ ⊢
    refine ⟨fun τ hτ => by rw [hfix σ τ hτ]; exact hσ.1 τ hτ, ?_⟩
    rw [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left]; exact hσ.2
  · intro σ _; simp [mul_assoc]
  · intro σ _; simp [mul_assoc]

/-- The values of `σ` in a set `B`. -/
theorem card_filter_perm_mem (σ : Equiv.Perm α) (B : Finset α) :
    (univ.filter fun u => σ u ∈ B).card = B.card := by
  have : (univ.filter fun u => σ u ∈ B) = B.image σ.symm := by
    ext u
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro h; exact ⟨σ u, h, by simp⟩
    · rintro ⟨a, ha, rfl⟩; simpa using ha
  rw [this, card_image_of_injective _ σ.symm.injective]

/-- **Adding the largest set.** If the sets of `S` lie in `A t`, a good
permutation for `S` sends `t` into `A t` with frequency `(|A t| - |S|)/(n - |S|)`. -/
theorem card_goodSet_insert_mul (S : Finset α) (A : α → Finset α) {t : α} (ht : t ∉ S)
    (hsub : ∀ τ ∈ S, A τ ⊆ A t) :
    (Fintype.card α - S.card) * (goodSet (insert t S) A).card =
      (goodSet S A).card * ((A t).card - S.card) := by
  set G := goodSet S A
  have htc : t ∈ Sᶜ := mem_compl.mpr ht
  -- every unconstrained position is equally likely to take a value in `A t`
  have h1 : ∑ u ∈ Sᶜ, ((G.filter fun σ => σ u ∈ A t).card) =
      (Fintype.card α - S.card) * (goodSet (insert t S) A).card := by
    rw [goodSet_insert, ← card_compl, ← smul_eq_mul, ← sum_const]
    exact sum_congr rfl fun u hu => card_goodSet_swap S A (A t) (mem_compl.mp hu) ht
  -- for a good permutation, exactly `|A t| - |S|` of them do
  have h2 : ∀ σ ∈ G, (Sᶜ.filter fun u => σ u ∈ A t).card = (A t).card - S.card := by
    intro σ hσ
    have hgood : ∀ τ ∈ S, σ τ ∈ A t := fun τ hτ =>
      hsub τ hτ ((mem_filter.mp hσ).2 τ hτ)
    have hsplit := card_filter_add_card_filter_not
      (s := univ.filter fun u => σ u ∈ A t) (p := fun u => u ∈ S)
    rw [card_filter_perm_mem, filter_filter, filter_filter] at hsplit
    have e1 : (univ.filter fun u => σ u ∈ A t ∧ u ∈ S) = S := by
      ext u; simp only [mem_filter, mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨hgood u h, h⟩⟩
    have e2 : (univ.filter fun u => σ u ∈ A t ∧ u ∉ S) = Sᶜ.filter fun u => σ u ∈ A t := by
      ext u; simp only [mem_filter, mem_univ, true_and, mem_compl]; tauto
    rw [e1, e2] at hsplit
    omega
  have h3 : ∑ u ∈ Sᶜ, ((G.filter fun σ => σ u ∈ A t).card) =
      ∑ σ ∈ G, (Sᶜ.filter fun u => σ u ∈ A t).card := by
    simp only [card_filter]
    exact sum_comm
  rw [← h1, h3, sum_congr rfl h2, sum_const, smul_eq_mul]

/-- **Nested constraints are no likelier than independent ones**:
`#{σ : σ τ ∈ A τ for τ ∈ S} · n^|S| ≤ n! · Π_{τ ∈ S} |A τ|`. -/
theorem card_goodSet_mul_le (A : α → Finset α) (hA : ∀ τ τ', A τ ⊆ A τ' ∨ A τ' ⊆ A τ) :
    ∀ p, ∀ S : Finset α, S.card = p →
      (goodSet S A).card * Fintype.card α ^ p ≤ (Fintype.card α).factorial * ∏ τ ∈ S, (A τ).card := by
  intro p
  induction p with
  | zero =>
    intro S hS
    rw [card_eq_zero.mp hS, goodSet_empty, card_univ, Fintype.card_perm]
    simp
  | succ p ih =>
    intro S hS
    obtain ⟨t, ht, hmax⟩ := exists_max_chain S (card_pos.mp (by omega)) A hA
    set S' := S.erase t with hS'def
    have htS' : t ∉ S' := notMem_erase t S
    have hS' : S'.card = p := by rw [card_erase_of_mem ht]; omega
    have hins : insert t S' = S := insert_erase ht
    have key := card_goodSet_insert_mul S' A htS' (fun τ hτ => hmax τ (mem_of_mem_erase hτ))
    rw [hins, hS'] at key
    have ih' := ih S' hS'
    rw [← hins, prod_insert htS', hins]
    set N := Fintype.card α
    set g := (goodSet S A).card
    set g' := (goodSet S' A).card
    set a := (A t).card
    set P := ∏ τ ∈ S', (A τ).card
    have hpN : p < N := by
      have := card_le_univ S
      omega
    have haN : a ≤ N := card_le_univ _
    -- `g N ≤ g' a`
    have hsub : (a - p) * N ≤ a * (N - p) := by
      rw [Nat.sub_mul, Nat.mul_sub]
      exact Nat.sub_le_sub_left (by rw [mul_comm p N]; exact Nat.mul_le_mul_right p haN) _
    have hgN : g * N ≤ g' * a := by
      have h1 : (N - p) * (g * N) ≤ (N - p) * (g' * a) := by
        calc (N - p) * (g * N) = ((N - p) * g) * N := by ring
          _ = g' * ((a - p) * N) := by rw [key]; ring
          _ ≤ g' * (a * (N - p)) := Nat.mul_le_mul_left _ hsub
          _ = (N - p) * (g' * a) := by ring
      exact Nat.le_of_mul_le_mul_left h1 (by omega)
    calc g * N ^ (p + 1) = (g * N) * N ^ p := by ring
      _ ≤ (g' * a) * N ^ p := Nat.mul_le_mul_right _ hgN
      _ = a * (g' * N ^ p) := by ring
      _ ≤ a * (N.factorial * P) := Nat.mul_le_mul_left _ ih'
      _ = N.factorial * (a * P) := by ring

/-- **Moment bound for nested sets.** -/
theorem sum_perm_prod_chain_le (T : Finset α) (A : α → Finset α)
    (hA : ∀ τ τ', A τ ⊆ A τ' ∨ A τ' ⊆ A τ) {c : ℝ} (hc : 0 ≤ c) (hn : 0 < Fintype.card α) :
    ∑ σ : Equiv.Perm α, ∏ τ ∈ T, (1 + c * if σ τ ∈ A τ then 1 else 0) ≤
      (Fintype.card α).factorial * ∏ τ ∈ T, (1 + c * (A τ).card / Fintype.card α) := by
  set N := Fintype.card α
  have hNR : (0 : ℝ) < N := by exact_mod_cast hn
  simp_rw [prod_one_add]
  rw [sum_comm, mul_sum]
  refine sum_le_sum fun S _ => ?_
  have e : ∀ σ : Equiv.Perm α, ∏ τ ∈ S, (c * if σ τ ∈ A τ then (1 : ℝ) else 0) =
      c ^ S.card * if σ ∈ goodSet S A then 1 else 0 := by
    intro σ
    rw [prod_mul_distrib, prod_const, prod_boole]
    simp [goodSet]
  simp_rw [e]
  rw [← mul_sum, sum_boole, filter_mem_eq_inter, univ_inter]
  have hcount := card_goodSet_mul_le A hA S.card S rfl
  have hcountR : ((goodSet S A).card : ℝ) * (N : ℝ) ^ S.card ≤
      (N.factorial : ℝ) * ∏ τ ∈ S, ((A τ).card : ℝ) := by exact_mod_cast hcount
  have hpow : (0 : ℝ) < (N : ℝ) ^ S.card := pow_pos hNR _
  have e2 : ∏ τ ∈ S, (c * (A τ).card / N) = c ^ S.card * (∏ τ ∈ S, ((A τ).card : ℝ)) /
      (N : ℝ) ^ S.card := by
    rw [prod_div_distrib, prod_mul_distrib, prod_const, prod_const]
  have hc' : 0 ≤ c ^ S.card := pow_nonneg hc _
  rw [e2, mul_div_assoc', le_div_iff₀ hpow]
  calc c ^ S.card * ((goodSet S A).card : ℝ) * (N : ℝ) ^ S.card =
        c ^ S.card * (((goodSet S A).card : ℝ) * (N : ℝ) ^ S.card) := by ring
    _ ≤ c ^ S.card * ((N.factorial : ℝ) * ∏ τ ∈ S, ((A τ).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hcountR hc'
    _ = _ := by ring

/-- `log (21/20) ≥ 2/41`, from `(21/20)^41 ≥ e²`. -/
theorem two_div_fortyone_le_log : (2 / 41 : ℝ) ≤ Real.log (21 / 20) := by
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have h2 : Real.exp 2 ≤ (21 / 20 : ℝ) ^ 41 := by
    have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    nlinarith
  have := Real.log_le_log (Real.exp_pos 2) h2
  rw [Real.log_exp, Real.log_pow] at this
  push_cast at this
  linarith

/-- **Upper tail for nested sets**: few permutations put at least
`(41/40) μ + λ` positions `τ ∈ T` into their sets, `μ = Σ_τ |A τ| / n`. -/
theorem card_upper_tail_chain (T : Finset α) (A : α → Finset α)
    (hA : ∀ τ τ', A τ ⊆ A τ' ∨ A τ' ⊆ A τ) (lam : ℕ) (hn : 0 < Fintype.card α) :
    ((univ.filter fun σ : Equiv.Perm α =>
        41 / 40 * ((∑ τ ∈ T, ((A τ).card : ℝ)) / Fintype.card α) + lam ≤
          ((T.filter fun τ => σ τ ∈ A τ).card : ℝ)).card : ℝ) * (21 / 20) ^ lam ≤
      (Fintype.card α).factorial := by
  set N := Fintype.card α
  set μ : ℝ := (∑ τ ∈ T, ((A τ).card : ℝ)) / N with hμ
  have hNR : (0 : ℝ) < N := by exact_mod_cast hn
  have hμ0 : 0 ≤ μ := div_nonneg (sum_nonneg fun τ _ => Nat.cast_nonneg _) hNR.le
  have hf0 : ∀ σ : Equiv.Perm α,
      0 ≤ ∏ τ ∈ T, (1 + 1 / 20 * if σ τ ∈ A τ then (1 : ℝ) else 0) :=
    fun σ => prod_nonneg fun τ _ => by split_ifs <;> norm_num
  have hfpow : ∀ σ : Equiv.Perm α, ∏ τ ∈ T, (1 + 1 / 20 * if σ τ ∈ A τ then (1 : ℝ) else 0) =
      (21 / 20 : ℝ) ^ (T.filter fun τ => σ τ ∈ A τ).card := by
    intro σ
    rw [← prod_const, prod_filter]
    refine prod_congr rfl fun τ _ => ?_
    split_ifs <;> norm_num
  have hmom := sum_perm_prod_chain_le T A hA (c := 1 / 20) (by norm_num) hn
  have hexp : ∏ τ ∈ T, (1 + 1 / 20 * ((A τ).card : ℝ) / N) ≤ Real.exp (μ / 20) := by
    calc ∏ τ ∈ T, (1 + 1 / 20 * ((A τ).card : ℝ) / N)
        ≤ ∏ τ ∈ T, Real.exp (1 / 20 * ((A τ).card : ℝ) / N) := by
          apply prod_le_prod (fun τ _ => by positivity)
          intro τ _
          have := Real.add_one_le_exp (1 / 20 * ((A τ).card : ℝ) / N)
          linarith
      _ = Real.exp (μ / 20) := by
          rw [← Real.exp_sum]; congr 1
          rw [hμ, ← sum_div, ← mul_sum]; ring
  have hlog := two_div_fortyone_le_log
  have hl0 : 0 < Real.log (21 / 20) := by linarith
  have hpow : ∀ m : ℕ, (21 / 20 : ℝ) ^ m = Real.exp (m * Real.log (21 / 20)) := by
    intro m; rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hmark := card_filter_mul_le_sum
    (fun σ : Equiv.Perm α => ∏ τ ∈ T, (1 + 1 / 20 * if σ τ ∈ A τ then (1 : ℝ) else 0)) hf0 (Real.exp (μ / 20) * (21 / 20) ^ lam)
    (fun σ => 41 / 40 * μ + lam ≤ ((T.filter fun τ => σ τ ∈ A τ).card : ℝ)) (by
      intro σ hσ
      rw [hfpow, hpow, hpow, ← Real.exp_add, Real.exp_le_exp]
      nlinarith [mul_le_mul_of_nonneg_right hσ hl0.le, mul_le_mul_of_nonneg_left hlog hμ0])
  have hfin := hmark.trans (hmom.trans (mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg _)))
  rw [mul_comm (Real.exp (μ / 20)), ← mul_assoc] at hfin
  exact le_of_mul_le_mul_right hfin (Real.exp_pos _)

/-! ## The lower tail with the exact exponent -/

/-- `log (4/3) ≤ 0.28769`, from the series of `log (1 - 1/4)`. -/
theorem log_four_thirds_le : Real.log (4 / 3) ≤ 28769 / 100000 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 1 / 4) (by norm_num) 8
  rw [abs_le] at h
  have e : Real.log (4 / 3) = -Real.log (1 - 1 / 4) := by
    rw [show (1 : ℝ) - 1 / 4 = (4 / 3)⁻¹ by norm_num, Real.log_inv, neg_neg]
  rw [e]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith [h.1]

/-- `(3/4)^v ≤ 1 - v/4` in exponential form: `exp(-0.28769 v) ≤ 1 - v/4` on `[0, 1]`. -/
theorem exp_neg_le_one_sub_quarter {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) :
    Real.exp (-(28769 / 100000 * v)) ≤ 1 - v / 4 := by
  have hb := rpow_one_add_le_one_add_mul_self (s := -1 / 4) (by norm_num) h0 h1
  rw [show (1 : ℝ) + -1 / 4 = 3 / 4 by norm_num, Real.rpow_def_of_pos (by norm_num)] at hb
  have hl : -(28769 / 100000 : ℝ) ≤ Real.log (3 / 4) := by
    have := log_four_thirds_le
    rw [show (3 : ℝ) / 4 = (4 / 3)⁻¹ by norm_num, Real.log_inv]
    linarith
  calc Real.exp (-(28769 / 100000 * v)) ≤ Real.exp (Real.log (3 / 4) * v) := by
        apply Real.exp_le_exp.mpr; nlinarith
    _ ≤ 1 + v * (-1 / 4) := hb
    _ = 1 - v / 4 := by ring

/-- **Lower tail** (terms in `[0, K]`): few permutations make the window sum at most
`(3/4) μ`; the exponent `3423/100000 < 1/4 - (3/4) log (4/3)` is nearly optimal
for the threshold `3/4`. -/
theorem card_lower_tail_log (T : Finset α) (g : α → ℝ) {K : ℝ} (hK : 0 < K)
    (hg0 : ∀ i, 0 ≤ g i) (hgK : ∀ i, g i ≤ K) (hn : 0 < Fintype.card α) :
    ((univ.filter fun σ : Equiv.Perm α =>
        ∑ τ ∈ T, g (σ τ) ≤ 3 / 4 * (T.card * (∑ i, g i) / Fintype.card α)).card : ℝ) ≤
      (Fintype.card α).factorial *
        Real.exp (-(3423 * (T.card * (∑ i, g i) / Fintype.card α)) / (100000 * K)) := by
  set n := Fintype.card α
  set μ : ℝ := T.card * (∑ i, g i) / n with hμ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set y : α → ℝ := fun i => 1 - g i / (4 * K) with hy
  have hy0 : ∀ i, 0 ≤ y i := by
    intro i; simp only [hy]
    have : g i / (4 * K) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]; linarith [hgK i]
    linarith
  have hmom := sum_perm_prod_le T y hy0
  have hmean : (∑ i, y i) / n = 1 - (∑ i, g i) / (4 * K * n) := by
    simp only [hy, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, ← sum_div]
    field_simp; simp only [n]; ring
  have hmean0 : 0 ≤ (∑ i, y i) / n := div_nonneg (sum_nonneg fun i _ => hy0 i) hnR.le
  have hexp : ((∑ i, y i) / n) ^ T.card ≤ Real.exp (-(μ / (4 * K))) := by
    calc ((∑ i, y i) / n) ^ T.card ≤ (Real.exp (-((∑ i, g i) / (4 * K * n)))) ^ T.card := by
          apply pow_le_pow_left₀ hmean0
          rw [hmean]; linarith [Real.add_one_le_exp (-((∑ i, g i) / (4 * K * n)))]
      _ = Real.exp (-(μ / (4 * K))) := by
          rw [← Real.exp_nat_mul]; congr 1; rw [hμ]; field_simp
  have hmark := card_filter_mul_le_sum (fun σ : Equiv.Perm α => ∏ τ ∈ T, y (σ τ))
    (fun σ => prod_nonneg fun τ _ => hy0 _) (Real.exp (-(28769 * (3 * μ) / (400000 * K))))
    (fun σ => ∑ τ ∈ T, g (σ τ) ≤ 3 / 4 * μ) (by
      intro σ hσ
      calc Real.exp (-(28769 * (3 * μ) / (400000 * K))) ≤
            Real.exp (-(28769 / 100000 * ∑ τ ∈ T, g (σ τ)) / K) := by
            apply Real.exp_le_exp.mpr
            rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
        _ = ∏ τ ∈ T, Real.exp (-(28769 / 100000 * (g (σ τ) / K))) := by
            rw [← Real.exp_sum]; congr 1
            rw [neg_div, mul_sum, sum_div, ← sum_neg_distrib]
            refine sum_congr rfl fun τ _ => ?_
            field_simp
        _ ≤ ∏ τ ∈ T, y (σ τ) := by
            apply prod_le_prod (fun τ _ => (Real.exp_pos _).le)
            intro τ _
            have h := exp_neg_le_one_sub_quarter (div_nonneg (hg0 (σ τ)) hK.le)
              (by rw [div_le_iff₀ hK]; linarith [hgK (σ τ)])
            simp only [hy]
            rw [show g (σ τ) / (4 * K) = g (σ τ) / K / 4 by field_simp]
            exact h)
  have hfin : ((univ.filter fun σ : Equiv.Perm α => ∑ τ ∈ T, g (σ τ) ≤ 3 / 4 * μ).card : ℝ) *
      Real.exp (-(28769 * (3 * μ) / (400000 * K))) ≤ n.factorial * Real.exp (-(μ / (4 * K))) :=
    hmark.trans (hmom.trans (mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg _)))
  have hpos := Real.exp_pos (-(28769 * (3 * μ) / (400000 * K)))
  have hμ0 : 0 ≤ μ := by
    have : 0 ≤ ∑ i, g i := sum_nonneg fun i _ => hg0 i
    positivity
  have hsplit : Real.exp (-(μ / (4 * K))) ≤
      Real.exp (-(3423 * μ) / (100000 * K)) * Real.exp (-(28769 * (3 * μ) / (400000 * K))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : 0 ≤ μ / K := div_nonneg hμ0 hK.le
    have e1 : -(μ / (4 * K)) = -(1 / 4) * (μ / K) := by field_simp
    have e2 : -(3423 * μ) / (100000 * K) + -(28769 * (3 * μ) / (400000 * K)) =
        -(3423 / 100000 + 86307 / 400000) * (μ / K) := by field_simp; ring
    rw [e1, e2]
    nlinarith
  have hfin' : ((univ.filter fun σ : Equiv.Perm α => ∑ τ ∈ T, g (σ τ) ≤ 3 / 4 * μ).card : ℝ) *
      Real.exp (-(28769 * (3 * μ) / (400000 * K))) ≤
      (n.factorial * Real.exp (-(3423 * μ) / (100000 * K))) *
        Real.exp (-(28769 * (3 * μ) / (400000 * K))) := by
    rw [mul_assoc]
    exact hfin.trans (mul_le_mul_of_nonneg_left hsplit (Nat.cast_nonneg _))
  exact le_of_mul_le_mul_right hfin' hpos

end SlidingPuzzle.Hub
