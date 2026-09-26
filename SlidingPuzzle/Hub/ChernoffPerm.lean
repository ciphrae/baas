import SlidingPuzzle.Hub.ChernoffMaclaurin

/-! # Chernoff bounds for a uniformly random permutation restricted to a window

For a fixed set `T` of positions, `σ ↦ T.image σ` hits every `|T|`-subset equally
often, so sums over permutations of functions of `T.image σ` are sums over subsets
(`sum_perm_image`). With Maclaurin's inequality this bounds the moment
`Σ_σ Π_{τ∈T} y (σ τ)` by `n! · mean(y)^|T|`, and Markov's inequality gives the
two tails used for the in-flight bound, stated as counts of permutations. -/
namespace SlidingPuzzle.Hub

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Two subsets of equal size are related by a permutation. -/
theorem exists_perm_image_eq {T W : Finset α} (h : W.card = T.card) :
    ∃ π : Equiv.Perm α, T.image π = W := by
  have hc : Fintype.card {x // x ∈ T} = Fintype.card {x // x ∈ W} := by simp [h]
  let e := Fintype.equivOfCardEq hc
  refine ⟨e.extendSubtype, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [Equiv.extendSubtype_apply_of_mem e x hx]
    exact (e ⟨x, hx⟩).2
  · rw [Finset.card_image_of_injective _ (Equiv.injective _), h]

/-- All fibres of `σ ↦ T.image σ` over `|T|`-subsets have the same size. -/
theorem card_fiber_perm_image (T W : Finset α) (h : W.card = T.card) :
    (univ.filter fun σ : Equiv.Perm α => T.image σ = W).card =
      (univ.filter fun σ : Equiv.Perm α => T.image σ = T).card := by
  obtain ⟨π, hπ⟩ := exists_perm_image_eq h
  symm
  refine Finset.card_bij' (fun σ _ => π * σ) (fun σ _ => π⁻¹ * σ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    rw [Equiv.Perm.coe_mul, ← Finset.image_image, hσ, hπ]
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    rw [Equiv.Perm.coe_mul, ← Finset.image_image, hσ, ← hπ, Finset.image_image]
    simp
  · intro σ _; simp
  · intro σ _; simp

/-- Sums over permutations of a function of `T.image σ` are sums over subsets. -/
theorem sum_perm_image (T : Finset α) (F : Finset α → ℝ) :
    (∑ σ : Equiv.Perm α, F (T.image σ)) * ((Fintype.card α).choose T.card) =
      (Fintype.card α).factorial * ∑ W ∈ (univ : Finset α).powersetCard T.card, F W := by
  set c := (univ.filter fun σ : Equiv.Perm α => T.image σ = T).card
  have hmaps : ∀ σ ∈ (univ : Finset (Equiv.Perm α)),
      T.image σ ∈ (univ : Finset α).powersetCard T.card := by
    intro σ _
    simp [Finset.card_image_of_injective _ (Equiv.injective σ)]
  have hsum : ∀ G : Finset α → ℝ, ∑ σ : Equiv.Perm α, G (T.image σ) =
      c * ∑ W ∈ (univ : Finset α).powersetCard T.card, G W := by
    intro G
    rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
    refine Finset.sum_congr rfl fun W hW => ?_
    rw [Finset.sum_congr rfl (g := fun _ => G W) (fun σ hσ => by rw [(mem_filter.mp hσ).2]),
      Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hWc : W.card = T.card := (mem_powersetCard.mp hW).2
    exact_mod_cast card_fiber_perm_image T W hWc
  have h1 := hsum (fun _ => 1)
  simp only [sum_const, card_univ, Fintype.card_perm, nsmul_eq_mul, mul_one,
    card_powersetCard] at h1
  rw [hsum F, h1]
  ring

/-- Moment bound: `Σ_σ Π_{τ∈T} y (σ τ) ≤ n! · mean(y)^|T|`. -/
theorem sum_perm_prod_le (T : Finset α) (y : α → ℝ) (hy : ∀ i, 0 ≤ y i) :
    ∑ σ : Equiv.Perm α, ∏ τ ∈ T, y (σ τ) ≤
      (Fintype.card α).factorial * ((∑ i, y i) / Fintype.card α) ^ T.card := by
  have hprod : ∀ σ : Equiv.Perm α, ∏ τ ∈ T, y (σ τ) = ∏ i ∈ T.image σ, y i := by
    intro σ
    rw [Finset.prod_image (fun a _ b _ h => σ.injective h)]
  simp_rw [hprod]
  have h := sum_perm_image T (fun W => ∏ i ∈ W, y i)
  have hM := maclaurin_finset (univ : Finset α) y (fun i _ => hy i) T.card
  rw [card_univ] at hM
  have hC : (0 : ℝ) < ((Fintype.card α).choose T.card) := by
    have : T.card ≤ Fintype.card α := Finset.card_le_univ T
    exact_mod_cast Nat.choose_pos this
  have hfac : (0 : ℝ) ≤ (Fintype.card α).factorial := Nat.cast_nonneg _
  refine le_of_mul_le_mul_right ?_ hC
  rw [h]
  calc _ ≤ ((Fintype.card α).factorial : ℝ) * (((Fintype.card α).choose T.card) *
        ((∑ i, y i) / Fintype.card α) ^ T.card) := mul_le_mul_of_nonneg_left hM hfac
    _ = _ := by ring

/-- Markov's inequality for a sum over permutations. -/
theorem card_filter_mul_le_sum (f : Equiv.Perm α → ℝ) (hf : ∀ σ, 0 ≤ f σ) (θ : ℝ)
    (P : Equiv.Perm α → Prop) [DecidablePred P] (hP : ∀ σ, P σ → θ ≤ f σ) :
    ((univ.filter P).card : ℝ) * θ ≤ ∑ σ, f σ := by
  calc ((univ.filter P).card : ℝ) * θ = ∑ σ ∈ univ.filter P, θ := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ σ ∈ univ.filter P, f σ := sum_le_sum fun σ hσ => hP σ (mem_filter.mp hσ).2
    _ ≤ ∑ σ, f σ := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun σ _ _ => hf σ

/-- `exp(-4v/3) ≤ 1 - v` for `v ∈ [0, 1/4]`. -/
theorem exp_neg_le_one_sub {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1 / 4) :
    Real.exp (-(4 / 3 * v)) ≤ 1 - v := by
  have he := Real.add_one_le_exp (4 / 3 * v)
  have hp : 0 < Real.exp (4 / 3 * v) := Real.exp_pos _
  have hprod : Real.exp (-(4 / 3 * v)) * Real.exp (4 / 3 * v) = 1 := by
    rw [← Real.exp_add]; simp
  have hq : 1 ≤ (1 - v) * Real.exp (4 / 3 * v) := by nlinarith
  nlinarith [Real.exp_pos (-(4 / 3 * v))]

/-- Lower tail (terms in `[0, K]`): few permutations make the window sum at most
half its mean `μ = |T| · Σ g / n`. -/
theorem card_lower_tail (T : Finset α) (g : α → ℝ) {K : ℝ} (hK : 0 < K)
    (hg0 : ∀ i, 0 ≤ g i) (hgK : ∀ i, g i ≤ K) (hn : 0 < Fintype.card α) :
    ((univ.filter fun σ : Equiv.Perm α =>
        ∑ τ ∈ T, g (σ τ) ≤ T.card * (∑ i, g i) / Fintype.card α / 2).card : ℝ) ≤
      (Fintype.card α).factorial *
        Real.exp (-(T.card * (∑ i, g i) / Fintype.card α) / (12 * K)) := by
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
    (fun σ => prod_nonneg fun τ _ => hy0 _) (Real.exp (-(μ / (6 * K))))
    (fun σ => ∑ τ ∈ T, g (σ τ) ≤ μ / 2) (by
      intro σ hσ
      calc Real.exp (-(μ / (6 * K))) ≤ Real.exp (-(∑ τ ∈ T, g (σ τ)) / (3 * K)) := by
            apply Real.exp_le_exp.mpr
            rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
        _ = ∏ τ ∈ T, Real.exp (-(4 / 3 * (g (σ τ) / (4 * K)))) := by
            rw [← Real.exp_sum]; congr 1
            rw [neg_div, sum_div, ← sum_neg_distrib]
            refine sum_congr rfl fun τ _ => ?_
            field_simp
        _ ≤ ∏ τ ∈ T, y (σ τ) := by
            apply prod_le_prod (fun τ _ => (Real.exp_pos _).le)
            intro τ _
            apply exp_neg_le_one_sub (div_nonneg (hg0 _) (by positivity))
            rw [div_le_iff₀ (by positivity)]; linarith [hgK (σ τ)])
  have hfin : ((univ.filter fun σ : Equiv.Perm α => ∑ τ ∈ T, g (σ τ) ≤ μ / 2).card : ℝ) *
      Real.exp (-(μ / (6 * K))) ≤ n.factorial * Real.exp (-(μ / (4 * K))) :=
    hmark.trans (hmom.trans (mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg _)))
  have hpos := Real.exp_pos (-(μ / (6 * K)))
  have hsplit : Real.exp (-(μ / (4 * K))) = Real.exp (-μ / (12 * K)) * Real.exp (-(μ / (6 * K))) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [hsplit, ← mul_assoc] at hfin
  exact le_of_mul_le_mul_right hfin hpos

/-- Upper tail (terms in `{0,1}`): few permutations make the window sum at least
`2μ + λ`, `μ = |T| · Σ a / n`. -/
theorem card_upper_tail (T : Finset α) (a : α → ℕ) (ha : ∀ i, a i ≤ 1) (lam : ℕ)
    (hn : 0 < Fintype.card α) :
    ((univ.filter fun σ : Equiv.Perm α =>
        2 * (T.card * (∑ i, (a i : ℝ)) / Fintype.card α) + lam ≤
          ((∑ τ ∈ T, a (σ τ) : ℕ) : ℝ)).card : ℝ) * 2 ^ lam ≤
      (Fintype.card α).factorial := by
  set n := Fintype.card α
  set μ : ℝ := T.card * (∑ i, (a i : ℝ)) / n with hμ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hμ0 : 0 ≤ μ := by positivity
  set y : α → ℝ := fun i => 1 + (a i : ℝ) with hy
  have hy0 : ∀ i, 0 ≤ y i := fun i => by positivity
  have hy2 : ∀ i, y i = 2 ^ a i := by
    intro i; simp only [hy]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (ha i) with h | h <;> rw [h] <;> norm_num
  have hmom := sum_perm_prod_le T y hy0
  have hmean0 : 0 ≤ (∑ i, y i) / n := div_nonneg (sum_nonneg fun i _ => hy0 i) hnR.le
  have hexp : ((∑ i, y i) / n) ^ T.card ≤ Real.exp μ := by
    have hmean : (∑ i, y i) / n = 1 + (∑ i, (a i : ℝ)) / n := by
      simp only [hy, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one]
      field_simp; rfl
    calc ((∑ i, y i) / n) ^ T.card ≤ (Real.exp ((∑ i, (a i : ℝ)) / n)) ^ T.card := by
          apply pow_le_pow_left₀ hmean0
          rw [hmean]; linarith [Real.add_one_le_exp ((∑ i, (a i : ℝ)) / n)]
      _ = Real.exp μ := by
          rw [← Real.exp_nat_mul]; congr 1; rw [hμ]; field_simp
  have hlog := Real.log_two_gt_d9
  have h2pow : ∀ m : ℕ, (2 : ℝ) ^ m = Real.exp (m * Real.log 2) := by
    intro m; rw [Real.exp_nat_mul, Real.exp_log two_pos]
  have hmark := card_filter_mul_le_sum (fun σ : Equiv.Perm α => ∏ τ ∈ T, y (σ τ))
    (fun σ => prod_nonneg fun τ _ => hy0 _) (Real.exp μ * 2 ^ lam)
    (fun σ => 2 * μ + lam ≤ ((∑ τ ∈ T, a (σ τ) : ℕ) : ℝ)) (by
      intro σ hσ
      rw [prod_congr rfl (fun τ _ => hy2 (σ τ)), prod_pow_eq_pow_sum, h2pow, h2pow,
        ← Real.exp_add, Real.exp_le_exp]
      nlinarith)
  have hfin := hmark.trans (hmom.trans (mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg _)))
  rw [mul_comm (Real.exp μ), ← mul_assoc] at hfin
  exact le_of_mul_le_mul_right hfin (Real.exp_pos μ)

end SlidingPuzzle.Hub
