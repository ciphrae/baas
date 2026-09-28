import SlidingPuzzle.Hub.ChernoffMaclaurin

/-! # Chernoff bounds for a uniformly random permutation restricted to a window

For a fixed set `T` of positions, `σ ↦ T.image σ` hits every `|T|`-subset equally
often, so sums over permutations of functions of `T.image σ` are sums over subsets
(`sum_perm_image`). With Maclaurin's inequality this bounds the moment
`Σ_σ Π_{τ∈T} y (σ τ)` by `n! · mean(y)^|T|`. With Markov's inequality
(`card_filter_mul_le_sum`) this gives the tails in `Hub/ChernoffChain.lean`,
stated as counts of permutations. -/
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

end SlidingPuzzle.Hub
