import SlidingPuzzle.Hub.InFlightWindow

/-! # The row insertions of one round

`roundIns r` lists, for each source square `S` with a real edge leaving its
block column, the insertion `ent r S`. Counts over `roundIns r` are counts of
source squares (`countP_roundIns`). Since `r.perm` is a bijection, a round
inserts each `(H, d, x)` at most once, and at most `k` times into a half (the
sources lie in one band). -/
namespace SlidingPuzzle.Hub

open Finset

variable {k : ℕ}

/-- Sources of row insertions in a round. -/
noncomputable def srcs (r : Round k) : Finset (Sq k) :=
  univ.filter fun S => r.real S ∧ S.2 ≠ (r.perm S).2

/-- The insertion made by a source. -/
def ent (r : Round k) (S : Sq k) : RowH k × ℕ × Sq k :=
  (hop1Half S (S.1, (r.perm S).2), hop1Dist S (S.1, (r.perm S).2), r.perm S)

theorem roundIns_eq (r : Round k) : roundIns r = (srcs r).toList.map (ent r) := rfl

theorem countP_toList {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    s.toList.countP (fun a => decide (P a)) = (s.filter P).card := by
  rw [← Multiset.coe_countP, Finset.coe_toList, Multiset.countP_eq_card_filter]
  rfl

theorem countP_roundIns (r : Round k) (P : RowH k × ℕ × Sq k → Prop) [DecidablePred P] :
    (roundIns r).countP (fun p => decide (P p)) = ((srcs r).filter fun S => P (ent r S)).card := by
  rw [roundIns_eq, List.countP_map]
  exact countP_toList _ (fun S => P (ent r S))

theorem mem_roundIns {r : Round k} {p : RowH k × ℕ × Sq k} (hp : p ∈ roundIns r) :
    ∃ S ∈ srcs r, ent r S = p := by
  rw [roundIns_eq, List.mem_map] at hp
  obtain ⟨S, hS, rfl⟩ := hp
  exact ⟨S, Finset.mem_toList.mp hS, rfl⟩

theorem ent_dist_lt (r : Round k) (S : Sq k) : (ent r S).2.1 < k := by
  have h1 := S.2.isLt
  have h2 := (r.perm S).2.isLt
  simp only [ent, hop1Dist, Nat.dist]
  omega

theorem dist_lt_of_mem {r : Round k} {p : RowH k × ℕ × Sq k} (hp : p ∈ roundIns r) :
    p.2.1 < k := by
  obtain ⟨S, -, rfl⟩ := mem_roundIns hp
  exact ent_dist_lt r S

theorem class_col_of_mem {r : Round k} {p : RowH k × ℕ × Sq k} (hp : p ∈ roundIns r) :
    p.2.2.2 = p.1.2.1 := by
  obtain ⟨S, -, rfl⟩ := mem_roundIns hp
  rfl

/-- A round inserts a given `(H, d, x)` at most once. -/
theorem count_roundIns_le_one (r : Round k) (q : RowH k × ℕ × Sq k) :
    (roundIns r).countP (fun p => decide (p = q)) ≤ 1 := by
  rw [countP_roundIns]
  apply card_le_one.mpr
  intro a ha b hb
  simp only [mem_filter] at ha hb
  have : r.perm a = r.perm b := by
    have h1 := congrArg (fun p => p.2.2) ha.2
    have h2 := congrArg (fun p => p.2.2) hb.2
    simp only [ent] at h1 h2
    rw [h1, h2]
  exact r.perm.injective this

/-- A round inserts at most `k` times into a half. -/
theorem countP_half_le (r : Round k) (H : RowH k) (Q : RowH k × ℕ × Sq k → Prop)
    [DecidablePred Q] :
    (roundIns r).countP (fun p => decide (p.1 = H ∧ Q p)) ≤ k := by
  rw [countP_roundIns]
  calc _ ≤ (univ : Finset (Fin k)).card := by
        apply card_le_card_of_injOn (fun S => S.2) (fun _ _ => mem_coe.mpr (mem_univ _))
        intro a ha b hb hab
        simp only [coe_filter, Set.mem_ofPred_eq] at ha hb
        have h1 := congrArg (fun p => p.1) ha.2.1
        have h2 := congrArg (fun p => p.1) hb.2.1
        simp only [ent, hop1Half] at h1 h2
        exact Prod.ext (h1.trans h2.symm) hab
    _ = k := by simp

/-- Insertions land inside their half. -/
theorem insPos_lt_rowLen_of_mem {s : ℕ} (hs : 1 ≤ s) {r : Round k} {p : RowH k × ℕ × Sq k}
    (hp : p ∈ roundIns r) : insPos k s p.1 p.2.1 + 1 ≤ rowLen k s p.1 := by
  obtain ⟨S, hS, rfl⟩ := mem_roundIns hp
  simp only [srcs, mem_filter, mem_univ, true_and] at hS
  have hne : S.2.val ≠ (r.perm S).2.val := fun h => hS.2 (Fin.ext h)
  have h1 := S.2.isLt
  have h2 := (r.perm S).2.isLt
  simp only [ent, insPos, rowLen, hop1Half, hop1Dist, Nat.dist]
  by_cases hlt : (r.perm S).2 < S.2
  · have hlt' : (r.perm S).2.val < S.2.val := hlt
    simp only [hlt, decide_true, if_true]
    have e1 : S.2.val - (r.perm S).2.val - 1 + 1 ≤ k - 1 - (r.perm S).2.val := by omega
    have := Nat.mul_le_mul_right s e1
    have : 1 ≤ (S.2.val - (r.perm S).2.val - 1 + 1) * s := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))
    rw [show (r.perm S).2.val - S.2.val = 0 by omega, add_zero]
    omega
  · have hlt' : ¬ (r.perm S).2.val < S.2.val := hlt
    simp only [hlt, decide_false, Bool.false_eq_true, if_false]
    have e1 : (r.perm S).2.val - S.2.val - 1 + 1 ≤ (r.perm S).2.val := by omega
    have := Nat.mul_le_mul_right s e1
    have : 1 ≤ (r.perm S).2.val * s := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))
    rw [show S.2.val - (r.perm S).2.val = 0 by omega, zero_add]
    omega

/-- Splitting the insertions from distances `≥ d` by distance. -/
theorem countP_ge_eq_sum (r : Round k) (H : RowH k) (d : ℕ) :
    (roundIns r).countP (fun p => decide (p.1 = H ∧ d ≤ p.2.1)) =
      ∑ d' ∈ Ico d k, (roundIns r).countP (fun p => decide (p.1 = H ∧ p.2.1 = d')) := by
  simp_rw [countP_roundIns]
  rw [card_eq_sum_card_fiberwise (f := fun S => (ent r S).2.1) (t := Ico d k)]
  · refine sum_congr rfl fun d' hd' => ?_
    rw [filter_filter]
    apply congrArg; apply filter_congr
    intro S _
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ (mem_Ico.mp hd').1⟩, h2⟩
  · intro S hS
    simp only [coe_filter, Set.mem_ofPred_eq] at hS
    exact mem_Ico.mpr ⟨hS.2.2, ent_dist_lt r S⟩

/-- Splitting the insertions at distance `d` by class. -/
theorem sum_count_class (r : Round k) (H : RowH k) (d : ℕ) :
    ∑ x : Sq k, (roundIns r).countP (fun p => decide (p = (H, d, x))) =
      (roundIns r).countP (fun p => decide (p.1 = H ∧ p.2.1 = d)) := by
  simp_rw [countP_roundIns]
  rw [card_eq_sum_card_fiberwise (f := fun S => (ent r S).2.2) (t := univ)
    (fun _ _ => mem_coe.mpr (mem_univ _))]
  refine sum_congr rfl fun x _ => ?_
  rw [filter_filter]
  apply congrArg; apply filter_congr
  intro S _
  constructor
  · intro h; rw [h]; exact ⟨⟨rfl, rfl⟩, rfl⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rw [← h1, ← h2, ← h3]

/-! ## Per-half statistics of the plan and the window parameters -/

section params

variable {Δ : ℕ} (s : ℕ) (rs : Fin Δ → Round k)

/-- Insertions into `H` from distances `≥ d` in plan round `j`. -/
noncomputable def gcnt (H : RowH k) (d : ℕ) (j : Fin Δ) : ℕ :=
  (roundIns (rs j)).countP fun p => decide (p.1 = H ∧ d ≤ p.2.1)

/-- Insertions into `H` from distance exactly `d` in plan round `j`. -/
noncomputable def gdist (H : RowH k) (d : ℕ) (j : Fin Δ) : ℕ :=
  (roundIns (rs j)).countP fun p => decide (p.1 = H ∧ p.2.1 = d)

/-- Insertions of `(H, d, x)` in plan round `j` (`0` or `1`). -/
noncomputable def acnt (H : RowH k) (d : ℕ) (x : Sq k) (j : Fin Δ) : ℕ :=
  (roundIns (rs j)).countP fun p => decide (p = (H, d, x))

/-- `B_d`: all insertions into `H` from distances `≥ d`. -/
noncomputable def Btot (H : RowH k) (d : ℕ) : ℕ := ∑ j, gcnt rs H d j

/-- `A_{x,d}`: all insertions of `(H, d, x)`. -/
noncomputable def Atot (H : RowH k) (d : ℕ) (x : Sq k) : ℕ := ∑ j, acnt rs H d x j

/-- The window length `w_d = min Δ (⌊6 (p_d + 1) Δ / (5 B_d)⌋ + 1)` (`Δ` if `B_d = 0`). -/
noncomputable def win (H : RowH k) (d : ℕ) : ℕ :=
  if Btot rs H d = 0 then Δ else min Δ (6 * (insPos k s H d + 1) * Δ / (5 * Btot rs H d) + 1)

/-- The additive slack `λ = 4 (log₂ n + 1)`. -/
def lamN (n : ℕ) : ℕ := 4 * (Nat.log 2 n + 1)

/-- The bound on present `(H, d, x)` tiles. -/
noncomputable def Nb (n : ℕ) (H : RowH k) (d : ℕ) (x : Sq k) : ℕ :=
  if Atot rs H d x = 0 then 0 else 17 * Atot rs H d x * (win s rs H d + 1) / (16 * Δ) + 6 * lamN n

/-- The row insertions at time `τ` of the order `σ` (none after the end). -/
noncomputable def rnd (σ : Equiv.Perm (Fin Δ)) (τ : ℕ) : List (RowH k × ℕ × Sq k) :=
  if h : τ < Δ then roundIns (rs (σ ⟨τ, h⟩)) else []

/-- Sums over times of a function of `rnd` are sums over plan rounds. -/
theorem sum_rnd (σ : Equiv.Perm (Fin Δ)) (U : Finset ℕ) (F : List (RowH k × ℕ × Sq k) → ℕ)
    (hF : F [] = 0) :
    ∑ τ ∈ U, F (rnd rs σ τ) =
      ∑ τ ∈ univ.filter (fun τ : Fin Δ => τ.val ∈ U), F (roundIns (rs (σ τ))) := by
  have h1 : ∑ τ ∈ univ.filter (fun τ : Fin Δ => τ.val ∈ U), F (roundIns (rs (σ τ))) =
      ∑ τ ∈ (univ.filter (fun τ : Fin Δ => τ.val ∈ U)).map Fin.valEmbedding, F (rnd rs σ τ) := by
    rw [sum_map]
    refine sum_congr rfl fun τ _ => ?_
    simp [rnd, τ.isLt]
  have h2 : (univ.filter (fun τ : Fin Δ => τ.val ∈ U)).map Fin.valEmbedding =
      U.filter (· < Δ) := by
    ext i
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨ha, a.isLt⟩
    · rintro ⟨hi, hlt⟩; exact ⟨⟨i, hlt⟩, hi, rfl⟩
  rw [h1, h2, sum_filter]
  refine sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rfl
  · simp [rnd, h, hF]

theorem card_fin_filter_mem {Δ : ℕ} (U : Finset ℕ) :
    (univ.filter (fun τ : Fin Δ => τ.val ∈ U)).card = (U.filter (· < Δ)).card := by
  rw [← card_map Fin.valEmbedding]
  congr 1
  ext i
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨ha, a.isLt⟩
  · rintro ⟨hi, hlt⟩; exact ⟨⟨i, hlt⟩, hi, rfl⟩

theorem mem_rnd {σ : Equiv.Perm (Fin Δ)} {τ : ℕ} {p : RowH k × ℕ × Sq k} (hp : p ∈ rnd rs σ τ) :
    ∃ j, p ∈ roundIns (rs j) := by
  unfold rnd at hp
  split_ifs at hp
  · exact ⟨_, hp⟩
  · simp at hp

/-- A consistent list performs `rnd` at every time. -/
theorem consistent_rnd {σ : Equiv.Perm (Fin Δ)} {L : List (InsRec k)} (hL : Consistent rs σ L)
    (τ : ℕ) : ((L.filter fun r => r.τ = τ).map proj).Perm (rnd rs σ τ) := by
  unfold rnd
  split_ifs with h
  · exact hL.2.2 τ h
  · have : L.filter (fun r => r.τ = τ) = [] := by
      rw [List.filter_eq_nil_iff]
      intro r hr
      have := hL.2.1 r hr
      simp only [decide_eq_true_eq]; omega
    rw [this]; exact List.Perm.refl _

end params

end SlidingPuzzle.Hub
