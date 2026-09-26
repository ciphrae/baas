import SlidingPuzzle.Hub.Plan
import SlidingPuzzle.Hub.WalkSnake

/-! # The walk of one round

In a round every square with a real in-edge is served once, by its sender, and
the blank follows the tiles backwards: serving `D` from `S = perm⁻¹ D` moves the
blank from `D` to `S`. The components of the round are cut at dummy edges into
paths (each started by one relocation) and dummy-free cycles, which are started
at their snake-minimal square in snake order, so that the relocations between
consecutive cycles telescope. -/
namespace SlidingPuzzle.Hub

/-- High-level events: `serve S D` (blank at `D`, ends at `S`) and a relocation
of the blank from `E` to `Z`. -/
inductive HEvent (k : ℕ) where
  | serve (S D : Sq k)
  | reloc (E Z : Sq k)
  deriving DecidableEq

/-- Blank consistency of a list of events started with the blank in `b`. -/
def HChain {k : ℕ} : Sq k → List (HEvent k) → Prop
  | _, [] => True
  | b, .serve S D :: es => b = D ∧ HChain S es
  | b, .reloc E Z :: es => b = E ∧ E ≠ Z ∧ HChain Z es

/-- The square holding the blank after a list of events. -/
def hEnd {k : ℕ} : Sq k → List (HEvent k) → Sq k
  | b, [] => b
  | _, .serve S _ :: es => hEnd S es
  | _, .reloc _ Z :: es => hEnd Z es

/-- Weight of a relocation (`1 + ` its square distance); serves weigh nothing. -/
def relocWeight {k : ℕ} : HEvent k → ℕ
  | .serve _ _ => 0
  | .reloc E Z => 1 + sqDist E Z

/-! ## Chain lemmas -/

lemma hChain_append {k : ℕ} (b : Sq k) (l1 l2 : List (HEvent k)) :
    HChain b (l1 ++ l2) ↔ HChain b l1 ∧ HChain (hEnd b l1) l2 := by
  induction l1 generalizing b with
  | nil => simp [HChain, hEnd]
  | cons e l ih =>
    cases e with
    | serve S D => simp [HChain, hEnd, ih, and_assoc]
    | reloc E Z => simp [HChain, hEnd, ih, and_assoc]

lemma hEnd_append {k : ℕ} (b : Sq k) (l1 l2 : List (HEvent k)) :
    hEnd b (l1 ++ l2) = hEnd (hEnd b l1) l2 := by
  induction l1 generalizing b with
  | nil => rfl
  | cons e l ih => cases e <;> simp [hEnd, ih]

/-- Relocate the blank from `b` to `Z` unless it is already there. -/
def relocTo {k : ℕ} (b Z : Sq k) : List (HEvent k) := if b = Z then [] else [.reloc b Z]

lemma relocTo_chain {k : ℕ} (b Z : Sq k) : HChain b (relocTo b Z) ∧ hEnd b (relocTo b Z) = Z := by
  unfold relocTo
  split_ifs with h
  · exact ⟨trivial, h⟩
  · exact ⟨⟨rfl, h, trivial⟩, rfl⟩

lemma relocTo_count {k : ℕ} (b Z S D : Sq k) : (relocTo b Z).count (.serve S D) = 0 := by
  unfold relocTo; split_ifs <;> simp

lemma relocTo_weight {k : ℕ} (b Z : Sq k) : ((relocTo b Z).map relocWeight).sum + 1 ≤ 2 * k := by
  have := sqDist_le_two b Z
  unfold relocTo; split_ifs <;> simp [relocWeight]
  all_goals omega

lemma relocTo_weight_snake {k : ℕ} (b Z : Sq k) (h : snake b ≤ snake Z) :
    ((relocTo b Z).map relocWeight).sum ≤ 1 + (snake Z - snake b) := by
  have := sqDist_le_snake h
  unfold relocTo; split_ifs <;> simp [relocWeight]
  all_goals omega

/-! ## The walk -/

namespace Round
variable {k : ℕ} (r : Round k)

/-- `D` has a real in-edge (it is served in this round). -/
def inR (D : Sq k) : Prop := r.real (r.perm.symm D)

instance (D : Sq k) : Decidable (r.inR D) := by unfold inR; infer_instance

lemma inR_ne {D : Sq k} (h : r.inR D) : r.perm.symm D ≠ D := by
  intro h2; apply h.1; simp only [Equiv.apply_symm_apply]; exact h2.symm

end Round

/-- Walk backwards along real edges from `x`, serving unserved squares. Returns
the events, the new set of served squares and the final blank square. -/
def walk {k : ℕ} (r : Round k) (sv : Finset (Sq k)) (x : Sq k) :
    List (HEvent k) × Finset (Sq k) × Sq k :=
  if _h : r.inR x ∧ x ∉ sv then
    let res := walk r (insert x sv) (r.perm.symm x)
    (.serve (r.perm.symm x) x :: res.1, res.2)
  else ([], sv, x)
termination_by Fintype.card (Sq k) - sv.card
decreasing_by
  have h1 := Finset.card_insert_of_notMem _h.2
  have h2 := Finset.card_le_univ (insert x sv)
  omega

lemma walk_chain {k : ℕ} (r : Round k) (sv : Finset (Sq k)) (x : Sq k) :
    HChain x (walk r sv x).1 ∧ hEnd x (walk r sv x).1 = (walk r sv x).2.2 := by
  fun_induction walk r sv x with
  | case1 sv x h res ih =>
    simp only [HChain, hEnd, true_and]
    exact ih
  | case2 sv x h => exact ⟨trivial, rfl⟩

lemma walk_weight {k : ℕ} (r : Round k) (sv : Finset (Sq k)) (x : Sq k) :
    ((walk r sv x).1.map relocWeight).sum = 0 := by
  fun_induction walk r sv x with
  | case1 sv x h res ih => simpa [relocWeight] using ih
  | case2 sv x h => rfl

/-- Indicator of `serve S D` having happened, given the served set. -/
def ind {k : ℕ} (r : Round k) (sv : Finset (Sq k)) (S D : Sq k) : ℕ :=
  if D ∈ sv ∧ S = r.perm.symm D then 1 else 0

lemma walk_count {k : ℕ} (r : Round k) (sv : Finset (Sq k)) (x : Sq k) (S D : Sq k) :
    (walk r sv x).1.count (.serve S D) + ind r sv S D = ind r (walk r sv x).2.1 S D := by
  fun_induction walk r sv x with
  | case1 sv x h res ih =>
    dsimp only [res] at ih ⊢
    rw [← ih, List.count_cons]
    have key : ind r (insert x sv) S D =
        ind r sv S D + (if HEvent.serve (r.perm.symm x) x == HEvent.serve S D then 1 else 0) := by
      unfold ind
      by_cases hD : D = x
      · subst hD
        by_cases hS : S = r.perm.symm D
        · subst hS; simp [h.2]
        · simp [hS, Ne.symm hS]
      · simp [hD, Ne.symm hD]
    rw [key]; omega
  | case2 sv x h => simp

lemma walk_sub {k : ℕ} (r : Round k) (sv : Finset (Sq k)) (x : Sq k) :
    sv ⊆ (walk r sv x).2.1 ∧ ∀ D ∈ (walk r sv x).2.1, D ∈ sv ∨ r.inR D := by
  fun_induction walk r sv x with
  | case1 sv x h res ih =>
    refine ⟨fun y hy => ih.1 (Finset.mem_insert_of_mem hy), fun D hD => ?_⟩
    rcases ih.2 D hD with h1 | h1
    · rcases Finset.mem_insert.1 h1 with h2 | h2
      · subst h2; exact Or.inr h.1
      · exact Or.inl h2
    · exact Or.inr h1
  | case2 sv x h => exact ⟨subset_rfl, fun D hD => Or.inl hD⟩

lemma walk_mem {k : ℕ} (r : Round k) (sv : Finset (Sq k)) (x : Sq k) (hx : r.inR x)
    (hxs : x ∉ sv) : x ∈ (walk r sv x).2.1 := by
  rw [walk, dif_pos ⟨hx, hxs⟩]
  exact (walk_sub r _ _).1 (Finset.mem_insert_self _ _)

/-- Closure of the served set: a served square's real in-neighbour is served. -/
def P2 {k : ℕ} (r : Round k) (sv : Finset (Sq k)) : Prop :=
  ∀ y ∈ sv, r.inR (r.perm.symm y) → r.perm.symm y ∈ sv

/-- Every path start (dummy out-edge, real in-edge) is served. -/
def P1 {k : ℕ} (r : Round k) (sv : Finset (Sq k)) : Prop :=
  ∀ Z, r.isDummy Z → r.inR Z → Z ∈ sv

lemma walk_P2_aux {k : ℕ} (r : Round k) (sv : Finset (Sq k)) (x : Sq k)
    (hQ : ∀ y ∈ sv, y ≠ r.perm x → r.inR (r.perm.symm y) → r.perm.symm y ∈ sv) :
    P2 r (walk r sv x).2.1 := by
  fun_induction walk r sv x with
  | case1 sv x h res ih =>
    apply ih
    intro y hy hne hR
    simp only [Equiv.apply_symm_apply] at hne
    rcases Finset.mem_insert.1 hy with h1 | h1
    · exact absurd h1 hne
    · by_cases h2 : y = r.perm x
      · subst h2; simp
      · exact Finset.mem_insert_of_mem (hQ y h1 h2 hR)
  | case2 sv x h =>
    intro y hy hR
    by_cases h2 : y = r.perm x
    · subst h2
      simp only [Equiv.symm_apply_apply] at hR ⊢
      by_contra h3
      exact h ⟨hR, h3⟩
    · exact hQ y hy h2 hR

lemma walk_P2 {k : ℕ} (r : Round k) (sv : Finset (Sq k)) (x : Sq k) (h : P2 r sv) :
    P2 r (walk r sv x).2.1 :=
  walk_P2_aux r sv x fun y hy _ hR => h y hy hR

lemma walk_cycle {k : ℕ} (r : Round k) (sv : Finset (Sq k)) (x D : Sq k)
    (ha : (r.inR x ∧ x ∉ sv) ∨ x = D)
    (hb : ∀ y, r.inR y → y ∉ sv → (r.inR (r.perm.symm y) ∧ r.perm.symm y ∉ sv) ∨
      r.perm.symm y = D)
    (hc : x ≠ D → ¬ (r.inR (r.perm x) ∧ r.perm x ∉ sv)) :
    (walk r sv x).2.2 = D := by
  fun_induction walk r sv x with
  | case1 sv x h res ih =>
    have hne := r.inR_ne h.1
    apply ih
    · rcases hb x h.1 h.2 with h1 | h1
      · refine Or.inl ⟨h1.1, ?_⟩
        rw [Finset.mem_insert, not_or]; exact ⟨hne, h1.2⟩
      · exact Or.inr h1
    · intro y hy hys
      rw [Finset.mem_insert, not_or] at hys
      rcases hb y hy hys.2 with h1 | h1
      · by_cases h2 : r.perm.symm y = x
        · by_cases hxD : x = D
          · exact Or.inr (h2.trans hxD)
          · exfalso
            apply hc hxD
            rw [← h2, Equiv.apply_symm_apply]; exact ⟨hy, hys.2⟩
        · refine Or.inl ⟨h1.1, ?_⟩
          rw [Finset.mem_insert, not_or]; exact ⟨h2, h1.2⟩
      · exact Or.inr h1
    · intro _ h1
      simp only [Equiv.apply_symm_apply] at h1
      exact h1.2 (Finset.mem_insert_self _ _)
  | case2 sv x h =>
    rcases ha with h1 | h1
    · exact absurd h1 h
    · exact h1

/-- The served set is closed under the in-neighbour map on unserved real squares. -/
lemma inv_of_P {k : ℕ} (r : Round k) (sv : Finset (Sq k)) (h1 : P1 r sv) (h2 : P2 r sv)
    (y : Sq k) (hy : r.inR y) (hys : y ∉ sv) :
    r.inR (r.perm.symm y) ∧ r.perm.symm y ∉ sv := by
  have step : ∀ z, r.inR z → z ∉ sv → r.inR (r.perm z) ∧ r.perm z ∉ sv := by
    intro z hz hzs
    have hne := r.inR_ne hz
    have hpz : r.perm z ≠ z := by
      intro h; apply hne; rw [Equiv.symm_apply_eq]; exact h.symm
    have hreal : r.real z := by
      refine ⟨hpz, ?_⟩
      by_contra hd
      exact hzs (h1 z ⟨hpz, by simpa using hd⟩ hz)
    have hR : r.inR (r.perm z) := by
      unfold Round.inR; simpa using hreal
    refine ⟨hR, fun hm => hzs ?_⟩
    have := h2 _ hm
    simp only [Equiv.symm_apply_apply] at this
    exact this hz
  have hall : ∀ j : ℕ, r.inR ((r.perm ^ j) y) ∧ (r.perm ^ j) y ∉ sv := by
    intro j
    induction j with
    | zero => exact ⟨hy, hys⟩
    | succ j ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact step _ ih.1 ih.2
  have hinv : r.perm ^ (orderOf r.perm - 1) = r.perm⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos r.perm), pow_orderOf_eq_one]
  have := hall (orderOf r.perm - 1)
  rw [hinv] at this
  exact this

/-- The events of one round, started with the blank in `cur`. -/
theorem exists_round_events {k : ℕ} (r : Round k) (cur : Sq k) :
    ∃ es : List (HEvent k),
      HChain cur es ∧
      (∀ S D, es.count (.serve S D) = if r.perm S = D ∧ r.real S then 1 else 0) ∧
      (es.map relocWeight).sum ≤
        4 * k ^ 2 + 4 * k * (1 + (Finset.univ.filter fun S => r.isDummy S).card) := by
  sorry

end SlidingPuzzle.Hub
