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

/-- Weight of a relocation: `13 + 21·` its square distance for one jump between
aligned squares, `26 + 21·` it for two jumps through a corner (a jump costs
`(s + 3)(13 + 21 d)`); serves weigh nothing. -/
def relocWeight {k : ℕ} : HEvent k → ℕ
  | .serve _ _ => 0
  | .reloc E Z => if E.1 = Z.1 ∨ E.2 = Z.2 then 13 + 21 * sqDist E Z else 26 + 21 * sqDist E Z

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

lemma relocTo_weight {k : ℕ} (b Z : Sq k) : ((relocTo b Z).map relocWeight).sum ≤ 42 * k + 18 := by
  have := sqDist_le_two b Z
  unfold relocTo; split_ifs <;> simp [relocWeight]
  all_goals split_ifs <;> omega

/-- The row index does not decrease along the snake. -/
lemma row_le_of_snake_le {k : ℕ} {b Z : Sq k} (h : snake b ≤ snake Z) : b.1.val ≤ Z.1.val := by
  by_contra hc
  have h1 := snakePos_lt (k := k) (b := Z.1.val) Z.2.isLt
  have h2 : (Z.1.val + 1) * k ≤ b.1.val * k := Nat.mul_le_mul_right _ (by omega)
  unfold snake at h
  nlinarith

/-- A relocation along the snake needs a second jump only when it changes rows. -/
lemma relocTo_weight_snake {k : ℕ} (b Z : Sq k) (h : snake b ≤ snake Z) :
    ((relocTo b Z).map relocWeight).sum ≤
      13 + 21 * (snake Z - snake b) + 13 * (Z.1.val - b.1.val) := by
  have := sqDist_le_snake h
  have hrow := row_le_of_snake_le h
  unfold relocTo; split_ifs with hbZ <;> simp [relocWeight]
  split_ifs with hal
  · omega
  · have : b.1.val ≠ Z.1.val := fun e => hal (Or.inl (Fin.ext e))
    omega

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
def walkInd {k : ℕ} (r : Round k) (sv : Finset (Sq k)) (S D : Sq k) : ℕ :=
  if D ∈ sv ∧ S = r.perm.symm D then 1 else 0

lemma walk_count {k : ℕ} (r : Round k) (sv : Finset (Sq k)) (x : Sq k) (S D : Sq k) :
    (walk r sv x).1.count (.serve S D) + walkInd r sv S D = walkInd r (walk r sv x).2.1 S D := by
  fun_induction walk r sv x with
  | case1 sv x h res ih =>
    dsimp only [res] at ih ⊢
    rw [← ih, List.count_cons]
    have key : walkInd r (insert x sv) S D =
        walkInd r sv S D + (if HEvent.serve (r.perm.symm x) x == HEvent.serve S D then 1 else 0) := by
      unfold walkInd
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

/-! ## Phases -/

/-- Process the squares of `L` in order: each square `Z` with `p Z` that is real and
unserved gets a relocation (if needed) and a walk from `Z`. -/
def phase {k : ℕ} (r : Round k) (p : Sq k → Bool) :
    List (Sq k) → Finset (Sq k) → Sq k → List (HEvent k) × Finset (Sq k) × Sq k
  | [], sv, b => ([], sv, b)
  | Z :: Zs, sv, b =>
    if p Z ∧ r.inR Z ∧ Z ∉ sv then
      ((relocTo b Z ++ (walk r sv Z).1) ++
          (phase r p Zs (walk r sv Z).2.1 (walk r sv Z).2.2).1,
        (phase r p Zs (walk r sv Z).2.1 (walk r sv Z).2.2).2)
    else phase r p Zs sv b

section phase
variable {k : ℕ} (r : Round k) (p : Sq k → Bool)

lemma phase_chain (L : List (Sq k)) (sv : Finset (Sq k)) (b : Sq k) :
    HChain b (phase r p L sv b).1 ∧ hEnd b (phase r p L sv b).1 = (phase r p L sv b).2.2 := by
  induction L generalizing sv b with
  | nil => exact ⟨trivial, rfl⟩
  | cons Z Zs ih =>
    simp only [phase]
    split_ifs with h
    · have h1 := relocTo_chain b Z
      have h2 := walk_chain r sv Z
      have h3 := ih (walk r sv Z).2.1 (walk r sv Z).2.2
      rw [hChain_append, hChain_append]
      simp only [hEnd_append, h1.2, h2.2]
      exact ⟨⟨⟨h1.1, h2.1⟩, h3.1⟩, h3.2⟩
    · exact ih sv b

lemma phase_count (L : List (Sq k)) (sv : Finset (Sq k)) (b : Sq k) (S D : Sq k) :
    (phase r p L sv b).1.count (.serve S D) + walkInd r sv S D =
      walkInd r (phase r p L sv b).2.1 S D := by
  induction L generalizing sv b with
  | nil => simp [phase]
  | cons Z Zs ih =>
    simp only [phase]
    split_ifs with h
    · rw [List.count_append, List.count_append, relocTo_count, ← ih, ← walk_count r sv Z S D]
      omega
    · exact ih sv b

lemma phase_sub (L : List (Sq k)) (sv : Finset (Sq k)) (b : Sq k) :
    sv ⊆ (phase r p L sv b).2.1 ∧ ∀ D ∈ (phase r p L sv b).2.1, D ∈ sv ∨ r.inR D := by
  induction L generalizing sv b with
  | nil => exact ⟨subset_rfl, fun D hD => Or.inl hD⟩
  | cons Z Zs ih =>
    simp only [phase]
    split_ifs with h
    · have h1 := walk_sub r sv Z
      have h2 := ih (walk r sv Z).2.1 (walk r sv Z).2.2
      refine ⟨h1.1.trans h2.1, fun D hD => ?_⟩
      rcases h2.2 D hD with h3 | h3
      · exact h1.2 D h3
      · exact Or.inr h3
    · exact ih sv b

lemma phase_cover (L : List (Sq k)) (sv : Finset (Sq k)) (b : Sq k) :
    ∀ Z ∈ L, p Z → r.inR Z → Z ∈ (phase r p L sv b).2.1 := by
  induction L generalizing sv b with
  | nil => simp
  | cons Z Zs ih =>
    intro Z' hZ' hp hR
    simp only [phase]
    split_ifs with h
    · rcases List.mem_cons.1 hZ' with h1 | h1
      · subst h1
        exact (phase_sub r p Zs _ _).1 (walk_mem r sv Z' hR h.2.2)
      · exact ih _ _ Z' h1 hp hR
    · rcases List.mem_cons.1 hZ' with h1 | h1
      · subst h1
        by_contra h2
        apply h ⟨hp, hR, fun h3 => h2 ((phase_sub r p Zs sv b).1 h3)⟩
      · exact ih _ _ Z' h1 hp hR

lemma phase_P2 (L : List (Sq k)) (sv : Finset (Sq k)) (b : Sq k) (h : P2 r sv) :
    P2 r (phase r p L sv b).2.1 := by
  induction L generalizing sv b with
  | nil => exact h
  | cons Z Zs ih =>
    simp only [phase]
    split_ifs with h1
    · exact ih _ _ (walk_P2 r sv Z h)
    · exact ih sv b h

lemma phase_cost1 (L : List (Sq k)) (sv : Finset (Sq k)) (b : Sq k) :
    ((phase r p L sv b).1.map relocWeight).sum ≤
      (L.map fun Z => if p Z then 42 * k + 18 else 0).sum := by
  induction L generalizing sv b with
  | nil => simp [phase]
  | cons Z Zs ih =>
    simp only [phase, List.map_cons, List.sum_cons]
    split_ifs with h h'
    · simp only [List.map_append, List.sum_append, walk_weight]
      have := relocTo_weight b Z
      have := ih (walk r sv Z).2.1 (walk r sv Z).2.2
      omega
    · exact absurd h.1 h'
    · have := ih sv b; omega
    · have := ih sv b; omega

end phase

/-- A cycle walk started at an unserved real square serves at least two squares. -/
lemma walk_card_two {k : ℕ} (r : Round k) (sv : Finset (Sq k)) (Z : Sq k)
    (h : r.inR Z ∧ Z ∉ sv) (h1 : P1 r sv) (h2 : P2 r sv) :
    sv.card + 2 ≤ (walk r sv Z).2.1.card := by
  have hi := inv_of_P r sv h1 h2 Z h.1 h.2
  have hne := r.inR_ne h.1
  have hmem : r.perm.symm Z ∉ insert Z sv := by
    rw [Finset.mem_insert, not_or]; exact ⟨hne, hi.2⟩
  rw [walk, dif_pos h]
  dsimp only
  have hsub := (walk_sub r (insert Z sv) (r.perm.symm Z)).1
  have hin := walk_mem r (insert Z sv) (r.perm.symm Z) hi.1 hmem
  have hcard := Finset.card_le_card (Finset.insert_subset hin hsub)
  rw [Finset.card_insert_of_notMem hmem, Finset.card_insert_of_notMem h.2] at hcard
  exact hcard

lemma phase_costA {k : ℕ} (r : Round k) (L : List (Sq k)) (sv : Finset (Sq k)) (B : Sq k)
    (hL : L.Pairwise (fun P Q => snake P < snake Q)) (hB : ∀ Z ∈ L, snake B ≤ snake Z)
    (h1 : P1 r sv) (h2 : P2 r sv) :
    ((phase r (fun _ => true) L sv B).1.map relocWeight).sum + 21 * snake B + 13 * B.1.val +
      7 * sv.card ≤ 7 * (phase r (fun _ => true) L sv B).2.1.card + 21 * (k * k) + 13 * k := by
  induction L generalizing sv B with
  | nil => simp only [phase]; have := snake_lt B; have := B.1.isLt; simp; omega
  | cons Z Zs ih =>
    rw [List.pairwise_cons] at hL
    have hBZ := hB Z List.mem_cons_self
    have hZk := snake_lt Z
    simp only [phase]
    split_ifs with h
    · have hend : (walk r sv Z).2.2 = Z := by
        apply walk_cycle r sv Z Z (Or.inl h.2)
        · intro y hy hys; exact Or.inl (inv_of_P r sv h1 h2 y hy hys)
        · intro h3; exact absurd rfl h3
      have hsub := walk_sub r sv Z
      have := ih (walk r sv Z).2.1 Z hL.2 (fun Z' hZ' => (hL.1 Z' hZ').le)
        (fun Z' hd hR => hsub.1 (h1 Z' hd hR)) (walk_P2 r sv Z h2)
      rw [hend]
      simp only [List.map_append, List.sum_append, walk_weight]
      have := relocTo_weight_snake B Z hBZ
      have := row_le_of_snake_le hBZ
      have := walk_card_two r sv Z ⟨h.2.1, h.2.2⟩ h1 h2
      omega
    · exact ih sv B hL.2 (fun Z' hZ' => hB Z' (List.mem_cons_of_mem _ hZ')) h1 h2

lemma phase_costB {k : ℕ} (r : Round k) (L : List (Sq k)) (sv : Finset (Sq k)) (b : Sq k)
    (hL : L.Pairwise (fun P Q => snake P < snake Q)) (h1 : P1 r sv) (h2 : P2 r sv) :
    ((phase r (fun _ => true) L sv b).1.map relocWeight).sum + 7 * sv.card ≤
      42 * k + 18 + 7 * (phase r (fun _ => true) L sv b).2.1.card + 21 * (k * k) + 13 * k := by
  induction L generalizing sv b with
  | nil => simp [phase]; omega
  | cons Z Zs ih =>
    rw [List.pairwise_cons] at hL
    simp only [phase]
    split_ifs with h
    · have hend : (walk r sv Z).2.2 = Z := by
        apply walk_cycle r sv Z Z (Or.inl h.2)
        · intro y hy hys; exact Or.inl (inv_of_P r sv h1 h2 y hy hys)
        · intro h3; exact absurd rfl h3
      have hsub := walk_sub r sv Z
      have := phase_costA r Zs (walk r sv Z).2.1 Z hL.2 (fun Z' hZ' => (hL.1 Z' hZ').le)
        (fun Z' hd hR => hsub.1 (h1 Z' hd hR)) (walk_P2 r sv Z h2)
      rw [hend]
      simp only [List.map_append, List.sum_append, walk_weight]
      have := relocTo_weight b Z
      have := walk_card_two r sv Z ⟨h.2.1, h.2.2⟩ h1 h2
      omega
    · exact ih sv b hL.2 h1 h2

/-- The events of one round, started with the blank in `cur`. -/
theorem exists_round_events {k : ℕ} (r : Round k) (cur : Sq k) :
    ∃ es : List (HEvent k),
      HChain cur es ∧
      (∀ S D, es.count (.serve S D) = if r.perm S = D ∧ r.real S then 1 else 0) ∧
      (es.map relocWeight).sum ≤
        28 * k ^ 2 + 55 * k + 18 + (42 * k + 18) * (Finset.univ.filter fun S => r.isDummy S).card := by
  let p1 : Sq k → Bool := fun Z => decide (r.isDummy Z)
  let ph1 := phase r p1 Finset.univ.toList ∅ cur
  let ph2 := phase r (fun _ => true) (snakeList k) ph1.2.1 ph1.2.2
  have hP1 : P1 r ph1.2.1 := fun Z hd hR =>
    phase_cover r p1 _ ∅ cur Z (Finset.mem_toList.2 (Finset.mem_univ Z)) (by simp [p1, hd]) hR
  have hP2 : P2 r ph1.2.1 := phase_P2 r p1 _ ∅ cur (by intro y hy; simp at hy)
  refine ⟨ph1.1 ++ ph2.1, ?_, ?_, ?_⟩
  · rw [hChain_append]
    have a := phase_chain r p1 Finset.univ.toList ∅ cur
    have b := phase_chain r (fun _ => true) (snakeList k) ph1.2.1 ph1.2.2
    rw [a.2]
    exact ⟨a.1, b.1⟩
  · intro S D
    have c1 : ph1.1.count (.serve S D) + walkInd r ∅ S D = walkInd r ph1.2.1 S D :=
      phase_count r p1 Finset.univ.toList ∅ cur S D
    have c2 : ph2.1.count (.serve S D) + walkInd r ph1.2.1 S D = walkInd r ph2.2.1 S D :=
      phase_count r (fun _ => true) (snakeList k) ph1.2.1 ph1.2.2 S D
    have hind0 : walkInd r ∅ S D = 0 := by simp [walkInd]
    have hsv : D ∈ ph2.2.1 ↔ r.inR D := by
      constructor
      · intro hD
        rcases (phase_sub r _ (snakeList k) ph1.2.1 ph1.2.2).2 D hD with h | h
        · rcases (phase_sub r p1 Finset.univ.toList ∅ cur).2 D h with h' | h'
          · simp at h'
          · exact h'
        · exact h
      · intro hD
        exact phase_cover r _ (snakeList k) _ _ D (mem_snakeList D) rfl hD
    rw [List.count_append]
    have hsum : ph1.1.count (.serve S D) + ph2.1.count (.serve S D) = walkInd r ph2.2.1 S D := by
      omega
    rw [hsum]
    unfold walkInd
    by_cases h : r.perm S = D ∧ r.real S
    · rw [if_pos h, if_pos]
      obtain ⟨rfl, h2⟩ := h
      refine ⟨hsv.2 ?_, by simp⟩
      unfold Round.inR; simpa using h2
    · rw [if_neg h, if_neg]
      rintro ⟨h1, rfl⟩
      apply h
      refine ⟨by simp, ?_⟩
      exact hsv.1 h1
  · rw [List.map_append, List.sum_append]
    have k1 := phase_cost1 r p1 Finset.univ.toList ∅ cur
    rw [Finset.sum_map_toList] at k1
    have e : ∑ Z, (if p1 Z = true then 42 * k + 18 else 0) =
        (Finset.univ.filter fun S => r.isDummy S).card * (42 * k + 18) := by
      rw [← Finset.sum_filter]
      simp [p1]
    rw [e] at k1
    have k2 := phase_costB r (snakeList k) ph1.2.1 ph1.2.2 snakeList_pairwise hP1 hP2
    have k3 : ph2.2.1.card ≤ k * k := by
      simpa [Fintype.card_prod] using Finset.card_le_univ ph2.2.1
    change _ + (List.map relocWeight ph2.1).sum ≤ _
    nlinarith [k1, k2, k3]

end SlidingPuzzle.Hub
