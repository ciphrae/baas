import SlidingPuzzle.Hub.RunStep

/-! # Rounds of the run: structure

The events of a round (`roundEvs`, chosen by `exists_round_events`), the fold
of `hstep` over them (`runEvs`), one round (`runRound`, also counting the
round's dummy edges in `dd`) and the whole run (`runRounds`). Structural facts
that hold whatever the state: the insertions, weights, serve counters, and the
consistency of the insertion list with the plan order. -/
namespace SlidingPuzzle.Hub

open Finset

variable {k : ℕ}

/-- `1` if `S → D` is a real edge of the round. -/
def ind (r : Round k) (S D : Sq k) : ℕ := if r.perm S = D ∧ r.real S then 1 else 0

/-- `1` if `Z`'s edge is dummy in the round. -/
def dummyAt (r : Round k) (Z : Sq k) : ℕ := if r.isDummy Z then 1 else 0

/-- Budget of relocation weight of a round. -/
def roundW (r : Round k) : ℕ :=
  (3 * k ^ 2 + 6 * k) / 2 + 2 * k * (Finset.univ.filter fun S => r.isDummy S).card

/-- The events of a round. -/
noncomputable def roundEvs (r : Round k) (cur : Sq k) : List (HEvent k) :=
  Classical.choose (exists_round_events r cur)

theorem roundEvs_chain (r : Round k) (cur : Sq k) : HChain cur (roundEvs r cur) :=
  (Classical.choose_spec (exists_round_events r cur)).1

theorem roundEvs_count (r : Round k) (cur S D : Sq k) :
    (roundEvs r cur).count (.serve S D) = ind r S D :=
  (Classical.choose_spec (exists_round_events r cur)).2.1 S D

theorem roundEvs_weight (r : Round k) (cur : Sq k) :
    ((roundEvs r cur).map relocWeight).sum ≤ roundW r := by
  have := (Classical.choose_spec (exists_round_events r cur)).2.2
  unfold roundW
  change 2 * ((roundEvs r cur).map relocWeight).sum ≤ _ at this
  have e : 4 * k * (Finset.univ.filter fun S => r.isDummy S).card =
      2 * (2 * k * (Finset.univ.filter fun S => r.isDummy S).card) := by ring
  omega

/-- Process a list of events of round `τ`. -/
noncomputable def runEvs (s τ : ℕ) (G : GS k) (es : List (HEvent k)) : GS k :=
  es.foldl (hstep s τ) G

/-- One round. -/
noncomputable def runRound (s τ : ℕ) (r : Round k) (G : GS k) : GS k :=
  { runEvs s τ G (roundEvs r G.σ.blank) with
    dd := fun Z => (runEvs s τ G (roundEvs r G.σ.blank)).dd Z + dummyAt r Z }

/-- The first `m` rounds. -/
noncomputable def runRounds (s : ℕ) (rd : ℕ → Round k) : ℕ → GS k → GS k
  | 0, G => G
  | m + 1, G => runRound s m (rd m) (runRounds s rd m G)

/-- Serves into `Z`. -/
def cntIn (es : List (HEvent k)) (Z : Sq k) : ℕ := ∑ S, es.count (.serve S Z)

/-- Serves from `Z`. -/
def cntOut (es : List (HEvent k)) (Z : Sq k) : ℕ := ∑ D, es.count (.serve Z D)

section structural

variable (s τ : ℕ)

theorem count_cons_serve (S D S' D' : Sq k) (l : List (HEvent k)) :
    (HEvent.serve S D :: l).count (.serve S' D') =
      l.count (.serve S' D') + if S' = S ∧ D' = D then 1 else 0 := by
  rw [List.count_cons]
  congr 1
  by_cases h : S' = S ∧ D' = D
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [if_neg h, if_neg]
    simp only [beq_iff_eq, HEvent.serve.injEq]
    tauto

theorem count_cons_reloc (E Z S' D' : Sq k) (l : List (HEvent k)) :
    (HEvent.reloc E Z :: l).count (.serve S' D') = l.count (.serve S' D') := by
  rw [List.count_cons]; simp

theorem cntIn_cons_serve (S D Z : Sq k) (l : List (HEvent k)) :
    cntIn (.serve S D :: l) Z = cntIn l Z + if Z = D then 1 else 0 := by
  unfold cntIn
  simp only [count_cons_serve, sum_add_distrib]
  congr 1
  by_cases h : Z = D
  · subst h; simp
  · simp [h]

theorem cntOut_cons_serve (S D Z : Sq k) (l : List (HEvent k)) :
    cntOut (.serve S D :: l) Z = cntOut l Z + if Z = S then 1 else 0 := by
  unfold cntOut
  simp only [count_cons_serve, sum_add_distrib]
  congr 1
  by_cases h : Z = S
  · subst h; simp
  · simp [h]

theorem cntIn_cons_reloc (E Z' Z : Sq k) (l : List (HEvent k)) :
    cntIn (.reloc E Z' :: l) Z = cntIn l Z := by
  unfold cntIn; simp only [count_cons_reloc]

theorem cntOut_cons_reloc (E Z' Z : Sq k) (l : List (HEvent k)) :
    cntOut (.reloc E Z' :: l) Z = cntOut l Z := by
  unfold cntOut; simp only [count_cons_reloc]

theorem hstep_blank (G : GS k) (e : HEvent k) : (hstep s τ G e).σ.blank = hNext e := by
  cases e with
  | serve S D => exact hServe_blank τ G S D
  | reloc E Z => exact (hReloc_same G E Z).2.2.2.2.2.2.2.2.2

theorem hstep_ins (G : GS k) (e : HEvent k) :
    (hstep s τ G e).ins = G.ins ++ (hIns τ e).toList := by
  cases e with
  | serve S D => exact hServe_ins τ G S D
  | reloc E Z => simp [hstep, (hReloc_same G E Z).2.2.2.2.1, hIns]

theorem hstep_wt (G : GS k) (e : HEvent k) : (hstep s τ G e).wt = G.wt + relocWeight e := by
  cases e with
  | serve S D => simp [hstep, (hServe_rest (s := s) τ G S D).2.2.1, relocWeight]
  | reloc E Z => rfl

theorem hstep_dd (G : GS k) (e : HEvent k) : (hstep s τ G e).dd = G.dd := by
  cases e with
  | serve S D => exact (hServe_rest (s := s) τ G S D).2.2.2
  | reloc E Z => exact (hReloc_same G E Z).2.2.2.2.2.2.2.2.1

theorem runEvs_cons (G : GS k) (e : HEvent k) (l : List (HEvent k)) :
    runEvs s τ G (e :: l) = runEvs s τ (hstep s τ G e) l := rfl

theorem runEvs_ins (G : GS k) (l : List (HEvent k)) :
    (runEvs s τ G l).ins = G.ins ++ l.filterMap (hIns τ) := by
  induction l generalizing G with
  | nil => simp [runEvs]
  | cons e l ih =>
    rw [runEvs_cons, ih, hstep_ins, List.filterMap_cons]
    cases hIns τ e <;> simp

theorem runEvs_wt (G : GS k) (l : List (HEvent k)) :
    (runEvs s τ G l).wt = G.wt + (l.map relocWeight).sum := by
  induction l generalizing G with
  | nil => simp [runEvs]
  | cons e l ih =>
    rw [runEvs_cons, ih, hstep_wt]
    simp; ring

theorem runEvs_dd (G : GS k) (l : List (HEvent k)) : (runEvs s τ G l).dd = G.dd := by
  induction l generalizing G with
  | nil => rfl
  | cons e l ih => rw [runEvs_cons, ih, hstep_dd]

theorem runRound_ins (r : Round k) (G : GS k) :
    (runRound s τ r G).ins = G.ins ++ (roundEvs r G.σ.blank).filterMap (hIns τ) :=
  runEvs_ins s τ G _

theorem runRound_wt (r : Round k) (G : GS k) : (runRound s τ r G).wt ≤ G.wt + roundW r := by
  show (runEvs s τ G _).wt ≤ _
  rw [runEvs_wt]
  have := roundEvs_weight r G.σ.blank
  omega

theorem runRounds_ins_prefix (rd : ℕ → Round k) (G : GS k) {m m' : ℕ} (h : m ≤ m') :
    (runRounds s rd m G).ins <+: (runRounds s rd m' G).ins := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih =>
    refine ih.trans ?_
    show _ <+: (runRound s _ _ _).ins
    rw [runRound_ins]
    exact List.prefix_append _ _

end structural

/-! ## The insertion list is consistent with the plan order -/

section consistent

/-- Source of the insertion of a serve. -/
def srcP : HEvent k → Option (Sq k)
  | .serve S D => if S.2 = D.2 then none else some S
  | .reloc _ _ => none

theorem perm_roundIns (r : Round k) (es : List (HEvent k))
    (hc : ∀ S D, es.count (.serve S D) = ind r S D) (τ : ℕ) :
    ((es.filterMap (hIns τ)).map fun x => (x.H, x.d, x.x)).Perm (roundIns r) := by
  set g : Sq k → RowH k × ℕ × Sq k := fun S =>
    (hop1Half S (S.1, (r.perm S).2), hop1Dist S (S.1, (r.perm S).2), r.perm S) with hg
  have hmem : ∀ S D, HEvent.serve S D ∈ es → r.perm S = D ∧ r.real S := by
    intro S D hm
    have h1 := List.count_pos_iff.2 hm
    rw [hc] at h1
    unfold ind at h1
    split_ifs at h1 with h
    · exact h
    · omega
  have step1 : (es.filterMap (hIns τ)).map (fun x => (x.H, x.d, x.x)) =
      (es.filterMap srcP).map g := by
    rw [List.map_filterMap, List.map_filterMap]
    refine List.filterMap_congr fun e he => ?_
    cases e with
    | serve S D =>
      obtain ⟨rfl, -⟩ := hmem S _ he
      simp only [hIns, srcP]
      split_ifs <;> rfl
    | reloc E Z => rfl
  rw [step1]
  unfold roundIns
  refine List.Perm.map g ?_
  rw [List.perm_iff_count]
  intro S
  rw [List.Nodup.count (Finset.nodup_toList _), List.count_filterMap]
  have : List.countP (fun a => srcP a == some S) es =
      List.countP (fun a => a == HEvent.serve S (r.perm S) && decide (S.2 ≠ (r.perm S).2)) es := by
    refine List.countP_congr fun e he => ?_
    cases e with
    | serve S' D =>
      obtain ⟨rfl, -⟩ := hmem S' _ he
      simp only [srcP, beq_iff_eq, HEvent.serve.injEq, Bool.and_eq_true, decide_eq_true_eq]
      split_ifs with h1
      · simp only [false_iff, not_and, not_not]
        rintro ⟨rfl, -⟩; exact h1
      · simp only [Option.some.injEq]
        constructor
        · rintro rfl; exact ⟨⟨rfl, rfl⟩, h1⟩
        · rintro ⟨⟨rfl, -⟩, -⟩; rfl
    | reloc E Z => simp only [srcP]; simp
  rw [this]
  by_cases h2 : S.2 ≠ (r.perm S).2
  · have hd : decide (S.2 ≠ (r.perm S).2) = true := decide_eq_true h2
    simp only [hd, Bool.and_true]
    rw [← List.count, hc]
    unfold ind
    simp [Finset.mem_toList, h2]
  · have hd : decide (S.2 ≠ (r.perm S).2) = false := decide_eq_false h2
    simp only [hd, Bool.and_false, List.countP_false]
    simp [Finset.mem_toList, h2]

variable (s : ℕ) (rd : ℕ → Round k)

theorem runRounds_consistent (G : GS k) (hG : G.ins = []) (m : ℕ) :
    (∀ x ∈ (runRounds s rd m G).ins, x.τ < m) ∧
      (runRounds s rd m G).ins.Pairwise (fun a b => a.τ ≤ b.τ) ∧
      ∀ τ < m, ((((runRounds s rd m G).ins.filter fun x => x.τ = τ).map
        fun x => (x.H, x.d, x.x))).Perm (roundIns (rd τ)) := by
  induction m with
  | zero => simp [runRounds, hG]
  | succ m ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    have hins : (runRounds s rd (m + 1) G).ins = (runRounds s rd m G).ins ++
        (roundEvs (rd m) (runRounds s rd m G).σ.blank).filterMap (hIns m) :=
      runRound_ins s m (rd m) _
    set A := (runRounds s rd m G).ins
    set B := (roundEvs (rd m) (runRounds s rd m G).σ.blank).filterMap (hIns m)
    have hB : ∀ x ∈ B, x.τ = m := by
      intro x hx
      obtain ⟨e, -, he⟩ := List.mem_filterMap.1 hx
      cases e with
      | serve S D =>
        simp only [hIns] at he
        split_ifs at he
        cases he; rfl
      | reloc E Z => simp [hIns] at he
    rw [hins]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.1 hx with h | h
      · have := i1 x h; omega
      · rw [hB x h]; omega
    · rw [List.pairwise_append]
      refine ⟨i2, ?_, ?_⟩
      · exact List.pairwise_of_forall_mem_list fun a ha b hb => by rw [hB a ha, hB b hb]
      · intro a ha b hb; have := i1 a ha; rw [hB b hb]; omega
    · intro τ hτ
      rw [List.filter_append]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hτ with h | rfl
      · have : B.filter (fun x => decide (x.τ = τ)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx; rw [hB x hx]; simp; omega
        rw [this, List.append_nil]
        exact i3 τ h
      · have h1 : A.filter (fun x => decide (x.τ = τ)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx; have := i1 x hx; simp; omega
        have h2 : B.filter (fun x => decide (x.τ = τ)) = B := by
          rw [List.filter_eq_self]
          intro x hx; simp [hB x hx]
        rw [h1, h2, List.nil_append]
        exact perm_roundIns _ _ (roundEvs_count _ _) _

end consistent

end SlidingPuzzle.Hub
