import SlidingPuzzle.Tree.RunReloc
import SlidingPuzzle.Hub.RunRound

/-! # Events and rounds of the run

`hstep` resolves a high-level event (a serve along the whole route, or a
relocation), `runEvs` folds it over the events of a round, `runRounds` over the
rounds. The insertion records of a round are, up to order, the route records of
its real edges: a fixed function of the round, which is what the residence bound
needs. -/
namespace SlidingPuzzle.Tree
open Finset
open SlidingPuzzle.Hub (Sq sqDist HEvent relocWeight Round bump roundEvs ind dummyAt roundW
  roundEvs_count roundEvs_chain roundEvs_weight HChain)

variable {k q : ℕ} (L : LaneSys k q)

/-- One high-level event of round `τ`. -/
noncomputable def hstep (s τ : ℕ) (G : GS k q) : HEvent k → GS k q
  | .serve S D => { hServe L s τ G S D with served := bump G.served D, sent := bump G.sent S }
  | .reloc E Z => { hReloc s G E Z with wt := G.wt + relocWeight (HEvent.reloc E Z) }

/-- The events of a round. -/
noncomputable def runEvs (s τ : ℕ) (G : GS k q) (es : List (HEvent k)) : GS k q :=
  es.foldl (hstep L s τ) G

/-- One round. -/
noncomputable def runRound (s τ : ℕ) (r : Round k) (G : GS k q) : GS k q :=
  runEvs L s τ G (roundEvs r G.σ.blank)

/-- The first `m` rounds. -/
noncomputable def runRounds (s : ℕ) (rd : ℕ → Round k) : ℕ → GS k q → GS k q
  | 0, G => G
  | m + 1, G => runRound L s m (rd m) (runRounds s rd m G)

/-! ## Insertion records -/

/-- The residence record of a ghost record (dropping the clean flag). -/
def toRes (r : GRec k q) : GroupedPipe.InsRec (Ln k q) (Sq k) := ⟨r.τ, r.H, r.d, r.x.1⟩

/-- A route record at time `τ`. -/
def resRec (τ : ℕ) (p : Ln k q × ℕ × Sq k) : GroupedPipe.InsRec (Ln k q) (Sq k) :=
  ⟨τ, p.1, p.2.1, p.2.2⟩

theorem edgeIns_cons {u x : Sq k} (h : u ≠ x) : L.edgeIns u x =
    ((L.stage u x).1, LaneSys.pdist (L.stage u x).1.2.t.val (L.stage u x).2.val, x) ::
      L.edgeIns (L.nxt u x) x := by
  unfold LaneSys.edgeIns; rw [nodes_cons L h]; rfl

theorem gStage_ins (s τ : ℕ) (G : GS k q) (u x : Sq k) (kd : Kind) (y : Sq k) :
    (gStage L s τ G u x kd y).ins = G.ins ++ [⟨τ, (L.stage u x).1,
      LaneSys.pdist (L.stage u x).1.2.t.val (L.stage u x).2.val, (x, decide (kd ≠ .plh))⟩] := rfl

theorem hGates_ins (s τ : ℕ) (G : GS k q) (D : Sq k) :
    ∀ w, ∃ R, (hGates L s τ G w D).ins = G.ins ++ R ∧
      R.map toRes = (L.edgeIns w D).reverse.map (resRec τ) := by
  intro w
  induction hr : L.srank w D generalizing w with
  | zero =>
    rw [srank_eq_zero hr, hGates_self]
    refine ⟨[], by simp, ?_⟩
    unfold LaneSys.edgeIns; rw [nodes_self]; rfl
  | succ r ih =>
    have hne : w ≠ D := fun e => by rw [e, srank_self] at hr; omega
    have := srank_nxt (L := L) hne
    obtain ⟨R, hR, hRm⟩ := ih (L.nxt w D) (by omega)
    rw [hGates_cons L s τ G hne]
    unfold gGate
    split_ifs
    · refine ⟨R ++ [_], by rw [gStage_ins, hR, List.append_assoc], ?_⟩
      rw [edgeIns_cons L hne, List.reverse_cons, List.map_append, List.map_append, hRm]; rfl
    · refine ⟨R ++ [_], by rw [gStage_ins, hR, List.append_assoc], ?_⟩
      rw [edgeIns_cons L hne, List.reverse_cons, List.map_append, List.map_append, hRm]; rfl

theorem hServe_ins (s τ : ℕ) (G : GS k q) {S D : Sq k} (hSD : S ≠ D) :
    ∃ R, (hServe L s τ G S D).ins = G.ins ++ R ∧
      R.map toRes = (L.edgeIns S D).reverse.map (resRec τ) := by
  obtain ⟨R, hR, hRm⟩ := hGates_ins L s τ G D (L.nxt S D)
  refine ⟨R ++ [_], by unfold hServe; rw [gStage_ins, hR, List.append_assoc], ?_⟩
  rw [edgeIns_cons L hSD, List.reverse_cons, List.map_append, List.map_append, hRm]; rfl

/-- Records of an event. -/
def evRecs : HEvent k → List (Ln k q × ℕ × Sq k)
  | .serve S D => (L.edgeIns S D).reverse
  | .reloc _ _ => []

theorem hstep_ins (s τ : ℕ) (G : GS k q) (e : HEvent k) (he : ∀ S D, e = .serve S D → S ≠ D) :
    ∃ R, (hstep L s τ G e).ins = G.ins ++ R ∧ R.map toRes = (evRecs L e).map (resRec τ) := by
  cases e with
  | serve S D =>
    obtain ⟨R, hR, hRm⟩ := hServe_ins L s τ G (he S D rfl)
    exact ⟨R, hR, hRm⟩
  | reloc E Z =>
    refine ⟨[], ?_, rfl⟩
    show (hReloc s G E Z).ins = G.ins ++ []
    rw [(hReloc_same G E Z).1, List.append_nil]

theorem runEvs_ins (s τ : ℕ) (es : List (HEvent k))
    (he : ∀ S D, HEvent.serve S D ∈ es → S ≠ D) (G : GS k q) :
    ∃ R, (runEvs L s τ G es).ins = G.ins ++ R ∧
      R.map toRes = (es.flatMap (evRecs L)).map (resRec τ) := by
  induction es generalizing G with
  | nil => exact ⟨[], by simp [runEvs], rfl⟩
  | cons e es ih =>
    obtain ⟨R1, h1, m1⟩ := hstep_ins L s τ G e (fun S D h => he S D (h ▸ List.mem_cons_self))
    obtain ⟨R2, h2, m2⟩ := ih (fun S D h => he S D (List.mem_cons_of_mem _ h)) (hstep L s τ G e)
    refine ⟨R1 ++ R2, ?_, ?_⟩
    · show (runEvs L s τ (hstep L s τ G e) es).ins = _
      rw [h2, h1, List.append_assoc]
    · rw [List.map_append, m1, m2, List.flatMap_cons, List.map_append]

/-- The route records of the real edges of a round. -/
noncomputable def roundIns (r : Round k) : List (Ln k q × ℕ × Sq k) :=
  ((Finset.univ.filter fun S => r.real S).toList).flatMap fun S => L.edgeIns S (r.perm S)

/-- Is the event a serve. -/
def isServe : HEvent k → Bool
  | .serve _ _ => true
  | .reloc _ _ => false

theorem flatMap_evRecs_filter (es : List (HEvent k)) :
    es.flatMap (evRecs L) = (es.filter isServe).flatMap (evRecs L) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | serve S D => simp only [List.flatMap_cons, List.filter_cons, isServe, if_true, ih]
    | reloc E Z =>
      simp only [List.flatMap_cons, List.filter_cons, isServe, Bool.false_eq_true, if_false, ih]
      rfl

theorem perm_roundRecs (r : Round k) (es : List (HEvent k))
    (hc : ∀ S D, es.count (.serve S D) = ind r S D) :
    (es.flatMap (evRecs L)).Perm (roundIns L r) := by
  classical
  set realL := (Finset.univ.filter fun S => r.real S).toList with hrealL
  have hnd : realL.Nodup := Finset.nodup_toList _
  set sv : Sq k → HEvent k := fun S => HEvent.serve S (r.perm S) with hsv
  have hinj : Function.Injective sv := by
    intro a b h; simp only [hsv, HEvent.serve.injEq] at h; exact h.1
  have hmemL : ∀ S, S ∈ realL ↔ r.real S := by
    intro S; simp [hrealL]
  -- the serves of the round
  have hS : (es.filter isServe).Perm (realL.map sv) := by
    rw [List.perm_iff_count]
    intro e
    cases e with
    | serve S D =>
      rw [List.count_filter (by rfl), hc S D]
      by_cases hD : r.perm S = D
      · subst hD
        rw [show HEvent.serve S (r.perm S) = sv S from rfl, List.count_map_of_injective _ _ hinj]
        unfold ind
        by_cases hm : S ∈ realL
        · rw [List.count_eq_one_of_mem hnd hm]; simp [(hmemL S).mp hm]
        · rw [List.count_eq_zero.mpr hm]; simp [← hmemL, hm]
      · rw [List.count_eq_zero.mpr]
        · unfold ind; simp [hD]
        · intro hm
          obtain ⟨S', -, hS'⟩ := List.mem_map.mp hm
          simp only [hsv, HEvent.serve.injEq] at hS'
          obtain ⟨rfl, rfl⟩ := hS'
          exact hD rfl
    | reloc E Z =>
      rw [List.count_eq_zero.mpr, List.count_eq_zero.mpr]
      · intro hm
        obtain ⟨S', -, hS'⟩ := List.mem_map.mp hm
        simp [hsv] at hS'
      · intro hm
        have := (List.mem_filter.mp hm).2
        simp [isServe] at this
  rw [flatMap_evRecs_filter L es]
  refine (List.Perm.flatMap_right _ hS).trans ?_
  unfold roundIns
  rw [List.flatMap_map]
  exact List.Perm.flatMap_left _ fun S _ => List.reverse_perm _

theorem serve_ne_of_count {r : Round k} {es : List (HEvent k)}
    (hc : ∀ S D, es.count (.serve S D) = ind r S D) :
    ∀ S D, HEvent.serve S D ∈ es → S ≠ D := by
  intro S D hm e
  have h1 := List.count_pos_iff.2 hm
  rw [hc] at h1
  unfold ind at h1
  split_ifs at h1 with h
  · exact h.2.1 (h.1.trans e.symm)
  · omega

theorem runRound_ins (s τ : ℕ) (r : Round k) (G : GS k q) :
    ∃ R, (runRound L s τ r G).ins = G.ins ++ R ∧
      R.map toRes = ((roundEvs r G.σ.blank).flatMap (evRecs L)).map (resRec τ) :=
  runEvs_ins L s τ _ (serve_ne_of_count (roundEvs_count r G.σ.blank)) G

theorem runRounds_ins_prefix (s : ℕ) (rd : ℕ → Round k) (G : GS k q) {m m' : ℕ} (h : m ≤ m') :
    (runRounds L s rd m G).ins <+: (runRounds L s rd m' G).ins := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih =>
    refine ih.trans ?_
    obtain ⟨R, hR, -⟩ := runRound_ins L s _ (rd _) (runRounds L s rd _ G)
    show _ <+: (runRound L s _ _ _).ins
    rw [hR]; exact List.prefix_append _ _

theorem runRounds_consistent (s : ℕ) (rd : ℕ → Round k) (G : GS k q) (hG : G.ins = [])
    (m : ℕ) :
    (∀ x ∈ (runRounds L s rd m G).ins.map toRes, x.τ < m) ∧
      ((runRounds L s rd m G).ins.map toRes).Pairwise (fun a b => a.τ ≤ b.τ) ∧
      ∀ τ < m, ((((runRounds L s rd m G).ins.map toRes).filter fun x => x.τ = τ).map
        GroupedPipe.proj).Perm (roundIns L (rd τ)) := by
  induction m with
  | zero => simp [runRounds, hG]
  | succ m ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    obtain ⟨R, hR, hRm⟩ := runRound_ins L s m (rd m) (runRounds L s rd m G)
    have hins : (runRounds L s rd (m + 1) G).ins.map toRes =
        (runRounds L s rd m G).ins.map toRes ++
          ((roundEvs (rd m) (runRounds L s rd m G).σ.blank).flatMap (evRecs L)).map (resRec m) := by
      show (runRound L s m (rd m) (runRounds L s rd m G)).ins.map toRes = _
      rw [hR, List.map_append, hRm]
    set A := (runRounds L s rd m G).ins.map toRes
    set B := ((roundEvs (rd m) (runRounds L s rd m G).σ.blank).flatMap (evRecs L)).map (resRec m)
    have hB : ∀ x ∈ B, x.τ = m := by
      intro x hx
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
      rfl
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
        have e : B.map GroupedPipe.proj =
            (roundEvs (rd τ) (runRounds L s rd τ G).σ.blank).flatMap (evRecs L) := by
          simp only [B, List.map_map]
          exact List.map_id' _
        rw [e]
        exact perm_roundRecs L _ _ (roundEvs_count _ _)

end SlidingPuzzle.Tree
