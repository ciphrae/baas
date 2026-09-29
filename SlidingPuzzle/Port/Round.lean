import SlidingPuzzle.Port.Reloc
import SlidingPuzzle.Tree.RunRound

/-! # Events and rounds of the port run

As `Tree.RunRound`, with `pServe` and `pReloc`. The insertion records are those of
the tree run: one per stage of every served route. -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle.Hub (Sq sqDist HEvent relocWeight Round bump roundEvs ind dummyAt roundW
  roundEvs_count roundEvs_chain roundEvs_weight HChain)
open SlidingPuzzle.Tree

variable {k q : ℕ} (L : LaneSys k q)

/-- One high-level event of round `τ`. -/
noncomputable def phstep (s σ' τ : ℕ) (G : PG k q) : HEvent k → PG k q
  | .serve S D => { pServe L s τ G S D with served := bump G.served D, sent := bump G.sent S }
  | .reloc E Z => { pReloc L s σ' G E Z with wt := G.wt + relocWeight (HEvent.reloc E Z) }

/-- The events of a round. -/
noncomputable def prunEvs (s σ' τ : ℕ) (G : PG k q) (es : List (HEvent k)) : PG k q :=
  es.foldl (phstep L s σ' τ) G

/-- One round. -/
noncomputable def prunRound (s σ' τ : ℕ) (r : Round k) (G : PG k q) : PG k q :=
  prunEvs L s σ' τ G (roundEvs r G.σ.blank)

/-- The first `m` rounds. -/
noncomputable def prunRounds (s σ' : ℕ) (rd : ℕ → Round k) : ℕ → PG k q → PG k q
  | 0, G => G
  | m + 1, G => prunRound L s σ' m (rd m) (prunRounds s σ' rd m G)

theorem pGates_ins (s τ : ℕ) (G : PG k q) (D : Sq k) :
    ∀ w, ∃ R, (pGates L s τ G w D).ins = G.ins ++ R ∧
      R.map toRes = (L.edgeIns w D).reverse.map (resRec τ) := by
  intro w
  induction hr : L.srank w D generalizing w with
  | zero =>
    rw [srank_eq_zero hr, pGates_self]
    refine ⟨[], by simp, ?_⟩
    unfold LaneSys.edgeIns; rw [nodes_self]; rfl
  | succ r ih =>
    have hne : w ≠ D := fun e => by rw [e, srank_self] at hr; omega
    have := srank_nxt (L := L) hne
    obtain ⟨R, hR, hRm⟩ := ih (L.nxt w D) (by omega)
    rw [pGates_cons L s τ G hne]
    unfold pGate
    split_ifs
    · refine ⟨R ++ [_], by rw [pStep_ins, hR, List.append_assoc], ?_⟩
      rw [edgeIns_cons L hne, List.reverse_cons, List.map_append, List.map_append, hRm]; rfl
    · refine ⟨R ++ [_], by rw [pStep_ins, hR, List.append_assoc], ?_⟩
      rw [edgeIns_cons L hne, List.reverse_cons, List.map_append, List.map_append, hRm]; rfl

theorem pServe_ins (s τ : ℕ) (G : PG k q) {S D : Sq k} (hSD : S ≠ D) :
    ∃ R, (pServe L s τ G S D).ins = G.ins ++ R ∧
      R.map toRes = (L.edgeIns S D).reverse.map (resRec τ) := by
  obtain ⟨R, hR, hRm⟩ := pGates_ins L s τ G D (L.nxt S D)
  refine ⟨R ++ [_], by unfold pServe; rw [pStep_ins, hR, List.append_assoc], ?_⟩
  rw [edgeIns_cons L hSD, List.reverse_cons, List.map_append, List.map_append, hRm]; rfl

theorem phstep_ins (s σ' τ : ℕ) (G : PG k q) (e : HEvent k)
    (he : ∀ S D, e = .serve S D → S ≠ D) :
    ∃ R, (phstep L s σ' τ G e).ins = G.ins ++ R ∧ R.map toRes = (evRecs L e).map (resRec τ) := by
  cases e with
  | serve S D =>
    obtain ⟨R, hR, hRm⟩ := pServe_ins L s τ G (he S D rfl)
    exact ⟨R, hR, hRm⟩
  | reloc E Z =>
    refine ⟨[], ?_, rfl⟩
    show (pReloc L s σ' G E Z).ins = G.ins ++ []
    rw [(pReloc_same L G E Z).1.ins, List.append_nil]

theorem prunEvs_ins (s σ' τ : ℕ) (es : List (HEvent k))
    (he : ∀ S D, HEvent.serve S D ∈ es → S ≠ D) (G : PG k q) :
    ∃ R, (prunEvs L s σ' τ G es).ins = G.ins ++ R ∧
      R.map toRes = (es.flatMap (evRecs L)).map (resRec τ) := by
  induction es generalizing G with
  | nil => exact ⟨[], by simp [prunEvs], rfl⟩
  | cons e es ih =>
    obtain ⟨R1, h1, m1⟩ := phstep_ins L s σ' τ G e
      (fun S D h => he S D (h ▸ List.mem_cons_self))
    obtain ⟨R2, h2, m2⟩ := ih (fun S D h => he S D (List.mem_cons_of_mem _ h))
      (phstep L s σ' τ G e)
    refine ⟨R1 ++ R2, ?_, ?_⟩
    · show (prunEvs L s σ' τ (phstep L s σ' τ G e) es).ins = _
      rw [h2, h1, List.append_assoc]
    · rw [List.map_append, m1, m2, List.flatMap_cons, List.map_append]

theorem prunRound_ins (s σ' τ : ℕ) (r : Round k) (G : PG k q) :
    ∃ R, (prunRound L s σ' τ r G).ins = G.ins ++ R ∧
      R.map toRes = ((roundEvs r G.σ.blank).flatMap (evRecs L)).map (resRec τ) :=
  prunEvs_ins L s σ' τ _ (serve_ne_of_count (roundEvs_count r G.σ.blank)) G

theorem prunRounds_ins_prefix (s σ' : ℕ) (rd : ℕ → Round k) (G : PG k q) {m m' : ℕ}
    (h : m ≤ m') : (prunRounds L s σ' rd m G).ins <+: (prunRounds L s σ' rd m' G).ins := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih =>
    refine ih.trans ?_
    obtain ⟨R, hR, -⟩ := prunRound_ins L s σ' _ (rd _) (prunRounds L s σ' rd _ G)
    show _ <+: (prunRound L s σ' _ _ _).ins
    rw [hR]; exact List.prefix_append _ _

theorem prunRounds_consistent (s σ' : ℕ) (rd : ℕ → Round k) (G : PG k q) (hG : G.ins = [])
    (m : ℕ) :
    (∀ x ∈ (prunRounds L s σ' rd m G).ins.map toRes, x.τ < m) ∧
      ((prunRounds L s σ' rd m G).ins.map toRes).Pairwise (fun a b => a.τ ≤ b.τ) ∧
      ∀ τ < m, ((((prunRounds L s σ' rd m G).ins.map toRes).filter fun x => x.τ = τ).map
        GroupedPipe.proj).Perm (roundIns L (rd τ)) := by
  induction m with
  | zero => simp [prunRounds, hG]
  | succ m ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    obtain ⟨R, hR, hRm⟩ := prunRound_ins L s σ' m (rd m) (prunRounds L s σ' rd m G)
    have hins : (prunRounds L s σ' rd (m + 1) G).ins.map toRes =
        (prunRounds L s σ' rd m G).ins.map toRes ++
          ((roundEvs (rd m) (prunRounds L s σ' rd m G).σ.blank).flatMap (evRecs L)).map
            (resRec m) := by
      show (prunRound L s σ' m (rd m) (prunRounds L s σ' rd m G)).ins.map toRes = _
      rw [hR, List.map_append, hRm]
    set A := (prunRounds L s σ' rd m G).ins.map toRes
    set B := ((roundEvs (rd m) (prunRounds L s σ' rd m G).σ.blank).flatMap (evRecs L)).map
      (resRec m)
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
            (roundEvs (rd τ) (prunRounds L s σ' rd τ G).σ.blank).flatMap (evRecs L) := by
          simp only [B, List.map_map]
          exact List.map_id' _
        rw [e]
        exact perm_roundRecs L _ _ (roundEvs_count _ _)

end SlidingPuzzle.Port
