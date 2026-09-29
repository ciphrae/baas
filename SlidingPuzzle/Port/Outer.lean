import SlidingPuzzle.Port.Inv
import SlidingPuzzle.Tree.RunOuter

/-! # Invariants along the rounds of the port run -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle.Hub (Sq sqDist HEvent relocWeight Round bump roundEvs ind dummyAt roundW
  roundEvs_count roundEvs_chain roundEvs_weight HChain cntIn cntOut count_cons_serve
  count_cons_reloc cntIn_cons_serve cntOut_cons_serve cntIn_cons_reloc cntOut_cons_reloc
  real_add_dummy_le sum_ind_left sum_ind_right cntOut_le)
open SlidingPuzzle.Tree

variable {k q : ℕ} (L : LaneSys k q)

/-- Invariant between the events of round `m`; `rem` are the remaining events. -/
structure PInner (c : PCtx k q) (m : ℕ) (G : PG k q) (rem : List (HEvent k)) : Prop where
  lt : m < c.Δ
  lin : PLInv L c.s c.σ' c.σ0 c.F0 G
  hin : PHInv L c G
  chain : HChain G.σ.blank rem
  cnt_le : ∀ S D, rem.count (.serve S D) ≤ ind (c.rd m) S D
  sched : ∀ S D, G.sched S D = (∑ τ ∈ Ico (m + 1) c.Δ, ind (c.rd τ) S D) + rem.count (.serve S D)
  bal : ∀ Z, G.served Z + cntIn rem Z ≤ G.sent Z + cntOut rem Z +
    (∑ τ ∈ range m, dummyAt (c.rd τ) Z) + dummyAt (c.rd m) Z
  wt : G.wt + (rem.map relocWeight).sum ≤ (∑ τ ∈ range m, roundW (c.rd τ)) + roundW (c.rd m)

/-- Invariant between rounds (`m` rounds done). -/
structure POuter (c : PCtx k q) (m : ℕ) (G : PG k q) : Prop where
  le : m ≤ c.Δ
  lin : PLInv L c.s c.σ' c.σ0 c.F0 G
  hin : PHInv L c G
  sched : ∀ S D, G.sched S D = ∑ τ ∈ Ico m c.Δ, ind (c.rd τ) S D
  bal : ∀ Z, G.served Z ≤ G.sent Z + ∑ τ ∈ range m, dummyAt (c.rd τ) Z
  wt : G.wt ≤ ∑ τ ∈ range m, roundW (c.rd τ)

section inner

variable {c : PCtx k q} (hc : c.OK L) {n : ℕ} [NeZero n] (td : TDims n k c.s q)

include hc in
theorem PInner.free_pos {m : ℕ} {G : PG k q} {rem : List (HEvent k)} (hI : PInner L c m G rem)
    (Q : Sq k) (hQ : Q ≠ G.σ.blank) : 1 ≤ pfr G Q := by
  have h1 := hI.hin.free_lo Q
  have h2 := hI.bal Q
  have h3 := cntOut_le hI.cnt_le Q
  have h4 := real_add_dummy_le (c.rd m) Q
  have h5 : (∑ τ ∈ range m, dummyAt (c.rd τ) Q) + dummyAt (c.rd m) Q ≤ c.dmax Q := by
    rw [← sum_range_succ]
    refine le_trans ?_ (hc.dmax Q)
    exact sum_le_sum_of_subset (range_subset_range.2 hI.lt)
  have h6 := psB_le L hI.hin Q
  have h7 := hc.free0 (by have := hI.lt; omega) Q
  rw [if_neg (Ne.symm hQ)] at h1
  have h8 : (if c.σ0.blank = Q then 1 else 0) ≥ 0 := Nat.zero_le _
  omega

include hc td in
theorem PInner.step {m : ℕ} {G : PG k q} {e : HEvent k} {rest : List (HEvent k)}
    (hI : PInner L c m G (e :: rest)) (hpre : (phstep L c.s c.σ' m G e).ins <+: c.Lfin) :
    PInner L c m (phstep L c.s c.σ' m G e) rest := by
  cases e with
  | serve S D =>
    have hch := hI.chain
    simp only [HChain] at hch
    obtain ⟨hb, hrest⟩ := hch
    have hcnt := hI.cnt_le S D
    rw [count_cons_serve] at hcnt
    simp only [and_self, if_true] at hcnt
    have hedge : (c.rd m).perm S = D ∧ (c.rd m).real S := by
      unfold ind at hcnt; split_ifs at hcnt with h
      · exact h
      · omega
    have hne : S ≠ D := by
      intro e; exact hedge.2.1 (hedge.1.trans e.symm)
    have hsch := hI.sched S D
    rw [count_cons_serve] at hsch
    simp only [and_self, if_true] at hsch
    obtain ⟨hL', hH'⟩ := phstep_serve L hc td hI.lin hI.hin m hb hne (by omega)
      (hI.free_pos L hc) hpre
    have hS := pServe_inv L td m c.Nv hc.cap hI.lin hne hb (hI.hin.identD L D) hI.hin.dirty
      hI.hin.binv c.Lfin hc.Fb (by omega)
      (fun u hu => hI.free_pos L hc u (by rw [hb]; exact (mem_nodes L hu).1)) hpre
    refine ⟨hI.lt, hL', hH', ?_, ?_, ?_, ?_, ?_⟩
    · show HChain (pServe L c.s m G S D).σ.blank rest
      rw [hS.blank]; exact hrest
    · intro S' D'
      have := hI.cnt_le S' D'
      rw [count_cons_serve] at this
      omega
    · intro S' D'
      have := hI.sched S' D'
      rw [count_cons_serve] at this
      show (pServe L c.s m G S D).sched S' D' = _
      rw [hS.sched]
      split_ifs at this ⊢ <;> omega
    · intro Z
      have := hI.bal Z
      rw [cntIn_cons_serve, cntOut_cons_serve] at this
      show bump G.served D Z + cntIn rest Z ≤ bump G.sent S Z + cntOut rest Z +
        (∑ τ ∈ range m, dummyAt (c.rd τ) Z) + dummyAt (c.rd m) Z
      simp only [bump]
      omega
    · have := hI.wt
      simp only [List.map_cons, List.sum_cons, relocWeight] at this
      show (pServe L c.s m G S D).wt + _ ≤ _
      rw [hS.wt]; omega
  | reloc E Z =>
    have hch := hI.chain
    simp only [HChain] at hch
    obtain ⟨hb, hEZ, hrest⟩ := hch
    obtain ⟨hL', hH'⟩ := phstep_reloc L hc td hI.lin hI.hin m hb hEZ (hI.free_pos L hc)
    obtain ⟨r, rb, -⟩ := pReloc_same L (s := c.s) (σ' := c.σ') G E Z
    refine ⟨hI.lt, hL', hH', ?_, ?_, ?_, ?_, ?_⟩
    · show HChain (pReloc L c.s c.σ' G E Z).σ.blank rest
      rw [rb]; exact hrest
    · intro S' D'
      have := hI.cnt_le S' D'
      rwa [count_cons_reloc] at this
    · intro S' D'
      have := hI.sched S' D'
      rw [count_cons_reloc] at this
      show (pReloc L c.s c.σ' G E Z).sched S' D' = _
      rw [r.sched]; exact this
    · intro Q
      have := hI.bal Q
      rw [cntIn_cons_reloc, cntOut_cons_reloc] at this
      show (pReloc L c.s c.σ' G E Z).served Q + cntIn rest Q ≤
        (pReloc L c.s c.σ' G E Z).sent Q + cntOut rest Q +
        (∑ τ ∈ range m, dummyAt (c.rd τ) Q) + dummyAt (c.rd m) Q
      rw [r.served, r.sent]; exact this
    · have := hI.wt
      simp only [List.map_cons, List.sum_cons] at this
      show G.wt + relocWeight (HEvent.reloc E Z) + (rest.map relocWeight).sum ≤
        (∑ τ ∈ range m, roundW (c.rd τ)) + roundW (c.rd m)
      omega

include hc td in
theorem PInner.run {m : ℕ} : ∀ (rem : List (HEvent k)) (G : PG k q), PInner L c m G rem →
    (prunEvs L c.s c.σ' m G rem).ins <+: c.Lfin → PInner L c m (prunEvs L c.s c.σ' m G rem) []
  | [], G, hI, _ => hI
  | e :: rest, G, hI, hpre => by
    have hG : (phstep L c.s c.σ' m G e).ins <+: c.Lfin := by
      refine List.IsPrefix.trans ?_ hpre
      show (phstep L c.s c.σ' m G e).ins <+: (prunEvs L c.s c.σ' m (phstep L c.s c.σ' m G e) rest).ins
      have hne : ∀ S D, HEvent.serve S D ∈ rest → S ≠ D := by
        intro S D hm
        have h1 := hI.cnt_le S D
        have h2 : 0 < (e :: rest).count (.serve S D) :=
          List.count_pos_iff.2 (List.mem_cons_of_mem _ hm)
        unfold ind at h1
        split_ifs at h1 with h
        · intro e; exact h.2.1 (h.1.trans e.symm)
        · omega
      obtain ⟨R, hR, -⟩ := prunEvs_ins L c.s c.σ' m rest hne (phstep L c.s c.σ' m G e)
      rw [hR]; exact List.prefix_append _ _
    exact PInner.run rest _ (hI.step L hc td hG) hpre

theorem POuter.start {m : ℕ} {G : PG k q} (hO : POuter L c m G) (hm : m < c.Δ) :
    PInner L c m G (roundEvs (c.rd m) G.σ.blank) := by
  refine ⟨hm, hO.lin, hO.hin, roundEvs_chain _ _, ?_, ?_, ?_, ?_⟩
  · intro S D; rw [roundEvs_count]
  · intro S D
    rw [hO.sched, roundEvs_count, Finset.sum_eq_sum_Ico_succ_bot hm]
    ring
  · intro Z
    have h1 := hO.bal Z
    have h2 : cntIn (roundEvs (c.rd m) G.σ.blank) Z = ∑ S, ind (c.rd m) S Z := by
      unfold cntIn; simp only [roundEvs_count]
    have h3 : cntOut (roundEvs (c.rd m) G.σ.blank) Z = if (c.rd m).real Z then 1 else 0 := by
      unfold cntOut; simp only [roundEvs_count]; exact sum_ind_left _ _
    have h4 := sum_ind_right (c.rd m) Z
    omega
  · have := hO.wt
    have := roundEvs_weight (c.rd m) G.σ.blank
    omega

include hc td in
theorem POuter.round {m : ℕ} {G : PG k q} (hO : POuter L c m G) (hm : m < c.Δ)
    (hpre : (prunRound L c.s c.σ' m (c.rd m) G).ins <+: c.Lfin) :
    POuter L c (m + 1) (prunRound L c.s c.σ' m (c.rd m) G) := by
  have hI := PInner.run L hc td _ _ (hO.start L hm) hpre
  refine ⟨hm, hI.lin, hI.hin, ?_, ?_, ?_⟩
  · intro S D
    have := hI.sched S D
    simpa [prunRound] using this
  · intro Z
    have := hI.bal Z
    simp only [cntIn, cntOut, List.count_nil, sum_const_zero, add_zero] at this
    rw [sum_range_succ]
    unfold prunRound
    omega
  · have := hI.wt
    simp only [List.map_nil, List.sum_nil, add_zero] at this
    rw [sum_range_succ]; unfold prunRound; exact this

include hc td in
theorem POuter.all {G : PG k q} (h0 : POuter L c 0 G)
    (hL : c.Lfin = (prunRounds L c.s c.σ' c.rd c.Δ G).ins) :
    ∀ m ≤ c.Δ, POuter L c m (prunRounds L c.s c.σ' c.rd m G) := by
  intro m hm
  induction m with
  | zero => exact h0
  | succ m ih =>
    have hO := ih (by omega)
    refine hO.round L hc td (by omega) ?_
    rw [hL]
    exact prunRounds_ins_prefix L c.s c.σ' c.rd G hm

end inner

end SlidingPuzzle.Port
