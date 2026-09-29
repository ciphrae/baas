import SlidingPuzzle.Port.GhostStage

/-! # The local invariant through transfers and legs -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle.Hub (Sq sqDist shiftIn incCnt decCnt)
open SlidingPuzzle.Tree

variable {k q : ℕ} (L : LaneSys k q)

/-- The mode an insertion would need to move port counts as a leg does. -/
def legMode (b : Pt) (p : Part) (z : Sq k) : Mode k := if p = some b then .cheap else .imp p z

theorem legPc_eq (f : Sq k → Pt → Sq k → ℕ) (Z : Sq k) (b : Pt) (y : Sq k) (p : Part) (z : Sq k) :
    PState.legPc f Z b y p z = PState.srcPc f Z b y (legMode b p z) := by
  rcases p with _ | p'
  · simp [PState.legPc, PState.srcPc, legMode]
  · by_cases h : p' = b
    · subst h; simp [PState.legPc, PState.srcPc, legMode]
    · simp [PState.legPc, PState.srcPc, legMode, h]

section ops
variable {s σ' : ℕ} {σ0 : PState k q} {F0 : ℕ}

theorem pXfer_linv {G : PG k q} (hL : PLInv L s σ' σ0 F0 G) {pt : Pt} {c : Sq k}
    (hne : G.σ.bp ≠ pt) (htl : G.σ.bp = .tl ∨ pt = .tl)
    (hc : dem L G G.σ.blank (some pt) c < G.σ.pc G.σ.blank pt c) :
    PLInv L s σ' σ0 F0 (pXfer s G pt c) := by
  have hpre : G.σ.Pre L (.xfer pt c) := ⟨hne, htl, by omega⟩
  obtain ⟨hrun, hval⟩ := ppre_append L hL hpre
  set Q0 := G.σ.blank
  set b := G.σ.bp
  have hpc : (pXfer s G pt c).σ.pc = incP (decP G.σ.pc Q0 pt c) Q0 b c := rfl
  have h1 : 1 ≤ G.σ.pc Q0 pt c := by omega
  refine ⟨hL.roles_le, hL.roles_ge, hL.stock_diag, hL.ghost_clean, hL.ghost_len, ?_, ?_, ?_,
    hrun, hval, ?_, hL.free_tot, hL.turn⟩
  · intro Q y
    show ∑ pt', incP (decP G.σ.pc Q0 pt c) Q0 b c Q pt' y ≤ G.σ.cnt Q y
    rw [sumPt_incP]
    have := sumPt_decP G.σ.pc Q0 pt c Q y h1
    have := hL.pc_le Q y
    omega
  · intro Q pt'
    show (∑ z, incP (decP G.σ.pc Q0 pt c) Q0 b c Q pt' z) +
      (if Q0 = Q ∧ pt = pt' then 1 else 0) = _
    rw [sumZ_incP, ← hL.psum Q pt']
    have := sumZ_decP G.σ.pc Q0 pt c Q pt' h1
    have e1 : (if Q0 = Q ∧ pt = pt' then 1 else 0) = (if Q = Q0 ∧ pt' = pt then 1 else 0) := by
      by_cases h : Q = Q0 ∧ pt' = pt
      · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
      · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]
    have e2 : (if G.σ.blank = Q ∧ G.σ.bp = pt' then 1 else 0) = (if Q = Q0 ∧ pt' = b then 1 else 0) := by
      by_cases h : Q = Q0 ∧ pt' = b
      · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
      · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]
    rw [e1, e2]
    omega
  · intro u x hux
    have h0 := hL.stockIn u x hux
    show G.stock u (dport L u x) x ≤ incP (decP G.σ.pc Q0 pt c) Q0 b c u (dport L u x) x
    rw [incP_apply, decP_apply]
    by_cases h : u = Q0 ∧ dport L u x = pt ∧ x = c
    · obtain ⟨hu, h2, hx⟩ := h
      rw [if_pos ⟨hu, h2, hx⟩]
      rw [← hu, ← hx] at hc
      have : dem L G u (some pt) x = G.stock u pt x := by
        show (if x ≠ u ∧ dport L u x = pt then G.stock u pt x else 0) = _
        rw [if_pos ⟨Ne.symm hux, h2⟩]
      rw [this] at hc
      rw [h2]
      omega
    · rw [if_neg h]; omega
  · have hc' := pcost_append L hL (.xfer pt c)
    have hL' := hL.cost
    show σ0.totalCost s σ' (G.evs ++ [.xfer pt c]) + (G.σ.step s (.xfer pt c)).pot L s ≤
      σ0.pot L s + hopKc k q σ' * G.nh + hopKi k s σ' * G.ni + xferK k s σ' * (G.nx + 1) +
        (k * s) * (∑ Q, ∑ x, G.B Q x) + G.jc
    rw [hc', pot_xfer]
    have : G.σ.cost s σ' (.xfer pt c) = xferK k s σ' := rfl
    rw [this, mul_add, mul_one]
    omega

theorem pLeg_linv {G : PG k q} (hL : PLInv L s σ' σ0 F0 G) {Z y : Sq k} {p : Part} {z : Sq k}
    (hEZ : G.σ.blank ≠ Z) (hal : G.σ.blank.1 = Z.1 ∨ G.σ.blank.2 = Z.2) (hf : 1 ≤ G.free Z y)
    (hy : dem L G Z p y < G.σ.partCnt Z p y)
    (hz : p ≠ some G.σ.bp → dem L G Z (some G.σ.bp) z < G.σ.pc Z G.σ.bp z) :
    PLInv L s σ' σ0 F0 (pLeg s σ' G Z y p z) := by
  set E := G.σ.blank with hE
  set b := G.σ.bp with hb
  set f := incP G.σ.pc E b y with hfdef
  have hfZ : ∀ pt w, f Z pt w = G.σ.pc Z pt w := fun pt w => by
    rw [hfdef, incP_apply, if_neg (fun h => hEZ h.1.symm), add_zero]
  have hpc : (pLeg s σ' G Z y p z).σ.pc = PState.srcPc f Z b y (legMode b p z) := by
    show PState.legPc f Z b y p z = _
    exact legPc_eq f Z b y p z
  have hsok : SrcOK f Z b y (legMode b p z) := by
    rcases p with _ | p'
    · show 1 ≤ f Z b z
      rw [hfZ]; have := hz (by simp); omega
    · by_cases h : p' = b
      · rw [show legMode b (some p') z = Mode.cheap by simp [legMode, h]]
        show 1 ≤ f Z b y
        rw [hfZ]; simp only [dem, PState.partCnt] at hy; rw [h] at hy; omega
      · rw [show legMode b (some p') z = Mode.imp (some p') z by simp [legMode, h]]
        refine ⟨h, ?_, ?_⟩
        · rw [hfZ]; simp only [dem, PState.partCnt] at hy; omega
        · rw [hfZ]; have := hz (by simp [h]); omega
  have hmain : p = none → (∑ pt, G.σ.pc Z pt y) + 1 ≤ G.σ.cnt Z y := by
    rintro rfl
    simp only [dem, PState.partCnt, PState.mcnt] at hy; omega
  have hpcZy : p ≠ none → 1 ≤ ∑ pt, G.σ.pc Z pt y := by
    intro hp
    obtain ⟨p', rfl⟩ := Option.ne_none_iff_exists'.mp hp
    simp only [dem, PState.partCnt] at hy
    exact le_trans (by omega) (Finset.single_le_sum (f := fun pt => G.σ.pc Z pt y)
      (fun _ _ => Nat.zero_le _) (mem_univ p'))
  have hcnt1 : 1 ≤ G.σ.cnt Z y := by have := hL.roles_le Z y; omega
  have hpre : G.σ.Pre L (.leg Z y p z) := by
    exact ⟨hEZ, hal, lt_of_le_of_lt (Nat.zero_le _) hy,
      fun h => lt_of_le_of_lt (Nat.zero_le _) (hz h)⟩
  obtain ⟨hrun, hval⟩ := ppre_append L hL hpre
  have hcnt : ∀ Q x, (pLeg s σ' G Z y p z).σ.cnt Q x = G.σ.cnt Q x -
      (if Q = Z ∧ x = y then 1 else 0) + (if Q = E ∧ x = y then 1 else 0) := by
    intro Q x; simp only [pLeg, PState.step, Hub.incCnt_apply, Hub.decCnt_apply]; rfl
  have hZ : ∀ Q x, (if Q = Z ∧ x = y then 1 else 0) ≤ G.free Q x := by
    intro Q x; split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; exact hf
    · exact Nat.zero_le _
  have hZc : ∀ Q x, (if Q = Z ∧ x = y then 1 else 0) ≤ G.σ.cnt Q x := by
    intro Q x; split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; exact hcnt1
    · exact Nat.zero_le _
  have hfree : ∀ Q x, (pLeg s σ' G Z y p z).free Q x = G.free Q x -
      (if Q = Z ∧ x = y then 1 else 0) + (if Q = E ∧ x = y then 1 else 0) := fun _ _ => rfl
  have hmout : Mode.out y (legMode b p z) = if p = none then z else y := by
    rcases p with _ | p'
    · rfl
    · by_cases h : p' = b
      · subst h; simp [legMode, Mode.out]
      · simp [legMode, Mode.out, h]
  refine ⟨?_, ?_, hL.stock_diag, ?_, ?_, ?_, ?_, ?_, hrun, hval, ?_, ?_, hL.turn⟩
  · intro Q x
    rw [hcnt, hfree]
    have := hL.roles_le Q x; have := hZ Q x
    show G.sched Q x + G.stk Q x + _ ≤ _
    omega
  · intro Q x hx
    rw [hcnt, hfree]
    have := hL.roles_ge Q x hx; have := hZ Q x; have := hZc Q x
    show _ ≤ G.sched Q x + G.stk Q x + _
    omega
  · intro l r x d h; exact hL.ghost_clean l r x d h
  · intro l r h; exact hL.ghost_len l r h
  · intro Q w
    rw [hpc, hcnt]
    have hS := srcPc_sumPt f Z b y (legMode b p z) hsok Q w
    have hI : ∑ pt, f Q pt w = (∑ pt, G.σ.pc Q pt w) + (if Q = E ∧ w = y then 1 else 0) :=
      sumPt_incP G.σ.pc E b y Q w
    have hle := hL.pc_le Q w
    rw [hmout] at hS
    by_cases h : Q = Z ∧ w = y
    · have hQE : ¬ (Q = E ∧ w = y) := fun h' => hEZ (h'.1.symm.trans h.1)
      rw [if_neg hQE] at hI ⊢
      rw [if_pos h]
      have A : p = none → (∑ pt, G.σ.pc Q pt w) + 1 ≤ G.σ.cnt Q w := by
        rw [h.1, h.2]; exact hmain
      have B : p ≠ none → 1 ≤ ∑ pt, G.σ.pc Q pt w := by rw [h.1, h.2]; exact hpcZy
      by_cases hp : p = none
      · have := A hp; rw [if_pos hp] at hS; split_ifs at hS <;> omega
      · have := B hp; rw [if_neg hp, if_pos h] at hS; omega
    · rw [if_neg h]
      split_ifs at hS <;> omega
  · intro Q pt
    rw [hpc]
    have hS := srcPc_sumZ f Z b y (legMode b p z) hsok Q pt
    have hI : ∑ w, f Q pt w = (∑ w, G.σ.pc Q pt w) + (if Q = E ∧ pt = b then 1 else 0) :=
      sumZ_incP G.σ.pc E b y Q pt
    have h0 := hL.psum Q pt
    show _ + (if Z = Q ∧ b = pt then 1 else 0) = _
    have e1 : (if Z = Q ∧ b = pt then 1 else 0) = (if Q = Z ∧ pt = b then 1 else 0) := by
      by_cases h : Q = Z ∧ pt = b
      · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
      · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]
    have e2 : (if G.σ.blank = Q ∧ G.σ.bp = pt then 1 else 0) = (if Q = E ∧ pt = b then 1 else 0) := by
      by_cases h : Q = E ∧ pt = b
      · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
      · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]
    rw [e1]; rw [e2] at h0
    omega
  · intro u x hux
    have hs0 := hL.stockIn u x hux
    show G.stock u (dport L u x) x ≤ (pLeg s σ' G Z y p z).σ.pc u (dport L u x) x
    rw [hpc]
    by_cases hu : u = Z
    · subst hu
      have hdem : ∀ pt0, dport L u x = pt0 → dem L G u (some pt0) x = G.stock u pt0 x :=
        fun pt0 h => by
          show (if x ≠ u ∧ dport L u x = pt0 then G.stock u pt0 x else 0) = _
          rw [if_pos ⟨Ne.symm hux, h⟩]
      rcases p with _ | p'
      · show _ ≤ decP f u b z u (dport L u x) x
        rw [decP_apply, hfZ]
        by_cases h : u = u ∧ dport L u x = b ∧ x = z
        · obtain ⟨-, h2, h3⟩ := h
          rw [if_pos ⟨rfl, h2, h3⟩]
          have := hz (by simp)
          rw [← h3, hdem b h2] at this
          rw [h2] at hs0 ⊢; omega
        · rw [if_neg h]; omega
      · by_cases hpb : p' = b
        · rw [show legMode b (some p') z = Mode.cheap by simp [legMode, hpb]]
          show _ ≤ decP f u b y u (dport L u x) x
          rw [decP_apply, hfZ]
          by_cases h : u = u ∧ dport L u x = b ∧ x = y
          · obtain ⟨-, h2, h3⟩ := h
            rw [if_pos ⟨rfl, h2, h3⟩]
            simp only [PState.partCnt] at hy
            rw [hpb, ← h3, hdem b h2] at hy
            rw [h2] at hs0 ⊢; omega
          · rw [if_neg h]; omega
        · rw [show legMode b (some p') z = Mode.imp (some p') z by simp [legMode, hpb]]
          show _ ≤ decP (incP (decP f u p' y) u p' z) u b z u (dport L u x) x
          rw [decP_apply, incP_apply, decP_apply, hfZ]
          have hzb := hz (by simp [hpb])
          by_cases h1 : u = u ∧ dport L u x = p' ∧ x = y
          · obtain ⟨-, h2, h3⟩ := h1
            have hc3 : ¬ (u = u ∧ dport L u x = b ∧ x = z) := fun h => hpb (h2.symm.trans h.2.1)
            rw [if_pos (show u = u ∧ dport L u x = p' ∧ x = y from ⟨rfl, h2, h3⟩), if_neg hc3]
            simp only [PState.partCnt] at hy
            rw [← h3, hdem p' h2] at hy
            rw [h2] at hs0 ⊢
            (try split_ifs) <;> omega
          · rw [if_neg h1]
            by_cases h3 : u = u ∧ dport L u x = b ∧ x = z
            · obtain ⟨-, h2, h4⟩ := h3
              have hc2 : ¬ (u = u ∧ dport L u x = p' ∧ x = z) := fun h => hpb (h.2.1.symm.trans h2)
              rw [if_pos (show u = u ∧ dport L u x = b ∧ x = z from ⟨rfl, h2, h4⟩), if_neg hc2]
              rw [← h4, hdem b h2] at hzb
              rw [h2] at hs0 ⊢
              (try split_ifs) <;> omega
            · rw [if_neg h3]; (try split_ifs) <;> omega
    · rw [srcPc_ne _ Z _ y _ hu, hfdef, incP_apply]
      omega
  · have hc' := pcost_append L hL (.leg Z y p z)
    have hL' := hL.cost
    show σ0.totalCost s σ' (G.evs ++ [.leg Z y p z]) + (G.σ.step s (.leg Z y p z)).pot L s ≤
      σ0.pot L s + hopKc k q σ' * G.nh + hopKi k s σ' * G.ni + xferK k s σ' * G.nx +
        (k * s) * (∑ Q, ∑ x, G.B Q x) + (G.jc + G.σ.cost s σ' (.leg Z y p z))
    rw [hc', pot_leg]
    omega
  · have hF := sum_sum_sub_add G.free True True Z y E y (fun _ => hf)
    simp only [true_and, if_true] at hF
    have ht := hL.free_tot
    have hu : puntagged L s (pLeg s σ' G Z y p z) = puntagged L s G := rfl
    show (∑ Q, ∑ x, (G.free Q x - (if Q = Z ∧ x = y then 1 else 0) +
      (if Q = E ∧ x = y then 1 else 0))) + puntagged L s (pLeg s σ' G Z y p z) +
        (∑ Q, ∑ x, G.B Q x) = F0 + ∑ Q, ∑ x, G.dA Q x
    rw [hu]; omega

end ops

end SlidingPuzzle.Port
