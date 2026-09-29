import SlidingPuzzle.Port.Dance

/-! # Transfer of the blank between two ports of a square

From the cell `a0` of the blank's port box nearest its corner, the blank jumps to
the aligned cell `z0` of the other port's box (same rows for `tl`/`tr`, same
columns for `tl`/`bl`); a three-cycle in that port's corner box lines up a class-`c`
tile on `z'` (two cells deeper); the blank jumps back and then to `z'`. The
class-`c` tile ends on `a0`, in the former port. -/
namespace SlidingPuzzle.Port
open Classical
open SlidingPuzzle.Hub (Sq HDims sqOf classOf apply_blank blank_eq_of_apply val_ne_zero_of_ne_blank
  exists_vjump_step exists_hjump_step exists_box_three_cycle_near cornerDist InBox)
open SlidingPuzzle.Tree

variable {n k s q σ : ℕ} (L : LaneSys k q)

/-- The box cell of a port nearest its corner. -/
def ncell (k s : ℕ) : Pt → ℕ × ℕ
  | .tl => (k + 1, k + 1)
  | .tr => (k + 1, s - 2)
  | .bl => (s - 2, k + 1)

/-- The target of the first jump of a transfer from port `b` to port `pt`, before the parity
shift `j`. -/
def xz0 (k s : ℕ) (b pt : Pt) (j : ℕ) : ℕ × ℕ :=
  match b, pt with
  | .tl, .tr => (k + 1 + j, s - 2)
  | .tr, .tl => (k + 1 + j, k + 1)
  | .tl, .bl => (s - 2, k + 1 + j)
  | .bl, .tl => (k + 1, k + 1 + j)
  | _, _ => (k + 1, k + 1)

/-- The cell two steps deeper, where the carried tile is lined up. -/
def xz1 (k s : ℕ) (b pt : Pt) (j : ℕ) : ℕ × ℕ :=
  match b, pt with
  | .tl, .tr => (k + 1 + j, s - 4)
  | .tr, .tl => (k + 1 + j, k + 3)
  | .tl, .bl => (s - 4, k + 1 + j)
  | .bl, .tl => (k + 3, k + 1 + j)
  | _, _ => (k + 1, k + 1)

/-- The parity shift. -/
def xj (k s : ℕ) (b pt : Pt) : ℕ :=
  ((ncell k s b).1 + (ncell k s b).2 + (xz0 k s b pt 0).1 + (xz0 k s b pt 0).2 + 1) % 2

/-- The admissible pairs of ports. -/
def XOK (b pt : Pt) : Prop := (b = .tl ∧ pt = .tr) ∨ (b = .tr ∧ pt = .tl) ∨
  (b = .tl ∧ pt = .bl) ∨ (b = .bl ∧ pt = .tl)

theorem xok_of (b pt : Pt) (h1 : b ≠ pt) (h2 : b = .tl ∨ pt = .tl) : XOK b pt := by
  unfold XOK; cases b <;> cases pt <;> simp_all

/-- Geometry of a transfer, in local coordinates. -/
theorem xgeom (h4 : 4 ≤ σ) (hs : 2 * σ + 2 * k + 8 ≤ s) {b pt : Pt} (h : XOK b pt) :
    let a := ncell k s b
    let z := xz0 k s b pt (xj k s b pt)
    let z' := xz1 k s b pt (xj k s b pt)
    inBox k s σ b a.1 a.2 ∧ inBox k s σ pt z.1 z.2 ∧ inBox k s σ pt z'.1 z'.2 ∧
    z ≠ z' ∧ (∀ i : Fin 3, spare k s pt i ≠ z ∧ spare k s pt i ≠ z') ∧
    ((a.1 + 1 ≥ z.1 ∧ z.1 + 1 ≥ a.1 ∧ a.1 + 1 ≥ z'.1 ∧ z'.1 + 1 ≥ a.1) ∨
      (a.2 + 1 ≥ z.2 ∧ z.2 + 1 ≥ a.2 ∧ a.2 + 1 ≥ z'.2 ∧ z'.2 + 1 ≥ a.2)) ∧
    (a.1 + a.2 + z.1 + z.2) % 2 = 1 ∧ (a.1 + a.2 + z'.1 + z'.2) % 2 = 1 ∧
    cdist k s σ pt z.1 z.2 ≤ 2 * k + 3 ∧ cdist k s σ pt z'.1 z'.2 ≤ 2 * k + 5 ∧
    a.1 < s ∧ a.2 < s ∧ z.1 < s ∧ z.2 < s ∧ z'.1 < s ∧ z'.2 < s := by
  intro a z z'
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a, z, z', ncell, xz0, xz1, xj, inBox, spare, cdist, cfr, cfc, ne_eq,
      Prod.mk.injEq, if_true, if_false, Bool.false_eq_true, Nat.dist] <;>
    refine ⟨?_, ?_, ?_, ?_, fun i => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try have := i.isLt) <;> (try split_ifs) <;> omega

end SlidingPuzzle.Port

namespace SlidingPuzzle.Port
open Classical
open SlidingPuzzle.Hub (Sq HDims sqOf classOf apply_blank blank_eq_of_apply val_ne_zero_of_ne_blank
  exists_vjump_step exists_hjump_step exists_box_three_cycle_near cornerDist InBox)
open SlidingPuzzle.Tree

variable {n k s q σ : ℕ} [NeZero n] (L : LaneSys k q)

/-- A jump between two aligned local cells of a square. -/
theorem jump_local (pd : PDims n k s q σ) (Q : Sq k) {r1 c1 r2 c2 : ℕ} (h1 : r1 < s) (h2 : c1 < s)
    (h3 : r2 < s) (h4 : c2 < s)
    (hal : (r1 ≤ r2 + 1 ∧ r2 ≤ r1 + 1) ∨ (c1 ≤ c2 + 1 ∧ c2 ≤ c1 + 1))
    (hpar : (r1 + c1 + r2 + c2) % 2 = 1) (B' : Board n) (hB' : blank B' = lc s Q r1 c1) :
    ∃ p : Path B' (swapCells B' (blank B') (lc s Q r2 c2)), p.inefficientMoves ≤ 7 * (s + 1) := by
  have a1 := lc_fst (n := n) pd.hd Q c1 h1
  have a2 := lc_snd (n := n) pd.hd Q r1 h2
  have b1 := lc_fst (n := n) pd.hd Q c2 h3
  have b2 := lc_snd (n := n) pd.hd Q r2 h4
  generalize Q.1.val * s = R at *
  generalize Q.2.val * s = C at *
  rcases hal with hal | hal
  · obtain ⟨p, hp⟩ := exists_hjump_step pd.hd.two_le_n B' (lc s Q r2 c2)
      (by rw [hB', a1, b1]; simp only [Nat.dist]; omega)
      (by rw [hB', a1, a2, b1, b2]; omega)
    exact ⟨p, hp.trans (by rw [hB', a2, b2]; simp only [Nat.dist]; omega)⟩
  · obtain ⟨p, hp⟩ := exists_vjump_step pd.hd.two_le_n B' (lc s Q r2 c2)
      (by rw [hB', a2, b2]; simp only [Nat.dist]; omega)
      (by rw [hB', a1, a2, b1, b2]; omega)
    exact ⟨p, hp.trans (by rw [hB', a1, b1]; simp only [Nat.dist]; omega)⟩

/-- Counts are kept when no tile changes its refined key. -/
theorem pcount_keep (pd : PDims n k s q σ) {B C : Board n}
    (K : KeepK (rkey L s σ pd.hd) B C ∅) (Q : Sq k) (p : Part) (y : Sq k) :
    pcount L s σ pd.hd C Q p y = pcount L s σ pd.hd B Q p y := by
  have e := kcount_keepK (rkey L s σ pd.hd) pd.hd K (some (Q, p)) y
  simp at e
  exact e

theorem regionCount_keep (pd : PDims n k s q σ) {B C : Board n}
    (K : KeepK (rkey L s σ pd.hd) B C ∅) (Q y : Sq k) :
    regionCount L pd.hd C Q y = regionCount L pd.hd B Q y := by
  rw [regionCount_eq_sum L (σ := σ), regionCount_eq_sum L (σ := σ)]
  exact Finset.sum_congr rfl fun p _ => pcount_keep L pd K Q p y

end SlidingPuzzle.Port

namespace SlidingPuzzle.Port
open Classical
open SlidingPuzzle.Hub (Sq HDims sqOf classOf apply_blank blank_eq_of_apply val_ne_zero_of_ne_blank
  exists_vjump_step exists_hjump_step exists_box_three_cycle_near cornerDist InBox)
open SlidingPuzzle.Tree

variable {n k s q σ : ℕ} [NeZero n] (L : LaneSys k q)

/-- Port counts through a move of one tile between two parts of a square. -/
theorem pc_move1 (pd : PDims n k s q σ) {B C : Board n} {t : Tile n} {Q : Sq k} {a b : Pt}
    (hab : a ≠ b) (K : KeepK (rkey L s σ pd.hd) B C {t}) (ht : t.val ≠ 0)
    (hB : rkey L s σ pd.hd (position B t) = some (Q, some a))
    (hC : rkey L s σ pd.hd (position C t) = some (Q, some b)) (hpos : 1 ≤ pcOf L pd B Q a (classOf pd.hd t)) :
    pcOf L pd C = incP (decP (pcOf L pd B) Q a (classOf pd.hd t)) Q b (classOf pd.hd t) := by
  funext Q' pt' z
  have e := kcount_move1 (rkey L s σ pd.hd) pd.hd K ht (some (Q', some pt')) z
  rw [hB, hC] at e
  unfold pcOf pcount incP decP at *
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  by_cases h1 : Q' = Q ∧ pt' = a ∧ z = classOf pd.hd t
  · obtain ⟨rfl, rfl, rfl⟩ := h1
    have : ¬ (Q' = Q' ∧ pt' = b ∧ classOf pd.hd t = classOf pd.hd t) := fun h => hab h.2.1
    simp only [and_self, if_true, true_and, and_true] at e ⊢
    rw [if_neg (fun h => hab h.symm)] at e
    rw [if_neg (fun h => hab h)]
    omega
  · rw [if_neg h1]
    rw [if_neg (by rintro ⟨⟨h2, h3⟩, h4⟩; exact h1 ⟨h2.symm, h3.symm, h4.symm⟩)] at e
    by_cases h2 : Q' = Q ∧ pt' = b ∧ z = classOf pd.hd t
    · rw [if_pos h2]
      rw [if_pos ⟨⟨h2.1.symm, h2.2.1.symm⟩, h2.2.2.symm⟩] at e
      omega
    · rw [if_neg h2]
      rw [if_neg (by rintro ⟨⟨h3, h4⟩, h5⟩; exact h2 ⟨h3.symm, h4.symm, h5.symm⟩)] at e
      omega

/-- A transfer realized on the board. -/
theorem simulate_xfer (pd : PDims n k s q σ) (h4 : 4 ≤ σ) {B : Board n} {ρ : PState k q}
    (hR : PRel L pd B ρ) {pt : Pt} {c : Sq k} (hpre : ρ.Pre L (.xfer pt c)) :
    ∃ C : Board n, ∃ p : Path B C, PRel L pd C (ρ.step s (.xfer pt c)) ∧
      p.inefficientMoves ≤ ρ.cost s σ (.xfer pt c) := by
  obtain ⟨hne, htl, hc⟩ := hpre
  have hf := pd.fit
  have hqk := pd.td.q_le
  set Q := ρ.blank with hQ
  set b := ρ.bp with hb
  have hx : XOK b pt := xok_of b pt hne htl
  obtain ⟨ga, gz, gz1, gzz, gsp, gal, gp1, gp2, gc1, gc2, ga1, ga2, gzr, gzc, gwr, gwc⟩ :=
    xgeom (k := k) h4 hf hx
  set a := ncell k s b with ha
  set z := xz0 k s b pt (xj k s b pt) with hz
  set z' := xz1 k s b pt (xj k s b pt) with hz'
  set a0 : Cell n := lc s Q a.1 a.2 with ha0
  set z0 : Cell n := lc s Q z.1 z.2 with hz0
  set z1 : Cell n := lc s Q z'.1 z'.2 with hz1
  have ka0 : rkey L s σ pd.hd a0 = some (Q, some b) := rkey_box L pd Q ga
  have kz0 : rkey L s σ pd.hd z0 = some (Q, some pt) := rkey_box L pd Q gz
  have kz1 : rkey L s σ pd.hd z1 = some (Q, some pt) := rkey_box L pd Q gz1
  have hbpt : (some (Q, some b) : Option (Sq k × Part)) ≠ some (Q, some pt) := by
    simp only [ne_eq, Option.some.injEq, Prod.mk.injEq, true_and]; exact hne
  have ha0z0 : a0 ≠ z0 := ne_of_rkey L (by rw [ka0, kz0]; exact hbpt)
  have ha0z1 : a0 ≠ z1 := ne_of_rkey L (by rw [ka0, kz1]; exact hbpt)
  have hz0z1 : z0 ≠ z1 := fun e => gzz (Prod.ext (lc_inj pd.hd Q gzr gzc gwr gwc e).1
    (lc_inj pd.hd Q gzr gzc gwr gwc e).2)
  have hjump : ∀ (r1 c1 r2 c2 : ℕ), r1 < s → c1 < s → r2 < s → c2 < s →
      ((r1 ≤ r2 + 1 ∧ r2 ≤ r1 + 1) ∨ (c1 ≤ c2 + 1 ∧ c2 ≤ c1 + 1)) →
      (r1 + c1 + r2 + c2) % 2 = 1 → ∀ B' : Board n, blank B' = lc s Q r1 c1 →
      ∃ p : Path B' (swapCells B' (blank B') (lc s Q r2 c2)), p.inefficientMoves ≤ 7 * (s + 1) :=
    fun r1 c1 r2 c2 h1 h2 h3 h4' hal hp B' hB' => jump_local pd Q h1 h2 h3 h4' hal hp B' hB'
  have hal0 : (a.1 ≤ z.1 + 1 ∧ z.1 ≤ a.1 + 1) ∨ (a.2 ≤ z.2 + 1 ∧ z.2 ≤ a.2 + 1) := by
    rcases gal with h | h
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have hal1 : (a.1 ≤ z'.1 + 1 ∧ z'.1 ≤ a.1 + 1) ∨ (a.2 ≤ z'.2 + 1 ∧ z'.2 ≤ a.2 + 1) := by
    rcases gal with h | h
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have hal0' : (z.1 ≤ a.1 + 1 ∧ a.1 ≤ z.1 + 1) ∨ (z.2 ≤ a.2 + 1 ∧ a.2 ≤ z.2 + 1) := by
    rcases hal0 with h | h
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr ⟨h.2, h.1⟩
  have gp1' : (z.1 + z.2 + a.1 + a.2) % 2 = 1 := by omega
  -- walk to `a0`
  obtain ⟨B0, p0, hb0, hi0, hf0, K0⟩ := exists_box_walk L pd (by omega) B hR.2.2.2.2
    (inBoxOf_lc pd Q ga)
  replace hb0 : blank B0 = a0 := hb0
  have hpc0 : pcount L s σ pd.hd B0 Q (some pt) c = ρ.pc Q pt c := by
    rw [pcount_keep L pd K0, hR.2.2.2.1]
  obtain ⟨t, htk, ht0, htc⟩ := exists_of_kcount (rkey L s σ pd.hd) pd.hd B0
    (show 1 ≤ kcount (rkey L s σ pd.hd) pd.hd B0 (some (Q, some pt)) c by
      rw [show kcount (rkey L s σ pd.hd) pd.hd B0 (some (Q, some pt)) c =
        pcount L s σ pd.hd B0 Q (some pt) c from rfl, hpc0]; exact hc)
  have hta0 : t ≠ a0 := ne_of_rkey L (by rw [htk, ka0]; exact hbpt.symm)
  have hB0t : B0 t = B t := hf0 t (fun h => by
    have := rkey_inBoxOf L pd h; rw [htk] at this; exact hbpt this.symm)
  set Tc := B0 t with hTc
  -- the board after the transfer, and what it keeps
  obtain ⟨C, p1, hCa0, hbC, hCQ, KC, hi1⟩ : ∃ C : Board n, ∃ p : Path B0 C,
      C a0 = Tc ∧ InBoxOf s σ Q pt (blank C) ∧
      (∀ x, rkey L s σ pd.hd x ≠ some (Q, some pt) → x ≠ a0 → C x = B0 x) ∧
      KeepK (rkey L s σ pd.hd) B0 C {Tc} ∧
      p.inefficientMoves ≤ 21 * (s + 1) + 10 * σ + 600 * k + 2000 := by
    by_cases htz : t = z0
    · -- the class-`c` tile is on `z0`: one jump
      obtain ⟨pj, hpj⟩ := hjump a.1 a.2 z.1 z.2 ga1 ga2 gzr gzc hal0 gp1 B0 hb0
      refine ⟨swapCells B0 (blank B0) z0, pj, ?_, ?_, ?_, ?_, by omega⟩
      · rw [hb0, swapCells_at_left, hTc, htz]
      · rw [blank_swapCells]; exact inBoxOf_lc pd Q gz
      · intro x h1 h2
        exact swapCells_preserves B0 (by rw [hb0]; exact h2)
          (fun e => h1 (by rw [e]; exact kz0))
      · have := keepK_of_agree_outside (rkey L s σ pd.hd) (B := B0)
          (C := swapCells B0 (blank B0) z0) {a0, z0}
          (fun x hx => by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
            exact swapCells_preserves B0 (by rw [hb0]; exact hx.1) hx.2)
        have e1 : B0 a0 = 0 := by rw [← hb0]; exact apply_blank B0
        have e2 : B0 z0 = Tc := by rw [hTc, htz]
        rw [Finset.image_insert, Finset.image_singleton, e1, e2] at this
        exact KeepK.erase_zero this
    · -- the dance, lining up the tile on `z1`
      obtain ⟨i, hi, hut⟩ : ∃ i : Fin 3, i.val ≤ 1 ∧
          lc (n := n) s Q (spare k s pt i).1 (spare k s pt i).2 ≠ t := by
        by_cases h0 : lc (n := n) s Q (spare k s pt 0).1 (spare k s pt 0).2 = t
        · refine ⟨1, by simp, fun h1 => ?_⟩
          have := spare_lt pd pt 0
          have := spare_lt pd pt 1
          have e := lc_inj pd.hd Q (by omega) (by omega) (by omega) (by omega) (h0.trans h1.symm)
          exact absurd (spare_inj hf pt (Prod.ext e.1 e.2)) (by decide)
        · exact ⟨0, by simp, h0⟩
      set u : Cell n := lc s Q (spare k s pt i).1 (spare k s pt i).2 with hu
      have hubox := spare_box h4 hf pt i
      have ku : rkey L s σ pd.hd u = some (Q, some pt) := rkey_box L pd Q hubox
      obtain ⟨hs1, hs2⟩ := spare_lt pd pt i
      have huz0 : u ≠ z0 := fun e => (gsp i).1 (Prod.ext (lc_inj pd.hd Q hs1 hs2 gzr gzc e).1
        (lc_inj pd.hd Q hs1 hs2 gzr gzc e).2)
      have huz1 : u ≠ z1 := fun e => (gsp i).2 (Prod.ext (lc_inj pd.hd Q hs1 hs2 gwr gwc e).1
        (lc_inj pd.hd Q hs1 hs2 gwr gwc e).2)
      have hua0 : u ≠ a0 := ne_of_rkey L (by rw [ku, ka0]; exact hbpt.symm)
      set U : Cell n → Prop := fun x => x = t ∨ x = u ∨ x = z1 with hU
      have hUa : ¬ U a0 := by
        rintro (e | e | e)
        · exact hta0 e.symm
        · exact hua0 e.symm
        · exact ha0z1 e
      have hUz0 : ¬ U z0 := by
        rintro (e | e | e)
        · exact htz e.symm
        · exact huz0 e.symm
        · exact hz0z1 e
      set B1 := swapCells B0 (blank B0) z0 with hB1
      have hbB1 : blank B1 = z0 := blank_swapCells B0 _
      have hB1x : ∀ x, x ≠ a0 → x ≠ z0 → B1 x = B0 x := fun x h1 h2 =>
        swapCells_preserves B0 (by rw [hb0]; exact h1) h2
      have hB1t : B1 t = Tc := hB1x t hta0 htz
      -- the middle: a three-cycle in the port's corner box
      obtain ⟨M, pm, hbM, hpm, hMx, hMz1, hMtu, hMeq⟩ : ∃ M : Board n, ∃ p : Path B1 M,
          blank M = z0 ∧
          p.inefficientMoves ≤ 10 * σ + 600 * k + 2000 ∧ (∀ x, ¬ U x → M x = B1 x) ∧
          M z1 = Tc ∧ (t ≠ z1 → M t = B1 u ∧ M u = B1 z1) ∧ (t = z1 → ∀ x, M x = B1 x) := by
        by_cases htz1 : t = z1
        · refine ⟨B1, .nil B1, hbB1, by simp [Path.inefficientMoves], fun _ _ => rfl, ?_,
            fun h => absurd htz1 h, fun _ _ => rfl⟩
          rw [← htz1, hB1t]
        obtain ⟨fit1, fit2⟩ := corner_fits pd Q pt
        obtain ⟨c1, c2, c3, c4⟩ := box_corner pd gz
        obtain ⟨d1, d2, d3, d4⟩ := box_corner pd gz1
        obtain ⟨u1, u2, u3, u4⟩ := box_corner pd hubox
        have h0 : ∀ x : Cell n, x ≠ z0 → B1 x ≠ 0 := fun x hx e =>
          hx (hbB1 ▸ (blank_eq_of_apply e).symm)
        obtain ⟨M, pm, hpm, hMa, hMb, hMc, hMx⟩ := exists_box_three_cycle_near B1
          (Q.1.val * s + cr0 k s σ pt) (Q.2.val * s + cc0 k s σ pt) (k + 2 + σ) (cfr pt) (cfc pt)
          (by omega) fit1 fit2 (by rw [hbB1]; exact inCorner_lc pd Q pt c1 c2 c3 c4 gzr gzc)
          z1 t u (inCorner_lc pd Q pt d1 d2 d3 d4 gwr gwc) (inCorner_of_rkey L pd htk)
          (inCorner_lc pd Q pt u1 u2 u3 u4 hs1 hs2) (Ne.symm htz1) (Ne.symm huz1) (Ne.symm hut)
          (h0 z1 (Ne.symm hz0z1)) (h0 t htz) (h0 u huz0)
        have hcd : cornerDist (Q.1.val * s + cr0 k s σ pt) (Q.2.val * s + cc0 k s σ pt)
            (k + 2 + σ) (cfr pt) (cfc pt) (blank B1) z1 u ≤ 6 * k + 17 := by
          rw [hbB1, cr0_eq, cc0_eq]
          refine (cornerDist_le pd Q pt (by omega) (by omega) gzr gzc gwr gwc hs1 hs2).trans ?_
          have := cdist_spare (σ := σ) hf pt i
          omega
        refine ⟨M, pm, (blank_of_cycle (by rw [hbB1]; exact Ne.symm hz0z1)
            (by rw [hbB1]; exact htz) (by rw [hbB1]; exact huz0) hMx).trans hbB1, ?_,
          fun x hx => hMx x (fun e => hx (Or.inr (Or.inr e))) (fun e => hx (Or.inl e))
            (fun e => hx (Or.inr (Or.inl e))), by rw [hMa, hB1t], fun _ => ⟨hMb, hMc⟩,
          fun h => absurd h htz1⟩
        have : 82 * cornerDist (Q.1.val * s + cr0 k s σ pt) (Q.2.val * s + cc0 k s σ pt)
          (k + 2 + σ) (cfr pt) (cfc pt) (blank B1) z1 u ≤ 82 * (6 * k + 17) :=
          Nat.mul_le_mul_left _ hcd
        omega
      obtain ⟨C, pc, hCa, hbC, hCz0, hCx, hic⟩ := dance B0 hb0 ha0z0 hz0z1 ha0z1 U hUa
        (7 * (s + 1)) (10 * σ + 600 * k + 2000)
        (hjump a.1 a.2 z.1 z.2 ga1 ga2 gzr gzc hal0 gp1 B0 hb0)
        (fun B' hB' => hjump z.1 z.2 a.1 a.2 gzr gzc ga1 ga2 hal0' gp1' B' hB')
        (fun B' hB' => hjump a.1 a.2 z'.1 z'.2 ga1 ga2 gwr gwc hal1 gp2 B' hB')
        M pm hbM hpm hMx
      have hCt : ∀ x, x ≠ a0 → x ≠ z0 → x ≠ z1 → ¬ U x → C x = B0 x := fun x h1 h2 h3 h4' =>
        (hCx x h1 h2 h3).trans ((hMx x h4').trans (hB1x x h1 h2))
      have hCz1 : C z1 = 0 := by rw [← hbC]; exact apply_blank C
      have hB0a0 : B0 a0 = 0 := by rw [← hb0]; exact apply_blank B0
      refine ⟨C, pc, by rw [hCa, hMz1], by rw [hbC]; exact inBoxOf_lc pd Q gz1, ?_, ?_,
        le_of_le_of_eq hic (by ring)⟩
      · intro x h1 h2
        have hxz0 : x ≠ z0 := fun e => h1 (by rw [e]; exact kz0)
        have hxz1 : x ≠ z1 := fun e => h1 (by rw [e]; exact kz1)
        by_cases hxU : U x
        · exfalso
          rcases hxU with e | e | e
          · exact h1 (by rw [e]; exact htk)
          · exact h1 (by rw [e]; exact ku)
          · exact hxz1 e
        · exact hCt x h2 hxz0 hxz1 hxU
      · -- only the carried tile changes its refined key
        by_cases htz1 : t = z1
        · have hCo : ∀ x, x ∉ ({a0, z1} : Finset (Cell n)) → C x = B0 x := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
            by_cases hx0 : x = z0
            · rw [hx0, hCz0]
            · rw [hCx x hx.1 hx0 hx.2, hMeq htz1 x, hB1x x hx.1 hx0]
          have K := keepK_of_agree_outside (rkey L s σ pd.hd) {a0, z1} hCo
          have e2 : B0 z1 = Tc := by rw [hTc, htz1]
          rw [Finset.image_insert, Finset.image_singleton, hB0a0, e2] at K
          exact KeepK.erase_zero K
        · obtain ⟨hMt, hMu⟩ := hMtu htz1
          have hCo : ∀ x, x ∉ ({a0, z1, t, u} : Finset (Cell n)) → C x = B0 x := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
            by_cases hx0 : x = z0
            · rw [hx0, hCz0]
            · exact hCt x hx.1 hx0 hx.2.1 (by
                rintro (e | e | e)
                · exact hx.2.2.1 e
                · exact hx.2.2.2 e
                · exact hx.2.1 e)
          have K := keepK_of_agree_outside (rkey L s σ pd.hd) {a0, z1, t, u} hCo
          rw [Finset.image_insert, Finset.image_insert, Finset.image_insert, Finset.image_singleton,
            hB0a0] at K
          have hut' : u ≠ t := hut
          have hCt' : C t = B0 u := by
            rw [hCx t hta0 htz htz1, hMt, hB1x u hua0 huz0]
          have hCu' : C u = B0 z1 := by
            rw [hCx u hua0 huz0 huz1, hMu, hB1x z1 (Ne.symm ha0z1) (Ne.symm hz0z1)]
          intro T hT0 hT
          rw [Finset.mem_singleton] at hT
          by_cases e1 : T = B0 z1
          · subst e1
            rw [position_eq_of_apply hCu', show position B0 (B0 z1) = z1 by simp [position], ku, kz1]
          by_cases e2 : T = B0 u
          · subst e2
            rw [position_eq_of_apply hCt', show position B0 (B0 u) = u by simp [position], htk, ku]
          apply K T hT0
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun e => hT0 (by rw [e]; rfl), e1, hT, e2⟩
  -- the relation after the transfer
  have K : KeepK (rkey L s σ pd.hd) B C {Tc} := by
    have := K0.trans KC; simpa using this
  have hposB : position B Tc = t := by
    have e : Tc = B t := hB0t
    rw [e]; simp [position]
  have hposC : position C Tc = a0 := position_eq_of_apply hCa0
  have hT0 : Tc.val ≠ 0 := ht0
  refine ⟨C, p0.append p1, prel_of_lanes L pd ?_ ?_ ?_ ?_, ?_⟩
  · intro l r hr
    have hk := rkey_lcell L pd l hr
    rw [hCQ _ (by rw [hk]; simp) (fun e => by rw [e, ka0] at hk; cases hk),
      hf0 _ (fun h => by have := rkey_inBoxOf L pd h; rw [hk] at this; cases this)]
    exact prel_lane L pd hR l hr
  · intro Q' y
    have KK : KeepKey L pd.hd B C ∅ := by
      have K' := keepKey_of_keepK L pd.hd K
      intro T hT0' _
      by_cases e : T = Tc
      · subst e
        rw [hposB, hposC, key_of_rkey L pd.hd htk, key_of_rkey L pd.hd ka0]
      · exact K' T hT0' (by simpa using e)
    have e := regionCount_keepKey L pd.hd KK Q' y
    simp only [Finset.filter_empty, Finset.card_empty, add_zero] at e
    rw [e]; exact hR.2.2.1 Q' y
  · intro Q' pt' z
    have hpos : 1 ≤ pcOf L pd B Q pt (classOf pd.hd Tc) := by
      unfold pcOf; rw [hR.2.2.2.1]; show 1 ≤ ρ.pc Q pt (classOf pd.hd (B0 t)); rw [htc]; exact hc
    have e := pc_move1 L pd hne.symm K hT0 (by rw [hposB]; exact htk) (by rw [hposC]; exact ka0)
      hpos
    show pcOf L pd C Q' pt' z = _
    rw [e]
    have hpcB : pcOf L pd B = ρ.pc :=
      funext fun Q => funext fun pt => funext fun z => hR.2.2.2.1 Q pt z
    rw [hpcB]
    show incP (decP ρ.pc Q pt (classOf pd.hd (B0 t))) Q b (classOf pd.hd (B0 t)) Q' pt' z = _
    rw [htc]
    rfl
  · exact hbC
  · rw [Path.inefficientMoves_append]
    show _ ≤ xferK k s σ
    unfold xferK
    omega


end SlidingPuzzle.Port
