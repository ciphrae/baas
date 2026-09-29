import SlidingPuzzle.Port.LegOp

/-! # The two kinds of legs on boards -/
namespace SlidingPuzzle.Port
open Classical
open SlidingPuzzle.Hub (Sq HDims sqOf classOf sqDist apply_blank blank_eq_of_apply
  val_ne_zero_of_ne_blank exists_box_three_cycle_near cornerDist InBox)
open SlidingPuzzle.Tree

variable {n k s q σ : ℕ} [NeZero n] (L : LaneSys k q)

/-- A three-cycle in the box of square `Z`, staged at the corner of port `b`, the blank and
two of the cells on box cells of that port. -/
theorem square_cycle (pd : PDims n k s q σ) (h8 : 8 ≤ σ) (B1 : Board n) (Z : Sq k) (b : Pt)
    {rb cb ra ca rc cc : ℕ} (hbx : inBox k s σ b rb cb) (hax : inBox k s σ b ra ca)
    (hcx : inBox k s σ b rc cc) (hbl : blank B1 = lc s Z rb cb) {t : Cell n} {p : Part}
    (ht : rkey L s σ pd.hd t = some (Z, p))
    (hb : cdist k s σ b rb cb ≤ 2 * k + 8) (ha : cdist k s σ b ra ca ≤ 2 * k + 8)
    (hc : cdist k s σ b rc cc ≤ 2 * k + 8)
    (h1 : lc (n := n) s Z ra ca ≠ t) (h2 : lc (n := n) s Z ra ca ≠ lc s Z rc cc)
    (h3 : t ≠ lc s Z rc cc)
    (h1' : lc (n := n) s Z ra ca ≠ blank B1) (h2' : t ≠ blank B1)
    (h3' : lc (n := n) s Z rc cc ≠ blank B1) :
    ∃ M : Board n, ∃ p : Path B1 M, p.inefficientMoves ≤ 10 * s + 600 * k + 3000 ∧
      M (lc s Z ra ca) = B1 t ∧ M t = B1 (lc s Z rc cc) ∧ M (lc s Z rc cc) = B1 (lc s Z ra ca) ∧
      blank M = blank B1 ∧
      ∀ x, x ≠ lc s Z ra ca → x ≠ t → x ≠ lc s Z rc cc → M x = B1 x := by
  have hf := pd.fit
  have hs6 : 6 ≤ s := by omega
  have bb : ∀ {r c : ℕ}, inBox k s σ b r c → r < s ∧ c < s := fun h => by
    have := box_bounds pd b; rw [inBox_iff (by omega)] at h; omega
  obtain ⟨b1, b2⟩ := bb hbx
  obtain ⟨a1, a2⟩ := bb hax
  obtain ⟨c1, c2⟩ := bb hcx
  have hs0 : Z.1.val * s + (if cfr b then s - s else 0) + s ≤ n := by
    have := pd.hd.band_le Z.1.isLt; split_ifs <;> omega
  have hs0' : Z.2.val * s + (if cfc b then s - s else 0) + s ≤ n := by
    have := pd.hd.band_le Z.2.isLt; split_ifs <;> omega
  have sq : ∀ {x : Cell n}, InBox (Z.1.val * s) (Z.2.val * s) s x →
      InBox (Z.1.val * s + (if cfr b then s - s else 0))
        (Z.2.val * s + (if cfc b then s - s else 0)) s x := fun h => by
    simp only [Nat.sub_self, ite_self, add_zero]; exact h
  have h0 : ∀ x : Cell n, x ≠ blank B1 → B1 x ≠ 0 := fun x hx e => hx (blank_eq_of_apply e).symm
  obtain ⟨M, pm, hpm, hMa, hMb, hMc, hMx⟩ := exists_box_three_cycle_near B1
    (Z.1.val * s + (if cfr b then s - s else 0)) (Z.2.val * s + (if cfc b then s - s else 0)) s
    (cfr b) (cfc b) hs6 hs0 hs0' (by rw [hbl]; exact sq (inSquare_lc pd Z b1 b2))
    (lc s Z ra ca) t (lc s Z rc cc) (sq (inSquare_lc pd Z a1 a2)) (sq (inSquare_of_rkey L pd ht))
    (sq (inSquare_lc pd Z c1 c2)) h1 h2 h3 (h0 _ h1') (h0 _ h2') (h0 _ h3')
  have hcd : cornerDist (Z.1.val * s + (if cfr b then s - s else 0))
      (Z.2.val * s + (if cfc b then s - s else 0)) s (cfr b) (cfc b) (blank B1) (lc s Z ra ca)
      (lc s Z rc cc) ≤ 6 * k + 25 := by
    rw [hbl]
    refine (cornerDist_le pd Z b (by omega) le_rfl b1 b2 a1 a2 c1 c2).trans ?_
    omega
  refine ⟨M, pm, ?_, hMa, hMb, hMc, blank_of_cycle h1' h2' h3' hMx, hMx⟩
  have : 82 * cornerDist (Z.1.val * s + (if cfr b then s - s else 0))
    (Z.2.val * s + (if cfc b then s - s else 0)) s (cfr b) (cfc b) (blank B1) (lc s Z ra ca)
      (lc s Z rc cc) ≤ 82 * (6 * k + 25) := Nat.mul_le_mul_left _ hcd
  omega

end SlidingPuzzle.Port

namespace SlidingPuzzle.Port
open Classical
open SlidingPuzzle.Hub (Sq HDims sqOf classOf sqDist apply_blank blank_eq_of_apply
  val_ne_zero_of_ne_blank)
open SlidingPuzzle.Tree

variable {n k s q σ : ℕ} [NeZero n] (L : LaneSys k q)

/-- The cells of a leg, their keys and jumps. -/
structure LegCells (pd : PDims n k s q σ) (E Z : Sq k) (b : Pt) (m : ℕ) : Prop where
  ga : inBox k s σ b (ncell k s b).1 (ncell k s b).2
  gz : inBox k s σ b (lz k s b (legHor E Z) (legJ s E Z) m).1 (lz k s b (legHor E Z) (legJ s E Z) m).2
  gz' : inBox k s σ b (lz k s b (legHor E Z) (legJ s E Z) (m + 2)).1
    (lz k s b (legHor E Z) (legJ s E Z) (m + 2)).2
  sp : ∀ i : Fin 3, spare k s b i ≠ lz k s b (legHor E Z) (legJ s E Z) m ∧
    spare k s b i ≠ lz k s b (legHor E Z) (legJ s E Z) (m + 2)
  cz : cdist k s σ b (lz k s b (legHor E Z) (legJ s E Z) m).1
    (lz k s b (legHor E Z) (legJ s E Z) m).2 ≤ 2 * k + 8
  cz' : cdist k s σ b (lz k s b (legHor E Z) (legJ s E Z) (m + 2)).1
    (lz k s b (legHor E Z) (legJ s E Z) (m + 2)).2 ≤ 2 * k + 8
  ne : lz k s b (legHor E Z) (legJ s E Z) m ≠ lz k s b (legHor E Z) (legJ s E Z) (m + 2)

theorem legCells (pd : PDims n k s q σ) (h8 : 8 ≤ σ) (E Z : Sq k) (b : Pt) {m : ℕ} (hm : m ≤ 2) :
    LegCells pd E Z b m := by
  have hf := pd.fit
  have hj : legJ s E Z ≤ 1 := by unfold legJ; split_ifs <;> omega
  obtain ⟨g1, g2, g3, -, -, g4, -⟩ := lgeom (k := k) h8 hf b (legHor E Z) hj (m := m) (by omega)
  obtain ⟨-, g5, g6, -, -, g7, -⟩ := lgeom (k := k) h8 hf b (legHor E Z) hj (m := m + 2) (by omega)
  exact ⟨g1, g2, g5, fun i => ⟨g3 i, g6 i⟩, g4, g7, lz_ne (by omega) (by omega) (by omega) (by omega)⟩

/-- A leg carrying a tile of `Z`'s port `b` to `E`'s. -/
theorem leg_same (pd : PDims n k s q σ) (h8 : 8 ≤ σ) (B0 : Board n) {E Z : Sq k} (hEZ : E ≠ Z)
    (hal : E.1 = Z.1 ∨ E.2 = Z.2) (b : Pt)
    (hb0 : blank B0 = lc s E (ncell k s b).1 (ncell k s b).2)
    {ty : Cell n} (hty : rkey L s σ pd.hd ty = some (Z, some b)) :
    ∃ C : Board n, ∃ p : Path B0 C, C (blank B0) = B0 ty ∧ InBoxOf s σ Z b (blank C) ∧
      (∀ x, rkey L s σ pd.hd x ≠ some (Z, some b) → x ≠ blank B0 → C x = B0 x) ∧
      KeepK (rkey L s σ pd.hd) B0 C {B0 ty} ∧
      p.inefficientMoves ≤ 21 * (sqDist E Z * s + 5) + 10 * σ + 600 * k + 3000 := by
  have hf := pd.fit
  obtain ⟨ga, gz, gz', gsp, gcz, gcz', gne⟩ := legCells pd h8 E Z b (m := 0) (by omega)
  set a := ncell k s b
  set w0 := lz k s b (legHor E Z) (legJ s E Z) 0
  set w1 := lz k s b (legHor E Z) (legJ s E Z) (0 + 2)
  set a0 : Cell n := lc s E a.1 a.2
  set z0 : Cell n := lc s Z w0.1 w0.2
  set z1 : Cell n := lc s Z w1.1 w1.2
  have bb : ∀ {r c : ℕ}, inBox k s σ b r c → r < s ∧ c < s := fun h => by
    have := box_bounds pd b; rw [inBox_iff (by omega)] at h; omega
  have ka0 : rkey L s σ pd.hd a0 = some (E, some b) := rkey_box L pd E ga
  have kz0 : rkey L s σ pd.hd z0 = some (Z, some b) := rkey_box L pd Z gz
  have kz1 : rkey L s σ pd.hd z1 = some (Z, some b) := rkey_box L pd Z gz'
  have hEb : (some (E, some b) : Option (Sq k × Part)) ≠ some (Z, some b) := by simp [hEZ]
  have ha0z0 : a0 ≠ z0 := ne_of_rkey L (by rw [ka0, kz0]; exact hEb)
  have ha0z1 : a0 ≠ z1 := ne_of_rkey L (by rw [ka0, kz1]; exact hEb)
  have hz0z1 : z0 ≠ z1 := fun e => gne (Prod.ext (lc_inj pd.hd Z (bb gz).1 (bb gz).2 (bb gz').1
    (bb gz').2 e).1 (lc_inj pd.hd Z (bb gz).1 (bb gz).2 (bb gz').1 (bb gz').2 e).2)
  obtain ⟨j0f, j0b⟩ := (leg_jump pd h8 hal b (m := 0) (by omega)).resolve_right (by norm_num)
  obtain ⟨j2f, -⟩ := (leg_jump pd h8 hal b (m := 0 + 2) (by omega)).resolve_right (by norm_num)
  replace hb0 : blank B0 = a0 := hb0
  have hB0a0 : B0 a0 = 0 := by rw [← hb0]; exact apply_blank B0
  have htya0 : ty ≠ a0 := ne_of_rkey L (by rw [hty, ka0]; exact hEb.symm)
  have hbudget : 7 * (sqDist E Z * s + 5) ≤ 21 * (sqDist E Z * s + 5) + 10 * σ + 600 * k + 3000 := by
    omega
  by_cases htz : ty = z0
  · obtain ⟨pj, hpj⟩ := j0f B0 hb0
    refine ⟨swapCells B0 (blank B0) z0, pj, ?_, ?_, ?_, ?_, hpj.trans hbudget⟩
    · rw [hb0, swapCells_at_left, htz]
    · rw [blank_swapCells]; exact inBoxOf_lc pd Z gz
    · intro x h1 h2
      exact swapCells_preserves B0 h2 (fun e => h1 (by rw [e]; exact kz0))
    · have := keepK_of_agree_outside (rkey L s σ pd.hd) (B := B0)
        (C := swapCells B0 (blank B0) z0) {a0, z0}
        (fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
          exact swapCells_preserves B0 (by rw [hb0]; exact hx.1) hx.2)
      have e2 : B0 z0 = B0 ty := by rw [htz]
      rw [Finset.image_insert, Finset.image_singleton, hB0a0, e2] at this
      exact KeepK.erase_zero this
  -- a spare cell of the port, not `ty`
  obtain ⟨i, hi, hut⟩ : ∃ i : Fin 3, i.val ≤ 1 ∧
      lc (n := n) s Z (spare k s b i).1 (spare k s b i).2 ≠ ty := by
    by_cases h0 : lc (n := n) s Z (spare k s b 0).1 (spare k s b 0).2 = ty
    · refine ⟨1, by simp, fun h1 => ?_⟩
      have := spare_lt pd b 0
      have := spare_lt pd b 1
      have e := lc_inj pd.hd Z (by omega) (by omega) (by omega) (by omega) (h0.trans h1.symm)
      exact absurd (spare_inj hf b (Prod.ext e.1 e.2)) (by decide)
    · exact ⟨0, by simp, h0⟩
  set u : Cell n := lc s Z (spare k s b i).1 (spare k s b i).2 with hu
  have gu := spare_box (by omega) hf b i
  have ku : rkey L s σ pd.hd u = some (Z, some b) := rkey_box L pd Z gu
  have hua0 : u ≠ a0 := ne_of_rkey L (by rw [ku, ka0]; exact hEb.symm)
  have hsl := spare_lt pd b i
  have huz0 : u ≠ z0 := fun e => (gsp i).1 (Prod.ext (lc_inj pd.hd Z hsl.1 hsl.2 (bb gz).1
    (bb gz).2 e).1 (lc_inj pd.hd Z hsl.1 hsl.2 (bb gz).1 (bb gz).2 e).2)
  have huz1 : u ≠ z1 := fun e => (gsp i).2 (Prod.ext (lc_inj pd.hd Z hsl.1 hsl.2 (bb gz').1
    (bb gz').2 e).1 (lc_inj pd.hd Z hsl.1 hsl.2 (bb gz').1 (bb gz').2 e).2)
  set U : Cell n → Prop := fun x => x = ty ∨ x = u ∨ x = z1 with hU
  have hUa : ¬ U a0 := by
    rintro (e | e | e)
    · exact htya0 e.symm
    · exact hua0 e.symm
    · exact ha0z1 e
  set B1 := swapCells B0 (blank B0) z0 with hB1
  have hbB1 : blank B1 = z0 := blank_swapCells B0 _
  have hB1x : ∀ x, x ≠ a0 → x ≠ z0 → B1 x = B0 x := fun x h1 h2 =>
    swapCells_preserves B0 (by rw [hb0]; exact h1) h2
  obtain ⟨M, pm, hbM, hpm, hMx, hMz1, hMtu, hMeq⟩ : ∃ M : Board n, ∃ p : Path B1 M,
      blank M = z0 ∧ p.inefficientMoves ≤ 10 * σ + 600 * k + 3000 ∧
      (∀ x, ¬ U x → M x = B1 x) ∧ M z1 = B0 ty ∧
      (ty ≠ z1 → M ty = B1 u ∧ M u = B1 z1) ∧ (ty = z1 → ∀ x, M x = B1 x) := by
    by_cases htz1 : ty = z1
    · refine ⟨B1, .nil B1, hbB1, by simp [Path.inefficientMoves], fun _ _ => rfl, ?_,
        fun h => absurd htz1 h, fun _ _ => rfl⟩
      rw [← htz1, hB1x ty htya0 htz]
    obtain ⟨M, pm, hpm, hMa, hMb, hMc, hbM, hMx⟩ := port_cycle L pd h8 B1 Z b gz gz' gu hbB1 hty
      gcz gcz' (cdist_spare hf b i) (Ne.symm htz1) (Ne.symm huz1) (Ne.symm hut)
      (by rw [hbB1]; exact Ne.symm hz0z1) (by rw [hbB1]; exact htz) (by rw [hbB1]; exact huz0)
    refine ⟨M, pm, hbM.trans hbB1, hpm,
      fun x hx => hMx x (fun e => hx (Or.inr (Or.inr e))) (fun e => hx (Or.inl e))
        (fun e => hx (Or.inr (Or.inl e))), by rw [hMa, hB1x ty htya0 htz], fun _ => ⟨hMb, hMc⟩,
      fun h => absurd h htz1⟩
  obtain ⟨C, pc, hCa, hbC, hCz0, hCx, hic⟩ := dance B0 hb0 ha0z0 hz0z1 ha0z1 U hUa
    (7 * (sqDist E Z * s + 5)) (10 * σ + 600 * k + 3000) (j0f B0 hb0) j0b j2f M pm hbM hpm hMx
  have hCt : ∀ x, x ≠ a0 → x ≠ z0 → x ≠ z1 → ¬ U x → C x = B0 x := fun x h1 h2 h3 h4' =>
    (hCx x h1 h2 h3).trans ((hMx x h4').trans (hB1x x h1 h2))
  have hW : ∀ x, ¬ (x = a0 ∨ x = z0 ∨ x = z1 ∨ x = ty ∨ x = u) → C x = B0 x := by
    intro x hx
    simp only [not_or] at hx
    exact hCt x hx.1 hx.2.1 hx.2.2.1 (by
      rintro (e | e | e)
      · exact hx.2.2.2.1 e
      · exact hx.2.2.2.2 e
      · exact hx.2.2.1 e)
  refine ⟨C, pc, by rw [hb0, hCa, hMz1], by rw [hbC]; exact inBoxOf_lc pd Z gz', ?_, ?_,
    le_of_le_of_eq hic (by ring)⟩
  · intro x h1 h2
    exact hW x (by
      rintro (e | e | e | e | e)
      · exact h2 (e.trans hb0.symm)
      · exact h1 (by rw [e]; exact kz0)
      · exact h1 (by rw [e]; exact kz1)
      · exact h1 (by rw [e]; exact hty)
      · exact h1 (by rw [e]; exact ku))
  · have K := keepK_of_block (rkey L s σ pd.hd) (B := B0) (C := C)
      (fun x => x = a0 ∨ x = z0 ∨ x = z1 ∨ x = ty ∨ x = u) (some (Z, some b))
      (a := a0) (c := a0) (Ta := B0 ty) (Tc := B0 ty) hW
      (fun x hx h1 _ => by
        rcases hx with e | e | e | e | e
        · exact absurd e h1
        · rw [e]; exact kz0
        · rw [e]; exact kz1
        · rw [e]; exact hty
        · rw [e]; exact ku)
      (by rw [hCa, hMz1]) (by rw [hCa, hMz1]) (Or.inl (by rw [hB0a0]; rfl))
      (Or.inl (by rw [hB0a0]; rfl))
    simpa using K

end SlidingPuzzle.Port

namespace SlidingPuzzle.Port
open Classical
open SlidingPuzzle.Hub (Sq HDims sqOf classOf sqDist apply_blank blank_eq_of_apply
  val_ne_zero_of_ne_blank)
open SlidingPuzzle.Tree

variable {n k s q σ : ℕ} [NeZero n] (L : LaneSys k q)

/-- A leg carrying a tile from part `p ≠ b` of `Z` to `E`'s port `b`; a tile of `Z`'s port `b`
takes its place. -/
theorem leg_other (pd : PDims n k s q σ) (h8 : 8 ≤ σ) (B0 : Board n) {E Z : Sq k} (hEZ : E ≠ Z)
    (hal : E.1 = Z.1 ∨ E.2 = Z.2) (b : Pt)
    (hb0 : blank B0 = lc s E (ncell k s b).1 (ncell k s b).2)
    {p : Part} (hp : p ≠ some b) {ty tz : Cell n} (hty : rkey L s σ pd.hd ty = some (Z, p))
    (htz : rkey L s σ pd.hd tz = some (Z, some b)) :
    ∃ C : Board n, ∃ p' : Path B0 C, C (blank B0) = B0 ty ∧ C ty = B0 tz ∧
      InBoxOf s σ Z b (blank C) ∧
      (∀ x, rkey L s σ pd.hd x ≠ some (Z, some b) → x ≠ blank B0 → x ≠ ty → C x = B0 x) ∧
      KeepK (rkey L s σ pd.hd) B0 C {B0 ty, B0 tz} ∧
      p'.inefficientMoves ≤ 21 * (sqDist E Z * s + 5) + 10 * s + 10 * σ + 1200 * k + 6000 := by
  have hf := pd.fit
  have bb : ∀ {r c : ℕ}, inBox k s σ b r c → r < s ∧ c < s := fun h => by
    have := box_bounds pd b; rw [inBox_iff (by omega)] at h; omega
  -- the first jump avoids the class-`z` tile
  set m0 : ℕ := if lc (n := n) s Z (lz k s b (legHor E Z) (legJ s E Z) 0).1
      (lz k s b (legHor E Z) (legJ s E Z) 0).2 = tz then 2 else 0 with hm0
  have hm0' : m0 ≤ 2 := by rw [hm0]; split_ifs <;> omega
  obtain ⟨ga, gz, gz', gsp, gcz, gcz', gne⟩ := legCells pd h8 E Z b (m := m0) hm0'
  set a := ncell k s b
  set w0 := lz k s b (legHor E Z) (legJ s E Z) m0
  set w1 := lz k s b (legHor E Z) (legJ s E Z) (m0 + 2)
  set a0 : Cell n := lc s E a.1 a.2
  set z0 : Cell n := lc s Z w0.1 w0.2
  set z1 : Cell n := lc s Z w1.1 w1.2
  have hz0tz : z0 ≠ tz := by
    intro e
    by_cases h : lc (n := n) s Z (lz k s b (legHor E Z) (legJ s E Z) 0).1
      (lz k s b (legHor E Z) (legJ s E Z) 0).2 = tz
    · have hm : m0 = 2 := by rw [hm0, if_pos h]
      have hj : legJ s E Z ≤ 1 := by unfold legJ; split_ifs <;> omega
      obtain ⟨-, g0, -⟩ := lgeom (k := k) h8 hf b (legHor E Z) hj (m := 0) (by omega)
      obtain ⟨-, g2, -⟩ := lgeom (k := k) h8 hf b (legHor E Z) hj (m := 2) (by omega)
      have e' := h.trans e.symm
      simp only [z0, w0, hm] at e'
      have := lc_inj pd.hd Z (bb g0).1 (bb g0).2 (bb g2).1 (bb g2).2 e'
      exact lz_ne (k := k) (s := s) (b := b) (hor := legHor E Z) (j := legJ s E Z) (m := 0) (m' := 2)
        (by omega) (by omega) (by omega) (by omega) (Prod.ext this.1 this.2)
    · have hm : m0 = 0 := by rw [hm0, if_neg h]
      apply h
      simp only [z0, w0, hm] at e
      exact e
  have ka0 : rkey L s σ pd.hd a0 = some (E, some b) := rkey_box L pd E ga
  have kz0 : rkey L s σ pd.hd z0 = some (Z, some b) := rkey_box L pd Z gz
  have kz1 : rkey L s σ pd.hd z1 = some (Z, some b) := rkey_box L pd Z gz'
  have hEb : ∀ pp : Part, (some (E, some b) : Option (Sq k × Part)) ≠ some (Z, pp) := by
    intro pp; simp [hEZ]
  have hpb : (some (Z, p) : Option (Sq k × Part)) ≠ some (Z, some b) := by simp [hp]
  have ha0z0 : a0 ≠ z0 := ne_of_rkey L (by rw [ka0, kz0]; exact hEb _)
  have ha0z1 : a0 ≠ z1 := ne_of_rkey L (by rw [ka0, kz1]; exact hEb _)
  have hz0z1 : z0 ≠ z1 := fun e => gne (Prod.ext (lc_inj pd.hd Z (bb gz).1 (bb gz).2 (bb gz').1
    (bb gz').2 e).1 (lc_inj pd.hd Z (bb gz).1 (bb gz).2 (bb gz').1 (bb gz').2 e).2)
  obtain ⟨j0f, j0b⟩ := (leg_jump pd h8 hal b (m := m0) (by omega)).resolve_right
    (by rw [hm0]; split_ifs <;> norm_num)
  obtain ⟨j2f, -⟩ := (leg_jump pd h8 hal b (m := m0 + 2) (by omega)).resolve_right
    (by rw [hm0]; split_ifs <;> norm_num)
  replace hb0 : blank B0 = a0 := hb0
  have hB0a0 : B0 a0 = 0 := by rw [← hb0]; exact apply_blank B0
  have htya0 : ty ≠ a0 := ne_of_rkey L (by rw [hty, ka0]; exact (hEb _).symm)
  have htza0 : tz ≠ a0 := ne_of_rkey L (by rw [htz, ka0]; exact (hEb _).symm)
  have htyz0 : ty ≠ z0 := ne_of_rkey L (by rw [hty, kz0]; exact hpb)
  have htyz1 : ty ≠ z1 := ne_of_rkey L (by rw [hty, kz1]; exact hpb)
  have htytz : ty ≠ tz := ne_of_rkey L (by rw [hty, htz]; exact hpb)
  -- the cells `g` (receiving the class-`z` tile) and `u1`
  set g : Cell n := lc s Z (spare k s b 0).1 (spare k s b 0).2 with hg
  have gg := spare_box (by omega) hf b 0
  have kg : rkey L s σ pd.hd g = some (Z, some b) := rkey_box L pd Z gg
  have hsg := spare_lt pd b 0
  have hgz0 : g ≠ z0 := fun e => (gsp 0).1 (Prod.ext (lc_inj pd.hd Z hsg.1 hsg.2 (bb gz).1
    (bb gz).2 e).1 (lc_inj pd.hd Z hsg.1 hsg.2 (bb gz).1 (bb gz).2 e).2)
  have hgz1 : g ≠ z1 := fun e => (gsp 0).2 (Prod.ext (lc_inj pd.hd Z hsg.1 hsg.2 (bb gz').1
    (bb gz').2 e).1 (lc_inj pd.hd Z hsg.1 hsg.2 (bb gz').1 (bb gz').2 e).2)
  have hga0 : g ≠ a0 := ne_of_rkey L (by rw [kg, ka0]; exact (hEb _).symm)
  have htyg : ty ≠ g := ne_of_rkey L (by rw [hty, kg]; exact hpb)
  set B1 := swapCells B0 (blank B0) z0 with hB1
  have hbB1 : blank B1 = z0 := blank_swapCells B0 _
  have hB1x : ∀ x, x ≠ a0 → x ≠ z0 → B1 x = B0 x := fun x h1 h2 =>
    swapCells_preserves B0 (by rw [hb0]; exact h1) h2
  set U : Cell n → Prop := fun x => rkey L s σ pd.hd x = some (Z, some b) ∨ x = ty with hU
  have hUa : ¬ U a0 := by
    rintro (e | e)
    · rw [ka0] at e; exact hEb _ e
    · exact htya0 e.symm
  -- the middle: put the class-`z` tile on `g`, then the three-cycle in the square
  obtain ⟨M1, pm1, hbM1, hpm1, hM1g, hM1x⟩ : ∃ M1 : Board n, ∃ p : Path B1 M1, blank M1 = z0 ∧
      p.inefficientMoves ≤ 10 * σ + 600 * k + 3000 ∧ M1 g = B0 tz ∧
      ∀ x, rkey L s σ pd.hd x ≠ some (Z, some b) → M1 x = B1 x := by
    by_cases htg : tz = g
    · exact ⟨B1, .nil B1, hbB1, by simp [Path.inefficientMoves],
        by rw [← htg, hB1x tz htza0 (Ne.symm hz0tz)], fun _ _ => rfl⟩
    obtain ⟨i, hi1, hi2, hut⟩ : ∃ i : Fin 3, 1 ≤ i.val ∧ i.val ≤ 2 ∧
        lc (n := n) s Z (spare k s b i).1 (spare k s b i).2 ≠ tz := by
      by_cases h0 : lc (n := n) s Z (spare k s b 1).1 (spare k s b 1).2 = tz
      · refine ⟨2, by simp, by simp, fun h1 => ?_⟩
        have := spare_lt pd b 1
        have := spare_lt pd b 2
        have e := lc_inj pd.hd Z (by omega) (by omega) (by omega) (by omega) (h0.trans h1.symm)
        exact absurd (spare_inj hf b (Prod.ext e.1 e.2)) (by decide)
      · exact ⟨1, by simp, by simp, h0⟩
    set u : Cell n := lc s Z (spare k s b i).1 (spare k s b i).2 with hu
    have gu := spare_box (by omega) hf b i
    have hsu := spare_lt pd b i
    have hgu : g ≠ u := by
      intro e
      have e' := lc_inj pd.hd Z hsg.1 hsg.2 hsu.1 hsu.2 e
      have := spare_inj hf b (Prod.ext e'.1 e'.2)
      rw [Fin.ext_iff] at this; simp at this; omega
    have huz0 : u ≠ z0 := fun e => (gsp i).1 (Prod.ext (lc_inj pd.hd Z hsu.1 hsu.2 (bb gz).1
      (bb gz).2 e).1 (lc_inj pd.hd Z hsu.1 hsu.2 (bb gz).1 (bb gz).2 e).2)
    obtain ⟨M1, pm1, hpm1, hMa, -, -, hbM1, hMx⟩ := port_cycle L pd h8 B1 Z b gz gg gu hbB1 htz
      gcz (cdist_spare hf b 0) (cdist_spare hf b i) (Ne.symm htg) hgu (Ne.symm hut)
      (by rw [hbB1]; exact hgz0) (by rw [hbB1]; exact Ne.symm hz0tz) (by rw [hbB1]; exact huz0)
    refine ⟨M1, pm1, hbM1.trans hbB1, hpm1, by rw [hMa, hB1x tz htza0 (Ne.symm hz0tz)], ?_⟩
    intro x hx
    exact hMx x (fun e => hx (by rw [e]; exact kg)) (fun e => hx (by rw [e]; exact htz))
      (fun e => hx (by rw [e]; exact rkey_box L pd Z gu))
  obtain ⟨M, pm2, hpm2, hMz1, hMty, -, hbM, hMx⟩ := square_cycle L pd h8 M1 Z b gz gz' gg
    (by rw [hbM1]) hty gcz gcz' (cdist_spare hf b 0) (Ne.symm htyz1) (Ne.symm hgz1) htyg
    (by rw [hbM1]; exact Ne.symm hz0z1) (by rw [hbM1]; exact htyz0) (by rw [hbM1]; exact hgz0)
  have hM1ty : M1 ty = B0 ty := by
    rw [hM1x ty (by rw [hty]; exact hpb), hB1x ty htya0 htyz0]
  obtain ⟨C, pc, hCa, hbC, hCz0, hCx, hic⟩ := dance B0 hb0 ha0z0 hz0z1 ha0z1 U hUa
    (7 * (sqDist E Z * s + 5)) (10 * σ + 600 * k + 3000 + (10 * s + 600 * k + 3000))
    (j0f B0 hb0) j0b j2f M (pm1.append pm2) (hbM.trans hbM1)
    (by rw [Path.inefficientMoves_append]; omega)
    (fun x hx => by
      simp only [hU, not_or] at hx
      rw [hMx x (fun e => hx.1 (by rw [e]; exact kz1)) hx.2 (fun e => hx.1 (by rw [e]; exact kg)),
        hM1x x hx.1])
  have hW : ∀ x, ¬ (x = a0 ∨ x = ty ∨ rkey L s σ pd.hd x = some (Z, some b)) → C x = B0 x := by
    intro x hx
    simp only [not_or] at hx
    have hxz0 : x ≠ z0 := fun e => hx.2.2 (by rw [e]; exact kz0)
    have hxz1 : x ≠ z1 := fun e => hx.2.2 (by rw [e]; exact kz1)
    rw [hCx x hx.1 hxz0 hxz1, hMx x (fun e => hx.2.2 (by rw [e]; exact kz1)) hx.2.1
      (fun e => hx.2.2 (by rw [e]; exact kg)), hM1x x hx.2.2, hB1x x hx.1 hxz0]
  have hCty : C ty = B0 tz := by
    rw [hCx ty htya0 htyz0 htyz1, hMty, hM1g]
  refine ⟨C, pc, by rw [hb0, hCa, hMz1, hM1ty], hCty, by rw [hbC]; exact inBoxOf_lc pd Z gz', ?_, ?_,
    le_of_le_of_eq hic (by ring)⟩
  · intro x h1 h2 h3
    exact hW x (by
      rintro (e | e | e)
      · exact h2 (e.trans hb0.symm)
      · exact h3 e
      · exact h1 e)
  · exact keepK_of_block (rkey L s σ pd.hd) (B := B0) (C := C)
      (fun x => x = a0 ∨ x = ty ∨ rkey L s σ pd.hd x = some (Z, some b)) (some (Z, some b))
      (a := a0) (c := ty) (Ta := B0 ty) (Tc := B0 tz) hW
      (fun x hx h1 h2 => by
        rcases hx with e | e | e
        · exact absurd e h1
        · exact absurd e h2
        · exact e)
      (by rw [hCa, hMz1, hM1ty]) hCty (Or.inl (by rw [hB0a0]; rfl)) (Or.inr (Or.inl rfl))

end SlidingPuzzle.Port
