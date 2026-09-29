import SlidingPuzzle.Port.Land

/-! # Landing of a row lane from its port

Lanes after their landing block (`side`) drop their head on column `s - 1` of the
landing block, next to position `0`; lanes before it on column `k`, reached from
position `0` by a horizontal jump over `k` strip cells. The blank comes from the
port box by a vertical jump. -/
namespace SlidingPuzzle.Port
open Classical
open SlidingPuzzle.Hub (Sq HDims sqOf classOf mkCell mkCell_fst mkCell_snd cell_ext
  div_eq_iff_bounds moveCost moveCost_le_one exists_move_step exists_vjump_step exists_hjump_step)
open SlidingPuzzle.Hub.LayoutAux
open SlidingPuzzle.Tree

variable {n k s q σ : ℕ} [NeZero n] (L : LaneSys k q)

/-- The drop cell of a row lane: column `s - 1` (`side`) or `k` of the landing block. -/
def dropR (s : ℕ) (H : LaneI k q) : Cell n :=
  lc s (rowLand H) H.o.val (if H.side then s - 1 else k)

theorem lport_row (H : LaneI k q) : lport ((false, H) : Ln k q) = if H.side then .tr else .tl := by
  unfold lport; rfl

theorem dropR_coords (pd : PDims n k s q σ) (H : LaneI k q) :
    (dropR (n := n) s H).1.val = H.b.val * s + H.o.val ∧
      (dropR (n := n) s H).2.val = H.t.val * s + (if H.side then s - 1 else k) := by
  have hq := H.o.isLt
  have hqk := pd.td.q_le
  have hks := pd.td.k_lt_s
  exact ⟨lc_fst pd.hd _ _ (by omega), lc_snd pd.hd _ _ (by split_ifs <;> omega)⟩

theorem rkey_dropR (pd : PDims n k s q σ) (H : LaneI k q) (hpos : 0 < blen L H) :
    rkey L s σ pd.hd (dropR (n := n) s H) = some (rowLand H, some (lport ((false, H) : Ln k q))) := by
  have hq := H.o.isLt
  have hqk := pd.td.q_le
  have hks := pd.td.k_lt_s
  obtain ⟨h1, h2⟩ := dropR_coords (n := n) pd H
  have hreg := region_strip L pd.td H hpos h1 h2 (by split_ifs <;> omega)
  obtain ⟨-, d2, -, d4⟩ := lc_div (n := n) pd.hd (rowLand H) (r := H.o.val)
    (c := if H.side then s - 1 else k) (by omega) (by split_ifs <;> omega)
  apply rkey_line L pd hreg
  unfold dropR
  rw [d2, d4, lport_row]
  cases H.side <;> simp [onLine]

theorem not_inBoxOf_dropR (pd : PDims n k s q σ) (H : LaneI k q) (pt : Pt) :
    ¬ InBoxOf s σ (rowLand H) pt (dropR (n := n) s H) := by
  rintro ⟨-, -, h⟩
  have hq := H.o.isLt
  have hqk := pd.td.q_le
  have hks := pd.td.k_lt_s
  have hb := box_bounds pd pt
  obtain ⟨-, d2, -, -⟩ := lc_div (n := n) pd.hd (rowLand H) (r := H.o.val)
    (c := if H.side then s - 1 else k) (by omega) (by split_ifs <;> omega)
  unfold dropR at h
  rw [d2, inBox_iff (by have := pd.fit; omega)] at h
  omega

/-- Landing of a row lane from its port and walk to the insertion position of block `J`. -/
theorem landR (pd : PDims n k s q σ) (h3 : 3 ≤ σ) (B : Board n) {H : LaneI k q} {J : Fin k}
    (hJ : LIn L H J)
    (hbl : InBoxOf s σ (rowLand H) (lport ((false, H) : Ln k q)) (blank B)) :
    ∃ C : Board n, ∃ p : Path B C, blank C = rowCell s H (rowPos k s H J) ∧
      (∀ r, r < rowPos k s H J → C (rowCell s H r) = B (rowCell s H (r + 1))) ∧
      C (dropR s H) = B (rowCell s H 0) ∧
      (∀ x, ¬ InBoxOf s σ (rowLand H) (lport ((false, H) : Ln k q)) x → x ≠ dropR s H →
        (∀ r, r ≤ rowPos k s H J → x ≠ rowCell s H r) → C x = B x) ∧
      KeepK (rkey L s σ pd.hd) B C {B (rowCell s H 0)} ∧
      p.inefficientMoves ≤ 2 * σ + 14 * k + 35 +
        ((Finset.range (rowPos k s H J + 1)).filter fun r =>
          ¬ rowGood H (classOf pd.hd (B (rowCell s H r)))).card := by
  set P := rowPos k s H J with hP
  obtain ⟨hPl, -⟩ := rowPos_geom L pd.td H J hJ
  rw [← hP] at hPl
  have hpos := blen_pos_of_in L hJ
  have hq := H.o.isLt
  have hqk := pd.td.q_le
  have hks := pd.td.k_lt_s
  have hf := pd.fit
  have hb1 := pd.td.band_le H.b.isLt
  have hb2 := pd.td.band_le H.t.isLt
  obtain ⟨kk, hkk⟩ := pd.hd.even
  set D := rowLand H with hD
  set pt := lport ((false, H) : Ln k q) with hpt
  set d := dropR (n := n) s H with hd
  obtain ⟨dr, dc⟩ := dropR_coords (n := n) pd H
  rw [← hd] at dr dc
  -- the box cell next to the drop cell
  set j := (k + H.o.val + 1) % 2 with hj
  have hj1 : j ≤ 1 := by omega
  set wc := if H.side then s - 2 else k + 1 with hwc
  set w0 : Cell n := lc s D (k + 1 + j) wc with hw0
  have hw0box : inBox k s σ pt (k + 1 + j) wc := by
    rw [hpt, lport_row, hwc]
    cases H.side <;> simp only [inBox, if_true, if_false, Bool.false_eq_true] <;> omega
  have hw0in : InBoxOf s σ D pt w0 := inBoxOf_lc pd D hw0box
  have w0r : w0.1.val = H.b.val * s + (k + 1 + j) := lc_fst pd.hd D _ (by omega)
  have w0c : w0.2.val = H.t.val * s + wc := lc_snd pd.hd D _ (by rw [hwc]; split_ifs <;> omega)
  have hdw1 : Nat.dist w0.1.val d.1.val ≤ k + 2 := by
    rw [w0r, dr]; simp only [Nat.dist]; omega
  have hdw2 : Nat.dist w0.2.val d.2.val ≤ 1 := by
    rw [w0c, dc, hwc]; split_ifs <;> simp only [Nat.dist] <;> omega
  have hpw : (w0.1.val + w0.2.val + d.1.val + d.2.val) % 2 = 1 := by
    rw [w0r, w0c, dr, dc, hwc]
    have e2 : ∀ x : ℕ, (x + x) % 2 = 0 := fun x => by omega
    split_ifs <;> omega
  -- the lane
  set f : ℕ → Cell n := fun t => rowCell s H t with hfdef
  have hfk : ∀ t, t ≤ P → rkey L s σ pd.hd (f t) = none := fun t ht =>
    rkey_rowCell L pd H t (by omega)
  have hfl : ∀ t, t ≤ P → f t = lineCell s H (s + t) := fun t ht =>
    (lineCell_rowCell L pd.td H t (by omega)).symm
  obtain ⟨C, p, hbC, hC, hCd, hCx, K, hi⟩ := land_core L pd h3 B hbl hw0in
    (rkey_dropR L pd H hpos) (not_inBoxOf_dropR pd H pt) (7 * (k + 3))
    (fun B' hB' => by
      obtain ⟨p, hp⟩ := exists_vjump_step pd.hd.two_le_n B' d
        (by rw [hB']; exact hdw2) (by rw [hB']; exact hpw)
      exact ⟨p, hp.trans (by rw [hB']; omega)⟩)
    P f hfk
    (fun t t' ht ht' e => (rowCell_inj L pd.td (by omega) (by omega) e).2)
    (7 * (k + 2))
    (fun B' hB' => by
      have f0 : (f 0).1.val = H.b.val * s + H.o.val := rowCell_fst pd.td H 0
      have f0c : (f 0).2.val = rowCol s H 0 := rowCell_snd L pd.td H 0 (by omega)
      unfold rowCol at f0c
      have ht1 : H.side = false → 1 ≤ H.t.val := fun e => by
        have := (blen_side L H).2 e; omega
      cases e : H.side
      · simp only [e, Bool.false_eq_true, if_false] at dc f0c
        have hts : s ≤ H.t.val * s := Nat.le_mul_of_pos_left s (by have := ht1 e; omega)
        obtain ⟨p, hp⟩ := exists_hjump_step pd.hd.two_le_n B' (f 0)
          (by rw [hB', dr, f0]; simp [Nat.dist])
          (by rw [hB', dr, dc, f0, f0c]; omega)
        exact ⟨p, hp.trans (by rw [hB', dc, f0c]; simp only [Nat.dist]; omega)⟩
      · simp only [e, if_true] at dc f0c
        have hadj : gridDistance d (f 0) = 1 := by
          unfold gridDistance
          rw [dr, dc, f0, f0c]
          simp only [Nat.dist]
          omega
        obtain ⟨p, hp⟩ := exists_move_step B' (f 0) (by rw [hB']; exact hadj)
        exact ⟨p, hp.trans ((moveCost_le_one _ _ _).trans (by omega))⟩)
    (fun t T => moveCost (f t) (f (t + 1)) T)
    (fun t ht B' hB' => by
      obtain ⟨p, hp⟩ := exists_move_step B' (f (t + 1)) (by
        rw [hB', hfl t (by omega), hfl (t + 1) (by omega)]
        have := lineCell_adj (n := n) L pd.td H (s + t) (by omega)
        rwa [show s + t + 1 = s + (t + 1) by ring] at this)
      exact ⟨p, hp.trans (by rw [hB'])⟩)
  refine ⟨C, p, hbC, hC, hCd, hCx, K, ?_⟩
  have hsum : ∑ t ∈ Finset.range P, moveCost (f t) (f (t + 1)) (B (f (t + 1))) ≤
      ((Finset.range (P + 1)).filter fun r =>
        ¬ rowGood H (classOf pd.hd (B (rowCell s H r)))).card := by
    rw [Finset.card_filter, Finset.sum_range_succ']
    refine le_trans (Finset.sum_le_sum fun t ht => ?_) (Nat.le_add_right _ _)
    rw [Finset.mem_range] at ht
    by_cases hg : rowGood H (classOf pd.hd (B (rowCell s H (t + 1))))
    · rw [if_neg (not_not.mpr hg), hfl t (by omega), hfl (t + 1) (by omega)]
      have e : lineCell (n := n) s H (s + (t + 1)) = lineCell s H (s + t + 1) := by
        congr 1
      rw [e, moveCost_lineCell (n := n) L pd.td H (s + t) (by omega) (by omega) _
        (by rw [← e, ← hfl (t + 1) (by omega)]; exact hg)]
    · rw [if_pos hg]; exact moveCost_le_one _ _ _
  omega

end SlidingPuzzle.Port
