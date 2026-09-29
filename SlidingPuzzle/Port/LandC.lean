import SlidingPuzzle.Port.LandR

/-! # Landing of a column lane from its port

Lanes after their landing band (`side`) drop their head on row `s - 1` of the
landing band (a jump of `q + 1` over the next band's row group), lanes before it
on row `k` (a jump of `k + 1` over the band's row group and strip). The blank comes
from the port box by a horizontal jump. -/
namespace SlidingPuzzle.Port
open Classical
open SlidingPuzzle.Hub (Sq HDims sqOf classOf mkCell mkCell_fst mkCell_snd cell_ext
  div_eq_iff_bounds moveCost moveCost_le_one exists_move_step exists_vjump_step exists_hjump_step)
open SlidingPuzzle.Hub.LayoutAux
open SlidingPuzzle.Tree

variable {n k s q σ : ℕ} (L : LaneSys k q)

/-- The insertion position of a column hop: in the source band, on the row where the lane's
side drops its heads. -/
theorem colPosP_geom (td : TDims n k s q) (V : LaneI k q) (I : Fin k) (hI : LIn L V I) :
    colPosP k s q V I < colLen L s V ∧ cBand s q V (colPosP k s q V I) = I.val ∧
      cOff s q V (colPosP k s q V I) = (if V.side then s - 1 else k) := by
  have hks := td.k_lt_s
  have hm : 0 < s - q := by have := td.q_lt_s; omega
  have hqk := td.q_le
  unfold LIn InPiece at hI
  unfold colPosP colLen cBand cOff LaneSys.pdist
  cases h : V.side
  · simp only [h, Bool.false_eq_true, if_false] at hI ⊢
    have hd1 : Nat.dist I.val V.t.val - 1 = V.t.val - I.val - 1 := by unfold Nat.dist; omega
    rw [hd1]
    have d := divmod (b := V.t.val - I.val - 1) (show s - 1 - k < s - q by omega)
    rw [d.1, d.2]
    refine ⟨?_, by omega, by omega⟩
    have := Nat.mul_le_mul_right (s - q) (show V.t.val - I.val - 1 + 1 ≤ blen L V by omega)
    rw [add_mul, one_mul] at this
    omega
  · simp only [h, if_true] at hI ⊢
    have hd1 : Nat.dist I.val V.t.val - 1 = I.val - V.t.val - 1 := by unfold Nat.dist; omega
    rw [hd1]
    have d := divmod (b := I.val - V.t.val - 1) (show s - 1 - q < s - q by omega)
    rw [d.1, d.2]
    refine ⟨?_, by omega, by omega⟩
    have := Nat.mul_le_mul_right (s - q) (show I.val - V.t.val - 1 + 1 ≤ blen L V by omega)
    rw [add_mul, one_mul] at this
    omega

variable [NeZero n]

/-- The drop cell of a column lane: row `s - 1` (`side`) or `k` of the landing band. -/
def dropC (k s : ℕ) (V : LaneI k q) : Cell n :=
  lc s (colLand V) (if V.side then s - 1 else k) V.o.val

theorem lport_col (V : LaneI k q) : lport ((true, V) : Ln k q) = if V.side then .bl else .tl := by
  unfold lport; rfl

theorem dropC_coords (pd : PDims n k s q σ) (V : LaneI k q) :
    (dropC (n := n) k s V).1.val = V.t.val * s + (if V.side then s - 1 else k) ∧
      (dropC (n := n) k s V).2.val = V.b.val * s + V.o.val := by
  have hq := V.o.isLt
  have hqk := pd.td.q_le
  have hks := pd.td.k_lt_s
  exact ⟨lc_fst pd.hd _ _ (by split_ifs <;> omega), lc_snd pd.hd _ _ (by omega)⟩

theorem rkey_dropC (pd : PDims n k s q σ) (V : LaneI k q) (hpos : 0 < blen L V) :
    rkey L s σ pd.hd (dropC (n := n) k s V) = some (colLand V, some (lport ((true, V) : Ln k q))) := by
  have hq := V.o.isLt
  have hqk := pd.td.q_le
  have hks := pd.td.k_lt_s
  obtain ⟨h1, h2⟩ := dropC_coords (n := n) pd V
  have hreg := region_ownCol L pd.td V hpos h1 (by split_ifs <;> omega) (by split_ifs <;> omega) h2
  obtain ⟨-, d2, -, d4⟩ := lc_div (n := n) pd.hd (colLand V) (r := if V.side then s - 1 else k)
    (c := V.o.val) (by split_ifs <;> omega) (by omega)
  apply rkey_line L pd hreg
  unfold dropC
  rw [d2, d4, lport_col]
  cases V.side <;> simp [onLine]

theorem not_inBoxOf_dropC (pd : PDims n k s q σ) (V : LaneI k q) (pt : Pt) :
    ¬ InBoxOf s σ (colLand V) pt (dropC (n := n) k s V) := by
  rintro ⟨-, -, h⟩
  have hq := V.o.isLt
  have hqk := pd.td.q_le
  have hks := pd.td.k_lt_s
  have hb := box_bounds pd pt
  obtain ⟨-, -, -, d4⟩ := lc_div (n := n) pd.hd (colLand V) (r := if V.side then s - 1 else k)
    (c := V.o.val) (by split_ifs <;> omega) (by omega)
  unfold dropC at h
  rw [d4, inBox_iff (by have := pd.fit; omega)] at h
  omega

/-- Landing of a column lane from its port and walk to the insertion position of band `I`. -/
theorem landC (pd : PDims n k s q σ) (h3 : 3 ≤ σ) (B : Board n) {V : LaneI k q} {I : Fin k}
    (hI : LIn L V I)
    (hbl : InBoxOf s σ (colLand V) (lport ((true, V) : Ln k q)) (blank B)) :
    ∃ C : Board n, ∃ p : Path B C, blank C = colCell s V (colPosP k s q V I) ∧
      (∀ r, r < colPosP k s q V I → C (colCell s V r) = B (colCell s V (r + 1))) ∧
      C (dropC k s V) = B (colCell s V 0) ∧
      (∀ x, ¬ InBoxOf s σ (colLand V) (lport ((true, V) : Ln k q)) x → x ≠ dropC k s V →
        (∀ r, r ≤ colPosP k s q V I → x ≠ colCell s V r) → C x = B x) ∧
      KeepK (rkey L s σ pd.hd) B C {B (colCell s V 0)} ∧
      p.inefficientMoves ≤ 2 * σ + 14 * k + 35 + 7 * (q + 2) * k +
        ((Finset.range (colPosP k s q V I + 1)).filter fun r =>
          ¬ colGood V (classOf pd.hd (B (colCell s V r)))).card := by
  set P := colPosP k s q V I with hP
  obtain ⟨hPl, -, -⟩ := colPosP_geom L pd.td V I hI
  rw [← hP] at hPl
  have hpos := blen_pos_of_in L hI
  have hq := V.o.isLt
  have hqk := pd.td.q_le
  have hks := pd.td.k_lt_s
  have hqs := pd.td.q_lt_s
  have hf := pd.fit
  have hm : 0 < s - q := by omega
  have hb1 := pd.td.band_le V.t.isLt
  have hb2 := pd.td.band_le V.b.isLt
  have hbs := blen_side L V
  obtain ⟨kk, hkk⟩ := pd.hd.even
  obtain ⟨qq, hqq⟩ := pd.td.even_q
  set D := colLand V with hD
  set pt := lport ((true, V) : Ln k q) with hpt
  set d := dropC (n := n) k s V with hd
  obtain ⟨dr, dc⟩ := dropC_coords (n := n) pd V
  rw [← hd] at dr dc
  -- the box cell next to the drop cell
  set j := (k + V.o.val + 1) % 2 with hj
  have hj1 : j ≤ 1 := by omega
  set wr := if V.side then s - 2 else k + 1 with hwr
  set w0 : Cell n := lc s D wr (k + 1 + j) with hw0
  have hw0box : inBox k s σ pt wr (k + 1 + j) := by
    rw [hpt, lport_col, hwr]
    cases V.side <;> simp only [inBox, if_true, if_false, Bool.false_eq_true] <;> omega
  have hw0in : InBoxOf s σ D pt w0 := inBoxOf_lc pd D hw0box
  have w0r : w0.1.val = V.t.val * s + wr := lc_fst pd.hd D _ (by rw [hwr]; split_ifs <;> omega)
  have w0c : w0.2.val = V.b.val * s + (k + 1 + j) := lc_snd pd.hd D _ (by omega)
  have hdw1 : Nat.dist w0.2.val d.2.val ≤ k + 2 := by
    rw [w0c, dc]; simp only [Nat.dist]; omega
  have hdw2 : Nat.dist w0.1.val d.1.val ≤ 1 := by
    rw [w0r, dr, hwr]; split_ifs <;> simp only [Nat.dist] <;> omega
  have hpw : (w0.1.val + w0.2.val + d.1.val + d.2.val) % 2 = 1 := by
    rw [w0r, w0c, dr, dc, hwr]
    split_ifs <;> omega
  -- the lane
  set f : ℕ → Cell n := fun t => colCell s V t with hfdef
  have hfk : ∀ t, t ≤ P → rkey L s σ pd.hd (f t) = none := fun t ht =>
    rkey_colCell L pd V t (by omega)
  obtain ⟨C, p, hbC, hC, hCd, hCx, K, hi⟩ := land_core L pd h3 B hbl hw0in
    (rkey_dropC L pd V hpos) (not_inBoxOf_dropC pd V pt) (7 * (k + 3))
    (fun B' hB' => by
      obtain ⟨p, hp⟩ := exists_hjump_step pd.hd.two_le_n B' d
        (by rw [hB']; exact hdw2) (by rw [hB']; exact hpw)
      exact ⟨p, hp.trans (by rw [hB']; omega)⟩)
    P f hfk
    (fun t t' ht ht' e => (colCell_inj L pd.td (by omega) (by omega) e).2)
    (7 * (k + 2))
    (fun B' hB' => by
      have f0 : (f 0).1.val = cBand s q V 0 * s + cOff s q V 0 :=
        colCell_fst L pd.td V 0 (by omega)
      have f0c : (f 0).2.val = V.b.val * s + V.o.val := colCell_snd pd.td V 0
      obtain ⟨z1, z2⟩ := cBand_zero (k := k) (s := s) (q := q) V
      rw [z1, z2] at f0
      cases e : V.side
      · simp only [e, Bool.false_eq_true, if_false] at dr f0
        have ht1 : 1 ≤ V.t.val := by have := hbs.2 e; omega
        have e1 : (V.t.val - 1) * s + s = V.t.val * s := by
          rw [← add_one_mul]; congr 1; omega
        obtain ⟨p, hp⟩ := exists_vjump_step pd.hd.two_le_n B' (f 0)
          (by rw [hB', dc, f0c]; simp [Nat.dist])
          (by rw [hB', dr, dc, f0, f0c]; omega)
        exact ⟨p, hp.trans (by rw [hB', dr, f0]; simp only [Nat.dist]; omega)⟩
      · simp only [e, if_true] at dr f0
        have e1 : (V.t.val + 1) * s = V.t.val * s + s := by ring
        obtain ⟨p, hp⟩ := exists_vjump_step pd.hd.two_le_n B' (f 0)
          (by rw [hB', dc, f0c]; simp [Nat.dist])
          (by rw [hB', dr, dc, f0, f0c]; omega)
        exact ⟨p, hp.trans (by rw [hB', dr, f0]; simp only [Nat.dist]; omega)⟩)
    (fun t T => if (t + 1) % (s - q) = 0 then 7 * (q + 2) else moveCost (f t) (f (t + 1)) T)
    (fun t ht B' hB' => by
      obtain ⟨hcol, hcase⟩ := colCell_step (n := n) L pd.td V t (by omega)
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · obtain ⟨r, hr⟩ := exists_vjump_step pd.hd.two_le_n B' (f (t + 1))
          (by rw [hB']; simp [f, hcol])
          (by
            rw [hB']
            have := congrArg Fin.val hcol
            unfold Nat.dist at h2
            simp only [f] at this ⊢
            omega)
        refine ⟨r, hr.trans ?_⟩
        rw [if_pos h1, hB']
        simp only [f] at h2 ⊢
        rw [h2]
      · obtain ⟨r, hr⟩ := exists_move_step B' (f (t + 1)) (by
          rw [hB']
          have := congrArg Fin.val hcol
          simp only [gridDistance, f, Nat.dist] at this ⊢
          cases e : V.side
          · have := h3 e; omega
          · have := h2 e; omega)
        exact ⟨r, hr.trans (by rw [if_neg h1, hB'])⟩)
  refine ⟨C, p, hbC, hC, hCd, hCx, K, ?_⟩
  have hterm : ∀ t ∈ Finset.range P,
      (if (t + 1) % (s - q) = 0 then 7 * (q + 2) else moveCost (f t) (f (t + 1)) (B (f (t + 1))))
        ≤ 7 * (q + 2) * (if (s - q) ∣ t + 1 then 1 else 0) +
          (if ¬ colGood V (classOf pd.hd (B (f (t + 1)))) then 1 else 0) := by
    intro t ht
    rw [Finset.mem_range] at ht
    by_cases h1 : (t + 1) % (s - q) = 0
    · rw [if_pos h1, if_pos (Nat.dvd_of_mod_eq_zero h1)]; omega
    · rw [if_neg h1, if_neg (fun h' => h1 (Nat.mod_eq_zero_of_dvd h'))]
      by_cases hg : colGood V (classOf pd.hd (B (f (t + 1))))
      · rw [moveCost_colCell (n := n) L pd.td V t (by omega) h1 _ hg]; simp
      · rw [if_pos hg]; have := moveCost_le_one (f t) (f (t + 1)) (B (f (t + 1))); omega
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.card_filter,
    Nat.card_multiples] at hsum
  have hdivk : P / (s - q) ≤ k := by
    apply Nat.div_le_of_le_mul
    have : colLen L s V ≤ k * (s - q) := by
      unfold colLen
      apply Nat.mul_le_mul_right
      have := V.t.isLt
      cases e : V.side
      · have := hbs.2 e; omega
      · have := hbs.1 e; omega
    rw [mul_comm]; omega
  have hj : ∑ t ∈ Finset.range P, (if ¬ colGood V (classOf pd.hd (B (f (t + 1)))) then 1 else 0)
      ≤ ((Finset.range (P + 1)).filter fun r =>
        ¬ colGood V (classOf pd.hd (B (colCell s V r)))).card := by
    rw [Finset.card_filter, Finset.sum_range_succ']
    exact Nat.le_add_right _ _
  have hmul : 7 * (q + 2) * (P / (s - q)) ≤ 7 * (q + 2) * k := Nat.mul_le_mul_left _ hdivk
  omega

end SlidingPuzzle.Port
