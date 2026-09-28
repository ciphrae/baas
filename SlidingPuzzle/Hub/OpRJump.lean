import SlidingPuzzle.Hub.OpJump

/-! # Designated jumps and restores

`rjump E Z a y`: the blank walks inside `E`'s reservoir onto the designated cell
`a` of `E` and jumps onto the designated cell `landB s E Z a` of `Z`, whose
recorded class-`y` tile goes to `E`'s designated cell `a`. One strip jump
instead of three.

`restore Z c y`: the blank walks next to the bottom-right corner of `Z`'s box
and a near-corner three-cycle puts a class-`y` tile of the region on the
designated cell `c`. -/
namespace SlidingPuzzle.Hub
open Classical

variable {n k s : ℕ} [NeZero n]

/-- The designated cells of `E` and `Z` lie on a line and the jump between them is odd. -/
theorem rjump_geom (hd : HDims n k s) {E Z : Sq k} (a : Bool)
    (hal : E.1 = Z.1 ∨ E.2 = Z.2) :
    ((dcell (n := n) k s E a).1.val + (dcell (n := n) k s E a).2.val +
        (dcell (n := n) k s Z (landB s E Z a)).1.val +
        (dcell (n := n) k s Z (landB s E Z a)).2.val) % 2 = 1 := by
  rw [dcell_fst hd, dcell_snd hd, dcell_fst hd, dcell_snd hd]
  have hroom := hd.room
  have hX : E.1.val * s + E.2.val * s + Z.1.val * s + Z.2.val * s =
      (E.1.val + E.2.val + Z.1.val + Z.2.val) * s := by ring
  unfold landB
  by_cases hc : ((E.1.val + E.2.val + Z.1.val + Z.2.val) * s + (if a then 1 else 0)) % 2 = 0
  · simp only [hc, decide_true, if_true]
    split_ifs at hc ⊢ <;> omega
  · simp only [hc, decide_false, Bool.false_eq_true, if_false]
    split_ifs at hc ⊢ <;> omega

/-- A designated jump realized on the board. -/
theorem simulate_rjump (hd : HDims n k s) {B : Board n} {σ : IState k} (hR : Rel hd B σ)
    {E Z : Sq k} {a : Bool} {y : Sq k} (hpre : σ.Pre s (.rjump E Z a y)) :
    ∃ C : Board n, ∃ p : Path B C, Rel hd C (σ.step s (.rjump E Z a y)) ∧
      p.inefficientMoves ≤ σ.cost s (.rjump E Z a y) := by
  obtain ⟨hbl, hEZ, hal, hdes⟩ := hpre
  obtain ⟨hRrow, hRcol, hRcnt, hRbl, hRd⟩ := hR
  rw [hbl] at hRbl
  set b := landB s E Z a with hb
  set dE : Cell n := dcell k s E a with hdE
  set dZ : Cell n := dcell k s Z b with hdZ
  have hZd := hRd Z b y hdes
  have hkE : keyOf hd dE = some E := keyOf_reservoir hd (reservoir_dcell hd E a)
  have hkZ : keyOf hd dZ = some Z := keyOf_reservoir hd (reservoir_dcell hd Z b)
  have hEZk : some E ≠ some Z := fun e => hEZ (Option.some.inj e)
  have hdEZ : dE ≠ dZ := ne_of_keyOf (by rw [hkE, hkZ]; exact hEZk)
  have hZE : ¬ reservoir k s E dZ := fun hr => by
    rw [keyOf_reservoir hd hr] at hkZ; exact hEZ (Option.some.inj hkZ)
  -- walk onto the designated cell of `E`
  obtain ⟨B1, p1, hbB1, hl1, hf1, hdc1⟩ :=
    exists_reservoir_walk hd B hRbl (reservoir_dcell hd E a)
  rw [← hdE] at hbB1
  have hcolor := rjump_geom (n := n) hd a hal
  rw [← hb, ← hdE, ← hdZ] at hcolor
  have hroom := hd.room
  have hE1 := dcell_fst (n := n) hd E a
  have hE2 := dcell_snd (n := n) hd E a
  have hZ1 := dcell_fst (n := n) hd Z b
  have hZ2 := dcell_snd (n := n) hd Z b
  rw [← hdE] at hE1 hE2; rw [← hdZ] at hZ1 hZ2
  -- the jump
  set C := swapCells B1 (blank B1) dZ with hCdef
  obtain ⟨p2, hp2⟩ : ∃ p : Path B1 C,
      p.inefficientMoves ≤ 7 * (sqDist E Z * s + 2) := by
    rcases hal with h | h
    · have hs1 : E.1.val * s = Z.1.val * s := by rw [h]
      have hd0 : sqDist E Z = Nat.dist E.2.val Z.2.val := by
        unfold sqDist; rw [h, Nat.dist_self, zero_add]
      have hdm := Nat.dist_mul_right E.2.val s Z.2.val
      obtain ⟨p, hp⟩ := exists_hjump_step hd.two_le_n B1 dZ
        (by rw [hbB1, hE1, hZ1, hs1]; simp [Nat.dist]) (by rw [hbB1]; exact hcolor)
      refine ⟨p, hp.trans ?_⟩
      rw [hbB1, hE2, hZ2, hd0]
      unfold Nat.dist at hdm ⊢
      split_ifs <;> omega
    · have hs2 : E.2.val * s = Z.2.val * s := by rw [h]
      have hd0 : sqDist E Z = Nat.dist E.1.val Z.1.val := by
        unfold sqDist; rw [h, Nat.dist_self, add_zero]
      have hdm := Nat.dist_mul_right E.1.val s Z.1.val
      obtain ⟨p, hp⟩ := exists_vjump_step hd.two_le_n B1 dZ
        (by rw [hbB1, hE2, hZ2, hs2]; simp only [Nat.dist]; split_ifs <;> omega)
        (by rw [hbB1]; exact hcolor)
      refine ⟨p, hp.trans ?_⟩
      rw [hbB1, hE1, hZ1, hd0]
      unfold Nat.dist at hdm ⊢
      omega
  have hbC : blank C = dZ := blank_swapCells B1 _
  have hCdE : C dE = B dZ := by
    rw [hCdef, ← hbB1, swapCells_at_left, hf1 dZ hZE]
  have hC : ∀ x, ¬ reservoir k s E x → x ≠ dZ → C x = B x := by
    intro x h1 h2
    rw [hCdef, swapCells_preserves B1 (by rw [hbB1]; exact fun e => h1 (e ▸ reservoir_dcell hd E a)) h2,
      hf1 x h1]
  have hT0 : (B dZ).val ≠ 0 := hZd.1
  have K1 : KeepKey hd B B1 ∅ := keepKey_of_agree hd (reservoir k s E)
    (fun x y hx hy => by rw [keyOf_reservoir hd hx, keyOf_reservoir hd hy]) hf1
  have K2 : KeepKey hd B1 C {0, B dZ} := by
    have := keepKey_of_agree_outside hd (B := B1) (C := C) {dE, dZ}
      (fun x hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        exact swapCells_preserves B1 (by rw [hbB1]; exact hx.1) hx.2)
    rwa [Finset.image_insert, Finset.image_singleton, ← hbB1, apply_blank,
      hf1 dZ hZE] at this
  have K : KeepKey hd B C {B dZ} := by
    intro t h0 ht
    apply (K1.trans K2) t h0
    simp only [Finset.empty_union, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun e => h0 (by rw [e]; rfl), fun e => ht (by rw [e]; simp)⟩
  have hcor : ∀ x, keyOf hd x = none → C x = B x := fun x hx =>
    hC x (fun hr => by rw [keyOf_reservoir hd hr] at hx; cases hx)
      (ne_of_keyOf (by rw [hx, hkZ]; simp))
  refine ⟨C, p1.append p2, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro H q hq
    simp only [IState.step]
    rw [hcor _ (keyOf_rowCell hd H q hq)]
    exact hRrow H q hq
  · intro V q hq
    simp only [IState.step]
    rw [hcor _ (keyOf_colCell hd V q hq)]
    exact hRcol V q hq
  · intro Q y'
    simp only [IState.step]
    have hkB : keyOf hd (position B (B dZ)) = some Z := by
      rw [show position B (B dZ) = dZ by simp [position]]; exact hkZ
    have hkC : keyOf hd (position C (B dZ)) = some E := by
      rw [position_eq_of_apply hCdE]; exact hkE
    rw [regionCount_move1 hd K hT0 (fun e => hEZ e.symm) hkB hkC Q y', hZd.2]
    have hc : regionCount hd B = σ.cnt := funext fun Q => funext fun y => hRcnt Q y
    rw [hc]
  · simp only [IState.step]
    rw [hbC]; exact reservoir_dcell hd Z b
  · intro Q c y' hdes'
    simp only [IState.step] at hdes'
    by_cases h1 : Q = Z ∧ c = b
    · rw [if_pos h1] at hdes'; cases hdes'
    rw [if_neg h1] at hdes'
    by_cases h2 : Q = E ∧ c = a
    · rw [if_pos h2] at hdes'
      obtain ⟨rfl, rfl⟩ := h2
      cases hdes'
      rw [← hdE, hCdE]; exact hZd
    rw [if_neg h2] at hdes'
    have hB := hRd Q c y' hdes'
    suffices C (dcell k s Q c) = B (dcell k s Q c) by rw [this]; exact hB
    have hkQ : keyOf hd (dcell (n := n) k s Q c) = some Q :=
      keyOf_reservoir hd (reservoir_dcell hd Q c)
    have hne2 : dcell (n := n) k s Q c ≠ dZ := by
      intro e
      by_cases hQ : Q = Z
      · subst hQ; exact h1 ⟨rfl, dcell_inj hd e⟩
      · rw [e, hkZ] at hkQ; exact hQ (Option.some.inj hkQ).symm
    have hne1 : dcell (n := n) k s Q c ≠ dE := by
      intro e
      by_cases hQ : Q = E
      · subst hQ; exact h2 ⟨rfl, dcell_inj hd e⟩
      · rw [e, hkE] at hkQ; exact hQ (Option.some.inj hkQ).symm
    rw [hCdef, swapCells_preserves B1 (by rw [hbB1]; exact hne1) hne2]
    by_cases hQ : Q = E
    · subst hQ
      exact hdc1 c (ne_blank_of_val hB.1) hne1
    · exact hf1 _ (fun hr => by rw [keyOf_reservoir hd hr] at hkQ
                                exact hQ (Option.some.inj hkQ).symm)
  · simp only [IState.cost, Path.inefficientMoves_append]
    have c1 := p1.inefficientMoves_le_length
    have e1 : (s + 3) * (3 + 7 * sqDist E Z) = 3 * s + 7 * (sqDist E Z * s) + 9 + 21 * sqDist E Z := by
      ring
    have e2 : 7 * (sqDist E Z * s + 2) = 7 * (sqDist E Z * s) + 14 := by ring
    omega

omit [NeZero n] in
/-- The corner of a restore: the blank next to the bottom-right corner, the
designated cell on it, the spare cell two rows up. -/
theorem restore_cornerDist (hd : HDims n k s) {Z : Sq k} {c : Bool} {j : ℕ} {w0 dc u : Cell n}
    (w0f : w0.1.val = Z.1.val * s + (s - 2)) (w0s : w0.2.val = Z.2.val * s + (s - 1))
    (hdc1 : dc.1.val = Z.1.val * s + (s - 1))
    (hdc2 : dc.2.val = Z.2.val * s + (s - 2) + (if c then 1 else 0))
    (huf : u.1.val = Z.1.val * s + (s - 3)) (hus : u.2.val = Z.2.val * s + (s - 3) + j)
    (hj : j ≤ 2) :
    cornerDist (Z.1.val * s) (Z.2.val * s) s true true w0 dc u ≤ 5 := by
  have hroom := hd.room
  unfold cornerDist reflC
  simp only [if_true]
  rw [w0f, w0s, hdc1, hdc2, huf, hus]
  have d1 : Nat.dist (Z.1.val * s + (s - 2)) (Z.1.val * s + (s - 1 - 1)) = 0 := by
    rw [show s - 1 - 1 = s - 2 by omega]; exact Nat.dist_self _
  have d2 : Nat.dist (Z.2.val * s + (s - 1)) (Z.2.val * s + (s - 1 - 0)) = 0 := by
    rw [Nat.sub_zero]; exact Nat.dist_self _
  have d3 : Nat.dist (Z.1.val * s + (s - 1)) (Z.1.val * s + (s - 1 - 0)) = 0 := by
    rw [Nat.sub_zero]; exact Nat.dist_self _
  have d4 : Nat.dist (Z.2.val * s + (s - 2) + (if c then 1 else 0)) (Z.2.val * s + (s - 1 - 0)) ≤ 1 := by
    simp only [Nat.dist]; split_ifs <;> omega
  have d5 : Nat.dist (Z.1.val * s + (s - 3)) (Z.1.val * s + (s - 1 - 0)) ≤ 2 := by
    simp only [Nat.dist]; omega
  have d6 : Nat.dist (Z.2.val * s + (s - 3) + j) (Z.2.val * s + (s - 1 - 0)) ≤ 2 := by
    simp only [Nat.dist]; omega
  omega

/-- A restore realized on the board. -/
theorem simulate_restore (hd : HDims n k s) {B : Board n} {σ : IState k} (hR : Rel hd B σ)
    {Z : Sq k} {c : Bool} {y : Sq k} (hpre : σ.Pre s (.restore Z c y)) :
    ∃ C : Board n, ∃ p : Path B C, Rel hd C (σ.step s (.restore Z c y)) ∧
      p.inefficientMoves ≤ σ.cost s (.restore Z c y) := by
  obtain ⟨hbl, hdes, hcnt⟩ := hpre
  obtain ⟨hRrow, hRcol, hRcnt, hRbl, hRd⟩ := hR
  rw [hbl] at hRbl
  have hroom := hd.room
  have hbig := hd.big
  have hb1 := hd.band_le Z.1.isLt
  have hb2 := hd.band_le Z.2.isLt
  set dc : Cell n := dcell k s Z c with hdc
  have hdc1 := dcell_fst (n := n) hd Z c
  have hdc2 := dcell_snd (n := n) hd Z c
  rw [← hdc] at hdc1 hdc2
  have hkdc : keyOf hd dc = some Z := keyOf_reservoir hd (reservoir_dcell hd Z c)
  -- walk next to the corner
  let w0 : Cell n := mkCell n (Z.1.val * s + (s - 2)) (Z.2.val * s + (s - 1))
  have w0f : w0.1.val = Z.1.val * s + (s - 2) := mkCell_fst (by omega)
  have w0s : w0.2.val = Z.2.val * s + (s - 1) := mkCell_snd (by omega)
  have hw0 : reservoir k s Z w0 := (reservoir_iff hd).mpr (by omega)
  have hw0d : ∀ c', dcell (n := n) k s Z c' ≠ w0 := fun c' e => by
    have := dcell_fst (n := n) hd Z c'; rw [e, w0f] at this; omega
  obtain ⟨B1, p1, hbB1, hl1, hf1, hdg1⟩ := exists_reservoir_walk hd B hRbl hw0
  have hK1 : KeepKey hd B B1 ∅ := keepKey_of_agree hd (reservoir k s Z)
    (fun x y hx hy => by rw [keyOf_reservoir hd hx, keyOf_reservoir hd hy]) hf1
  have hreg1 : ∀ Q y', regionCount hd B1 Q y' = regionCount hd B Q y' := by
    intro Q y'; have := regionCount_keepKey hd hK1 Q y'; simpa using this
  -- the recorded designated cells of the whole board are kept by the walk
  have hval1 : ∀ Q c' y', σ.des Q c' = some y' → B1 (dcell k s Q c') = B (dcell k s Q c') := by
    intro Q c' y' h
    by_cases hQ : Q = Z
    · subst hQ; exact hdg1 c' (ne_blank_of_val (hRd Q c' y' h).1) (hw0d c')
    · exact hf1 _ (fun hr => hQ (Option.some.inj
        ((keyOf_reservoir hd (reservoir_dcell (n := n) hd Q c')).symm.trans
          (keyOf_reservoir hd hr))))
  have hdc0 : (B1 dc).val ≠ 0 := val_ne_zero_of_ne_blank (by rw [hbB1]; exact hw0d c)
  -- general facts on the final board
  have final : ∀ C : Board n, ∀ p : Path B1 C,
      (∀ x, keyOf hd x ≠ some Z → C x = B1 x) → KeepKey hd B1 C ∅ → blank C = w0 →
      (C dc).val ≠ 0 → classOf hd (C dc) = y →
      (∀ c' y', σ.des Z c' = some y' → C (dcell k s Z c') = B1 (dcell k s Z c')) →
      p.inefficientMoves ≤ 11 * s →
      ∃ C : Board n, ∃ p : Path B C, Rel hd C (σ.step s (.restore Z c y)) ∧
        p.inefficientMoves ≤ σ.cost s (.restore Z c y) := by
    intro C p hout hK hbC h0 hcl hZd hp
    have hcor : ∀ x, keyOf hd x = none → C x = B x := fun x hx => by
      rw [hout x (by rw [hx]; simp), hf1 x (fun hr => by rw [keyOf_reservoir hd hr] at hx; cases hx)]
    refine ⟨C, p1.append p, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro H q hq
      rw [hcor _ (keyOf_rowCell hd H q hq)]; exact hRrow H q hq
    · intro V q hq
      rw [hcor _ (keyOf_colCell hd V q hq)]; exact hRcol V q hq
    · intro Q y'
      have := regionCount_keepKey hd hK Q y'
      simp only [Finset.filter_empty, Finset.card_empty, add_zero] at this
      rw [this, hreg1]; exact hRcnt Q y'
    · rw [hbC]; show reservoir k s σ.blank w0; rw [hbl]; exact hw0
    · intro Q c' y' h
      change (if Q = Z ∧ c' = c then some y else σ.des Q c') = some y' at h
      by_cases h1 : Q = Z ∧ c' = c
      · rw [if_pos h1] at h; cases h
        obtain ⟨rfl, rfl⟩ := h1
        exact ⟨h0, hcl⟩
      rw [if_neg h1] at h
      have hB := hRd Q c' y' h
      by_cases hQ : Q = Z
      · subst hQ; rw [hZd c' y' h, hval1 _ _ _ h]; exact hB
      · rw [hout _ (by rw [keyOf_reservoir hd (reservoir_dcell hd Q c')]
                       exact fun e => hQ (Option.some.inj e)), hval1 _ _ _ h]
        exact hB
    · simp only [IState.cost, Path.inefficientMoves_append]
      have := p1.inefficientMoves_le_length
      omega
  -- the designated cell may already hold a class-`y` tile
  by_cases hy : classOf hd (B1 dc) = y
  · exact final B1 (.nil B1) (fun _ _ => rfl) (KeepKey.refl hd B1 ∅) hbB1 hdc0 hy
      (fun _ _ _ => rfl) (by simp [Path.inefficientMoves])
  -- a class-`y` tile of the region, off the recorded designated cells
  obtain ⟨t, htF, htQ, htT, htc⟩ := exists_of_regionCount_avoid hd B1
    (validD (n := n) (s := s) σ Z y) (by
      have := card_validD_le (n := n) (s := s) σ Z y
      rw [hreg1, hRcnt]; exact (Nat.add_le_add_right this 1).trans hcnt)
  have htdc : t ≠ dc := fun e => hy (by rw [← e]; exact htc)
  have htd : ∀ c' y', σ.des Z c' = some y' → t ≠ dcell k s Z c' := by
    intro c' y' h e
    have h1 := (hRd Z c' y' h).2
    rw [← hval1 _ _ _ h, ← e, htc] at h1
    subst h1
    exact htF (e ▸ mem_validD h)
  obtain ⟨j, hj, hu, hut, huw⟩ := exists_reservoir_near hd Z (ro := s - 3) (co := s - 3)
    (by omega) (by omega) (by omega) (by omega) t w0
  set u := mkCell n (Z.1.val * s + (s - 3)) (Z.2.val * s + (s - 3) + j) with hudef
  have huf : u.1.val = Z.1.val * s + (s - 3) := mkCell_fst (by omega)
  have hus : u.2.val = Z.2.val * s + (s - 3) + j := mkCell_snd (by omega)
  have hku : keyOf hd u = some Z := keyOf_reservoir hd hu
  have hkt : keyOf hd t = some Z := (keyOf_eq_some hd).mpr htQ
  have hudc : u ≠ dc := fun e => by rw [e, hdc1] at huf; omega
  have hU0 : (B1 u).val ≠ 0 := val_ne_zero_of_ne_blank (by rw [hbB1]; exact huw)
  obtain ⟨C, p, hp, hCa, hCb, hCc, hCx⟩ := exists_box_three_cycle_near B1 (Z.1.val * s)
    (Z.2.val * s) s true true (by omega) (hd.band_le Z.1.isLt) (hd.band_le Z.2.isLt)
    (by rw [hbB1]; exact inBox_of_reservoir hd hw0) dc t u
    (inBox_of_reservoir hd (reservoir_dcell hd Z c)) (inBox_of_region hd htQ)
    (inBox_of_reservoir hd hu) htdc.symm hudc.symm (Ne.symm hut)
    (fun e => hdc0 (by rw [e]; rfl)) (fun e => htT (by rw [e]; rfl)) (fun e => hU0 (by rw [e]; rfl))
  have hcd : cornerDist (Z.1.val * s) (Z.2.val * s) s true true (blank B1) dc u ≤ 5 := by
    rw [hbB1]
    exact restore_cornerDist hd w0f w0s hdc1 hdc2 huf hus hj
  have hout : ∀ x, keyOf hd x ≠ some Z → C x = B1 x := by
    intro x hx
    apply hCx
    · rintro rfl; exact hx hkdc
    · rintro rfl; exact hx hkt
    · rintro rfl; exact hx hku
  refine final C p hout ?_ ?_ ?_ ?_ ?_ ?_
  · exact keepKey_of_agree hd (fun x => keyOf hd x = some Z)
      (fun x y hx hy => by rw [hx, hy]) (fun x hx => hout x hx)
  · apply blank_eq_of_apply
    rw [hCx w0 (fun e => hw0d c e.symm) (fun e => htT (by rw [← e, ← hbB1, apply_blank]; rfl))
      (fun e => huw e.symm)]
    rw [← hbB1]; exact apply_blank B1
  · rw [hCa]; exact htT
  · rw [hCa]; exact htc
  · intro c' y' h
    have hne : dcell (n := n) k s Z c' ≠ dc := by
      intro e
      have := dcell_inj hd e
      subst this
      rw [hdes] at h; cases h
    apply hCx _ hne (htd c' y' h).symm
    intro e; have := dcell_fst (n := n) hd Z c'; rw [e, huf] at this; omega
  · omega

end SlidingPuzzle.Hub
