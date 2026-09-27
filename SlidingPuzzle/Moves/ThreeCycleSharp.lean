import SlidingPuzzle.Moves.ThreeCycle

/-! # Three-cycles with a small linear constant

`exists_three_cycle` stages its three tiles with a general prefix placement
whose first step alone costs about `106 n`. Here the staging uses only the
sharp Parberry placements (`8 n` each): after moving the blank below the top-left
corner, the three tiles go to `(0,1), (0,2), (0,3)`, or, if one of them already
sits in the corner, the other two go to `(0,1), (0,2)`. A top-row three-cycle on
the staged columns and the reversed staging give `exists_three_cycle_sharp`, in
at most `52 n` moves. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

/-- Rotate the top-row cells `j, j+1, j+2` with the blank below `(0, j)`. -/
theorem exists_top_three_cycle_at (B : Board n) (hn : 4 ≤ n) (j : ℕ) (hj : j + 3 ≤ n)
    (hb : blank B = (⟨1, by omega⟩, ⟨j, by omega⟩)) :
    ∃ C : Board n, ∃ q : Path B C,
      q.length ≤ 24 ∧ blank C = blank B ∧
      C (0, ⟨j, by omega⟩) = B (0, ⟨j + 1, by omega⟩) ∧
      C (0, ⟨j + 1, by omega⟩) = B (0, ⟨j + 2, by omega⟩) ∧
      C (0, ⟨j + 2, by omega⟩) = B (0, ⟨j, by omega⟩) ∧
      ∀ x : Cell n, x ≠ (0, ⟨j, by omega⟩) → x ≠ (0, ⟨j + 1, by omega⟩) →
        x ≠ (0, ⟨j + 2, by omega⟩) → C x = B x := by
  classical
  let : NeZero (n*n) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne n)⟩
  let c₀ : Fin n := ⟨j, by omega⟩
  let c₁ : Fin n := ⟨j + 1, by omega⟩
  let c₂ : Fin n := ⟨j + 2, by omega⟩
  let p : Zhong.Cell 2 n := Zhong.bot c₀
  let u : Zhong.Cell 2 n := Zhong.top c₀
  let v : Zhong.Cell 2 n := Zhong.top c₁
  let w : Zhong.Cell 2 n := Zhong.top c₂
  have hc₀ : c₀.val + 2 * 0 + 1 < n := by simp [c₀]; omega
  have hc₁ : c₁.val + 2 * 0 + 1 < n := by simp [c₁]; omega
  have hc₀' : c₀.val + 2 * 0 < n := by simp [c₀]; omega
  have hlast : 2 * 1 ≤ c₂.val := by simp [c₂]
  have hreturn : (⟨c₂.val - 2 * 1, by omega⟩ : Fin n) = c₀ := by
    apply Fin.ext
    simp [c₀,c₂]
  have hpu : p ≠ u := by simp [p,u]
  have hpv : p ≠ v := by simp [p,v]
  have hpw : p ≠ w := by simp [p,w]
  have huv : u ≠ v := by simp [u,v,c₀,c₁,Fin.ext_iff]
  have huw : u ≠ w := by simp [u,w,c₀,c₂,Fin.ext_iff]
  have hvw : v ≠ w := by simp [v,w,c₁,c₂,Fin.ext_iff]
  let σ₁ := Zhong.flipJumpWord 0
  let σ₂ := Zhong.row0Word 0
  let σ₃ := Zhong.row0Word 0
  let σ₄ := Zhong.reflJumpWord 1
  let P := Equiv.swap p u * Equiv.swap u v * Equiv.swap v w * Equiv.swap w p
  have h₁ : Zhong.permOf p σ₁ = Equiv.swap p u := by
    have h := Zhong.permOf_flipJumpWord (m := n) (c := c₀) 0 hc₀'
    have e : (⟨c₀.val + 2 * 0, hc₀'⟩ : Fin n) = c₀ := Fin.ext (by simp)
    rw [e] at h
    exact h
  have h₂ : Zhong.permOf u σ₂ = Equiv.swap u v := by
    have h := Zhong.permOf_row0Word (m := n) (c := c₀) 0 hc₀
    have e : (⟨c₀.val + 2 * 0 + 1, hc₀⟩ : Fin n) = c₁ := Fin.ext (by simp [c₀, c₁])
    rw [e] at h
    exact h
  have h₃ : Zhong.permOf v σ₃ = Equiv.swap v w := by
    have h := Zhong.permOf_row0Word (m := n) (c := c₁) 0 hc₁
    have e : (⟨c₁.val + 2 * 0 + 1, hc₁⟩ : Fin n) = c₂ := Fin.ext (by simp [c₁, c₂])
    rw [e] at h
    exact h
  have h₄ : Zhong.permOf w σ₄ = Equiv.swap w p := by
    have h := Zhong.permOf_reflJumpWord (m := n) (c := c₂) 1 hlast
    rw [hreturn] at h
    exact h
  have ht₁ : Zhong.trace p σ₁ = u := Zhong.trace_eq_of_permOf_swap h₁
  have ht₂ : Zhong.trace u σ₂ = v := Zhong.trace_eq_of_permOf_swap h₂
  have ht₃ : Zhong.trace v σ₃ = w := Zhong.trace_eq_of_permOf_swap h₃
  let σ := ((σ₁ ++ σ₂) ++ σ₃) ++ σ₄
  have happ : Zhong.ApplicableFrom p σ := by
    change Zhong.ApplicableFrom p (((σ₁ ++ σ₂) ++ σ₃) ++ σ₄)
    rw [Zhong.applicableFrom_append,Zhong.applicableFrom_append,
      Zhong.applicableFrom_append]
    simp only [Zhong.trace_append,ht₁,ht₂,ht₃]
    exact ⟨⟨⟨Zhong.applicableFrom_flipJumpWord (m := n) (c := c₀) 0 hc₀',
        Zhong.applicableFrom_row0Word (m := n) (c := c₀) 0 hc₀⟩,
        Zhong.applicableFrom_row0Word (m := n) (c := c₁) 0 hc₁⟩,
      Zhong.applicableFrom_reflJumpWord (m := n) (c := c₂) 1 hlast⟩
  have hperm : Zhong.permOf p σ = P := by
    change Zhong.permOf p (((σ₁ ++ σ₂) ++ σ₃) ++ σ₄) = P
    exact Zhong.permOf_four_jumps σ₁ σ₂ σ₃ σ₄ h₁ ht₁ h₂ ht₂ h₃ ht₃ h₄
  have hlen : σ.length = 24 := by
    simp [σ,σ₁,σ₂,σ₃,σ₄,Zhong.flipJumpWord_length,
      Zhong.row0Word_length,Zhong.reflJumpWord_length]
  let ι := Zhong.hStrip (n := n) (m := n) 0 (by omega)
  have hfix (x : Zhong.Cell 2 n) (hx : x ∉ ({u,v,w} : Finset _)) : P x = x := by
    by_cases he : x = p
    · subst x
      exact Zhong.fourChain_apply_p hpu hpv hpw huv huw hvw
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      exact Zhong.fourChain_fixes he hx.1 hx.2.1 hx.2.2
  have hstart : ι p = blank B := by rw [hb]; rfl
  have hmap {a b : Zhong.Cell 2 n} (h : P a = b) :
      Zhong.permOf (blank B) σ (ι a) = ι b := by
    have hh := (Zhong.hStrip_permOf_spec (n := n) 0 (by omega) happ hperm h hfix).1
    simpa only [← hstart] using hh
  have hout (x : Cell n) (hx : x ∉ ({u,v,w} : Finset _).image ι) :
      Zhong.permOf (blank B) σ x = x := by
    have hh := (Zhong.hStrip_permOf_spec (n := n) 0 (by omega) happ hperm
      (Zhong.fourChain_apply_p hpu hpv hpw huv huw hvw) hfix).2 x hx
    simpa only [← hstart] using hh
  have hιu : ι u = (0, ⟨j, by omega⟩) := rfl
  have hιv : ι v = (0, ⟨j + 1, by omega⟩) := rfl
  have hιw : ι w = (0, ⟨j + 2, by omega⟩) := rfl
  obtain ⟨q,hq⟩ := path_of_zhong_word B σ
  refine ⟨Zhong.actSeq B σ,q,hq.trans (by rw [hlen]),?_,?_,?_,?_,?_⟩
  · have hf := hmap (Zhong.fourChain_apply_p hpu hpv hpw huv huw hvw)
    rw [hstart] at hf
    apply (Zhong.actSeq B σ).injective
    simp only [blank, position, Equiv.apply_symm_apply]
    change 0 = (Zhong.actSeq B σ) (blank B)
    rw [Zhong.actSeq_eq_permOf]
    change 0 = B (Zhong.permOf (blank B) σ (blank B))
    rw [hf]
    exact (B.apply_symm_apply 0).symm
  · rw [Zhong.actSeq_eq_permOf, ← hιu, ← hιv]
    change B (Zhong.permOf (blank B) σ (ι u)) = B (ι v)
    rw [hmap (Zhong.fourChain_apply_u hpu hpv hpw huv huw hvw)]
  · rw [Zhong.actSeq_eq_permOf, ← hιv, ← hιw]
    change B (Zhong.permOf (blank B) σ (ι v)) = B (ι w)
    rw [hmap (Zhong.fourChain_apply_v hpu hpv hpw huv huw hvw)]
  · rw [Zhong.actSeq_eq_permOf, ← hιw, ← hιu]
    change B (Zhong.permOf (blank B) σ (ι w)) = B (ι u)
    rw [hmap (Zhong.fourChain_apply_w hpu hpv hpw huv huw hvw)]
  · intro x hxu hxv hxw
    rw [Zhong.actSeq_eq_permOf]
    change B (Zhong.permOf (blank B) σ x) = B x
    rw [hout]
    simp only [Finset.image_insert,Finset.image_singleton,Finset.mem_insert,
      Finset.mem_singleton,not_or]
    rw [hιu, hιv, hιw]
    exact ⟨hxu,hxv,hxw⟩

/-- Place tile `t` at `(0, b+1)` with the blank below `(0, b)`, keeping `(0, 0..b)`. -/
theorem exists_place_top (D : Board n) (b : ℕ) (hb2 : b + 2 < n)
    (hblank : blank D = (⟨1, by omega⟩, ⟨b, by omega⟩)) (t : Tile n) (ht0 : t ≠ 0)
    (hfree : ∀ i (hi : i ≤ b), D (0, ⟨i, by omega⟩) ≠ t) :
    ∃ E : Board n, ∃ q : Path D E,
      q.length + 2 * min (b + 1) (n - (b + 1)) + 7 ≤ 8 * n ∧
      blank E = (⟨1, by omega⟩, ⟨b + 1, by omega⟩) ∧
      E (0, ⟨b + 1, by omega⟩) = t ∧
      ∀ i (hi : i ≤ b), E (0, ⟨i, by omega⟩) = D (0, ⟨i, by omega⟩) := by
  set s := D.symm t with hs
  have hDs : D s = t := D.apply_symm_apply t
  have hfree' : 0 < s.1.val ∨ (0 = s.1.val ∧ b + 1 ≤ s.2.val) := by
    by_contra hh
    have h1 : s.1 = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    have h2 : s.2.val ≤ b := by omega
    apply hfree s.2.val h2
    rw [← hDs]
    congr 1
    exact Prod.ext h1.symm rfl
  have hne : (s.1, s.2) ≠ blank D := by
    intro he
    apply ht0
    rw [← hDs, show s = blank D from he]
    exact D.apply_symm_apply 0
  obtain ⟨E, q, hq, hbE, hE, hfix⟩ :=
    Parberry.exists_placement D 0 b s.1 s.2 hfree' hne (by omega) hb2 hblank
  refine ⟨E, q, hq, hbE, ?_, ?_⟩
  · have e : ((0 : Fin n), (⟨b + 1, by omega⟩ : Fin n)) =
        ((⟨0, by omega⟩ : Fin n), (⟨b + 1, by omega⟩ : Fin n)) := Prod.ext (Fin.ext (by simp)) rfl
    rw [e, hE]; exact hDs
  · intro i hi
    exact hfix _ (Or.inr ⟨rfl, by simp only; omega⟩)

/-- Stage three distinct nonblank tiles in cyclic order in the top row, at columns
`j, j+1, j+2` for some `j ≤ 1`, with the blank below column `j`. -/
theorem exists_stage_three_sharp (B : Board n) (hn : 6 ≤ n) (x y z : Tile n)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    ∃ j, ∃ hj : j ≤ 1, ∃ C : Board n, ∃ p : Path B C,
      p.length + 31 ≤ 26 * n ∧ blank C = (⟨1, by omega⟩, ⟨j, by omega⟩) ∧
      ((C (0, ⟨j, by omega⟩) = x ∧ C (0, ⟨j + 1, by omega⟩) = y ∧
          C (0, ⟨j + 2, by omega⟩) = z) ∨
        (C (0, ⟨j, by omega⟩) = y ∧ C (0, ⟨j + 1, by omega⟩) = z ∧
          C (0, ⟨j + 2, by omega⟩) = x) ∨
        (C (0, ⟨j, by omega⟩) = z ∧ C (0, ⟨j + 1, by omega⟩) = x ∧
          C (0, ⟨j + 2, by omega⟩) = y)) := by
  obtain ⟨D0, p0, hp0, hb0, -⟩ :=
    exists_blank_below_top_prefix B (by omega) 0 (fun j hj => by omega)
  have hb0' : blank D0 = (⟨1, by omega⟩, ⟨0, by omega⟩) := by rw [hb0]; rfl
  -- two placements after a tile already in the corner
  have two (u v w : Tile n) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hv : v ≠ 0)
      (hw : w ≠ 0) (hu0 : D0 (0, ⟨0, by omega⟩) = u) :
      ∃ C : Board n, ∃ p : Path D0 C, p.length + 18 ≤ 16 * n ∧
        blank C = (⟨1, by omega⟩, ⟨0, by omega⟩) ∧
        C (0, ⟨0, by omega⟩) = u ∧ C (0, ⟨1, by omega⟩) = v ∧ C (0, ⟨2, by omega⟩) = w := by
    obtain ⟨E1, q1, hq1, hb1, hE1, hf1⟩ := exists_place_top D0 0 (by omega) hb0' v hv
      (fun i hi => by
        have : i = 0 := by omega
        subst this; rw [hu0]; exact huv)
    obtain ⟨E2, q2, hq2, hb2, hE2, hf2⟩ := exists_place_top E1 1 (by omega) hb1 w hw
      (fun i hi => by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with h | h
        · subst h; rw [hf1 0 le_rfl, hu0]; exact huw
        · subst h; rw [hE1]; exact hvw)
    obtain ⟨E3, q3, hb3, hq3, hf3⟩ :=
      exists_blank_access_path_preserving E2 (⟨1, by omega⟩, ⟨0, by omega⟩)
    have hrow : ∀ i (hi : i < n), E3 (0, ⟨i, hi⟩) = E2 (0, ⟨i, hi⟩) := fun i hi =>
      hf3 _ (Or.inl (by rw [hb2]; simp))
    refine ⟨E3, (q1.append q2).append q3, ?_, hb3, ?_, ?_, ?_⟩
    · have hd : gridDistance (blank E2) (⟨1, by omega⟩, ⟨0, by omega⟩) = 2 := by
        rw [hb2]; simp [gridDistance, Nat.dist]
      have hm1 : 1 ≤ min (0 + 1) (n - (0 + 1)) := by omega
      have hm2 : 2 ≤ min (1 + 1) (n - (1 + 1)) := by omega
      simp only [Path.length_append]
      omega
    · rw [hrow, hf2 0 (by omega), hf1 0 le_rfl, hu0]
    · rw [hrow, hf2 1 le_rfl, hE1]
    · rw [hrow, hE2]
  by_cases hcx : D0 (0, ⟨0, by omega⟩) = x
  · obtain ⟨C, p, hp, hbC, h0, h1, h2⟩ := two x y z hxy hxz hyz hy hz hcx
    refine ⟨0, by omega, C, p0.append p, ?_, hbC, Or.inl ⟨h0, h1, h2⟩⟩
    rw [Path.length_append]; omega
  by_cases hcy : D0 (0, ⟨0, by omega⟩) = y
  · obtain ⟨C, p, hp, hbC, h0, h1, h2⟩ := two y z x hyz hxy.symm hxz.symm hz hx hcy
    refine ⟨0, by omega, C, p0.append p, ?_, hbC, Or.inr (Or.inl ⟨h0, h1, h2⟩)⟩
    rw [Path.length_append]; omega
  by_cases hcz : D0 (0, ⟨0, by omega⟩) = z
  · obtain ⟨C, p, hp, hbC, h0, h1, h2⟩ := two z x y hxz.symm hyz.symm hxy hx hy hcz
    refine ⟨0, by omega, C, p0.append p, ?_, hbC, Or.inr (Or.inr ⟨h0, h1, h2⟩)⟩
    rw [Path.length_append]; omega
  -- no staged tile in the corner: use columns 1, 2, 3
  obtain ⟨E1, q1, hq1, hb1, hE1, hf1⟩ := exists_place_top D0 0 (by omega) hb0' x hx
    (fun i hi => by
      have : i = 0 := by omega
      subst this; exact hcx)
  obtain ⟨E2, q2, hq2, hb2, hE2, hf2⟩ := exists_place_top E1 1 (by omega) hb1 y hy
    (fun i hi => by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with h | h
      · subst h; rw [hf1 0 le_rfl]; exact hcy
      · subst h; rw [hE1]; exact hxy)
  obtain ⟨E3, q3, hq3, hb3, hE3, hf3⟩ := exists_place_top E2 2 (by omega) hb2 z hz
    (fun i hi => by
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with h | h | h
      · subst h; rw [hf2 0 (by omega), hf1 0 le_rfl]; exact hcz
      · subst h; rw [hf2 1 le_rfl, hE1]; exact hxz
      · subst h; rw [hE2]; exact hyz)
  obtain ⟨E4, q4, hb4, hq4, hf4⟩ :=
    exists_blank_access_path_preserving E3 (⟨1, by omega⟩, ⟨1, by omega⟩)
  have hrow : ∀ i (hi : i < n), E4 (0, ⟨i, hi⟩) = E3 (0, ⟨i, hi⟩) := fun i hi =>
    hf4 _ (Or.inl (by rw [hb3]; simp))
  refine ⟨1, le_rfl, E4, (((p0.append q1).append q2).append q3).append q4, ?_, hb4,
    Or.inl ⟨?_, ?_, ?_⟩⟩
  · have hd : gridDistance (blank E3) (⟨1, by omega⟩, ⟨1, by omega⟩) = 2 := by
      rw [hb3]; simp [gridDistance, Nat.dist]
    have hm1 : 1 ≤ min (0 + 1) (n - (0 + 1)) := by omega
    have hm2 : 2 ≤ min (1 + 1) (n - (1 + 1)) := by omega
    have hm3 : 3 ≤ min (2 + 1) (n - (2 + 1)) := by omega
    simp only [Path.length_append]
    omega
  · rw [hrow, hf3 1 (by omega), hf2 1 le_rfl, hE1]
  · rw [hrow, hf3 2 le_rfl, hE2]
  · rw [hrow, hE3]

/-- Rotate any three distinct nonblank tiles, restore every other tile and the
blank, in at most `52 n` moves. -/
theorem exists_three_cycle_sharp (B : Board n) (hn : 6 ≤ n)
    (a b c : Cell n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : B a ≠ 0) (hb : B b ≠ 0) (hc : B c ≠ 0) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 52*n ∧ blank C = blank B ∧
      C a = B b ∧ C b = B c ∧ C c = B a ∧
      ∀ x, x ≠ a → x ≠ b → x ≠ c → C x = B x := by
  have hxy : B a ≠ B b := fun h => hab (B.injective h)
  have hxz : B a ≠ B c := fun h => hac (B.injective h)
  have hyz : B b ≠ B c := fun h => hbc (B.injective h)
  obtain ⟨j, hj, D, p, hp, hbD, hlay⟩ :=
    exists_stage_three_sharp B hn (B a) (B b) (B c) hxy hxz hyz ha hb hc
  obtain ⟨E, q, hq, hbE, hE0, hE1, hE2, hfixE⟩ :=
    exists_top_three_cycle_at D (by omega) j (by omega) hbD
  obtain ⟨F, r, hr, hbF, hF⟩ := p.exists_unstaged q hbE
  have hc0 : (0, (⟨j, by omega⟩ : Fin n)) ≠ (0, ⟨j + 1, by omega⟩) := by simp
  have hc1 : (0, (⟨j, by omega⟩ : Fin n)) ≠ (0, ⟨j + 2, by omega⟩) := by simp
  have hc2 : (0, (⟨j + 1, by omega⟩ : Fin n)) ≠ (0, ⟨j + 2, by omega⟩) := by simp
  have hsymm {w : Cell n} {t : Tile n} (h : D w = t) : D.symm t = w := by
    rw [← h]; exact D.symm_apply_apply w
  refine ⟨F, r, by omega, hbF, ?_, ?_, ?_, ?_⟩
  · rw [hF]
    rcases hlay with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · rw [hsymm h0, hE0, h1]
    · rw [hsymm h2, hE2, h0]
    · rw [hsymm h1, hE1, h2]
  · rw [hF]
    rcases hlay with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · rw [hsymm h1, hE1, h2]
    · rw [hsymm h0, hE0, h1]
    · rw [hsymm h2, hE2, h0]
  · rw [hF]
    rcases hlay with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · rw [hsymm h2, hE2, h0]
    · rw [hsymm h1, hE1, h2]
    · rw [hsymm h0, hE0, h1]
  · intro w hwa hwb hwc
    rw [hF]
    have hne : ∀ t, t = B a ∨ t = B b ∨ t = B c → B w ≠ t := by
      rintro t (rfl | rfl | rfl) h
      · exact hwa (B.injective h)
      · exact hwb (B.injective h)
      · exact hwc (B.injective h)
    have hpos : ∀ i (hi : i < n), (0, ⟨i, hi⟩) = D.symm (B w) →
        D (0, ⟨i, hi⟩) = B w := fun i hi h => by rw [h]; exact D.apply_symm_apply _
    rw [hfixE]
    · exact D.apply_symm_apply _
    all_goals
      intro h
      have := hpos _ _ h.symm
      rcases hlay with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
      all_goals first
        | exact hne _ (Or.inl rfl) (by rw [← this]; assumption)
        | exact hne _ (Or.inr (Or.inl rfl)) (by rw [← this]; assumption)
        | exact hne _ (Or.inr (Or.inr rfl)) (by rw [← this]; assumption)

end SlidingPuzzle
