import SlidingPuzzle.Moves.ShiftCarry
import SlidingPuzzle.Moves.Jump
import SlidingPuzzle.Moves.LineWalk

/-! The three-row carry followed by the blank's return.

After the carry (`exists_shiftWord_trace`) has brought the tile next to the
corridor and the tile has been jumped out, the blank walks back along the tile's
row to the tile's old cell. For odd `m` this undoes the carry's rotation
exactly, so the whole exit is a blank/tile exchange: every other tile of the
strip is where it was. -/
namespace SlidingPuzzle
open Strip

variable {n : ℕ} [NeZero n]

/-- A blank/tile exchange raises the potential by at most their distance. -/
theorem manhattan_swapCells_blank_le (B : Board n) (x : Cell n) :
    manhattan (swapCells B (blank B) x) ≤ manhattan B + gridDistance (blank B) x := by
  by_cases hx : x = blank B
  · subst hx
    have h : swapCells B (blank B) (blank B) = B := by ext y; simp
    rw [h]; omega
  · have hbal := manhattan_blank_swap_balance B x hx
    have htri : gridDistance (blank B) (position (target n) (B x)) ≤
        gridDistance (blank B) x + gridDistance x (position (target n) (B x)) := by
      simp only [gridDistance, Nat.dist]; omega
    omega

/-- The carry with restore, on strip rows `row 0..2` and columns
`col 0..col (m+1)` with `m` odd. The blank starts at `c` outside the strip, next
to `c'`. It jumps to `(row 1, col 0)`, carries the tile of `(row 2, col (m+1))`
to `(row 1, col 1)`, jumps back to `c`, steps to `c'`, jumps the tile to `c'`,
and walks back through `(row 2, col 1), …, (row 2, col (m+1))`. The net effect
is the blank exchange `c ↔ c'` followed by `c' ↔ (row 2, col (m+1))`. -/
theorem exists_restore_carry (hn : 2 ≤ n) (row col : ℕ → Fin n) (m : ℕ)
    (hrow : StripCol row 2) (hcol : StripCol col (m+1)) (hm : m % 2 = 1)
    (S : Board n) (c c' : Cell n)
    (hc : ∀ q, region 2 (m+1) q → emb row col q ≠ c)
    (hc' : ∀ q, region 2 (m+1) q → emb row col q ≠ c')
    (hcc' : gridDistance c c' = 1) (hS : blank S = c)
    (hrowe : Nat.dist c.1.val (row 1).val ≤ 1)
    (hpare : (c.1.val+c.2.val+(row 1).val+(col 0).val) % 2 = 1)
    (hrowz : Nat.dist c'.1.val (row 1).val ≤ 1)
    (hparz : (c'.1.val+c'.2.val+(row 1).val+(col 1).val) % 2 = 1)
    (t : Cell n) (ht : (row 2, col (m+1)) = t) :
    ∃ p : Path S (swapCells (swapCells S c c') c' t),
      p.length ≤ 50*(Nat.dist c.2.val (col 0).val+1)+7*m+8+
        25*(Nat.dist c'.2.val (col 1).val+1) := by
  subst ht
  have hreg : ∀ r a, r ≤ 2 → a ≤ m+1 → region 2 (m+1) (r,a) := fun r a h1 h2 => ⟨h1, h2⟩
  have hinj : ∀ p q, region 2 (m+1) p → region 2 (m+1) q → emb row col p = emb row col q →
      p = q := fun p q hp hq h => emb_inj hrow hcol hp hq h
  let e : Cell n := (row 1, col 0)
  let z : Cell n := (row 1, col 1)
  let b : Cell n := (row 2, col (m+1))
  have hee : emb row col (1,0) = e := rfl
  have hez : emb row col (1,1) = z := rfl
  have heb : emb row col (2,m+1) = b := rfl
  have hce : c ≠ e := (hc (1,0) (hreg _ _ (by omega) (by omega))).symm
  have hcz : c ≠ z := (hc (1,1) (hreg _ _ (by omega) (by omega))).symm
  have hcb : c ≠ b := (hc (2,m+1) (hreg _ _ (by omega) (by omega))).symm
  have hc'z : c' ≠ z := (hc' (1,1) (hreg _ _ (by omega) (by omega))).symm
  have hc'b : c' ≠ b := (hc' (2,m+1) (hreg _ _ (by omega) (by omega))).symm
  have hcc : c ≠ c' := by intro h; rw [h, gridDistance_self] at hcc'; omega
  -- E1: jump into the strip.
  set S₁ := swapCells S (blank S) e with hS₁
  obtain ⟨p₁, hp₁⟩ := exists_horizontal_jump hn S e (by rw [hS]; exact hrowe)
    (by rw [hS]; exact hpare)
  have hbS₁ : blank S₁ = e := blank_swapCells S e
  have F1 : ∀ x, x ≠ c → x ≠ e → S₁ x = S x := fun x h₁ h₂ =>
    swapCells_preserves S (by rw [hS]; exact h₁) h₂
  have F1c : S₁ c = S e := by rw [hS₁, ← hS, swapCells_at_left]
  -- E2: the carry.
  obtain ⟨S₂, cs, hE, hl, hS₂, hS₂out⟩ := exists_shiftWord_trace row col m hrow hcol S₁ hbS₁
  obtain ⟨q₂, hq₂⟩ := hE.exists_path
  have hS₂e : S₂ e = 0 := by
    rw [← hee, hS₂ (1,0) (hreg _ _ (by omega) (by omega)),
      show shiftEffect m (1,0) = (1,0) by simp [shiftEffect], hee, ← hbS₁]
    simp [blank, position]
  have hbS₂ : blank S₂ = e := by simp only [blank, position, Equiv.symm_apply_eq, hS₂e]
  have hcS₂ : S₂ c = S₁ c := hS₂out c (fun q hq h => hc q hq h.symm)
  have hc'S₂ : S₂ c' = S₁ c' := hS₂out c' (fun q hq h => hc' q hq h.symm)
  -- E3: jump back.
  set S₃ := swapCells S₂ (blank S₂) c with hS₃
  obtain ⟨p₃, hp₃⟩ := exists_horizontal_jump hn S₂ c
    (by rw [hbS₂, Nat.dist_comm]; exact hrowe) (by rw [hbS₂]; simp only [e]; omega)
  have hbS₃ : blank S₃ = c := blank_swapCells S₂ c
  have F3 : ∀ x, x ≠ e → x ≠ c → S₃ x = S₂ x := fun x h₁ h₂ =>
    swapCells_preserves S₂ (by rw [hbS₂]; exact h₁) h₂
  have F3e : S₃ e = S₂ c := by rw [hS₃, ← hbS₂, swapCells_at_left]
  -- E4: one corridor move.
  have hd₄ : gridDistance (blank S₃) c' = 1 := by rw [hbS₃]; exact hcc'
  set S₄ := swapCells S₃ (blank S₃) c' with hS₄
  have hbS₄ : blank S₄ = c' := blank_swapCells S₃ c'
  have F4 : ∀ x, x ≠ c → x ≠ c' → S₄ x = S₃ x := fun x h₁ h₂ =>
    swapCells_preserves S₃ (by rw [hbS₃]; exact h₁) h₂
  have F4c : S₄ c = S₃ c' := by rw [hS₄, ← hbS₃, swapCells_at_left]
  -- E5: jump the tile out.
  set S₅ := swapCells S₄ (blank S₄) z with hS₅
  obtain ⟨p₅, hp₅⟩ := exists_horizontal_jump hn S₄ z (by rw [hbS₄]; exact hrowz)
    (by rw [hbS₄]; exact hparz)
  have hbS₅ : blank S₅ = z := blank_swapCells S₄ z
  have F5 : ∀ x, x ≠ c' → x ≠ z → S₅ x = S₄ x := fun x h₁ h₂ =>
    swapCells_preserves S₄ (by rw [hbS₄]; exact h₁) h₂
  have F5c' : S₅ c' = S₄ z := by rw [hS₅, ← hbS₄, swapCells_at_left]
  -- E6: walk back along the tile's row.
  let g : ℕ → SCell := fun t => if t = 0 then (1,1) else (2,t)
  let f : ℕ → Cell n := fun t => emb row col (g t)
  have hgr : ∀ t, t ≤ m+1 → region 2 (m+1) (g t) := by
    intro t ht; simp only [g]; split_ifs <;> exact hreg _ _ (by omega) (by omega)
  have hginj : ∀ t t', t ≤ m+1 → t' ≤ m+1 → f t = f t' → t = t' := by
    intro t t' ht ht' h
    have := hinj _ _ (hgr t ht) (hgr t' ht') h
    simp only [g] at this
    split_ifs at this <;> simp only [Prod.mk.injEq] at this <;> omega
  obtain ⟨D, p₆, hp₆, hbD, hDline, hDfix⟩ := exists_line_walk f 0 (m+1)
    (fun t ht => by
      simp only [f, zero_add]
      rw [emb_dist hrow hcol (hgr t (by omega)) (hgr (t+1) (by omega))]
      rcases Nat.eq_zero_or_pos t with rfl | ht0
      · simp [g, sdist, Nat.dist]
      · simp only [g, sdist, Nat.dist, show t ≠ 0 by omega, show t+1 ≠ 0 by omega, ↓reduceIte]
        omega)
    (fun t t' ht ht' h => by simpa using hginj t t' ht ht' (by simpa using h))
    S₅ (by rw [hbS₅]; rfl)
  simp only [zero_add] at hbD hDline hDfix
  -- The net effect.
  have hf0 : f 0 = z := rfl
  have hfb : f (m+1) = b := by simp only [f, g]; rw [if_neg (by omega)]; rfl
  have hfS : ∀ t, t ≤ m+1 → ∃ q, region 2 (m+1) q ∧ f t = emb row col q :=
    fun t ht => ⟨g t, hgr t ht, rfl⟩
  have hfc : ∀ t, t ≤ m+1 → f t ≠ c := fun t ht => hc _ (hgr t ht)
  have hfc' : ∀ t, t ≤ m+1 → f t ≠ c' := fun t ht => hc' _ (hgr t ht)
  have hDb : D b = 0 := by
    rw [← hfb, ← hbD]; simp [blank, position]
  have hS0 : S c = 0 := by rw [← hS]; simp [blank, position]
  have hDG : D = swapCells (swapCells S c c') c' b := by
    refine Equiv.ext fun x => ?_
    simp only [swapCells_apply]
    by_cases hxs : ∃ q, region 2 (m+1) q ∧ x = emb row col q
    · obtain ⟨q, hq, rfl⟩ := hxs
      have hqc := hc q hq
      have hqc' := hc' q hq
      by_cases hqb : q = (2, m+1)
      · subst hqb
        rw [heb, hDb, Equiv.swap_apply_right, Equiv.swap_apply_right, hS0]
      have hqb' : emb row col q ≠ b := fun h => hqb (hinj _ _ hq
        (hreg _ _ (by omega) (by omega)) (h.trans heb.symm))
      rw [Equiv.swap_apply_of_ne_of_ne hqc' hqb', Equiv.swap_apply_of_ne_of_ne hqc hqc']
      by_cases hline : ∃ t, t ≤ m ∧ q = g t
      · obtain ⟨t, ht, rfl⟩ := hline
        have hgt : g (t+1) = (2, t+1) := by simp only [g]; rw [if_neg (by omega)]
        have hft1z : f (t+1) ≠ z := by
          rw [← hf0]; intro h; have := hginj _ _ (by omega) (by omega) h; omega
        have hft1e : f (t+1) ≠ e := by
          simp only [f, hgt]; rw [← hee]; intro h
          have := hinj _ _ (hreg _ _ (by omega) (by omega)) (hreg _ _ (by omega) (by omega)) h
          simp at this
        have hfte : f t ≠ e := by
          simp only [f]; rw [← hee]; intro h
          have := hinj _ _ (hgr t (by omega)) (hreg _ _ (by omega) (by omega)) h
          simp only [g] at this; split_ifs at this <;> simp at this
        change D (f t) = S (f t)
        rw [hDline t (by omega), F5 _ (hfc' _ (by omega)) hft1z,
          F4 _ (hfc _ (by omega)) (hfc' _ (by omega)), F3 _ hft1e (hfc _ (by omega))]
        simp only [f]
        rw [hS₂ _ (hgr (t+1) (by omega)), hgt]
        have hsh : shiftEffect m (2, t+1) = g t := by
          unfold shiftEffect
          split_ifs with h1 h2 h3
          · exact absurd (congrArg Prod.fst h1) (by simp)
          · have h' : t = 0 := by have := congrArg Prod.snd h2; simp at this; omega
            subst h'; rfl
          · have h' : t ≠ 0 := by intro h; subst h; exact h2 (by simp [hm])
            simp [g, h']
          · have h' : t ≠ 0 := by intro h; subst h; exact h2 (by simp [hm])
            exact absurd ⟨rfl, by simp; omega, by simp; omega⟩ h3
        rw [hsh]
        exact F1 _ (hfc t (by omega)) hfte
      · push Not at hline
        have hoff : ∀ t, t ≤ m+1 → emb row col q ≠ f t := by
          intro t ht h
          have := hinj _ _ hq (hgr t ht) h
          rcases Nat.lt_or_ge t (m+1) with h' | h'
          · exact hline t (by omega) this
          · have ht' : t = m+1 := by omega
            subst ht'
            exact hqb (this.trans (by simp only [g]; rw [if_neg (by omega)]))
        rw [hDfix _ hoff]
        by_cases hqe : q = (1,0)
        · subst hqe
          rw [hee, F5 e (fun h => hc' _ (hreg _ _ (by omega) (by omega)) (hee.trans h))
              (fun h => by
                have := hinj _ _ (hreg _ _ (by omega) (by omega)) (hreg _ _ (by omega) (by omega))
                  (hee.trans (h.trans hez.symm))
                simp at this),
            F4 e hce.symm (fun h => hc' _ (hreg _ _ (by omega) (by omega)) (hee.trans h)),
            F3e, hcS₂, F1c]
        · have hqe' : emb row col q ≠ e := fun h => hqe (hinj _ _ hq
            (hreg _ _ (by omega) (by omega)) (h.trans hee.symm))
          have hqz : emb row col q ≠ z := fun h => by
            have := hinj _ _ hq (hreg _ _ (by omega) (by omega)) (h.trans hez.symm)
            exact hline 0 (by omega) (by simpa [g] using this)
          rw [F5 _ hqc' hqz, F4 _ hqc hqc', F3 _ hqe' hqc, hS₂ q hq]
          have hsh : shiftEffect m q = q := by
            unfold shiftEffect
            split_ifs with h1 h2 h3
            · exact absurd h1 (by simpa [g] using hline 0 (by omega))
            · exact absurd (h2.trans (by rw [hm])) (by simpa [g] using hline 1 (by omega))
            · exfalso
              obtain ⟨r, a⟩ := q
              obtain ⟨hr, ha1, ha2⟩ := h3
              simp only at hr ha1 ha2
              subst hr
              rcases Nat.lt_or_ge a (m+1) with h | h
              · exact hline a (by omega) (by simp only [g]; rw [if_neg (by omega)])
              · exact hqb (Prod.ext rfl (show a = m+1 by omega))
            · rfl
          rw [hsh]
          exact F1 _ hqc hqe'
    · push Not at hxs
      have hoff : ∀ t, t ≤ m+1 → x ≠ f t := fun t ht => hxs (g t) (hgr t ht)
      rw [hDfix x hoff]
      have hc'e : c' ≠ e := fun h => hc' (1,0) (hreg _ _ (by omega) (by omega)) (hee.trans h.symm)
      have hze : z ≠ e := fun h => by
        have := hinj _ _ (hreg _ _ (by omega) (by omega)) (hreg _ _ (by omega) (by omega))
          (hez.trans (h.trans hee.symm))
        simp at this
      have hbe : b ≠ e := fun h => by
        have := hinj _ _ (hreg _ _ (by omega) (by omega)) (hreg _ _ (by omega) (by omega))
          (heb.trans (h.trans hee.symm))
        simp at this
      by_cases hxc : x = c
      · subst hxc
        rw [Equiv.swap_apply_of_ne_of_ne hcc hcb, Equiv.swap_apply_left,
          F5 _ hcc hcz, F4c, F3 _ hc'e hcc.symm, hc'S₂, F1 _ hcc.symm hc'e]
      by_cases hxc' : x = c'
      · subst hxc'
        rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hcb.symm hc'b.symm, F5c',
          F4 _ hcz.symm hc'z.symm, F3 _ hze hcz.symm, ← hez, hS₂ (1,1) (hreg _ _ (by omega) (by omega))]
        have hsh : shiftEffect m (1,1) = (2, m+1) := by simp [shiftEffect]
        rw [hsh, heb, F1 _ hcb.symm hbe]
      have hxz : x ≠ z := fun h => hxs (1,1) (hreg _ _ (by omega) (by omega)) (h.trans hez.symm)
      have hxe : x ≠ e := fun h => hxs (1,0) (hreg _ _ (by omega) (by omega)) (h.trans hee.symm)
      have hxb : x ≠ b := fun h => hxs (2,m+1) (hreg _ _ (by omega) (by omega)) (h.trans heb.symm)
      rw [Equiv.swap_apply_of_ne_of_ne hxc' hxb, Equiv.swap_apply_of_ne_of_ne hxc hxc',
        F5 _ hxc' hxz, F4 _ hxc hxc', F3 _ hxe hxc,
        hS₂out x (fun q hq h => hxs q hq h), F1 _ hxc hxe]
  subst hDG
  refine ⟨p₁.append (q₂.append (p₃.append ((movePath S₃ c' hd₄).append (p₅.append p₆)))), ?_⟩
  simp only [Path.length_append]
  have h₁ : p₁.length ≤ 25*(Nat.dist c.2.val (col 0).val+1) :=
    hp₁.trans (by rw [hS])
  have h₃ : p₃.length ≤ 25*(Nat.dist c.2.val (col 0).val+1) :=
    hp₃.trans (by rw [hbS₂, Nat.dist_comm])
  have h₅ : p₅.length ≤ 25*(Nat.dist c'.2.val (col 1).val+1) :=
    hp₅.trans (by rw [hbS₄])
  have h₄ := movePath_length S₃ c' hd₄
  omega

end SlidingPuzzle
