import SlidingPuzzle.Moves.Carry
import SlidingPuzzle.Moves.Efficiency

/-! A walk followed by five-move carries, as one explicit word, with its
effect on the Manhattan potential. The word lives in two adjacent rows `R`, `H`
whose columns are parametrized by `col`, so one proof serves both directions.

The blank starts at `(R, col a)` and the tile at `(R, col (a+m+1))`. The blank
walks to the tile and carries it back, ending at `(R, col a)` with the tile at
`(R, col (a+1))`. The word has length `6m`, but its tiles move little in net:
the potential rises by at most `4m+2`, so at most `5m+1` moves are inefficient. -/
namespace SlidingPuzzle
noncomputable section

variable {n : ℕ} [NeZero n]

/-- The walk-and-carry word. -/
def exitWord (R H : Fin n) (col : ℕ → Fin n) : ℕ → ℕ → List (Cell n)
  | _, 0 => []
  | a, m+1 => (R, col (a+1)) :: (exitWord R H col (a+1) m ++
      [(R, col (a+2)), (H, col (a+2)), (H, col (a+1)), (H, col a), (R, col a)])

theorem exitWord_length (R H : Fin n) (col : ℕ → Fin n) (a m : ℕ) :
    (exitWord R H col a m).length = 6*m := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih => simp [exitWord, ih]; ring

/-- The cells of the word lie in the strip's columns `a..a+m+1`. -/
theorem exitWord_mem (R H : Fin n) (col : ℕ → Fin n) (a m : ℕ) (x : Cell n)
    (hx : x ∈ exitWord R H col a m) :
    ∃ c, a ≤ c ∧ c ≤ a+m+1 ∧ (x = (R, col c) ∨ x = (H, col c)) := by
  induction m generalizing a with
  | zero => simp [exitWord] at hx
  | succ m ih =>
    simp only [exitWord, List.cons_append, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | hx | rfl | rfl | rfl | rfl | rfl
    · exact ⟨a+1, by omega, by omega, Or.inl rfl⟩
    · obtain ⟨c, h1, h2, h3⟩ := ih (a+1) hx
      exact ⟨c, by omega, by omega, h3⟩
    · exact ⟨a+2, by omega, by omega, Or.inl rfl⟩
    · exact ⟨a+2, by omega, by omega, Or.inr rfl⟩
    · exact ⟨a+1, by omega, by omega, Or.inr rfl⟩
    · exact ⟨a, by omega, by omega, Or.inr rfl⟩
    · exact ⟨a, by omega, by omega, Or.inl rfl⟩

/-- A strip parametrization: `col` is isometric on `0..N`. -/
def StripCol (col : ℕ → Fin n) (N : ℕ) : Prop :=
  ∀ a b, a ≤ N → b ≤ N → Nat.dist (col a).val (col b).val = Nat.dist a b

private theorem strip_ne {col : ℕ → Fin n} {N : ℕ} (hcol : StripCol col N)
    {a b : ℕ} (ha : a ≤ N) (hb : b ≤ N) (hab : a ≠ b) (r r' : Fin n) :
    ((r, col a) : Cell n) ≠ (r', col b) := by
  intro h
  have h2 := congrArg (fun x : Cell n => x.2.val) h
  have := hcol a b ha hb
  simp only at h2
  rw [h2, Nat.dist_self] at this
  simp [Nat.dist] at this
  omega

private theorem rows_ne {R H : Fin n} (hRH : Nat.dist R.val H.val = 1) (c c' : Fin n) :
    ((R, c) : Cell n) ≠ (H, c') := by
  intro h
  have := congrArg (fun x : Cell n => x.1.val) h
  simp only at this
  rw [this] at hRH
  simp at hRH

private theorem strip_dist {R H : Fin n} (hRH : Nat.dist R.val H.val = 1)
    {col : ℕ → Fin n} {N : ℕ} (hcol : StripCol col N) {a b : ℕ} (ha : a ≤ N) (hb : b ≤ N) :
    gridDistance ((R, col a) : Cell n) (R, col b) = Nat.dist a b ∧
      gridDistance ((H, col a) : Cell n) (H, col b) = Nat.dist a b ∧
      gridDistance ((R, col a) : Cell n) (H, col b) = Nat.dist a b+1 ∧
      gridDistance ((H, col a) : Cell n) (R, col b) = Nat.dist a b+1 := by
  have h := hcol a b ha hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [gridDistance, Nat.dist_self, h, zero_add]
  · simp only [gridDistance, Nat.dist_self, h, zero_add]
  · simp only [gridDistance, h, hRH]; ring
  · simp only [gridDistance, h, Nat.dist_comm H.val R.val, hRH]; ring

/-- The walk-and-carry word from a board with the blank at `(R, col a)`. For
`m ≥ 1`, the first walked tile ends at `(H, col a)`, and the potential,
corrected by that tile's distance, rises by at most `4m`. -/
theorem exists_exitWord (R H : Fin n) (hRH : Nat.dist R.val H.val = 1)
    (col : ℕ → Fin n) (N : ℕ) (hcol : StripCol col N) (a m : ℕ) (hm : a+m+1 ≤ N)
    (X : Board n) (hX : blank X = (R, col a)) :
    ∃ Y : Board n, Executes X (exitWord R H col a m) Y ∧ blank Y = (R, col a) ∧
      Y (R, col (a+1)) = X (R, col (a+m+1)) ∧
      (m = 0 → Y = X) ∧
      (1 ≤ m → Y (H, col a) = X (R, col (a+1)) ∧
        manhattan Y+gridDistance (R, col (a+1)) (position (target n) (X (R, col (a+1)))) ≤
          manhattan X+gridDistance (H, col a) (position (target n) (X (R, col (a+1))))+4*m) := by
  induction m generalizing a X with
  | zero =>
    refine ⟨X, .nil X, hX, rfl, fun _ => rfl, fun h => by omega⟩
  | succ m ih =>
    have hRHne := rows_ne hRH
    have sne : ∀ {c c' : ℕ}, c ≤ N → c' ≤ N → c ≠ c' → ∀ r r' : Fin n,
        ((r, col c) : Cell n) ≠ (r', col c') := fun hc hc' h r r' => strip_ne hcol hc hc' h r r'
    have sd : ∀ {c c' : ℕ}, c ≤ N → c' ≤ N → _ := fun hc hc' => strip_dist hRH hcol hc hc'
    -- The first walk move.
    have h₁ : gridDistance (blank X) (R, col (a+1)) = 1 := by
      rw [hX, (sd (by omega) (by omega)).1]; simp [Nat.dist]
    let X' := swapCells X (blank X) (R, col (a+1))
    have hbX' : blank X' = (R, col (a+1)) := blank_swapCells X _
    have hX'fix : ∀ x, x ≠ (R, col a) → x ≠ (R, col (a+1)) → X' x = X x := by
      intro x h1 h2
      exact swapCells_preserves X (by rw [hX]; exact h1) h2
    have hX'a : X' (R, col a) = X (R, col (a+1)) := by
      change swapCells X (blank X) _ _ = _
      rw [← hX, swapCells_at_left]
    have hne01 : ((R, col (a+1)) : Cell n) ≠ blank X := by
      rw [hX]; exact sne (by omega) (by omega) (by omega) R R
    have hbal₀ := manhattan_blank_swap_balance X (R, col (a+1)) hne01
    change manhattan X'+_ = _ at hbal₀
    have hdX : gridDistance (blank X) (position (target n) (X (R, col (a+1)))) =
        gridDistance (R, col a) (position (target n) (X (R, col (a+1)))) := by rw [hX]
    rw [hdX] at hbal₀
    -- The inner word.
    obtain ⟨X'', hE, hbX'', hT'', h0, h1⟩ := ih (a+1) (by omega) X' hbX'
    have hin := exitWord_mem R H col (a+1) m
    have hX''fix : ∀ r : Fin n, X'' (r, col a) = X' (r, col a) := by
      intro r
      apply hE.preserves
      · rw [hbX']; exact sne (by omega) (by omega) (by omega) r R
      · intro hm'
        obtain ⟨c, hc1, hc2, hc3⟩ := hin _ hm'
        rcases hc3 with h | h
        · exact sne (by omega) (by omega) (by omega) r R h
        · exact sne (by omega) (by omega) (by omega) r H h
    -- The final carry cycle.
    let c₁ : Cell n := (R, col (a+2))
    let c₂ : Cell n := (H, col (a+2))
    let c₃ : Cell n := (H, col (a+1))
    let c₄ : Cell n := (H, col a)
    let c₅ : Cell n := (R, col a)
    have hd₁ : gridDistance (blank X'') c₁ = 1 := by
      rw [hbX'', (sd (by omega) (by omega)).1]; simp [Nat.dist]
    let B₁ := swapCells X'' (blank X'') c₁
    have hbB₁ : blank B₁ = c₁ := blank_swapCells _ _
    have hd₂ : gridDistance (blank B₁) c₂ = 1 := by
      rw [hbB₁]; simp only [c₁, c₂]; rw [(sd (by omega) (by omega)).2.2.1]; simp
    let B₂ := swapCells B₁ (blank B₁) c₂
    have hbB₂ : blank B₂ = c₂ := blank_swapCells _ _
    have hd₃ : gridDistance (blank B₂) c₃ = 1 := by
      rw [hbB₂]; simp only [c₂, c₃]; rw [(sd (by omega) (by omega)).2.1]; simp [Nat.dist]
    let B₃ := swapCells B₂ (blank B₂) c₃
    have hbB₃ : blank B₃ = c₃ := blank_swapCells _ _
    have hd₄ : gridDistance (blank B₃) c₄ = 1 := by
      rw [hbB₃]; simp only [c₃, c₄]; rw [(sd (by omega) (by omega)).2.1]; simp [Nat.dist]
    let B₄ := swapCells B₃ (blank B₃) c₄
    have hbB₄ : blank B₄ = c₄ := blank_swapCells _ _
    have hd₅ : gridDistance (blank B₄) c₅ = 1 := by
      rw [hbB₄]; simp only [c₄, c₅]; rw [(sd (by omega) (by omega)).2.2.2]; simp
    let Y := swapCells B₄ (blank B₄) c₅
    have hbY : blank Y = c₅ := blank_swapCells _ _
    have hEY : Executes X (exitWord R H col a (m+1)) Y := by
      simp only [exitWord]
      refine Executes.cons h₁ ?_
      refine hE.append ?_
      exact .cons hd₁ (.cons hd₂ (.cons hd₃ (.cons hd₄ (.cons hd₅ (.nil _)))))
    -- Distinctness of the cycle's cells.
    have n01 : c₁ ≠ (R, col (a+1)) := sne (by omega) (by omega) (by omega) R R
    have n12 : c₂ ≠ c₁ := (hRHne _ _).symm
    have n13 : c₃ ≠ c₁ := (hRHne _ _).symm
    have n23 : c₃ ≠ c₂ := sne (by omega) (by omega) (by omega) H H
    have n14 : c₄ ≠ c₁ := (hRHne _ _).symm
    have n24 : c₄ ≠ c₂ := sne (by omega) (by omega) (by omega) H H
    have n34 : c₄ ≠ c₃ := sne (by omega) (by omega) (by omega) H H
    have n15 : c₅ ≠ c₁ := sne (by omega) (by omega) (by omega) R R
    have n25 : c₅ ≠ c₂ := hRHne _ _
    have n35 : c₅ ≠ c₃ := hRHne _ _
    have n45 : c₅ ≠ c₄ := hRHne _ _
    have n0c2 : c₂ ≠ (R, col (a+1)) := (hRHne _ _).symm
    have n0c3 : c₃ ≠ (R, col (a+1)) := (hRHne _ _).symm
    have n0c4 : c₄ ≠ (R, col (a+1)) := (hRHne _ _).symm
    have n0c5 : c₅ ≠ (R, col (a+1)) := sne (by omega) (by omega) (by omega) R R
    -- The tiles moved by the cycle, in terms of `X''`.
    have hB₁ : ∀ x, x ≠ (R, col (a+1)) → x ≠ c₁ → B₁ x = X'' x := fun x h1 h2 =>
      swapCells_preserves X'' (by rw [hbX'']; exact h1) h2
    have hB₂ : ∀ x, x ≠ c₁ → x ≠ c₂ → B₂ x = B₁ x := fun x h1 h2 =>
      swapCells_preserves B₁ (by rw [hbB₁]; exact h1) h2
    have hB₃ : ∀ x, x ≠ c₂ → x ≠ c₃ → B₃ x = B₂ x := fun x h1 h2 =>
      swapCells_preserves B₂ (by rw [hbB₂]; exact h1) h2
    have hB₄ : ∀ x, x ≠ c₃ → x ≠ c₄ → B₄ x = B₃ x := fun x h1 h2 =>
      swapCells_preserves B₃ (by rw [hbB₃]; exact h1) h2
    have hY : ∀ x, x ≠ c₄ → x ≠ c₅ → Y x = B₄ x := fun x h1 h2 =>
      swapCells_preserves B₄ (by rw [hbB₄]; exact h1) h2
    have τ₂ : B₁ c₂ = X'' c₂ := hB₁ c₂ n0c2 n12
    have τ₃ : B₂ c₃ = X'' c₃ := by rw [hB₂ c₃ n13 n23, hB₁ c₃ n0c3 n13]
    have τ₄ : B₃ c₄ = X'' c₄ := by rw [hB₃ c₄ n24 n34, hB₂ c₄ n14 n24, hB₁ c₄ n0c4 n14]
    have τ₅ : B₄ c₅ = X'' c₅ := by
      rw [hB₄ c₅ n35 n45, hB₃ c₅ n25 n35, hB₂ c₅ n15 n25, hB₁ c₅ n0c5 n15]
    -- Potential balance of each move.
    have hc₁ : c₁ ≠ blank X'' := by rw [hbX'']; exact n01
    have hc₂ : c₂ ≠ blank B₁ := by rw [hbB₁]; exact n12
    have hc₃ : c₃ ≠ blank B₂ := by rw [hbB₂]; exact n23
    have hc₄ : c₄ ≠ blank B₃ := by rw [hbB₃]; exact n34
    have hc₅ : c₅ ≠ blank B₄ := by rw [hbB₄]; exact n45
    have b₁ := manhattan_blank_swap_balance X'' c₁ hc₁
    have b₂ := manhattan_blank_swap_balance B₁ c₂ hc₂
    have b₃ := manhattan_blank_swap_balance B₂ c₃ hc₃
    have b₄ := manhattan_blank_swap_balance B₃ c₄ hc₄
    have b₅ := manhattan_blank_swap_balance B₄ c₅ hc₅
    change manhattan B₁+_ = _ at b₁
    change manhattan B₂+_ = _ at b₂
    change manhattan B₃+_ = _ at b₃
    change manhattan B₄+_ = _ at b₄
    change manhattan Y+_ = _ at b₅
    have g₁ : ∀ w, gridDistance (blank X'') w = gridDistance (R, col (a+1)) w :=
      fun w => by rw [hbX'']
    have g₂ : ∀ w, gridDistance (blank B₁) w = gridDistance c₁ w := fun w => by rw [hbB₁]
    have g₃ : ∀ w, gridDistance (blank B₂) w = gridDistance c₂ w := fun w => by rw [hbB₂]
    have g₄ : ∀ w, gridDistance (blank B₃) w = gridDistance c₃ w := fun w => by rw [hbB₃]
    have g₅ : ∀ w, gridDistance (blank B₄) w = gridDistance c₄ w := fun w => by rw [hbB₄]
    rw [g₁] at b₁
    rw [g₂, τ₂] at b₂
    rw [g₃, τ₃] at b₃
    rw [g₄, τ₄] at b₄
    rw [g₅, τ₅] at b₅
    -- Unit steps change distances by at most one.
    have tri : ∀ (u v w : Cell n), gridDistance u v = 1 →
        gridDistance u w ≤ gridDistance v w+1 := by
      intro u v w h
      simp only [gridDistance, Nat.dist] at h ⊢
      omega
    have e₁ := tri (R, col (a+1)) c₁ (position (target n) (X'' c₁)) (by
      rw [(sd (by omega) (by omega)).1]; simp [Nat.dist])
    have e₂ := tri c₁ c₂ (position (target n) (X'' c₂)) (by
      simp only [c₁, c₂]; rw [(sd (by omega) (by omega)).2.2.1]; simp)
    have e₄ := tri c₃ c₄ (position (target n) (X'' c₄)) (by
      simp only [c₃, c₄]; rw [(sd (by omega) (by omega)).2.1]; simp [Nat.dist])
    have hc₅X : X'' c₅ = X (R, col (a+1)) := by rw [hX''fix R, hX'a]
    rw [hc₅X] at b₅
    refine ⟨Y, hEY, hbY, ?_, fun h => by omega, fun _ => ⟨?_, ?_⟩⟩
    · -- The carried tile.
      have hY1 : Y (R, col (a+1)) = B₁ (R, col (a+1)) := by
        rw [hY _ n0c4.symm n0c5.symm, hB₄ _ n0c3.symm n0c4.symm, hB₃ _ n0c2.symm n0c3.symm,
          hB₂ _ n01.symm n0c2.symm]
      rw [hY1]
      change swapCells X'' (blank X'') c₁ _ = _
      rw [← hbX'', swapCells_at_left]
      have hT : X'' c₁ = X' (R, col (a+(m+1)+1)) := by
        rcases Nat.eq_zero_or_pos m with hm0 | hm0
        · subst hm0; rw [h0 rfl]
        · simp only [c₁]
          have := hT''
          rwa [show a+1+1 = a+2 by ring, show a+1+m+1 = a+(m+1)+1 by ring] at this
      rw [hT]
      exact hX'fix _ (sne (by omega) (by omega) (by omega) R R)
        (sne (by omega) (by omega) (by omega) R R)
    · -- The first walked tile.
      change swapCells B₄ (blank B₄) c₅ c₄ = _
      rw [← hbB₄, swapCells_at_left, τ₅, hc₅X]
    · -- The potential.
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        have hX''eq := h0 rfl
        have e₃ := tri c₂ c₃ (position (target n) (X'' c₃)) (by
          simp only [c₂, c₃]; rw [(sd (by omega) (by omega)).2.1]; simp [Nat.dist])
        rw [hX''eq] at b₁ b₂ b₃ b₄ e₁ e₂ e₃ e₄
        simp only [c₁, c₂, c₃, c₄, c₅] at b₁ b₂ b₃ b₄ b₅ e₁ e₂ e₃ e₄ ⊢
        omega
      · obtain ⟨hu, hM⟩ := h1 hm0
        -- `X'' c₃` is the tile first walked by the inner word.
        have hu' : X'' c₃ = X' (R, col (a+1+1)) := hu
        have hX'2 : X' (R, col (a+1+1)) = X (R, col (a+2)) :=
          hX'fix _ (sne (by omega) (by omega) (by omega) R R)
            (sne (by omega) (by omega) (by omega) R R)
        have e₃ := tri c₂ (R, col (a+2)) (position (target n) (X'' c₃)) (by
          simp only [c₂]; rw [(sd (by omega) (by omega)).2.2.2]; simp)
        rw [hu'] at b₃ e₃
        rw [show a+1+1 = a+2 by ring] at hM b₃ e₃
        simp only [c₁, c₂, c₃, c₄, c₅] at b₁ b₂ b₃ b₄ b₅ e₁ e₂ e₃ e₄ ⊢
        omega

/-- The walk-and-carry word from the strip's first column, with the potential
rising by at most `4m+2`. -/
theorem exists_exitWord_walk (R H : Fin n) (hRH : Nat.dist R.val H.val = 1)
    (col : ℕ → Fin n) (m : ℕ) (hcol : StripCol col (m+1))
    (X : Board n) (hX : blank X = (R, col 0)) :
    ∃ Y : Board n, ∃ cs : List (Cell n), Executes X cs Y ∧ cs.length ≤ 6*m ∧
      manhattan Y ≤ manhattan X+(4*m+2) ∧ blank Y = (R, col 0) ∧
      Y (R, col 1) = X (R, col (m+1)) ∧
      ∀ x ∈ cs, ∃ c, c ≤ m+1 ∧ (x = (R, col c) ∨ x = (H, col c)) := by
  obtain ⟨Y, hE, hbY, hT, h0, h1⟩ := exists_exitWord R H hRH col (m+1) hcol 0 m (by omega) X hX
  refine ⟨Y, _, hE, (exitWord_length R H col 0 m).le, ?_, hbY, by simpa using hT, ?_⟩
  · rcases Nat.eq_zero_or_pos m with hm | hm
    · rw [h0 hm]; omega
    · obtain ⟨-, hM⟩ := h1 hm
      have hd := hcol 0 1 (by omega) (by omega)
      have tri : ∀ u v w : Cell n, gridDistance u w ≤ gridDistance u v+gridDistance v w := by
        intro u v w; simp only [gridDistance, Nat.dist]; omega
      have h2 : gridDistance ((H, col 0) : Cell n) (R, col (0+1)) = 2 := by
        simp only [gridDistance, zero_add]
        rw [hd, Nat.dist_comm, hRH]; rfl
      have htri := tri (H, col 0) (R, col (0+1)) (position (target n) (X (R, col (0+1))))
      omega
  · intro x hx
    obtain ⟨c, -, hc, h⟩ := exitWord_mem R H col 0 m x hx
    exact ⟨c, by omega, h⟩

end
end SlidingPuzzle
