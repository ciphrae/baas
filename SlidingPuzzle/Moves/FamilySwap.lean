import SlidingPuzzle.Moves.Conveyor
import SlidingPuzzle.Moves.ProtectedTranslation
import SlidingPuzzle.Moves.Transpose

/-! Exchanging two row families by moving one next to the other. The upper
family descends row by row to just above the lower one; whichever of the two
lies further right is carried left along its row by a conveyor; the two
adjacent rows are exchanged by the row-shift word; the staging is undone by its
reverse path. Moves along a family's own row cost `2m+3` per cell, across rows
`6m+5`, so the cost reflects the distance between the families. -/
namespace SlidingPuzzle

variable {n : ℕ} [NeZero n]

/-- Lower a row segment by `V` rows, one protected shift at a time, with the
blank parked just left of the segment and two rows below it. -/
theorem exists_row_descent (B : Board n) (ro co m V : ℕ) (hm : 1 < m) (hco : 1 ≤ co)
    (hc : co+m ≤ n) (hr : ro+V+2 < n)
    (hb : blank B = (⟨ro+2, by omega⟩, ⟨co-1, by omega⟩)) :
    ∃ C : Board n, ∃ p : Path B C, p.length ≤ V*(6*m+5) ∧
      blank C = (⟨ro+V+2, hr⟩, ⟨co-1, by omega⟩) ∧
      (∀ t (ht : t < m), C (⟨ro+V, by omega⟩, ⟨co+t, by omega⟩) =
        B (⟨ro, by omega⟩, ⟨co+t, by omega⟩)) ∧
      (∀ x : Cell n, x.1.val < ro ∨ ro+V+2 < x.1.val ∨ x.2.val+1 < co ∨ co+m ≤ x.2.val ∨
        (ro+V < x.1.val ∧ x.2.val+1 ≠ co) → C x = B x) := by
  induction V generalizing ro B with
  | zero =>
    exact ⟨B, .nil B, by simp, by simpa using hb, fun t ht => rfl, fun _ _ => rfl⟩
  | succ V ih =>
    obtain ⟨B₁, p₁, hp₁, hb₁, hrow₁, hfix₁⟩ := exists_protected_row_shift_with_cost B ro co m
      (by omega) hc hm (by rw [hb])
    have hd : gridDistance (blank B) (⟨ro+2, by omega⟩, ⟨co, by omega⟩) = 1 := by
      rw [hb]; simp [gridDistance, Nat.dist]; omega
    rw [hd] at hp₁
    have hd₂ : gridDistance (blank B₁) (⟨ro+3, by omega⟩, ⟨co-1, by omega⟩) = 1 := by
      rw [hb₁, hb]; simp [gridDistance, Nat.dist]
    let B₂ := swapCells B₁ (blank B₁) (⟨ro+3, by omega⟩, ⟨co-1, by omega⟩)
    have hb₂ : blank B₂ = (⟨ro+1+2, by omega⟩, ⟨co-1, by omega⟩) := by
      rw [blank_swapCells]
    have hB₂ : ∀ x, x ≠ blank B₁ → x ≠ (⟨ro+3, by omega⟩, ⟨co-1, by omega⟩) → B₂ x = B₁ x :=
      fun x h1 h2 => swapCells_preserves B₁ h1 h2
    obtain ⟨C, p, hp, hbC, hrow, hfix⟩ := ih (ro := ro+1) (B := B₂) (by omega) hb₂
    refine ⟨C, p₁.append ((movePath B₁ _ hd₂).append p), ?_, ?_, ?_, ?_⟩
    · simp only [Path.length_append, movePath_length]; nlinarith
    · rw [hbC]; congr 2; omega
    · intro t ht
      have e : (⟨ro+(V+1), by omega⟩ : Fin n) = ⟨ro+1+V, by omega⟩ := Fin.ext (by simp; ring)
      rw [e, hrow t ht]
      rw [hB₂ _ (by rw [hb₁, hb]; intro h; have := congrArg (fun x : Cell n => x.1.val) h
                    simp at this)
          (by intro h; have := congrArg (fun x : Cell n => x.1.val) h; simp at this)]
      exact hrow₁ ⟨t, ht⟩
    · intro x hx
      rw [hfix x (by omega)]
      have hx₁ : x ≠ blank B₁ := by
        rw [hb₁, hb]; rintro rfl; simp at hx; omega
      have hx₂ : x ≠ (⟨ro+3, by omega⟩, ⟨co-1, by omega⟩) := by
        rintro rfl; simp at hx; omega
      rw [hB₂ x hx₁ hx₂]
      exact hfix₁ x (by omega)

/-- A row shift exchanges the two data rows as sets, at any position. -/
theorem exists_row_set_exchange_at (B : Board n) (ro co m : ℕ) (hm : 1 < m)
    (hr : ro+3 ≤ n) (hc : co+m ≤ n)
    (hb : blank B = (⟨ro+2, by omega⟩, ⟨co, by omega⟩)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 6*m+2 ∧ blank C = blank B ∧
      (∀ i (hi : i < m), ∃ j, ∃ hj : j < m,
        C (⟨ro, by omega⟩, ⟨co+i, by omega⟩) = B (⟨ro+1, by omega⟩, ⟨co+j, by omega⟩)) ∧
      (∀ i (hi : i < m), C (⟨ro+1, by omega⟩, ⟨co+i, by omega⟩) =
        B (⟨ro, by omega⟩, ⟨co+i, by omega⟩)) ∧
      ∀ x : Cell n, x.1.val < ro ∨ ro+2 ≤ x.1.val ∨ x.2.val < co ∨ co+m ≤ x.2.val →
        C x = B x := by
  obtain ⟨C, p, hp, hbC, hrow, hfix⟩ := exists_row_shift B ro co m hr hc hm hb
  refine ⟨C, p, hp, hbC, ?_, fun i hi => hrow ⟨i, hi⟩, hfix⟩
  intro i hi
  let x : Cell n := (⟨ro, by omega⟩, ⟨co+i, by omega⟩)
  let y := B.symm (C x)
  have hy : B y = C x := B.apply_symm_apply _
  have hyr : ro ≤ y.1.val ∧ y.1.val < ro+2 ∧ co ≤ y.2.val ∧ y.2.val < co+m := by
    by_contra hh
    have he : y = x := C.injective ((hfix y (by omega)).trans hy)
    have he' := congrArg (fun z : Cell n => (z.1.val, z.2.val)) he
    simp [x] at he'
    omega
  have hyr1 : y.1.val = ro+1 := by
    by_contra hh
    have hy0 : y = (⟨ro, by omega⟩, ⟨co+(y.2.val-co), by omega⟩) :=
      Prod.ext (Fin.ext (by simp; omega)) (Fin.ext (by simp; omega))
    have hh2 := hrow ⟨y.2.val-co, by omega⟩
    rw [← hy0, hy] at hh2
    have he := congrArg (fun z : Cell n => z.1.val) (C.injective hh2)
    simp [x] at he
  refine ⟨y.2.val-co, by omega, ?_⟩
  have hy' : y = (⟨ro+1, by omega⟩, ⟨co+(y.2.val-co), by omega⟩) :=
    Prod.ext (Fin.ext (by simp; omega)) (Fin.ext (by simp; omega))
  exact hy.symm.trans (congrArg B hy')

/-- A straight blank move along a row or column changes only the cells of that
segment. -/
private theorem exists_straight_access (B : Board n) (c : Cell n)
    (hline : (blank B).1 = c.1 ∨ (blank B).2 = c.2) :
    ∃ C : Board n, ∃ p : Path B C, blank C = c ∧ p.length ≤ n ∧
      p.length ≤ gridDistance (blank B) c ∧
      ∀ x : Cell n, (x.1.val < min (blank B).1.val c.1.val ∨ max (blank B).1.val c.1.val < x.1.val ∨
        x.2.val < min (blank B).2.val c.2.val ∨ max (blank B).2.val c.2.val < x.2.val) →
        C x = B x := by
  obtain ⟨C, p, hbC, hp, hfix⟩ := exists_blank_access_path_preserving B c
  refine ⟨C, p, hbC, hp.trans ?_, hp, hfix⟩
  have := (blank B).1.isLt; have := (blank B).2.isLt; have := c.1.isLt; have := c.2.isLt
  simp only [gridDistance, Nat.dist]
  rcases hline with h | h
  · rw [h]; omega
  · rw [h]; omega

/-- Stage two row families in adjacent rows `l-1`, `l` over the same columns:
the upper family descends, then the family further right moves left. -/
theorem exists_row_family_staging (B : Board n) (u l cu cl m : ℕ) (hm : 2 ≤ m)
    (hul : u < l) (hl2 : 2 ≤ l) (hln : l+2 ≤ n) (hcu : 1 ≤ cu) (hcl : 1 ≤ cl)
    (hcun : cu+m ≤ n) (hcln : cl+m ≤ n) (hpark : ∀ t, t < m → cl+t+1 ≠ cu)
    (hrow : (blank B).1.val ≠ u ∧ (blank B).1.val ≠ l) :
    ∃ c0 : ℕ, ∃ hc0 : c0+m ≤ n, ∃ D : Board n, ∃ S : Path B D,
      S.length ≤ 4*n+(l-1-u)*(6*m+5)+Nat.dist cu cl*(2*m+3) ∧
      blank D = (⟨l+1, by omega⟩, ⟨c0, by omega⟩) ∧
      (∀ t (ht : t < m), D (⟨l-1, by omega⟩, ⟨c0+t, by omega⟩) =
        B (⟨u, by omega⟩, ⟨cu+t, by omega⟩)) ∧
      (∀ t (ht : t < m), D (⟨l, by omega⟩, ⟨c0+t, by omega⟩) =
        B (⟨l, by omega⟩, ⟨cl+t, by omega⟩)) := by
  set V := l-1-u with hV
  -- S1, S2: route the blank along its row, then down column `cu-1`.
  obtain ⟨B₁, p₁, hb₁, hp₁, hp₁d, hf₁⟩ := exists_straight_access B ((blank B).1, ⟨cu-1, by omega⟩)
    (Or.inl rfl)
  obtain ⟨B₂, p₂, hb₂, hp₂, hp₂d, hf₂⟩ := exists_straight_access B₁ (⟨u+2, by omega⟩, ⟨cu-1, by omega⟩)
    (Or.inr (by rw [hb₁]))
  rw [hb₁] at hf₂
  have hU₂ : ∀ t (ht : t < m), B₂ (⟨u, by omega⟩, ⟨cu+t, by omega⟩) =
      B (⟨u, by omega⟩, ⟨cu+t, by omega⟩) := by
    intro t ht
    rw [hf₂ _ (by simp; omega), hf₁ _ (by simp; omega)]
  have hL₂ : ∀ t (ht : t < m), B₂ (⟨l, by omega⟩, ⟨cl+t, by omega⟩) =
      B (⟨l, by omega⟩, ⟨cl+t, by omega⟩) := by
    intro t ht
    have := hpark t ht
    rw [hf₂ _ (by simp; omega), hf₁ _ (by simp; omega)]
  -- S3: descend the upper family to row `l-1`.
  obtain ⟨B₃, p₃, hp₃, hb₃, hU₃, hf₃⟩ := exists_row_descent B₂ u cu m V (by omega) hcu hcun
    (by omega) (by rw [hb₂])
  have hU₃' : ∀ t (ht : t < m), B₃ (⟨l-1, by omega⟩, ⟨cu+t, by omega⟩) =
      B (⟨u, by omega⟩, ⟨cu+t, by omega⟩) := by
    intro t ht
    have e : (⟨l-1, by omega⟩ : Fin n) = ⟨u+V, by omega⟩ := Fin.ext (by simp; omega)
    rw [e, hU₃ t ht, hU₂ t ht]
  have hL₃ : ∀ t (ht : t < m), B₃ (⟨l, by omega⟩, ⟨cl+t, by omega⟩) =
      B (⟨l, by omega⟩, ⟨cl+t, by omega⟩) := by
    intro t ht
    have := hpark t ht
    rw [hf₃ _ (by simp; omega), hL₂ t ht]
  have hlen₁₂ : p₁.length+p₂.length ≤ 2*n := by omega
  by_cases hcase : cl ≤ cu
  · -- Case A: the upper family moves left along row `l-1`, lane `l-2`.
    obtain ⟨B₄, p₄, hb₄, hp₄, hp₄d, hf₄⟩ := exists_straight_access B₃ (⟨l-1, by omega⟩, ⟨cu-1, by omega⟩)
      (Or.inr (by rw [hb₃]))
    rw [hb₃] at hf₄
    have hU₄ : ∀ t (ht : t < m), B₄ (⟨l-1, by omega⟩, ⟨cu+t, by omega⟩) =
        B (⟨u, by omega⟩, ⟨cu+t, by omega⟩) := by
      intro t ht; rw [hf₄ _ (by simp; omega), hU₃' t ht]
    have hL₄ : ∀ t (ht : t < m), B₄ (⟨l, by omega⟩, ⟨cl+t, by omega⟩) =
        B (⟨l, by omega⟩, ⟨cl+t, by omega⟩) := by
      intro t ht; have := hpark t ht; rw [hf₄ _ (by simp; omega), hL₃ t ht]
    obtain ⟨B₅, p₅, hp₅, hb₅, hU₅, hf₅⟩ := exists_conveyor B₄ ⟨l-1, by omega⟩ ⟨l-2, by omega⟩
      (by simp [Nat.dist]; omega) (cl-1) m (cu-cl) (by omega)
      (by rw [hb₄]; exact Prod.ext rfl (Fin.ext (by simp; omega)))
    have hU₅ : ∀ t (ht : t < m), B₅ (⟨l-1, by omega⟩, ⟨cl+t, by omega⟩) =
        B (⟨u, by omega⟩, ⟨cu+t, by omega⟩) := by
      intro t ht
      have h := hU₅ t ht
      have e1 : ((⟨l-1, by omega⟩ : Fin n), (⟨cl-1+1+t, by omega⟩ : Fin n)) =
          (⟨l-1, by omega⟩, ⟨cl+t, by omega⟩) := Prod.ext rfl (Fin.ext (by simp; omega))
      have e2 : ((⟨l-1, by omega⟩ : Fin n), (⟨cl-1+(cu-cl)+1+t, by omega⟩ : Fin n)) =
          (⟨l-1, by omega⟩, ⟨cu+t, by omega⟩) := Prod.ext rfl (Fin.ext (by simp; omega))
      rw [e1, e2] at h
      rw [h, hU₄ t ht]
    have hL₅ : ∀ t (ht : t < m), B₅ (⟨l, by omega⟩, ⟨cl+t, by omega⟩) =
        B (⟨l, by omega⟩, ⟨cl+t, by omega⟩) := by
      intro t ht; rw [hf₅ _ (Or.inl (by simp; omega)), hL₄ t ht]
    obtain ⟨B₆, p₆, hb₆, hp₆, hp₆d, hf₆⟩ := exists_straight_access B₅ (⟨l+1, by omega⟩, ⟨cl-1, by omega⟩)
      (Or.inr (by rw [hb₅]))
    rw [hb₅] at hf₆
    obtain ⟨B₇, p₇, hb₇, hp₇, hp₇d, hf₇⟩ := exists_straight_access B₆ (⟨l+1, by omega⟩, ⟨cl, by omega⟩)
      (Or.inl (by rw [hb₆]))
    rw [hb₆] at hf₇
    have hd₄ : gridDistance (blank B₃) (⟨l-1, by omega⟩, ⟨cu-1, by omega⟩) = 2 := by
      rw [hb₃]; simp [gridDistance, Nat.dist]; omega
    have hd₆ : gridDistance (blank B₅) (⟨l+1, by omega⟩, ⟨cl-1, by omega⟩) = 2 := by
      rw [hb₅]; simp [gridDistance, Nat.dist]; omega
    have hd₇ : gridDistance (blank B₆) (⟨l+1, by omega⟩, ⟨cl, by omega⟩) = 1 := by
      rw [hb₆]; simp [gridDistance, Nat.dist]; omega
    refine ⟨cl, hcln, B₇, p₁.append (p₂.append (p₃.append (p₄.append (p₅.append
      (p₆.append p₇))))), ?_, hb₇, ?_, ?_⟩
    · simp only [Path.length_append]
      have hD : Nat.dist cu cl = cu-cl := by simp [Nat.dist]; omega
      rw [hD]
      omega
    · intro t ht
      rw [hf₇ _ (by simp <;> omega), hf₆ _ (by simp <;> omega), hU₅ t ht]
    · intro t ht
      rw [hf₇ _ (by simp <;> omega), hf₆ _ (by simp <;> omega), hL₅ t ht]
  · -- Case B: the lower family moves left along row `l`, lane `l+1`.
    obtain ⟨B₄, p₄, hb₄, hp₄, hp₄d, hf₄⟩ := exists_straight_access B₃ (⟨l+1, by omega⟩, ⟨cl-1, by omega⟩)
      (Or.inl (by rw [hb₃]; exact Fin.ext (by simp; omega)))
    rw [hb₃] at hf₄
    obtain ⟨B₅, p₅, hb₅, hp₅, hp₅d, hf₅⟩ := exists_straight_access B₄ (⟨l, by omega⟩, ⟨cl-1, by omega⟩)
      (Or.inr (by rw [hb₄]))
    rw [hb₄] at hf₅
    have hU₅ : ∀ t (ht : t < m), B₅ (⟨l-1, by omega⟩, ⟨cu+t, by omega⟩) =
        B (⟨u, by omega⟩, ⟨cu+t, by omega⟩) := by
      intro t ht; rw [hf₅ _ (by simp; omega), hf₄ _ (by simp; omega), hU₃' t ht]
    have hL₅ : ∀ t (ht : t < m), B₅ (⟨l, by omega⟩, ⟨cl+t, by omega⟩) =
        B (⟨l, by omega⟩, ⟨cl+t, by omega⟩) := by
      intro t ht; rw [hf₅ _ (by simp; omega), hf₄ _ (by simp; omega), hL₃ t ht]
    obtain ⟨B₆, p₆, hp₆, hb₆, hL₆, hf₆⟩ := exists_conveyor B₅ ⟨l, by omega⟩ ⟨l+1, by omega⟩
      (by simp [Nat.dist]) (cu-1) m (cl-cu) (by omega)
      (by rw [hb₅]; exact Prod.ext rfl (Fin.ext (by simp; omega)))
    have hL₆' : ∀ t (ht : t < m), B₆ (⟨l, by omega⟩, ⟨cu+t, by omega⟩) =
        B (⟨l, by omega⟩, ⟨cl+t, by omega⟩) := by
      intro t ht
      have h := hL₆ t ht
      have e1 : ((⟨l, by omega⟩ : Fin n), (⟨cu-1+1+t, by omega⟩ : Fin n)) =
          (⟨l, by omega⟩, ⟨cu+t, by omega⟩) := Prod.ext rfl (Fin.ext (by simp; omega))
      have e2 : ((⟨l, by omega⟩ : Fin n), (⟨cu-1+(cl-cu)+1+t, by omega⟩ : Fin n)) =
          (⟨l, by omega⟩, ⟨cl+t, by omega⟩) := Prod.ext rfl (Fin.ext (by simp; omega))
      rw [e1, e2] at h
      rw [h, hL₅ t ht]
    have hU₆ : ∀ t (ht : t < m), B₆ (⟨l-1, by omega⟩, ⟨cu+t, by omega⟩) =
        B (⟨u, by omega⟩, ⟨cu+t, by omega⟩) := by
      intro t ht; rw [hf₆ _ (Or.inl (by simp; omega)), hU₅ t ht]
    obtain ⟨B₇, p₇, hb₇, hp₇, hp₇d, hf₇⟩ := exists_straight_access B₆ (⟨l+1, by omega⟩, ⟨cu-1, by omega⟩)
      (Or.inr (by rw [hb₆]))
    rw [hb₆] at hf₇
    obtain ⟨B₈, p₈, hb₈, hp₈, hp₈d, hf₈⟩ := exists_straight_access B₇ (⟨l+1, by omega⟩, ⟨cu, by omega⟩)
      (Or.inl (by rw [hb₇]))
    rw [hb₇] at hf₈
    have hd₄ : gridDistance (blank B₃) (⟨l+1, by omega⟩, ⟨cl-1, by omega⟩) = cl-cu := by
      rw [hb₃]; simp [gridDistance, Nat.dist]; omega
    have hd₅ : gridDistance (blank B₄) (⟨l, by omega⟩, ⟨cl-1, by omega⟩) = 1 := by
      rw [hb₄]; simp [gridDistance, Nat.dist]
    have hd₇ : gridDistance (blank B₆) (⟨l+1, by omega⟩, ⟨cu-1, by omega⟩) = 1 := by
      rw [hb₆]; simp [gridDistance, Nat.dist]
    have hd₈ : gridDistance (blank B₇) (⟨l+1, by omega⟩, ⟨cu, by omega⟩) = 1 := by
      rw [hb₇]; simp [gridDistance, Nat.dist]; omega
    refine ⟨cu, hcun, B₈, p₁.append (p₂.append (p₃.append (p₄.append (p₅.append
      (p₆.append (p₇.append p₈)))))), ?_, hb₈, ?_, ?_⟩
    · simp only [Path.length_append]
      have hD : Nat.dist cu cl = cl-cu := by simp [Nat.dist]; omega
      rw [hD]
      have hcl' : cl ≤ n := by omega
      omega
    · intro t ht
      rw [hf₈ _ (by simp <;> omega), hf₇ _ (by simp <;> omega), hU₆ t ht]
    · intro t ht
      rw [hf₈ _ (by simp <;> omega), hf₇ _ (by simp <;> omega), hL₆' t ht]

/-- Exchange two row families: stage them in adjacent rows, exchange the rows,
undo the staging. -/
theorem exists_row_family_swap (B : Board n) (u l cu cl m : ℕ) (hm : 2 ≤ m)
    (hul : u < l) (hl2 : 2 ≤ l) (hln : l+2 ≤ n) (hcu : 1 ≤ cu) (hcl : 1 ≤ cl)
    (hcun : cu+m ≤ n) (hcln : cl+m ≤ n) (hpark : ∀ t, t < m → cl+t+1 ≠ cu)
    (hrow : (blank B).1.val ≠ u ∧ (blank B).1.val ≠ l) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 8*n+2*((l-1-u)*(6*m+5))+2*(Nat.dist cu cl*(2*m+3))+(6*m+2) ∧
      blank C = blank B ∧
      (∀ t (ht : t < m), ∃ j, ∃ hj : j < m, C (⟨u, by omega⟩, ⟨cu+t, by omega⟩) =
        B (⟨l, by omega⟩, ⟨cl+j, by omega⟩)) ∧
      (∀ t (ht : t < m), C (⟨l, by omega⟩, ⟨cl+t, by omega⟩) =
        B (⟨u, by omega⟩, ⟨cu+t, by omega⟩)) ∧
      (∀ x : Cell n, (∀ t (ht : t < m), x ≠ (⟨u, by omega⟩, ⟨cu+t, by omega⟩)) →
        (∀ t (ht : t < m), x ≠ (⟨l, by omega⟩, ⟨cl+t, by omega⟩)) → C x = B x) := by
  obtain ⟨c0, hc0, D, S, hS, hbD, hDU, hDL⟩ :=
    exists_row_family_staging B u l cu cl m hm hul hl2 hln hcu hcl hcun hcln hpark hrow
  obtain ⟨E, q, hq, hbE, hEa, hEb, hfixE⟩ := exists_row_set_exchange_at D (l-1) c0 m
    (by omega) (by omega) hc0 (by rw [hbD]; exact Prod.ext (Fin.ext (by simp; omega)) rfl)
  obtain ⟨C, r, hr, hbC, hC⟩ := S.exists_unstaged q hbE
  have hposU : ∀ t (ht : t < m), D.symm (B (⟨u, by omega⟩, ⟨cu+t, by omega⟩)) =
      (⟨l-1, by omega⟩, ⟨c0+t, by omega⟩) := by
    intro t ht; rw [← hDU t ht]; simp
  have hposL : ∀ t (ht : t < m), D.symm (B (⟨l, by omega⟩, ⟨cl+t, by omega⟩)) =
      (⟨l, by omega⟩, ⟨c0+t, by omega⟩) := by
    intro t ht; rw [← hDL t ht]; simp
  refine ⟨C, r, by rw [hr]; omega, hbC, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨j, hj, hE⟩ := hEa t ht
    refine ⟨j, hj, ?_⟩
    rw [hC, hposU t ht, hE]
    have e : (⟨l-1+1, by omega⟩ : Fin n) = ⟨l, by omega⟩ := Fin.ext (by simp; omega)
    rw [e, hDL j hj]
  · intro t ht
    rw [hC, hposL t ht]
    have e : (⟨l, by omega⟩ : Fin n) = ⟨l-1+1, by omega⟩ := Fin.ext (by simp; omega)
    rw [e, hEb t ht, hDU t ht]
  · intro x hxU hxL
    rw [hC, hfixE]
    · exact D.apply_symm_apply (B x)
    · by_contra hh
      set y := D.symm (B x) with hy
      have hyD : D y = B x := D.apply_symm_apply _
      have hy2 : c0 ≤ y.2.val ∧ y.2.val < c0+m := by omega
      have hy1 : y.1.val = l-1 ∨ y.1.val = l := by omega
      rcases hy1 with h1 | h1
      · have e : y = (⟨l-1, by omega⟩, ⟨c0+(y.2.val-c0), by omega⟩) :=
          Prod.ext (Fin.ext (by simp; omega)) (Fin.ext (by simp; omega))
        rw [e, hDU _ (by omega)] at hyD
        exact hxU _ (by omega) (B.injective hyD).symm
      · have e : y = (⟨l, by omega⟩, ⟨c0+(y.2.val-c0), by omega⟩) :=
          Prod.ext (Fin.ext (by simp; omega)) (Fin.ext (by simp; omega))
        rw [e, hDL _ (by omega)] at hyD
        exact hxL _ (by omega) (B.injective hyD).symm

/-- Exchange two column families, the left one at column `c₁`. -/
private theorem exists_column_family_swap_lt (B : Board n) (c₁ c₂ r₁ r₂ m : ℕ) (hm : 2 ≤ m)
    (hc : c₁ < c₂) (hc2 : 2 ≤ c₂) (hcn : c₂+2 ≤ n) (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂)
    (hr₁n : r₁+m ≤ n) (hr₂n : r₂+m ≤ n) (hpark : ∀ t, t < m → r₂+t+1 ≠ r₁)
    (hcol : (blank B).2.val ≠ c₁ ∧ (blank B).2.val ≠ c₂) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 8*n+2*((c₂-1-c₁)*(6*m+5))+2*(Nat.dist r₁ r₂*(2*m+3))+(6*m+2) ∧
      blank C = blank B ∧
      (∀ t (ht : t < m), ∃ j, ∃ hj : j < m, C (⟨r₁+t, by omega⟩, ⟨c₁, by omega⟩) =
        B (⟨r₂+j, by omega⟩, ⟨c₂, by omega⟩)) ∧
      (∀ t (ht : t < m), ∃ j, ∃ hj : j < m, C (⟨r₂+t, by omega⟩, ⟨c₂, by omega⟩) =
        B (⟨r₁+j, by omega⟩, ⟨c₁, by omega⟩)) ∧
      (∀ x : Cell n, (∀ t (ht : t < m), x ≠ (⟨r₁+t, by omega⟩, ⟨c₁, by omega⟩)) →
        (∀ t (ht : t < m), x ≠ (⟨r₂+t, by omega⟩, ⟨c₂, by omega⟩)) → C x = B x) := by
  obtain ⟨C', q, hq, hbC', hU, hL, hfix⟩ := exists_row_family_swap (transposeBoard B)
    c₁ c₂ r₁ r₂ m hm hc hc2 hcn hr₁ hr₂ hr₁n hr₂n hpark (by simpa using hcol)
  have htr : ∃ q' : Path B (transposeBoard C'), q'.length = q.length := by
    have h := q.exists_transpose
    rw [transposeBoard_transposeBoard] at h
    exact h
  obtain ⟨q', hq'⟩ := htr
  refine ⟨transposeBoard C', q', by rw [hq']; exact hq, ?_, ?_, ?_, ?_⟩
  · rw [blank_transposeBoard, hbC', blank_transposeBoard, Prod.swap_swap]
  · intro t ht
    obtain ⟨j, hj, h⟩ := hU t ht
    exact ⟨j, hj, h⟩
  · intro t ht
    exact ⟨t, ht, hL t ht⟩
  · intro x hx1 hx2
    change C' x.swap = B x
    rw [hfix x.swap (fun t ht h => hx1 t ht (by rw [← Prod.swap_swap x, h]; rfl))
      (fun t ht h => hx2 t ht (by rw [← Prod.swap_swap x, h]; rfl))]
    rfl

/-- Exchange two column families of `m` tiles, at columns `c₁ ≠ c₂` with top
rows `r₁`, `r₂`. The cost is `12m` per column and `4m` per row between them,
plus `8n+6m+2`. -/
theorem exists_column_family_swap (B : Board n) (c₁ c₂ r₁ r₂ m : ℕ) (hm : 2 ≤ m)
    (hc : c₁ ≠ c₂) (hc2 : 2 ≤ max c₁ c₂) (hcn : max c₁ c₂+2 ≤ n) (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂)
    (hr₁n : r₁+m ≤ n) (hr₂n : r₂+m ≤ n)
    (hpark : ∀ t, t < m → r₂+t+1 ≠ r₁ ∧ r₁+t+1 ≠ r₂)
    (hcol : (blank B).2.val ≠ c₁ ∧ (blank B).2.val ≠ c₂) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 8*n+2*((Nat.dist c₁ c₂-1)*(6*m+5))+2*(Nat.dist r₁ r₂*(2*m+3))+(6*m+2) ∧
      blank C = blank B ∧
      (∀ t (ht : t < m), ∃ j, ∃ hj : j < m, C (⟨r₁+t, by omega⟩, ⟨c₁, by omega⟩) =
        B (⟨r₂+j, by omega⟩, ⟨c₂, by omega⟩)) ∧
      (∀ t (ht : t < m), ∃ j, ∃ hj : j < m, C (⟨r₂+t, by omega⟩, ⟨c₂, by omega⟩) =
        B (⟨r₁+j, by omega⟩, ⟨c₁, by omega⟩)) ∧
      (∀ x : Cell n, (∀ t (ht : t < m), x ≠ (⟨r₁+t, by omega⟩, ⟨c₁, by omega⟩)) →
        (∀ t (ht : t < m), x ≠ (⟨r₂+t, by omega⟩, ⟨c₂, by omega⟩)) → C x = B x) := by
  rcases Nat.lt_or_gt_of_ne hc with h | h
  · obtain ⟨C, p, hp, hb, h1, h2, hf⟩ := exists_column_family_swap_lt B c₁ c₂ r₁ r₂ m hm h
      (by omega) (by omega) hr₁ hr₂ hr₁n hr₂n (fun t ht => (hpark t ht).1) hcol
    refine ⟨C, p, ?_, hb, h1, h2, hf⟩
    have : Nat.dist c₁ c₂ = c₂-c₁ := by simp [Nat.dist]; omega
    rw [this, show c₂-c₁-1 = c₂-1-c₁ by omega]; exact hp
  · obtain ⟨C, p, hp, hb, h1, h2, hf⟩ := exists_column_family_swap_lt B c₂ c₁ r₂ r₁ m hm h
      (by omega) (by omega) hr₂ hr₁ hr₂n hr₁n (fun t ht => (hpark t ht).2) ⟨hcol.2, hcol.1⟩
    refine ⟨C, p, ?_, hb, h2, h1, fun x a b => hf x b a⟩
    have : Nat.dist c₁ c₂ = c₁-c₂ := by simp [Nat.dist]; omega
    rw [this, show c₁-c₂-1 = c₁-1-c₂ by omega, Nat.dist_comm r₁]; exact hp

end SlidingPuzzle
