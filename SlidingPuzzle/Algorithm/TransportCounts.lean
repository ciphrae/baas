import Mathlib

/-! A finite transport-count abstraction for Algorithm 4.

The rows and columns are `Fin (m + 1)`.  A move transports one unit from the
incoming off-diagonal entry `(j,i)` into the diagonal entry `(i,i)` and makes
`j` the new blank index.
-/
namespace SlidingPuzzle.TransportCounts

abbrev CountMatrix (m : ℕ) := Fin (m + 1) → Fin (m + 1) → ℕ

variable {m : ℕ}

def offdiagMass (C : CountMatrix m) : ℕ :=
  ∑ r, ∑ c, if r = c then 0 else C r c

def rowSum (C : CountMatrix m) (r : Fin (m + 1)) : ℕ := ∑ c, C r c

def colSum (C : CountMatrix m) (c : Fin (m + 1)) : ℕ := ∑ r, C r c

def incoming (C : CountMatrix m) (i : Fin (m + 1)) : ℕ :=
  ∑ r, if r = i then 0 else C r i

def move (C : CountMatrix m) (i j : Fin (m + 1)) : CountMatrix m :=
  fun r c =>
    if r = j ∧ c = i then C r c - 1
    else if r = i ∧ c = i then C r c + 1
    else C r c

def Chooses (C : CountMatrix m) (i j : Fin (m + 1)) : Prop :=
  j ≠ i ∧ 0 < C j i ∧ ∀ r, r ≠ i → 0 < C r i → j ≤ r

theorem move_at_source (C : CountMatrix m) {i j : Fin (m + 1)} (_hji : j ≠ i) :
    move C i j j i = C j i - 1 := by
  simp [move]

theorem move_at_diagonal (C : CountMatrix m) {i j : Fin (m + 1)} (hji : j ≠ i) :
    move C i j i i = C i i + 1 := by
  simp [move, hji.symm]

theorem move_unchanged (C : CountMatrix m) {i j r c : Fin (m + 1)}
    (hsrc : ¬ (r = j ∧ c = i)) (hdiag : ¬ (r = i ∧ c = i)) :
    move C i j r c = C r c := by
  simp [move, hsrc, hdiag]

theorem move_offdiag_le (C : CountMatrix m) (i j r c : Fin (m + 1)) (hrc : r ≠ c) :
    move C i j r c ≤ C r c := by
  have hdiag : ¬ (r = i ∧ c = i) := by rintro ⟨hr, hc⟩; exact hrc (hr.trans hc.symm)
  by_cases hsrc : r = j ∧ c = i
  · simp [move, hsrc]
  · simp [move, hsrc, hdiag]

theorem incoming_eq_erase (C : CountMatrix m) (i : Fin (m + 1)) :
    incoming C i = ∑ r ∈ Finset.univ.erase i, C r i := by
  classical
  let f : Fin (m + 1) → ℕ := fun r => if r = i then 0 else C r i
  change (∑ r, f r) = _
  rw [← Finset.sum_erase Finset.univ (show f i = 0 by simp [f])]
  apply Finset.sum_congr rfl
  intro r hr
  simp [f, (Finset.mem_erase.mp hr).1]

theorem offdiagMass_eq_sum_incoming (C : CountMatrix m) :
    offdiagMass C = ∑ i, incoming C i := by
  classical
  unfold offdiagMass incoming
  rw [Finset.sum_comm]

theorem incoming_move (C : CountMatrix m) {i j : Fin (m + 1)}
    (hji : j ≠ i) (hpos : 0 < C j i) :
    incoming (move C i j) i = incoming C i - 1 := by
  rw [incoming_eq_erase, incoming_eq_erase]
  rw [← Finset.sum_erase_add (Finset.univ.erase i) (fun r => move C i j r i)
    (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩)]
  rw [← Finset.sum_erase_add (Finset.univ.erase i) (fun r => C r i)
    (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩)]
  simp only [move_at_source C hji]
  have hrest :
      ∑ r ∈ (Finset.univ.erase i).erase j, move C i j r i =
        ∑ r ∈ (Finset.univ.erase i).erase j, C r i := by
    apply Finset.sum_congr rfl
    intro r hr
    have hri : r ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
    have hrj : r ≠ j := (Finset.mem_erase.mp hr).1
    simp [move, hri, hrj]
  rw [hrest]
  omega

theorem incoming_move_ne (C : CountMatrix m) {i j k : Fin (m + 1)} (hki : k ≠ i) :
    incoming (move C i j) k = incoming C k := by
  rw [incoming_eq_erase, incoming_eq_erase]
  apply Finset.sum_congr rfl
  intro r hr
  have hrk : r ≠ k := (Finset.mem_erase.mp hr).1
  simp only [move]
  by_cases hsrc : r = j ∧ k = i
  · exact False.elim (hki hsrc.2)
  by_cases hdiag : r = i ∧ k = i
  · exact False.elim (hki hdiag.2)
  simp [hsrc, hdiag]

theorem offdiagMass_move (C : CountMatrix m) {i j : Fin (m + 1)}
    (hji : j ≠ i) (hpos : 0 < C j i) :
    offdiagMass (move C i j) = offdiagMass C - 1 := by
  rw [offdiagMass_eq_sum_incoming, offdiagMass_eq_sum_incoming]
  rw [← Finset.sum_erase_add Finset.univ (incoming (move C i j)) (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add Finset.univ (incoming C) (Finset.mem_univ i)]
  rw [incoming_move C hji hpos]
  have hrest : ∑ k ∈ Finset.univ.erase i, incoming (move C i j) k =
      ∑ k ∈ Finset.univ.erase i, incoming C k := by
    apply Finset.sum_congr rfl
    intro k hk
    exact incoming_move_ne C (Finset.mem_erase.mp hk).1
  rw [hrest]
  have hin : 0 < incoming C i := by
    rw [incoming_eq_erase]
    exact lt_of_lt_of_le hpos
      (Finset.single_le_sum (s := Finset.univ.erase i) (f := fun r => C r i)
        (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩))
  omega

theorem rowSum_move_source (C : CountMatrix m) {i j : Fin (m + 1)}
    (hji : j ≠ i) (hpos : 0 < C j i) :
    rowSum (move C i j) j = rowSum C j - 1 := by
  unfold rowSum
  rw [← Finset.sum_erase_add Finset.univ (fun c => move C i j j c) (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add Finset.univ (fun c => C j c) (Finset.mem_univ i)]
  simp only [move_at_source C hji]
  have hrest : ∑ c ∈ Finset.univ.erase i, move C i j j c =
      ∑ c ∈ Finset.univ.erase i, C j c := by
    apply Finset.sum_congr rfl
    intro c hc
    have hci : c ≠ i := (Finset.mem_erase.mp hc).1
    simp [move, hji, hci]
  rw [hrest]
  omega

theorem rowSum_move_blank (C : CountMatrix m) {i j : Fin (m + 1)}
    (hji : j ≠ i) :
    rowSum (move C i j) i = rowSum C i + 1 := by
  unfold rowSum
  rw [← Finset.sum_erase_add Finset.univ (fun c => move C i j i c) (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add Finset.univ (fun c => C i c) (Finset.mem_univ i)]
  simp only [move_at_diagonal C hji]
  have hrest : ∑ c ∈ Finset.univ.erase i, move C i j i c =
      ∑ c ∈ Finset.univ.erase i, C i c := by
    apply Finset.sum_congr rfl
    intro c hc
    have hci : c ≠ i := (Finset.mem_erase.mp hc).1
    simp [move, hci]
  rw [hrest]
  omega

theorem rowSum_move_ne (C : CountMatrix m) {i j r : Fin (m + 1)}
    (hri : r ≠ i) (hrj : r ≠ j) : rowSum (move C i j) r = rowSum C r := by
  unfold rowSum
  apply Finset.sum_congr rfl
  intro c hc
  simp [move, hri, hrj]

theorem colSum_move_blank (C : CountMatrix m) {i j : Fin (m + 1)}
    (hji : j ≠ i) (hpos : 0 < C j i) :
    colSum (move C i j) i = colSum C i := by
  unfold colSum
  rw [← Finset.sum_erase_add Finset.univ (fun r => move C i j r i) (Finset.mem_univ j)]
  rw [← Finset.sum_erase_add Finset.univ (fun r => C r i) (Finset.mem_univ j)]
  simp only [move_at_source C hji]
  rw [← Finset.sum_erase_add (Finset.univ.erase j) (fun r => move C i j r i)
    (Finset.mem_erase.mpr ⟨hji.symm, Finset.mem_univ _⟩)]
  rw [← Finset.sum_erase_add (Finset.univ.erase j) (fun r => C r i)
    (Finset.mem_erase.mpr ⟨hji.symm, Finset.mem_univ _⟩)]
  simp only [move_at_diagonal C hji]
  have hrest :
      ∑ r ∈ (Finset.univ.erase j).erase i, move C i j r i =
        ∑ r ∈ (Finset.univ.erase j).erase i, C r i := by
    apply Finset.sum_congr rfl
    intro r hr
    have hri : r ≠ i := (Finset.mem_erase.mp hr).1
    have hrj : r ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
    simp [move, hri, hrj]
  rw [hrest]
  omega

theorem colSum_move_ne (C : CountMatrix m) {i j c : Fin (m + 1)} (hci : c ≠ i) :
    colSum (move C i j) c = colSum C c := by
  unfold colSum
  apply Finset.sum_congr rfl
  intro r hr
  simp [move, hci]

/-- If the last row has a zero in a non-last column, that whole column has no
off-diagonal mass. -/
def LastInvariant (C : CountMatrix m) : Prop :=
  ∀ c, c ≠ Fin.last m → C (Fin.last m) c = 0 → ∀ r, r ≠ c → C r c = 0

theorem lastInvariant_of_last_row_positive (C : CountMatrix m)
    (hpositive : ∀ c, c ≠ Fin.last m → 0 < C (Fin.last m) c) :
    LastInvariant C := by
  intro c hc hzero
  exact False.elim ((Nat.ne_of_gt (hpositive c hc)) hzero)

/-- The minimum-source rule preserves the last-row empty-column invariant. -/
theorem lastInvariant_move (C : CountMatrix m) {i j : Fin (m + 1)}
    (hC : LastInvariant C) (hchoice : Chooses C i j) :
    LastInvariant (move C i j) := by
  rcases hchoice with ⟨hji, hpos, hmin⟩
  intro c hc hlast r hrc
  by_cases hci : c = i
  · subst c
    have hiL : i ≠ Fin.last m := hc
    have hjL : j = Fin.last m := by
      by_contra hjL
      have hsame : move C i j (Fin.last m) i = C (Fin.last m) i := by
        apply move_unchanged
        · rintro ⟨h, _⟩
          exact hjL h.symm
        · rintro ⟨h, _⟩
          exact hiL h.symm
      rw [hsame] at hlast
      have hz := hC i hiL hlast j hji
      exact (Nat.ne_of_gt hpos) hz
    subst j
    by_cases hrL : r = Fin.last m
    · subst r
      simpa [move] using hlast
    · have hzero : C r i = 0 := by
        by_contra hne
        have hpositive : 0 < C r i := Nat.pos_of_ne_zero hne
        have hle : Fin.last m ≤ r := hmin r hrc hpositive
        exact hrL (le_antisymm (Fin.le_last r) hle)
      simp [move, hrL, hrc, hzero]
  · have hlastOld : C (Fin.last m) c = 0 := by
      have hsame : move C i j (Fin.last m) c = C (Fin.last m) c := by
        apply move_unchanged
        · simp [hci]
        · simp [hci]
      rwa [hsame] at hlast
    have hzero := hC c hc hlastOld r hrc
    rw [move_unchanged C (by simp [hci]) (by simp [hci])]
    exact hzero

/-- Row capacities reserve one unit for the current blank; column capacities
reserve one unit in the distinguished last column. -/
def Margins (C : CountMatrix m) (blank : Fin (m + 1)) (capacity : ℕ) : Prop :=
  (∀ r, rowSum C r + (if r = blank then 1 else 0) = capacity) ∧
    ∀ c, colSum C c + (if c = Fin.last m then 1 else 0) = capacity

theorem margins_move (C : CountMatrix m) {i j : Fin (m + 1)} {capacity : ℕ}
    (hMargins : Margins C i capacity) (hchoice : Chooses C i j) :
    Margins (move C i j) j capacity := by
  rcases hchoice with ⟨hji, hpos, hmin⟩
  constructor
  · intro r
    by_cases hri : r = i
    · subst r
      rw [rowSum_move_blank C hji]
      have h := hMargins.1 i
      simp [hji.symm] at h ⊢
      omega
    by_cases hrj : r = j
    · subst r
      rw [rowSum_move_source C hji hpos]
      have h := hMargins.1 j
      have hrowpos : 0 < rowSum C j :=
        lt_of_lt_of_le hpos
          (Finset.single_le_sum (s := Finset.univ) (f := fun c => C j c)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
      simp [hji] at h ⊢
      omega
    · rw [rowSum_move_ne C hri hrj]
      simpa [hri, hrj] using hMargins.1 r
  · intro c
    by_cases hci : c = i
    · subst c
      rw [colSum_move_blank C hji hpos]
      exact hMargins.2 i
    · rw [colSum_move_ne C hci]
      exact hMargins.2 c

theorem colSum_eq_diag_of_incoming_zero (C : CountMatrix m) (i : Fin (m + 1))
    (hzero : incoming C i = 0) : colSum C i = C i i := by
  unfold colSum
  rw [← Finset.sum_erase_add Finset.univ (fun r => C r i) (Finset.mem_univ i)]
  rw [← incoming_eq_erase C i, hzero]
  simp

theorem incoming_zero_entry (C : CountMatrix m) {i r : Fin (m + 1)}
    (hzero : incoming C i = 0) (hri : r ≠ i) : C r i = 0 := by
  rw [incoming_eq_erase] at hzero
  have hle : C r i ≤ ∑ x ∈ Finset.univ.erase i, C x i :=
    Finset.single_le_sum (s := Finset.univ.erase i) (f := fun x => C x i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hri, Finset.mem_univ _⟩)
  omega

theorem row_offdiag_zero_of_rowSum_eq_diag (C : CountMatrix m) (r c : Fin (m + 1))
    (hsum : rowSum C r = C r r) (hcr : c ≠ r) : C r c = 0 := by
  unfold rowSum at hsum
  rw [← Finset.sum_erase_add Finset.univ (fun x => C r x) (Finset.mem_univ r)] at hsum
  have hsumzero : ∑ x ∈ Finset.univ.erase r, C r x = 0 := by omega
  have hle : C r c ≤ ∑ x ∈ Finset.univ.erase r, C r x :=
    Finset.single_le_sum (s := Finset.univ.erase r) (f := fun x => C r x)
      (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hcr, Finset.mem_univ _⟩)
  omega

/-- At an incoming-empty blank, the capacity margins force that blank to be
the last index; the last-row invariant then forces every transport count off
the diagonal to vanish. -/
theorem terminal_of_margins (C : CountMatrix m) (i : Fin (m + 1)) (capacity : ℕ)
    (hMargins : Margins C i capacity) (hInvariant : LastInvariant C)
    (hincoming : incoming C i = 0) : i = Fin.last m ∧ offdiagMass C = 0 := by
  have hcol : colSum C i = C i i := colSum_eq_diag_of_incoming_zero C i hincoming
  have hdiag_le_row : C i i ≤ rowSum C i :=
    Finset.single_le_sum (s := Finset.univ) (f := fun c => C i c)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hilast : i = Fin.last m := by
    by_contra hne
    have hrow := hMargins.1 i
    have hcolumn := hMargins.2 i
    simp [hne, hcol] at hrow hcolumn
    omega
  subst i
  constructor
  · rfl
  have hrow := hMargins.1 (Fin.last m)
  have hcolumn := hMargins.2 (Fin.last m)
  simp at hrow hcolumn
  have hrowdiag : rowSum C (Fin.last m) = C (Fin.last m) (Fin.last m) := by
    rw [← hcol]
    omega
  have hall : ∀ r c, r ≠ c → C r c = 0 := by
    intro r c hrc
    by_cases hc : c = Fin.last m
    · subst c
      exact incoming_zero_entry C hincoming hrc
    · exact hInvariant c hc
        (row_offdiag_zero_of_rowSum_eq_diag C (Fin.last m) c hrowdiag hc) r hrc
  unfold offdiagMass
  apply Finset.sum_eq_zero
  intro r hr
  apply Finset.sum_eq_zero
  intro c hc
  split
  · rfl
  · exact hall r c (by assumption)

inductive Run : CountMatrix m → Fin (m + 1) → CountMatrix m → Fin (m + 1) → ℕ → Prop where
  | nil (C : CountMatrix m) (i : Fin (m + 1)) : Run C i C i 0
  | cons {C D : CountMatrix m} {i j k : Fin (m + 1)} {t : ℕ} :
      Chooses C i j → Run (move C i j) j D k t → Run C i D k (t + 1)

theorem Run.margins {C D : CountMatrix m} {i j : Fin (m + 1)} {t capacity : ℕ}
    (h : Run C i D j t) (hMargins : Margins C i capacity) : Margins D j capacity := by
  induction h generalizing capacity with
  | nil => exact hMargins
  | cons hchoice hrun ih => exact ih (margins_move _ hMargins hchoice)

theorem Run.lastInvariant {C D : CountMatrix m} {i j : Fin (m + 1)} {t : ℕ}
    (h : Run C i D j t) (hInvariant : LastInvariant C) : LastInvariant D := by
  induction h with
  | nil => exact hInvariant
  | cons hchoice hrun ih => exact ih (lastInvariant_move _ hInvariant hchoice)

theorem exists_choice_of_incoming_pos (C : CountMatrix m) (i : Fin (m + 1))
    (hpos : 0 < incoming C i) : ∃ j, Chooses C i j := by
  have hex : ∃ r, r ≠ i ∧ 0 < C r i := by
    by_contra h
    have hall : ∀ r, r ≠ i → C r i = 0 := by
      intro r hri
      by_contra hne
      exact h ⟨r, hri, Nat.pos_of_ne_zero hne⟩
    have hzero : incoming C i = 0 := by
      unfold incoming
      apply Finset.sum_eq_zero
      intro r hr
      by_cases hri : r = i
      · simp [hri]
      · simp [hri, hall r hri]
    omega
  let s : Finset (Fin (m + 1)) := Finset.univ.filter (fun r => r ≠ i ∧ 0 < C r i)
  have hs : s.Nonempty := by
    rcases hex with ⟨r, hr, hp⟩
    exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr, hp⟩⟩
  refine ⟨s.min' hs, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (Finset.min'_mem s hs)).2.1
  · exact (Finset.mem_filter.mp (Finset.min'_mem s hs)).2.2
  · intro r hri hp
    apply Finset.min'_le s r
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hri, hp⟩

theorem exists_terminal_run_aux : ∀ n : ℕ, ∀ (C : CountMatrix m) (i : Fin (m + 1)) (capacity : ℕ),
    offdiagMass C = n → Margins C i capacity → LastInvariant C →
      ∃ D j t, Run C i D j t ∧ t ≤ n ∧ incoming D j = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro C i capacity hmass hMargins hInvariant
    by_cases hin : incoming C i = 0
    · exact ⟨C, i, 0, Run.nil C i, Nat.zero_le _, hin⟩
    · have hinpos : 0 < incoming C i := Nat.pos_of_ne_zero hin
      obtain ⟨j, hchoice⟩ := exists_choice_of_incoming_pos C i hinpos
      have hmasspos : 0 < offdiagMass C := by
        rw [offdiagMass_eq_sum_incoming]
        exact lt_of_lt_of_le hinpos
          (Finset.single_le_sum (s := Finset.univ) (f := incoming C)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
      have hnext : offdiagMass (move C i j) = n - 1 := by
        rw [offdiagMass_move C hchoice.1 hchoice.2.1, hmass]
      obtain ⟨D, k, t, hrun, ht, hterminal⟩ :=
        ih (n - 1) (by omega) (move C i j) j capacity hnext
          (margins_move C hMargins hchoice) (lastInvariant_move C hInvariant hchoice)
      exact ⟨D, k, t + 1, Run.cons hchoice hrun, by omega, hterminal⟩

/-- Finite count-only execution of Algorithm 4's transport loop. -/
theorem exists_sorted_run (C : CountMatrix m) (i : Fin (m + 1)) (capacity : ℕ)
    (hMargins : Margins C i capacity) (hInvariant : LastInvariant C) :
    ∃ D j t, Run C i D j t ∧ t ≤ offdiagMass C ∧ j = Fin.last m ∧ offdiagMass D = 0 := by
  obtain ⟨D, j, t, hrun, ht, hterminal⟩ :=
    exists_terminal_run_aux (offdiagMass C) C i capacity rfl hMargins hInvariant
  have hMarginsD := hrun.margins hMargins
  have hInvariantD := hrun.lastInvariant hInvariant
  obtain ⟨hj, hmass⟩ := terminal_of_margins D j capacity hMarginsD hInvariantD hterminal
  exact ⟨D, j, t, hrun, ht, hj, hmass⟩

end SlidingPuzzle.TransportCounts
