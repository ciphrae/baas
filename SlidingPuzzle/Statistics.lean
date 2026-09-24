import SlidingPuzzle.Paths

/-! Uniform statistics on the finite reachable orbit. The sequences used in
asymptotic statements are set to zero below the valid board sizes `2 ≤ n`. -/
namespace SlidingPuzzle

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α]

/-- The uniform real-valued mean on a nonempty finite type. -/
def finiteMean (f : α → ℝ) : ℝ := (∑ a, f a) / Fintype.card α

/-- The maximum of a real-valued function on a nonempty finite type. -/
def finiteMaximum (f : α → ℝ) : ℝ := by
  classical
  exact (Finset.univ.image f).max' (Finset.univ_nonempty.image f)

theorem finiteMean_mono {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    finiteMean f ≤ finiteMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (by positivity)

@[simp] theorem finiteMean_const (c : ℝ) : finiteMean (fun _ : α => c) = c := by
  simp [finiteMean, Fintype.card_ne_zero]

omit [Nonempty α] in
@[simp] theorem finiteMean_add (f g : α → ℝ) :
    finiteMean (fun a => f a + g a) = finiteMean f + finiteMean g := by
  simp [finiteMean, Finset.sum_add_distrib, add_div]

theorem le_finiteMaximum (f : α → ℝ) (a : α) : f a ≤ finiteMaximum f := by
  classical
  exact Finset.le_max' _ _ (Finset.mem_image_of_mem f (Finset.mem_univ a))

theorem finiteMaximum_le {f : α → ℝ} {c : ℝ} (h : ∀ a, f a ≤ c) :
    finiteMaximum f ≤ c := by
  classical
  apply Finset.max'_le
  intro y hy
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hy
  exact h a

theorem finiteMaximum_attained (f : α → ℝ) : ∃ a, f a = finiteMaximum f := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp
    (Finset.max'_mem (Finset.univ.image f) (Finset.univ_nonempty.image f))
  exact ⟨a, ha⟩

theorem finiteMaximum_mono {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    finiteMaximum f ≤ finiteMaximum g :=
  finiteMaximum_le fun a => (h a).trans (le_finiteMaximum g a)

@[simp] theorem finiteMaximum_add_const (f : α → ℝ) (c : ℝ) :
    finiteMaximum (fun a => f a + c) = finiteMaximum f + c := by
  apply le_antisymm
  · exact finiteMaximum_le fun a => add_le_add (le_finiteMaximum f a) le_rfl
  · obtain ⟨a, ha⟩ := finiteMaximum_attained f
    rw [← ha]
    exact le_finiteMaximum (fun a => f a + c) a

/-- Pointwise additive error transfers unchanged to uniform means. -/
theorem finiteMean_sandwich {D L : α → ℝ} {E : ℝ}
    (hlo : ∀ a, D a ≤ L a) (hhi : ∀ a, L a ≤ D a + E) :
    finiteMean D ≤ finiteMean L ∧ finiteMean L ≤ finiteMean D + E := by
  exact ⟨finiteMean_mono hlo, by simpa using finiteMean_mono hhi⟩

/-- Pointwise additive error transfers unchanged to maxima. -/
theorem finiteMaximum_sandwich {D L : α → ℝ} {E : ℝ}
    (hlo : ∀ a, D a ≤ L a) (hhi : ∀ a, L a ≤ D a + E) :
    finiteMaximum D ≤ finiteMaximum L ∧ finiteMaximum L ≤ finiteMaximum D + E := by
  exact ⟨finiteMaximum_mono hlo, by simpa using finiteMaximum_mono hhi⟩

variable (n : ℕ) [NeZero n]

def orbitAverageOptimalLength : ℝ :=
  finiteMean (fun B : ReachableBoard n => (optimalLength B : ℝ))

def orbitAverageManhattan : ℝ :=
  finiteMean (fun B : ReachableBoard n => (manhattan B.val : ℝ))

def orbitMaximumManhattan : ℝ :=
  finiteMaximum (fun B : ReachableBoard n => (manhattan B.val : ℝ))

def orbitGodsNumber : ℝ :=
  finiteMaximum (fun B : ReachableBoard n => (optimalLength B : ℝ))

theorem orbitGodsNumber_attained :
    ∃ B : ReachableBoard n, (optimalLength B : ℝ) = orbitGodsNumber n :=
  finiteMaximum_attained _

theorem orbitMaximumManhattan_attained :
    ∃ B : ReachableBoard n, (manhattan B.val : ℝ) = orbitMaximumManhattan n :=
  finiteMaximum_attained _

theorem orbit_statistics_sandwich {E : ℝ}
    (hlo : ∀ B : ReachableBoard n, (manhattan B.val : ℝ) ≤ optimalLength B)
    (hhi : ∀ B : ReachableBoard n, (optimalLength B : ℝ) ≤ manhattan B.val + E) :
    (orbitAverageManhattan n ≤ orbitAverageOptimalLength n ∧
      orbitAverageOptimalLength n ≤ orbitAverageManhattan n + E) ∧
    (orbitMaximumManhattan n ≤ orbitGodsNumber n ∧
      orbitGodsNumber n ≤ orbitMaximumManhattan n + E) :=
  ⟨finiteMean_sandwich hlo hhi, finiteMaximum_sandwich hlo hhi⟩

end

noncomputable def averageOptimalLength (n : ℕ) : ℝ :=
  if h : 2 ≤ n then
    letI : NeZero n := ⟨by omega⟩
    orbitAverageOptimalLength n
  else 0

noncomputable def averageManhattan (n : ℕ) : ℝ :=
  if h : 2 ≤ n then
    letI : NeZero n := ⟨by omega⟩
    orbitAverageManhattan n
  else 0

noncomputable def maximumManhattan (n : ℕ) : ℝ :=
  if h : 2 ≤ n then
    letI : NeZero n := ⟨by omega⟩
    orbitMaximumManhattan n
  else 0

noncomputable def godsNumber (n : ℕ) : ℝ :=
  if h : 2 ≤ n then
    letI : NeZero n := ⟨by omega⟩
    orbitGodsNumber n
  else 0

theorem averageOptimalLength_of_two_le (n : ℕ) [NeZero n] (h : 2 ≤ n) :
    averageOptimalLength n = orbitAverageOptimalLength n := by
  simp [averageOptimalLength, h]

theorem averageManhattan_of_two_le (n : ℕ) [NeZero n] (h : 2 ≤ n) :
    averageManhattan n = orbitAverageManhattan n := by
  simp [averageManhattan, h]

theorem maximumManhattan_of_two_le (n : ℕ) [NeZero n] (h : 2 ≤ n) :
    maximumManhattan n = orbitMaximumManhattan n := by
  simp [maximumManhattan, h]

theorem godsNumber_of_two_le (n : ℕ) [NeZero n] (h : 2 ≤ n) :
    godsNumber n = orbitGodsNumber n := by
  simp [godsNumber, h]

@[simp] theorem averageOptimalLength_of_lt_two {n : ℕ} (h : n < 2) :
    averageOptimalLength n = 0 := by
  simp [averageOptimalLength, Nat.not_le.mpr h]

@[simp] theorem averageManhattan_of_lt_two {n : ℕ} (h : n < 2) :
    averageManhattan n = 0 := by
  simp [averageManhattan, Nat.not_le.mpr h]

@[simp] theorem maximumManhattan_of_lt_two {n : ℕ} (h : n < 2) :
    maximumManhattan n = 0 := by
  simp [maximumManhattan, Nat.not_le.mpr h]

@[simp] theorem godsNumber_of_lt_two {n : ℕ} (h : n < 2) :
    godsNumber n = 0 := by
  simp [godsNumber, Nat.not_le.mpr h]

/-- Transfer a boardwise Manhattan error bound to the two statistical sequences. -/
theorem statistics_sandwich (n : ℕ) [NeZero n] (hn : 2 ≤ n) {E : ℝ}
    (hlo : ∀ B : ReachableBoard n, (manhattan B.val : ℝ) ≤ optimalLength B)
    (hhi : ∀ B : ReachableBoard n, (optimalLength B : ℝ) ≤ manhattan B.val + E) :
    (averageManhattan n ≤ averageOptimalLength n ∧
      averageOptimalLength n ≤ averageManhattan n + E) ∧
    (maximumManhattan n ≤ godsNumber n ∧
      godsNumber n ≤ maximumManhattan n + E) := by
  simpa only [averageManhattan_of_two_le n hn, averageOptimalLength_of_two_le n hn,
    maximumManhattan_of_two_le n hn, godsNumber_of_two_le n hn]
    using orbit_statistics_sandwich n hlo hhi

end SlidingPuzzle
