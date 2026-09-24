import SlidingPuzzle.Paths
import Zhong.Orbit

/-! A translation between Zhong operation words and legal sliding-puzzle paths. -/

namespace SlidingPuzzle

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
private theorem zhong_neighbor_gridDistance_one {c c' : Cell n} {δ : Zhong.Dir}
    (h : Zhong.neighbor? c δ = some c') : gridDistance c c' = 1 := by
  rcases c with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
  rcases c' with ⟨⟨r', hr'⟩, ⟨s', hs'⟩⟩
  cases δ <;> simp only [Zhong.neighbor?] at h <;> split_ifs at h <;>
    simp_all only [Option.some.injEq, Fin.mk.injEq, Prod.mk.injEq] <;>
    simp [gridDistance, Nat.dist] <;> omega

omit [NeZero n] in
private theorem exists_zhong_neighbor_of_gridDistance_one {c c' : Cell n}
    (h : gridDistance c c' = 1) : ∃ δ : Zhong.Dir, Zhong.neighbor? c δ = some c' := by
  rcases c with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
  rcases c' with ⟨⟨r', hr'⟩, ⟨s', hs'⟩⟩
  simp only [gridDistance, Nat.dist] at h
  by_cases hrr : r < r'
  · refine ⟨Zhong.Dir.U, ?_⟩
    have hrow : r' = r + 1 := by omega
    have hcol : s' = s := by omega
    subst r'
    subst s'
    have hlt : r + 1 < n := by omega
    simp [Zhong.neighbor?, hlt]
  by_cases hrr' : r' < r
  · refine ⟨Zhong.Dir.D, ?_⟩
    have hrow : r = r' + 1 := by omega
    have hcol : s' = s := by omega
    subst r
    subst s'
    have hlt : 0 < r' + 1 := by omega
    simp [Zhong.neighbor?, hlt]
  have hrow : r' = r := by omega
  subst r'
  by_cases hss : s < s'
  · refine ⟨Zhong.Dir.L, ?_⟩
    have hcol : s' = s + 1 := by omega
    subst s'
    have hlt : s + 1 < n := by omega
    simp [Zhong.neighbor?, hlt]
  · refine ⟨Zhong.Dir.R, ?_⟩
    have hcol : s = s' + 1 := by omega
    subst s
    have hlt : 0 < s' + 1 := by omega
    simp [Zhong.neighbor?, hlt]

private theorem step_of_zhong_act {B : Board n} (δ : Zhong.Dir)
    (h : Zhong.Applicable B δ) : Step B (Zhong.act B δ) := by
  unfold Zhong.Applicable at h
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
  refine ⟨c, zhong_neighbor_gridDistance_one hc, ?_⟩
  exact Zhong.act_of_neighbor? hc

/-- A Zhong operation word determines a legal path after inapplicable moves are omitted. -/
theorem path_of_zhong_word (B : Board n) (word : List Zhong.Dir) :
    ∃ p : Path B (Zhong.actSeq B word), p.length ≤ word.length := by
  induction word generalizing B with
  | nil => exact ⟨.nil B, le_rfl⟩
  | cons δ word ih =>
      cases hδ : Zhong.neighbor? (Zhong.blank B) δ with
      | none =>
          have hact : Zhong.act B δ = B := Zhong.act_of_neighbor?_eq_none hδ
          obtain ⟨p, hp⟩ := ih B
          rw [Zhong.actSeq_cons, hact]
          exact ⟨p, Nat.le_succ_of_le hp⟩
      | some c =>
          have happ : Zhong.Applicable B δ := by
            unfold Zhong.Applicable
            simp [hδ]
          obtain ⟨p, hp⟩ := ih (Zhong.act B δ)
          refine ⟨.cons (step_of_zhong_act δ happ) p, ?_⟩
          simpa [Zhong.actSeq_cons, Path.length_cons, Nat.succ_eq_add_one,
            Nat.add_comm] using Nat.succ_le_succ hp

/-- A legal step is one applicable Zhong operation. -/
theorem zhong_act_of_step {B C : Board n} (h : Step B C) :
    ∃ δ : Zhong.Dir, Zhong.act B δ = C := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨δ, hδ⟩ := exists_zhong_neighbor_of_gridDistance_one hc
  exact ⟨δ, Zhong.act_of_neighbor? hδ⟩

/-- A legal path gives an exactly equally long Zhong operation word. -/
theorem zhong_word_of_path {B C : Board n} (p : Path B C) :
    ∃ word : List Zhong.Dir, Zhong.actSeq B word = C ∧ word.length = p.length := by
  induction p with
  | nil B => exact ⟨[], rfl, rfl⟩
  | cons step tail ih =>
      obtain ⟨δ, hδ⟩ := zhong_act_of_step step
      obtain ⟨word, hword, hlength⟩ := ih
      refine ⟨δ :: word, ?_, ?_⟩
      · rw [Zhong.actSeq_cons, hδ, hword]
      · simpa [Path.length_cons] using congrArg Nat.succ hlength

/-- Every legal path is a Zhong operation word. -/
theorem zhong_reachable_of_path {B C : Board n} (p : Path B C) : Zhong.Reachable B C := by
  obtain ⟨word, hword, _⟩ := zhong_word_of_path p
  exact ⟨word, hword⟩

/-- Zhong reachability and existence of a legal path are equivalent. -/
theorem zhong_reachable_iff_path {B C : Board n} :
    Zhong.Reachable B C ↔ Nonempty (Path B C) := by
  constructor
  · rintro ⟨word, rfl⟩
    obtain ⟨p, _⟩ := path_of_zhong_word B word
    exact ⟨p⟩
  · rintro ⟨p⟩
    exact zhong_reachable_of_path p

/-- Reachability from the frozen target agrees with Zhong reachability. -/
theorem reachable_iff_zhong {B : Board n} :
    Reachable B ↔ Zhong.Reachable (Zhong.target n n) B := by
  change Nonempty (Path (Zhong.target n n) B) ↔ Zhong.Reachable (Zhong.target n n) B
  exact zhong_reachable_iff_path.symm

end SlidingPuzzle
