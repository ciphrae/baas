import SlidingPuzzle.Moves.Conjugation
import SlidingPuzzle.Moves.BlankAccess

/-! Row translations that restore the access route and protect all other rows. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

/-- The one-row shift returns the blank and changes only its two data rows. -/
theorem exists_row_shift (B : Board n) (ro co M : ℕ)
    (hr : ro+3 ≤ n) (hc : co+M ≤ n) (hM : 1 < M)
    (hb : blank B = (⟨ro+2,by omega⟩,⟨co,by omega⟩)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 6*M+2 ∧ blank C = blank B ∧
      (∀ j : Fin M, C (⟨ro+1,by omega⟩,⟨co+j.val,by omega⟩) =
        B (⟨ro,by omega⟩,⟨co+j.val,by omega⟩)) ∧
      (∀ x : Cell n, x.1.val < ro ∨ ro+2 ≤ x.1.val ∨
        x.2.val < co ∨ co+M ≤ x.2.val → C x = B x) := by
  let : NeZero (n*n) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne n)⟩
  let ι := Zhong.blockStrip (n := n) 3 M ro co hr hc
  let a : Zhong.Cell 3 M := (2,⟨0,by omega⟩)
  have hstart : ι a = blank B := by rw [hb]; rfl
  have happ := Zhong.applicableFrom_shiftWord hM
  have hmap (y : Zhong.Cell 3 M) :
      Zhong.permOf (blank B) (Zhong.shiftWord M) (ι y) =
        ι (Zhong.permOf a (Zhong.shiftWord M) y) := by
    have h := Zhong.permOf_map_apply_of_neighbor_map
      (ι := ι) (f := id) (Zhong.blockStrip_injective hr hc)
      (Zhong.blockStrip_neighbor hr hc) a (Zhong.shiftWord M) happ (x := y)
    simpa only [List.map_id, hstart] using h
  have hrow2 (j : Fin M) :
      Zhong.permOf (blank B) (Zhong.shiftWord M) (ι (2,j)) = ι (2,j) := by
    rw [hmap]
    exact congrArg ι (Zhong.permOf_shiftWord_row2 hM j)
  obtain ⟨p,hp⟩ := path_of_zhong_word B (Zhong.shiftWord M)
  refine ⟨Zhong.actSeq B (Zhong.shiftWord M),p,?_,?_,?_,?_⟩
  · simpa [Zhong.shiftWord_length hM] using hp
  · have hh : Zhong.actSeq B (Zhong.shiftWord M) (blank B) = 0 := by
      rw [Zhong.actSeq_eq_permOf]
      change B (Zhong.permOf (blank B) (Zhong.shiftWord M) (blank B)) = 0
      have hhfix := hrow2 ⟨0,by omega⟩
      change Zhong.permOf (blank B) (Zhong.shiftWord M) (ι a) = ι a at hhfix
      rw [hstart] at hhfix
      rw [hhfix]
      simp [blank, position]
    apply (Zhong.actSeq B (Zhong.shiftWord M)).injective
    simpa [blank, position] using hh.symm
  · intro j
    rw [Zhong.actSeq_eq_permOf]
    change B (Zhong.permOf (blank B) (Zhong.shiftWord M) (ι (1,j))) = B (ι (0,j))
    rw [hmap, Zhong.permOf_shiftWord_row1 hM]
  · intro x hx
    rw [Zhong.actSeq_eq_permOf]
    change B (Zhong.permOf (blank B) (Zhong.shiftWord M) x) = B x
    congr 1
    by_cases hxin : x ∈ Set.range ι
    · obtain ⟨y,rfl⟩ := hxin
      have hy1 := y.1.isLt
      have hy2 := y.2.isLt
      change ro+y.1.val < ro ∨ ro+2 ≤ ro+y.1.val ∨
        co+y.2.val < co ∨ co+M ≤ co+y.2.val at hx
      have hy : y.1 = 2 := Fin.ext (by change y.1.val = 2; omega)
      have hey : y = (2,y.2) := Prod.ext hy rfl
      rw [hey]
      exact hrow2 y.2
    · have h := Zhong.permOf_map_fixes_of_not_mem_range
        (ι := ι) (f := id) (Zhong.blockStrip_neighbor hr hc)
        a (Zhong.shiftWord M) happ hxin
      simpa only [List.map_id, hstart] using h

/-- With the blank below the two data rows, shift one row and restore the access
route. Only the source and destination row segments can change. -/
theorem exists_protected_row_shift_with_cost (B : Board n) (ro co M : ℕ)
    (hr : ro+3 ≤ n) (hc : co+M ≤ n) (hM : 1 < M)
    (hb : ro+2 ≤ (blank B).1.val) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 2*gridDistance (blank B) (⟨ro+2,by omega⟩,⟨co,by omega⟩)+6*M+2 ∧ blank C = blank B ∧
      (∀ j : Fin M, C (⟨ro+1,by omega⟩,⟨co+j.val,by omega⟩) =
        B (⟨ro,by omega⟩,⟨co+j.val,by omega⟩)) ∧
      (∀ x : Cell n, x.1.val < ro ∨ ro+2 ≤ x.1.val ∨
        x.2.val < co ∨ co+M ≤ x.2.val → C x = B x) := by
  let a : Cell n := (⟨ro+2,by omega⟩,⟨co,by omega⟩)
  obtain ⟨D,p,hblank,hp,hfix⟩ := exists_blank_access_path_preserving B a
  obtain ⟨E,q,hq,hqb,hrow,hqfix⟩ := exists_row_shift D ro co M hr hc hM hblank
  let S : Set (Cell n) := {x | ro ≤ x.1.val ∧ x.1.val < ro+2 ∧
    co ≤ x.2.val ∧ x.2.val < co+M}
  have haccess (x : Cell n) (hx : x ∈ S) : D x = B x := by
    apply hfix
    left
    change x.1.val < min (blank B).1.val (ro+2)
    have := hx.2.1
    exact lt_min (by omega) this
  have hlocal (x : Cell n) (hx : x ∉ S) : E x = D x := by
    apply hqfix
    change ¬ (ro ≤ x.1.val ∧ x.1.val < ro+2 ∧ co ≤ x.2.val ∧ x.2.val < co+M) at hx
    omega
  obtain ⟨F,r,hlen,hbF,hF,hFfix⟩ := p.exists_conjugated q hqb S haccess hlocal
  refine ⟨F,r,?_,hbF,?_,?_⟩
  · rw [hlen]
    dsimp [a] at hp
    omega
  · intro j
    rw [hF _ (by change ro ≤ ro+1 ∧ ro+1 < ro+2 ∧ co ≤ co+j.val ∧ co+j.val < co+M; omega),
      hrow, haccess _ (by change ro ≤ ro ∧ ro < ro+2 ∧ co ≤ co+j.val ∧ co+j.val < co+M; omega)]
  · intro x hx
    apply hFfix
    change ¬ (ro ≤ x.1.val ∧ x.1.val < ro+2 ∧ co ≤ x.2.val ∧ x.2.val < co+M)
    omega

/-- The ambient-size bound for protected row shifts. -/
theorem exists_protected_row_shift (B : Board n) (ro co M : ℕ)
    (hr : ro+3 ≤ n) (hc : co+M ≤ n) (hM : 1 < M)
    (hb : ro+2 ≤ (blank B).1.val) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 12*n ∧ blank C = blank B ∧
      (∀ j : Fin M, C (⟨ro+1,by omega⟩,⟨co+j.val,by omega⟩) =
        B (⟨ro,by omega⟩,⟨co+j.val,by omega⟩)) ∧
      (∀ x : Cell n, x.1.val < ro ∨ ro+2 ≤ x.1.val ∨
        x.2.val < co ∨ co+M ≤ x.2.val → C x = B x) := by
  obtain ⟨C,p,hp,hbC,hrow,hfix⟩ := exists_protected_row_shift_with_cost B ro co M hr hc hM hb
  refine ⟨C,p,?_,hbC,hrow,hfix⟩
  have hdist : gridDistance (blank B) (⟨ro+2,by omega⟩,⟨co,by omega⟩) ≤ 2*n := by
    unfold gridDistance Nat.dist
    have := (blank B).1.isLt
    have := (blank B).2.isLt
    omega
  omega

/-- Translate a row downward while restoring every cell outside the source-to-
destination band, including the blank. This bound includes all access moves. -/
theorem exists_protected_row_translation (B : Board n) (ro co M t : ℕ)
    (hr : ro+t+3 ≤ n) (hc : co+M ≤ n) (hM : 1 < M)
    (hb : ro+t+2 ≤ (blank B).1.val) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 12*n*t ∧ blank C = blank B ∧
      (∀ j : Fin M, C (⟨ro+t,by omega⟩,⟨co+j.val,by omega⟩) =
        B (⟨ro,by omega⟩,⟨co+j.val,by omega⟩)) ∧
      (∀ x : Cell n, x.1.val < ro ∨ ro+t < x.1.val ∨
        x.2.val < co ∨ co+M ≤ x.2.val → C x = B x) := by
  induction t with
  | zero => exact ⟨B,Path.nil B,by simp,rfl,fun _ => rfl,fun _ _ => rfl⟩
  | succ t ih =>
    obtain ⟨D,p,hp,hbD,hrowD,hfixD⟩ := ih (by omega) (by omega)
    obtain ⟨E,q,hq,hbE,hrowE,hfixE⟩ := exists_protected_row_shift D (ro+t) co M
      (by omega) hc hM (by rw [hbD]; omega)
    refine ⟨E,p.append q,?_,hbE.trans hbD,?_,?_⟩
    · rw [Path.length_append]
      calc
        p.length+q.length ≤ 12*n*t+12*n := Nat.add_le_add hp hq
        _ = 12*n*(t+1) := by ring
    · intro j
      have hh := hrowE j
      rw [hrowD] at hh
      simpa [Nat.add_assoc] using hh
    · intro x hx
      rw [hfixE x (by omega), hfixD x (by omega)]

end SlidingPuzzle
