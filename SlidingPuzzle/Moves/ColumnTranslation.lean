import SlidingPuzzle.Moves.ProtectedTranslation
import SlidingPuzzle.Moves.Transpose

/-! Protected column translations, with nearby access and bounded-length chunks. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

/-- A transposed protected shift, retaining its actual blank-access cost. -/
theorem exists_protected_column_shift (B : Board n) (ro co H : ℕ)
    (hr : ro+H ≤ n) (hc : co+3 ≤ n) (hH : 1 < H)
    (hb : co+2 ≤ (blank B).2.val) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 2*gridDistance (blank B) (⟨ro,by omega⟩,⟨co+2,by omega⟩)+6*H+2 ∧
      blank C = blank B ∧
      (∀ j : Fin H, C (⟨ro+j.val,by omega⟩,⟨co+1,by omega⟩) =
        B (⟨ro+j.val,by omega⟩,⟨co,by omega⟩)) ∧
      (∀ x : Cell n, x.1.val < ro ∨ ro+H ≤ x.1.val ∨
        x.2.val < co ∨ co+2 ≤ x.2.val → C x = B x) := by
  obtain ⟨D,p,hp,hbD,hrow,hfix⟩ := exists_protected_row_shift_with_cost
    (transposeBoard B) co ro H hc hr hH hb
  have htrans : ∃ q : Path B (transposeBoard D), q.length = p.length := by
    have h := p.exists_transpose
    rw [transposeBoard_transposeBoard] at h
    exact h
  obtain ⟨q,hq⟩ := htrans
  refine ⟨transposeBoard D,q,?_,?_,?_,?_⟩
  · rw [hq]
    simpa [gridDistance, Nat.add_comm] using hp
  · rw [blank_transposeBoard, hbD, blank_transposeBoard, Prod.swap_swap]
  · intro j
    exact hrow j
  · intro x hx
    exact hfix x.swap (by rcases hx with h | h | h | h <;> simp_all)

/-- Translate with the blank parked immediately above the data and near the
right edge. Each unit shift pays for nearby access rather than the board side. -/
theorem exists_nearby_column_translation (B : Board n) (ro co H t A : ℕ)
    (hr0 : 0 < ro) (hr : ro+H ≤ n) (hc : A+1 ≤ n) (hH : 1 < H)
    (ht : co+t+2 ≤ A) (hbr : (blank B).1.val = ro-1) (hbc : (blank B).2.val = A) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ t*(2*(A-co)+6*H+4) ∧ blank C = blank B ∧
      (∀ j : Fin H, C (⟨ro+j.val,by omega⟩,⟨co+t,by omega⟩) =
        B (⟨ro+j.val,by omega⟩,⟨co,by omega⟩)) ∧
      (∀ x : Cell n, x.1.val < ro ∨ ro+H ≤ x.1.val ∨
        x.2.val < co ∨ co+t < x.2.val → C x = B x) := by
  induction t with
  | zero => exact ⟨B,Path.nil B,by simp,rfl,fun _ => rfl,fun _ _ => rfl⟩
  | succ t ih =>
    obtain ⟨D,p,hp,hbD,hcolD,hfixD⟩ := ih (by omega)
    obtain ⟨E,q,hq,hbE,hcolE,hfixE⟩ := exists_protected_column_shift D ro (co+t) H
      hr (by omega) hH (by rw [hbD,hbc]; omega)
    have hdist : gridDistance (blank D) (⟨ro,by omega⟩,⟨co+t+2,by omega⟩) ≤ A-co+1 := by
      rw [hbD]
      unfold gridDistance Nat.dist
      rw [hbr,hbc]
      simp only
      omega
    have hq' : q.length ≤ 2*(A-co)+6*H+4 := by omega
    refine ⟨E,p.append q,?_,hbE.trans hbD,?_,?_⟩
    · rw [Path.length_append]
      calc
        p.length+q.length ≤ t*(2*(A-co)+6*H+4)+(2*(A-co)+6*H+4) := Nat.add_le_add hp hq'
        _ = (t+1)*(2*(A-co)+6*H+4) := by ring
    · intro j
      have hh := hcolE j
      rw [hcolD] at hh
      simpa [Nat.add_assoc] using hh
    · intro x hx
      rw [hfixE x (by omega),hfixD x (by omega)]

/-- A short column translation, including access from and return to the original
blank. Every cell outside the data rectangle is restored. -/
theorem exists_column_translation_chunk (B : Board n) (ro co H t : ℕ)
    (hr0 : 0 < ro) (hr : ro+H ≤ n) (hc : co+t+3 ≤ n) (hH : 1 < H)
    (hb : co+t < (blank B).2.val) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 4*n+t*(2*t+6*H+8) ∧ blank C = blank B ∧
      (∀ j : Fin H, C (⟨ro+j.val,by omega⟩,⟨co+t,by omega⟩) =
        B (⟨ro+j.val,by omega⟩,⟨co,by omega⟩)) ∧
      (∀ x : Cell n, x.1.val < ro ∨ ro+H ≤ x.1.val ∨
        x.2.val < co ∨ co+t < x.2.val → C x = B x) := by
  let a : Cell n := (⟨ro-1,by omega⟩,⟨co+t+2,by omega⟩)
  obtain ⟨D,p,hblank,hp,hfix⟩ := exists_blank_access_path_elbow B a
  obtain ⟨E,q,hq,hbE,hcol,hqfix⟩ := exists_nearby_column_translation D ro co H t (co+t+2)
    hr0 hr (by omega) hH le_rfl (by rw [hblank]) (by rw [hblank])
  let S : Set (Cell n) := {x | ro ≤ x.1.val ∧ x.1.val < ro+H ∧
    co ≤ x.2.val ∧ x.2.val ≤ co+t}
  have haccess (x : Cell n) (hx : x ∈ S) : D x = B x := by
    apply hfix
    · intro he
      have := congrArg Fin.val he
      have := hx.2.2.2
      omega
    · intro he
      have := congrArg Fin.val he
      change x.1.val = ro-1 at this
      have := hx.1
      omega
  have hlocal (x : Cell n) (hx : x ∉ S) : E x = D x := by
    apply hqfix
    change ¬ (ro ≤ x.1.val ∧ x.1.val < ro+H ∧ co ≤ x.2.val ∧ x.2.val ≤ co+t) at hx
    omega
  obtain ⟨F,r,hlen,hbF,hF,hFfix⟩ := p.exists_conjugated q hbE S haccess hlocal
  refine ⟨F,r,?_,hbF,?_,?_⟩
  · have hcost : 2*(co+t+2-co)+6*H+4 = 2*t+6*H+8 := by omega
    rw [hcost] at hq
    rw [hlen]
    omega
  · intro j
    rw [hF _ (by change ro ≤ ro+j.val ∧ ro+j.val < ro+H ∧ co ≤ co+t ∧ co+t ≤ co+t; omega),
      hcol,haccess _ (by change ro ≤ ro+j.val ∧ ro+j.val < ro+H ∧ co ≤ co ∧ co ≤ co+t; omega)]
  · intro x hx
    apply hFfix
    change ¬ (ro ≤ x.1.val ∧ x.1.val < ro+H ∧ co ≤ x.2.val ∧ x.2.val ≤ co+t)
    omega

/-- Split a long translation into at most `q` chunks of width at most `m`.
The cost separates board-wide access from the local translation length. -/
theorem exists_chunked_column_translation (B : Board n) (ro co H t m q : ℕ)
    (hr0 : 0 < ro) (hr : ro+H ≤ n) (hc : co+t+3 ≤ n) (hH : 1 < H)
    (hb : co+t < (blank B).2.val) (ht : t ≤ q*m) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ q*(4*n+m*(2*m+6*H+8)) ∧ blank C = blank B ∧
      (∀ j : Fin H, C (⟨ro+j.val,by omega⟩,⟨co+t,by omega⟩) =
        B (⟨ro+j.val,by omega⟩,⟨co,by omega⟩)) ∧
      (∀ x : Cell n, x.1.val < ro ∨ ro+H ≤ x.1.val ∨
        x.2.val < co ∨ co+t < x.2.val → C x = B x) := by
  induction q generalizing B co t with
  | zero =>
    have ht0 : t = 0 := by simpa using ht
    subst t
    exact ⟨B,Path.nil B,by simp,rfl,fun _ => rfl,fun _ _ => rfl⟩
  | succ q ih =>
    let u := min t m
    have hu : u ≤ t ∧ u ≤ m := ⟨min_le_left _ _,min_le_right _ _⟩
    obtain ⟨D,p,hp,hbD,hcolD,hfixD⟩ := exists_column_translation_chunk B ro co H u
      hr0 hr (by omega) hH (by omega)
    obtain ⟨E,s,hs,hbE,hcolE,hfixE⟩ := ih D (co+u) (t-u)
      (by omega) (by rw [hbD]; omega) (by dsimp [u]; rw [Nat.succ_mul] at ht; omega)
    have hp' : p.length ≤ 4*n+m*(2*m+6*H+8) := by
      apply hp.trans
      gcongr <;> exact hu.2
    refine ⟨E,p.append s,?_,hbE.trans hbD,?_,?_⟩
    · rw [Path.length_append]
      calc
        p.length+s.length ≤ (4*n+m*(2*m+6*H+8))+q*(4*n+m*(2*m+6*H+8)) := Nat.add_le_add hp' hs
        _ = (q+1)*(4*n+m*(2*m+6*H+8)) := by ring
    · intro j
      have hh := hcolE j
      rw [hcolD] at hh
      simpa only [show co+u+(t-u) = co+t by omega] using hh
    · intro x hx
      rw [hfixE x (by omega),hfixD x (by omega)]

end SlidingPuzzle
