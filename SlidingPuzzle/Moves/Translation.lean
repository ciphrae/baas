import SlidingPuzzle.Moves.Strips

/-! Legal subarray translations with explicit length and preservation guarantees. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

/-- Translate a row segment downward inside its three-row working margin. -/
theorem exists_row_translation_with_blank (B : Board n) (ro co M t : ℕ)
    (hr : ro+t+3 ≤ n) (hc : co+M ≤ n) (hM : 1<M)
    (hb : blank B = (⟨ro+2,by omega⟩,⟨co,by omega⟩)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ t*(6*M+3) ∧
      (∀ c : Fin M, C (⟨ro+t,by omega⟩,⟨co+c.val,by omega⟩) =
        B (⟨ro,by omega⟩,⟨co+c.val,by omega⟩)) ∧
      (∀ x : Cell n, x.1.val<ro ∨ ro+t+3≤x.1.val ∨
        x.2.val<co ∨ co+M≤x.2.val → C x=B x) ∧
      blank C = (⟨ro+t+2,by omega⟩,⟨co,by omega⟩) := by
  let : NeZero (n*n) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne n)⟩
  have hr' : ro+(t+3)≤n := by omega
  obtain ⟨p,hp⟩ := path_of_zhong_word B (Zhong.downWord M t)
  refine ⟨Zhong.actSeq B (Zhong.downWord M t),p,?_,?_,?_,?_⟩
  · simpa [Zhong.downWord_length hM] using hp
  · exact Zhong.blockStrip_downWord_effect hr' hc (by omega) hM B hb
  · intro x hx
    rw [Zhong.actSeq_eq_permOf]
    change B (Zhong.permOf (blank B) (Zhong.downWord M t) x)=B x
    rw [hb]
    congr 1
    apply Zhong.permOf_apply_of_not_mem_traceSet
    intro hmem
    have h := Zhong.traceSet_blockStrip_downWord hr' hc (by omega) hM x hmem
    omega
  · change Zhong.blank (Zhong.actSeq B (Zhong.downWord M t)) = _
    rw [Zhong.blank_actSeq]
    change Zhong.trace (blank B) (Zhong.downWord M t) = _
    rw [hb]
    have h := Zhong.trace_map_of_neighbor_map
      (ι := Zhong.blockStrip (n := n) (t+3) M ro co hr' hc) (f := id)
      (Zhong.blockStrip_neighbor hr' hc)
      ((⟨2,by omega⟩,⟨0,by omega⟩) : Zhong.Cell (t+3) M)
      (Zhong.downWord M t) (Zhong.applicableFrom_downWord (by omega) hM)
    simp only [List.map_id] at h
    rw [Zhong.trace_downWord (by omega) hM] at h
    simpa [Zhong.blockStrip, Nat.add_assoc] using h

/-- The row-translation interface without its optional blank endpoint. -/
theorem exists_row_translation (B : Board n) (ro co M t : ℕ)
    (hr : ro+t+3 ≤ n) (hc : co+M ≤ n) (hM : 1<M)
    (hb : blank B = (⟨ro+2,by omega⟩,⟨co,by omega⟩)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ t*(6*M+3) ∧
      (∀ c : Fin M, C (⟨ro+t,by omega⟩,⟨co+c.val,by omega⟩) =
        B (⟨ro,by omega⟩,⟨co+c.val,by omega⟩)) ∧
      (∀ x : Cell n, x.1.val<ro ∨ ro+t+3≤x.1.val ∨
        x.2.val<co ∨ co+M≤x.2.val → C x=B x) := by
  obtain ⟨C,p,hp,hrow,hfix,_⟩ := exists_row_translation_with_blank B ro co M t hr hc hM hb
  exact ⟨C,p,hp,hrow,hfix⟩

private theorem block_column_word_length (H t K : ℕ) (hH : 1<H) :
    (Zhong.blockColWord H t K).length=K*(t*(6*H+4)+1) := by
  induction K with
  | zero => simp [Zhong.blockColWord]
  | succ K ih =>
      simp only [Zhong.blockColWord,List.length_append,List.length_replicate,
        Zhong.rightWord_length hH,ih]
      ring

/-- Translate a block of data columns to the right using one scratch row.
Data outside the source-to-destination band remains fixed. -/
theorem exists_column_block_translation (B : Board n) (ro co H K t : ℕ)
    (hr : ro+H≤n) (hH : 1<H) (hc : co+K+t+3≤n)
    (hb : blank B=(⟨ro,by omega⟩,⟨co+K+1,by omega⟩)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ K*(t*(6*H+4)+1) ∧
      (∀ (j : ℕ) (hj : j<K) (r : Fin n), ro+1≤r.val → r.val<ro+H →
        C (r,⟨co+t+j,by omega⟩)=B (r,⟨co+j,by omega⟩)) ∧
      (∀ x : Cell n, ro+1≤x.1.val → x.1.val<ro+H →
        (x.2.val<co ∨ co+t+K≤x.2.val) → C x=B x) := by
  let : NeZero (n*n) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne n)⟩
  obtain ⟨p,hp⟩ := path_of_zhong_word B (Zhong.blockColWord H t K)
  obtain ⟨he,hfix⟩ := Zhong.blockColWord_spec hr hH hc B hb
  refine ⟨Zhong.actSeq B (Zhong.blockColWord H t K),p,?_,he,hfix⟩
  simpa [block_column_word_length H t K hH] using hp
end SlidingPuzzle
