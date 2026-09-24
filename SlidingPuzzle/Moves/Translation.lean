import SlidingPuzzle.Bridge.Words
import Zhong.Algorithm.Lift

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

end SlidingPuzzle
