import SlidingPuzzle.Bridge.Words
import Zhong.Algorithm.Place

/-! A top-row three-cycle, with every other cell restored. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

/-- Rotate the first three top-row cells while returning the blank below them.
The move bound includes the possibly nonlocal jumps inside the two-row strip. -/
theorem exists_top_three_cycle (B : Board n) (hn : 4 ≤ n)
    (hb : blank B = (⟨1,by omega⟩,0)) :
    ∃ C : Board n, ∃ q : Path B C,
      q.length ≤ 24 ∧ blank C = blank B ∧
      C (0,0) = B (0,⟨1,by omega⟩) ∧
      C (0,⟨1,by omega⟩) = B (0,⟨2,by omega⟩) ∧
      C (0,⟨2,by omega⟩) = B (0,0) ∧
      ∀ x : Cell n, x ≠ (0,0) → x ≠ (0,⟨1,by omega⟩) →
        x ≠ (0,⟨2,by omega⟩) → C x = B x := by
  classical
  let : NeZero (n*n) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne n)⟩
  let c₀ : Fin n := ⟨0, by omega⟩
  let c₁ : Fin n := ⟨1, by omega⟩
  let c₂ : Fin n := ⟨2, by omega⟩
  let p : Zhong.Cell 2 n := Zhong.bot c₀
  let u : Zhong.Cell 2 n := Zhong.top c₀
  let v : Zhong.Cell 2 n := Zhong.top c₁
  let w : Zhong.Cell 2 n := Zhong.top c₂
  have hc₀ : c₀.val + 1 < n := by simp [c₀]; omega
  have hc₁ : c₁.val + 1 < n := by simp [c₁]; omega
  have hlast : 2 * 1 ≤ c₂.val := by simp [c₂]
  have hreturn : (⟨c₂.val - 2 * 1, by omega⟩ : Fin n) = c₀ := by
    apply Fin.ext
    simp [c₀,c₂]
  have hpu : p ≠ u := by simp [p,u]
  have hpv : p ≠ v := by simp [p,v]
  have hpw : p ≠ w := by simp [p,w]
  have huv : u ≠ v := by simp [u,v,Fin.ext_iff]
  have huw : u ≠ w := by simp [u,w,Fin.ext_iff]
  have hvw : v ≠ w := by
    intro h
    have hh := congrArg (fun x : Zhong.Cell 2 n => x.2.val) h
    have : c₁.val ≠ c₂.val := by simp [c₁,c₂]
    exact this hh
  let σ₁ := Zhong.flipJumpWord 0
  let σ₂ := Zhong.row0Word 0
  let σ₃ := Zhong.row0Word 0
  let σ₄ := Zhong.reflJumpWord 1
  let P := Equiv.swap p u * Equiv.swap u v * Equiv.swap v w * Equiv.swap w p
  have h₁ : Zhong.permOf p σ₁ = Equiv.swap p u := by
    simpa [p,u,σ₁,Zhong.top,Zhong.bot] using
      (Zhong.permOf_flipJumpWord (m := n) 0 (by omega))
  have h₂ : Zhong.permOf u σ₂ = Equiv.swap u v := by
    simpa [u,v,σ₂,Zhong.top] using
      (Zhong.permOf_row0Word (m := n) (c := c₀) 0 hc₀)
  have h₃ : Zhong.permOf v σ₃ = Equiv.swap v w := by
    simpa [v,w,σ₃,Zhong.top] using
      (Zhong.permOf_row0Word (m := n) (c := c₁) 0 hc₁)
  have h₄ : Zhong.permOf w σ₄ = Equiv.swap w p := by
    simpa [w,p,σ₄,Zhong.top,Zhong.bot,hreturn] using
      (Zhong.permOf_reflJumpWord (m := n) (c := c₂) 1 hlast)
  have ht₁ : Zhong.trace p σ₁ = u := Zhong.trace_eq_of_permOf_swap h₁
  have ht₂ : Zhong.trace u σ₂ = v := Zhong.trace_eq_of_permOf_swap h₂
  have ht₃ : Zhong.trace v σ₃ = w := Zhong.trace_eq_of_permOf_swap h₃
  let σ := ((σ₁ ++ σ₂) ++ σ₃) ++ σ₄
  have happ : Zhong.ApplicableFrom p σ := by
    change Zhong.ApplicableFrom p (((σ₁ ++ σ₂) ++ σ₃) ++ σ₄)
    rw [Zhong.applicableFrom_append,Zhong.applicableFrom_append,
      Zhong.applicableFrom_append]
    simp only [Zhong.trace_append,ht₁,ht₂,ht₃]
    simpa [p,u,v,w,Zhong.top,Zhong.bot] using
      (⟨⟨⟨Zhong.applicableFrom_flipJumpWord (m := n) 0 (by omega),
          Zhong.applicableFrom_row0Word (m := n) (c := c₀) 0 hc₀⟩,
          Zhong.applicableFrom_row0Word (m := n) (c := c₁) 0 hc₁⟩,
        Zhong.applicableFrom_reflJumpWord (m := n) (c := c₂) 1 hlast⟩ : _)
  have hperm : Zhong.permOf p σ = P := by
    change Zhong.permOf p (((σ₁ ++ σ₂) ++ σ₃) ++ σ₄) = P
    exact Zhong.permOf_four_jumps σ₁ σ₂ σ₃ σ₄ h₁ ht₁ h₂ ht₂ h₃ ht₃ h₄
  have hlen : σ.length = 24 := by
    simp [σ,σ₁,σ₂,σ₃,σ₄,Zhong.flipJumpWord_length,
      Zhong.row0Word_length,Zhong.reflJumpWord_length]
  let ι := Zhong.hStrip (n := n) (m := n) 0 (by omega)
  have hfix (x : Zhong.Cell 2 n) (hx : x ∉ ({u,v,w} : Finset _)) : P x = x := by
    by_cases he : x = p
    · subst x
      exact Zhong.fourChain_apply_p hpu hpv hpw huv huw hvw
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      exact Zhong.fourChain_fixes he hx.1 hx.2.1 hx.2.2
  have hstart : ι p = blank B := by rw [hb]; rfl
  have hmap {a b : Zhong.Cell 2 n} (h : P a = b) :
      Zhong.permOf (blank B) σ (ι a) = ι b := by
    have hh := (Zhong.hStrip_permOf_spec (n := n) 0 (by omega) happ hperm h hfix).1
    simpa only [← hstart] using hh
  have hout (x : Cell n) (hx : x ∉ ({u,v,w} : Finset _).image ι) :
      Zhong.permOf (blank B) σ x = x := by
    have hh := (Zhong.hStrip_permOf_spec (n := n) 0 (by omega) happ hperm
      (Zhong.fourChain_apply_p hpu hpv hpw huv huw hvw) hfix).2 x hx
    simpa only [← hstart] using hh
  obtain ⟨q,hq⟩ := path_of_zhong_word B σ
  refine ⟨Zhong.actSeq B σ,q,hq.trans (by rw [hlen]),?_,?_,?_,?_,?_⟩
  · have hf := hmap (Zhong.fourChain_apply_p hpu hpv hpw huv huw hvw)
    rw [hstart] at hf
    apply (Zhong.actSeq B σ).injective
    simp only [blank, position, Equiv.apply_symm_apply]
    change 0 = (Zhong.actSeq B σ) (blank B)
    rw [Zhong.actSeq_eq_permOf]
    change 0 = B (Zhong.permOf (blank B) σ (blank B))
    rw [hf]
    exact (B.apply_symm_apply 0).symm
  · rw [Zhong.actSeq_eq_permOf]
    change B (Zhong.permOf (blank B) σ (ι u)) = B (ι v)
    rw [hmap (Zhong.fourChain_apply_u hpu hpv hpw huv huw hvw)]
  · rw [Zhong.actSeq_eq_permOf]
    change B (Zhong.permOf (blank B) σ (ι v)) = B (ι w)
    rw [hmap (Zhong.fourChain_apply_v hpu hpv hpw huv huw hvw)]
  · rw [Zhong.actSeq_eq_permOf]
    change B (Zhong.permOf (blank B) σ (ι w)) = B (ι u)
    rw [hmap (Zhong.fourChain_apply_w hpu hpv hpw huv huw hvw)]
  · intro x hxu hxv hxw
    rw [Zhong.actSeq_eq_permOf]
    change B (Zhong.permOf (blank B) σ x) = B x
    rw [hout]
    simp only [Finset.image_insert,Finset.image_singleton,Finset.mem_insert,
      Finset.mem_singleton,not_or]
    exact ⟨hxu,hxv,hxw⟩
end SlidingPuzzle
