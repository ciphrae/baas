import SlidingPuzzle.Algorithm.Parberry.RowBudget
import Zhong.Algorithm.Assembly

/-! A complete protected-row construction. The interior uses the sharp
Parberry placements; the three boundary columns use the existing checked
linear-cost placement routine. Thus their cost affects only the linear term,
not the quadratic coefficient `15/2`. -/
namespace SlidingPuzzle.Parberry
variable {n : ℕ} [NeZero n]
local notation "c(" a "," b ")" => ((⟨a, by omega⟩ : Fin n), (⟨b, by omega⟩ : Fin n))

/-- Normalize the blank below the first column while preserving the first tile
and every completed row above it. -/
theorem exists_row_start (B : Board n) (a : ℕ) (ha2 : a+2 < n)
    (hfixed : ∀ z : Cell n, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<1) → B z=target n z) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 2*n ∧ blank C=c(a+1,0) ∧
      ∀ z : Cell n, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<1) → C z=target n z := by
  let s := blank B
  have hs : a < s.1.val ∨ (a=s.1.val ∧ 1 ≤ s.2.val) := by
    by_contra hh
    have hzero : target n s=0 := (hfixed s (by omega)).symm.trans (B.apply_symm_apply 0)
    have he := (target n).injective (hzero.trans (target_bottomRight n).symm)
    have hx := congrArg (fun z : Cell n => z.1.val) he
    simp only [Fin.val_mk] at hx
    omega
  let w := Zhong.moveToWord s.1.val s.2.val (a+1) 0
  have hlen : w.length ≤ 2*n := by
    exact (Zhong.length_moveToWord_le _ _ _ _ (by omega : a+1 < n) s.1.isLt
      (by omega : 0 < n) s.2.isLt).trans (by omega)
  have hfix : ∀ z : Cell n, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<1) →
      Zhong.permOf s w z=z := by
    intro z hz
    apply Zhong.permOf_apply_of_not_mem_traceSet
    intro hmem
    change z ∈ Zhong.traceSet s (Zhong.moveXWord s.1.val (a+1) ++
      Zhong.moveYWord s.2.val 0) at hmem
    rw [Zhong.traceSet_append] at hmem
    rcases Finset.mem_union.mp hmem with hmem | hmem
    · have hh := Zhong.moveXWord_traceSet s.1.val s.2.val (a+1)
        (by omega : a+1 < n) s.1.isLt s.2.isLt z hmem
      have hc := congrArg Fin.val hh.1
      simp only [Fin.val_mk] at hc
      omega
    · have ht := Zhong.trace_moveXWord s.1.val s.2.val (a+1)
        (by omega : a+1 < n) s.1.isLt s.2.isLt
      change Zhong.trace s (Zhong.moveXWord s.1.val (a+1))=(⟨a+1,by omega⟩,s.2) at ht
      rw [ht] at hmem
      have hh := Zhong.moveYWord_traceSet (a+1) s.2.val 0
        (by omega : 0 < n) (by omega : a+1 < n) s.2.isLt z hmem
      have hr := congrArg Fin.val hh
      simp only [Fin.val_mk] at hr
      omega
  obtain ⟨p,hp⟩ := path_of_zhong_word B w
  refine ⟨Zhong.actSeq B w,p,hp.trans hlen,?_,?_⟩
  · exact Zhong.blank_actSeq_moveToWord s.1.val s.2.val (a+1) 0
      (by omega) (by omega) s.1.isLt s.2.isLt B rfl
  · intro z hz
    rw [Zhong.actSeq_eq_permOf]
    change B (Zhong.permOf s w z)=target n z
    rw [hfix z hz,hfixed z hz]

/-- A complete row solver with the Parberry quadratic leading coefficient.
The explicit linear remainder records the coarser boundary placement routine. -/
theorem exists_complete_row (B : Board n) (a : ℕ) (ha2 : a+2 < n) (hn : 4 ≤ n)
    (habove : ∀ x y : Fin n, x.val<a → B (x,y)=target n (x,y)) :
    ∃ C : Board n, ∃ p : Path B C,
      2*p.length ≤ 15*n^2+3002*n+1 ∧
      (∀ x y : Fin n, x.val<a → C (x,y)=B (x,y)) ∧
      (∀ y : Fin n, C ((⟨a,by omega⟩ : Fin n),y)=target n ((⟨a,by omega⟩ : Fin n),y)) := by
  letI : NeZero (n*n) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne n)⟩
  obtain ⟨w,hw,haboveW,_,_,hlenW⟩ := Zhong.placeStep a (by omega) ha2 hn 0 (by omega)
    B 0 (by omega) habove (by intros; omega) (by intros; omega) (by omega)
  obtain ⟨p,hp⟩ := path_of_zhong_word B w
  have hfirst : ∀ z : Cell n, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<1) →
      Zhong.actSeq B w z=target n z := by
    intro z hz
    rcases hz with hz | ⟨hx,hy⟩
    · exact haboveW z.1 z.2 hz
    · have he : z=c(a,0) := by
        apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega
      rw [he]; exact hw
  obtain ⟨D,q,hq,hblankD,hD⟩ := exists_row_start (Zhong.actSeq B w) a ha2 hfirst
  obtain ⟨E,r,hr,hblankE,hE⟩ := exists_row_prefix_quadratic D a (n-3) ha2 (by omega) hblankD hD
  obtain ⟨v,haboveV,_,hrowV,hlenV⟩ := Zhong.solveRowAux a (by omega) ha2 hn 0 (by omega)
    2 (n-2) (by omega) (by omega) (by omega) E
    (fun x y hx => hE (x,y) (Or.inl hx)) (by intros; omega)
    (fun y hy => hE (⟨a,by omega⟩,y) (Or.inr ⟨rfl,by simp only [Fin.val_mk]; omega⟩))
  obtain ⟨s,hs⟩ := path_of_zhong_word E v
  refine ⟨Zhong.actSeq E v,((p.append q).append r).append s,?_,?_,hrowV⟩
  · simp only [Path.length_append]
    have hW : p.length ≤ 502*n := by nlinarith
    have hV : s.length ≤ 1004*n := by
      have he : n-(n-2)=2 := by omega
      rw [he] at hlenV
      nlinarith
    nlinarith
  · intro x y hx
    exact (haboveV x y hx).trans (habove x y hx).symm

end SlidingPuzzle.Parberry
