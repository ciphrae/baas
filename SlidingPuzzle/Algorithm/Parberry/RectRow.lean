import SlidingPuzzle.Algorithm.Parberry.RectPlacement
import SlidingPuzzle.Algorithm.Parberry.RowBudget
import Zhong.Algorithm.Assembly

/-! Complete rectangular row words, including a legal-word normalization before
lifting into a larger board. The linear boundary costs are explicit. -/
namespace SlidingPuzzle.Parberry.Rect
open Zhong
variable {n m : ℕ} [NeZero (n*m)]
local notation "c(" a "," b ")" => ((⟨a, by omega⟩ : Fin n), (⟨b, by omega⟩ : Fin m))

/-- Delete inactive moves without increasing length or changing the action. -/
theorem exists_applicable_word (p : Zhong.Cell n m) (σ : List Dir) :
    ∃ τ : List Dir, τ.length ≤ σ.length ∧ ApplicableFrom p τ ∧ permOf p τ=permOf p σ := by
  induction σ generalizing p with
  | nil => exact ⟨[],le_rfl,trivial,rfl⟩
  | cons δ σ ih =>
      cases h : neighbor? p δ with
      | none =>
          obtain ⟨τ,hlen,ha,hp⟩ := ih p
          exact ⟨τ,Nat.le_succ_of_le hlen,ha,by rw [permOf_cons_of_neighbor?_eq_none h,hp]⟩
      | some q =>
          obtain ⟨τ,hlen,ha,hp⟩ := ih q
          refine ⟨δ::τ,by simpa using Nat.succ_le_succ hlen,⟨q,h,ha⟩,?_⟩
          simp only [permOf_cons_of_neighbor? h,hp]

/-- The desired tile is selected from the board, not assumed to be in a sector. -/
theorem exists_correct_word (B : Zhong.Board n m) (a b : ℕ) (hm : m ≤ n)
    (ha2 : a+2 < n) (hb2 : b+2 < m)
    (hblank : Zhong.blank B=c(a+1,b))
    (hfixed : ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
      B z=Zhong.target n m z) :
    ∃ σ : List Dir, σ.length ≤ rowStepBudget n (b+1) ∧
      Zhong.blank (actSeq B σ)=c(a+1,b+1) ∧
      ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+2) →
        actSeq B σ z=Zhong.target n m z := by
  let s := B.symm (Zhong.target n m c(a,b+1))
  have hs : B s=Zhong.target n m c(a,b+1) := B.apply_symm_apply _
  have hfree : a < s.1.val ∨ (a=s.1.val ∧ b+1 ≤ s.2.val) := by
    by_contra hh
    have he : s=c(a,b+1) := (Zhong.target n m).injective ((hfixed s (by omega)).symm.trans hs)
    have hx := congrArg (fun z : Zhong.Cell n m => z.1.val) he
    have hy := congrArg (fun z : Zhong.Cell n m => z.2.val) he
    simp only at hx hy
    omega
  have hne : s≠c(a+1,b) := by
    intro he
    have hzero : Zhong.target n m c(a,b+1)=0 := by
      rw [← hs,he,← hblank]; exact B.apply_symm_apply 0
    exact Zhong.target_ne_zero a (b+1) (by omega) (by omega) hzero
  obtain ⟨σ,hlen,_,ht,hp,hfix⟩ := exists_placementWord a b s.1 s.2 hm hfree ha2 hb2 hne
  refine ⟨σ,by dsimp [rowStepBudget]; omega,?_,?_⟩
  · rw [blank_actSeq,hblank,ht]
  · intro z hz
    rw [actSeq_eq_permOf]
    change B (permOf (Zhong.blank B) σ z)=Zhong.target n m z
    rw [hblank]
    by_cases hprev : z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1)
    · rw [hfix z hprev,hfixed z hprev]
    · have he : z=c(a,b+1) := by
        apply Prod.ext <;> apply Fin.ext <;> simp only <;> omega
      rw [he,hp,hs]

/-- Concatenate the ordinary rectangular placements with no repeated routing. -/
theorem exists_prefix_word (B : Zhong.Board n m) (a d : ℕ) (hm : m ≤ n)
    (ha2 : a+2 < n) (hd : d+2 ≤ m) (hblank : Zhong.blank B=c(a+1,0))
    (hfixed : ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<1) →
      B z=Zhong.target n m z) :
    ∃ σ : List Dir, σ.length ≤ rowPrefixBudget n d ∧ Zhong.blank (actSeq B σ)=c(a+1,d) ∧
      ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<d+1) →
        actSeq B σ z=Zhong.target n m z := by
  induction d with
  | zero => exact ⟨[],by simp [rowPrefixBudget],hblank,hfixed⟩
  | succ d ih =>
      obtain ⟨σ,hlen,hblankσ,hσ⟩ := ih (by omega) hblank
      obtain ⟨τ,hlenτ,hblankτ,hτ⟩ := exists_correct_word (actSeq B σ) a d hm ha2
        (by omega) hblankσ hσ
      refine ⟨σ++τ,?_,?_,?_⟩
      · simpa only [List.length_append,rowPrefixBudget,Finset.sum_range_succ] using Nat.add_le_add hlen hlenτ
      · simpa only [actSeq_append] using hblankτ
      · simpa only [actSeq_append,Nat.add_assoc] using hτ

/-- Blank normalization stays outside the solved prefix. -/
theorem exists_start_word (B : Zhong.Board n m) (a : ℕ) (hm : m ≤ n)
    (ha2 : a+2 < n) (hm0 : 0 < m)
    (hfixed : ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<1) →
      B z=Zhong.target n m z) :
    ∃ σ : List Dir, σ.length ≤ 2*n ∧ Zhong.blank (actSeq B σ)=c(a+1,0) ∧
      ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<1) →
        actSeq B σ z=Zhong.target n m z := by
  let s := Zhong.blank B
  have hs : a < s.1.val ∨ (a=s.1.val ∧ 1 ≤ s.2.val) := by
    by_contra hh
    have hzero : Zhong.target n m s=0 := (hfixed s (by omega)).symm.trans (B.apply_symm_apply 0)
    exact Zhong.target_ne_zero s.1.val s.2.val s.2.isLt (by omega) hzero
  let w := moveToWord s.1.val s.2.val (a+1) 0
  have hlen : w.length ≤ 2*n := by
    exact (length_moveToWord_le _ _ _ _ (by omega : a+1 < n) s.1.isLt hm0 s.2.isLt).trans (by omega)
  have hfix : ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<1) → permOf s w z=z := by
    intro z hz
    apply permOf_apply_of_not_mem_traceSet
    intro hmem
    change z ∈ traceSet s (moveXWord s.1.val (a+1) ++ moveYWord s.2.val 0) at hmem
    rw [traceSet_append] at hmem
    rcases Finset.mem_union.mp hmem with hmem | hmem
    · have hh := moveXWord_traceSet s.1.val s.2.val (a+1)
        (by omega : a+1 < n) s.1.isLt s.2.isLt z hmem
      have hc := congrArg Fin.val hh.1
      simp only at hc
      omega
    · have ht := trace_moveXWord s.1.val s.2.val (a+1) (by omega : a+1 < n) s.1.isLt s.2.isLt
      change trace s (moveXWord s.1.val (a+1))=(⟨a+1,by omega⟩,s.2) at ht
      rw [ht] at hmem
      have hh := moveYWord_traceSet (a+1) s.2.val 0 hm0 (by omega : a+1 < n) s.2.isLt z hmem
      have hr := congrArg Fin.val hh
      simp only at hr
      omega
  refine ⟨w,hlen,?_,?_⟩
  · exact blank_actSeq_moveToWord s.1.val s.2.val (a+1) 0 (by omega) hm0 s.1.isLt s.2.isLt B rfl
  · intro z hz
    rw [actSeq_eq_permOf]
    change B (permOf s w z)=Zhong.target n m z
    rw [hfix z hz,hfixed z hz]

/-- An applicable complete row word, ready to lift into a larger puzzle. -/
theorem exists_complete_row_word (B : Zhong.Board n m) (a : ℕ)
    (ha2 : a+2 < n) (hm : 4 ≤ m) (hmn : m ≤ n)
    (habove : ∀ (x : Fin n) (y : Fin m), x.val<a → B (x,y)=Zhong.target n m (x,y)) :
    ∃ σ : List Dir, 2*σ.length ≤ 15*n^2+3002*n+1 ∧ ApplicableFrom (Zhong.blank B) σ ∧
      (∀ (x : Fin n) (y : Fin m), x.val<a → actSeq B σ (x,y)=B (x,y)) ∧
      (∀ y : Fin m, actSeq B σ ((⟨a,by omega⟩ : Fin n),y)=
        Zhong.target n m ((⟨a,by omega⟩ : Fin n),y)) := by
  obtain ⟨w,hw,haboveW,_,_,hlenW⟩ := Zhong.placeStep a (by omega) ha2 hm 0 (by omega)
    B 0 (by omega) habove (by intros; omega) (by intros; omega) (by omega)
  have hfirst : ∀ z : Zhong.Cell n m, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<1) →
      actSeq B w z=Zhong.target n m z := by
    intro z hz
    rcases hz with hz | ⟨hx,hy⟩
    · exact haboveW z.1 z.2 hz
    · have he : z=c(a,0) := by
        apply Prod.ext <;> apply Fin.ext <;> simp only <;> omega
      rw [he]; exact hw
  obtain ⟨q,hq,hblankQ,hQ⟩ := exists_start_word (actSeq B w) a hmn ha2 (by omega) hfirst
  obtain ⟨r,hr,hblankR,hR⟩ := exists_prefix_word (actSeq (actSeq B w) q) a (m-3) hmn ha2
    (by omega) hblankQ hQ
  obtain ⟨v,haboveV,_,hrowV,hlenV⟩ := Zhong.solveRowAux a (by omega) ha2 hm 0 (by omega)
    2 (m-2) (by omega) (by omega) (by omega) (actSeq (actSeq (actSeq B w) q) r)
    (fun x y hx => hR (x,y) (Or.inl hx)) (by intros; omega)
    (fun y hy => hR (⟨a,by omega⟩,y) (Or.inr ⟨rfl,by simp only; omega⟩))
  let σ := ((w++q)++r)++v
  have hlen : 2*σ.length ≤ 15*n^2+3002*n+1 := by
    have hW : w.length ≤ 502*n := by nlinarith
    have hV : v.length ≤ 1004*n := by
      rw [show m-(m-2)=2 by omega] at hlenV
      nlinarith
    have hcost := rowPrefixBudget_quadratic (by omega : 2 ≤ n) (by omega : (m-3)+1 ≤ n)
    simp only [σ,List.length_append]
    omega
  obtain ⟨τ,hlenτ,happ,hperm⟩ := exists_applicable_word (Zhong.blank B) σ
  have he : actSeq B τ=actSeq B σ := by
    apply Equiv.ext; intro z
    simp only [actSeq_eq_permOf,Equiv.trans_apply,hperm]
  refine ⟨τ,by omega,happ,?_,?_⟩
  · intro x y hx
    rw [he]
    simpa only [σ,actSeq_append] using (haboveV x y hx).trans (habove x y hx).symm
  · intro y
    rw [he]
    simpa only [σ,actSeq_append] using hrowV y

end SlidingPuzzle.Parberry.Rect
