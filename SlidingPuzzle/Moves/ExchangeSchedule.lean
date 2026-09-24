import SlidingPuzzle.Paths

/-! A finite schedule of disjoint paired region exchanges.

The schedule charges one set-exchange per nontrivial involution pair, so its
uniform coefficient is half the coefficient of the underlying exchange gadget.
-/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

/-- A legal set exchange with a uniform budget for regions of size at most M. -/
def SetExchangeBound (n : ℕ) [NeZero n] (M cost : ℕ) : Prop :=
  ∀ (B : Board n) (s t : Finset (Cell n)), Disjoint s t → s.card = t.card →
    2 ≤ s.card → s.card ≤ M →
    (∀ x ∈ s, B x ≠ 0) → (∀ x ∈ t, B x ≠ 0) →
    ∀ (P Q : Tile n → Prop), (∀ x ∈ s, P (B x)) → (∀ x ∈ t, Q (B x)) →
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 2*cost*n ∧ blank C = blank B ∧
      (∀ x ∈ s, Q (C x)) ∧ (∀ x ∈ t, P (C x)) ∧
      ∀ x, x ∉ s → x ∉ t → C x = B x

/-- Route disjoint regions according to an involution. Fixed regions need no
moves; each nontrivial pair is exchanged once, with all access restored. -/
theorem exists_involution_region_path_of_exchange {α : Type*} [DecidableEq α]
    (B : Board n) (_hn : 4 ≤ n) (S : α → Finset (Cell n))
    (τ : α → α) (hτ : Function.Involutive τ)
    (hdis : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (M : ℕ) (hsize : ∀ i, 2 ≤ (S i).card ∧ (S i).card ≤ M)
    (hcard : ∀ i, (S i).card = (S (τ i)).card)
    (hzero : ∀ i x, x ∈ S i → B x ≠ 0)
    (cost : ℕ) (hexchange : SetExchangeBound n M cost)
    (P : α → Tile n → Prop) (s : Finset α)
    (hclosed : ∀ i ∈ s, τ i ∈ s)
    (hinit : ∀ i ∈ s, ∀ x ∈ S i, P (τ i) (B x)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ cost*s.card*n ∧ blank C = blank B ∧
      (∀ i ∈ s, ∀ x ∈ S i, P i (C x)) ∧
      (∀ x, (∀ i ∈ s, x ∉ S i) → C x = B x) := by
  classical
  revert hclosed hinit
  induction s using Finset.strongInductionOn
  rename_i s ih
  intro hclosed hinit
  by_cases hempty : s = ∅
  · subst s
    exact ⟨B,Path.nil B,by simp,rfl,by simp,fun _ _ => rfl⟩
  obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  by_cases hfixed : τ i = i
  · let t := s.erase i
    have ht : t ⊂ s := Finset.erase_ssubset hi
    have htclosed : ∀ j ∈ t, τ j ∈ t := by
      intro j hj
      obtain ⟨hji,hjs⟩ := Finset.mem_erase.mp hj
      apply Finset.mem_erase.mpr
      refine ⟨?_,hclosed j hjs⟩
      intro he
      apply hji
      calc j = τ (τ j) := (hτ j).symm
           _ = i := by rw [he,hfixed]
    obtain ⟨C,p,hp,hbC,hC,hfix⟩ := ih t ht htclosed
      (fun j hj => hinit j (Finset.mem_of_mem_erase hj))
    refine ⟨C,p,hp.trans (by gcongr),hbC,?_,?_⟩
    · intro j hj x hx
      by_cases hji : j=i
      · subst j
        rw [hfix x (by
          intro j hj
          exact fun hxj => Finset.disjoint_left.mp (hdis i j (Finset.mem_erase.mp hj).1.symm) hx hxj)]
        simpa [hfixed] using hinit i hi x hx
      · exact hC j (Finset.mem_erase.mpr ⟨hji,hj⟩) x hx
    · intro x hx
      exact hfix x (fun j hj => hx j (Finset.mem_of_mem_erase hj))
  · let j := τ i
    have hj : j ∈ s := hclosed i hi
    have hij : i ≠ j := Ne.symm hfixed
    let t := (s.erase i).erase j
    have ht : t ⊂ s := (Finset.erase_subset _ _).trans_ssubset (Finset.erase_ssubset hi)
    have htmem {a : α} : a ∈ t ↔ a ≠ j ∧ a ≠ i ∧ a ∈ s := by
      simp [t,Finset.mem_erase]
    have htclosed : ∀ a ∈ t, τ a ∈ t := by
      intro a ha
      obtain ⟨haj,hai,has⟩ := htmem.mp ha
      apply htmem.mpr
      refine ⟨?_,?_,hclosed a has⟩
      · intro he
        exact hai (hτ.injective he)
      · intro he
        apply haj
        calc a = τ (τ a) := (hτ a).symm
             _ = j := by rw [he]
    obtain ⟨D,p,hp,hbD,hD,hfix⟩ := ih t ht htclosed
      (fun a ha => hinit a (htmem.mp ha).2.2)
    have hDi (x : Cell n) (hx : x ∈ S i) : D x = B x := by
      apply hfix
      intro a ha hxa
      exact Finset.disjoint_left.mp (hdis i a (htmem.mp ha).2.1.symm) hx hxa
    have hDj (x : Cell n) (hx : x ∈ S j) : D x = B x := by
      apply hfix
      intro a ha hxa
      exact Finset.disjoint_left.mp (hdis j a (htmem.mp ha).1.symm) hx hxa
    obtain ⟨C,q,hq,hbC,hCi,hCj,hCfix⟩ := hexchange D (S i) (S j)
      (hdis i j hij) (hcard i) (hsize i).1 (hsize i).2
      (fun x hx => by rw [hDi x hx]; exact hzero i x hx)
      (fun x hx => by rw [hDj x hx]; exact hzero j x hx)
      (P j) (P i)
      (fun x hx => by rw [hDi x hx]; exact hinit i hi x hx)
      (fun x hx => by rw [hDj x hx]; simpa [j,hτ i] using hinit j hj x hx)
    refine ⟨C,p.append q,?_,hbC.trans hbD,?_,?_⟩
    · rw [Path.length_append]
      calc
        p.length + q.length ≤ cost*t.card*n + 2*cost*n :=
          Nat.add_le_add hp hq
        _ = cost*(t.card+2)*n := by ring
        _ ≤ cost*s.card*n := by
          have hcard : t.card + 2 = s.card := by
            have hjt : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
            dsimp [t]
            have h1 := Finset.card_erase_add_one hi
            have h2 := Finset.card_erase_add_one hjt
            omega
          rw [hcard]
    · intro a ha x hx
      by_cases hai : a=i
      · subst a; exact hCi x hx
      by_cases haj : a=j
      · subst a; exact hCj x hx
      rw [hCfix x (fun hxi => Finset.disjoint_left.mp (hdis a i hai) hx hxi)
        (fun hxj => Finset.disjoint_left.mp (hdis a j haj) hx hxj)]
      exact hD a (htmem.mpr ⟨haj,hai,ha⟩) x hx
    · intro x hx
      rw [hCfix x (hx i hi) (hx j hj)]
      exact hfix x (fun a ha => hx a (htmem.mp ha).2.2)
/-- Only nonfixed regions contribute to the exchange budget. The original
schedule can be applied to this closed subset, leaving every fixed region alone. -/
theorem exists_involution_region_path_active_of_exchange {α : Type*} [DecidableEq α]
    (B : Board n) (hn : 4 ≤ n) (S : α → Finset (Cell n))
    (τ : α → α) (hτ : Function.Involutive τ)
    (hdis : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (M : ℕ) (hsize : ∀ i, 2 ≤ (S i).card ∧ (S i).card ≤ M)
    (hcard : ∀ i, (S i).card = (S (τ i)).card)
    (hzero : ∀ i x, x ∈ S i → B x ≠ 0)
    (cost : ℕ) (hexchange : SetExchangeBound n M cost)
    (P : α → Tile n → Prop) (s : Finset α)
    (hclosed : ∀ i ∈ s, τ i ∈ s)
    (hinit : ∀ i ∈ s, ∀ x ∈ S i, P (τ i) (B x)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ cost*(s.filter (fun i => τ i ≠ i)).card*n ∧
      blank C = blank B ∧
      (∀ i ∈ s, ∀ x ∈ S i, P i (C x)) ∧
      (∀ x, (∀ i ∈ s, x ∉ S i) → C x = B x) := by
  classical
  let t := s.filter (fun i => τ i ≠ i)
  have htclosed : ∀ i ∈ t, τ i ∈ t := by
    intro i hi
    obtain ⟨his,hine⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hclosed i his, by simpa [hτ i, ne_comm] using hine⟩
  obtain ⟨C,p,hp,hb,hC,hfix⟩ := exists_involution_region_path_of_exchange B hn S τ hτ
    hdis M hsize hcard hzero cost hexchange P t htclosed
    (fun i hi => hinit i (Finset.mem_filter.mp hi).1)
  refine ⟨C,p,hp,hb,?_,fun x hx => hfix x (fun i hi => hx i (Finset.mem_filter.mp hi).1)⟩
  intro i hi x hx
  by_cases he : τ i = i
  · rw [hfix x (by
      intro j hj hxj
      have hji : i ≠ j := by
        rintro rfl
        exact (Finset.mem_filter.mp hj).2 he
      exact Finset.disjoint_left.mp (hdis i j hji) hx hxj)]
    simpa [he] using hinit i hi x hx
  · exact hC i (Finset.mem_filter.mpr ⟨hi,he⟩) x hx

end SlidingPuzzle
