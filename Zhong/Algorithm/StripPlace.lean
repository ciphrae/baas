import Zhong.Algorithm.Place

namespace Zhong

open Equiv

variable {n m : ℕ}

/-- **Bounded lower-row candidate.**  The candidate of `exists_low_color_from` can always be
found in the four columns `[lo, lo + 4)`.  This is what lets a placement use a *fixed-width*
workspace, such as a single `R` block of the data row below, instead of the whole half-plane:
the auxiliary never leaves the block. -/
lemma exists_low_color_lt {m : ℕ} (lo d : ℕ) (hd : d < 2) (hlo : lo + 4 ≤ m)
    (x : Cell 2 m) :
    ∃ u : Cell 2 m, u.1.val = 1 ∧ (u.1.val + u.2.val) % 2 = d ∧ lo ≤ u.2.val
      ∧ u.2.val < lo + 4 ∧ u ≠ x := by
  classical
  have key : ∀ c : ℕ, c % 2 = (d + 1) % 2 → lo ≤ c → c ≤ lo + 1 → c + 2 < m →
      ∃ u : Cell 2 m, u.1.val = 1 ∧ (u.1.val + u.2.val) % 2 = d ∧ lo ≤ u.2.val
        ∧ u.2.val < lo + 4 ∧ u ≠ x := by
    intro c hc hloc hclu hcm
    let u0 : Cell 2 m := ((1 : Fin 2), ⟨c, by omega⟩)
    let u1 : Cell 2 m := ((1 : Fin 2), ⟨c + 2, by omega⟩)
    have hc0 : (u0.1.val + u0.2.val) % 2 = d := by
      simp only [u0]; omega
    have hc1 : (u1.1.val + u1.2.val) % 2 = d := by
      simp only [u1]; omega
    have hne : u0 ≠ u1 := by
      intro h
      have := congrArg (fun w : Cell 2 m => w.2.val) h
      simp only [u0, u1] at this
      omega
    have hb0 : u0.2.val < lo + 4 := by simp only [u0]; omega
    have hb1 : u1.2.val < lo + 4 := by simp only [u1]; omega
    by_cases hx : u0 = x
    · exact ⟨u1, by simp [u1], hc1, by simp only [u1]; omega, hb1,
        fun h => hne (hx.trans h.symm)⟩
    · exact ⟨u0, by simp [u0], hc0, by simp only [u0]; omega, hb0, hx⟩
  by_cases hpar : lo % 2 = (d + 1) % 2
  · exact key lo hpar le_rfl (by omega) (by omega)
  · exact key (lo + 1) (by omega) (by omega) (by omega) (by omega)

/-- **Three candidates in the full strip.**  In the `2 × w` unplaced region (`w = m - lo ≥ 3`)
there are three cells of every colour, one in each of the columns `lo, lo+1, lo+2`.  Hence one
of them avoids any two prescribed cells.  Unlike `exists_low_color_from` the cell may lie in
either row, which is what lets the two-row solver avoid the cell it has just placed. -/
lemma exists_strip_color_from {m : ℕ} (lo d : ℕ) (hd : d < 2) (hlo : lo + 3 ≤ m)
    (x y : Cell 2 m) :
    ∃ u : Cell 2 m, (u.1.val + u.2.val) % 2 = d ∧ lo ≤ u.2.val ∧ u ≠ x ∧ u ≠ y := by
  classical
  have key : ∀ c : ℕ, lo ≤ c → c < m → ∃ u : Cell 2 m,
      (u.1.val + u.2.val) % 2 = d ∧ u.2.val = c := by
    intro c hc hcm
    refine ⟨((⟨(d + c) % 2, by omega⟩ : Fin 2), ⟨c, hcm⟩), ?_, rfl⟩
    simp only
    omega
  obtain ⟨u0, hc0, he0⟩ := key lo le_rfl (by omega)
  obtain ⟨u1, hc1, he1⟩ := key (lo + 1) (by omega) (by omega)
  obtain ⟨u2, hc2, he2⟩ := key (lo + 2) (by omega) (by omega)
  have hl0 : lo ≤ u0.2.val := by rw [he0]
  have hl1 : lo ≤ u1.2.val := by rw [he1]; omega
  have hl2 : lo ≤ u2.2.val := by rw [he2]; omega
  have d01 : u0 ≠ u1 := by intro h; have := congrArg (fun w : Cell 2 m => w.2.val) h; omega
  have d02 : u0 ≠ u2 := by intro h; have := congrArg (fun w : Cell 2 m => w.2.val) h; omega
  have d12 : u1 ≠ u2 := by intro h; have := congrArg (fun w : Cell 2 m => w.2.val) h; omega
  by_cases h0 : u0 ≠ x ∧ u0 ≠ y
  · exact ⟨u0, hc0, hl0, h0.1, h0.2⟩
  · by_cases h1 : u1 ≠ x ∧ u1 ≠ y
    · exact ⟨u1, hc1, hl1, h1.1, h1.2⟩
    · refine ⟨u2, hc2, hl2, ?_, ?_⟩
      · intro hxu2
        have hxu2' : x = u2 := hxu2.symm
        rcases not_and_or.mp h0 with h | h
        · exact absurd ((not_not.mp h).trans hxu2') d02
        · rcases not_and_or.mp h1 with h' | h'
          · exact absurd ((not_not.mp h').trans hxu2') d12
          · exact absurd ((not_not.mp h).trans (not_not.mp h').symm) d01
      · intro hyu2
        have hyu2' : y = u2 := hyu2.symm
        rcases not_and_or.mp h0 with h | h
        · rcases not_and_or.mp h1 with h' | h'
          · exact absurd ((not_not.mp h).trans (not_not.mp h').symm) d01
          · exact absurd ((not_not.mp h').trans hyu2') d12
        · exact absurd ((not_not.mp h).trans hyu2') d02

/-! ### The general placement primitive on a strip

`stripPlace` places the tile at `a` into the target `c` (in the upper row of the strip),
assuming the blank is at `p` in the *lower* row.  It realises the four parity cases of
`Algorithm/Place.lean`; when all three colours agree it first jumps the blank to an
opposite-coloured cell and reduces to the case `A = C ≠ P`.  Auxiliaries are chosen in the
lower row, so the only upper-row cells touched are the tile and the target. -/

/-- Turn the "fixes everything outside the support `S`" property of a placement into the
row- and target-aware property needed by the row assembly: rows above `r` are fixed, and in
row `r` every cell left of the target is fixed.  It suffices that the upper-row elements of
`S` are either the target `c` or lie at or to the right of `c`. -/
lemma fixes_of_support {r : ℕ} (hr : r + 1 < n) {p c : Cell 2 m} {σ : List Dir}
    {S : Finset (Cell 2 m)}
    (hfix : ∀ y : Cell n m, y ∉ S.image (hStrip (m := m) r hr) →
        permOf (hStrip (m := m) r hr p) σ y = y)
    (hS : ∀ x ∈ S, x.1.val = 0 → x = c ∨ c.2.val ≤ x.2.val) :
    (∀ z : Cell n m, z.1.val < r → permOf (hStrip (m := m) r hr p) σ z = z) ∧
    (∀ z : Cell n m, z.1.val = r → z.2.val < c.2.val →
        permOf (hStrip (m := m) r hr p) σ z = z) := by
  constructor
  · intro z hz
    apply hfix
    intro hzmem
    rcases Finset.mem_image.mp hzmem with ⟨x, _, hxz⟩
    have := congrArg (fun w : Cell n m => w.1.val) hxz
    simp only [hStrip, Fin.val_mk] at this
    omega
  · intro z hz hzc
    apply hfix
    intro hzmem
    rcases Finset.mem_image.mp hzmem with ⟨x, hxS, hxz⟩
    have hxrow : x.1.val = 0 := by
      have := congrArg (fun w : Cell n m => w.1.val) hxz
      simp only [hStrip, Fin.val_mk] at this
      omega
    have hx2 : z.2.val = x.2.val := by
      have := congrArg (fun w : Cell n m => w.2.val) hxz
      simp only [hStrip] at this
      omega
    rcases hS x hxS hxrow with h | h
    · rw [h] at hx2; omega
    · omega

/-- **Fixed-workspace support bound for a single-row placement.**  If every lower-row cell of
the support other than the blank `p` and the tile `a` lies in the four columns `[lo, lo + 4)`,
then the placement fixes every lower-row cell outside `[lo, lo + 4)` except the blank and the
tile.  This is the property that lets a placement run inside a *fixed-width* workspace, such as
a single `R` block of the data row below. -/
lemma stripPlace_fix_low {r : ℕ} (hr : r + 1 < n) {p a : Cell 2 m} {σ : List Dir}
    {S : Finset (Cell 2 m)} {lo : ℕ}
    (hfix : ∀ y : Cell n m, y ∉ S.image (hStrip (m := m) r hr) →
        permOf (hStrip (m := m) r hr p) σ y = y)
    (hS : ∀ x ∈ S, x.1.val = 1 → x ≠ p → x ≠ a → lo ≤ x.2.val ∧ x.2.val < lo + 4) :
    ∀ (y : Fin m), (y.val < lo ∨ lo + 4 ≤ y.val) →
      ((1, y) : Cell 2 m) ≠ p → ((1, y) : Cell 2 m) ≠ a →
      permOf (hStrip (m := m) r hr p) σ (hStrip r hr (1, y)) = hStrip r hr (1, y) := by
  intro y hy hne_p hne_a
  apply hfix
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨x, hxS, hxz⟩
  have hx : x = (1, y) := hStrip_injective r hr hxz
  subst hx
  have hb := hS (1, y) hxS rfl hne_p hne_a
  simp only at hb
  omega

/-- The row-fix property for a placement whose target lies in the *lower* row: rows above the
strip are fixed, and every cell of the lower row left of the target is fixed, provided the
lower-row elements of the support are the target or lie to its right. -/
lemma fixes_of_support_low {r : ℕ} (hr : r + 1 < n) {p c : Cell 2 m} {σ : List Dir}
    {S : Finset (Cell 2 m)}
    (hfix : ∀ y : Cell n m, y ∉ S.image (hStrip (m := m) r hr) →
        permOf (hStrip (m := m) r hr p) σ y = y)
    (hS : ∀ x ∈ S, x.1.val = 1 → x = c ∨ c.2.val ≤ x.2.val) :
    (∀ z : Cell n m, z.1.val < r → permOf (hStrip (m := m) r hr p) σ z = z) ∧
    (∀ z : Cell n m, z.1.val = r + 1 → z.2.val < c.2.val →
        permOf (hStrip (m := m) r hr p) σ z = z) := by
  constructor
  · intro z hz
    apply hfix
    intro hzmem
    rcases Finset.mem_image.mp hzmem with ⟨x, _, hxz⟩
    have := congrArg (fun w : Cell n m => w.1.val) hxz
    simp only [hStrip, Fin.val_mk] at this
    omega
  · intro z hz hzc
    apply hfix
    intro hzmem
    rcases Finset.mem_image.mp hzmem with ⟨x, hxS, hxz⟩
    have hxrow : x.1.val = 1 := by
      have := congrArg (fun w : Cell n m => w.1.val) hxz
      simp only [hStrip, Fin.val_mk] at this
      omega
    have hx2 : z.2.val = x.2.val := by
      have := congrArg (fun w : Cell n m => w.2.val) hxz
      simp only [hStrip] at this
      omega
    rcases hS x hxS hxrow with h | h
    · rw [h] at hx2; omega
    · omega

lemma fixes_of_low {r : ℕ} (hr : r + 1 < n) {p : Cell 2 m} {σ : List Dir} {lo : ℕ}
    {S : Finset (Cell 2 m)}
    (hfix : ∀ y : Cell n m, y ∉ S.image (hStrip (m := m) r hr) →
        permOf (hStrip (m := m) r hr p) σ y = y)
    (hS : ∀ x ∈ S, lo ≤ x.2.val) :
    ∀ z : Cell n m, z.2.val < lo → permOf (hStrip (m := m) r hr p) σ z = z := by
  intro z hz
  apply hfix
  intro hzmem
  rcases Finset.mem_image.mp hzmem with ⟨x, hxS, hxz⟩
  have h2 : z.2.val = x.2.val := by
    have := congrArg (fun w : Cell n m => w.2.val) hxz
    simp only [hStrip] at this
    exact this.symm
  have := hS x hxS
  omega

theorem stripPlace (r : ℕ) (hr : r + 1 < n) (_hm : 4 ≤ m) (lo : ℕ) (hlo : lo + 4 ≤ m)
    {p a c : Cell 2 m}
    (hp : p.1.val = 1) (hc : c.1.val = 0) (hpa : p ≠ a) (hac : a ≠ c)
    (hrow : a.1.val = 0 → c.2.val ≤ a.2.val)
    (hplo : lo ≤ p.2.val) (halo : lo ≤ a.2.val) (hclo : lo ≤ c.2.val) :
    ∃ σ : List Dir, ApplicableFrom (hStrip (m := m) r hr p) σ ∧
      permOf (hStrip (m := m) r hr p) σ (hStrip r hr c) = hStrip r hr a ∧
      (∀ z : Cell n m, z.1.val < r → permOf (hStrip (m := m) r hr p) σ z = z) ∧
      (∀ z : Cell n m, z.1.val = r → z.2.val < c.2.val →
          permOf (hStrip (m := m) r hr p) σ z = z) ∧
      (∀ z : Cell n m, z.2.val < lo → permOf (hStrip (m := m) r hr p) σ z = z) ∧
      (∀ (y : Fin m), (y.val < lo ∨ lo + 4 ≤ y.val) →
          ((1, y) : Cell 2 m) ≠ p → ((1, y) : Cell 2 m) ≠ a →
          permOf (hStrip (m := m) r hr p) σ (hStrip r hr (1, y)) = hStrip r hr (1, y)) ∧
      σ.length ≤ 96 * m + 8 := by
  have hpc_ne : p ≠ c := by
    intro h; have := congrArg (fun w : Cell 2 m => w.1.val) h; omega
  by_cases hpa1 : (p.1.val + p.2.val + a.1.val + a.2.val) % 2 = 1
  · by_cases hpc1 : (p.1.val + p.2.val + c.1.val + c.2.val) % 2 = 1
    · -- Case 3: `A = C ≠ P`.
      obtain ⟨v, hv1, hvcol, hvlo, hvhi, hvp⟩ :
          ∃ v : Cell 2 m, v.1.val = 1 ∧
            (v.1.val + v.2.val) % 2 = (1 + p.2.val) % 2 ∧ lo ≤ v.2.val ∧
            v.2.val < lo + 4 ∧ v ≠ p :=
        exists_low_color_lt lo ((1 + p.2.val) % 2) (by omega) hlo p
      obtain ⟨σ, hapσ, hperm, hfix, hlen⟩ :=
        hStrip_place_four_content (n := n) (m := m) r hr
          (p := p) (a := a) (v := v) (c := c)
          (by omega) (by omega) (by omega) (by omega)
          hvp.symm hpc_ne hac
      obtain ⟨hf1, hf2⟩ := fixes_of_support (S := ({p, a, v, c} : Finset (Cell 2 m)))
        hr hfix (by
          intro x hx hx1
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with h | h | h | h
          · rw [h] at hx1; omega
          · rw [h] at hx1 ⊢; exact Or.inr (hrow hx1)
          · rw [h] at hx1; omega
          · exact Or.inl h)
      have hf3 := fixes_of_low (lo := lo) hr hfix (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h | h | h
        · rw [h]; exact hplo
        · rw [h]; exact halo
        · rw [h]; exact hvlo
        · rw [h]; exact hclo)
      have hf4 := stripPlace_fix_low (lo := lo) hr hfix (by
        intro x hx hx1 hxp hxa
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h | h | h
        · rw [h] at hxp; exact absurd rfl hxp
        · rw [h] at hxa; exact absurd rfl hxa
        · rw [h]; exact ⟨hvlo, hvhi⟩
        · rw [h] at hx1; omega)
      exact ⟨σ, hapσ, hperm, hf1, hf2, hf3, hf4, by omega⟩
    · -- Case 2: `A ≠ P = C`.
      obtain ⟨u, hu1, hucol, hulo, huhi, hua⟩ :
          ∃ u : Cell 2 m, u.1.val = 1 ∧
            (u.1.val + u.2.val) % 2 = p.2.val % 2 ∧ lo ≤ u.2.val ∧
            u.2.val < lo + 4 ∧ u ≠ a :=
        exists_low_color_lt lo (p.2.val % 2) (by omega) hlo a
      obtain ⟨σ, hapσ, hperm, hfix, hlen⟩ :=
        hStrip_place_four_content_v (n := n) (m := m) r hr
          (p := p) (u := u) (c := c) (a := a)
          (by omega) (by omega) (by omega) (by omega)
          hpc_ne hua
      obtain ⟨hf1, hf2⟩ := fixes_of_support (S := ({p, u, c, a} : Finset (Cell 2 m)))
        hr hfix (by
          intro x hx hx1
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with h | h | h | h
          · rw [h] at hx1; omega
          · rw [h] at hx1; omega
          · exact Or.inl h
          · rw [h] at hx1 ⊢; exact Or.inr (hrow hx1))
      have hf3 := fixes_of_low (lo := lo) hr hfix (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h | h | h
        · rw [h]; exact hplo
        · rw [h]; exact hulo
        · rw [h]; exact hclo
        · rw [h]; exact halo)
      have hf4 := stripPlace_fix_low (lo := lo) hr hfix (by
        intro x hx hx1 hxp hxa
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h | h | h
        · rw [h] at hxp; exact absurd rfl hxp
        · rw [h]; exact ⟨hulo, huhi⟩
        · rw [h] at hx1; omega
        · rw [h] at hxa; exact absurd rfl hxa)
      exact ⟨σ, hapσ, hperm, hf1, hf2, hf3, hf4, by omega⟩
  · by_cases hpc1 : (p.1.val + p.2.val + c.1.val + c.2.val) % 2 = 1
    · -- Case 1: `A = P ≠ C`.
      obtain ⟨σ, hapσ, hperm, hfix, hlen⟩ :=
        hStrip_place_two_content (n := n) (m := m) r hr
          (p := p) (c := c) (a := a)
          hpc1 (by omega) hpa.symm hac
      obtain ⟨hf1, hf2⟩ := fixes_of_support (S := ({p, c, a} : Finset (Cell 2 m)))
        hr hfix (by
          intro x hx hx1
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with h | h | h
          · rw [h] at hx1; omega
          · exact Or.inl h
          · rw [h] at hx1 ⊢; exact Or.inr (hrow hx1))
      have hf3 := fixes_of_low (lo := lo) hr hfix (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h | h
        · rw [h]; exact hplo
        · rw [h]; exact hclo
        · rw [h]; exact halo)
      have hf4 := stripPlace_fix_low (lo := lo) hr hfix (by
        intro x hx hx1 hxp hxa
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h | h
        · rw [h] at hxp; exact absurd rfl hxp
        · rw [h] at hx1; omega
        · rw [h] at hxa; exact absurd rfl hxa)
      exact ⟨σ, hapσ, hperm, hf1, hf2, hf3, hf4, by omega⟩
    · -- Case 4: `A = P = C`.  Jump the blank to an opposite-coloured cell `q`.
      obtain ⟨q, hq1, hqcol, hqlo, hqhi, hqa⟩ :
          ∃ q : Cell 2 m, q.1.val = 1 ∧
            (q.1.val + q.2.val) % 2 = p.2.val % 2 ∧ lo ≤ q.2.val ∧
            q.2.val < lo + 4 ∧ q ≠ a :=
        exists_low_color_lt lo (p.2.val % 2) (by omega) hlo a
      have hpq_col : (p.1.val + p.2.val + q.1.val + q.2.val) % 2 = 1 := by omega
      have hjump : ∃ σj : List Dir, ApplicableFrom (hStrip (m := m) r hr p) σj ∧
          permOf (hStrip (m := m) r hr p) σj
            = Equiv.swap (hStrip (m := m) r hr p) (hStrip (m := m) r hr q) ∧
          σj.length ≤ 12 * m + 1 := by
        obtain ⟨σj, hapj, hpermj, hlenj⟩ := strip_jump (p := p) (q := q) hpq_col
        refine ⟨σj, ?_, ?_, hlenj⟩
        · simpa using applicableFrom_map_of_neighbor_map (ι := hStrip (m := m) r hr)
            (f := id) (hStrip_neighbor r hr) hapj
        · simpa using permOf_map_eq_swap (hStrip_injective r hr) (hStrip_neighbor r hr)
            p σj hapj hpermj
      obtain ⟨σj, hapj, hpermj, hlenj⟩ := hjump
      have htracej : trace (hStrip (m := m) r hr p) σj = hStrip (m := m) r hr q := by
        rw [← permOf_symm_apply, hpermj, Equiv.symm_swap, Equiv.swap_apply_left]
      obtain ⟨v, hv1, hvcol, hvlo, hvhi, hvq⟩ :
          ∃ v : Cell 2 m, v.1.val = 1 ∧
            (v.1.val + v.2.val) % 2 = (1 + q.2.val) % 2 ∧ lo ≤ v.2.val ∧
            v.2.val < lo + 4 ∧ v ≠ q :=
        exists_low_color_lt lo ((1 + q.2.val) % 2) (by omega) hlo q
      obtain ⟨σc, hapσc, hpermc, hfixc, hlenc⟩ :=
        hStrip_place_four_content (n := n) (m := m) r hr
          (p := q) (a := a) (v := v) (c := c)
          (by omega) (by omega) (by omega) (by omega)
          hvq.symm
          (by intro h; have := congrArg (fun w : Cell 2 m => w.1.val) h; omega)
          hac
      obtain ⟨hf1, hf2⟩ := fixes_of_support (S := ({q, a, v, c} : Finset (Cell 2 m)))
        hr hfixc (by
          intro x hx hx1
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with h | h | h | h
          · rw [h] at hx1; omega
          · rw [h] at hx1 ⊢; exact Or.inr (hrow hx1)
          · rw [h] at hx1; omega
          · exact Or.inl h)
      have hf3 := fixes_of_low (lo := lo) hr hfixc (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h | h | h
        · rw [h]; exact hqlo
        · rw [h]; exact halo
        · rw [h]; exact hvlo
        · rw [h]; exact hclo)
      have hf4c := stripPlace_fix_low (lo := lo) hr hfixc (by
        intro x hx hx1 hxp hxa
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h | h | h
        · rw [h]; exact ⟨hqlo, hqhi⟩
        · rw [h] at hxa; exact absurd rfl hxa
        · rw [h]; exact ⟨hvlo, hvhi⟩
        · rw [h] at hx1; omega)
      have hzfixj : ∀ {z : Cell n m}, z.1.val ≤ r →
          permOf (hStrip (m := m) r hr p) σj z = z := by
        intro z hz
        rw [hpermj]
        exact Equiv.swap_apply_of_ne_of_ne
          (by intro h; have := congrArg (fun w : Cell n m => w.1.val) h
              simp only [hStrip, Fin.val_mk] at this; omega)
          (by intro h; have := congrArg (fun w : Cell n m => w.1.val) h
              simp only [hStrip, Fin.val_mk] at this; omega)
      have hzfixjlo : ∀ {z : Cell n m}, z.2.val < lo →
          permOf (hStrip (m := m) r hr p) σj z = z := by
        intro z hz
        rw [hpermj]
        exact Equiv.swap_apply_of_ne_of_ne
          (by intro h; have := congrArg (fun w : Cell n m => w.2.val) h
              simp only [hStrip] at this; omega)
          (by intro h; have := congrArg (fun w : Cell n m => w.2.val) h
              simp only [hStrip] at this; omega)
      have hf4 : ∀ (y : Fin m), (y.val < lo ∨ lo + 4 ≤ y.val) →
          ((1, y) : Cell 2 m) ≠ p → ((1, y) : Cell 2 m) ≠ a →
          permOf (hStrip (m := m) r hr p) (σj ++ σc) (hStrip r hr (1, y))
            = hStrip r hr (1, y) := by
        intro y hy hne_p hne_a
        have hne_q : ((1, y) : Cell 2 m) ≠ q := by
          intro h
          have := congrArg (fun w : Cell 2 m => w.2.val) h
          simp only at this
          omega
        have hzj : permOf (hStrip (m := m) r hr p) σj (hStrip r hr (1, y))
            = hStrip r hr (1, y) := by
          rw [hpermj]
          exact Equiv.swap_apply_of_ne_of_ne
            (fun h => hne_p (hStrip_injective r hr h))
            (fun h => hne_q (hStrip_injective r hr h))
        rw [permOf_append, htracej, Equiv.Perm.mul_apply, hf4c y hy hne_q hne_a, hzj]
      refine ⟨σj ++ σc, ?_, ?_, ?_, ?_, ?_, hf4, by rw [List.length_append]; omega⟩
      · rw [applicableFrom_append, htracej]; exact ⟨hapj, hapσc⟩
      · rw [permOf_append, htracej, Equiv.Perm.mul_apply, hpermc, hpermj]
        exact Equiv.swap_apply_of_ne_of_ne
          (fun h => hpa (hStrip_injective r hr h).symm)
          (fun h => hqa (hStrip_injective r hr h).symm)
      · intro z hz
        rw [permOf_append, htracej, Equiv.Perm.mul_apply, hf1 z hz, hzfixj (by omega)]
      · intro z hz hzc
        rw [permOf_append, htracej, Equiv.Perm.mul_apply, hf2 z hz hzc, hzfixj (by omega)]
      · intro z hz
        rw [permOf_append, htracej, Equiv.Perm.mul_apply, hf3 z hz, hzfixjlo hz]

/-! ### The two-row placement primitives

`stripPlace` and `stripPlaceFlip` choose their auxiliaries in a single row so that the row
assembly never disturbs the row it is working on.  The two-row solver, by contrast, places
*both* rows of a strip and has to avoid the cell it has just placed.  Allowing the auxiliary
to lie in either row gives three candidates of each colour in the `2 × 3` unplaced region,
enough to avoid two prescribed cells (`exists_strip_color_from`).  These variants require the
frontier to coincide with the target column, so that an auxiliary in the target row still lies
to the right of the target. -/

/-- Two-row placement, blank in the lower row.  Same as `stripPlace` but the auxiliaries may
lie in either row, at columns `≥ c.2`, and one extra cell `J` (the cell just placed) is
avoided. -/
theorem stripPlace2 (r : ℕ) (hr : r + 1 < n) (_hm : 4 ≤ m) (lo : ℕ) (hlo : lo + 3 ≤ m)
    {p a c J : Cell 2 m} (hlo_eq : c.2.val = lo)
    (hp : p.1.val = 1) (hc : c.1.val = 0) (hpa : p ≠ a) (hac : a ≠ c)
    (hrow : a.1.val = 0 → c.2.val ≤ a.2.val)
    (hplo : lo ≤ p.2.val) (halo : lo ≤ a.2.val) (hclo : lo ≤ c.2.val) :
    ∃ σ : List Dir, ApplicableFrom (hStrip (m := m) r hr p) σ ∧
      permOf (hStrip (m := m) r hr p) σ (hStrip r hr c) = hStrip r hr a ∧
      (∀ z : Cell n m, z.1.val < r → permOf (hStrip (m := m) r hr p) σ z = z) ∧
      (∀ z : Cell n m, z.1.val = r → z.2.val < c.2.val →
          permOf (hStrip (m := m) r hr p) σ z = z) ∧
      (∀ z : Cell n m, z.2.val < lo → permOf (hStrip (m := m) r hr p) σ z = z) ∧
      σ.length ≤ 96 * m + 8 := by
  have hpc_ne : p ≠ c := by
    intro h; have := congrArg (fun w : Cell 2 m => w.1.val) h; omega
  by_cases hpa1 : (p.1.val + p.2.val + a.1.val + a.2.val) % 2 = 1
  · by_cases hpc1 : (p.1.val + p.2.val + c.1.val + c.2.val) % 2 = 1
    · -- Case 3: `A = C ≠ P`.  Auxiliary `v` has the colour of `p`.
      obtain ⟨v, hvcol, hvlo, hvp, _⟩ :
          ∃ v : Cell 2 m, (v.1.val + v.2.val) % 2 = (p.1.val + p.2.val) % 2
            ∧ lo ≤ v.2.val ∧ v ≠ p ∧ v ≠ J :=
        exists_strip_color_from lo ((p.1.val + p.2.val) % 2) (by omega) hlo p J
      obtain ⟨σ, hapσ, hperm, hfix, hlen⟩ :=
        hStrip_place_four_content (n := n) (m := m) r hr
          (p := p) (a := a) (v := v) (c := c)
          (by omega) (by omega) (by omega) (by omega)
          hvp.symm hpc_ne hac
      obtain ⟨hf1, hf2⟩ := fixes_of_support (S := ({p, a, v, c} : Finset (Cell 2 m)))
        hr hfix (by
          intro x hx hx1
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with h | h | h | h
          · rw [h] at hx1; omega
          · rw [h] at hx1 ⊢; exact Or.inr (hrow hx1)
          · rw [h] at hx1 ⊢; exact Or.inr (by rw [hlo_eq]; exact hvlo)
          · exact Or.inl h)
      have hf3 := fixes_of_low (lo := lo) hr hfix (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h | h | h
        · rw [h]; exact hplo
        · rw [h]; exact halo
        · rw [h]; exact hvlo
        · rw [h]; exact hclo)
      exact ⟨σ, hapσ, hperm, hf1, hf2, hf3, by omega⟩
    · -- Case 2: `A ≠ P = C`.  Auxiliary `u` has the colour opposite to `p`.
      obtain ⟨u, hucol, hulo, hua, _⟩ :
          ∃ u : Cell 2 m, (u.1.val + u.2.val) % 2 = p.2.val % 2
            ∧ lo ≤ u.2.val ∧ u ≠ a ∧ u ≠ J :=
        exists_strip_color_from lo (p.2.val % 2) (by omega) hlo a J
      obtain ⟨σ, hapσ, hperm, hfix, hlen⟩ :=
        hStrip_place_four_content_v (n := n) (m := m) r hr
          (p := p) (u := u) (c := c) (a := a)
          (by omega) (by omega) (by omega) (by omega)
          hpc_ne hua
      obtain ⟨hf1, hf2⟩ := fixes_of_support (S := ({p, u, c, a} : Finset (Cell 2 m)))
        hr hfix (by
          intro x hx hx1
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with h | h | h | h
          · rw [h] at hx1; omega
          · rw [h] at hx1 ⊢; exact Or.inr (by rw [hlo_eq]; exact hulo)
          · exact Or.inl h
          · rw [h] at hx1 ⊢; exact Or.inr (hrow hx1))
      have hf3 := fixes_of_low (lo := lo) hr hfix (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h | h | h
        · rw [h]; exact hplo
        · rw [h]; exact hulo
        · rw [h]; exact hclo
        · rw [h]; exact halo)
      exact ⟨σ, hapσ, hperm, hf1, hf2, hf3, by omega⟩
  · by_cases hpc1 : (p.1.val + p.2.val + c.1.val + c.2.val) % 2 = 1
    · -- Case 1: `A = P ≠ C`.  No auxiliary.
      obtain ⟨σ, hapσ, hperm, hfix, hlen⟩ :=
        hStrip_place_two_content (n := n) (m := m) r hr
          (p := p) (c := c) (a := a)
          hpc1 (by omega) hpa.symm hac
      obtain ⟨hf1, hf2⟩ := fixes_of_support (S := ({p, c, a} : Finset (Cell 2 m)))
        hr hfix (by
          intro x hx hx1
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with h | h | h
          · rw [h] at hx1; omega
          · exact Or.inl h
          · rw [h] at hx1 ⊢; exact Or.inr (hrow hx1))
      have hf3 := fixes_of_low (lo := lo) hr hfix (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h | h
        · rw [h]; exact hplo
        · rw [h]; exact hclo
        · rw [h]; exact halo)
      exact ⟨σ, hapσ, hperm, hf1, hf2, hf3, by omega⟩
    · -- Case 4: `A = P = C`.  Jump the blank to an opposite-coloured cell `q`.
      obtain ⟨q, hqcol, hqlo, hqa, _⟩ :
          ∃ q : Cell 2 m, (q.1.val + q.2.val) % 2 = p.2.val % 2
            ∧ lo ≤ q.2.val ∧ q ≠ a ∧ q ≠ J :=
        exists_strip_color_from lo (p.2.val % 2) (by omega) hlo a J
      have hpq_col : (p.1.val + p.2.val + q.1.val + q.2.val) % 2 = 1 := by omega
      obtain ⟨σj, hapj, hpermj, hlenj⟩ :
          ∃ σj : List Dir, ApplicableFrom (hStrip (m := m) r hr p) σj ∧
            permOf (hStrip (m := m) r hr p) σj
              = Equiv.swap (hStrip (m := m) r hr p) (hStrip (m := m) r hr q) ∧
            σj.length ≤ 12 * m + 1 := by
        obtain ⟨σj, hapj, hpermj, hlenj⟩ := strip_jump (p := p) (q := q) hpq_col
        refine ⟨σj, ?_, ?_, hlenj⟩
        · simpa using applicableFrom_map_of_neighbor_map (ι := hStrip (m := m) r hr)
            (f := id) (hStrip_neighbor r hr) hapj
        · simpa using permOf_map_eq_swap (hStrip_injective r hr) (hStrip_neighbor r hr)
            p σj hapj hpermj
      have htracej : trace (hStrip (m := m) r hr p) σj = hStrip (m := m) r hr q := by
        rw [← permOf_symm_apply, hpermj, Equiv.symm_swap, Equiv.swap_apply_left]
      obtain ⟨v, hvcol, hvlo, hvq, _⟩ :
          ∃ v : Cell 2 m, (v.1.val + v.2.val) % 2 = (q.1.val + q.2.val) % 2
            ∧ lo ≤ v.2.val ∧ v ≠ q ∧ v ≠ J :=
        exists_strip_color_from lo ((q.1.val + q.2.val) % 2) (by omega) hlo q J
      obtain ⟨σc, hapσc, hpermc, hfixc, hlenc⟩ :=
        hStrip_place_four_content (n := n) (m := m) r hr
          (p := q) (a := a) (v := v) (c := c)
          (by omega) (by omega) (by omega) (by omega)
          hvq.symm
          (by
            intro h
            have hq : (q.1.val + q.2.val) % 2 = p.2.val % 2 := hqcol
            have := congrArg (fun w : Cell 2 m => (w.1.val + w.2.val) % 2) h
            omega)
          hac
      obtain ⟨hf1, hf2⟩ := fixes_of_support (S := ({q, a, v, c} : Finset (Cell 2 m)))
        hr hfixc (by
          intro x hx hx1
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with h | h | h | h
          · rw [h] at hx1 ⊢; exact Or.inr (by rw [hlo_eq]; exact hqlo)
          · rw [h] at hx1 ⊢; exact Or.inr (hrow hx1)
          · rw [h] at hx1 ⊢; exact Or.inr (by rw [hlo_eq]; exact hvlo)
          · exact Or.inl h)
      have hf3 := fixes_of_low (lo := lo) hr hfixc (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h | h | h
        · rw [h]; exact hqlo
        · rw [h]; exact halo
        · rw [h]; exact hvlo
        · rw [h]; exact hclo)
      have hzfixj1 : ∀ {z : Cell n m}, z.1.val < r →
          permOf (hStrip (m := m) r hr p) σj z = z := by
        intro z hz
        rw [hpermj]
        exact Equiv.swap_apply_of_ne_of_ne
          (by intro h; have := congrArg (fun w : Cell n m => w.1.val) h
              simp only [hStrip, Fin.val_mk] at this; omega)
          (by intro h; have := congrArg (fun w : Cell n m => w.1.val) h
              simp only [hStrip, Fin.val_mk] at this; omega)
      have hzfixj2 : ∀ {z : Cell n m}, z.1.val = r → z.2.val < c.2.val →
          permOf (hStrip (m := m) r hr p) σj z = z := by
        intro z hzr hzc
        rw [hpermj]
        exact Equiv.swap_apply_of_ne_of_ne
          (by intro h; have := congrArg (fun w : Cell n m => w.1.val) h
              simp only [hStrip, Fin.val_mk] at this; omega)
          (by intro h
              have h2 := congrArg (fun w : Cell n m => w.2.val) h
              simp only [hStrip] at h2
              omega)
      have hzfixjlo : ∀ {z : Cell n m}, z.2.val < lo →
          permOf (hStrip (m := m) r hr p) σj z = z := by
        intro z hz
        rw [hpermj]
        exact Equiv.swap_apply_of_ne_of_ne
          (by intro h; have := congrArg (fun w : Cell n m => w.2.val) h
              simp only [hStrip] at this; omega)
          (by intro h; have := congrArg (fun w : Cell n m => w.2.val) h
              simp only [hStrip] at this; omega)
      refine ⟨σj ++ σc, ?_, ?_, ?_, ?_, ?_, by rw [List.length_append]; omega⟩
      · rw [applicableFrom_append, htracej]; exact ⟨hapj, hapσc⟩
      · rw [permOf_append, htracej, Equiv.Perm.mul_apply, hpermc, hpermj]
        exact Equiv.swap_apply_of_ne_of_ne
          (fun h => hpa (hStrip_injective r hr h).symm)
          (fun h => hqa (hStrip_injective r hr h).symm)
      · intro z hz
        rw [permOf_append, htracej, Equiv.Perm.mul_apply, hf1 z hz, hzfixj1 hz]
      · intro z hz hzc
        rw [permOf_append, htracej, Equiv.Perm.mul_apply, hf2 z hz hzc, hzfixj2 hz hzc]
      · intro z hz
        rw [permOf_append, htracej, Equiv.Perm.mul_apply, hf3 z hz, hzfixjlo hz]

/-- A cell `J` outside the support `S` of a placement is fixed. -/
lemma fixes_of_support_cell {r : ℕ} (hr : r + 1 < n) {p : Cell 2 m} {σ : List Dir}
    {S : Finset (Cell 2 m)}
    (hfix : ∀ y : Cell n m, y ∉ S.image (hStrip (m := m) r hr) →
        permOf (hStrip (m := m) r hr p) σ y = y)
    {J : Cell 2 m} (hJ : J ∉ S) :
    permOf (hStrip (m := m) r hr p) σ (hStrip r hr J) = hStrip r hr J := by
  apply hfix
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨x, hxS, hxJ⟩
  exact hJ (hStrip_injective r hr hxJ ▸ hxS)

/-- Two-row placement, blank in the upper row.  The row-swapped analogue of `stripPlace2`. -/
theorem stripPlaceFlip2 (r : ℕ) (hr : r + 1 < n) (_hm : 4 ≤ m) (lo : ℕ) (hlo : lo + 3 ≤ m)
    {p a c J : Cell 2 m} (hlo_eq : c.2.val = lo)
    (hp : p.1.val = 0) (hc : c.1.val = 1) (hpa : p ≠ a) (hac : a ≠ c)
    (hrow : a.1.val = 1 → c.2.val ≤ a.2.val)
    (hplo : lo ≤ p.2.val) (halo : lo ≤ a.2.val) (hclo : lo ≤ c.2.val)
    (hJp : J ≠ p) (hJa : J ≠ a) (hJc : J ≠ c) :
    ∃ σ : List Dir, ApplicableFrom (hStrip (m := m) r hr p) σ ∧
      permOf (hStrip (m := m) r hr p) σ (hStrip r hr c) = hStrip r hr a ∧
      (∀ z : Cell n m, z.1.val < r → permOf (hStrip (m := m) r hr p) σ z = z) ∧
      (∀ z : Cell n m, z.1.val = r + 1 → z.2.val < c.2.val →
          permOf (hStrip (m := m) r hr p) σ z = z) ∧
      (∀ z : Cell n m, z.2.val < lo → permOf (hStrip (m := m) r hr p) σ z = z) ∧
      permOf (hStrip (m := m) r hr p) σ (hStrip r hr J) = hStrip r hr J ∧
      σ.length ≤ 96 * m + 8 := by
  have hpc_ne : p ≠ c := by
    intro h; have := congrArg (fun w : Cell 2 m => w.1.val) h; omega
  by_cases hpa1 : (p.1.val + p.2.val + a.1.val + a.2.val) % 2 = 1
  · by_cases hpc1 : (p.1.val + p.2.val + c.1.val + c.2.val) % 2 = 1
    · -- Case 3: `A = C ≠ P`.
      obtain ⟨v, hvcol, hvlo, hvp, hvJ⟩ :
          ∃ v : Cell 2 m, (v.1.val + v.2.val) % 2 = (p.1.val + p.2.val) % 2
            ∧ lo ≤ v.2.val ∧ v ≠ p ∧ v ≠ J :=
        exists_strip_color_from lo ((p.1.val + p.2.val) % 2) (by omega) hlo p J
      obtain ⟨σ, hapσ, hperm, hfix, hlen⟩ :=
        hStrip_place_four_content (n := n) (m := m) r hr
          (p := p) (a := a) (v := v) (c := c)
          (by omega) (by omega) (by omega) (by omega)
          hvp.symm hpc_ne hac
      obtain ⟨hf1, hf2⟩ := fixes_of_support_low (S := ({p, a, v, c} : Finset (Cell 2 m)))
        hr hfix (by
          intro x hx hx1
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with h | h | h | h
          · rw [h] at hx1; omega
          · rw [h] at hx1 ⊢; exact Or.inr (hrow hx1)
          · rw [h] at hx1 ⊢; exact Or.inr (by rw [hlo_eq]; exact hvlo)
          · exact Or.inl h)
      have hf3 := fixes_of_low (lo := lo) hr hfix (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h | h | h
        · rw [h]; exact hplo
        · rw [h]; exact halo
        · rw [h]; exact hvlo
        · rw [h]; exact hclo)
      have hJfix := fixes_of_support_cell hr hfix (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hJp, hJa, Ne.symm hvJ, hJc⟩)
      exact ⟨σ, hapσ, hperm, hf1, hf2, hf3, hJfix, by omega⟩
    · -- Case 2: `A ≠ P = C`.
      obtain ⟨u, hucol, hulo, hua, huJ⟩ :
          ∃ u : Cell 2 m, (u.1.val + u.2.val) % 2 = (1 + p.2.val) % 2
            ∧ lo ≤ u.2.val ∧ u ≠ a ∧ u ≠ J :=
        exists_strip_color_from lo ((1 + p.2.val) % 2) (by omega) hlo a J
      obtain ⟨σ, hapσ, hperm, hfix, hlen⟩ :=
        hStrip_place_four_content_v (n := n) (m := m) r hr
          (p := p) (u := u) (c := c) (a := a)
          (by omega) (by omega) (by omega) (by omega)
          hpc_ne hua
      obtain ⟨hf1, hf2⟩ := fixes_of_support_low (S := ({p, u, c, a} : Finset (Cell 2 m)))
        hr hfix (by
          intro x hx hx1
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with h | h | h | h
          · rw [h] at hx1; omega
          · rw [h] at hx1 ⊢; exact Or.inr (by rw [hlo_eq]; exact hulo)
          · exact Or.inl h
          · rw [h] at hx1 ⊢; exact Or.inr (hrow hx1))
      have hf3 := fixes_of_low (lo := lo) hr hfix (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h | h | h
        · rw [h]; exact hplo
        · rw [h]; exact hulo
        · rw [h]; exact hclo
        · rw [h]; exact halo)
      have hJfix := fixes_of_support_cell hr hfix (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hJp, Ne.symm huJ, hJc, hJa⟩)
      exact ⟨σ, hapσ, hperm, hf1, hf2, hf3, hJfix, by omega⟩
  · by_cases hpc1 : (p.1.val + p.2.val + c.1.val + c.2.val) % 2 = 1
    · -- Case 1: `A = P ≠ C`.
      obtain ⟨σ, hapσ, hperm, hfix, hlen⟩ :=
        hStrip_place_two_content (n := n) (m := m) r hr
          (p := p) (c := c) (a := a)
          hpc1 (by omega) hpa.symm hac
      obtain ⟨hf1, hf2⟩ := fixes_of_support_low (S := ({p, c, a} : Finset (Cell 2 m)))
        hr hfix (by
          intro x hx hx1
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with h | h | h
          · rw [h] at hx1; omega
          · exact Or.inl h
          · rw [h] at hx1 ⊢; exact Or.inr (hrow hx1))
      have hf3 := fixes_of_low (lo := lo) hr hfix (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h | h
        · rw [h]; exact hplo
        · rw [h]; exact hclo
        · rw [h]; exact halo)
      have hJfix := fixes_of_support_cell hr hfix (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hJp, hJc, hJa⟩)
      exact ⟨σ, hapσ, hperm, hf1, hf2, hf3, hJfix, by omega⟩
    · -- Case 4: `A = P = C`.
      obtain ⟨q, hqcol, hqlo, hqa, hqJ⟩ :
          ∃ q : Cell 2 m, (q.1.val + q.2.val) % 2 = (1 + p.2.val) % 2
            ∧ lo ≤ q.2.val ∧ q ≠ a ∧ q ≠ J :=
        exists_strip_color_from lo ((1 + p.2.val) % 2) (by omega) hlo a J
      have hpq_col : (p.1.val + p.2.val + q.1.val + q.2.val) % 2 = 1 := by omega
      obtain ⟨σj, hapj, hpermj, hlenj⟩ :
          ∃ σj : List Dir, ApplicableFrom (hStrip (m := m) r hr p) σj ∧
            permOf (hStrip (m := m) r hr p) σj
              = Equiv.swap (hStrip (m := m) r hr p) (hStrip (m := m) r hr q) ∧
            σj.length ≤ 12 * m + 1 := by
        obtain ⟨σj, hapj, hpermj, hlenj⟩ := strip_jump (p := p) (q := q) hpq_col
        refine ⟨σj, ?_, ?_, hlenj⟩
        · simpa using applicableFrom_map_of_neighbor_map (ι := hStrip (m := m) r hr)
            (f := id) (hStrip_neighbor r hr) hapj
        · simpa using permOf_map_eq_swap (hStrip_injective r hr) (hStrip_neighbor r hr)
            p σj hapj hpermj
      have htracej : trace (hStrip (m := m) r hr p) σj = hStrip (m := m) r hr q := by
        rw [← permOf_symm_apply, hpermj, Equiv.symm_swap, Equiv.swap_apply_left]
      obtain ⟨v, hvcol, hvlo, hvq, hvJ⟩ :
          ∃ v : Cell 2 m, (v.1.val + v.2.val) % 2 = (1 + p.2.val) % 2
            ∧ lo ≤ v.2.val ∧ v ≠ q ∧ v ≠ J :=
        exists_strip_color_from lo ((1 + p.2.val) % 2) (by omega) hlo q J
      obtain ⟨σc, hapσc, hpermc, hfixc, hlenc⟩ :=
        hStrip_place_four_content (n := n) (m := m) r hr
          (p := q) (a := a) (v := v) (c := c)
          (by omega) (by omega) (by omega) (by omega)
          hvq.symm
          (by
            intro h
            have hq : (q.1.val + q.2.val) % 2 = (1 + p.2.val) % 2 := hqcol
            have := congrArg (fun w : Cell 2 m => (w.1.val + w.2.val) % 2) h
            omega)
          hac
      obtain ⟨hf1, hf2⟩ := fixes_of_support_low (S := ({q, a, v, c} : Finset (Cell 2 m)))
        hr hfixc (by
          intro x hx hx1
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with h | h | h | h
          · rw [h] at hx1 ⊢; exact Or.inr (by rw [hlo_eq]; exact hqlo)
          · rw [h] at hx1 ⊢; exact Or.inr (hrow hx1)
          · rw [h] at hx1 ⊢; exact Or.inr (by rw [hlo_eq]; exact hvlo)
          · exact Or.inl h)
      have hf3 := fixes_of_low (lo := lo) hr hfixc (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h | h | h
        · rw [h]; exact hqlo
        · rw [h]; exact halo
        · rw [h]; exact hvlo
        · rw [h]; exact hclo)
      have hzfixj1 : ∀ {z : Cell n m}, z.1.val < r →
          permOf (hStrip (m := m) r hr p) σj z = z := by
        intro z hz
        rw [hpermj]
        exact Equiv.swap_apply_of_ne_of_ne
          (by intro h; have := congrArg (fun w : Cell n m => w.1.val) h
              simp only [hStrip, Fin.val_mk] at this; omega)
          (by intro h; have := congrArg (fun w : Cell n m => w.1.val) h
              simp only [hStrip, Fin.val_mk] at this; omega)
      have hzfixj2 : ∀ {z : Cell n m}, z.1.val = r + 1 → z.2.val < c.2.val →
          permOf (hStrip (m := m) r hr p) σj z = z := by
        intro z hzr hzc
        rw [hpermj]
        exact Equiv.swap_apply_of_ne_of_ne
          (by intro h; have := congrArg (fun w : Cell n m => w.1.val) h
              simp only [hStrip, Fin.val_mk] at this; omega)
          (by intro h
              have h2 := congrArg (fun w : Cell n m => w.2.val) h
              simp only [hStrip] at h2
              omega)
      have hzfixjlo : ∀ {z : Cell n m}, z.2.val < lo →
          permOf (hStrip (m := m) r hr p) σj z = z := by
        intro z hz
        rw [hpermj]
        exact Equiv.swap_apply_of_ne_of_ne
          (by intro h; have := congrArg (fun w : Cell n m => w.2.val) h
              simp only [hStrip] at this; omega)
          (by intro h; have := congrArg (fun w : Cell n m => w.2.val) h
              simp only [hStrip] at this; omega)
      have hJfixc : permOf (hStrip (m := m) r hr q) σc (hStrip r hr J) = hStrip r hr J :=
        fixes_of_support_cell hr hfixc (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨Ne.symm hqJ, hJa, Ne.symm hvJ, hJc⟩)
      have hJfix : permOf (hStrip (m := m) r hr p) (σj ++ σc) (hStrip r hr J)
          = hStrip r hr J := by
        rw [permOf_append, htracej, Equiv.Perm.mul_apply, hJfixc, hpermj]
        exact Equiv.swap_apply_of_ne_of_ne
          (fun h => hJp (hStrip_injective r hr h))
          (fun h => hqJ (hStrip_injective r hr h).symm)
      refine ⟨σj ++ σc, ?_, ?_, ?_, ?_, ?_, ?_, by rw [List.length_append]; omega⟩
      · rw [applicableFrom_append, htracej]; exact ⟨hapj, hapσc⟩
      · rw [permOf_append, htracej, Equiv.Perm.mul_apply, hpermc, hpermj]
        exact Equiv.swap_apply_of_ne_of_ne
          (fun h => hpa (hStrip_injective r hr h).symm)
          (fun h => hqa (hStrip_injective r hr h).symm)
      · intro z hz
        rw [permOf_append, htracej, Equiv.Perm.mul_apply, hf1 z hz, hzfixj1 hz]
      · intro z hz hzc
        rw [permOf_append, htracej, Equiv.Perm.mul_apply, hf2 z hz hzc, hzfixj2 hz hzc]
      · intro z hz
        rw [permOf_append, htracej, Equiv.Perm.mul_apply, hf3 z hz, hzfixjlo hz]
      · exact hJfix

end Zhong
