/-
Copyright (c) 2026 The Zhong formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhong formalisation contributors
-/
import Zhong.Algorithm.JumpAll

/-!
# The tile-placement primitive on a `2 × m` strip

`Algorithm/JumpAll.lean` supplies the jump (Lemma 2) in every orientation of a `2 × m`
strip and packages it as `strip_jump`: whenever the blank at `p` and the target `q` lie on
opposite colours of the checkerboard there is an `O(m)`-move word realising the
transposition `swap p q`.

This file turns jumps into **tile placement**.  Given the blank at `p`, a tile currently at
`a` and a target cell `c`, we produce a word moving the tile `a` to `c`.  The four parity
cases are the ones worked out in `PLAN.md` (M7):

* `A = P ≠ C` (`strip_place_two_content`): the two-jump chain `p → c → a`;
* `A ≠ P = C` (`strip_place_four_content_v`): the four-jump chain `p → u → c → a → p`;
* `A = C ≠ P` (`strip_place_four_content`): the four-jump chain `p → a → v → c → p`;
* `A = P = C` (`strip_place_eight_content`): two four-jump chains
  `p → z → a → u₃ → p` and `p → u₁ → c → z → p`, whose composition is the `5`-cycle
  `c → a → u₃ → z → u₁ → c`.

Here `P`, `A`, `C` are the colours `(row + column) % 2` of `p`, `a`, `c`.

The point of the explicit permutation is that its **support** is exactly the named cells:
every cell outside `{p, a, c}` (resp. `{p, u, v, w}`, `{p, a, c, z, u₁, u₃}`) is fixed.
This is what lets the row-by-row assembly of Parberry's algorithm place tiles without
disturbing already-placed cells: the algorithm chooses the named cells in columns to the
right of the current frontier.

The auxiliary application lemmas `fourChain_apply_u`, `_v`, `_w`, `_p` and the support
lemmas `twoJump_fixes`, `fourChain_fixes`, `eightChain_fixes` are pure computations with
`Equiv.swap`.
-/

namespace Zhong

open Equiv

variable {m : ℕ}

/-- Cells on opposite colours are distinct. -/
theorem odd_ne {x y : Cell 2 m}
    (h : (x.1.val + x.2.val + y.1.val + y.2.val) % 2 = 1) : x ≠ y := by
  intro hxy
  subst hxy
  omega

/-! ### The four-swap chain

The product `swap p u * swap u v * swap v w * swap w p` is the three-cycle
`u → v → w → u` (fixing `p`).  We record its values on the four named cells. -/

/-- The chain product sends `u` to `v`. -/
theorem fourChain_apply_u {p u v w : Cell 2 m} (hpu : p ≠ u) (hpv : p ≠ v) (_hpw : p ≠ w)
    (huv : u ≠ v) (huw : u ≠ w) (_hvw : v ≠ w) :
    (Equiv.swap p u * Equiv.swap u v * Equiv.swap v w * Equiv.swap w p) u = v := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  rw [Equiv.swap_apply_of_ne_of_ne huw (Ne.symm hpu)]
  rw [Equiv.swap_apply_of_ne_of_ne huv huw]
  rw [Equiv.swap_apply_left]
  rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hpv) (Ne.symm huv)]

/-- The chain product sends `v` to `w`. -/
theorem fourChain_apply_v {p u v w : Cell 2 m} (_hpu : p ≠ u) (hpv : p ≠ v) (hpw : p ≠ w)
    (_huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    (Equiv.swap p u * Equiv.swap u v * Equiv.swap v w * Equiv.swap w p) v = w := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  rw [Equiv.swap_apply_of_ne_of_ne hvw (Ne.symm hpv)]
  rw [Equiv.swap_apply_left]
  rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm huw) (Ne.symm hvw)]
  rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hpw) (Ne.symm huw)]

/-- The chain product sends `w` to `u`. -/
theorem fourChain_apply_w {p u v w : Cell 2 m} (hpu : p ≠ u) (hpv : p ≠ v) (hpw : p ≠ w)
    (_huv : u ≠ v) (_huw : u ≠ w) (_hvw : v ≠ w) :
    (Equiv.swap p u * Equiv.swap u v * Equiv.swap v w * Equiv.swap w p) w = u := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  rw [Equiv.swap_apply_left]
  rw [Equiv.swap_apply_of_ne_of_ne hpv hpw]
  rw [Equiv.swap_apply_of_ne_of_ne hpu hpv]
  rw [Equiv.swap_apply_left]

/-- The chain product fixes `p`. -/
theorem fourChain_apply_p {p u v w : Cell 2 m} (_hpu : p ≠ u) (_hpv : p ≠ v) (_hpw : p ≠ w)
    (_huv : u ≠ v) (_huw : u ≠ w) (_hvw : v ≠ w) :
    (Equiv.swap p u * Equiv.swap u v * Equiv.swap v w * Equiv.swap w p) p = p := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  rw [Equiv.swap_apply_right]
  rw [Equiv.swap_apply_right]
  rw [Equiv.swap_apply_right]
  rw [Equiv.swap_apply_right]

/-! ### Support of the chains -/

/-- The two-swap chain `swap p c * swap c a` fixes every cell outside `{p, c, a}`. -/
theorem twoJump_fixes {p c a x : Cell 2 m} (hxp : x ≠ p) (hxc : x ≠ c) (hxa : x ≠ a) :
    (Equiv.swap p c * Equiv.swap c a) x = x := by
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxc hxa,
    Equiv.swap_apply_of_ne_of_ne hxp hxc]

/-- The four-swap chain fixes every cell outside `{p, u, v, w}`. -/
theorem fourChain_fixes {p u v w x : Cell 2 m}
    (hxp : x ≠ p) (hxu : x ≠ u) (hxv : x ≠ v) (hxw : x ≠ w) :
    (Equiv.swap p u * Equiv.swap u v * Equiv.swap v w * Equiv.swap w p) x = x := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  rw [Equiv.swap_apply_of_ne_of_ne hxw hxp]
  rw [Equiv.swap_apply_of_ne_of_ne hxv hxw]
  rw [Equiv.swap_apply_of_ne_of_ne hxu hxv]
  rw [Equiv.swap_apply_of_ne_of_ne hxp hxu]

/-- The eight-swap product of the `A = P = C` placement fixes every cell outside
`{p, z, a, u₃, u₁, c}`. -/
theorem eightChain_fixes {p a c z u1 u3 x : Cell 2 m}
    (hxp : x ≠ p) (hxz : x ≠ z) (hxa : x ≠ a) (hxu3 : x ≠ u3) (hxu1 : x ≠ u1)
    (hxc : x ≠ c) :
    (Equiv.swap p z * Equiv.swap z a * Equiv.swap a u3 * Equiv.swap u3 p
        * Equiv.swap p u1 * Equiv.swap u1 c * Equiv.swap c z * Equiv.swap z p) x = x := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  rw [Equiv.swap_apply_of_ne_of_ne hxz hxp]
  rw [Equiv.swap_apply_of_ne_of_ne hxc hxz]
  rw [Equiv.swap_apply_of_ne_of_ne hxu1 hxc]
  rw [Equiv.swap_apply_of_ne_of_ne hxp hxu1]
  rw [Equiv.swap_apply_of_ne_of_ne hxu3 hxp]
  rw [Equiv.swap_apply_of_ne_of_ne hxa hxu3]
  rw [Equiv.swap_apply_of_ne_of_ne hxz hxa]
  rw [Equiv.swap_apply_of_ne_of_ne hxp hxz]

/-! ### The four-jump placement (cases `A ≠ P = C` and `A = C ≠ P`) -/

/-- The four-jump chain `p → u → v → w → p` moves the content of `w` to `v`
(equivalently, the cell `v` ends up holding the content that was at `w`). -/
theorem strip_place_four_content_v {p u v w : Cell 2 m}
    (hpu : (p.1.val + p.2.val + u.1.val + u.2.val) % 2 = 1)
    (huv : (u.1.val + u.2.val + v.1.val + v.2.val) % 2 = 1)
    (hvw : (v.1.val + v.2.val + w.1.val + w.2.val) % 2 = 1)
    (hwp : (w.1.val + w.2.val + p.1.val + p.2.val) % 2 = 1)
    (hpv : p ≠ v) (hpw : p ≠ w) (huw : u ≠ w) :
    ∃ σ : List Dir, ApplicableFrom p σ ∧ permOf p σ v = w ∧ σ.length ≤ 48 * m + 4 := by
  obtain ⟨σ, hapσ, hperm, hlen⟩ := strip_place_four hpu huv hvw hwp
  refine ⟨σ, hapσ, ?_, hlen⟩
  rw [hperm, fourChain_apply_v (odd_ne hpu) hpv hpw (odd_ne huv) huw (odd_ne hvw)]

/-- The four-jump chain `p → u → v → w → p` moves the content of `v` to `u`
(equivalently, the cell `u` ends up holding the content that was at `v`). -/
theorem strip_place_four_content_u {p u v w : Cell 2 m}
    (hpu : (p.1.val + p.2.val + u.1.val + u.2.val) % 2 = 1)
    (huv : (u.1.val + u.2.val + v.1.val + v.2.val) % 2 = 1)
    (hvw : (v.1.val + v.2.val + w.1.val + w.2.val) % 2 = 1)
    (hwp : (w.1.val + w.2.val + p.1.val + p.2.val) % 2 = 1)
    (hpv : p ≠ v) (hpw : p ≠ w) (huw : u ≠ w) :
    ∃ σ : List Dir, ApplicableFrom p σ ∧ permOf p σ u = v ∧ σ.length ≤ 48 * m + 4 := by
  obtain ⟨σ, hapσ, hperm, hlen⟩ := strip_place_four hpu huv hvw hwp
  refine ⟨σ, hapσ, ?_, hlen⟩
  rw [hperm, fourChain_apply_u (odd_ne hpu) hpv hpw (odd_ne huv) huw (odd_ne hvw)]

/-! ### The eight-jump placement (case `A = P = C`) -/

/-- **Placement when the blank, the tile and the target share a colour.**  The two
four-jump chains `p → z → a → u₃ → p` and `p → u₁ → c → z → p` compose to the `5`-cycle
`c → a → u₃ → z → u₁ → c`, so the content of `a` moves to `c`.  All auxiliaries
`z, u₁, u₃` have the colour opposite to `p` (and to `a, c`). -/
theorem strip_place_eight_content {p a c z u1 u3 : Cell 2 m}
    (hpz : (p.1.val + p.2.val + z.1.val + z.2.val) % 2 = 1)
    (hza : (z.1.val + z.2.val + a.1.val + a.2.val) % 2 = 1)
    (hau3 : (a.1.val + a.2.val + u3.1.val + u3.2.val) % 2 = 1)
    (hu3p : (u3.1.val + u3.2.val + p.1.val + p.2.val) % 2 = 1)
    (hpu1 : (p.1.val + p.2.val + u1.1.val + u1.2.val) % 2 = 1)
    (hu1c : (u1.1.val + u1.2.val + c.1.val + c.2.val) % 2 = 1)
    (hcz : (c.1.val + c.2.val + z.1.val + z.2.val) % 2 = 1)
    (hzp : (z.1.val + z.2.val + p.1.val + p.2.val) % 2 = 1)
    (hpa : p ≠ a) (hpc : p ≠ c) (hzu3 : z ≠ u3) (hu1z : u1 ≠ z) :
    ∃ σ : List Dir, ApplicableFrom p σ ∧ permOf p σ c = a ∧ σ.length ≤ 96 * m + 8 := by
  obtain ⟨σo, hapo, hpermo, hleno⟩ := strip_place_four hpz hza hau3 hu3p
  obtain ⟨σi, hapi, hpermi, hleni⟩ := strip_place_four hpu1 hu1c hcz hzp
  have hfixo : permOf p σo p = p := by
    rw [hpermo, fourChain_apply_p (odd_ne hpz) hpa (odd_ne hu3p).symm (odd_ne hza) hzu3
      (odd_ne hau3)]
  have htraceo : trace p σo = p := by
    rw [← permOf_symm_apply p σo, Equiv.symm_apply_eq]
    exact hfixo.symm
  refine ⟨σo ++ σi, ?_, ?_, ?_⟩
  · rw [applicableFrom_append, htraceo]
    exact ⟨hapo, hapi⟩
  · have hinner : (Equiv.swap p u1 * Equiv.swap u1 c * Equiv.swap c z * Equiv.swap z p) c = z :=
      fourChain_apply_v (odd_ne hpu1) hpc (odd_ne hpz) (odd_ne hu1c) hu1z (odd_ne hcz)
    have houter : (Equiv.swap p z * Equiv.swap z a * Equiv.swap a u3 * Equiv.swap u3 p) z = a :=
      fourChain_apply_u (odd_ne hpz) hpa (odd_ne hu3p).symm (odd_ne hza) hzu3 (odd_ne hau3)
    rw [permOf_append_of_trace_eq p σo σi htraceo, Equiv.Perm.mul_apply,
      hpermo, hpermi, hinner, houter]
  · rw [List.length_append]
    omega

/-! ### Lifting placement to a strip of a larger board

The placement primitives above live on the abstract `2 × m` board.  The algorithm uses them
inside a two-row strip of an `n × m` board, embedded by `hStrip`.  The generic lemma
`hStrip_permOf_spec` transports an explicit strip permutation `P` (with a support bound) to
the board: it computes the effect on the named cells and shows that every board cell outside
the image of the support is fixed.  This is what lets the row assembly place tiles without
disturbing already-placed cells. -/

/-- Transport an explicit strip-level placement to a horizontal strip of a larger board. -/
theorem hStrip_permOf_spec {n m : ℕ} (r : ℕ) (hr : r + 1 < n) {p c a : Cell 2 m}
    {σ : List Dir} (happ : ApplicableFrom p σ) {P : Equiv.Perm (Cell 2 m)}
    (hP : permOf p σ = P) (hca : P c = a) {T : Finset (Cell 2 m)}
    (hT : ∀ x : Cell 2 m, x ∉ T → P x = x) :
    permOf (hStrip (m := m) r hr p) σ (hStrip r hr c) = hStrip r hr a
      ∧ (∀ y : Cell n m, y ∉ T.image (hStrip (m := m) r hr) →
          permOf (hStrip (m := m) r hr p) σ y = y) := by
  have hmap := permOf_map_apply_of_neighbor_map (ι := hStrip (m := m) r hr) (f := id)
    (hStrip_injective r hr) (hStrip_neighbor r hr) p σ happ c
  have hval : permOf (hStrip (m := m) r hr p) σ (hStrip r hr c) = hStrip r hr a := by
    simpa [hP, hca] using hmap
  refine ⟨hval, ?_⟩
  intro y hy
  by_cases hyr : y ∈ Set.range (hStrip (m := m) r hr)
  · obtain ⟨x, rfl⟩ := hyr
    have hxT : x ∉ T := fun hx => hy (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    have hx : P x = x := hT x hxT
    have hmapx := permOf_map_apply_of_neighbor_map (ι := hStrip (m := m) r hr) (f := id)
      (hStrip_injective r hr) (hStrip_neighbor r hr) p σ happ x
    simpa [hP, hx] using hmapx
  · have hfix := permOf_map_fixes_of_not_mem_range (ι := hStrip (m := m) r hr) (f := id)
      (hStrip_neighbor r hr) p σ happ hyr
    simpa using hfix

/-! ### The board-level placement primitive

These four theorems are the per-tile placement step of Parberry's algorithm, stated on a
horizontal strip of an `n × m` board.  Each returns a word whose induced board permutation
fixes every cell outside the image of the named strip cells, so it can be applied while
leaving already-placed cells untouched. -/

/-- **Board-level placement, case `A = P ≠ C`.**  On the strip at rows `r, r+1`, move the
content of `a` to `c` using the two-jump chain `p → c → a`. -/
theorem hStrip_place_two_content {n m : ℕ} (r : ℕ) (hr : r + 1 < n) {p c a : Cell 2 m}
    (hpc : (p.1.val + p.2.val + c.1.val + c.2.val) % 2 = 1)
    (hca : (c.1.val + c.2.val + a.1.val + a.2.val) % 2 = 1)
    (hap : a ≠ p) (hac : a ≠ c) :
    ∃ σ : List Dir, ApplicableFrom (hStrip (m := m) r hr p) σ
      ∧ permOf (hStrip (m := m) r hr p) σ (hStrip r hr c) = hStrip r hr a
      ∧ (∀ y : Cell n m, y ∉ ({p, c, a} : Finset (Cell 2 m)).image (hStrip (m := m) r hr) →
          permOf (hStrip (m := m) r hr p) σ y = y)
      ∧ σ.length ≤ 24 * m + 2 := by
  obtain ⟨σ, happ, hP, hlen⟩ := strip_place_two hpc hca
  have hca' : (Equiv.swap p c * Equiv.swap c a) c = a := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hap hac]
  have hT : ∀ x : Cell 2 m, x ∉ ({p, c, a} : Finset (Cell 2 m)) →
      (Equiv.swap p c * Equiv.swap c a) x = x := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact twoJump_fixes hx.1 hx.2.1 hx.2.2
  have happ' : ApplicableFrom (hStrip (m := m) r hr p) σ := by
    have := applicableFrom_map_of_neighbor_map (ι := hStrip (m := m) r hr) (f := id)
      (hStrip_neighbor r hr) happ
    simpa using this
  obtain ⟨hval, hfix⟩ := hStrip_permOf_spec r hr happ hP hca' hT
  exact ⟨σ, happ', hval, hfix, hlen⟩

/-- **Board-level placement, case `A = C ≠ P`.**  On the strip at rows `r, r+1`, move the
content of `a` to `c` using the four-jump chain `p → a → v → c → p`. -/
theorem hStrip_place_four_content {n m : ℕ} (r : ℕ) (hr : r + 1 < n) {p a v c : Cell 2 m}
    (hpa : (p.1.val + p.2.val + a.1.val + a.2.val) % 2 = 1)
    (hav : (a.1.val + a.2.val + v.1.val + v.2.val) % 2 = 1)
    (hvc : (v.1.val + v.2.val + c.1.val + c.2.val) % 2 = 1)
    (hcp : (c.1.val + c.2.val + p.1.val + p.2.val) % 2 = 1)
    (hpv : p ≠ v) (hpc : p ≠ c) (hac : a ≠ c) :
    ∃ σ : List Dir, ApplicableFrom (hStrip (m := m) r hr p) σ
      ∧ permOf (hStrip (m := m) r hr p) σ (hStrip r hr c) = hStrip r hr a
      ∧ (∀ y : Cell n m, y ∉ ({p, a, v, c} : Finset (Cell 2 m)).image (hStrip (m := m) r hr) →
          permOf (hStrip (m := m) r hr p) σ y = y)
      ∧ σ.length ≤ 48 * m + 4 := by
  obtain ⟨σ, happ, hP, hlen⟩ := strip_place_four hpa hav hvc hcp
  have hca' : (Equiv.swap p a * Equiv.swap a v * Equiv.swap v c * Equiv.swap c p) c = a :=
    fourChain_apply_w (odd_ne hpa) hpv hpc (odd_ne hav) hac (odd_ne hvc)
  have hT : ∀ x : Cell 2 m, x ∉ ({p, a, v, c} : Finset (Cell 2 m)) →
      (Equiv.swap p a * Equiv.swap a v * Equiv.swap v c * Equiv.swap c p) x = x := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact fourChain_fixes hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
  have happ' : ApplicableFrom (hStrip (m := m) r hr p) σ := by
    have := applicableFrom_map_of_neighbor_map (ι := hStrip (m := m) r hr) (f := id)
      (hStrip_neighbor r hr) happ
    simpa using this
  obtain ⟨hval, hfix⟩ := hStrip_permOf_spec r hr happ hP hca' hT
  exact ⟨σ, happ', hval, hfix, hlen⟩

/-- **The clean content exchange of the `A = C ≠ P` placement.**  The same word as
`hStrip_place_four_content`, but exposing the full three-cycle `a → v → c → a`: the content of
the tile cell `a` moves to the target `c`, the content of `c` is dumped into the workspace cell
`v`, and the content of `v` moves to `a`.  When `a` and `v` are don't-care cells, this places a
tile into the `H` row while moving the displaced content out of the row and into the workspace. -/
theorem hStrip_place_four_exchange {n m : ℕ} (r : ℕ) (hr : r + 1 < n) {p a v c : Cell 2 m}
    (hpa : (p.1.val + p.2.val + a.1.val + a.2.val) % 2 = 1)
    (hav : (a.1.val + a.2.val + v.1.val + v.2.val) % 2 = 1)
    (hvc : (v.1.val + v.2.val + c.1.val + c.2.val) % 2 = 1)
    (hcp : (c.1.val + c.2.val + p.1.val + p.2.val) % 2 = 1)
    (hpv : p ≠ v) (hpc : p ≠ c) (hac : a ≠ c) :
    ∃ σ : List Dir, ApplicableFrom (hStrip (m := m) r hr p) σ
      ∧ permOf (hStrip (m := m) r hr p) σ (hStrip r hr c) = hStrip r hr a
      ∧ permOf (hStrip (m := m) r hr p) σ (hStrip r hr a) = hStrip r hr v
      ∧ permOf (hStrip (m := m) r hr p) σ (hStrip r hr v) = hStrip r hr c
      ∧ (∀ y : Cell n m, y ∉ ({p, a, v, c} : Finset (Cell 2 m)).image (hStrip (m := m) r hr) →
          permOf (hStrip (m := m) r hr p) σ y = y)
      ∧ σ.length ≤ 48 * m + 4 := by
  obtain ⟨σ, happ, hP, hlen⟩ := strip_place_four hpa hav hvc hcp
  have hca' : (Equiv.swap p a * Equiv.swap a v * Equiv.swap v c * Equiv.swap c p) c = a :=
    fourChain_apply_w (odd_ne hpa) hpv hpc (odd_ne hav) hac (odd_ne hvc)
  have ha' : (Equiv.swap p a * Equiv.swap a v * Equiv.swap v c * Equiv.swap c p) a = v :=
    fourChain_apply_u (odd_ne hpa) hpv hpc (odd_ne hav) hac (odd_ne hvc)
  have hv' : (Equiv.swap p a * Equiv.swap a v * Equiv.swap v c * Equiv.swap c p) v = c :=
    fourChain_apply_v (odd_ne hpa) hpv hpc (odd_ne hav) hac (odd_ne hvc)
  have hT : ∀ x : Cell 2 m, x ∉ ({p, a, v, c} : Finset (Cell 2 m)) →
      (Equiv.swap p a * Equiv.swap a v * Equiv.swap v c * Equiv.swap c p) x = x := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact fourChain_fixes hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
  have happ' : ApplicableFrom (hStrip (m := m) r hr p) σ := by
    have := applicableFrom_map_of_neighbor_map (ι := hStrip (m := m) r hr) (f := id)
      (hStrip_neighbor r hr) happ
    simpa using this
  obtain ⟨hvalc, hfix⟩ := hStrip_permOf_spec r hr happ hP hca' hT
  have hvala : permOf (hStrip (m := m) r hr p) σ (hStrip r hr a) = hStrip r hr v := by
    have hmap := permOf_map_apply_of_neighbor_map (ι := hStrip (m := m) r hr) (f := id)
      (hStrip_injective r hr) (hStrip_neighbor r hr) p σ happ a
    simpa [hP, ha'] using hmap
  have hvalv : permOf (hStrip (m := m) r hr p) σ (hStrip r hr v) = hStrip r hr c := by
    have hmap := permOf_map_apply_of_neighbor_map (ι := hStrip (m := m) r hr) (f := id)
      (hStrip_injective r hr) (hStrip_neighbor r hr) p σ happ v
    simpa [hP, hv'] using hmap
  exact ⟨σ, happ', hvalc, hvala, hvalv, hfix, hlen⟩

/-- **Board-level placement, case `A ≠ P = C`.**  On the strip at rows `r, r+1`, move the
content of `a` to `c` using the four-jump chain `p → u → c → a → p`. -/
theorem hStrip_place_four_content_v {n m : ℕ} (r : ℕ) (hr : r + 1 < n) {p u c a : Cell 2 m}
    (hpu : (p.1.val + p.2.val + u.1.val + u.2.val) % 2 = 1)
    (huc : (u.1.val + u.2.val + c.1.val + c.2.val) % 2 = 1)
    (hca : (c.1.val + c.2.val + a.1.val + a.2.val) % 2 = 1)
    (hap : (a.1.val + a.2.val + p.1.val + p.2.val) % 2 = 1)
    (hpc : p ≠ c) (hua : u ≠ a) :
    ∃ σ : List Dir, ApplicableFrom (hStrip (m := m) r hr p) σ
      ∧ permOf (hStrip (m := m) r hr p) σ (hStrip r hr c) = hStrip r hr a
      ∧ (∀ y : Cell n m, y ∉ ({p, u, c, a} : Finset (Cell 2 m)).image (hStrip (m := m) r hr) →
          permOf (hStrip (m := m) r hr p) σ y = y)
      ∧ σ.length ≤ 48 * m + 4 := by
  obtain ⟨σ, happ, hP, hlen⟩ := strip_place_four hpu huc hca hap
  have hca' : (Equiv.swap p u * Equiv.swap u c * Equiv.swap c a * Equiv.swap a p) c = a :=
    fourChain_apply_v (odd_ne hpu) hpc (odd_ne hap).symm (odd_ne huc) hua (odd_ne hca)
  have hT : ∀ x : Cell 2 m, x ∉ ({p, u, c, a} : Finset (Cell 2 m)) →
      (Equiv.swap p u * Equiv.swap u c * Equiv.swap c a * Equiv.swap a p) x = x := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact fourChain_fixes hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
  have happ' : ApplicableFrom (hStrip (m := m) r hr p) σ := by
    have := applicableFrom_map_of_neighbor_map (ι := hStrip (m := m) r hr) (f := id)
      (hStrip_neighbor r hr) happ
    simpa using this
  obtain ⟨hval, hfix⟩ := hStrip_permOf_spec r hr happ hP hca' hT
  exact ⟨σ, happ', hval, hfix, hlen⟩

/-- **Board-level placement, case `A = P = C`.**  On the strip at rows `r, r+1`, move the
content of `a` to `c` using the two four-jump chains `p → z → a → u₃ → p` and
`p → u₁ → c → z → p`. -/
theorem hStrip_place_eight_content {n m : ℕ} (r : ℕ) (hr : r + 1 < n) {p a c z u1 u3 : Cell 2 m}
    (hpz : (p.1.val + p.2.val + z.1.val + z.2.val) % 2 = 1)
    (hza : (z.1.val + z.2.val + a.1.val + a.2.val) % 2 = 1)
    (hau3 : (a.1.val + a.2.val + u3.1.val + u3.2.val) % 2 = 1)
    (hu3p : (u3.1.val + u3.2.val + p.1.val + p.2.val) % 2 = 1)
    (hpu1 : (p.1.val + p.2.val + u1.1.val + u1.2.val) % 2 = 1)
    (hu1c : (u1.1.val + u1.2.val + c.1.val + c.2.val) % 2 = 1)
    (hcz : (c.1.val + c.2.val + z.1.val + z.2.val) % 2 = 1)
    (hzp : (z.1.val + z.2.val + p.1.val + p.2.val) % 2 = 1)
    (hpa : p ≠ a) (hpc : p ≠ c) (hzu3 : z ≠ u3) (hu1z : u1 ≠ z) :
    ∃ σ : List Dir, ApplicableFrom (hStrip (m := m) r hr p) σ
      ∧ permOf (hStrip (m := m) r hr p) σ (hStrip r hr c) = hStrip r hr a
      ∧ (∀ y : Cell n m,
          y ∉ ({p, a, c, z, u1, u3} : Finset (Cell 2 m)).image (hStrip (m := m) r hr) →
          permOf (hStrip (m := m) r hr p) σ y = y)
      ∧ σ.length ≤ 96 * m + 8 := by
  obtain ⟨σo, hapo, hpermo, hleno⟩ := strip_place_four hpz hza hau3 hu3p
  obtain ⟨σi, hapi, hpermi, hleni⟩ := strip_place_four hpu1 hu1c hcz hzp
  have hfixo : permOf p σo p = p := by
    rw [hpermo, fourChain_apply_p (odd_ne hpz) hpa (odd_ne hu3p).symm (odd_ne hza) hzu3
      (odd_ne hau3)]
  have htraceo : trace p σo = p := by
    rw [← permOf_symm_apply p σo, Equiv.symm_apply_eq]
    exact hfixo.symm
  have happ : ApplicableFrom p (σo ++ σi) := by
    rw [applicableFrom_append, htraceo]
    exact ⟨hapo, hapi⟩
  have hP : permOf p (σo ++ σi)
      = (Equiv.swap p z * Equiv.swap z a * Equiv.swap a u3 * Equiv.swap u3 p)
        * (Equiv.swap p u1 * Equiv.swap u1 c * Equiv.swap c z * Equiv.swap z p) := by
    rw [permOf_append_of_trace_eq p σo σi htraceo, hpermo, hpermi]
  have hca' : ((Equiv.swap p z * Equiv.swap z a * Equiv.swap a u3 * Equiv.swap u3 p)
        * (Equiv.swap p u1 * Equiv.swap u1 c * Equiv.swap c z * Equiv.swap z p)) c = a := by
    rw [Equiv.Perm.mul_apply]
    rw [fourChain_apply_v (odd_ne hpu1) hpc (odd_ne hpz) (odd_ne hu1c) hu1z (odd_ne hcz),
      fourChain_apply_u (odd_ne hpz) hpa (odd_ne hu3p).symm (odd_ne hza) hzu3 (odd_ne hau3)]
  have hT : ∀ x : Cell 2 m, x ∉ ({p, a, c, z, u1, u3} : Finset (Cell 2 m)) →
      ((Equiv.swap p z * Equiv.swap z a * Equiv.swap a u3 * Equiv.swap u3 p)
        * (Equiv.swap p u1 * Equiv.swap u1 c * Equiv.swap c z * Equiv.swap z p)) x = x := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    obtain ⟨hxp, hxa, hxc, hxz, hxu1, hxu3⟩ := hx
    rw [Equiv.Perm.mul_apply, fourChain_fixes hxp hxu1 hxc hxz,
      fourChain_fixes hxp hxz hxa hxu3]
  have happ' : ApplicableFrom (hStrip (m := m) r hr p) (σo ++ σi) := by
    have := applicableFrom_map_of_neighbor_map (ι := hStrip (m := m) r hr) (f := id)
      (hStrip_neighbor r hr) happ
    simpa using this
  obtain ⟨hval, hfix⟩ := hStrip_permOf_spec r hr happ hP hca' hT
  exact ⟨σo ++ σi, happ', hval, hfix, by rw [List.length_append]; omega⟩

end Zhong
