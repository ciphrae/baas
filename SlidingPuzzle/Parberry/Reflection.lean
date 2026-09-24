import SlidingPuzzle.Parberry.Wide

/-! Reflection of transport confined below the protected row. -/
namespace SlidingPuzzle.Parberry
open Zhong
variable {n m : ℕ}
local notation "c(" a "," b ")" => ((⟨a, by omega⟩ : Fin n), (⟨b, by omega⟩ : Fin m))

theorem reflectedWord_spec (σ : List Dir) (p q t s : Zhong.Cell n m) (r : ℕ)
    (happ : ApplicableFrom p σ) (ht : trace p σ=q) (hp : permOf p σ t=s)
    (hfix : ∀ z : Zhong.Cell n m, z.1.val<r → permOf p σ z=z) :
    ApplicableFrom (colRefl n m p) (σ.map reflDir) ∧
    trace (colRefl n m p) (σ.map reflDir)=colRefl n m q ∧
    permOf (colRefl n m p) (σ.map reflDir) (colRefl n m t)=colRefl n m s ∧
    ∀ z : Zhong.Cell n m, z.1.val<r → permOf (colRefl n m p) (σ.map reflDir) z=z := by
  have hstep : ∀ (c : Zhong.Cell n m) δ c', neighbor? c δ=some c' →
      neighbor? (colRefl n m c) (reflDir δ)=some (colRefl n m c') := by
    intro c δ c' h
    rw [neighbor?_colRefl,h,Option.map_some]
  refine ⟨applicableFrom_map_of_neighbor_map hstep happ,?_,?_,?_⟩
  · exact (trace_map_of_neighbor_map hstep _ _ happ).trans (congrArg (colRefl n m) ht)
  · exact (permOf_map_apply_of_neighbor_map (colRefl n m).injective hstep _ _ happ _).trans
      (congrArg (colRefl n m) hp)
  · intro z hz
    have h := permOf_map_apply_of_neighbor_map (colRefl n m).injective hstep _ _ happ (colRefl n m z)
    rw [hfix (colRefl n m z) (by simpa using hz)] at h
    simpa using h

/-- Northeast transport ending with the blank immediately left of the tile. -/
def eastTransportWord (m a c d v : ℕ) : List Dir :=
  (transportWord a (m-1-c) d v).map reflDir

@[simp] theorem eastTransportWord_length (m a c d v : ℕ) :
    (eastTransportWord m a c d v).length=6*d+5*v+3 := by
  simp [eastTransportWord]

theorem eastTransportWord_spec (a c d v : ℕ) (ha : a+v+d+1 < n)
    (hc : c < m) (hd : d ≤ c) (hc0 : 0 < c) :
    ApplicableFrom c(a+v+d,c-d) (eastTransportWord m a c d v) ∧
    trace c(a+v+d,c-d) (eastTransportWord m a c d v)=c(a,c-1) ∧
    permOf c(a+v+d,c-d) (eastTransportWord m a c d v) c(a,c)=c(a+v+d+1,c-d) ∧
    ∀ z : Zhong.Cell n m, z.1.val<a →
      permOf c(a+v+d,c-d) (eastTransportWord m a c d v) z=z := by
  obtain ⟨happ,ht,hp,hfix⟩ := transportWord_spec (n := n) (m := m)
    a (m-1-c) d v ha (by omega) (by omega)
  have hh := reflectedWord_spec _ _ _ _ _ a happ ht hp (fun z hz => hfix z (Or.inl hz))
  have hstart : colRefl n m c(a+v+d,m-1-c+d)=c(a+v+d,c-d) := by
    simp only [colRefl_apply]
    apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_rev]; omega
  have hend : colRefl n m c(a,m-1-c+1)=c(a,c-1) := by
    simp only [colRefl_apply]
    apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_rev]; omega
  have htarget : colRefl n m c(a,m-1-c)=c(a,c) := by
    simp only [colRefl_apply]
    apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_rev]; omega
  have hsource : colRefl n m c(a+v+d+1,m-1-c+d)=c(a+v+d+1,c-d) := by
    simp only [colRefl_apply]
    apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_rev]; omega
  simpa only [eastTransportWord,hstart,hend,htarget,hsource] using hh

/-- Predominantly horizontal northeast transport, ending below the tile. -/
def eastHorizontalWord (m a c d v : ℕ) : List Dir :=
  (horizontalWord a (m-1-c) d v).map reflDir

@[simp] theorem eastHorizontalWord_length (m a c d v : ℕ) :
    (eastHorizontalWord m a c d v).length=6*d+5*v+3 := by
  simp [eastHorizontalWord]

theorem eastHorizontalWord_spec (a c d v : ℕ) (ha : a+d < n)
    (ha1 : a+1 < n) (hc : c < m) (hd : v+d+1 ≤ c) :
    ApplicableFrom c(a+d,c-v-d) (eastHorizontalWord m a c d v) ∧
    trace c(a+d,c-v-d) (eastHorizontalWord m a c d v)=c(a+1,c) ∧
    permOf c(a+d,c-v-d) (eastHorizontalWord m a c d v) c(a,c)=c(a+d,c-v-d-1) ∧
    ∀ z : Zhong.Cell n m, z.1.val<a →
      permOf c(a+d,c-v-d) (eastHorizontalWord m a c d v) z=z := by
  obtain ⟨happ,ht,hp,hfix⟩ := horizontalWord_spec (n := n) (m := m)
    a (m-1-c) d v ha ha1 (by omega)
  have hh := reflectedWord_spec _ _ _ _ _ a happ ht hp (fun z hz => hfix z (Or.inl hz))
  have hstart : colRefl n m c(a+d,m-1-c+v+d)=c(a+d,c-v-d) := by
    simp only [colRefl_apply]
    apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_rev]; omega
  have hend : colRefl n m c(a+1,m-1-c)=c(a+1,c) := by
    simp only [colRefl_apply]
    apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_rev]; omega
  have htarget : colRefl n m c(a,m-1-c)=c(a,c) := by
    simp only [colRefl_apply]
    apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_rev]; omega
  have hsource : colRefl n m c(a+d,m-1-c+v+d+1)=c(a+d,c-v-d-1) := by
    simp only [colRefl_apply]
    apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_rev]; omega
  simpa only [eastHorizontalWord,hstart,hend,htarget,hsource] using hh

/-- Northeast diagonal travel, with a row-only preservation statement. -/
theorem eastDiagonalRun_spec (d a c : ℕ) (ha : a+d+1 < n)
    (hc : c < m) (hd : d ≤ c) :
    ApplicableFrom c(a+d,c-d) ((diagonalRun d).map reflDir) ∧
    trace c(a+d,c-d) ((diagonalRun d).map reflDir)=c(a,c) ∧
    permOf c(a+d,c-d) ((diagonalRun d).map reflDir) c(a+1,c)=c(a+d+1,c-d) ∧
    ∀ z : Zhong.Cell n m, z.1.val<a →
      permOf c(a+d,c-d) ((diagonalRun d).map reflDir) z=z := by
  obtain ⟨happ,ht,hp,hs⟩ := diagonalRun_spec (n := n) (m := m)
    d a (m-1-c) ha (by omega)
  have hfix : ∀ z : Zhong.Cell n m, z.1.val<a →
      permOf c(a+d,m-1-c+d) (diagonalRun d) z=z := by
    intro z hz
    apply permOf_apply_of_not_mem_traceSet
    intro hmem
    have hh := hs z hmem
    omega
  have hh := reflectedWord_spec _ _ _ _ _ a happ ht hp hfix
  have hstart : colRefl n m c(a+d,m-1-c+d)=c(a+d,c-d) := by
    simp only [colRefl_apply]
    apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_rev]; omega
  have hend : colRefl n m c(a,m-1-c)=c(a,c) := by
    simp only [colRefl_apply]
    apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_rev]; omega
  have htarget : colRefl n m c(a+1,m-1-c)=c(a+1,c) := by
    simp only [colRefl_apply]
    apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_rev]; omega
  have hsource : colRefl n m c(a+d+1,m-1-c+d)=c(a+d+1,c-d) := by
    simp only [colRefl_apply]
    apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_rev]; omega
  simpa only [hstart,hend,htarget,hsource] using hh

end SlidingPuzzle.Parberry
