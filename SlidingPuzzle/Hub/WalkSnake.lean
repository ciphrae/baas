import SlidingPuzzle.Hub.Basic

/-! # The snake order of the squares

Band `b` is traversed left to right if `b` is even and right to left otherwise,
so that consecutive squares in snake order are adjacent and the square distance
is at most the difference of snake indices. -/
namespace SlidingPuzzle.Hub

variable {k : ℕ}

/-- Position of `c` within band `b` in the snake order. -/
def snakePos (k b c : ℕ) : ℕ := if b % 2 = 0 then c else k - 1 - c

/-- Snake index of a square. -/
def snake (Q : Sq k) : ℕ := Q.1.val * k + snakePos k Q.1.val Q.2.val

lemma snakePos_lt {b c : ℕ} (hc : c < k) : snakePos k b c < k := by
  unfold snakePos; split_ifs <;> omega

lemma snakePos_snakePos {b c : ℕ} (hc : c < k) : snakePos k b (snakePos k b c) = c := by
  unfold snakePos; split_ifs <;> omega

lemma snake_lt (Q : Sq k) : snake Q < k * k := by
  have h1 := Q.1.isLt
  have h2 := snakePos_lt (k := k) (b := Q.1.val) Q.2.isLt
  unfold snake
  calc Q.1.val * k + snakePos k Q.1.val Q.2.val < Q.1.val * k + k := by omega
    _ = (Q.1.val + 1) * k := by ring
    _ ≤ k * k := Nat.mul_le_mul_right _ h1

/-- The square with a given snake index. -/
def snakeSq (m : Fin (k * k)) : Sq k :=
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · have := m.isLt; simp [h] at this
    · exact h
  (⟨m.val / k, by rw [Nat.div_lt_iff_lt_mul hk]; exact m.isLt⟩,
    ⟨snakePos k (m.val / k) (m.val % k), snakePos_lt (Nat.mod_lt _ hk)⟩)

lemma snake_snakeSq (m : Fin (k * k)) : snake (snakeSq m) = m.val := by
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · have := m.isLt; simp [h] at this
    · exact h
  simp only [snake, snakeSq]
  rw [snakePos_snakePos (Nat.mod_lt _ hk), mul_comm]
  exact Nat.div_add_mod _ _

lemma snakeSq_snake (Q : Sq k) : snakeSq ⟨snake Q, snake_lt Q⟩ = Q := by
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) Q.1.isLt
  have hp := snakePos_lt (k := k) (b := Q.1.val) Q.2.isLt
  have hdiv : snake Q / k = Q.1.val := by
    unfold snake
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hp, zero_add]
  have hmod : snake Q % k = snakePos k Q.1.val Q.2.val := by
    unfold snake
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp]
  ext
  · simp [snakeSq, hdiv]
  · simp only [snakeSq, hdiv, hmod]
    exact snakePos_snakePos Q.2.isLt

lemma snake_injective : Function.Injective (snake (k := k)) := by
  intro P Q h
  rw [← snakeSq_snake P, ← snakeSq_snake Q]
  congr 1
  exact Fin.ext h

lemma dist_le_snake_aux (b1 b2 c1 c2 : ℕ) (hc1 : c1 < k) (hc2 : c2 < k)
    (h : b1 * k + snakePos k b1 c1 ≤ b2 * k + snakePos k b2 c2) :
    Nat.dist b1 b2 + Nat.dist c1 c2 ≤ b2 * k + snakePos k b2 c2 - (b1 * k + snakePos k b1 c1) := by
  have hp1 := snakePos_lt (k := k) (b := b1) hc1
  have hp2 := snakePos_lt (k := k) (b := b2) hc2
  unfold Nat.dist
  rcases lt_trichotomy b1 b2 with hb | hb | hb
  · obtain ⟨e, rfl⟩ : ∃ e, b2 = b1 + 1 + e := ⟨b2 - b1 - 1, by omega⟩
    have hmul : (b1 + 1 + e) * k = b1 * k + k + e * k := by ring
    rw [hmul] at h ⊢
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he
      simp only [add_zero, zero_mul] at h ⊢
      generalize b1 * k = X at h ⊢
      unfold snakePos at h ⊢
      rcases Nat.mod_two_eq_zero_or_one b1 with hpar | hpar
      · have : (b1 + 1) % 2 = 1 := by omega
        simp only [hpar, this] at h ⊢
        simp at h ⊢
        omega
      · have : (b1 + 1) % 2 = 0 := by omega
        simp only [hpar, this] at h ⊢
        simp at h ⊢
        omega
    · have hek : e + k ≤ e * k + 1 := by
        obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        nlinarith
      generalize b1 * k = X at h ⊢
      generalize e * k = Y at h hek ⊢
      omega
  · subst hb
    unfold snakePos at h ⊢
    split_ifs at h ⊢ <;> omega
  · exfalso
    obtain ⟨e, rfl⟩ : ∃ e, b1 = b2 + 1 + e := ⟨b1 - b2 - 1, by omega⟩
    have hmul : (b2 + 1 + e) * k = b2 * k + k + e * k := by ring
    rw [hmul] at h
    omega

/-- Distance is bounded by the snake difference. -/
lemma sqDist_le_snake {P Q : Sq k} (h : snake P ≤ snake Q) :
    sqDist P Q ≤ snake Q - snake P :=
  dist_le_snake_aux _ _ _ _ P.2.isLt Q.2.isLt h

lemma sqDist_le_two (P Q : Sq k) : sqDist P Q + 2 ≤ 2 * k := by
  have h1 := P.1.isLt; have h2 := Q.1.isLt; have h3 := P.2.isLt; have h4 := Q.2.isLt
  unfold sqDist Nat.dist
  omega

/-- The squares in snake order. -/
def snakeList (k : ℕ) : List (Sq k) := (List.finRange (k * k)).map snakeSq

lemma mem_snakeList (Q : Sq k) : Q ∈ snakeList k := by
  unfold snakeList
  rw [List.mem_map]
  exact ⟨⟨snake Q, snake_lt Q⟩, List.mem_finRange _, snakeSq_snake Q⟩

lemma length_snakeList : (snakeList k).length = k * k := by
  simp [snakeList]

lemma snakeList_pairwise : (snakeList k).Pairwise (fun P Q => snake P < snake Q) := by
  unfold snakeList
  rw [List.pairwise_map]
  refine List.Pairwise.imp ?_ (List.pairwise_lt_finRange (k * k))
  intro a b hab
  rw [snake_snakeSq, snake_snakeSq]
  exact hab

end SlidingPuzzle.Hub
