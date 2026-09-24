import SlidingPuzzle.Moves.ThreeCycle

/-! Exchanges of tile sets, including the parity correction for odd set sizes. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

/-- Two disjoint swaps preserve parity and can be performed with two three-cycles. -/
theorem exists_double_swap (B : Board n) (hn : 4 ≤ n)
    (a b c d : Cell n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : B a ≠ 0) (hb : B b ≠ 0) (hc : B c ≠ 0) (hd : B d ≠ 0) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 6044*n ∧ blank C = blank B ∧
      C a = B c ∧ C b = B d ∧ C c = B a ∧ C d = B b ∧
      ∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d → C x = B x := by
  obtain ⟨D,p,hp,hbD,hDa,hDb,hDc,hfixD⟩ :=
    exists_three_cycle B hn a b c hab hac hbc ha hb hc
  have hDd : D d = B d := hfixD d had.symm hbd.symm hcd.symm
  obtain ⟨C,q,hq,hbC,hCa,hCb,hCd,hfixC⟩ := exists_three_cycle D hn a b d
    hab had hbd (by rwa [hDa]) (by rwa [hDb]) (by rwa [hDd])
  refine ⟨C,p.append q,?_,hbC.trans hbD,hCa.trans hDb,hCb.trans hDd,?_,
    hCd.trans hDa,?_⟩
  · rw [Path.length_append]; omega
  · exact (hfixC c hac.symm hbc.symm hcd).trans hDc
  · intro x hxa hxb hxc hxd
    rw [hfixC x hxa hxb hxd,hfixD x hxa hxb hxc]

end SlidingPuzzle
