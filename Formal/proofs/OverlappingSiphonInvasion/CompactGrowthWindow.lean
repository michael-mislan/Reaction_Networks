import proofs.OverlappingSiphonInvasion.UniformBlockGrowth

noncomputable section
open Set
namespace OverlappingSiphonInvasion

/-- Compactness changes point-dependent positive accumulated-growth times into
a single positive window for every state. The cocycle is explicit; no uniform
growth, persistence or invariant-measure premise is smuggled into the input. -/
theorem compact_positive_growth_window {E : Type*} [TopologicalSpace E] [CompactSpace E]
    (f : E → E) (A : ℕ → E → ℝ)
    (hA : ∀ n, Continuous (A n)) (hzero : ∀ x, A 0 x = 0)
    (hcocycle : ∀ n m x, A (n+m) x = A n x+A m (f^[n] x))
    (hpoint : ∀ x, ∃ n : ℕ, 1 < A (n+1) x) :
    ∃ n : ℕ, 0 < n ∧ ∀ x, 1 < A n x := by
  classical
  let U : ℕ → Set E := fun n => {x | 1 < A (n+1) x}
  have hU : ∀ n, IsOpen (U n) := fun n => isOpen_lt continuous_const (hA (n+1))
  have hcover : (univ : Set E) ⊆ ⋃ n, U n := by
    intro x _
    obtain ⟨n,hn⟩ := hpoint x
    exact mem_iUnion.2 ⟨n,hn⟩
  obtain ⟨J,hJ⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  let N := J.sup Nat.succ+1
  have hN : 0 < N := Nat.succ_pos _
  have hblocks : ∀ x, ∃ j : ℕ, 0 < j ∧ j ≤ N ∧ 1 ≤ A j x := by
    intro x
    obtain ⟨j,hj⟩ := mem_iUnion.1 (hJ (mem_univ x))
    obtain ⟨hjJ,hjx⟩ := mem_iUnion.1 hj
    refine ⟨j+1,Nat.succ_pos j,?_,hjx.le⟩
    have hh : j+1 ≤ J.sup Nat.succ := Finset.le_sup hjJ
    exact hh.trans (Nat.le_succ _)
  obtain ⟨b,hb⟩ := isCompact_univ.bddBelow_image (hA 1).continuousOn
  let M := max 0 (-b)
  have hM : 0 ≤ M := le_max_left _ _
  have hlower : ∀ x, -M ≤ A 1 x := by
    intro x
    have hh := hb (mem_image_of_mem (A 1) (mem_univ x))
    have hm := le_max_right (0:ℝ) (-b)
    dsimp [M]
    linarith only [hh,hm]
  have hlinear : ∀ (n : ℕ) (x : E), (n:ℝ)/N-((N:ℝ)*M+1) ≤ A n x := by
    intro n x
    have hs : ∀ t, -M ≤ A (t+1) x-A t x := by
      intro t
      rw [hcocycle]
      linarith only [hlower (f^[t] x)]
    have hg : ∀ t, ∃ j : ℕ, 0 < j ∧ j ≤ N ∧ 1 ≤ A (t+j) x-A t x := by
      intro t
      obtain ⟨j,hj,hjN,hgain⟩ := hblocks (f^[t] x)
      refine ⟨j,hj,hjN,?_⟩
      rw [hcocycle]
      linarith only [hgain]
    simpa only [Nat.zero_add,hzero,sub_zero] using
      bounded_blocks_linear_growth (fun n => A n x) M N hM hN hs hg n 0
  have hNR : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  obtain ⟨n,hn⟩ := exists_nat_gt ((N:ℝ)*((N:ℝ)*M+2))
  have hn0 : 0 < n := by
    have hp : 0 < (N:ℝ)*((N:ℝ)*M+2) := by positivity
    exact Nat.cast_pos.mp (hp.trans hn)
  refine ⟨n,hn0,?_⟩
  intro x
  have hh := hlinear n x
  have hdiv : (N:ℝ)*M+2 < (n:ℝ)/N :=
    (lt_div_iff₀ hNR).mpr (by nlinarith only [hn])
  linarith only [hh,hdiv]

end OverlappingSiphonInvasion
