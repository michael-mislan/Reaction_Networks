import proofs.RAF1519.Refinement.PositivePartCalculus

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators

/-- A graph barrier for continuous paths with right derivatives. The derivative
    condition is needed only where a coordinate violates the barrier. -/
theorem graph_right_barrier {ι : Type*} [Fintype ι] (k : ι → ι → ℝ)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j = k j i)
    (w v : ℝ → ι → ℝ) (T : ℝ)
    (hc : ∀ i, ContinuousOn (fun t => w t i) (Set.Icc 0 T))
    (hd : ∀ t ∈ Set.Ico 0 T, ∀ i, HasDerivWithinAt (fun u => w u i) (v t i) (Set.Ici t) t)
    (h0 : ∀ i, w 0 i ≤ 0)
    (hb : ∀ t ∈ Set.Ico 0 T, ∀ i, 0 < w t i → v t i ≤ ∑ j, k i j*(w t j-w t i)) :
    ∀ t ∈ Set.Icc 0 T, ∀ i, w t i ≤ 0 := by
  let E : ℝ → ℝ := fun t => ∑ i, (max 0 (w t i))^2
  let D : ℝ → ℝ := fun t => ∑ i, 2*max 0 (w t i)*v t i
  have hE : ContinuousOn E (Set.Icc 0 T) := by
    apply continuousOn_finsetSum
    intro i _
    have hp : Continuous (fun x : ℝ => (max 0 x)^2) :=
      continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_positive_square x).continuousAt)
    exact hp.comp_continuousOn (hc i)
  have hD : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt E (D t) (Set.Ici t) t := by
    intro t ht
    exact HasDerivWithinAt.fun_sum (fun i _ => hasDerivWithinAt_positive_square _ _ _ _ (hd t ht i))
  have hDle : ∀ t ∈ Set.Ico 0 T, D t ≤ 0 := by
    intro t ht
    have hh : D t ≤ 2*(∑ i, max 0 (w t i)*(∑ j, k i j*(w t j-w t i))) := by
      dsimp [D]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : 0 < w t i
      · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb t ht i hi)
          (show 0 ≤ 2*max 0 (w t i) by positivity)
      · simp only [max_eq_left (le_of_not_gt hi),mul_zero,zero_mul,le_refl]
    exact hh.trans (graph_positive_part_dissipation k hk hsym (w t))
  have hE0 : E 0 ≤ 0 := by
    dsimp [E]
    simp only [max_eq_left (h0 _),zero_pow (by decide : (2:ℕ) ≠ 0),Finset.sum_const_zero,le_refl]
  have hbound : ∀ t ∈ Set.Icc 0 T, E t ≤ 0 :=
    fun t ht => image_le_of_deriv_right_le_deriv_boundary hE hD hE0 continuousOn_const
      (fun t _ => (hasDerivAt_const t (0:ℝ)).hasDerivWithinAt) hDle ht
  intro t ht i
  have hs : (max 0 (w t i))^2 ≤ E t := Finset.single_le_sum
    (fun j _ => sq_nonneg (max 0 (w t j))) (Finset.mem_univ i)
  have hh := hs.trans (hbound t ht)
  have hi := le_max_right 0 (w t i)
  nlinarith [le_max_left 0 (w t i)]

end
end RAF1519.Refinement
