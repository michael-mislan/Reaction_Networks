import proofs.RAF1519.Refinement.GraphNoiseBounds

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators

theorem graph_forced_lower {ι : Type*} [Fintype ι] (k : ι → ι → ℝ)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (F v : ℝ → ι → ℝ) (T S L : ℝ)
    (hc : ∀ i, ContinuousOn (fun t => F t i) (Set.Icc 0 T))
    (hd : ∀ t ∈ Set.Ico 0 T, ∀ i, HasDerivWithinAt (fun u => F u i) (v t i) (Set.Ici t) t)
    (h0 : ∀ i, S ≤ F 0 i)
    (hv : ∀ t ∈ Set.Ico 0 T, ∀ i, graphDiffusion k (F t) i-L ≤ v t i) :
    ∀ t ∈ Set.Icc 0 T, ∀ i, S-L*t ≤ F t i := by
  have hB (t : ℝ) : HasDerivAt (fun u => S-L*u) (-L) t := by
    simpa using ((hasDerivAt_id t).const_mul L).const_sub S
  have hBc : Continuous (fun t => S-L*t) := by fun_prop
  have hb := graph_right_barrier k hk hsym (fun t i => (S-L*t)-F t i)
    (fun t i => -L-v t i) T
    (fun i => hBc.continuousOn.sub (hc i))
    (fun t ht i => (hB t).hasDerivWithinAt.sub (hd t ht i))
    (fun i => by simpa using sub_nonpos.mpr (h0 i)) (by
      intro t ht i _
      have he : (∑ j, k i j*(((S-L*t)-F t j)-((S-L*t)-F t i))) =
          -graphDiffusion k (F t) i := by
        unfold graphDiffusion
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [he]
      linarith [hv t ht i])
  intro t ht i
  linarith [hb t ht i]

end
end RAF1519.Refinement
