import proofs.RAFReactionCriticality.RAFCurvature

namespace RAFReactionCriticality.ExposureVariance
open RAF RAFQueryCompilation FunctionalSource FiniteProductDerivative FiniteThinning
open scoped BigOperators
variable {R : Type*} [Fintype R] [DecidableEq R]

theorem count_as_indicators (f : R → R) (m : R → Bool) :
    ((evaluate source (catalysts f) (available m)).card : ℝ) =
      ∑ r, indicator (orbitSet f r) m := by
  classical
  have hc : ((evaluate source (catalysts f) (available m)).card : ℝ) =
      ∑ r : R, if r ∈ evaluate source (catalysts f) (available m) then 1 else 0 := by simp
  rw [hc]
  apply Finset.sum_congr rfl
  intro r _
  have he : r ∈ evaluate source (catalysts f) (available m) ↔ Contains (orbitSet f r) m := by
    rw [evaluate_iff_orbit,safe_iff_orbit_subset,orbit_subset_available]
  simp only [indicator,he]

theorem functional_variance (f : R → R) (p : ℝ) :
    variance p (fun m => ((evaluate source (catalysts f) (available m)).card : ℝ)) =
      ∑ r, ∑ s, (p^(orbitSet f r ∪ orbitSet f s).card -
        p^((orbitSet f r).card+(orbitSet f s).card)) := by
  simp_rw [count_as_indicators]
  exact exposure_variance _ _

theorem normalized_concentration (E : (n : ℕ) → Fin n → Finset (Fin n))
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (h : Filter.Tendsto (fun n =>
      (∑ i : Fin n, ∑ j : Fin n, if (E n i ∩ E n j).Nonempty then (1 : ℝ) else 0) /
        (n : ℝ)^2) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => variance p (fun m => ∑ i, indicator (E n i) m) /
      (n : ℝ)^2) Filter.atTop (nhds 0) := by
  classical
  apply squeeze_zero
  · intro n
    exact div_nonneg (exposure_bounds (E n) hp hp1).1 (sq_nonneg _)
  · intro n
    exact div_le_div_of_nonneg_right (exposure_bounds (E n) hp hp1).2 (sq_nonneg _)
  · exact h

end RAFReactionCriticality.ExposureVariance
