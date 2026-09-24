import proofs.RAFReactionCriticality.GeneralPivotality

namespace RAFReactionCriticality.GeneralPivotality
open RAF RAFQueryCompilation FiniteProductDerivative
open scoped BigOperators
variable {M R : Type*} [DecidableEq M] [Fintype M] [DecidableEq R] [Fintype R]
variable (Q : CRS M R) (C : Catalysis M R) [∀ x r, Decidable (C x r)]

omit [Fintype M] [Fintype R] in
theorem retained_join_mono (S : Finset R) (i : R) (m : {j : R // j ≠ i} → Bool) :
    retained S (join i false m) ⊆ retained S (join i true m) := by
  intro r hr
  obtain ⟨hs, hm⟩ := Finset.mem_filter.mp hr
  apply Finset.mem_filter.mpr
  refine ⟨hs, ?_⟩
  by_cases hri : r = i
  · subst r
    simp at hm
  · simpa only [join_other i true m r hri] using
      (show m ⟨r,hri⟩ = true from by simpa only [join_other i false m r hri] using hm)

noncomputable def pivotalProbability (S : Finset R) (p : ℝ) (i : R) : ℝ :=
  ∑ m : {j : R // j ≠ i} → Bool, offWeight p i (join i false m) *
    if (evaluate Q C (retained S (join i true m))).Nonempty ∧
      evaluate Q C (retained S (join i false m)) = ∅ then 1 else 0

theorem survival_marginal_eq_pivotal (S : Finset R) (p : ℝ) (i : R) :
    marginal (survivalObservable Q C S) p i = pivotalProbability Q C S p i := by
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  have hmono := evaluate_mono Q C (retained_join_mono S i m)
  by_cases hlo : (evaluate Q C (retained S (join i false m))).Nonempty
  · have hhi := hlo.mono hmono
    simp [survivalObservable, hlo, hhi, Finset.nonempty_iff_ne_empty.mp hlo]
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hlo
    by_cases hhi : (evaluate Q C (retained S (join i true m))).Nonempty <;>
      simp [survivalObservable, hhi, hempty]

/-- Boolean Russo identity: the derivative is the sum of literal RAF pivotal probabilities. -/
theorem survival_derivative_pivotal (S : Finset R) (p : ℝ) :
    HasDerivAt (expectation (survivalObservable Q C S))
      (∑ i, pivotalProbability Q C S p i) p := by
  simpa only [survival_marginal_eq_pivotal] using survival_derivative Q C S p

end RAFReactionCriticality.GeneralPivotality
