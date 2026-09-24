import proofs.OptimalAffinity.Affinity

/-!
Terminal source-level counterexample theorem.  The quantified proposition below
is the two-species/two-reaction restriction of the literature's general
seed-dependent lower-bound conjecture.  A counterexample to this restriction is
therefore a counterexample to the general universal claim.
-/

namespace OptimalAffinity

def TwoByTwoSeedLowerBound : Prop :=
  ∀ (N : Network) (x y : ℝ),
    SourceValid N → IsUniqueGlobalMaximum N x y →
    seedRatio N ≤ affinityExp N x y

theorem oa2x2_sourceFaithfulCounterexample :
    ∃ (N : Network) (x y : ℝ),
      SourceValid N ∧ IsUniqueGlobalMaximum N x y ∧
      affinityExp N x y < seedRatio N := by
  exact ⟨oa2x2, 1, 1, oa2x2_isSourceNetwork,
    oa2x2_uniqueGlobalMaximum, oa2x2_affinityViolation⟩

theorem optimalAffinity_seedLowerBound_false : ¬ TwoByTwoSeedLowerBound := by
  intro h
  have hbound := h oa2x2 1 1 oa2x2_isSourceNetwork oa2x2_uniqueGlobalMaximum
  exact (not_le_of_gt oa2x2_affinityViolation) hbound

end OptimalAffinity
