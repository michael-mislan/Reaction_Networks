import proofs.InheritedCellAssay.ScalarSourceConstruction

namespace InheritedCellAssay.ScalarRateSource

/-- An explicit normalized scalar count source satisfying the rate-derived
    backward equations. This rules out a vacuous source-condition theorem. -/
noncomputable def concreteScalarSource : BackwardCountSource where
  weight := endpointWeight
  nonneg := endpointWeight_nonneg
  normalized := by
    simpa [ScalarBackward.candidate] using endpointWeight_pgf 1 (by norm_num)
  pgf := ScalarBackward.candidate meanRatio accumulatedBirth
  linked := endpointWeight_pgf
  continuous := by
    intro z hz
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.div
    · exact meanRatio_continuous.continuousOn.mul continuousOn_const
    · exact continuousOn_const.add (accumulatedBirth_continuous.continuousOn.mul continuousOn_const)
    · intro x hx
      have ha := accumulatedBirth_nonneg x hx.2
      have hw : 0 ≤ 1-z := by linarith [hz.2]
      positivity
  derivative := by
    intro z hz t ht
    apply ScalarBackward.candidate_derivative
    · exact meanRatio_derivative t ht.1.le
    · exact accumulatedBirth_derivative t
    · have ha := accumulatedBirth_nonneg t ht.2
      have hw : 0 ≤ 1-z := by linarith [hz.2]
      positivity
  bounds := fun z hz t ht => candidate_unit_bounds t z ⟨ht.1.le,ht.2⟩ hz
  terminal := fun z _ => candidate_terminal z

theorem concrete_scalar_coverage : 19/20 < endpointWeight 0+endpointWeight 1+endpointWeight 2 :=
  scalar_source_coverage concreteScalarSource

end InheritedCellAssay.ScalarRateSource
