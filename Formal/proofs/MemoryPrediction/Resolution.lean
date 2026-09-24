import proofs.MemoryPrediction.Decision
import proofs.MemoryPrediction.DetectionBoundary

namespace MemoryPrediction
noncomputable section
open MeasureTheory ProbabilityTheory LowFounderPrediction RandomViability

def slowTrace := jumpTrajectoryLaw (1,0) next (rate yuleRates)
  (rate_nonneg yuleRates) (total_pos yuleRates)
def fastTrace := jumpTrajectoryLaw (0,1) next (rate yuleRates)
  (rate_nonneg yuleRates) (total_pos yuleRates)

/-- The guide's source-connected methods theorem. Calibration uses perfect
two-founder counts within the specified menu. The separate demographic-box
safety statement permits arbitrary deletion and the stated preparation/errors.
No desired CDF, observation equality or confidence event is an assumption. -/
theorem method_resolution
    {Obs Ω : Type*} [MeasurableSpace Obs] [MeasurableSpace Ω]
    (observe : (ℕ → JumpState State (Fin 7)) → Obs)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (O : Fin 4000 → Ω → State) (hO : ∀ i, Measurable (O i))
    (hi : iIndepFun O μ) (b : Bool) (hlaw : ∀ i, μ.map (O i)=menuLaw b)
    (Y : Ω → State) (hY : Measurable Y) (hfuture : μ.map Y=menuLaw b)
    (X : Ω → State) (hX : Measurable X) (D A : Ω → ℕ)
    (hD : ∀ ω, D ω ≤ totalCount (X ω))
    (hfalse : μ.real {ω | 0 < A ω} ≤ 1/100)
    (a : Rates) (ha : demographicBox a) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (empty single multiple : NNReal) (hsum : empty+single+multiple=1)
    (hm : (multiple : ℝ) ≤ 1/1000) (bad : Measure State) [IsProbabilityMeasure bad]
    (hprep : μ.map X = empty • Measure.dirac (0,0) +
      single • preparedSingle a p + multiple • bad) :
    ((independentFamilies slowTrace fastTrace).map Prod.fst).map observe =
      ((sharedFamilies slowTrace fastTrace).map Prod.fst).map observe ∧
    ((19/20 : ℝ) ≤ sourceCDF independentSource 6 ∧
      (∀ k < 6, sourceCDF independentSource k < 19/20) ∧
      (19/20 : ℝ) ≤ sourceCDF sharedSource 7 ∧
      (∀ k < 7, sourceCDF sharedSource k < 19/20)) ∧
    (153045/160000 : ℝ) ≤ μ.real {ω | totalCount (Y ω) ≤ chosenEndpoint O ω} ∧
    (952037/1000000 : ℝ) ≤ μ.real {ω | D ω+A ω ≤ 4} := by
  refine ⟨chronological_single_observation_equal observe,
    chronological_minimal_endpoints, ?_, ?_⟩
  · exact adaptive_prediction μ O hO hi b hlaw Y hY hfuture
  · exact observed_four μ X hX D A hD hfalse a ha p hp0 hp1
      empty single multiple hsum hm bad hprep

theorem both_prediction_margins :
    (19/20 : ℝ) < 153045/160000 ∧ (19/20 : ℝ) < 952037/1000000 := by
  norm_num

end
end MemoryPrediction
