import proofs.RandomViability.MixedIncidenceDriftBound
import proofs.RandomViability.SingleIncidenceExclusion

set_option Elab.async false
namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 60000
variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

/-- Complete isolated mixed-channel exclusion for the original output event.
The kinetic drift bound is derived from source isolation, not assumed. -/
theorem physical_isolated_mixed_output_upper (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (z₀ : Molecule n) (r₀ : Reaction n)
    (hsingle : SingleLocalIncidence singleIncidenceCutoff c z₀ r₀)
    (hmixed : MixedFoodIncidence r₀)
    (hsmall : molLength (reactionProduct r₀) ≤ singleIncidenceHalfCutoff)
    (V : NNReal) (hV : 0 < (V : ℝ)) (hscale : (n : ℝ)/V ≤ 1/200)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (N : Molecule n → ℕ) (hinit : countNonfoodMass N = 0) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | physicalOutputEvent V z} ≤
      2*ENNReal.ofReal (Real.exp (-((1/200 : ℝ)^2*(V : ℝ)/(4*(n : ℝ)*(96011*101+1/200))))) := by
  have hpars := mixed_incidence_weight_parameters r₀ hmixed
  have ha := (ligationNonfoodMassGain_bounds r₀).1
  have hb1 : ∀ r,(basal r : ℝ) ≤ 1 := by
    intro r
    have hh := hb r
    linarith only [hh]
  apply physical_mixed_exclusion_of_drift hn (reactionProduct r₀) (ligationNonfoodMassGain r₀)
    ha hpars.1 hpars.2 c V hV hscale basal cat hb1 hcat _ N hinit
  intro M hM
  exact isolated_mixed_half_modified_drift_bound c z₀ r₀ hsingle hmixed hsmall V hV basal cat hb hcat M hM

end
end RandomViability
