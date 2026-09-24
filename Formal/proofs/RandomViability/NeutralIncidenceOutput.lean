import proofs.RandomViability.MixedIncidenceOutput

set_option Elab.async false
namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 50000

theorem half_modified_zero_credit {n : ℕ} (p q : Molecule n) (V : NNReal)
    (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) :
    halfModifiedInputReward p 0 V N ch = halfModifiedInputReward q 0 V N ch := by
  rcases ch with external | internal
  · rfl
  · simp only [halfModifiedInputReward,singleIncidence_count_eq,zero_mul,sub_zero]

/-- Neutral local channels, including both-nonfood and wholly-food channels,
cannot produce outside the stated exponentially small noise event. -/
theorem physical_isolated_neutral_output_upper {n : ℕ}
    [MeasurableSpace (PhysicalCountChannel n)] [MeasurableSingletonClass (PhysicalCountChannel n)]
    (hn : 4 ≤ n) (c : SourceMoleculeFibreConfig n) (z₀ : Molecule n) (r₀ : Reaction n)
    (hsingle : SingleLocalIncidence singleIncidenceCutoff c z₀ r₀)
    (hgain : ligationNonfoodMassGain r₀ = 0)
    (V : NNReal) (hV : 0 < (V : ℝ)) (hscale : (n : ℝ)/V ≤ 1/200)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (N : Molecule n → ℕ) (hinit : countNonfoodMass N = 0) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | physicalOutputEvent V z} ≤
      2*ENNReal.ofReal (Real.exp (-((1/200 : ℝ)^2*(V : ℝ)/(4*(n : ℝ)*(96011*101+1/200))))) := by
  let p : Molecule n := moleculeOfCode (L := 3) (by norm_num) (by omega) 0
  have plen : molLength p = 3 := molLength_moleculeOfCode _ _ _
  have hp : (0 : ℝ)+3 ≤ molLength p := by rw [plen]; norm_num
  have hb1 : ∀ r,(basal r : ℝ) ≤ 1 := by
    intro r
    have hh := hb r
    linarith only [hh]
  apply physical_mixed_exclusion_of_drift hn p 0 (by norm_num) (by norm_num) hp
    c V hV hscale basal cat hb1 hcat _ N hinit
  intro M hM
  have heq (c' : SourceMoleculeFibreConfig n) :
      markedRewardDrift c' V basal cat (halfModifiedInputReward p 0 V) M =
      markedRewardDrift c' V basal cat
        (halfModifiedInputReward (reactionProduct r₀) (ligationNonfoodMassGain r₀) V) M := by
    rw [hgain]
    congr 1
    funext Q ch
    exact half_modified_zero_credit p (reactionProduct r₀) V Q ch
  rw [heq c,half_modified_drift_erase c z₀ r₀ V basal cat M,← heq (eraseLocalIncidence c z₀ r₀)]
  exact short_free_half_modified_drift_bound (eraseLocalIncidence c z₀ r₀)
    (erase_local_has_no_short_incidence c z₀ r₀ hsingle) p
    (by rw [plen]; norm_num [singleIncidenceHalfCutoff]) (by rw [plen])
    0 (by norm_num) (by norm_num) V hV basal cat hb hcat M hM

end
end RandomViability
