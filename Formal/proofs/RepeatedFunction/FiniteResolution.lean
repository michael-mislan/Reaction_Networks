import proofs.RepeatedFunction.FiniteConverse
import proofs.RepeatedFunction.PositiveWitness

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

def missionLowerBound (a : ℝ) (n V : ℕ) : ℝ :=
  (sourceEmptyRowMass a n ^ 6*powerLawMoleculeGatewayHit a (sourceReactionCount n) 1)*
    (1-24*Real.exp (-(twoWindowNoiseRate*(V : ℝ)/(n : ℝ))))

def missionResidualBound (a : ℝ) (n V : ℕ) : ℝ :=
  eventMass a n (fun c => ¬AtMostOneLocalIncidence singleIncidenceCutoff c)+
    localOutputNoiseUpper n (V : NNReal)

def missionUpperBound (a : ℝ) (n V : ℕ) : ℝ :=
  15480*(windowZipfMean a (sourceReactionCount n)/sourceReactionCount n)+missionResidualBound a n V

theorem c6_short_coefficient :
    Fintype.card (Molecule 4)*Fintype.card (Reaction 6) = 15480 := by
  rw [HordijkSteelThreshold.card_molecules_exact,
    card_binaryReaction_eq_sourceReactionCount (n := 6) (by norm_num)]
  norm_num [sourceReactionCount]

local instance resolutionChannelSpace (n : ℕ) : MeasurableSpace (PhysicalCountChannel n) := ⊤
local instance resolutionChannelSingleton (n : ℕ) : MeasurableSingletonClass (PhysicalCountChannel n) := ⟨fun _ => trivial⟩

/-- Finite source-instantiated bracket and two explicit posterior bounds.
The local-multiplicity remainder is retained explicitly. This theorem does
not claim that this coarse finite remainder is small at practical n. -/
theorem two_window_finite_source_resolution {n : ℕ} (hn : 4 ≤ n) (V : ℕ)
    (hvolume : collectiveMinimalVolume n ≤ V) (a : ℝ) (ha : 1 < a) :
    let hV := (collective_minimal_volume_pos n).trans_le hvolume
    let S := averagedMissionProbability hn V hV a (fun _ => True)
    let A := sourceFoodSilentSeed (reactionProduct (productiveReaction hn)) (productiveReaction hn)
    0 < missionLowerBound a n V ∧ missionLowerBound a n V ≤ S ∧
      S ≤ missionUpperBound a n V ∧
      missionLowerBound a n V/missionUpperBound a n V ≤ averagedMissionProbability hn V hV a A/S ∧
      averagedMissionProbability hn V hV a noProductiveSingleton/S ≤
        missionResidualBound a n V/missionLowerBound a n V := by
  dsimp only
  let hV := (collective_minimal_volume_pos n).trans_le hvolume
  let S := averagedMissionProbability hn V hV a (fun _ => True)
  let A := sourceFoodSilentSeed (reactionProduct (productiveReaction hn)) (productiveReaction hn)
  have hsc := singleton_volume_scales n V hn hvolume
  have hvR : (10^60 : ℝ)*((n : ℝ)+1)^2 ≤ (V : ℝ) := by exact_mod_cast hvolume
  have hsc' := two_window_quadratic_volume_scale n V
    (by exact_mod_cast (show 1 ≤ n by omega)) hvR
  have hL : 0 < missionLowerBound a n V := by
    unfold missionLowerBound
    exact mul_pos (c6_source_witness_mass_pos a ha n)
      (by have hf := two_window_noise_factor_ge_half _ hsc'.2.2; linarith only [hf])
  have hlo : missionLowerBound a n V ≤ S :=
    averaged_mission_lower hn V hV hsc.1 a ha (fun _ => True) (fun _ _ => trivial)
  have hA : missionLowerBound a n V ≤ averagedMissionProbability hn V hV a A :=
    averaged_mission_lower hn V hV hsc.1 a ha A (fun _ hs => hs)
  have hup : S ≤ missionUpperBound a n V := by
    have hh := averaged_mission_finite_upper hn V hV hsc.1 hsc.2 a ha (fun _ => True)
    rw [c6_short_coefficient] at hh
    simpa only [missionUpperBound,missionResidualBound,Nat.cast_ofNat,add_assoc] using hh
  have hS : 0 < S := hL.trans_le hlo
  have hres := averaged_mission_without_singleton_upper hn V hV hsc.1 hsc.2 a ha
  have hr : 0 ≤ missionResidualBound a n V :=
    (averaged_mission_nonneg hn V hV a ha noProductiveSingleton).trans hres
  refine ⟨hL,hlo,hup,?_,?_⟩
  · exact (div_le_div_of_nonneg_left hL.le hS hup).trans
      (div_le_div_of_nonneg_right hA hS.le)
  · exact (div_le_div_of_nonneg_right hres hS.le).trans
      (div_le_div_of_nonneg_left hr hL hlo)

end
end RandomViability
