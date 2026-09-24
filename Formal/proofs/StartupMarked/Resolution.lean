import proofs.StartupMarked.SourceLower
import proofs.RepeatedFunction.MissionAccounts

namespace StartupMarked
open Classical RandomViability MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 70000

def startupVolume (n : ℕ) : ℕ := max (10^24) (10^13*n)

theorem startup_volume_pos (n : ℕ) : 0 < startupVolume n :=
  lt_of_lt_of_le (by norm_num : 0 < (10 : ℕ)^24) (le_max_left _ _)

local instance resolutionChannelSpace (n : ℕ) : MeasurableSpace (PhysicalCountChannel n) := ⊤
local instance resolutionChannelSingleton (n : ℕ) : MeasurableSingletonClass (PhysicalCountChannel n) := ⟨fun _ => trivial⟩

/-- Improved finite reliability for the original two-window mission and source,
with physical synthesis accounts. No asymptotic converse is asserted. -/
theorem startup_quantitative_resolution {n : ℕ} (hn : 4 ≤ n) (V : ℕ)
    (hvolume : startupVolume n ≤ V) (a : ℝ) (ha : 1 < a) :
    let hV := (startup_volume_pos n).trans_le hvolume
    (∀ (c : SourceMoleculeFibreConfig n) (basal : Reaction n → NNReal)
      (cat : Reaction n → Molecule n → NNReal),
      (∀ r,productiveEpsilon ≤ (basal r : ℝ) ∧ (basal r : ℝ) ≤ 4*productiveEpsilon) →
      (∀ r z,4 ≤ (cat r z : ℝ) ∧ (cat r z : ℝ) ≤ 16) →
      sourceFoodSilentSeed (reactionProduct (productiveReaction hn)) (productiveReaction hn) c →
      (9989/10000 : ℝ) ≤ (physicalTrajectoryLaw (by omega : 2 ≤ n) c (V : NNReal) 1
        (by exact_mod_cast hV) (by norm_num) basal cat (foodOnlyCounts n V)
        {z | twoWindowMission (V : NNReal) z}).toReal) ∧
    (sourceEmptyRowMass a n ^ 6*powerLawMoleculeGatewayHit a (sourceReactionCount n) 1)*(9989/10000) ≤
      fullyAveragedTwoWindowProbability hn V hV a ∧
    (∀ (c : SourceMoleculeFibreConfig n) (u : KineticMarkConfig n),
      ∀ᵐ z ∂physicalTrajectoryLaw (by omega : 2 ≤ n) c (V : NNReal) 1
        (by exact_mod_cast hV) (by norm_num) (kineticBasal u) (kineticCatalytic u) (foodOnlyCounts n V),
        twoWindowMission (V : NNReal) z →
        ∃ L,prefixElapsed L (Preorder.frestrictLe L z) ≤ 199 ∧
          199 < prefixElapsed (L+1) (Preorder.frestrictLe (L+1) z) ∧
          (1/5 : ℝ) < markedWindowReward (signedSynthesisReward (V : NNReal)) z 0 L) := by
  have hlargeNat : (10 : ℕ)^24 ≤ V := (le_max_left _ _).trans hvolume
  have hlinearNat : (10 : ℕ)^13*n ≤ V := (le_max_right _ _).trans hvolume
  have hlarge : 1000000000000000000000000 ≤ (V : ℝ) := by exact_mod_cast hlargeNat
  have hlinear : 10000000000000*(n : ℝ) ≤ V := by exact_mod_cast hlinearNat
  dsimp only
  refine ⟨?_,startup_fully_averaged_lower hn V ((startup_volume_pos n).trans_le hvolume) hlarge hlinear a ha,?_⟩
  · intro c basal cat hb hc hseed
    exact startup_concrete_success hn V ((startup_volume_pos n).trans_le hvolume) hlarge hlinear
      c basal cat hb hc hseed
  · intro c u
    exact physical_mission_accounts (by omega) c V ((startup_volume_pos n).trans_le hvolume)
      (kineticBasal u) (kineticCatalytic u)

end
end StartupMarked

