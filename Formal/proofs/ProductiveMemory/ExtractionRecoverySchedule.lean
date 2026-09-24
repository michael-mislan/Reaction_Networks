import proofs.ProductiveMemory.ExtractionRecoveryService

namespace ProductiveMemory
open FiniteCopy HeritableCompositions ResourceLimitedCompetition
noncomputable section
set_option Elab.async false

structure ExtractionRecoverySchedule (rho : ℝ) (hr : 0 ≤ rho) (zL zH : ℝ) (c : TaggedCell) where
  clock : NNReal
  quota : ℕ
  clock_pos : 0 < (clock:ℝ)
  quota_pos : 0 < quota
  decay_le : (c.compartment.2:ℝ)*localAlpha*readyLevel/480 ≤ clock
  total_le : ∀ x, (extractionStoppedModel rho hr c.compartment.2
    (extractionDomain rho zL zH c.high c.compartment.2)).total x ≤ clock
  quota_error : 5376*(clock:ℝ)/(quota:ℝ) ≤ 1/10^18

def extractionRecoverySchedule (rho : ℝ) (hr : 0 ≤ rho) (zL zH : ℝ) (c : TaggedCell) :
    ExtractionRecoverySchedule rho hr zL zH c := by
  classical
  have h : Nonempty (ExtractionRecoverySchedule rho hr zL zH c) := by
    obtain ⟨q,J,hq,hJ,hk,hclock,htail⟩ := extraction_finite_clock_quota rho hr zL zH c
    exact ⟨⟨q,J,hq,hJ,hk,hclock,htail⟩⟩
  exact Classical.choice h

end
end ProductiveMemory
