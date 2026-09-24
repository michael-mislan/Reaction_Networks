import proofs.ProductiveMemory.ExtractionPopulationRecovery
import proofs.SerialTransferSelection.ServiceJoint

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
open scoped NNReal
noncomputable section
set_option Elab.async false

def extractionServiceLaw (M : ℕ) (rho : ℝ) (hr : 0 ≤ rho) (zL zH : ℝ) (c : Fin M → TaggedCell)
    (hmem : ∀ i, (c i).compartment.1 ∈ extractionDomain rho zL zH (c i).high (c i).compartment.2)
    (J : Fin M → ℕ) (q : Fin M → NNReal) (hq : ∀ i, 0 < (q i:ℝ))
    (hclock : ∀ i x, (extractionStoppedModel rho hr (c i).compartment.2
      (extractionDomain rho zL zH (c i).high (c i).compartment.2)).total x ≤ q i) :
    FiniteLaw (∀ i, ExtractionStoppedCounts (extractionDomain rho zL zH (c i).high (c i).compartment.2) × Fin (J i+1)) :=
  SerialTransferSelection.recoveryProductLaw (fun i => poissonLaw
    ((SerialTransferSelection.serviceCounterModel (extractionStoppedModel rho hr (c i).compartment.2
      (extractionDomain rho zL zH (c i).high (c i).compartment.2)) (J i)).uniformize (q i) (hq i) (fun x => hclock i x.1))
      (q i*5376) (some ⟨(c i).compartment.1,hmem i⟩,0))

def extractionServiceGood (M : ℕ) (rho zL zH : ℝ) (c : Fin M → TaggedCell) (J : Fin M → ℕ) :
    Set (∀ i, ExtractionStoppedCounts (extractionDomain rho zL zH (c i).high (c i).compartment.2) × Fin (J i+1)) :=
  {x | ∀ i, (x i).1 ∈ extractionCellReady rho zL zH (c i) ∧ (x i).2.val < J i}

theorem extraction_service_return (M : ℕ) (rho zL zH : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (heL : extractDrift rho 0 (lift rho zL)=0) (heH : extractDrift rho 0 (lift rho zH)=0)
    (c : Fin M → TaggedCell) (hm : ∀ i, recoveryCount ≤ (c i).compartment.2)
    (hb : ∀ i, extractionCellEnergy rho zL zH (c i) ≤ 8*readyLevel)
    (hmem : ∀ i, (c i).compartment.1 ∈ extractionDomain rho zL zH (c i).high (c i).compartment.2)
    (J : Fin M → ℕ) (hJ : ∀ i, 0 < J i) (q : Fin M → NNReal) (hq : ∀ i, 0 < (q i:ℝ))
    (hclock : ∀ i x, (extractionStoppedModel rho (by linarith [hr.1]) (c i).compartment.2
      (extractionDomain rho zL zH (c i).high (c i).compartment.2)).total x ≤ q i)
    (hk : ∀ i, ((c i).compartment.2:ℝ)*localAlpha*readyLevel/480 ≤ q i)
    (htail : ∀ i, 5376*(q i:ℝ)/(J i:ℝ) ≤ 1/10^18) :
    1-2*(M:ℝ)/10^18 ≤ (extractionServiceLaw M rho (by linarith [hr.1]) zL zH c hmem J q hq hclock).expect
      (FiniteKernel.eventIndicator (extractionServiceGood M rho zL zH c J)) := by
  classical
  have hp := SerialTransferSelection.recoveryProductLaw_lower
    (fun i => poissonLaw
      ((SerialTransferSelection.serviceCounterModel (extractionStoppedModel rho (by linarith [hr.1]) (c i).compartment.2
        (extractionDomain rho zL zH (c i).high (c i).compartment.2)) (J i)).uniformize (q i) (hq i) (fun x => hclock i x.1))
        (q i*5376) (some ⟨(c i).compartment.1,hmem i⟩,0))
    (fun i => {x | x.1 ∈ extractionCellReady rho zL zH (c i) ∧ x.2.val < J i}) (2/10^18) (by norm_num) (fun i => ?_)
  · have hid : 1-2*(M:ℝ)/10^18 = 1-(M:ℝ)*(2/10^18) := by ring
    rw [hid]
    simpa only [Fintype.card_fin] using hp
  · rw [poissonLaw_expect]
    have hreturn := mixed_extraction_ready rho zL zH hr hzL hzH heL heH (c i).high (c i).compartment.2
      (hm i) (q i) (hq i) (hclock i) (hk i) ⟨(c i).compartment.1,hmem i⟩ (hb i)
    have hservice := SerialTransferSelection.service_joint_lower
      (extractionStoppedModel rho (by linarith [hr.1]) (c i).compartment.2
        (extractionDomain rho zL zH (c i).high (c i).compartment.2)) (J i) (hJ i) (q i) 5376 (hq i) (hclock i)
      (extractionCellReady rho zL zH (c i)) (some ⟨(c i).compartment.1,hmem i⟩)
    norm_num only [NNReal.coe_ofNat] at hservice
    apply le_trans _ hservice
    simp only [extractionCellReady]
    linarith only [hreturn,htail i]

theorem extraction_finite_clock_quota (rho : ℝ) (hr : 0 ≤ rho) (zL zH : ℝ) (c : TaggedCell) :
    ∃ q : NNReal, ∃ J : ℕ, 0 < (q:ℝ) ∧ 0 < J ∧
      ((c.compartment.2:ℝ)*localAlpha*readyLevel/480 ≤ q) ∧
      (∀ x, (extractionStoppedModel rho hr c.compartment.2
        (extractionDomain rho zL zH c.high c.compartment.2)).total x ≤ q) ∧
      5376*(q:ℝ)/(J:ℝ) ≤ 1/10^18 := by
  classical
  obtain ⟨q,hq,hk,hclock⟩ := (extractionStoppedModel rho hr c.compartment.2
    (extractionDomain rho zL zH c.high c.compartment.2)).exists_clock
      ((c.compartment.2:ℝ)*localAlpha*readyLevel/480)
  obtain ⟨J,hJ,ht⟩ := SerialTransferSelection.exists_finite_service_quota (q:ℝ) 5376 (1/10^18) (by norm_num)
  exact ⟨q,J,hq,hJ,hk,hclock,ht.le⟩

end
end ProductiveMemory
