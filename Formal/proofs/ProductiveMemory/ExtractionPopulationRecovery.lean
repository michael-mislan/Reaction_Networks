import proofs.ProductiveMemory.ExtractionSelected

namespace ProductiveMemory
open FiniteCopy HeritableCompositions ResourceLimitedCompetition Set
open scoped NNReal
noncomputable section
set_option Elab.async false

def extractionCellLaw (rho : ℝ) (hr : 0 ≤ rho) (zL zH : ℝ) (c : TaggedCell)
    (hmem : c.compartment.1 ∈ extractionDomain rho zL zH c.high c.compartment.2)
    (q : NNReal) (hq : 0 < (q:ℝ))
    (hclock : ∀ x, (extractionStoppedModel rho hr c.compartment.2
      (extractionDomain rho zL zH c.high c.compartment.2)).total x ≤ q) :
    FiniteLaw (ExtractionStoppedCounts (extractionDomain rho zL zH c.high c.compartment.2)) :=
  poissonLaw ((extractionStoppedModel rho hr c.compartment.2
    (extractionDomain rho zL zH c.high c.compartment.2)).uniformize q hq hclock)
    (q*5376) (some ⟨c.compartment.1,hmem⟩)

def extractionCellReady (rho zL zH : ℝ) (c : TaggedCell) :
    Set (ExtractionStoppedCounts (extractionDomain rho zL zH c.high c.compartment.2)) :=
  terminalReady c.compartment.2 (extractionDomain rho zL zH c.high c.compartment.2)
    (extractionCenter rho zL zH c.high) (extractionEnergy c.high)

theorem extraction_population_return (rho zL zH : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (heL : extractDrift rho 0 (lift rho zL) = 0)
    (heH : extractDrift rho 0 (lift rho zH) = 0)
    (M : ℕ) (c : Fin M → TaggedCell)
    (hm : ∀ i, recoveryCount ≤ (c i).compartment.2)
    (hb : ∀ i, extractionCellEnergy rho zL zH (c i) ≤ 8*readyLevel)
    (hmem : ∀ i, (c i).compartment.1 ∈ extractionDomain rho zL zH (c i).high (c i).compartment.2)
    (q : Fin M → NNReal) (hq : ∀ i, 0 < (q i:ℝ))
    (hclock : ∀ i x, (extractionStoppedModel rho (by linarith [hr.1]) (c i).compartment.2
      (extractionDomain rho zL zH (c i).high (c i).compartment.2)).total x ≤ q i)
    (hk : ∀ i, ((c i).compartment.2:ℝ)*localAlpha*readyLevel/480 ≤ q i) :
    1-(M:ℝ)/10^18 ≤
      (SerialTransferSelection.recoveryProductLaw (fun i => extractionCellLaw rho (by linarith [hr.1])
        zL zH (c i) (hmem i) (q i) (hq i) (hclock i))).expect
        (FiniteKernel.eventIndicator {x | ∀ i, x i ∈ extractionCellReady rho zL zH (c i)}) := by
  have h := SerialTransferSelection.recoveryProductLaw_lower
    (fun i => extractionCellLaw rho (by linarith [hr.1]) zL zH (c i) (hmem i) (q i) (hq i) (hclock i))
    (fun i => extractionCellReady rho zL zH (c i)) (1/10^18) (by norm_num) (fun i => ?_)
  · simpa [div_eq_mul_inv] using h
  · change 1-1/10^18 ≤ (poissonLaw _ _ _).expect _
    rw [poissonLaw_expect]
    exact mixed_extraction_ready rho zL zH hr hzL hzH heL heH (c i).high (c i).compartment.2
      (hm i) (q i) (hq i) (hclock i) (hk i) ⟨(c i).compartment.1,hmem i⟩ (hb i)

theorem extraction_retained_return (rho zL zH : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (heL : extractDrift rho 0 (lift rho zL) = 0)
    (heH : extractDrift rho 0 (lift rho zH) = 0)
    (M : ℕ) (s : PopulationState)
    (hsize : ∀ c ∈ s.live, recoveryCount ≤ c.compartment.2)
    (henergy : ∀ c ∈ s.live, extractionCellEnergy rho zL zH c ≤ 8*readyLevel)
    (S : SerialTransferSelection.TransferSubset s.live.length M) :
    let c := extractionRetained M s S
    let hmem := fun i => extraction_cell_admitted rho zL zH hr hzL hzH (c i)
      (hsize _ (extraction_retained_mem M s S i)) (henergy _ (extraction_retained_mem M s S i))
    ∃ q : Fin M → NNReal, ∃ hq : ∀ i, 0 < (q i:ℝ),
    ∃ hclock : ∀ i x, (extractionStoppedModel rho (by linarith [hr.1]) (c i).compartment.2
      (extractionDomain rho zL zH (c i).high (c i).compartment.2)).total x ≤ q i,
    1-(M:ℝ)/10^18 ≤
      (SerialTransferSelection.recoveryProductLaw (fun i => extractionCellLaw rho (by linarith [hr.1])
        zL zH (c i) (hmem i) (q i) (hq i) (hclock i))).expect
        (FiniteKernel.eventIndicator {x | ∀ i, x i ∈ extractionCellReady rho zL zH (c i)}) := by
  classical
  let c := extractionRetained M s S
  choose q hq hk hclock using fun i : Fin M =>
    (extractionStoppedModel rho (by linarith [hr.1]) (c i).compartment.2
      (extractionDomain rho zL zH (c i).high (c i).compartment.2)).exists_clock
      (((c i).compartment.2:ℝ)*localAlpha*readyLevel/480)
  refine ⟨q,hq,hclock,?_⟩
  exact extraction_population_return rho zL zH hr hzL hzH heL heH M c
    (fun i => hsize _ (extraction_retained_mem M s S i))
    (fun i => henergy _ (extraction_retained_mem M s S i)) _ q hq hclock hk

end
end ProductiveMemory
