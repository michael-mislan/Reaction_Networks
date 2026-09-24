import proofs.ProductiveMemory.ExtractionNewbornProbability
import proofs.ProductiveMemory.ExtractionReadoutCorollaries
import proofs.ProductiveMemory.Main
import proofs.ProductiveMemory.ExtractionAttractors
import proofs.ProductiveMemory.ExtractionStocks
import proofs.ProductiveMemory.ExtractionElementBalance
import proofs.ProductiveMemory.ExtractionRecoveryMark
import proofs.ProductiveMemory.ExtractionErrorDiagnostic

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
noncomputable section
set_option Elab.async false

/-- The source-specific #16 result. The upper-rate exclusion is stationary only;
finite-time copying is asserted on the explicit interior interval. -/
theorem productive_memory_publication_root :
    (∀ (rho : ℝ) (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100)),
      ∃ (zL zH : ℝ) (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
        (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000)),
        ExtractionAttracts rho (lift rho zL) lowExtractionEnergy ∧
        ExtractionAttracts rho (lift rho zH) highExtractionEnergy ∧
        Disjoint (energyRegion lowExtractionEnergy (lift rho zL) outerLevel)
          (energyRegion highExtractionEnergy (lift rho zH) outerLevel) ∧
        ∃ (s : ProductiveReady recoveryCount productiveM rho zL zH),
          (∀ b, ancestralCount b s.val.population.live=2000000000) ∧
          24482873/24500000 ≤
            (productiveTwoCycleLaw recoveryCount productiveM (by norm_num [recoveryCount])
              (by norm_num [productiveM]) le_rfl rho zL zH hr hzL hzH
              productiveGamma (by norm_num [productiveGamma]) productiveTime s).expect
              (FiniteKernel.eventIndicator (SerialTransferSelection.successfulOutput
                (productiveNewbornOutput recoveryCount productiveM
                  (productiveJ recoveryCount productiveM rho productiveTime) rho zL zH s.val)))) ∧
    (∀ rho, 31/1000 ≤ rho → ∀ x : Point, 2 ≤ x 2 → extractDrift rho 0 x ≠ 0) := by
  constructor
  · intro rho hr
    obtain ⟨⟨zL,hzL,hsL,_⟩,⟨zH,hzH,hsH,_⟩⟩ := two_positive_stationary_states rho hr
    obtain ⟨s,hs,hnew⟩ := extraction_balanced_newborn recoveryCount 2000000000
      (by norm_num [recoveryCount]) rho zL zH hr hzL hzH
    change ProductiveReady recoveryCount productiveM rho zL zH at s
    refine ⟨zL,zH,hzL,hzH,low_extraction_attracts rho zL hr hzL hsL,
      high_extraction_attracts rho zH hr hzH hsH,separated_outer_regions rho zL zH hzL hzH,s,hs,?_⟩
    apply productive_newborn_probability rho zL zH hr hzL hzH hsL hsH s hnew
    intro b
    rw [hs b]
    norm_num [productiveM]
  · exact no_high_stationary_above_boundary


end
end ProductiveMemory
