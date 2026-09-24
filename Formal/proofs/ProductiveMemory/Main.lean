import proofs.ProductiveMemory.ExtractionNetProduction
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
theorem productive_memory_root :
    (∀ (rho : ℝ) (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100)),
      ∃ (zL zH : ℝ) (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
        (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000)),
        ExtractionAttracts rho (lift rho zL) lowExtractionEnergy ∧
        ExtractionAttracts rho (lift rho zH) highExtractionEnergy ∧
        Disjoint (energyRegion lowExtractionEnergy (lift rho zL) outerLevel)
          (energyRegion highExtractionEnergy (lift rho zH) outerLevel) ∧
        ∃ (s : ProductiveReady recoveryCount productiveM rho zL zH),
          (∀ b, ancestralCount b s.val.population.live=2000000000) ∧
          995994/1000000 ≤
            (productiveTwoCycleLaw recoveryCount productiveM (by norm_num [recoveryCount])
              (by norm_num [productiveM]) le_rfl rho zL zH hr hzL hzH
              productiveGamma (by norm_num [productiveGamma]) productiveTime s).expect
              (FiniteKernel.eventIndicator (SerialTransferSelection.successfulOutput
                (productiveCountOutput recoveryCount productiveM
                  (productiveJ recoveryCount productiveM rho productiveTime) rho zL zH s.val)))) ∧
    (∀ rho, 31/1000 ≤ rho → ∀ x : Point, 2 ≤ x 2 → extractDrift rho 0 x ≠ 0) := by
  constructor
  · intro rho hr
    obtain ⟨zL,zH,hzL,hzH,s,hsL,hsH,_,hs,hprob⟩ := productive_extraction_compatibility rho hr
    exact ⟨zL,zH,hzL,hzH,low_extraction_attracts rho zL hr hzL hsL,
      high_extraction_attracts rho zH hr hzH hsH,separated_outer_regions rho zL zH hzL hzH,s,hs,hprob⟩
  · exact no_high_stationary_above_boundary

/-- Fixed stocks are selected before either cycle; recovery collection is included. -/
theorem productive_memory_resource_witness (rho zL zH : ℝ) (hr : 0 ≤ rho) :
    ∃ stock : ℕ, ∀ (s : Fin 2 → ProductiveReady recoveryCount productiveM rho zL zH)
      (c : Fin 2 → Fin productiveM → TaggedCell), (∀ j i, c j i ∈ cellBox recoveryCount) →
      ∀ (B : Fin 2 → ℕ) (R : Fin 2 → Fin productiveM → ℕ),
      (∀ j, B j < (extractionBatchSchedule rho productiveGamma hr (by norm_num [productiveGamma])
        recoveryCount productiveM (membrane (s j).val.population.live)
        (productiveCollectionQuota recoveryCount productiveM rho productiveTime) zL zH productiveTime).service) →
      (∀ j i, R j i < (extractionRecoverySchedule rho hr zL zH (c j i)).quota) →
      (∑ j, (B j+(∑ i, R j i))) < stock := by
  refine ⟨2*(productiveBatchStock recoveryCount productiveM rho zL zH productiveGamma hr
    (by norm_num [productiveGamma]) productiveTime+
      productiveM*extractionRecoveryStock recoveryCount rho zL zH hr),?_⟩
  exact productive_two_cycle_service_stock recoveryCount productiveM rho zL zH productiveGamma hr
    (by norm_num [productiveGamma]) productiveTime

end
end ProductiveMemory
