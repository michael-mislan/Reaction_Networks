import proofs.ProductiveMemory.ExtractionCountOutput
import proofs.ProductiveMemory.ExtractionInitialLattice
import proofs.ProductiveMemory.ExtractionBoundary

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
noncomputable section
set_option Elab.async false

/-- Nonvacuous source-specific stochastic compatibility on a rational extraction interval.
This does not by itself assert a closed-reservoir physical realization. -/
theorem productive_extraction_compatibility (rho : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100)) :
    ∃ (zL zH : ℝ) (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
      (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
      (s : ProductiveReady recoveryCount productiveM rho zL zH),
      extractDrift rho 0 (lift rho zL)=0 ∧ extractDrift rho 0 (lift rho zH)=0 ∧
      (∀ i, 0 < lift rho zL i ∧ 0 < lift rho zH i) ∧
      (∀ b, ancestralCount b s.val.population.live=2000000000) ∧
      995994/1000000 ≤
        (productiveTwoCycleLaw recoveryCount productiveM (by norm_num [recoveryCount])
          (by norm_num [productiveM]) le_rfl rho zL zH hr hzL hzH productiveGamma
          (by norm_num [productiveGamma]) productiveTime s).expect
          (FiniteKernel.eventIndicator (SerialTransferSelection.successfulOutput
            (productiveCountOutput recoveryCount productiveM
              (productiveJ recoveryCount productiveM rho productiveTime) rho zL zH s.val))) := by
  obtain ⟨⟨zL,hzL,hsL,hpL⟩,⟨zH,hzH,hsH,hpH⟩⟩ := two_positive_stationary_states rho hr
  obtain ⟨s,hs⟩ := extraction_balanced_initial recoveryCount 2000000000
    (by norm_num [recoveryCount]) rho zL zH hr hzL hzH
  change ProductiveReady recoveryCount productiveM rho zL zH at s
  refine ⟨zL,zH,hzL,hzH,s,hsL,hsH,fun i => ⟨hpL i,hpH i⟩,hs,?_⟩
  apply productive_count_output_probability rho zL zH hr hzL hzH hsL hsH s
  intro b
  rw [hs b]
  norm_num [productiveM]

end
end ProductiveMemory
