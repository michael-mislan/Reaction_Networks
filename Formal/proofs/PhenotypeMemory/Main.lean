import proofs.PhenotypeMemory.Partition
import proofs.PhenotypeMemory.PopulationBounds
import proofs.PhenotypeMemory.KilledMemory
import proofs.PhenotypeMemory.KernelAlgebra
import proofs.PhenotypeMemory.ReductionCertificate
import proofs.PhenotypeMemory.Regrowth
import proofs.PhenotypeMemory.StateOrder
import proofs.PhenotypeMemory.ComplementaryAssociation
import proofs.PhenotypeMemory.RiskResponse
import proofs.PhenotypeMemory.ThresholdRegrowth
import proofs.PhenotypeMemory.FiniteResponse

namespace PhenotypeMemory

/-- Critical finite certificates for the continuation paper. Probability
couplings, ODE validation and N=16 rational replay remain conventional. -/
theorem continuation_finite_certificate :
    (∀ i : Fin 6, molecular (1/100) independentUpper i + death i*(1-independentUpper i) +
      ((daughter independentUpper i)^2-independentUpper i)/10 < 0) ∧
    (∀ i : Fin 6, 0 ≤ independentUpper i ∧ independentUpper i < 988/1000) ∧
    (∀ i : Fin 6, 0 < responseWeight i ∧
      independentJacobian independentUpper responseWeight i ≤ (796/1000)*responseWeight i) ∧
    (686709/1000000 : ℚ)/(1-(988/1000)^300) < 706/1000 ∧
    (1 : ℚ)-22/100-(300/299)^299*(227/1000-22/100) > 760/1000 := by
  exact ⟨independent_supersolution, independent_upper_range, weighted_source_contraction,
    hit300_arithmetic.1, deadline_arithmetic⟩

/-- The promised formal endpoint is the source-connected finite certificate
package. Chronological stochastic-process identification is conventional and
is not hidden as a premise of this theorem. -/
theorem combined_finite_certificate :
    (∀ a r : ℕ, ∑ i ∈ Finset.range (a+1), ∑ j ∈ Finset.range (r+1),
      jointWeight a r i j = 1) ∧
    (∀ e : ℚ, 29/100 ≤ e → e ≤ 31/100 → ∀ i : Fin 6,
      meanAction e extinctionWeight i ≤ -(9/100)*extinctionWeight i) ∧
    (∀ e : ℚ, 99/10000 ≤ e → e ≤ 101/10000 → ∀ i : Fin 6,
      pgfResidual e jointUpper i ≤ 0) ∧
    (∀ e : ℚ, 0 ≤ e → e ≤ 3/100 → ∀ i : Fin 6,
      (1/10+death i)*restorationLower i-molecular e restorationLower i ≤
        daughter activeIndicator i/10) ∧
    (∀ n : Fin 8, ∀ i : Fin 6,
      lowerRow (n.val+1) i ≤ independentNext (lowerRow n.val) i) ∧
    lowerRow 8 5 > 31/100 ∧
    672/1000 < lowErasureHit-lowErasureTime/100 ∧ highErasureHit < 283/1000 := by
  exact ⟨joint_partition_normalized, uniform_extinction_certificate,
    uniform_joint_supersolution, uniform_restoration_certificate,
    lower_iteration_certificate, independent_lower_exceeds,
    exact_regrowth_arithmetic.1, exact_regrowth_arithmetic.2.1⟩

end PhenotypeMemory
