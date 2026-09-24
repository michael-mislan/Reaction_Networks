import proofs.ProductiveMemory.ExtractionWell
import proofs.HeritableCompositions.PartitionFailure

namespace ProductiveMemory
open FiniteCopy HeritableCompositions Set
noncomputable section
set_option Elab.async false

theorem low_extraction_energy_add_bound (y v : Point) :
    lowExtractionEnergy (fun i => y i+v i) ≤ (3/2)*lowExtractionEnergy y+3*lowExtractionEnergy v := by
  have h := lowExtractionEnergy_lower (fun i => y i-2*v i)
  have hn := normSq_nonneg (fun i => y i-2*v i)
  have hi : (3/2)*lowExtractionEnergy y+3*lowExtractionEnergy v-lowExtractionEnergy (fun i => y i+v i) =
      (1/2)*lowExtractionEnergy (fun i => y i-2*v i) := by unfold lowExtractionEnergy lowExtractionPair; ring
  nlinarith only [h,hn,hi]

theorem low_extraction_partition_return (y v : Point) (hy : lowExtractionEnergy y ≤ 2*innerEnergy)
    (hv : ∀ i, |v i| ≤ 1/1000000) :
    lowExtractionEnergy (fun i => y i+v i) < 4*innerEnergy := by
  have hn := partition_noise_norm v (1/1000000) hv
  have he := lowExtractionEnergy_upper v
  have ha := low_extraction_energy_add_bound y v
  norm_num [innerEnergy,outerEnergy] at hy ⊢
  nlinarith only [hn,he,ha,hy]

theorem low_extraction_partition_failure (rho z : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (98172/100000:ℝ) (98174/100000))
    (n : Counts) (N : ℕ) (hN : 0 < N)
    (hparent : lowExtractionEnergy (fun i => concentration (2*N) n i-lift rho z i) ≤ 2*readyLevel) :
    (∑ d ∈ daughterDraws n, daughterWeight n d*
      (if ¬(lowExtractionEnergy (fun i => concentration N d i-lift rho z i) < 4*readyLevel ∧
        lowExtractionEnergy (fun i => concentration N (fun j => n j-d j) i-lift rho z i) < 4*readyLevel) then 1 else 0)) ≤
      8*Real.exp (-(N:ℝ)*(1/1000000)^2/35) := by
  exact partition_failure_bound lowExtractionEnergy low_extraction_partition_return n N hN (lift rho z)
    (parent_count_bound lowExtractionEnergy lowExtractionEnergy_lower n N hN (lift rho z)
      (low_extraction_root_upper rho z hr hz) hparent) hparent

theorem high_extraction_energy_add_bound (y v : Point) :
    highExtractionEnergy (fun i => y i+v i) ≤ (3/2)*highExtractionEnergy y+3*highExtractionEnergy v := by
  have h := highExtractionEnergy_lower (fun i => y i-2*v i)
  have hn := normSq_nonneg (fun i => y i-2*v i)
  have hi : (3/2)*highExtractionEnergy y+3*highExtractionEnergy v-highExtractionEnergy (fun i => y i+v i) =
      (1/2)*highExtractionEnergy (fun i => y i-2*v i) := by unfold highExtractionEnergy highExtractionPair; ring
  nlinarith only [h,hn,hi]

theorem high_extraction_partition_return (y v : Point) (hy : highExtractionEnergy y ≤ 2*innerEnergy)
    (hv : ∀ i, |v i| ≤ 1/1000000) :
    highExtractionEnergy (fun i => y i+v i) < 4*innerEnergy := by
  have hn := partition_noise_norm v (1/1000000) hv
  have he := highExtractionEnergy_upper v
  have ha := high_extraction_energy_add_bound y v
  norm_num [innerEnergy,outerEnergy] at hy ⊢
  nlinarith only [hn,he,ha,hy]

theorem high_extraction_partition_failure (rho z : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (289014/100000:ℝ) (289017/100000))
    (n : Counts) (N : ℕ) (hN : 0 < N)
    (hparent : highExtractionEnergy (fun i => concentration (2*N) n i-lift rho z i) ≤ 2*readyLevel) :
    (∑ d ∈ daughterDraws n, daughterWeight n d*
      (if ¬(highExtractionEnergy (fun i => concentration N d i-lift rho z i) < 4*readyLevel ∧
        highExtractionEnergy (fun i => concentration N (fun j => n j-d j) i-lift rho z i) < 4*readyLevel) then 1 else 0)) ≤
      8*Real.exp (-(N:ℝ)*(1/1000000)^2/35) := by
  exact partition_failure_bound highExtractionEnergy high_extraction_partition_return n N hN (lift rho z)
    (parent_count_bound highExtractionEnergy highExtractionEnergy_lower n N hN (lift rho z)
      (high_extraction_root_upper rho z hr hz) hparent) hparent

end
end ProductiveMemory
