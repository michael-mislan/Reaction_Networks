import proofs.HeritableCompositions.GrowthTracking
import proofs.HeritableCompositions.RecoveryBudget

namespace HeritableCompositions
open FiniteCopy

theorem low_energy_add_bound (y v : Point) :
    lowEnergy (fun i => y i+v i) ≤ (3/2)*lowEnergy y+3*lowEnergy v := by
  have h := lowEnergy_lower (fun i => y i-2*v i)
  have hn := normSq_nonneg (fun i => y i-2*v i)
  have he : (3/2)*lowEnergy y+3*lowEnergy v-lowEnergy (fun i => y i+v i) =
      (1/2)*lowEnergy (fun i => y i-2*v i) := by
    unfold lowEnergy
    ring
  nlinarith only [h,hn,he]

theorem high_energy_add_bound (y v : Point) :
    highEnergy (fun i => y i+v i) ≤ (3/2)*highEnergy y+3*highEnergy v := by
  have h := highEnergy_lower (fun i => y i-2*v i)
  have hn := normSq_nonneg (fun i => y i-2*v i)
  have he : (3/2)*highEnergy y+3*highEnergy v-highEnergy (fun i => y i+v i) =
      (1/2)*highEnergy (fun i => y i-2*v i) := by
    unfold highEnergy
    ring
  nlinarith only [h,hn,he]

theorem partition_noise_norm (v : Point) (δ : ℝ) (hv : ∀ i, |v i| ≤ δ) :
    normSq v ≤ 4*δ^2 := by
  have hs (i) : (v i)^2 ≤ δ^2 := by
    simpa only [← pow_two,sq_abs] using mul_self_le_mul_self (abs_nonneg (v i)) (hv i)
  unfold normSq
  linarith only [hs 0,hs 1,hs 2,hs 3]

theorem low_partition_return (y v : Point) (hy : lowEnergy y ≤ 2*innerEnergy)
    (hv : ∀ i, |v i| ≤ 1/1000000) :
    lowEnergy (fun i => y i+v i) < 4*innerEnergy := by
  have hn := partition_noise_norm v (1/1000000) hv
  have he := lowEnergy_upper v
  have ha := low_energy_add_bound y v
  norm_num [innerEnergy,outerEnergy] at hy ⊢
  nlinarith only [hn,he,ha,hy]

theorem high_partition_return (y v : Point) (hy : highEnergy y ≤ 2*innerEnergy)
    (hv : ∀ i, |v i| ≤ 1/1000000) :
    highEnergy (fun i => y i+v i) < 4*innerEnergy := by
  have hn := partition_noise_norm v (1/1000000) hv
  have he := highEnergy_upper v
  have ha := high_energy_add_bound y v
  norm_num [innerEnergy,outerEnergy] at hy ⊢
  nlinarith only [hn,he,ha,hy]

end HeritableCompositions

