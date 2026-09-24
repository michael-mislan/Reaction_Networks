import proofs.MultiConsumerPermanence.DonorLoad
import proofs.RobustPermanence.ConsumerPotential
import proofs.RobustPermanence.UniformPotential

namespace MultiConsumerPermanence
open CoreCouplingGlobal CoreCouplingCAC RobustPermanence Set

theorem loaded_potential_hasDerivAt (e : ℝ) (p : PotentialPrimitives e)
    (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (S : ℝ → State) (x : ℝ → ℝ) (hS : IsLoadedResidentTrajectory e S x)
    (t : ℝ) (ht : 0 ≤ t) (hB : (S t).B ∈ Icc (2:ℝ) 34)
    (hz : (S t).z ∈ Icc (0:ℝ) 12) (hH : (S t).H ∈ Icc (0:ℝ) (1536/7)) :
    HasDerivAt (trajectoryPotential e p S)
      (potentialRate e (S t).A (S t).B (S t).z (S t).H (x t)) t := by
  have dr := ((hS.dA t ht).add (hS.dB t ht)).sub
    ((responseTotal_hasDerivAt e (S t).B he he' hB.1 hB.2).comp t (hS.dB t ht))
  exact responsePotential_hasDerivAt e p he he'
    (fun t => (S t).B) (fun t => (S t).z) (fun t => (S t).H)
    (fun t => (S t).A+(S t).B-responseTotal e (S t).B) t _ _ _ _
    hB hz hH (hS.dB t ht) (hS.dz t ht) (hS.dH t ht) dr

end MultiConsumerPermanence
