import proofs.RobustPermanence.RateAbsorber
import proofs.RobustPermanence.RateError
import proofs.RobustPermanence.UniformGradient
import proofs.RobustPermanence.ConsumerPotential

namespace RobustPermanence
open CoreCouplingGlobal CoreCouplingCAC Set

noncomputable def potentialDirection (e A B z H a' b' z' H' : ℝ) : ℝ :=
  (Real.log (z+2)-responseSlope e B*responseLog z+responsePIntegrand e B)*b'
    -(responseTotal e B-(1+z)*B-16*z-4*z^2+3*H)/((z+1)*(z+2))*z'
    +3*(responseLog (responsePhi H)-responseLog z)*H'
    +(A+B-responseTotal e B)*(a'+b'-responseSlope e B*b')

theorem small_potential_direction (e A B z H a' b' z' H' : ℝ)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (hA : 0 ≤ A) (hA' : A ≤ 34)
    (hB : 2 ≤ B) (hB' : B ≤ 34) (hz : 0 ≤ z) (hz' : z ≤ 12)
    (hH : 0 ≤ H) (hH' : H ≤ 1536/7)
    (ha : |a'| ≤ 1/10000000000000) (hb : |b'| ≤ 1/10000000000000)
    (hzz : |z'| ≤ 1/10000000000000) (hh : |H'| ≤ 1/10000000000000) :
    |potentialDirection e A B z H a' b' z' H'| ≤ 1/10000000 := by
  have scale (v : ℝ) (hv : |v| ≤ 1/10000000000000) : |10000000000000*v| ≤ 384 := by
    rw [abs_mul]
    norm_num
    linarith only [hv]
  have hg := potential_direction_bound e A B z H
    (10000000000000*a') (10000000000000*b') (10000000000000*z') (10000000000000*H')
    he he' hA hA' hB hB' hz hz' hH hH' (scale _ ha) (scale _ hb) (scale _ hzz) (scale _ hh)
  change |potentialDirection e A B z H (10000000000000*a') (10000000000000*b')
    (10000000000000*z') (10000000000000*H')| ≤ 1000000 at hg
  have hid : potentialDirection e A B z H (10000000000000*a') (10000000000000*b')
      (10000000000000*z') (10000000000000*H') =
      10000000000000*potentialDirection e A B z H a' b' z' H' := by
    dsimp [potentialDirection]
    ring
  rw [hid,abs_mul] at hg
  norm_num at hg
  linarith only [hg]

noncomputable def ratePotentialRate (e : ℝ) (r : AssemblyRates) (A B z H X : ℝ) : ℝ :=
  potentialDirection e A B z H (rateA r A B z) (rateB r A B z)
    (rateZ r A B z H X) (rateH r z H)

theorem rate_corrected_growth (e : ℝ) (r : AssemblyRates) (hr : RateNeighborhood e r)
    (A B z H X : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (hA : 0 ≤ A) (hA' : A ≤ 34) (hB : 2 ≤ B) (hB' : B ≤ 34)
    (hz : 0 ≤ z) (hz' : z ≤ 12) (hH : 0 ≤ H) (hH' : H ≤ 1536/7)
    (hX : 0 ≤ X) (hX' : X ≤ 12) :
    X*(1/8-60000001*X) ≤ rateX r z X-150000*X*ratePotentialRate e r A B z H X := by
  obtain ⟨ha,hb,hzz,hh,hg⟩ := rate_resident_errors e r hr A B z H X
    hA hA' (by linarith) hB' hz hz' hH hH' hX hX'
  have hp := small_potential_direction e A B z H
    (rateA r A B z-fA (flagshipRates e) A B z)
    (rateB r A B z-fB (flagshipRates e) A B z)
    (rateZ r A B z H X-(fZ (flagshipRates e) A B z H-z*X))
    (rateH r z H-fH (flagshipRates e) z H)
    he he' hA hA' hB hB' hz hz' hH hH' ha hb hzz hh
  have hid : potentialDirection e A B z H
      (rateA r A B z-fA (flagshipRates e) A B z)
      (rateB r A B z-fB (flagshipRates e) A B z)
      (rateZ r A B z H X-(fZ (flagshipRates e) A B z H-z*X))
      (rateH r z H-fH (flagshipRates e) z H) =
      ratePotentialRate e r A B z H X-potentialRate e A B z H X := by
    dsimp [potentialDirection,ratePotentialRate,potentialRate]
    ring
  rw [hid] at hp
  have hpd := mul_le_mul_of_nonneg_left (abs_le.1 hp).2
    (by positivity : 0 ≤ 150000*X)
  have hgd := mul_le_mul_of_nonneg_left (abs_le.1 hg).1 hX
  have hc := consumer_corrected_growth e A B z H X he he' hA hA' hB hB' hz hz' hH hH' hX
  dsimp [rateX]
  nlinarith only [hpd,hgd,hc,hX]

theorem rate_potential_hasDerivAt (e : ℝ) (p : PotentialPrimitives e)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (r : AssemblyRates)
    (S : ℝ → State) (x : ℝ → ℝ) (hS : IsRateTrajectory r S x)
    (t : ℝ) (ht : 0 ≤ t) (hB : (S t).B ∈ Icc (2:ℝ) 34)
    (hz : (S t).z ∈ Icc (0:ℝ) 12) (hH : (S t).H ∈ Icc (0:ℝ) (1536/7)) :
    HasDerivAt (trajectoryPotential e p S)
      (ratePotentialRate e r (S t).A (S t).B (S t).z (S t).H (x t)) t := by
  have dr := ((hS.dA t ht).add (hS.dB t ht)).sub
    ((responseTotal_hasDerivAt e (S t).B he he' hB.1 hB.2).comp t (hS.dB t ht))
  exact responsePotential_hasDerivAt e p he he'
    (fun t => (S t).B) (fun t => (S t).z) (fun t => (S t).H)
    (fun t => (S t).A+(S t).B-responseTotal e (S t).B) t _ _ _ _
    hB hz hH (hS.dB t ht) (hS.dz t ht) (hS.dH t ht) dr

end RobustPermanence
