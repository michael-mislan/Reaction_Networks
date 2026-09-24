import proofs.InheritedCellAssay.ScalarRateSource
import proofs.InheritedCellAssay.ThreePGFCertificate

namespace InheritedCellAssay.ScalarRateSource
open ScalarCount

theorem reciprocalMean_derivative (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (fun t => (64/33)*meanRatio t)
      (integrand x-(128/33)*rateMass x) x := by
  have h := (meanRatio_derivative x hx).const_mul (64/33)
  have hy : 1+x ≠ 0 := by linarith
  have hD := ne_of_gt (den_pos x)
  convert h using 1
  unfold integrand numerator denominator rateMass birth death meanRatio den
  unfold den at hD
  field_simp [hy, hD]
  ring

theorem accumulatedBirth_zero : accumulatedBirth 0 = (33*varianceIntegral-31)/128 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
    (fun x hx => reciprocalMean_derivative x (by
      have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
        simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      exact hx'.1))
    ((integrand_continuous.sub (continuous_const.mul rateMass_continuous)).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_sub (f := integrand) (g := fun x => (128/33)*rateMass x)
    (integrand_continuous.intervalIntegrable 0 1)
    ((continuous_const.mul rateMass_continuous).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul] at h
  change varianceIntegral-(128/33)*accumulatedBirth 0 =
    (64/33)*meanRatio 1-(64/33)*meanRatio 0 at h
  norm_num [meanRatio, den] at h
  linarith

theorem candidate_identification (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (H : ℝ → ℝ) (hcont : ContinuousOn H (Set.Icc (0 : ℝ) 1))
    (hderiv : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      HasDerivAt H (ScalarBackward.field (birth t) (death t) (H t)) t)
    (hb : ∀ t ∈ Set.Ioc (0 : ℝ) 1, H t ∈ Set.Icc (0 : ℝ) 1)
    (hterminal : H 1 = z) :
    H 0 = ScalarBackward.candidate meanRatio accumulatedBirth z 0 := by
  have hc : ContinuousOn (ScalarBackward.candidate meanRatio accumulatedBirth z)
      (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.div
    · exact meanRatio_continuous.continuousOn.mul continuousOn_const
    · exact continuousOn_const.add (accumulatedBirth_continuous.continuousOn.mul continuousOn_const)
    · intro x hx
      have ha := accumulatedBirth_nonneg x hx.2
      have hw : 0 ≤ 1-z := by linarith [hz.2]
      positivity
  have hd : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      HasDerivAt (ScalarBackward.candidate meanRatio accumulatedBirth z)
        (ScalarBackward.field (birth t) (death t)
          (ScalarBackward.candidate meanRatio accumulatedBirth z t)) t := by
    intro t ht
    apply ScalarBackward.candidate_derivative
    · exact meanRatio_derivative t ht.1.le
    · exact accumulatedBirth_derivative t
    · have ha := accumulatedBirth_nonneg t ht.2
      have hw : 0 ≤ 1-z := by linarith [hz.2]
      positivity
  have he := ScalarBackward.backward_unique birth death H
    (ScalarBackward.candidate meanRatio accumulatedBirth z) 0 1
    (fun t ht => birth_bounds t ⟨ht.1.le, ht.2⟩)
    (fun t ht => death_bounds t ⟨ht.1.le, ht.2⟩)
    hcont hc hderiv hd
    (fun t ht => by have h := hb t ht; constructor <;> linarith [h.1,h.2])
    (fun t ht => candidate_bounds t z ⟨ht.1.le,ht.2⟩ hz)
    (by rw [hterminal, candidate_terminal])
  exact he (by norm_num)

end InheritedCellAssay.ScalarRateSource
