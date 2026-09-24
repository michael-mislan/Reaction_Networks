import proofs.HeritableCompositions.RecoveryBudget
import proofs.FiniteCopy.LocalExponentialRate

namespace ProductiveMemory
open FiniteCopy HeritableCompositions
set_option Elab.async false

noncomputable def extractionGrowingCeiling (N γ : ℝ) : ℝ :=
  localAlpha*(200000000+8000000000*N*γ^2)*
    Real.exp (48000000000*localAlpha+1920000000000*localAlpha*N*γ^2)

theorem extractionGrowingCeiling_nonneg (N γ : ℝ) (hN : 0 ≤ N) : 0 ≤ extractionGrowingCeiling N γ := by
  unfold extractionGrowingCeiling localAlpha
  positivity

theorem extraction_growing_envelope (N γ v E : ℝ) (hN : 0 ≤ N) (hv : 0 ≤ v)
    (hE : E ≤ 60*v) :
    localAlpha*Real.exp (N*localAlpha*E)*(-N/4*v+200000000+8000000000*N*γ^2) ≤
      extractionGrowingCeiling N γ := by
  have hNE := mul_le_mul_of_nonneg_left hE hN
  have hNv := mul_nonneg hN hv
  have hα : 0 ≤ localAlpha := by norm_num [localAlpha]
  by_cases hb : -N/4*v+200000000+8000000000*N*γ^2 ≤ 0
  · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) hb).trans (extractionGrowingCeiling_nonneg N γ hN)
  · have he : N*localAlpha*E ≤ 48000000000*localAlpha+1920000000000*localAlpha*N*γ^2 := by
      unfold localAlpha
      nlinarith only [hNE,not_le.mp hb]
    have hexp := Real.exp_le_exp.mpr he
    have hbr : -N/4*v+200000000+8000000000*N*γ^2 ≤ 200000000+8000000000*N*γ^2 := by
      nlinarith only [hNv]
    have hfirst := mul_le_mul_of_nonneg_left hbr (by positivity : 0 ≤ localAlpha*Real.exp (N*localAlpha*E))
    have hsecond := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ localAlpha*(200000000+8000000000*N*γ^2))
    unfold extractionGrowingCeiling
    nlinarith only [hfirst,hsecond]

theorem extraction_growing_budget (N γ : ℝ) (hN : 200000000000000000000 ≤ N)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000) :
    200000000+8000000000*N*γ^2 ≤ N*innerEnergy/960 := by
  have hNs : 0 ≤ N := by linarith only [hN]
  have hg : γ^2 ≤ (1/100000000000 : ℝ)^2 := by nlinarith only [hγ,hγmax]
  have hng := mul_le_mul_of_nonneg_left hg hNs
  norm_num [innerEnergy,outerEnergy] at *
  nlinarith only [hN,hng]

/-- Affine exponential Foster bound: the recovery floor is A/2, permitting
recovery at a deterministic time instead of a random visit-time restart. -/
theorem extraction_growing_affine (N γ v E : ℝ)
    (hN : 200000000000000000000 ≤ N) (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (hv : 0 ≤ v) (hE : E ≤ 60*v) :
    localAlpha*Real.exp (N*localAlpha*E)*(-N/4*v+200000000+8000000000*N*γ^2) ≤
      -(N*localAlpha*innerEnergy/960)*Real.exp (N*localAlpha*E)+
        (N*localAlpha*innerEnergy/960)*(2*Real.exp (N*localAlpha*innerEnergy/2)) := by
  have hNs : 0 ≤ N := by linarith only [hN]
  have hα : 0 ≤ localAlpha := by norm_num [localAlpha]
  have hA : 0 ≤ innerEnergy := by norm_num [innerEnergy,outerEnergy]
  have hb := extraction_growing_budget N γ hN hγ hγmax
  have hNE := mul_le_mul_of_nonneg_left hE hNs
  have hNv := mul_nonneg hNs hv
  by_cases hlarge : innerEnergy/2 ≤ E
  · have hNA := mul_le_mul_of_nonneg_left hlarge hNs
    have hbr : -N/4*v+200000000+8000000000*N*γ^2 ≤ -N*innerEnergy/960 := by
      nlinarith only [hb,hNE,hNA]
    have hh := mul_le_mul_of_nonneg_left hbr (by positivity : 0 ≤ localAlpha*Real.exp (N*localAlpha*E))
    have hp : 0 ≤ (N*localAlpha*innerEnergy/960)*(2*Real.exp (N*localAlpha*innerEnergy/2)) := by positivity
    nlinarith only [hh,hp]
  · have hexp : Real.exp (N*localAlpha*E) ≤ Real.exp (N*localAlpha*innerEnergy/2) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left (le_of_lt (not_le.mp hlarge)) (mul_nonneg hNs hα)
      nlinarith only [hh]
    have hbr : -N/4*v+200000000+8000000000*N*γ^2+N*innerEnergy/960 ≤ N*innerEnergy/480 := by
      nlinarith only [hb,hNv]
    have hfirst := mul_le_mul_of_nonneg_left hbr (by positivity : 0 ≤ localAlpha*Real.exp (N*localAlpha*E))
    have hsecond := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ N*localAlpha*innerEnergy/480)
    nlinarith only [hfirst,hsecond]

end ProductiveMemory
