import proofs.HeritableCompositions.GrowthExit

namespace HeritableCompositions
open FiniteCopy

theorem growth_exit_tail (N γ R E t p : ℝ) (hN : 0 ≤ N) (ht : 0 ≤ t)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000) (hR : 2*innerEnergy ≤ R)
    (hgap : E ≤ R-innerEnergy/2)
    (hbound : Real.exp (N*localAlpha*R)*p ≤ Real.exp (N*localAlpha*E)+t*growingCeiling N γ) :
    p ≤ (1+t)*Real.exp (-(N*localAlpha*innerEnergy)/2) := by
  have hα : 0 ≤ N*localAlpha := by unfold localAlpha; positivity
  have hg := mul_le_mul_of_nonneg_left hgap hα
  have hfirst : Real.exp (N*localAlpha*E)*Real.exp (-N*localAlpha*R) ≤
      Real.exp (-(N*localAlpha*innerEnergy)/2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hg]
  have hsecond := mul_le_mul_of_nonneg_left (growing_ceiling_tail N γ R hN hγ hγmax hR) ht
  have hh := mul_le_mul_of_nonneg_right hbound (Real.exp_pos (-N*localAlpha*R)).le
  have hid : Real.exp (N*localAlpha*R)*Real.exp (-N*localAlpha*R) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  have hlhs : Real.exp (N*localAlpha*R)*p*Real.exp (-N*localAlpha*R) = p := by
    calc
      _ = p*(Real.exp (N*localAlpha*R)*Real.exp (-N*localAlpha*R)) := by ring
      _ = p := by rw [hid,mul_one]
  rw [hlhs] at hh
  nlinarith only [hh,hfirst,hsecond]

end HeritableCompositions
