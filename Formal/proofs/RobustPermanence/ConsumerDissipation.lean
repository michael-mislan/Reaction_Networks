import proofs.RobustPermanence.DeficitGap
import proofs.CoreCouplingGlobal.ResponseDissipation

namespace RobustPermanence
open CoreCouplingGlobal CoreCouplingCAC

noncomputable def potentialRate (e A B z H X : ℝ) : ℝ :=
  (Real.log (z+2)-responseSlope e B*responseLog z+responsePIntegrand e B)*
      fB (flagshipRates e) A B z
    -(responseTotal e B-(1+z)*B-16*z-4*z^2+3*H)/((z+1)*(z+2))*
      (fZ (flagshipRates e) A B z H-z*X)
    +3*(responseLog (responsePhi H)-responseLog z)*fH (flagshipRates e) z H
    +(A+B-responseTotal e B)*(fA (flagshipRates e) A B z+
      fB (flagshipRates e) A B z-responseSlope e B*fB (flagshipRates e) A B z)

theorem resource_gradient_upper (e B z H : ℝ)
    (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (hB : 2 ≤ B) (hB' : B ≤ 34) (hz : 0 ≤ z)
    (hH : H ≤ 1536/7) :
    (responseTotal e B-(1+z)*B-16*z-4*z^2+3*H)/((z+1)*(z+2))*z ≤ 400 := by
  have ha := (response_bounds e B he he' hB hB').2
  have htot : responseTotal e B ≤ 67 := by dsimp [responseTotal]; linarith
  have hBz := mul_nonneg (by linarith : 0 ≤ 1+z) (by linarith : 0 ≤ B)
  have hZ : responseTotal e B-(1+z)*B-16*z-4*z^2+3*H ≤ 2000 := by
    nlinarith only [htot,hBz,hz,hH,sq_nonneg z]
  have hw : 0 < (z+1)*(z+2) := by positivity
  have hzw : z / ((z+1)*(z+2)) ≤ 1/5 := by
    apply (div_le_iff₀ hw).2
    nlinarith only [sq_nonneg (z-1)]
  have hprod := mul_le_mul_of_nonneg_right hZ (div_nonneg hz (le_of_lt hw))
  calc
    _ = (responseTotal e B-(1+z)*B-16*z-4*z^2+3*H)*(z/((z+1)*(z+2))) := by ring
    _ ≤ 2000*(z/((z+1)*(z+2))) := hprod
    _ ≤ 400 := by linarith only [hzw]

theorem consumer_potential_dissipation (e A B z H X : ℝ)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (hA : 0 ≤ A) (hA' : A ≤ 34)
    (hB : 2 ≤ B) (hB' : B ≤ 34) (hz : 0 ≤ z) (hz' : z ≤ 12)
    (hH : 0 ≤ H) (hH' : H ≤ 1536/7) (hX : 0 ≤ X) :
    potentialRate e A B z H X ≤
      -dissipation (A+B-responseTotal e B) (60-(2+z)*B)
        (responseTotal e B-(1+z)*B-16*z-4*z^2+3*H)
        (16*z+2*z^2-(20001/10000)*H) + 400*X := by
  have hd := response_directional_dissipation e A B z H he he' hA hA'
    hB hB' hz hz' hH hH'
  dsimp only at hd
  have hh : fH (flagshipRates e) z H = 16*z+2*z^2-(20001/10000)*H := by
    dsimp [fH,flagshipRates]
    ring
  have hgrad := mul_le_mul_of_nonneg_right
    (resource_gradient_upper e B z H he he' hB hB' hz hH') hX
  dsimp [potentialRate,dissipation]
  rw [hh] at hd ⊢
  nlinarith only [hd,hgrad]

/-- Actual literal feedback satisfies the differential inequality needed by the
bounded corrector. The slightly coarser feedback constant avoids optimizing a floor. -/
theorem consumer_corrected_growth (e A B z H X : ℝ)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (hA : 0 ≤ A) (hA' : A ≤ 34)
    (hB : 2 ≤ B) (hB' : B ≤ 34) (hz : 0 ≤ z) (hz' : z ≤ 12)
    (hH : 0 ≤ H) (hH' : H ≤ 1536/7) (hX : 0 ≤ X) :
    X*(1/4-60000001*X) ≤ X*(z-1/2-X)-150000*X*potentialRate e A B z H X := by
  let D := dissipation (A+B-responseTotal e B) (60-(2+z)*B)
    (responseTotal e B-(1+z)*B-16*z-4*z^2+3*H)
    (16*z+2*z^2-(20001/10000)*H)
  have hD : 0 ≤ D := dissipation_nonneg _ _ _ _
  have hgap : z ≤ 3/4 → 529/103640000 ≤ D := by
    intro hlow
    exact residual_gap _ _ _ _ (low_resource_separation e B z H he he' hB hB' hz hlow)
  have hg := mul_le_mul_of_nonneg_right (corrected_boundary_growth z D hz hD hgap) hX
  have hp := mul_le_mul_of_nonneg_left
    (consumer_potential_dissipation e A B z H X he he' hA hA' hB hB' hz hz' hH hH' hX)
    (by positivity : 0 ≤ 150000*X)
  change 150000*X*potentialRate e A B z H X ≤ 150000*X*(-D+400*X) at hp
  nlinarith only [hg,hp]

end RobustPermanence
