import proofs.CoreCouplingGlobal.ResponsePotential
import proofs.CoreCouplingGlobal.TrajectoryBounds

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

theorem responsePotential_hasDerivAt (e : ℝ) (p : PotentialPrimitives e)
    (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (B z H r : ℝ → ℝ) (t b' z' H' r' : ℝ)
    (hB : B t ∈ Icc (2:ℝ) 34) (hz : z t ∈ Icc (0:ℝ) 12)
    (hH : H t ∈ Icc (0:ℝ) (1536/7))
    (dB : HasDerivAt B b' t) (dz : HasDerivAt z z' t)
    (dH : HasDerivAt H H' t) (dr : HasDerivAt r r' t) :
    HasDerivAt (fun s => responsePotential e p (B s) (z s) (H s) (r s))
      ((Real.log (z t+2)-responseSlope e (B t)*responseLog (z t)+responsePIntegrand e (B t))*b'
      -(responseTotal e (B t)-(1+z t)*B t-16*z t-4*(z t)^2+3*H t)/
        ((z t+1)*(z t+2))*z'
      +3*(responseLog (responsePhi (H t))-responseLog (z t))*H'+r t*r') t := by
  have hz₁ : z t+1 ≠ 0 := by linarith [hz.1]
  have hz₂ : z t+2 ≠ 0 := by linarith [hz.1]
  have dl := (responseLog_hasDerivAt (z t) (by linarith [hz.1])).comp t dz
  have dh := (responseTotal_hasDerivAt e (B t) he he' hB.1 hB.2).comp t dB
  have hv := (((((dB.mul ((dz.add_const 2).log hz₂)).sub (dh.mul dl)).add
    ((p.derivU (z t) hz).comp t dz)).sub ((dH.const_mul 3).mul dl)).add
    ((p.derivP (B t) hB).comp t dB)).add ((p.derivR (H t) hH).comp t dH)
  have hv' := hv.add ((dr.pow 2).div_const 2)
  convert hv' using 1
  simp only [Function.comp_apply]
  field_simp
  ring

theorem response_directional_dissipation (e A B z H : ℝ)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (hA : 0 ≤ A) (hA' : A ≤ 34)
    (hB : 2 ≤ B) (hB' : B ≤ 34) (hz : 0 ≤ z) (hz' : z ≤ 12)
    (hH : 0 ≤ H) (hH' : H ≤ 1536/7) :
    let r := A+B-responseTotal e B
    let F := 60-(2+z)*B
    let Z := responseTotal e B-(1+z)*B-16*z-4*z^2+3*H
    let K := fH (flagshipRates e) z H
    (Real.log (z+2)-responseSlope e B*responseLog z+responsePIntegrand e B)*
        fB (flagshipRates e) A B z
      -Z/((z+1)*(z+2))*fZ (flagshipRates e) A B z H
      +3*(responseLog (responsePhi H)-responseLog z)*K
      +r*(fA (flagshipRates e) A B z+fB (flagshipRates e) A B z-
        responseSlope e B*fB (flagshipRates e) A B z) ≤
      -r^2/4-F^2/1000-Z^2/364-K^2/4000 := by
  dsimp only
  obtain ⟨ha,ha',hc,hc'⟩ := response_coefficient_bounds e A B he he' hA hA' hB hB'
  obtain ⟨m,hm,hm',hmv⟩ := fork_gradient_secant B (responseSlope e B) z hB hB' hz hz' hc hc'
  obtain ⟨n,hn,hnv⟩ := H_gradient_secant H z hH hH' hz hz'
  have hq : responseTotal e B+e*(responseTotal e B-B)^2 = 33+e*B := by
    have hh := response_quadratic e B he he' hB hB'
    dsimp [responseTotal]
    nlinarith only [hh]
  obtain ⟨hs,hbb,hzz⟩ := response_residual_identities e A B z H (responseTotal e B) hq
  have haeq : 1+e*(A+responseTotal e B-B) = 1+e*(A+responseA e B) := by
    dsimp [responseTotal]; ring
  rw [haeq] at hs hbb
  have hgrad : Real.log (z+2)-responseSlope e B*responseLog z+responsePIntegrand e B =
      -m*(60-(2+z)*B) := by
    dsimp [responsePIntegrand]
    linarith only [hmv]
  have hk : fH (flagshipRates e) z H = 16*z+2*z^2-(20001/10000)*H := by
    dsimp [fH,flagshipRates]; ring
  rw [← hk] at hnv
  have hw : 2 ≤ (z+1)*(z+2) := by nlinarith
  have hw' : (z+1)*(z+2) ≤ 182 := by nlinarith [sq_nonneg (z-12)]
  have henergy := response_energy_dissipation (1+e*(A+responseA e B)) (responseSlope e B)
    m ((z+1)*(z+2)) (A+B-responseTotal e B) (60-(2+z)*B)
    (responseTotal e B-(1+z)*B-16*z-4*z^2+3*H) (fH (flagshipRates e) z H) n
    ha ha' hc hc' hm hm' hw hw' hn
  rw [hgrad,hnv,hs,hbb,hzz]
  convert henergy using 1
  ring

end CoreCouplingGlobal
