import proofs.CoreCouplingGlobal.SaddleCoefficients
import proofs.CoreCouplingGlobal.CurveEnergy

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

/-- A robust curvature margin on the entire middle bracket. -/
theorem middle_curvature_numerator_negative (z c : ℝ)
    (hz : z ∈ Icc (19/10:ℝ) (21/10)) (hc : c ≤ 1/500) :
    60*(20001/10000)*(1+c)+
      (16*(20001/10000)+8*(20001/10000)*z-3*(16+4*z))*(z+2)^2 < -7 := by
  have ht : -(1/10:ℝ) ≤ z-2 ∧ z-2 ≤ 1/10 := ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hs : (z-2)^2 ≤ 1/100 := by
    nlinarith [mul_nonneg (show 0 ≤ z-2+1/10 by linarith [ht.1])
      (show 0 ≤ 1/10-(z-2) by linarith [ht.2])]
  have hcube : (z-2)^3 ≤ 1/1000 := by
    have hm := mul_le_mul ht.2 hs (sq_nonneg (z-2)) (by norm_num : (0:ℝ) ≤ 1/10)
    nlinarith only [hm]
  nlinarith only [hc,hs,hcube,ht.2]

/-- Exact value of the candidate quadratic on the response-curve tangent. -/
theorem response_tangent_quadratic_identity (e z : ℝ) (hz : 0 ≤ z) :
    responseQuadratic (60/(z+2)) z (localForkSlope e (60/(z+2)) z)
      (localWeight z) (localHSlope z) (-(60/(z+2))/(z+2)) 1
      ((16+4*z)/(20001/10000)) 0 =
    (60*(20001/10000)*(1+responseSlope e (60/(z+2)))+
      (16*(20001/10000)+8*(20001/10000)*z-3*(16+4*z))*(z+2)^2)/
      (2*(20001/10000)*localWeight z*(z+2)^2) := by
  have h1 : z+1 ≠ 0 := by positivity
  have h2 : z+2 ≠ 0 := by positivity
  have hC : 16+4*z ≠ 0 := by positivity
  have hC' : 16+z*4 ≠ 0 := by positivity
  unfold responseQuadratic localForkSlope localHSlope localWeight
  field_simp
  ring

theorem middle_response_direction_negative (e z : ℝ)
    (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (hz : z ∈ Icc (19/10:ℝ) (21/10)) :
    responseQuadratic (60/(z+2)) z (localForkSlope e (60/(z+2)) z)
      (localWeight z) (localHSlope z) (-(60/(z+2))/(z+2)) 1
      ((16+4*z)/(20001/10000)) 0 < 0 := by
  have hz0 : 0 ≤ z := by linarith [hz.1]
  have hB := curve_B_bounds z ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hc := (response_coefficient_bounds e 0 (60/(z+2)) he hu
    (by norm_num) (by norm_num) hB.1 hB.2).2.2.2
  rw [response_tangent_quadratic_identity e z hz0]
  apply div_neg_of_neg_of_pos
  · linarith [middle_curvature_numerator_negative z _ hz hc]
  · unfold localWeight
    positivity

/-- The linear residual in the compatibility direction has strictly positive gain. -/
theorem middle_linear_tangent_positive (e z : ℝ)
    (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (hz : z ∈ Icc (19/10:ℝ) (21/10)) :
    0 < linearZ (60/(z+2)) z (responseSlope e (60/(z+2)))
      (-(60/(z+2))/(z+2)) 1 ((16+4*z)/(20001/10000)) := by
  have hz0 : 0 ≤ z := by linarith [hz.1]
  have hn := middle_response_direction_negative e z he hu hz
  rw [response_tangent_quadratic_identity e z hz0] at hn
  have hd : 0 < 2*(20001/10000)*localWeight z*(z+2)^2 := by
    unfold localWeight
    positivity
  have hnum := (div_lt_iff₀ hd).1 hn
  simp only [zero_mul] at hnum
  have h2 : z+2 ≠ 0 := by positivity
  have hident : linearZ (60/(z+2)) z (responseSlope e (60/(z+2)))
      (-(60/(z+2))/(z+2)) 1 ((16+4*z)/(20001/10000)) =
      -(60*(20001/10000)*(1+responseSlope e (60/(z+2)))+
        (16*(20001/10000)+8*(20001/10000)*z-3*(16+4*z))*(z+2)^2)/
        ((20001/10000)*(z+2)^2) := by
    unfold linearZ
    field_simp
    ring
  rw [hident]
  exact div_pos (neg_pos.mpr hnum) (by positivity)

/-- No nonzero displacement annihilates all four linear response residuals. -/
theorem middle_linear_residual_kernel (e z b ζ η r : ℝ)
    (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (hz : z ∈ Icc (19/10:ℝ) (21/10))
    (hF : linearFork (60/(z+2)) z b ζ = 0)
    (hZ : linearZ (60/(z+2)) z (responseSlope e (60/(z+2))) b ζ η = 0)
    (hK : linearH z ζ η = 0) (hr : r = 0) :
    b = 0 ∧ ζ = 0 ∧ η = 0 ∧ r = 0 := by
  have hz0 : 0 ≤ z := by linarith [hz.1]
  have h2 : z+2 ≠ 0 := by positivity
  have hb : b = (-(60/(z+2))/(z+2))*ζ := by
    unfold linearFork at hF
    have hb' : b = -(60/(z+2)*ζ)/(z+2) := by
      apply (eq_div_iff h2).2
      nlinarith only [hF]
    rw [hb']
    ring
  have hη : η = ((16+4*z)/(20001/10000))*ζ := by
    unfold linearH at hK
    linarith only [hK]
  have hgain := middle_linear_tangent_positive e z he hu hz
  have hmul : ζ*(linearZ (60/(z+2)) z (responseSlope e (60/(z+2)))
      (-(60/(z+2))/(z+2)) 1 ((16+4*z)/(20001/10000))) = 0 := by
    rw [hb,hη] at hZ
    convert hZ using 1
    unfold linearZ
    ring
  have hζ : ζ = 0 := (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hgain)
  exact ⟨by simpa [hζ] using hb,hζ,by simpa [hζ] using hη,hr⟩

/-- Both quadratic signs are bound to a literal middle stationary state. -/
theorem middle_stationary_quadratic_sides (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (s : State) (hs : s.Positive) (hstat : Stationary (flagshipRates e) s)
    (hz : s.z ∈ Icc (19/10:ℝ) (21/10)) :
    responseQuadratic s.B s.z (localForkSlope e s.B s.z) (localWeight s.z)
      (localHSlope s.z) (-s.B/(s.z+2)) 1 ((16+4*s.z)/(20001/10000)) 0 < 0 ∧
    ∀ ζ η r : ℝ, ζ ≠ 0 ∨ η ≠ 0 ∨ r ≠ 0 →
      0 < responseQuadratic s.B s.z (localForkSlope e s.B s.z) (localWeight s.z)
        (localHSlope s.z) 0 ζ η r := by
  have hB : s.B = 60/(s.z+2) := by
    have ha := hstat.1
    have hb := hstat.2.1
    dsimp [fA,fB,flagshipRates] at ha hb
    apply (eq_div_iff (by have := hs.2.2.1; positivity : s.z+2 ≠ 0)).2
    linear_combination -ha-2*hb
  constructor
  · rw [hB]
    exact middle_response_direction_negative e s.z he hu hz
  · exact state_quadratic_B_plane_positive e s hs
      (stationary_B_ge_eight e s hs hstat (by linarith [hz.2]))

end CoreCouplingGlobal
