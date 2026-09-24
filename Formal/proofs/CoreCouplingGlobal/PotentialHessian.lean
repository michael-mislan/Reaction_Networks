import proofs.CoreCouplingGlobal.PerturbedQuadratic

namespace CoreCouplingGlobal
open Set

theorem responseLog_hasStrictDerivAt (z : ℝ) (hz : -1 < z) :
    HasStrictDerivAt responseLog (1/((z+1)*(z+2))) z := by
  have hc : ContDiffAt ℝ (1:ℕ) responseLog z := by
    unfold responseLog
    fun_prop (disch := linarith)
  exact hc.hasStrictDerivAt' (responseLog_hasDerivAt z hz) (by norm_num)

theorem responsePhi_at_natural (z : ℝ) (hz : 0 ≤ z) :
    responsePhi ((16*z+2*z^2)/(20001/10000)) = z := by
  have hs : Real.sqrt (256+8*(20001/10000:ℝ)*((16*z+2*z^2)/(20001/10000))) = 16+4*z := by
    have hi : (256+8*(20001/10000:ℝ)*((16*z+2*z^2)/(20001/10000))) = (16+4*z)^2 := by ring
    rw [hi, Real.sqrt_sq (by positivity)]
  unfold responsePhi
  rw [hs]
  field_simp
  ring

theorem responsePhi_hasStrictDerivAt_natural (z : ℝ) (hz : 0 ≤ z) :
    HasStrictDerivAt responsePhi ((20001/10000)/(16+4*z))
      ((16*z+2*z^2)/(20001/10000)) := by
  let H := (16*z+2*z^2)/(20001/10000)
  have hs : Real.sqrt (256+8*(20001/10000:ℝ)*H) = 16+4*z := by
    have hi : 256+8*(20001/10000:ℝ)*H = (16+4*z)^2 := by dsimp [H]; ring
    rw [hi,Real.sqrt_sq (by positivity)]
  have hd : 256+8*(20001/10000:ℝ)*H ≠ 0 := by dsimp [H]; positivity
  have d := hasStrictDerivAt_id H
  have ds := ((d.const_mul (8*(20001/10000))).const_add 256).sqrt hd
  have dn : 16+Real.sqrt (256+8*(20001/10000:ℝ)*H) ≠ 0 := by positivity
  convert (d.const_mul (2*(20001/10000))).div (ds.const_add 16) dn using 1
  · simp only [id_eq]
    rw [hs]
    dsimp [H]
    have hc : 16+4*z ≠ 0 := by positivity
    have hc' : 16+z*4 ≠ 0 := by positivity
    field_simp
    ring

/-- The actual potential gradient in response coordinates (B,z,H,r). -/
noncomputable def potentialGradient (e : ℝ) (x : SaddleVector) : SaddleVector :=
  ![Real.log (x 1+2)-responseSlope e (x 0)*responseLog (x 1)+responsePIntegrand e (x 0),
    -(responseTotal e (x 0)-(1+x 1)*x 0-16*x 1-4*(x 1)^2+3*x 2)/localWeight (x 1),
    3*(responseLog (responsePhi (x 2))-responseLog (x 1)), x 3]

/-- At stationary response balance the derivative of the actual gradient
is exactly the linear map defining the saddle quadratic. -/
theorem potentialGradient_hasStrictFDerivAt (e z : ℝ)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (hz : z ∈ Icc (19/10:ℝ) (21/10))
    (hZ : responseTotal e (60/(z+2))-(1+z)*(60/(z+2))-16*z-4*z^2+
      3*((16*z+2*z^2)/(20001/10000)) = 0) :
    HasStrictFDerivAt (potentialGradient e) (saddleGradient e z).toContinuousLinearMap
      ![60/(z+2),z,(16*z+2*z^2)/(20001/10000),0] := by
  let B := 60/(z+2)
  let H := (16*z+2*z^2)/(20001/10000)
  let p : SaddleVector := ![B,z,H,0]
  have hz0 : 0 ≤ z := by linarith [hz.1]
  have hz1 : z+1 ≠ 0 := by positivity
  have hz2 : z+2 ≠ 0 := by positivity
  have hB := curve_B_bounds z ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hB0 : B ≠ 0 := by dsimp [B]; positivity
  have hratio : 60/B = z+2 := by dsimp [B]; field_simp
  have hratio' : 60/B-2 = z := by rw [hratio]; ring
  have d0 := hasStrictFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) p
  have d1 := hasStrictFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) p
  have d2 := hasStrictFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) p
  have d3 := hasStrictFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) p
  have dh := (responseTotal_hasStrictDerivAt e B he hu hB).comp_hasStrictFDerivAt p d0
  have dc := ((responseSlope_contDiffAt e B he hu hB).hasStrictDerivAt
    (by norm_num)).comp_hasStrictFDerivAt p d0
  have dl := (responseLog_hasStrictDerivAt z (by linarith)).comp_hasStrictFDerivAt p d1
  have drat := ((hasStrictDerivAt_inv hB0).comp_hasStrictFDerivAt p d0).const_mul 60
  have drl := (responseLog_hasStrictDerivAt (60/B-2)
    (by rw [hratio']; linarith)).comp_hasStrictFDerivAt p (drat.sub_const 2)
  have dgb := ((d1.add_const 2).log hz2).sub (dc.mul dl)
  have dgb' := dgb.add ((drat.log (by change 60/B ≠ 0; rw [hratio]; exact hz2)).neg.add (dc.mul drl))
  have dZ := (((dh.sub ((d1.const_add 1).mul d0)).sub (d1.const_mul 16)).sub
    ((d1.mul d1).const_mul 4)).add (d2.const_mul 3)
  have dw := (d1.add_const 1).mul (d1.add_const 2)
  have dwi := (hasStrictDerivAt_inv (mul_ne_zero hz1 hz2)).comp_hasStrictFDerivAt p dw
  have dgz := dZ.neg.mul dwi
  have dphi := (responsePhi_hasStrictDerivAt_natural z hz0).comp_hasStrictFDerivAt p d2
  have dlp := (responseLog_hasStrictDerivAt (responsePhi H)
    (by dsimp [H]; rw [responsePhi_at_natural z hz0]; linarith)).comp_hasStrictFDerivAt p dphi
  have dgH := (dlp.sub dl).const_mul 3
  apply hasStrictFDerivAt_pi''
  intro i
  fin_cases i
  · convert dgb' using 1
    ext x
    simp [saddleGradient,localForkSlope,localWeight,p,← div_eq_mul_inv,hratio]
    dsimp [B]
    field_simp
    ring
  · convert dgz using 1
    · funext x
      simp [potentialGradient,localWeight,div_eq_mul_inv,pow_two]
    · ext x
      simp [saddleGradient,localForkSlope,localWeight,p]
      have hZ' : -(3*H)+(4*(z*z)-(responseTotal e B-(1+z)*B-16*z)) = 0 := by
        dsimp [B,H]
        nlinarith only [hZ]
      rw [hZ']
      dsimp [B]
      field_simp
      ring
  · convert dgH using 1
    ext x
    simp [saddleGradient,localHSlope,localWeight,H,responsePhi_at_natural z hz0]
    have hc : 16+4*z ≠ 0 := by positivity
    have hc' : 16+z*4 ≠ 0 := by positivity
    field_simp
    ring
  · exact d3

theorem potentialGradient_at_stationary (e z : ℝ) (hz : 0 ≤ z)
    (hZ : responseTotal e (60/(z+2))-(1+z)*(60/(z+2))-16*z-4*z^2+
      3*((16*z+2*z^2)/(20001/10000)) = 0) :
    potentialGradient e ![60/(z+2),z,(16*z+2*z^2)/(20001/10000),0] = 0 := by
  have hratio : 60/(60/(z+2)) = z+2 := by
    have hd : z+2 ≠ 0 := by positivity
    field_simp
  ext i
  fin_cases i <;>
    simp [potentialGradient,responsePIntegrand,hratio,hZ,responsePhi_at_natural z hz]

/-- This is the gradient of the constructed potential, for arbitrary curves
inside the primitive domains, not merely along solutions of the ODE. -/
theorem responsePotential_gradient_hasDerivAt (e : ℝ) (P : PotentialPrimitives e)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (x : ℝ → SaddleVector)
    (v : SaddleVector) (t : ℝ) (hx : HasDerivAt x v t)
    (hB : x t 0 ∈ Icc (2:ℝ) 34) (hz : x t 1 ∈ Icc (0:ℝ) 12)
    (hH : x t 2 ∈ Icc (0:ℝ) (1536/7)) :
    HasDerivAt (fun s => responsePotential e P (x s 0) (x s 1) (x s 2) (x s 3))
      (saddlePairing (potentialGradient e (x t)) v) t := by
  have hd := responsePotential_hasDerivAt e P he hu
    (fun s => x s 0) (fun s => x s 1) (fun s => x s 2) (fun s => x s 3)
    t (v 0) (v 1) (v 2) (v 3) hB hz hH
    ((hasDerivAt_pi.mp hx) 0) ((hasDerivAt_pi.mp hx) 1)
    ((hasDerivAt_pi.mp hx) 2) ((hasDerivAt_pi.mp hx) 3)
  convert hd using 1
  simp [saddlePairing,potentialGradient,localWeight,Fin.sum_univ_succ]
  ring

theorem potentialGradient_linear_remainder (e z : ℝ)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (hz : z ∈ Icc (19/10:ℝ) (21/10))
    (hZ : responseTotal e (60/(z+2))-(1+z)*(60/(z+2))-16*z-4*z^2+
      3*((16*z+2*z^2)/(20001/10000)) = 0) (ε : ℝ) (hε : 0 < ε) :
    let p : SaddleVector := ![60/(z+2),z,(16*z+2*z^2)/(20001/10000),0]
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : SaddleVector, dist x p < δ →
      ‖potentialGradient e x-saddleGradient e z (x-p)‖ ≤ ε*‖x-p‖ := by
  dsimp only
  let p : SaddleVector := ![60/(z+2),z,(16*z+2*z^2)/(20001/10000),0]
  obtain ⟨δ,hδ,hr⟩ := strict_derivative_two_point_bound (potentialGradient e)
    (saddleGradient e z).toContinuousLinearMap p
    (potentialGradient_hasStrictFDerivAt e z he hu hz hZ) ε hε
  refine ⟨δ,hδ,?_⟩
  intro x hx
  have hzero : potentialGradient e p = 0 :=
    potentialGradient_at_stationary e z (by linarith [hz.1]) hZ
  simpa only [hzero,sub_zero] using hr x p hx (by simpa using hδ)

end CoreCouplingGlobal
