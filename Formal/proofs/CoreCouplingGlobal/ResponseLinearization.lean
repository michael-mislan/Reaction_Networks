import proofs.CoreCouplingGlobal.ResidualCoercivity
import Mathlib.Analysis.Calculus.ContDiff.RCLike

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter Topology

theorem responseA_contDiffAt (e B : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (hB : B ∈ Icc (2:ℝ) 34) : ContDiffAt ℝ (1:ℕ) (responseA e) B := by
  have hd := response_discriminant_pos e B he hu hB.1 hB.2
  unfold responseA
  fun_prop (disch := first | exact ne_of_gt hd | positivity)

theorem responseTotal_hasStrictDerivAt (e B : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (hB : B ∈ Icc (2:ℝ) 34) :
    HasStrictDerivAt (responseTotal e) (responseSlope e B) B := by
  have hc : ContDiffAt ℝ (1:ℕ) (responseTotal e) B :=
    contDiffAt_id.add (responseA_contDiffAt e B he hu hB)
  exact hc.hasStrictDerivAt' (responseTotal_hasDerivAt e B he hu hB.1 hB.2) (by norm_num)

theorem responseSlope_contDiffAt (e B : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (hB : B ∈ Icc (2:ℝ) 34) : ContDiffAt ℝ (1:ℕ) (responseSlope e) B := by
  have hA := responseA_contDiffAt e B he hu hB
  have hbound := (response_bounds e B he hu hB.1 hB.2).1
  have hm := mul_le_mul_of_nonneg_left hbound he
  have hd : 1+2*e*responseA e B ≠ 0 := by nlinarith
  unfold responseSlope
  fun_prop (disch := exact hd)

/-- The literal vector field in (B,z,H,r), with A=responseA(B)+r. -/
noncomputable def responseCoordinateField (e : ℝ) (x : SaddleVector) : SaddleVector :=
  let B := x 0
  let z := x 1
  let H := x 2
  let r := x 3
  let a := 1+e*(2*responseA e B+r)
  let c := responseSlope e B
  let F := 60-(2+z)*B
  let Z := responseTotal e B-(1+z)*B-16*z-4*z^2+3*H
  let K := 16*z+2*z^2-(20001/10000)*H
  ![F+a*r,Z+r,K,-a*(1+c)*r-c*F]

theorem responseCoordinateField_literal (e A B z H : ℝ)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (hB : B ∈ Icc (2:ℝ) 34) :
    responseCoordinateField e ![B,z,H,A+B-responseTotal e B] =
      ![fB (flagshipRates e) A B z,fZ (flagshipRates e) A B z H,
        fH (flagshipRates e) z H,
        fA (flagshipRates e) A B z+fB (flagshipRates e) A B z-
          responseSlope e B*fB (flagshipRates e) A B z] := by
  have hq : responseTotal e B+e*(responseTotal e B-B)^2 = 33+e*B := by
    have hh := response_quadratic e B he hu hB.1 hB.2
    dsimp [responseTotal]
    nlinarith only [hh]
  obtain ⟨hs,hbb,hzz⟩ := response_residual_identities e A B z H (responseTotal e B) hq
  rw [hs,hbb,hzz]
  ext i
  fin_cases i <;> dsimp [responseCoordinateField,responseTotal,fH,flagshipRates] <;> ring

noncomputable def responseCoordinateLinear (B z c a : ℝ) : SaddleVector →ₗ[ℝ] SaddleVector where
  toFun x := ![linearFork B z (x 0) (x 1)+a*x 3,
    linearZ B z c (x 0) (x 1) (x 2)+x 3,linearH z (x 1) (x 2),
    -a*(1+c)*x 3-c*linearFork B z (x 0) (x 1)]
  map_add' x y := by
    ext i
    fin_cases i <;> simp [linearFork,linearZ,linearH] <;> ring
  map_smul' a' x := by
    ext i
    fin_cases i <;> simp [linearFork,linearZ,linearH] <;> ring

theorem responseCoordinateField_hasStrictFDerivAt (e : ℝ) (p : SaddleVector)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (hB : p 0 ∈ Icc (2:ℝ) 34)
    (hr : p 3 = 0) (hF : 60-(2+p 1)*p 0 = 0) :
    HasStrictFDerivAt (responseCoordinateField e)
      (responseCoordinateLinear (p 0) (p 1) (responseSlope e (p 0))
        (1+2*e*responseA e (p 0))).toContinuousLinearMap p := by
  have d0 := hasStrictFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) p
  have d1 := hasStrictFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) p
  have d2 := hasStrictFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) p
  have d3 := hasStrictFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) p
  have dh := (responseTotal_hasStrictDerivAt e (p 0) he hu hB).comp_hasStrictFDerivAt p d0
  have dc := ((responseSlope_contDiffAt e (p 0) he hu hB).hasStrictDerivAt
    (by norm_num)).comp_hasStrictFDerivAt p d0
  have da := ((((dh.sub d0).const_mul 2).add d3).const_mul e).const_add 1
  have dF := ((d1.const_add 2).mul d0).const_sub 60
  have dZ := (((dh.sub ((d1.const_add 1).mul d0)).sub (d1.const_mul 16)).sub
    ((d1.mul d1).const_mul 4)).add (d2.const_mul 3)
  have dK := ((d1.const_mul 16).add ((d1.mul d1).const_mul 2)).sub
    (d2.const_mul (20001/10000))
  have df0 := dF.add (da.mul d3)
  have df1 := dZ.add d3
  have df3 := (((da.mul (dc.const_add 1)).mul d3).neg).sub (dc.mul dF)
  apply hasStrictFDerivAt_pi''
  intro i
  fin_cases i
  · convert df0 using 1
    · funext x
      simp [responseCoordinateField,responseTotal]
    · ext x
      simp [responseCoordinateLinear,linearFork,linearZ,linearH,responseTotal,hr]
      ring
  · convert df1 using 1
    · funext x
      simp [responseCoordinateField,responseTotal]
      ring
    · ext x
      simp [responseCoordinateLinear,linearFork,linearZ,linearH]
      ring
  · convert dK using 1
    · funext x
      simp [responseCoordinateField]
      ring
    · ext x
      simp [responseCoordinateLinear,linearFork,linearZ,linearH]
      ring
  · convert df3 using 1
    · funext x
      simp [responseCoordinateField,responseTotal]
      ring
    · ext x
      simp [responseCoordinateLinear,linearFork,linearZ,linearH,responseTotal,hr,hF]
      ring

theorem strict_derivative_two_point_bound (f : SaddleVector → SaddleVector)
    (L : SaddleVector →L[ℝ] SaddleVector) (p : SaddleVector)
    (hd : HasStrictFDerivAt f L p) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : SaddleVector, dist x p < δ → dist y p < δ →
      ‖f x-f y-L (x-y)‖ ≤ ε*‖x-y‖ := by
  have hb : ∀ᶠ q : SaddleVector × SaddleVector in 𝓝 (p,p),
      ‖f q.1-f q.2-L (q.1-q.2)‖ ≤ ε*‖q.1-q.2‖ := hd.isLittleO.bound hε
  obtain ⟨δ,hδ,hbound⟩ := Metric.eventually_nhds_iff.mp hb
  refine ⟨δ,hδ,?_⟩
  intro x y hx hy
  exact hbound (y := (x,y)) (by simpa only [Prod.dist_eq] using max_lt hx hy)

/-- A two-point remainder bound for the literal response field, rather than
only an expansion with one endpoint fixed at the stationary point. -/
theorem responseCoordinateField_two_point_remainder (e : ℝ) (p : SaddleVector)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (hB : p 0 ∈ Icc (2:ℝ) 34)
    (hr : p 3 = 0) (hF : 60-(2+p 1)*p 0 = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : SaddleVector, dist x p < δ → dist y p < δ →
      ‖responseCoordinateField e x-responseCoordinateField e y-
        responseCoordinateLinear (p 0) (p 1) (responseSlope e (p 0))
          (1+2*e*responseA e (p 0)) (x-y)‖ ≤ ε*‖x-y‖ := by
  exact strict_derivative_two_point_bound _ _ p
    (responseCoordinateField_hasStrictFDerivAt e p he hu hB hr hF) ε hε

end CoreCouplingGlobal
