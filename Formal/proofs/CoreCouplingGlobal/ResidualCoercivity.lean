import proofs.CoreCouplingGlobal.MiddleQuadratic
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace CoreCouplingGlobal
open Set

/-- Displacements are ordered (B,z,H,response error), not physical state coordinates. -/
abbrev SaddleVector := Fin 4 → ℝ

noncomputable def saddleResidualMap (e z : ℝ) : SaddleVector →ₗ[ℝ] SaddleVector where
  toFun x := ![linearFork (60/(z+2)) z (x 0) (x 1),
    linearZ (60/(z+2)) z (responseSlope e (60/(z+2))) (x 0) (x 1) (x 2),
    linearH z (x 1) (x 2),x 3]
  map_add' x y := by
    ext i
    fin_cases i <;> simp [linearFork,linearZ,linearH] <;> ring
  map_smul' a x := by
    ext i
    fin_cases i <;> simp [linearFork,linearZ,linearH] <;> ring

theorem middle_residual_map_injective (e z : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (hz : z ∈ Icc (19/10:ℝ) (21/10)) : Function.Injective (saddleResidualMap e z) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  have h2 := congrFun hx 2
  have h3 := congrFun hx 3
  simp only [saddleResidualMap,LinearMap.coe_mk,AddHom.coe_mk,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Pi.zero_apply] at h0 h1 h2 h3
  obtain ⟨hb,hz',hH,hr⟩ := middle_linear_residual_kernel e z (x 0) (x 1) (x 2) (x 3)
    he hu hz h0 h1 h2 h3
  ext i
  fin_cases i <;> simp_all

theorem saddle_vector_norm_sq_le (x : SaddleVector) :
    ‖x‖^2 ≤ (x 0)^2+(x 1)^2+(x 2)^2+(x 3)^2 := by
  let S := (x 0)^2+(x 1)^2+(x 2)^2+(x 3)^2
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hsqrt := Real.sq_sqrt hS
  have hnorm : ‖x‖ ≤ Real.sqrt S := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg S)).2
    intro i
    fin_cases i <;> simp only [Real.norm_eq_abs]
    all_goals
      have h0 := sq_nonneg (x 0)
      have h1 := sq_nonneg (x 1)
      have h2 := sq_nonneg (x 2)
      have h3 := sq_nonneg (x 3)
      have hsqrt0 := Real.sqrt_nonneg S
      dsimp [S] at *
      nlinarith [sq_abs (x 0),sq_abs (x 1),sq_abs (x 2),sq_abs (x 3),
        abs_nonneg (x 0),abs_nonneg (x 1),abs_nonneg (x 2),abs_nonneg (x 3)]
  nlinarith [norm_nonneg x,Real.sqrt_nonneg S]

noncomputable def saddleLinearDissipation (e z : ℝ) (x : SaddleVector) : ℝ :=
  (x 3)^2/4+(linearFork (60/(z+2)) z (x 0) (x 1))^2/1000+
    (linearZ (60/(z+2)) z (responseSlope e (60/(z+2))) (x 0) (x 1) (x 2))^2/364+
    (linearH z (x 1) (x 2))^2/4000

/-- Strict linear residual dissipation controls the whole displacement norm.
The positive constant may depend on e and the chosen middle-bracket z. -/
theorem middle_residual_coercivity (e z : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (hz : z ∈ Icc (19/10:ℝ) (21/10)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ x : SaddleVector, κ*‖x‖^2 ≤ saddleLinearDissipation e z x := by
  obtain ⟨C,hC,hbound⟩ := (saddleResidualMap e z).injective_iff_antilipschitz.mp
    (middle_residual_map_injective e z he hu hz)
  have hC0 : 0 < (C : ℝ) := hC
  refine ⟨1/(4000*(C:ℝ)^2),by positivity,?_⟩
  intro x
  have hn : ‖x‖ ≤ (C:ℝ)*‖saddleResidualMap e z x‖ := by
    simpa only [map_zero,dist_zero_right] using hbound.le_mul_dist x 0
  have hn2 : ‖x‖^2 ≤ (C:ℝ)^2*‖saddleResidualMap e z x‖^2 := by
    nlinarith [norm_nonneg x,norm_nonneg (saddleResidualMap e z x)]
  have hsq := saddle_vector_norm_sq_le (saddleResidualMap e z x)
  have hres : ‖saddleResidualMap e z x‖^2 ≤ 4000*saddleLinearDissipation e z x := by
    change ‖saddleResidualMap e z x‖^2 ≤
      (linearFork (60/(z+2)) z (x 0) (x 1))^2+
      (linearZ (60/(z+2)) z (responseSlope e (60/(z+2))) (x 0) (x 1) (x 2))^2+
      (linearH z (x 1) (x 2))^2+(x 3)^2 at hsq
    unfold saddleLinearDissipation
    nlinarith [sq_nonneg (x 3),sq_nonneg (linearFork (60/(z+2)) z (x 0) (x 1)),
      sq_nonneg (linearZ (60/(z+2)) z (responseSlope e (60/(z+2))) (x 0) (x 1) (x 2))]
  have hm := mul_le_mul_of_nonneg_left hres (sq_nonneg (C:ℝ))
  rw [one_div,mul_comm,← div_eq_mul_inv]
  apply (div_le_iff₀ (by positivity : 0 < 4000*(C:ℝ)^2)).2
  nlinarith only [hn2,hm]

noncomputable def saddleQuadraticRate (e z a : ℝ) (x : SaddleVector) : ℝ :=
  let B := 60/(z+2)
  let c := responseSlope e B
  let m := localForkSlope e B z
  let w := localWeight z
  let n := localHSlope z
  let F := linearFork B z (x 0) (x 1)
  let Z := linearZ B z c (x 0) (x 1) (x 2)
  let K := linearH z (x 1) (x 2)
  (m*(2+z)*x 0+m*B*x 1)*(F+a*x 3)+
    (m*B*x 0+(B+16+8*z)*x 1/w-3*x 2/w)*(Z+x 3)+
    (-3*x 1/w+n*(20001/10000)*x 2)*K+x 3*(-a*(1+c)*x 3-c*F)

/-- The certified quadratic directional derivative dissipates strictly relative
to displacement norm, uniformly in the allowed local relaxation coefficient a. -/
theorem middle_quadratic_rate_coercive (e z : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (hz : z ∈ Icc (19/10:ℝ) (21/10)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ a : ℝ, 99/100 ≤ a → a ≤ 101/100 →
      ∀ x : SaddleVector, saddleQuadraticRate e z a x ≤ -(κ*‖x‖^2) := by
  obtain ⟨κ,hκ,hbound⟩ := middle_residual_coercivity e z he hu hz
  have hB := curve_B_bounds z ⟨by linarith [hz.1],by linarith [hz.2]⟩
  obtain ⟨_,_,hc,hc',hm,hm',hw,hw',hn,hcross,hH⟩ :=
    local_response_coefficients e 0 (60/(z+2)) z he hu (by norm_num) (by norm_num)
      hB.1 hB.2 (by linarith [hz.1]) (by linarith [hz.2])
  refine ⟨κ,hκ,?_⟩
  intro a ha ha' x
  have hd := responseQuadratic_directional_bound (60/(z+2)) z a
    (responseSlope e (60/(z+2))) (localForkSlope e (60/(z+2)) z)
    (localWeight z) (localHSlope z) (x 0) (x 1) (x 2) (x 3)
    ha ha' hc hc' hm hm' hw hw' hn hcross hH
  have hd' : saddleQuadraticRate e z a x ≤ -saddleLinearDissipation e z x := by
    dsimp only [saddleQuadraticRate,saddleLinearDissipation]
    convert hd using 1
    ring
  exact hd'.trans (neg_le_neg (hbound x))

end CoreCouplingGlobal
