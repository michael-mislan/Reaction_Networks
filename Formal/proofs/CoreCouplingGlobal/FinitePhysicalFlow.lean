import proofs.CoreCouplingGlobal.FiniteVariation

namespace CoreCouplingGlobal
open Set Filter
open scoped Topology ContDiff BoundedContinuousFunction

theorem physicalTrajectoryMatrix_vector (e σ : ℝ) (a : PerronSpace)
    (v : ResponseVector) (t : ℝ) :
    (fun i => ∑ j, physicalTrajectoryMatrix e σ a i j t*v j)=
      σ • (physicalJacobian e (fun i => a i t)).toLin' v := by
  let w : PerronSpace := fun i => BoundedContinuousFunction.const ℝ (v i)
  simpa only [trajectoryMatrix_apply,w,BoundedContinuousFunction.const_apply] using
    physicalTrajectoryMatrix_apply e σ a w t

theorem physical_scaled_quadratic (e σ : ℝ) (v : ResponseVector) :
    coefficientQuadratic (bilinearCoefficients (σ • physicalBilinear e)) v=
      σ • physicalQuadratic e v := by
  rw [coefficientQuadratic_bilinear]
  simp only [ContinuousLinearMap.smul_apply,physicalBilinear_diagonal]

/-- Actual finite physical trajectories depending analytically on their initial
perturbation, with uniform proximity on the whole finite segment. The sign sigma
allows the same statement to construct reversed finite trajectories. -/
theorem physical_finite_analytic_family (e σ T : ℝ) (hT : 0 ≤ T)
    (X : ℝ → ResponseVector)
    (hX : ∀ t ∈ Icc 0 T, HasDerivAt X (σ • responseVectorField e (X t)) t) :
    ∃ Φ : ResponseVector → ResponseVector,
      Φ 0=X T ∧ ContDiffAt ℝ ω Φ 0 ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ ξ in 𝓝 (0:ResponseVector),
        ∃ Y : ℝ → ResponseVector,
          Y 0=X 0+ξ ∧ Y T=Φ ξ ∧
          (∀ t ∈ Icc 0 T, HasDerivAt Y (σ • responseVectorField e (Y t)) t) ∧
          ∀ t ∈ Icc 0 T, dist (Y t) (X t) < ε := by
  have hcont : ContinuousOn X (Icc 0 T) :=
    fun t ht => (hX t ht).continuousAt.continuousWithinAt
  obtain ⟨a,ha⟩ := finite_reference_exists T hT X hcont
  let m := physicalTrajectoryMatrix e σ a
  let q := bilinearCoefficients (σ • physicalBilinear e)
  obtain ⟨k,hk,ψ,hzero,hcd,hfamily⟩ := finite_variation_local_family m q T
  let Φ : ResponseVector → ResponseVector :=
    fun ξ => X T+Real.exp (k*T) • perronEvaluation T (ψ ξ)
  have hΦ : ContDiffAt ℝ ω Φ 0 :=
    contDiffAt_const.add (ContDiffAt.const_smul (Real.exp (k*T))
      ((perronEvaluation T).contDiff.contDiffAt.comp 0 hcd))
  refine ⟨Φ,?_,hΦ,?_⟩
  · simp [Φ,hzero]
  intro ε hε
  have hsmall : ∀ᶠ ξ in 𝓝 (0:ResponseVector), Real.exp (k*T)*‖ψ ξ‖ < ε := by
    have hc : ContinuousAt (fun ξ => Real.exp (k*T)*‖ψ ξ‖) 0 :=
      continuousAt_const.mul hcd.continuousAt.norm
    exact hc.eventually_lt_const (by simpa [hzero] using hε)
  filter_upwards [hfamily,hsmall] with ξ hξ hξsmall
  let D := finiteVariation k ξ (finiteForcing m q k T hk (ψ ξ))
  let Y := fun t => X t+D t
  have hD0 : D 0=ξ := hξ.1
  have hrep : ∀ t, 0 ≤ t → D t=Real.exp (k*t) • (fun i => ψ ξ i t) := hξ.2.2
  have hcoeff : ∀ t ∈ Icc 0 T, (fun i => a i t)=X t := by
    intro t ht
    funext i
    rw [ha,finiteTime_eq T t ht]
  have hlin : ∀ t ∈ Icc 0 T, (fun i => ∑ j, m i j t*D t j)=
      σ • (physicalJacobian e (X t)).toLin' (D t) := by
    intro t ht
    change (fun i => ∑ j, physicalTrajectoryMatrix e σ a i j t*D t j)=_
    rw [physicalTrajectoryMatrix_vector,hcoeff t ht]
  have hD : ∀ t ∈ Icc 0 T, HasDerivAt D
      (σ • (physicalJacobian e (X t)).toLin' (D t)+σ • physicalQuadratic e (D t)) t := by
    intro t ht
    have hh := hξ.2.1 t ht
    change HasDerivAt D ((fun i => ∑ j, m i j t*D t j)+coefficientQuadratic q (D t)) t at hh
    rw [hlin t ht,show coefficientQuadratic q (D t)=σ • physicalQuadratic e (D t) from
      physical_scaled_quadratic e σ (D t)] at hh
    exact hh
  refine ⟨Y,?_,?_,?_,?_⟩
  · exact congrArg (fun d => X 0+d) hD0
  · simpa only [Y,Φ,perronEvaluation,ContinuousLinearMap.pi_apply,
      ContinuousLinearMap.coe_comp',Function.comp_apply,ContinuousLinearMap.proj_apply,
      BoundedContinuousFunction.evalCLM_apply] using congrArg (fun d => X T+d) (hrep T hT)
  · intro t ht
    have hh := (hX t ht).add (hD t ht)
    convert hh using 1
    change σ • responseVectorField e (X t+D t)=_
    rw [responseVectorField_exact_quadratic,smul_add,smul_add]
    exact add_assoc _ _ _
  · intro t ht
    change dist (X t+D t) (X t) < ε
    rw [dist_eq_norm,add_sub_cancel_left,hrep t ht.1,norm_smul,
      Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply lt_of_le_of_lt _ hξsmall
    apply mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hk.le))
      (perron_evaluation_norm (ψ ξ) t) (norm_nonneg _) (Real.exp_pos _).le

end CoreCouplingGlobal
