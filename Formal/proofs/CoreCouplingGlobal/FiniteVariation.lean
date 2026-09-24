import proofs.CoreCouplingGlobal.FiniteTrajectoryCoefficients

namespace CoreCouplingGlobal
open Set Filter
open scoped Topology ContDiff BoundedContinuousFunction

noncomputable def recoveredFiniteVariation (k : ℝ) (ξ : ResponseVector)
    (f : PerronSpace) (t : ℝ) : ResponseVector :=
  fun i => Real.exp (-k*t)*ξ i+uncutPastTrajectory k (f i) t

noncomputable def finiteVariation (k : ℝ) (ξ : ResponseVector)
    (f : PerronSpace) (t : ℝ) : ResponseVector :=
  Real.exp (k*t) • recoveredFiniteVariation k ξ f t

theorem finiteVariation_initial (k : ℝ) (ξ : ResponseVector) (f : PerronSpace) :
    finiteVariation k ξ f 0=ξ := by
  ext i
  simp [finiteVariation,recoveredFiniteVariation,uncutPastTrajectory]

theorem finiteVariation_hasDerivAt (k : ℝ) (hk : 0 < k) (ξ : ResponseVector)
    (f : PerronSpace) (t : ℝ) :
    HasDerivAt (finiteVariation k ξ f) (Real.exp (k*t) • (fun i => f i t)) t := by
  have hr : HasDerivAt (recoveredFiniteVariation k ξ f)
      (fun i => -k*recoveredFiniteVariation k ξ f t i+f i t) t := by
    apply hasDerivAt_pi.2
    intro i
    have h := ((((hasDerivAt_id t).const_mul (-k)).exp).mul_const (ξ i)).add
      (uncutPastTrajectory_hasDerivAt k hk (f i) t)
    convert h using 1
    simp [recoveredFiniteVariation]
    ring
  have h := (((hasDerivAt_id t).const_mul k).exp).smul hr
  convert h using 1
  ext i
  simp
  ring

theorem finiteVariation_fixedPoint_representation (k : ℝ) (hk : 0 < k)
    (ξ : ResponseVector) (v f : PerronSpace)
    (heq : v=allPastLinear k hk ξ+allPastGreen k hk f) (t : ℝ) (ht : 0 ≤ t) :
    finiteVariation k ξ f t=Real.exp (k*t) • (fun i => v i t) := by
  unfold finiteVariation
  congr 1
  ext i
  have h := congrArg (fun w : PerronSpace => w i t) heq
  change v i t=allPastLinear k hk ξ i t+pastZeroTrajectory k hk (f i) t at h
  rw [allPastLinear_apply k hk ξ t ht,← uncutPastTrajectory_agrees k hk (f i) t ht] at h
  exact h.symm

noncomputable def finiteForcing (m : Fin 4 → Fin 4 → (ℝ →ᵇ ℝ))
    (q : Fin 4 → Fin 4 → Fin 4 → ℝ) (k T : ℝ) (hk : 0 < k)
    (v : PerronSpace) : PerronSpace :=
  trajectoryMatrix m v+trajectoryScale (finiteGrowth k T hk) (trajectoryBilinear q v v)

theorem finiteForcing_apply (m : Fin 4 → Fin 4 → (ℝ →ᵇ ℝ))
    (q : Fin 4 → Fin 4 → Fin 4 → ℝ) (k T : ℝ) (hk : 0 < k)
    (v : PerronSpace) (t : ℝ) (ht : t ∈ Icc 0 T) (i : Fin 4) :
    finiteForcing m q k T hk v i t=(∑ j, m i j t*v j t)+
      Real.exp (k*t)*coefficientQuadratic q (fun j => v j t) i := by
  simp [finiteForcing,trajectoryMatrix_apply,trajectoryScale,finiteGrowth,
    finiteTime_eq T t ht,trajectoryBilinear_apply,coefficientQuadratic]

theorem finiteVariation_fixedPoint_ODE (m : Fin 4 → Fin 4 → (ℝ →ᵇ ℝ))
    (q : Fin 4 → Fin 4 → Fin 4 → ℝ) (k T : ℝ) (hk : 0 < k)
    (ξ : ResponseVector) (v : PerronSpace)
    (heq : v=allPastLinear k hk ξ+allPastGreen k hk (finiteForcing m q k T hk v))
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    let D := finiteVariation k ξ (finiteForcing m q k T hk v)
    HasDerivAt D (fun i => (∑ j, m i j t*D t j)+coefficientQuadratic q (D t) i) t := by
  dsimp only
  convert finiteVariation_hasDerivAt k hk ξ (finiteForcing m q k T hk v) t using 1
  rw [finiteVariation_fixedPoint_representation k hk ξ v _ heq t ht.1,
    coefficientQuadratic_smul]
  ext i
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [finiteForcing_apply m q k T hk v t ht i]
  rw [mul_add,Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _hj
    ring
  · ring

/-- An actual analytic family of finite-time perturbations for an arbitrary
bounded time-dependent linear part and a fixed homogeneous quadratic part. -/
theorem finite_variation_local_family (m : Fin 4 → Fin 4 → (ℝ →ᵇ ℝ))
    (q : Fin 4 → Fin 4 → Fin 4 → ℝ) (T : ℝ) :
    ∃ k : ℝ, ∃ hk : 0 < k, ∃ ψ : ResponseVector → PerronSpace,
      ψ 0=0 ∧ ContDiffAt ℝ ω ψ 0 ∧ ∀ᶠ ξ in 𝓝 (0:ResponseVector),
        let D := finiteVariation k ξ (finiteForcing m q k T hk (ψ ξ))
        D 0=ξ ∧
        (∀ t ∈ Icc 0 T, HasDerivAt D
          (fun i => (∑ j, m i j t*D t j)+coefficientQuadratic q (D t) i) t) ∧
        ∀ t, 0 ≤ t → D t=Real.exp (k*t) • (fun i => ψ ξ i t) := by
  let H := trajectoryMatrix m
  obtain ⟨k,hk,hcontract⟩ := allPast_linear_contractive H
  let N : PerronSpace →L[ℝ] PerronSpace →L[ℝ] PerronSpace :=
    (ContinuousLinearMap.compL ℝ PerronSpace PerronSpace PerronSpace
      (trajectoryScale (finiteGrowth k T hk))).comp (trajectoryBilinear q)
  let GN : PerronSpace →L[ℝ] PerronSpace →L[ℝ] PerronSpace :=
    (ContinuousLinearMap.compL ℝ PerronSpace PerronSpace PerronSpace (allPastGreen k hk)).comp N
  obtain ⟨_S,_hS,ψ,hzero,hcd,_hd,heq⟩ := linear_quadratic_implicit_solution
    (allPastLinear k hk) ((allPastGreen k hk).comp H) GN hcontract
  refine ⟨k,hk,ψ,hzero,hcd,?_⟩
  filter_upwards [heq] with ξ hξ
  have hfixed : ψ ξ=allPastLinear k hk ξ+allPastGreen k hk (finiteForcing m q k T hk (ψ ξ)) := by
    change ψ ξ=allPastLinear k hk ξ+allPastGreen k hk (H (ψ ξ))+
      allPastGreen k hk (N (ψ ξ) (ψ ξ)) at hξ
    change ψ ξ=allPastLinear k hk ξ+allPastGreen k hk (H (ψ ξ)+N (ψ ξ) (ψ ξ))
    rw [map_add,← add_assoc]
    exact hξ
  exact ⟨finiteVariation_initial k ξ _,
    fun t ht => finiteVariation_fixedPoint_ODE m q k T hk ξ (ψ ξ) hfixed t ht,
    fun t ht => finiteVariation_fixedPoint_representation k hk ξ (ψ ξ) _ hfixed t ht⟩

end CoreCouplingGlobal
