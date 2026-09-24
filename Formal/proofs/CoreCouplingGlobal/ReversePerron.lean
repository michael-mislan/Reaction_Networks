import proofs.CoreCouplingGlobal.PerronTrajectories

namespace CoreCouplingGlobal
open Filter
open scoped BoundedContinuousFunction Topology ContDiff

noncomputable def recoveredReversePerron (μ : Fin 4 → ℝ) (β : ℝ)
    (ξ : Fin 4 → ℝ) (f : Fin 4 → (ℝ →ᵇ ℝ)) (t : ℝ) : Fin 4 → ℝ :=
  fun i => if i=3 then Real.exp ((μ i+β)*t)*ξ i+uncutPastTrajectory (-(μ i+β)) (f i) t
    else -exponentialAverage (μ i+β) 1 (f i) t

theorem recoveredReversePerron_hasDerivAt (μ : Fin 4 → ℝ) (β : ℝ)
    (hs : μ 3+β < 0) (hu : ∀ i : Fin 4, i ≠ 3 → 0 < μ i+β)
    (ξ : Fin 4 → ℝ) (f : Fin 4 → (ℝ →ᵇ ℝ)) (t : ℝ) :
    HasDerivAt (recoveredReversePerron μ β ξ f)
      (fun i => (μ i+β)*recoveredReversePerron μ β ξ f t i+f i t) t := by
  apply hasDerivAt_pi.2
  intro i
  by_cases hi : i=3
  · subst i
    have h := ((((hasDerivAt_id t).const_mul (μ 3+β)).exp).mul_const (ξ 3)).add
      (uncutPastTrajectory_hasDerivAt (-(μ 3+β)) (neg_pos.mpr hs) (f 3) t)
    convert h using 1
    simp [recoveredReversePerron]
    ring
  · have h := (exponential_future_hasDerivAt (μ i+β) (hu i hi) (f i) t).neg
    convert h using 1
    · funext u
      simp [recoveredReversePerron,hi]
    · simp [recoveredReversePerron,hi]
      ring

theorem recoveredReversePerron_stable_initial (μ : Fin 4 → ℝ) (β : ℝ)
    (ξ : Fin 4 → ℝ) (f : Fin 4 → (ℝ →ᵇ ℝ)) :
    recoveredReversePerron μ β ξ f 0 3=ξ 3 := by
  simp [recoveredReversePerron,uncutPastTrajectory]

noncomputable def weightedReversePerron (μ : Fin 4 → ℝ) (β : ℝ)
    (ξ : Fin 4 → ℝ) (f : Fin 4 → (ℝ →ᵇ ℝ)) (t : ℝ) : Fin 4 → ℝ :=
  Real.exp (-β*t) • recoveredReversePerron μ β ξ f t

theorem weightedReversePerron_hasDerivAt (μ : Fin 4 → ℝ) (β : ℝ)
    (hs : μ 3+β < 0) (hu : ∀ i : Fin 4, i ≠ 3 → 0 < μ i+β)
    (ξ : Fin 4 → ℝ) (f : Fin 4 → (ℝ →ᵇ ℝ)) (t : ℝ) :
    HasDerivAt (weightedReversePerron μ β ξ f)
      (fun i => μ i*weightedReversePerron μ β ξ f t i+Real.exp (-β*t)*f i t) t := by
  have h := (((hasDerivAt_id t).const_mul (-β)).exp).smul
    (recoveredReversePerron_hasDerivAt μ β hs hu ξ f t)
  convert h using 1
  ext i
  simp [weightedReversePerron]
  ring

/-- If the integral forcing matches the weighted homogeneous quadratic term,
the recovered trajectory solves the diagonal-plus-quadratic ODE, including at
time zero. Existence of such a self-consistent forcing is a separate theorem. -/
theorem weightedReversePerron_quadratic_ODE (μ : Fin 4 → ℝ) (β : ℝ)
    (hs : μ 3+β < 0) (hu : ∀ i : Fin 4, i ≠ 3 → 0 < μ i+β)
    (ξ : Fin 4 → ℝ) (f : Fin 4 → (ℝ →ᵇ ℝ))
    (Q : (Fin 4 → ℝ) → (Fin 4 → ℝ))
    (hQ : ∀ (a : ℝ) (x : Fin 4 → ℝ), Q (a • x)=a^2 • Q x) (t : ℝ)
    (hf : ∀ i, f i t=Real.exp (-β*t)*Q (recoveredReversePerron μ β ξ f t) i) :
    HasDerivAt (weightedReversePerron μ β ξ f)
      (fun i => μ i*weightedReversePerron μ β ξ f t i+Q (weightedReversePerron μ β ξ f t) i) t := by
  convert weightedReversePerron_hasDerivAt μ β hs hu ξ f t using 1
  ext i
  rw [hf i]
  change μ i*weightedReversePerron μ β ξ f t i+Q (Real.exp (-β*t) • recoveredReversePerron μ β ξ f t) i = _
  rw [hQ]
  simp only [Pi.smul_apply,smul_eq_mul]
  ring


noncomputable def reversePerronGreen (μ : Fin 4 → ℝ) (β : ℝ)
    (hs : μ 3+β < 0) (hu : ∀ i : Fin 4, i ≠ 3 → 0 < μ i+β) :
    PerronSpace →L[ℝ] PerronSpace :=
  ContinuousLinearMap.pi fun i => if hi : i=3 then
    (pastZeroOperator (-(μ i+β)) (by subst i; exact neg_pos.mpr hs)).comp
      (ContinuousLinearMap.proj i)
    else -((clampOperator.comp (exponentialGreenOperator (μ i+β) 1 (hu i hi))).comp
      (ContinuousLinearMap.proj i))

noncomputable def reversePerronLinear (μ : Fin 4 → ℝ) (β : ℝ)
    (hs : μ 3+β < 0) : ℝ →L[ℝ] PerronSpace :=
  ContinuousLinearMap.pi fun i => if hi : i=3 then
    (ContinuousLinearMap.id ℝ ℝ).smulRight
      (decayingProfile (-(μ i+β)) (by subst i; exact neg_pos.mpr hs))
    else 0

theorem reversePerronLinear_stable (μ : Fin 4 → ℝ) (β : ℝ)
    (hs : μ 3+β < 0) (a t : ℝ) (ht : 0 ≤ t) :
    reversePerronLinear μ β hs a 3 t=Real.exp ((μ 3+β)*t)*a := by
  simp [reversePerronLinear,decayingProfile,max_eq_left ht,mul_comm]

theorem reversePerronLinear_unstable (μ : Fin 4 → ℝ) (β : ℝ)
    (hs : μ 3+β < 0) (a t : ℝ) (i : Fin 4) (hi : i ≠ 3) :
    reversePerronLinear μ β hs a i t=0 := by
  simp [reversePerronLinear,hi]

theorem reversePerronGreen_stable (μ : Fin 4 → ℝ) (β : ℝ)
    (hs : μ 3+β < 0) (hu : ∀ i : Fin 4, i ≠ 3 → 0 < μ i+β)
    (f : PerronSpace) (t : ℝ) (ht : 0 ≤ t) :
    reversePerronGreen μ β hs hu f 3 t=uncutPastTrajectory (-(μ 3+β)) (f 3) t := by
  simpa [reversePerronGreen,pastZeroOperator] using
    (uncutPastTrajectory_agrees (-(μ 3+β)) (neg_pos.mpr hs) (f 3) t ht).symm

theorem reversePerronGreen_unstable (μ : Fin 4 → ℝ) (β : ℝ)
    (hs : μ 3+β < 0) (hu : ∀ i : Fin 4, i ≠ 3 → 0 < μ i+β)
    (f : PerronSpace) (i : Fin 4) (hi : i ≠ 3) (t : ℝ) (ht : 0 ≤ t) :
    reversePerronGreen μ β hs hu f i t=-exponentialAverage (μ i+β) 1 (f i) t := by
  simp [reversePerronGreen,hi,clampOperator,nonnegativeTime,max_eq_left ht,
    exponentialGreenOperator,exponentialAverageBCF]

def unstableExtension (a : ℝ) : Fin 4 → ℝ := fun i => if i=3 then a else 0

theorem reversePerron_fixedPoint_recovered (μ : Fin 4 → ℝ) (β : ℝ)
    (hs : μ 3+β < 0) (hu : ∀ i : Fin 4, i ≠ 3 → 0 < μ i+β)
    (a : ℝ) (v f : PerronSpace)
    (heq : v=reversePerronLinear μ β hs a+reversePerronGreen μ β hs hu f)
    (t : ℝ) (ht : 0 ≤ t) :
    recoveredReversePerron μ β (unstableExtension a) f t=(fun i => v i t) := by
  ext i
  by_cases hi : i=3
  · subst i
    have h := congrArg (fun w : PerronSpace => w 3 t) heq
    change v 3 t=reversePerronLinear μ β hs a 3 t+reversePerronGreen μ β hs hu f 3 t at h
    rw [reversePerronLinear_stable μ β hs a t ht,
      reversePerronGreen_stable μ β hs hu f t ht] at h
    simpa [recoveredReversePerron,unstableExtension] using h.symm
  · have h := congrArg (fun w : PerronSpace => w i t) heq
    change v i t=reversePerronLinear μ β hs a i t+reversePerronGreen μ β hs hu f i t at h
    rw [reversePerronLinear_unstable μ β hs a t i hi,
      reversePerronGreen_unstable μ β hs hu f i hi t ht,zero_add] at h
    simpa [recoveredReversePerron,hi] using h.symm

theorem reversePerron_local_actual_trajectories (μ : Fin 4 → ℝ) (β : ℝ) (hβ : 0 < β)
    (hs : μ 3+β < 0) (hu : ∀ i : Fin 4, i ≠ 3 → 0 < μ i+β)
    (q : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∃ ψ : ℝ → PerronSpace, ψ 0=0 ∧ ContDiffAt ℝ ω ψ 0 ∧
      HasFDerivAt ψ (reversePerronLinear μ β hs) 0 ∧
      ∀ᶠ a in 𝓝 (0:ℝ),
        let X := weightedReversePerron μ β (unstableExtension a)
          (weightedTrajectoryBilinear β hβ q (ψ a) (ψ a))
        (∀ t, 0 ≤ t → HasDerivAt X
          (fun i => μ i*X t i+coefficientQuadratic q (X t) i) t) ∧
        X 0 3=a ∧ ∀ t, 0 ≤ t → X t=Real.exp (-β*t) • (fun i => ψ a i t) := by
  let G := reversePerronGreen μ β hs hu
  let B := weightedTrajectoryBilinear β hβ q
  let GB : PerronSpace →L[ℝ] PerronSpace →L[ℝ] PerronSpace :=
    (ContinuousLinearMap.compL ℝ PerronSpace PerronSpace PerronSpace G).comp B
  obtain ⟨ψ,hzero,hcd,hd,heq,_⟩ := quadratic_implicit_solution (reversePerronLinear μ β hs) GB
  refine ⟨ψ,hzero,hcd,hd,?_⟩
  filter_upwards [heq] with a ha
  change ψ a=reversePerronLinear μ β hs a+
    reversePerronGreen μ β hs hu (weightedTrajectoryBilinear β hβ q (ψ a) (ψ a)) at ha
  refine ⟨?_,?_,?_⟩
  · intro t ht
    apply weightedReversePerron_quadratic_ODE μ β hs hu (unstableExtension a)
      (weightedTrajectoryBilinear β hβ q (ψ a) (ψ a)) (coefficientQuadratic q)
      (coefficientQuadratic_smul q) t
    intro i
    rw [reversePerron_fixedPoint_recovered μ β hs hu a (ψ a) _ ha t ht]
    simpa only [max_eq_left ht,coefficientQuadratic] using
      weightedTrajectoryBilinear_apply β hβ q (ψ a) (ψ a) t i
  · simpa [weightedReversePerron,unstableExtension] using
      recoveredReversePerron_stable_initial μ β (unstableExtension a)
        (weightedTrajectoryBilinear β hβ q (ψ a) (ψ a))
  · intro t ht
    unfold weightedReversePerron
    rw [reversePerron_fixedPoint_recovered μ β hs hu a (ψ a) _ ha t ht]

end CoreCouplingGlobal
