import proofs.CoreCouplingGlobal.PerronDifferential

namespace CoreCouplingGlobal
open scoped BoundedContinuousFunction

noncomputable def recoveredPerron (μ : Fin 4 → ℝ) (β : ℝ)
    (ξ : Fin 4 → ℝ) (f : Fin 4 → (ℝ →ᵇ ℝ)) (t : ℝ) : Fin 4 → ℝ :=
  fun i => if i=3 then -exponentialAverage (μ i+β) 1 (f i) t
    else Real.exp ((μ i+β)*t)*ξ i+uncutPastTrajectory (-(μ i+β)) (f i) t

theorem recoveredPerron_hasDerivAt (μ : Fin 4 → ℝ) (β : ℝ)
    (hs : ∀ i : Fin 4, i ≠ 3 → μ i+β < 0) (hu : 0 < μ 3+β)
    (ξ : Fin 4 → ℝ) (f : Fin 4 → (ℝ →ᵇ ℝ)) (t : ℝ) :
    HasDerivAt (recoveredPerron μ β ξ f)
      (fun i => (μ i+β)*recoveredPerron μ β ξ f t i+f i t) t := by
  apply hasDerivAt_pi.2
  intro i
  by_cases hi : i=3
  · subst i
    have h := (exponential_future_hasDerivAt (μ 3+β) hu (f 3) t).neg
    convert h using 1
    simp [recoveredPerron]
    ring
  · have h := ((((hasDerivAt_id t).const_mul (μ i+β)).exp).mul_const (ξ i)).add
      (uncutPastTrajectory_hasDerivAt (-(μ i+β)) (neg_pos.mpr (hs i hi)) (f i) t)
    convert h using 1
    · funext u
      simp [recoveredPerron,hi]
    · simp [recoveredPerron,hi]
      ring

theorem recoveredPerron_stable_initial (μ : Fin 4 → ℝ) (β : ℝ)
    (ξ : Fin 4 → ℝ) (f : Fin 4 → (ℝ →ᵇ ℝ)) (i : Fin 4) (hi : i ≠ 3) :
    recoveredPerron μ β ξ f 0 i=ξ i := by
  simp [recoveredPerron,hi,uncutPastTrajectory]

noncomputable def weightedPerron (μ : Fin 4 → ℝ) (β : ℝ)
    (ξ : Fin 4 → ℝ) (f : Fin 4 → (ℝ →ᵇ ℝ)) (t : ℝ) : Fin 4 → ℝ :=
  Real.exp (-β*t) • recoveredPerron μ β ξ f t

theorem weightedPerron_hasDerivAt (μ : Fin 4 → ℝ) (β : ℝ)
    (hs : ∀ i : Fin 4, i ≠ 3 → μ i+β < 0) (hu : 0 < μ 3+β)
    (ξ : Fin 4 → ℝ) (f : Fin 4 → (ℝ →ᵇ ℝ)) (t : ℝ) :
    HasDerivAt (weightedPerron μ β ξ f)
      (fun i => μ i*weightedPerron μ β ξ f t i+Real.exp (-β*t)*f i t) t := by
  have h := (((hasDerivAt_id t).const_mul (-β)).exp).smul
    (recoveredPerron_hasDerivAt μ β hs hu ξ f t)
  convert h using 1
  ext i
  simp [weightedPerron]
  ring

/-- If the integral forcing matches the weighted homogeneous quadratic term,
the recovered trajectory solves the diagonal-plus-quadratic ODE, including at
time zero. Existence of such a self-consistent forcing is a separate theorem. -/
theorem weightedPerron_quadratic_ODE (μ : Fin 4 → ℝ) (β : ℝ)
    (hs : ∀ i : Fin 4, i ≠ 3 → μ i+β < 0) (hu : 0 < μ 3+β)
    (ξ : Fin 4 → ℝ) (f : Fin 4 → (ℝ →ᵇ ℝ))
    (Q : (Fin 4 → ℝ) → (Fin 4 → ℝ))
    (hQ : ∀ (a : ℝ) (x : Fin 4 → ℝ), Q (a • x)=a^2 • Q x) (t : ℝ)
    (hf : ∀ i, f i t=Real.exp (-β*t)*Q (recoveredPerron μ β ξ f t) i) :
    HasDerivAt (weightedPerron μ β ξ f)
      (fun i => μ i*weightedPerron μ β ξ f t i+Q (weightedPerron μ β ξ f t) i) t := by
  convert weightedPerron_hasDerivAt μ β hs hu ξ f t using 1
  ext i
  rw [hf i]
  change μ i*weightedPerron μ β ξ f t i+Q (Real.exp (-β*t) • recoveredPerron μ β ξ f t) i = _
  rw [hQ]
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

end CoreCouplingGlobal
