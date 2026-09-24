import proofs.CoreCouplingGlobal.PerronEquation

namespace CoreCouplingGlobal
open Filter
open scoped BoundedContinuousFunction Topology ContDiff

def stableExtension (ξ : StableData) : Fin 4 → ℝ := Fin.lastCases 0 ξ

def coefficientQuadratic (q : Fin 4 → Fin 4 → Fin 4 → ℝ) (x : Fin 4 → ℝ) :
    Fin 4 → ℝ := fun i => ∑ j, ∑ k, q i j k*x j*x k

theorem coefficientQuadratic_smul (q : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (a : ℝ) (x : Fin 4 → ℝ) :
    coefficientQuadratic q (a • x)=a^2 • coefficientQuadratic q x := by
  ext i
  simp only [coefficientQuadratic,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro k _hk
  ring

theorem perron_fixedPoint_recovered (μ : Fin 4 → ℝ) (β : ℝ)
    (hs : ∀ i : Fin 4, i ≠ 3 → μ i+β < 0) (hu : 0 < μ 3+β)
    (ξ : StableData) (v f : PerronSpace)
    (heq : v=perronLinear μ β hs ξ+perronGreen μ β hs hu f)
    (t : ℝ) (ht : 0 ≤ t) :
    recoveredPerron μ β (stableExtension ξ) f t=(fun i => v i t) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have h := congrArg (fun w : PerronSpace => w 3 t) heq
    change v 3 t=perronLinear μ β hs ξ 3 t+perronGreen μ β hs hu f 3 t at h
    rw [perronLinear_unstable,perronGreen_unstable μ β hs hu f t ht,zero_add] at h
    simpa [recoveredPerron] using h.symm
  · have hj : j.castSucc ≠ (3 : Fin 4) := by simpa using j.castSucc_ne_last
    have h := congrArg (fun w : PerronSpace => w j.castSucc t) heq
    change v j.castSucc t=perronLinear μ β hs ξ j.castSucc t+
      perronGreen μ β hs hu f j.castSucc t at h
    rw [perronLinear_stable μ β hs ξ j t ht,perronGreen_stable μ β hs hu f j t ht] at h
    simpa [recoveredPerron,hj,stableExtension] using h.symm

/-- An actual solution of the nonlinear integral equation yields an actual ODE
trajectory for every nonnegative time, including an ordinary derivative at zero. -/
theorem perron_fixedPoint_ODE (μ : Fin 4 → ℝ) (β : ℝ) (hβ : 0 < β)
    (hs : ∀ i : Fin 4, i ≠ 3 → μ i+β < 0) (hu : 0 < μ 3+β)
    (q : Fin 4 → Fin 4 → Fin 4 → ℝ) (ξ : StableData) (v : PerronSpace)
    (heq : v=perronLinear μ β hs ξ+
      perronGreen μ β hs hu (weightedTrajectoryBilinear β hβ q v v))
    (t : ℝ) (ht : 0 ≤ t) :
    let X := weightedPerron μ β (stableExtension ξ) (weightedTrajectoryBilinear β hβ q v v)
    HasDerivAt X (fun i => μ i*X t i+coefficientQuadratic q (X t) i) t := by
  apply weightedPerron_quadratic_ODE μ β hs hu (stableExtension ξ)
    (weightedTrajectoryBilinear β hβ q v v) (coefficientQuadratic q)
    (coefficientQuadratic_smul q) t
  intro i
  rw [perron_fixedPoint_recovered μ β hs hu ξ v _ heq t ht]
  simpa only [max_eq_left ht,coefficientQuadratic] using
    weightedTrajectoryBilinear_apply β hβ q v v t i

theorem perron_trajectory_stable_initial (μ : Fin 4 → ℝ) (β : ℝ)
    (ξ : StableData) (f : PerronSpace) (i : Fin 3) :
    weightedPerron μ β (stableExtension ξ) f 0 i.castSucc=ξ i := by
  have hi : i.castSucc ≠ (3 : Fin 4) := by simpa using i.castSucc_ne_last
  simpa [weightedPerron,stableExtension] using
    recoveredPerron_stable_initial μ β (stableExtension ξ) f i.castSucc hi

/-- A smooth family of self-consistent bounded weighted trajectories solving
the actual diagonal quadratic ODE. No ODE solution or nonlinear forcing is
provided as a hypothesis. Physical-coordinate binding and coverage remain. -/
theorem perron_local_actual_trajectories (μ : Fin 4 → ℝ) (β : ℝ) (hβ : 0 < β)
    (hs : ∀ i : Fin 4, i ≠ 3 → μ i+β < 0) (hu : 0 < μ 3+β)
    (q : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∃ ψ : StableData → PerronSpace, ψ 0=0 ∧ ContDiffAt ℝ ω ψ 0 ∧
      HasFDerivAt ψ (perronLinear μ β hs) 0 ∧
      ∀ᶠ ξ in 𝓝 (0:StableData),
        let X := weightedPerron μ β (stableExtension ξ)
          (weightedTrajectoryBilinear β hβ q (ψ ξ) (ψ ξ))
        (∀ t, 0 ≤ t → HasDerivAt X
          (fun i => μ i*X t i+coefficientQuadratic q (X t) i) t) ∧
        (∀ i : Fin 3, X 0 i.castSucc=ξ i) ∧
        ∀ t, 0 ≤ t → X t=Real.exp (-β*t) • (fun i => ψ ξ i t) := by
  obtain ⟨ψ,hzero,hcd,hd,heq⟩ := perron_equation_local_solution μ β hβ hs hu q
  refine ⟨ψ,hzero,hcd,hd,?_⟩
  filter_upwards [heq] with ξ hξ
  refine ⟨fun t ht => perron_fixedPoint_ODE μ β hβ hs hu q ξ (ψ ξ) hξ t ht,
    fun i => perron_trajectory_stable_initial μ β ξ _ i,?_⟩
  intro t ht
  unfold weightedPerron
  rw [perron_fixedPoint_recovered μ β hs hu ξ (ψ ξ) _ hξ t ht]

end CoreCouplingGlobal
