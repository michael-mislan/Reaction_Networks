import proofs.OptimalAffinityRealizability.SmoothBranch
import Mathlib.Analysis.Calculus.DerivativeTest

namespace OptimalAffinityRealizability

open Filter
open SignType
open scoped ContDiff Topology
noncomputable section

def controlledBranchFlux {n : ℕ} (source : SquareSource n)
    (J : ℝ) (g q : Fin n → ℝ) (z : ℝ → (Fin n → ℝ)) (s : ℝ) : ℝ :=
  reconstructedLogSourceDrift source J g q (z s) source.controlled

def IsStrictLocalMaxAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ᶠ y in 𝓝[≠] x, f y < f x

theorem current_eq_controlledProductionRay {n : ℕ} (source : SquareSource n)
    (g current : Fin n → ℝ) (hmode : ControlledProductionMode source g)
    (hstationary : ∀ i, i ≠ source.controlled →
      source.netStoich.mulVec current i = 0) :
    current = (source.netStoich.mulVec current source.controlled) • g := by
  apply netStoich_mulVec_injective source
  funext i
  by_cases hi : i = source.controlled
  · subst i
    have hc : source.netStoich.mulVec g source.controlled = 1 := by
      simpa using hmode source.controlled
    rw [Matrix.mulVec_smul]
    simp only [Pi.smul_apply, smul_eq_mul, hc]
    ring
  · have hi0 : source.netStoich.mulVec g i = 0 := by
      simpa [hi] using hmode i
    rw [hstationary i hi, Matrix.mulVec_smul]
    simp only [Pi.smul_apply, smul_eq_mul, hi0, mul_zero]

theorem smoothLocalBranch_zero {n : ℕ} (source : SquareSource n)
    (J : ℝ) (g q : Fin n → ℝ)
    (hreduced : NoncontrolledSteadyJacobianInjective source
      (literalCurrentJacobian source J g q)) :
    smoothLocalBranch source J g q hreduced 0 = 0 := by
  simpa [smoothLocalBranch] using inverseFunctionBranch_zero
    (augmentedLogStationarity source J g q) 0
    (augmentedSteadyContinuousLinearEquiv source
      (literalCurrentJacobian source J g q) hreduced)
    ((augmentedLogStationarity_contDiff source J g q).contDiffAt.hasStrictFDerivAt'
      (augmentedLogStationarity_hasStrictFDerivAt_zero source J g q).hasFDerivAt
      (by simp))
    (controlledTargetDirection source)

theorem smoothLocalBranch_hasStrictFDerivAt_kernelTangent
    {n : ℕ} (source : SquareSource n) (J : ℝ) (g q u : Fin n → ℝ)
    (hreduced : NoncontrolledSteadyJacobianInjective source
      (literalCurrentJacobian source J g q))
    (hkernel : (literalCurrentJacobian source J g q).mulVec u = 0)
    (hcontrol : u source.controlled = 1) :
    HasStrictFDerivAt (smoothLocalBranch source J g q hreduced)
      (scalarDirectionMap u) 0 := by
  unfold smoothLocalBranch
  exact canonicalLocalBranch_hasStrictFDerivAt_kernelTangent
    source J g q hreduced u hkernel hcontrol

theorem smoothLocalBranch_eventually_currentRay {n : ℕ} (source : SquareSource n)
    (J : ℝ) (g q : Fin n → ℝ)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i) (hq : ∀ i, 1 < q i)
    (hmode : ControlledProductionMode source g)
    (hreduced : NoncontrolledSteadyJacobianInjective source
      (literalCurrentJacobian source J g q)) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      reconstructedLogReactionCurrent source J g q
          (smoothLocalBranch source J g q hreduced s) =
        controlledBranchFlux source J g q
          (smoothLocalBranch source J g q hreduced) s • g := by
  let F := augmentedLogStationarity source J g q
  let D := augmentedSteadyContinuousLinearEquiv source
    (literalCurrentJacobian source J g q) hreduced
  let hcont : ContDiffAt ℝ ⊤ F 0 := by
    simpa [F] using (augmentedLogStationarity_contDiff source J g q).contDiffAt
  let hderiv : HasFDerivAt F (D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) 0 := by
    simpa [F, D] using
      (augmentedLogStationarity_hasStrictFDerivAt_zero source J g q).hasFDerivAt
  let hD := hcont.hasStrictFDerivAt' hderiv (by simp)
  let z := smoothLocalBranch source J g q hreduced
  have hFzero : F 0 = 0 := by
    exact augmentedLogStationarity_zero source J g q hJ hg hq hmode
  have heqRaw := inverseFunctionBranch_eventually_equation F 0 D hD
    (controlledTargetDirection source)
  have heq : ∀ᶠ s in 𝓝 (0 : ℝ), F (z s) =
      s • controlledTargetDirection source := by
    filter_upwards [heqRaw] with s hs
    rw [hFzero, zero_add] at hs
    simpa [z, smoothLocalBranch, F, D, hcont, hderiv, hD] using hs
  filter_upwards [heq] with s hs
  apply current_eq_controlledProductionRay source g _ hmode
  intro i hi
  have hrow := congrFun hs i
  simpa [F, augmentedLogStationarity, hi, controlledTargetDirection,
    reconstructedLogSourceDrift] using hrow

theorem smoothLocalBranch_secondJet_coupled
    {n : ℕ} (source : SquareSource n) (J : ℝ)
    (g q u : Fin n → ℝ)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i) (hq : ∀ i, 1 < q i)
    (hmode : ControlledProductionMode source g)
    (hreduced : NoncontrolledSteadyJacobianInjective source
      (literalCurrentJacobian source J g q))
    (hkernel : (literalCurrentJacobian source J g q).mulVec u = 0)
    (hcontrol : u source.controlled = 1) :
    ∃ v : Fin n → ℝ,
      HasFDerivAt
          (fun s : ℝ => fderiv ℝ (smoothLocalBranch source J g q hreduced) s 1)
          (scalarDirectionMap v) 0 ∧
      reactionCurrentSecondJet source J g q u v =
        deriv (deriv (controlledBranchFlux source J g q
          (smoothLocalBranch source J g q hreduced))) 0 • g := by
  let z := smoothLocalBranch source J g q hreduced
  let dz := fun s : ℝ => fderiv ℝ z s 1
  let phi := controlledBranchFlux source J g q z
  have hzcont : ContDiffAt ℝ ⊤ z 0 := by
    simpa [z] using smoothLocalBranch_contDiffAt source J g q hreduced
  have hzstrict : HasStrictFDerivAt z (scalarDirectionMap u) 0 := by
    simpa [z] using smoothLocalBranch_hasStrictFDerivAt_kernelTangent
      source J g q u hreduced hkernel hcontrol
  have hz0 : z 0 = 0 := by
    simpa [z] using smoothLocalBranch_zero source J g q hreduced
  have hdz0 : dz 0 = u := by
    have hmap := hzstrict.hasFDerivAt.fderiv
    have happ := congrArg (fun L : ℝ →L[ℝ] (Fin n → ℝ) => L 1) hmap
    simpa [dz, scalarDirectionMap] using happ
  obtain ⟨v, hdz⟩ := contDiffAt_exists_secondVelocity z hzcont
  refine ⟨v, ?_, ?_⟩
  · simpa [z, dz] using hdz
  · funext i
    have hsecond :=
      (reconstructedLogReactionCurrent_secondDerivative_of_velocity
        source J g q u v z dz i hz0 hdz0 hzstrict.hasFDerivAt
          (by simpa [dz] using hdz)).2
    have hvelocityDeriv := reactionCurrentAlongVelocity_eventually_eq_deriv
      source J g q z i hzcont
    have hrayVector := smoothLocalBranch_eventually_currentRay
      source J g q hJ hg hq hmode hreduced
    have hrayComponent :
        (fun s => reconstructedLogReactionCurrent source J g q (z s) i) =ᶠ[𝓝 0]
          (fun s => phi s * g i) := by
      filter_upwards [hrayVector] with s hs
      have hi := congrFun hs i
      simpa [z, phi, Pi.smul_apply, smul_eq_mul] using hi
    have hfirstDeriv := hrayComponent.deriv
    have hmul : deriv (fun s => phi s * g i) =
        fun s => deriv phi s * g i := deriv_mul_const_field' (g i)
    rw [hmul] at hfirstDeriv
    have hvelocityDeriv' :
        (fun s => reactionCurrentAlongVelocity source J g q z dz i s) =ᶠ[𝓝 0]
          deriv (fun s => reconstructedLogReactionCurrent source J g q (z s) i) := by
      simpa [dz] using hvelocityDeriv
    have hvelocityRay :
        (fun s => reactionCurrentAlongVelocity source J g q z dz i s) =ᶠ[𝓝 0]
          (fun s => deriv phi s * g i) := by
      exact hvelocityDeriv'.trans hfirstDeriv
    have hsecondEq := hvelocityRay.deriv_eq
    rw [hsecond.deriv, deriv_mul_const_field] at hsecondEq
    simpa [z, phi, Pi.smul_apply, smul_eq_mul] using hsecondEq

theorem smoothLocalBranch_flux_secondDerivative_neg
    {n : ℕ} (source : SquareSource n) (J : ℝ)
    (g q u lambda : Fin n → ℝ)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i)
    (hf : ∀ i, 0 < source.reactant.transpose.mulVec u i)
    (hh : ∀ i, 0 < source.product.transpose.mulVec u i)
    (hlambda : ∀ i, 0 ≤ lambda i) (hlambda0 : lambda ≠ 0)
    (hq : ∀ i, 1 < q i)
    (hratio : ∀ i, source.product.transpose.mulVec u i =
      q i * source.reactant.transpose.mulVec u i)
    (hmode : ControlledProductionMode source g)
    (hreduced : NoncontrolledSteadyJacobianInjective source
      (literalCurrentJacobian source J g q))
    (hkernel : (literalCurrentJacobian source J g q).mulVec u = 0)
    (hcontrol : u source.controlled = 1)
    (hannih : ∀ w : Fin n → ℝ,
      dotProduct lambda ((literalCurrentJacobian source J g q).mulVec w) = 0) :
    deriv (deriv (controlledBranchFlux source J g q
      (smoothLocalBranch source J g q hreduced))) 0 < 0 := by
  obtain ⟨v, _, hcoupled⟩ := smoothLocalBranch_secondJet_coupled
    source J g q u hJ hg hq hmode hreduced hkernel hcontrol
  exact leftNull_curvature_strictly_negative source J _ g q u v lambda
    hJ hg hf hh hlambda hlambda0 hq hratio hannih hcoupled

theorem smoothLocalBranch_flux_firstDerivative_eq_zero
    {n : ℕ} (source : SquareSource n) (J : ℝ)
    (g q u : Fin n → ℝ)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i) (hq : ∀ i, 1 < q i)
    (hmode : ControlledProductionMode source g)
    (hreduced : NoncontrolledSteadyJacobianInjective source
      (literalCurrentJacobian source J g q))
    (hkernel : (literalCurrentJacobian source J g q).mulVec u = 0)
    (hcontrol : u source.controlled = 1) :
    deriv (controlledBranchFlux source J g q
      (smoothLocalBranch source J g q hreduced)) 0 = 0 := by
  let z := smoothLocalBranch source J g q hreduced
  let phi := controlledBranchFlux source J g q z
  have hz0 : z 0 = 0 := by
    simpa [z] using smoothLocalBranch_zero source J g q hreduced
  have hzstrict : HasStrictFDerivAt z (scalarDirectionMap u) 0 := by
    simpa [z] using smoothLocalBranch_hasStrictFDerivAt_kernelTangent
      source J g q u hreduced hkernel hcontrol
  have hcurrent := reconstructedLogReactionCurrent_comp_hasStrictFDerivAt_zero
    source J g q z u hz0 hzstrict hkernel
  have hcomponent := (hasStrictFDerivAt_pi'.mp hcurrent) source.controlled
  have hcurrentDeriv :
      deriv (fun s => reconstructedLogReactionCurrent source J g q (z s)
        source.controlled) 0 = 0 := by
    simpa using hcomponent.hasFDerivAt.hasDerivAt.deriv
  have hrayVector := smoothLocalBranch_eventually_currentRay
    source J g q hJ hg hq hmode hreduced
  have hrayComponent :
      (fun s => reconstructedLogReactionCurrent source J g q (z s)
        source.controlled) =ᶠ[𝓝 0]
      (fun s => phi s * g source.controlled) := by
    filter_upwards [hrayVector] with s hs
    have hc := congrFun hs source.controlled
    simpa [z, phi, Pi.smul_apply, smul_eq_mul] using hc
  have hderivEq := hrayComponent.deriv_eq
  rw [hcurrentDeriv, deriv_mul_const_field] at hderivEq
  have hmul : deriv phi 0 * g source.controlled = 0 := hderivEq.symm
  have hphi : deriv phi 0 = 0 :=
    (mul_eq_zero.mp hmul).resolve_right (ne_of_gt (hg source.controlled))
  simpa [z, phi] using hphi

theorem smoothLocalBranch_flux_isLocalMax
    {n : ℕ} (source : SquareSource n) (J : ℝ)
    (g q u lambda : Fin n → ℝ)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i)
    (hf : ∀ i, 0 < source.reactant.transpose.mulVec u i)
    (hh : ∀ i, 0 < source.product.transpose.mulVec u i)
    (hlambda : ∀ i, 0 ≤ lambda i) (hlambda0 : lambda ≠ 0)
    (hq : ∀ i, 1 < q i)
    (hratio : ∀ i, source.product.transpose.mulVec u i =
      q i * source.reactant.transpose.mulVec u i)
    (hmode : ControlledProductionMode source g)
    (hreduced : NoncontrolledSteadyJacobianInjective source
      (literalCurrentJacobian source J g q))
    (hkernel : (literalCurrentJacobian source J g q).mulVec u = 0)
    (hcontrol : u source.controlled = 1)
    (hannih : ∀ w : Fin n → ℝ,
      dotProduct lambda ((literalCurrentJacobian source J g q).mulVec w) = 0) :
    IsLocalMax (controlledBranchFlux source J g q
      (smoothLocalBranch source J g q hreduced)) 0 := by
  let z := smoothLocalBranch source J g q hreduced
  let phi := controlledBranchFlux source J g q z
  have hcurvature : deriv (deriv phi) 0 < 0 := by
    simpa [z, phi] using smoothLocalBranch_flux_secondDerivative_neg
      source J g q u lambda hJ hg hf hh hlambda hlambda0 hq hratio
        hmode hreduced hkernel hcontrol hannih
  have hfirst : deriv phi 0 = 0 := by
    simpa [z, phi] using smoothLocalBranch_flux_firstDerivative_eq_zero
      source J g q u hJ hg hq hmode hreduced hkernel hcontrol
  have hzcont := smoothLocalBranch_contDiffAt source J g q hreduced
  have hdrift := (reconstructedLogSourceDrift_contDiff source J g q).contDiffAt.comp
    0 hzcont
  have hphiContDiff := (contDiffAt_pi.mp hdrift) source.controlled
  have hcontinuous : ContinuousAt phi 0 := by
    simpa [z, phi, controlledBranchFlux] using hphiContDiff.continuousAt
  simpa [z, phi] using isLocalMax_of_deriv_deriv_neg hcurvature hfirst hcontinuous

theorem strictLocalMaxAt_of_secondDerivative_neg
    {f : ℝ → ℝ} {x₀ : ℝ}
    (hf : ContDiffAt ℝ ⊤ f x₀)
    (hsecond : deriv (deriv f) x₀ < 0)
    (hfirst : deriv f x₀ = 0) :
    IsStrictLocalMaxAt f x₀ := by
  have hlocal : IsLocalMax f x₀ :=
    isLocalMax_of_deriv_deriv_neg hsecond hfirst hf.continuousAt
  have hsign : ∀ᶠ y in 𝓝 x₀,
      sign (deriv f y) = sign (x₀ - y) :=
    eventually_nhdsWithin_sign_eq_of_deriv_neg hsecond hfirst
  have hfinite : ContDiffAt ℝ 1 f x₀ := hf.of_le (by simp)
  have hcontinuousNearby : ∀ᶠ y in 𝓝 x₀, ContinuousAt f y := by
    filter_upwards [hfinite.eventually (by simp)] with y hy
    exact hy.continuousAt
  have hgood : ∀ᶠ y in 𝓝 x₀,
      ContinuousAt f y ∧ sign (deriv f y) = sign (x₀ - y) ∧ f y ≤ f x₀ := by
    filter_upwards [hcontinuousNearby, hsign, hlocal] with y hycont hysign hyle
    exact ⟨hycont, hysign, hyle⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hgood
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x₀ hε),
    self_mem_nhdsWithin] with x hxball hxne
  have hxne' : x ≠ x₀ := by simpa using hxne
  have hxle : f x ≤ f x₀ := (hball hxball).2.2
  apply lt_of_le_of_ne hxle
  intro heq
  have hvalues : f x = f x₀ := le_antisymm hxle (le_of_eq heq.symm)
  rcases hxne'.lt_or_gt with hxlt | hxgt
  · have hcont : ContinuousOn f (Set.Icc x x₀) := by
      intro y hy
      have hyball : y ∈ Metric.ball x₀ ε := by
        rw [Metric.mem_ball, Real.dist_eq]
        have hxabs : |x - x₀| < ε := by
          simpa [Real.dist_eq] using hxball
        rw [abs_of_neg (sub_neg.mpr hxlt)] at hxabs
        rw [abs_of_nonpos (sub_nonpos.mpr hy.2)]
        linarith [hy.1]
      exact (hball hyball).1.continuousWithinAt
    obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero hxlt hcont hvalues
    have hcball : c ∈ Metric.ball x₀ ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have hxabs : |x - x₀| < ε := by
        simpa [Real.dist_eq] using hxball
      rw [abs_of_neg (sub_neg.mpr hxlt)] at hxabs
      rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hc.2))]
      linarith [hc.1]
    have hsignc := (hball hcball).2.1
    rw [hc0, sign_zero, sign_pos (sub_pos.mpr hc.2)] at hsignc
    exact SignType.noConfusion hsignc
  · have hcont : ContinuousOn f (Set.Icc x₀ x) := by
      intro y hy
      have hyball : y ∈ Metric.ball x₀ ε := by
        rw [Metric.mem_ball, Real.dist_eq]
        have hxabs : |x - x₀| < ε := by
          simpa [Real.dist_eq] using hxball
        rw [abs_of_pos (sub_pos.mpr hxgt)] at hxabs
        rw [abs_of_nonneg (sub_nonneg.mpr hy.1)]
        linarith [hy.2]
      exact (hball hyball).1.continuousWithinAt
    obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero hxgt hcont hvalues.symm
    have hcball : c ∈ Metric.ball x₀ ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have hxabs : |x - x₀| < ε := by
        simpa [Real.dist_eq] using hxball
      rw [abs_of_pos (sub_pos.mpr hxgt)] at hxabs
      rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt hc.1))]
      linarith [hc.2]
    have hsignc := (hball hcball).2.1
    rw [hc0, sign_zero, sign_neg (sub_neg.mpr hc.1)] at hsignc
    exact SignType.noConfusion hsignc

theorem smoothLocalBranch_flux_isStrictLocalMax
    {n : ℕ} (source : SquareSource n) (J : ℝ)
    (g q u lambda : Fin n → ℝ)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i)
    (hf : ∀ i, 0 < source.reactant.transpose.mulVec u i)
    (hh : ∀ i, 0 < source.product.transpose.mulVec u i)
    (hlambda : ∀ i, 0 ≤ lambda i) (hlambda0 : lambda ≠ 0)
    (hq : ∀ i, 1 < q i)
    (hratio : ∀ i, source.product.transpose.mulVec u i =
      q i * source.reactant.transpose.mulVec u i)
    (hmode : ControlledProductionMode source g)
    (hreduced : NoncontrolledSteadyJacobianInjective source
      (literalCurrentJacobian source J g q))
    (hkernel : (literalCurrentJacobian source J g q).mulVec u = 0)
    (hcontrol : u source.controlled = 1)
    (hannih : ∀ w : Fin n → ℝ,
      dotProduct lambda ((literalCurrentJacobian source J g q).mulVec w) = 0) :
    IsStrictLocalMaxAt (controlledBranchFlux source J g q
      (smoothLocalBranch source J g q hreduced)) 0 := by
  let z := smoothLocalBranch source J g q hreduced
  let phi := controlledBranchFlux source J g q z
  have hzcont := smoothLocalBranch_contDiffAt source J g q hreduced
  have hdrift := (reconstructedLogSourceDrift_contDiff source J g q).contDiffAt.comp
    0 hzcont
  have hphi : ContDiffAt ℝ ⊤ phi 0 := by
    simpa [z, phi, controlledBranchFlux] using
      (contDiffAt_pi.mp hdrift) source.controlled
  have hcurvature : deriv (deriv phi) 0 < 0 := by
    simpa [z, phi] using smoothLocalBranch_flux_secondDerivative_neg
      source J g q u lambda hJ hg hf hh hlambda hlambda0 hq hratio
        hmode hreduced hkernel hcontrol hannih
  have hfirst : deriv phi 0 = 0 := by
    simpa [z, phi] using smoothLocalBranch_flux_firstDerivative_eq_zero
      source J g q u hJ hg hq hmode hreduced hkernel hcontrol
  simpa [z, phi] using
    strictLocalMaxAt_of_secondDerivative_neg hphi hcurvature hfirst

end
end OptimalAffinityRealizability
