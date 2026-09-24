import proofs.OscillatoryCores.ShootingDerivative
import Mathlib.Analysis.Calculus.ImplicitContDiff

namespace OscillatoryCores

open Set Filter
open scoped ContDiff Topology Matrix

theorem shootingResidual_base_zero
    (g : ShootingState → ShootingState) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (Φ : ℝ → ShootingState → ShootingState) (hΦ0 : ∀ x, Φ 0 x=x)
    (hΦ : ∀ x t, HasDerivAt (fun s => Φ s x) (g (Φ t x)) t)
    (c : ShootingState) (R : ℝ) (hge : ∀ x ∈ Metric.closedBall c R, g x=augmentedField x)
    (t w T : ℝ) (u : ℝ → State) (v e f : State)
    (hu : normalizedLinear t (u t) = -w • v) (hv : normalizedLinear t v=w • u t)
    (hT : w*T=2*Real.pi)
    (hball : ∀ s ∈ Icc (0 : ℝ) 1,
      augmentedLinearCurve t T (centerCurve (u t) v w) s ∈ Metric.ball c R) :
    shootingResidual Φ u e f 0 ![t,T,0,0]=0 := by
  let y := augmentedLinearCurve t T (centerCurve (u t) v w)
  have he := localized_curve_eq_flow g hg hgc Φ hΦ0 hΦ c R hge y
    (augmentedLinearCurve_hasDerivAt t T _
      (fun s => centerCurve_hasDerivAt t (u t) v w s hu hv))
    (fun s hs => Metric.ball_subset_closedBall (hball s hs)) 1 ⟨by norm_num,le_rfl⟩
  have hproj := congrArg (fun x : ShootingState => x.2.2.2) he
  have hreturn : (Φ 1 (t,0,T,u t)).2.2.2=u t := by
    simpa [y,augmentedLinearCurve,centerCurve,hT] using hproj
  simpa [shootingResidual,shootingInitial] using sub_eq_zero.mpr hreturn

/-- The implicit-function step constructs zeros of the actual shooting
residual, once its verified derivative is invertible. -/
theorem shooting_zero_branch
    (Φ : ℝ → ShootingState → ShootingState) (hΦc : ContDiff ℝ 1 (Φ 1))
    (u : ℝ → State) (e f : State) (x : State) (hu : ContDiffAt ℝ 1 u (x 0))
    (D : State →L[ℝ] State) (hD : HasFDerivAt (shootingResidual Φ u e f 0) D x)
    (hInv : D.IsInvertible) (hzero : shootingResidual Φ u e f 0 x=0) :
    ∃ z : ℝ → State, z 0=x ∧ ContDiffAt ℝ 1 z 0 ∧
      (∀ᶠ r in 𝓝 (0 : ℝ), shootingResidual Φ u e f r (z r)=0) := by
  let F := fun p : ℝ × State => shootingResidual Φ u e f p.1 p.2
  have hc : ContDiffAt ℝ 1 F (0,x) := shootingResidual_contDiffAt Φ hΦc u e f 0 x hu
  have hdF := (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hin : HasFDerivAt (fun v : State => ((0 : ℝ),v))
      (ContinuousLinearMap.inr ℝ ℝ State) x := by
    simpa using (hasFDerivAt_const (0 : ℝ) x).prodMk (hasFDerivAt_id x)
  have heq : fderiv ℝ F (0,x) ∘L ContinuousLinearMap.inr ℝ ℝ State=D := by
    have hh : HasFDerivAt (shootingResidual Φ u e f 0)
        (fderiv ℝ F (0,x) ∘L ContinuousLinearMap.inr ℝ ℝ State) x := by
      simpa only [F,Function.comp_def] using hdF.comp x hin
    exact hh.unique hD
  have hi : (fderiv ℝ F (0,x) ∘L ContinuousLinearMap.inr ℝ ℝ State).IsInvertible := by
    rw [heq]
    exact hInv
  refine ⟨hc.implicitFunction (by norm_num) hi,hc.implicitFunction_apply_self (by norm_num) hi,
    hc.contDiffAt_implicitFunction (by norm_num) hi,?_⟩
  simpa only [F,hzero] using hc.eventually_apply_implicitFunction (by norm_num) hi

end OscillatoryCores
