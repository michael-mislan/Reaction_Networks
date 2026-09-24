import proofs.OscillatoryCores.LinearShootingCurves

namespace OscillatoryCores

open Set Filter
open scoped ContDiff Topology

theorem stable_flow_return_hasDerivAt
    (g : ShootingState → ShootingState) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (Φ : ℝ → ShootingState → ShootingState) (hΦ0 : ∀ x, Φ 0 x=x)
    (hΦ : ∀ x t, HasDerivAt (fun s => Φ s x) (g (Φ t x)) t)
    (c : ShootingState) (R : ℝ) (hge : ∀ x ∈ Metric.closedBall c R, g x=augmentedField x)
    (t w l T : ℝ) (u v e : State)
    (hu : normalizedLinear t u = -w • v) (hv : normalizedLinear t v=w • u)
    (he : normalizedLinear t e=l • e) (hT : w*T=2*Real.pi)
    (hball : ∀ s ∈ Icc (0 : ℝ) 1,
      augmentedLinearCurve t T (centerCurve u v w) s ∈ Metric.ball c R) :
    HasDerivAt (fun a : ℝ => (Φ 1 (t,0,T,u+a • e)).2.2.2-(u+a • e))
      ((Real.exp (l*T)-1) • e) 0 := by
  let y := fun a => augmentedLinearCurve t T (stableVariationCurve u v e w l a)
  have hyc : ∀ s ∈ Icc (0 : ℝ) 1, ContinuousAt (fun q : ℝ × ℝ => y q.1 q.2) (0,s) := by
    intro s _
    dsimp [y,augmentedLinearCurve,stableVariationCurve,centerCurve]
    fun_prop
  have hy : ∀ᶠ a in 𝓝 (0 : ℝ), ∀ s, HasDerivAt (y a) (augmentedField (y a s)) s := by
    apply Filter.Eventually.of_forall
    intro a s
    exact augmentedLinearCurve_hasDerivAt t T _
      (fun s => stableVariationCurve_hasDerivAt t u v e w l a s hu hv he) s
  have hball' : ∀ s ∈ Icc (0 : ℝ) 1, y 0 s ∈ Metric.ball c R := by
    simpa [y,augmentedLinearCurve,stableVariationCurve] using hball
  have hend := localized_family_endpoint (0 : ℝ) g hg hgc Φ hΦ0 hΦ c R hge y hyc hy hball'
  have heq : (fun a => (Φ 1 (t,0,T,u+a • e)).2.2.2-(u+a • e)) =ᶠ[𝓝 (0 : ℝ)]
      (fun a => stableVariationCurve u v e w l a T-stableVariationCurve u v e w l a 0) := by
    filter_upwards [hend] with a ha
    have hh := congrArg (fun x : ShootingState => x.2.2.2) ha
    simpa [y,augmentedLinearCurve,stableVariationCurve_zero] using
      congrArg (fun x => x-(u+a • e)) hh
  exact (stable_return_hasDerivAt u v e w l T hT).congr_of_eventuallyEq heq

theorem period_flow_return_hasDerivAt
    (g : ShootingState → ShootingState) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (Φ : ℝ → ShootingState → ShootingState) (hΦ0 : ∀ x, Φ 0 x=x)
    (hΦ : ∀ x t, HasDerivAt (fun s => Φ s x) (g (Φ t x)) t)
    (c : ShootingState) (R : ℝ) (hge : ∀ x ∈ Metric.closedBall c R, g x=augmentedField x)
    (t w T : ℝ) (u v : State)
    (hu : normalizedLinear t u = -w • v) (hv : normalizedLinear t v=w • u)
    (hT : w*T=2*Real.pi)
    (hball : ∀ s ∈ Icc (0 : ℝ) 1,
      augmentedLinearCurve t T (centerCurve u v w) s ∈ Metric.ball c R) :
    HasDerivAt (fun P => (Φ 1 (t,0,P,u)).2.2.2-u) (-w • v) T := by
  let y := fun P => augmentedLinearCurve t P (centerCurve u v w)
  have hyc : ∀ s ∈ Icc (0 : ℝ) 1, ContinuousAt (fun q : ℝ × ℝ => y q.1 q.2) (T,s) := by
    intro s _
    dsimp [y,augmentedLinearCurve,centerCurve]
    fun_prop
  have hy : ∀ᶠ P in 𝓝 T, ∀ s, HasDerivAt (y P) (augmentedField (y P s)) s := by
    apply Filter.Eventually.of_forall
    intro P s
    exact augmentedLinearCurve_hasDerivAt t P _
      (fun s => centerCurve_hasDerivAt t u v w s hu hv) s
  have hend := localized_family_endpoint T g hg hgc Φ hΦ0 hΦ c R hge y hyc hy hball
  have heq : (fun P => (Φ 1 (t,0,P,u)).2.2.2-u) =ᶠ[𝓝 T]
      (fun P => centerCurve u v w P-u) := by
    filter_upwards [hend] with P hP
    have hh := congrArg (fun x : ShootingState => x.2.2.2) hP
    simpa [y,augmentedLinearCurve,centerCurve] using congrArg (fun x => x-u) hh
  exact (period_return_hasDerivAt t u v w T hu hv hT).congr_of_eventuallyEq heq

end OscillatoryCores
