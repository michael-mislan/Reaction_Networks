import proofs.OscillatoryCores.AugmentedLinearCurve

namespace OscillatoryCores

open Set Filter
open scoped ContDiff Topology

theorem parameter_curve_continuousAt
    (a b : ℝ → ℝ) (u v : ℝ → State) (t T s : ℝ)
    (ha : ContinuousAt a t) (hb : ContinuousAt b t)
    (hu : ContinuousAt u t) (hv : ContinuousAt v t) :
    ContinuousAt (fun p : ℝ × ℝ => augmentedLinearCurve p.1 T
      (growingCurve (u p.1) (v p.1) (a p.1) (b p.1)) p.2) (t,s) := by
  have hau : ContinuousAt (fun p : ℝ × ℝ => a p.1) (t,s) := ha.comp continuousAt_fst
  have hbu : ContinuousAt (fun p : ℝ × ℝ => b p.1) (t,s) := hb.comp continuousAt_fst
  have huu : ContinuousAt (fun p : ℝ × ℝ => u p.1) (t,s) := hu.comp continuousAt_fst
  have hvu : ContinuousAt (fun p : ℝ × ℝ => v p.1) (t,s) := hv.comp continuousAt_fst
  have hs : ContinuousAt (fun p : ℝ × ℝ => T*p.2) (t,s) := by fun_prop
  have he : ContinuousAt (fun p : ℝ × ℝ => Real.exp (a p.1*(T*p.2))) (t,s) :=
    Real.continuous_exp.continuousAt.comp (hau.mul hs)
  have hc : ContinuousAt (fun p : ℝ × ℝ => Real.cos (b p.1*(T*p.2))) (t,s) :=
    Real.continuous_cos.continuousAt.comp (hbu.mul hs)
  have hsi : ContinuousAt (fun p : ℝ × ℝ => Real.sin (b p.1*(T*p.2))) (t,s) :=
    Real.continuous_sin.continuousAt.comp (hbu.mul hs)
  exact continuousAt_fst.prodMk (continuousAt_const.prodMk (continuousAt_const.prodMk
    (he.smul ((hc.smul huu).sub (hsi.smul hvu)))))

/-- The source-parameter column is obtained from an actual localized flow,
not merely from a formal derivative of a proposed return map. -/
theorem parameter_return_hasDerivAt
    (g : ShootingState → ShootingState) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (Φ : ℝ → ShootingState → ShootingState)
    (hΦ0 : ∀ x, Φ 0 x=x)
    (hΦ : ∀ x t, HasDerivAt (fun s => Φ s x) (g (Φ t x)) t)
    (c : ShootingState) (R : ℝ)
    (hge : ∀ x ∈ Metric.closedBall c R, g x=augmentedField x)
    (a b : ℝ → ℝ) (u v : ℝ → State) (t T da db : ℝ) (du dv : State)
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t)
    (hu : HasDerivAt u du t) (hv : HasDerivAt v dv t)
    (ha0 : a t=0) (hbT : b t*T=2*Real.pi)
    (hmodes : ∀ᶠ p in 𝓝 t,
      normalizedLinear p (u p)=a p • u p-b p • v p ∧
      normalizedLinear p (v p)=b p • u p+a p • v p)
    (hball : ∀ s ∈ Icc (0 : ℝ) 1, augmentedLinearCurve t T
      (growingCurve (u t) (v t) (a t) (b t)) s ∈ Metric.ball c R) :
    HasDerivAt (fun p => (Φ 1 (p,0,T,u p)).2.2.2-u p)
      ((T*da) • u t-(T*db) • v t) t := by
  let y := fun p => augmentedLinearCurve p T (growingCurve (u p) (v p) (a p) (b p))
  have hyc : ∀ s ∈ Icc (0 : ℝ) 1, ContinuousAt (fun q : ℝ × ℝ => y q.1 q.2) (t,s) := by
    intro s _
    exact parameter_curve_continuousAt a b u v t T s ha.continuousAt hb.continuousAt
      hu.continuousAt hv.continuousAt
  have hy : ∀ᶠ p in 𝓝 t, ∀ s, HasDerivAt (y p) (augmentedField (y p s)) s := by
    filter_upwards [hmodes] with p hp
    intro s
    exact augmentedLinearCurve_hasDerivAt p T _
      (fun s => growingCurve_hasDerivAt p (u p) (v p) (a p) (b p) s hp.1 hp.2) s
  have hend := localized_family_endpoint t g hg hgc Φ hΦ0 hΦ c R hge y hyc hy hball
  have heq : (fun p => (Φ 1 (p,0,T,u p)).2.2.2-u p) =ᶠ[𝓝 t]
      (fun p => growingCurve (u p) (v p) (a p) (b p) T-u p) := by
    filter_upwards [hend] with p hp
    have hp' := congrArg (fun x : ShootingState => x.2.2.2) hp
    simpa [y,augmentedLinearCurve,growingCurve,centerCurve] using congrArg (fun x => x-u p) hp'
  exact (moving_return_hasDerivAt a b u v t T da db du dv ha hb hu hv ha0 hbT).congr_of_eventuallyEq heq

end OscillatoryCores
