import proofs.OscillatoryCores.ShootingResidual
import proofs.OscillatoryCores.ParameterReturn
import proofs.OscillatoryCores.OtherReturns

namespace OscillatoryCores

open Set Filter
open scoped ContDiff Topology Matrix

/-- The exact border is the derivative of the actual localized nonlinear
shooting residual at zero amplitude. -/
theorem shootingResidual_hasFDerivAt
    (g : ShootingState → ShootingState) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (Φ : ℝ → ShootingState → ShootingState) (hΦ0 : ∀ x, Φ 0 x=x)
    (hΦ : ∀ x t, HasDerivAt (fun s => Φ s x) (g (Φ t x)) t)
    (hΦc : ContDiff ℝ 1 (Φ 1))
    (c : ShootingState) (R : ℝ) (hge : ∀ x ∈ Metric.closedBall c R, g x=augmentedField x)
    (a b : ℝ → ℝ) (u v : ℝ → State) (t T da db l m : ℝ) (du dv e f : State)
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t)
    (hu : HasDerivAt u du t) (hv : HasDerivAt v dv t) (hus : ContDiffAt ℝ 1 u t)
    (ha0 : a t=0) (hbT : b t*T=2*Real.pi)
    (hmodes : ∀ᶠ p in 𝓝 t,
      normalizedLinear p (u p)=a p • u p-b p • v p ∧
      normalizedLinear p (v p)=b p • u p+a p • v p)
    (hLe : normalizedLinear t e=l • e) (hLf : normalizedLinear t f=m • f)
    (hball : ∀ s ∈ Icc (0 : ℝ) 1,
      augmentedLinearCurve t T (centerCurve (u t) (v t) (b t)) s ∈ Metric.ball c R) :
    HasFDerivAt (shootingResidual Φ u e f 0)
      (shootingLinear T (b t) da db l m (u t) (v t) e f) ![t,T,0,0] := by
  have hm := hmodes.self_of_nhds
  have hLu : normalizedLinear t (u t) = -b t • v t := by simpa [ha0] using hm.1
  have hLv : normalizedLinear t (v t) = b t • u t := by simpa [ha0] using hm.2
  have hball' : ∀ s ∈ Icc (0 : ℝ) 1,
      augmentedLinearCurve t T (growingCurve (u t) (v t) (a t) (b t)) s ∈ Metric.ball c R := by
    simpa [augmentedLinearCurve,growingCurve,ha0] using hball
  have hparam := parameter_return_hasDerivAt g hg hgc Φ hΦ0 hΦ c R hge a b u v t T da db du dv
    ha hb hu hv ha0 hbT hmodes hball'
  have hperiod := period_flow_return_hasDerivAt g hg hgc Φ hΦ0 hΦ c R hge t (b t) T (u t) (v t)
    hLu hLv hbT hball
  have hstable1 := stable_flow_return_hasDerivAt g hg hgc Φ hΦ0 hΦ c R hge t (b t) l T (u t) (v t) e
    hLu hLv hLe hbT hball
  have hstable2 := stable_flow_return_hasDerivAt g hg hgc Φ hΦ0 hΦ c R hge t (b t) m T (u t) (v t) f
    hLu hLv hLf hbT hball
  have hps : HasDerivAt (fun s => (Φ 1 (t+s,0,T,u (t+s))).2.2.2-u (t+s))
      ((T*da) • u t-(T*db) • v t) 0 := by
    have hp : HasDerivAt (fun p => (Φ 1 (p,0,T,u p)).2.2.2-u p)
      ((T*da) • u t-(T*db) • v t) (t+0) := by simpa using hparam
    simpa only [Function.comp_def,one_smul] using hp.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_add t)
  have hTs : HasDerivAt (fun s => (Φ 1 (t,0,T+s,u t)).2.2.2-u t) (-b t • v t) 0 := by
    have hp : HasDerivAt (fun P => (Φ 1 (t,0,P,u t)).2.2.2-u t) (-b t • v t) (T+0) := by
      simpa using hperiod
    simpa only [Function.comp_def,one_smul] using hp.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_add T)
  have hs := shootingResidual_contDiffAt Φ hΦc u e f 0 ![t,T,0,0] hus
  have hi : DifferentiableAt ℝ (fun x : State => ((0 : ℝ),x)) ![t,T,0,0] := by fun_prop
  have hdiff : DifferentiableAt ℝ (shootingResidual Φ u e f 0) ![t,T,0,0] :=
    (hs.differentiableAt (by norm_num)).comp _ hi
  apply hasFDerivAt_of_coordinate_curves _ _ _ hdiff
  intro i
  fin_cases i
  · simpa [shootingResidual,shootingInitial,shootingLinear,Pi.single_apply] using hps
  · simpa [shootingResidual,shootingInitial,shootingLinear,Pi.single_apply] using hTs
  · simpa [shootingResidual,shootingInitial,shootingLinear,Pi.single_apply] using hstable1
  · simpa [shootingResidual,shootingInitial,shootingLinear,Pi.single_apply] using hstable2

end OscillatoryCores
