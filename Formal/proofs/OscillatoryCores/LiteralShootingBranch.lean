import proofs.OscillatoryCores.ShootingBranch
import proofs.OscillatoryCores.SourceShootingData

namespace OscillatoryCores

open Set Filter
open scoped ContDiff Topology Matrix

/-- A zero-residual branch for the literal field, retaining the exact
localization region and a nonzero base displacement velocity. -/
theorem literal_shooting_zero_branch :
    ∃ t T R : ℝ, ∃ u : ℝ → State, ∃ e f : State,
    ∃ g : ShootingState → ShootingState, ∃ Φ : ℝ → ShootingState → ShootingState,
    ∃ z : ℝ → State,
      0 < t ∧ 0 < T ∧ 0 < R ∧ ContinuousAt u t ∧
      (∀ x ∈ Metric.closedBall (0 : ShootingState) R, g x=augmentedField x) ∧
      (∀ x, Φ 0 x=x) ∧
      (∀ x s, HasDerivAt (fun s => Φ s x) (g (Φ s x)) s) ∧
      (∀ s p x, Φ s (Φ p x)=Φ (p+s) x) ∧
      Continuous (fun p : ℝ × ShootingState => Φ p.1 p.2) ∧
      z 0=![t,T,0,0] ∧ ContinuousAt z 0 ∧
      (∀ᶠ r in 𝓝 (0 : ℝ), shootingResidual Φ u e f r (z r)=0) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, Φ s (shootingInitial u e f 0 (z 0)) ∈ Metric.ball 0 R) ∧
      amplitudeField t 0 (u t) ≠ 0 := by
  obtain ⟨t,w,T,l,m,eig,q,d,e,f,ht,hw,hTeq,hT,hz,heig,hes,hed,hdr,hqs,hq3,hqe,
    hlm,hm,he,hf,hLe,hLf,hInv⟩ := source_shooting_data
  let a : ℝ → ℝ := fun s => (eig s).re
  let b : ℝ → ℝ := fun s => (eig s).im
  let u : ℝ → State := fun s i => (q s i).re
  let v : ℝ → State := fun s i => (q s i).im
  have hus : ContDiffAt ℝ ∞ u t := by
    apply contDiffAt_pi.mpr
    intro i
    exact Complex.reCLM.contDiff.contDiffAt.comp t ((contDiffAt_pi.mp hqs) i)
  have hvs : ContDiffAt ℝ ∞ v t := by
    apply contDiffAt_pi.mpr
    intro i
    exact Complex.imCLM.contDiff.contDiffAt.comp t ((contDiffAt_pi.mp hqs) i)
  have ha : HasDerivAt a d.re t := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hed
  have hb : HasDerivAt b d.im t := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hed
  have hu := (hus.differentiableAt (by simp)).hasDerivAt
  have hv := (hvs.differentiableAt (by simp)).hasDerivAt
  have ha0 : a t=0 := by simp [a,heig]
  have hbw : b t=w := by simp [b,heig]
  have hbT : b t*T=2*Real.pi := by rw [hbw,hTeq]; field_simp
  have hmodes : ∀ᶠ p in 𝓝 t,
      normalizedLinear p (u p)=a p • u p-b p • v p ∧
      normalizedLinear p (v p)=b p • u p+a p • v p := by
    filter_upwards [hqe] with p hp
    exact complex_eigenvector_real_modes p (eig p) (q p) hp
  have hmode := hmodes.self_of_nhds
  have hLu : normalizedLinear t (u t) = -b t • v t := by simpa [ha0] using hmode.1
  have hLv : normalizedLinear t (v t) = b t • u t := by simpa [ha0] using hmode.2
  let y := augmentedLinearCurve t T (centerCurve (u t) (v t) (b t))
  have hyc : Continuous y := by
    change Continuous (fun s => (t,(0 : ℝ),T,
      Real.cos (b t*(T*s)) • u t-Real.sin (b t*(T*s)) • v t))
    fun_prop
  have hycompact : IsCompact (y '' Icc (0 : ℝ) 1) := isCompact_Icc.image hyc
  obtain ⟨R,hR,hRb⟩ := hycompact.isBounded.subset_ball_lt 0 (0 : ShootingState)
  have hball : ∀ s ∈ Icc (0 : ℝ) 1, y s ∈ Metric.ball 0 R := fun s hs => hRb ⟨s,hs,rfl⟩
  obtain ⟨g,hge,hg,hgc,Φ,hΦ0,hΦ,hΦc,hΦadd,hΦjoint⟩ := augmented_cutoff_flow (0 : ShootingState) hR
  have hΦ1 : ContDiff ℝ 1 (Φ 1) := hΦc 1
  have hD := shootingResidual_hasFDerivAt g hg hgc Φ hΦ0 hΦ hΦ1 0 R hge a b u v t T d.re d.im l m
    _ _ e f ha hb hu hv (hus.of_le (by simp)) ha0 hbT hmodes hLe hLf hball
  have hzero := shootingResidual_base_zero g hg hgc Φ hΦ0 hΦ 0 R hge t (b t) T u (v t) e f
    hLu hLv hbT hball
  have hinv : (shootingLinear T (b t) d.re d.im l m (u t) (v t) e f).IsInvertible := by
    simpa only [hbw] using hInv
  obtain ⟨z,hz0,hzs,hzr⟩ := shooting_zero_branch Φ hΦ1 u e f ![t,T,0,0]
    (hus.of_le (by simp)) _ hD hinv hzero
  refine ⟨t,T,R,u,e,f,g,Φ,z,ht,hT,hR,hus.continuousAt,hge,hΦ0,hΦ,hΦadd,hΦjoint,
    hz0,hzs.continuousAt,hzr,?_,?_⟩
  · intro s hs
    have hcurve := localized_curve_eq_flow g hg hgc Φ hΦ0 hΦ 0 R hge y
      (augmentedLinearCurve_hasDerivAt t T _
        (fun s => centerCurve_hasDerivAt t (u t) (v t) (b t) s hLu hLv))
      (fun s hs => Metric.ball_subset_closedBall (hball s hs)) s hs
    have hstart : shootingInitial u e f 0 (z 0)=y 0 := by
      simp [hz0,shootingInitial,y,augmentedLinearCurve,centerCurve]
    rw [hstart,hcurve]
    exact hball s hs
  · rw [amplitudeField_zero,hLu]
    have hu0 : u t ≠ 0 := by
      intro h
      have hh := congrFun h 3
      simp [u,hq3 t] at hh
    have hv0 : v t ≠ 0 := by
      intro h
      rw [h,map_zero] at hLv
      exact ((smul_eq_zero.mp hLv.symm).resolve_left (by simpa [hbw] using ne_of_gt hw)) |> hu0
    exact smul_ne_zero (neg_ne_zero.mpr (by simpa [hbw] using ne_of_gt hw)) hv0

end OscillatoryCores
