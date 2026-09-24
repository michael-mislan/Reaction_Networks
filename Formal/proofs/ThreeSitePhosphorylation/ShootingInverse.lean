import proofs.ThreeSitePhosphorylation.ShootingMap
import proofs.ThreeSitePhosphorylation.PathKernel

namespace ThreeSitePhosphorylation
noncomputable section
open scoped Topology
set_option maxHeartbeats 200000

theorem shooting_partial_invertible (r w : ℝ) (hw : 0<w)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0)
    (ψ : FlowData → SourcePath)
    (hψ : ContDiffAt ℝ ⊤ ψ ((0,(r,2*Real.pi/w)),realPart (adjugateVector (Complex.I*(w:ℂ)))))
    (hb : ψ ((0,(r,2*Real.pi/w)),realPart (adjugateVector (Complex.I*(w:ℂ))))=
      referencePath (realPart (adjugateVector (Complex.I*(w:ℂ))))
        (imagPart (adjugateVector (Complex.I*(w:ℂ)))) w (2*Real.pi/w))
    (he : ∀ᶠ p in 𝓝 ((0,(r,2*Real.pi/w)),realPart (adjugateVector (Complex.I*(w:ℂ)))),
      pathResidual (p,ψ p)=0) :
    (fderiv ℝ (shootingMap ψ (sourceGauge r w) (realPart (adjugateVector (Complex.I*(w:ℂ)))))
      (0,(realPart (adjugateVector (Complex.I*(w:ℂ))),(r:ℂ)+Complex.I*((2*Real.pi/w:ℝ):ℂ))) ∘L
        ContinuousLinearMap.inr ℝ ℝ ShootingState).IsInvertible := by
  let x := realPart (adjugateVector (Complex.I*(w:ℂ)))
  let T := 2*Real.pi/w
  let s0 : ShootingState := (x,(r:ℂ)+Complex.I*(T:ℂ))
  let F := shootingMap ψ (sourceGauge r w) x
  let A := fderiv ℝ F (0,s0) ∘L ContinuousLinearMap.inr ℝ ℝ ShootingState
  have hs : ContDiffAt ℝ ⊤ F (0,s0) :=
    shootingMap_smooth ψ (sourceGauge r w) x (0,s0) (by simpa [shootingArgument,s0] using hψ)
  have hker (d : ShootingState) (had : A d=0) : d=0 := by
    let q := fderiv ℝ ψ ((0,(r,T)),x) ((0,(d.2.re,d.2.im)),d.1)
    have hline := flowLine_derivative r T d.2.re d.2.im x d.1
    have hqd : HasDerivAt (fun s : ℝ => ψ ((0,(r+s*d.2.re,T+s*d.2.im)),x+s • d.1)) q 0 := by
      exact hψ.differentiableAt (by simp) |>.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp [x,T])
    have hev : ∀ᶠ s in 𝓝 (0:ℝ),
        pathResidual (((0,(r+s*d.2.re,T+s*d.2.im)),x+s • d.1),
          ψ ((0,(r+s*d.2.re,T+s*d.2.im)),x+s • d.1))=0 := by
      have hh := hline.continuousAt.tendsto
      simp only [zero_mul,add_zero,zero_smul] at hh
      exact hh.eventually he
    have hq := variational_path_equation r T d.2.re d.2.im x d.1 _ q hqd hev
    simp only [zero_mul,add_zero,zero_smul] at hq
    have hb' : ψ ((0,(r,T)),x)=
        referencePath x (imagPart (adjugateVector (Complex.I*(w:ℂ)))) w T := hb
    rw [hb'] at hq
    have hsd := shootingMap_direction ψ (sourceGauge r w) x d.1 r T d.2.re d.2.im q hqd
    have hfd := hs.differentiableAt (by simp) |>.hasFDerivAt.comp_hasDerivAt_of_eq 0
      (shootingLine_derivative r T x d) (by simp [s0])
    have hunique := hsd.unique hfd
    change (q ⟨1,by norm_num⟩-d.1,sourceGauge r w d.1)=A d at hunique
    rw [had] at hunique
    have h1 : q ⟨1,by norm_num⟩=d.1 := sub_eq_zero.mp (congrArg Prod.fst hunique)
    have hn : sourceLeft r (Complex.I*(w:ℂ)) (complexify d.1)=0 := congrArg Prod.snd hunique
    have h0 : q ⟨0,by norm_num⟩=d.1 := by
      exact (integralVariation_eq d.1 _ q hq ⟨0,by norm_num⟩).symm.trans
        (integralVariation_initial d.1 _)
    obtain ⟨hdr,hdt,hdx⟩ := periodic_path_kernel r w hw hp d.2.re d.2.im d.1 q hq
      (h1.trans h0.symm) hn
    apply Prod.ext hdx
    exact Complex.ext hdr hdt
  have hinj : Function.Injective A := by
    intro d e h
    exact sub_eq_zero.mp (hker (d-e) (by rw [map_sub,h,sub_self]))
  have hsurj : Function.Surjective A :=
    (LinearMap.injective_iff_surjective (f := A.toLinearMap)).mp hinj
  obtain ⟨v,hv⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj,hsurj⟩
  exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ ShootingState v,hv⟩

end
end ThreeSitePhosphorylation
