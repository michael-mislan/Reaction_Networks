import proofs.ThreeSitePhosphorylation.ShootingInverse

namespace ThreeSitePhosphorylation
noncomputable section
open scoped Topology

structure ClosedPathFamily (r w : ℝ) where
  parameters : ℝ → ShootingState
  paths : ℝ → SourcePath
  parameters_smooth : ContDiffAt ℝ ⊤ parameters 0
  paths_smooth : ContDiffAt ℝ ⊤ paths 0
  parameters_zero : parameters 0=
    (realPart (adjugateVector (Complex.I*(w:ℂ))),(r:ℂ)+Complex.I*((2*Real.pi/w:ℝ):ℂ))
  paths_zero : paths 0=referencePath (realPart (adjugateVector (Complex.I*(w:ℂ))))
    (imagPart (adjugateVector (Complex.I*(w:ℂ)))) w (2*Real.pi/w)
  residual : ∀ᶠ a in 𝓝 (0:ℝ), pathResidual (shootingArgument (a,parameters a),paths a)=0
  closed : ∀ᶠ a in 𝓝 (0:ℝ), paths a ⟨1,by norm_num⟩=(parameters a).1

theorem closed_path_family_exists (r w : ℝ) (hw : 0<w)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0) : Nonempty (ClosedPathFamily r w) := by
  let v := adjugateVector (Complex.I*(w:ℂ))
  let x := realPart v
  let T := 2*Real.pi/w
  let s0 : ShootingState := (x,(r:ℂ)+Complex.I*(T:ℂ))
  let u0 := referencePath x (imagPart v) w T
  have hev := (source_root_eigenvector r (Complex.I*(w:ℂ)) hp).2
  obtain ⟨ψ,hψ,hψ0,hres⟩ := smooth_full_interval_paths r T x u0
    (source_reference_solution r w T v hev)
  have hi := shooting_partial_invertible r w hw hp ψ hψ hψ0 hres
  have hs := shootingMap_smooth ψ (sourceGauge r w) x (0,s0)
    (by simpa [shootingArgument,s0] using hψ)
  have hzero : shootingMap ψ (sourceGauge r w) x (0,s0)=0 := by
    apply shootingMap_zero
    rw [hψ0]
    exact (referencePath_endpoints x (imagPart v) w (ne_of_gt hw)).2
  let b := hs.implicitFunction (by simp) hi
  have hb : ContDiffAt ℝ ⊤ b 0 := hs.contDiffAt_implicitFunction (by simp) hi
  have hb0 : b 0=s0 := hs.implicitFunction_apply_self (by simp) hi
  have hclosed : ∀ᶠ a in 𝓝 (0:ℝ), shootingMap ψ (sourceGauge r w) x (a,b a)=0 := by
    simpa only [hzero] using hs.eventually_apply_implicitFunction (by simp) hi
  have harg : ContDiffAt ℝ ⊤ (fun a => shootingArgument (a,b a)) 0 :=
    shootingArgument_smooth.contDiffAt.comp 0 (contDiffAt_id.prodMk hb)
  have harg0 : shootingArgument (0,b 0)=((0,(r,T)),x) := by
    rw [hb0]
    simp [shootingArgument,s0]
  have hpath : ContDiffAt ℝ ⊤ (fun a => ψ (shootingArgument (a,b a))) 0 := by
    apply ContDiffAt.comp 0 _ harg
    rwa [harg0]
  refine ⟨{
    parameters := b
    paths := fun a => ψ (shootingArgument (a,b a))
    parameters_smooth := hb
    paths_smooth := hpath
    parameters_zero := hb0
    paths_zero := by rw [harg0,hψ0]
    residual := ?_
    closed := ?_ }⟩
  · have ht := harg.continuousAt.tendsto
    rw [harg0] at ht
    exact ht.eventually hres
  · filter_upwards [hclosed] with a ha
    exact sub_eq_zero.mp (congrArg Prod.fst ha)

end
end ThreeSitePhosphorylation
