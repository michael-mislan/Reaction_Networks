import proofs.OscillatoryCores.AugmentedField
import proofs.OscillatoryCores.ShootingInverse

namespace OscillatoryCores

open scoped ContDiff BigOperators

noncomputable def shootingInitial (u : ℝ → State) (e f : State) (r : ℝ) (x : State) : ShootingState :=
  (x 0,r,x 1,u (x 0)+x 2 • e+x 3 • f)

noncomputable def shootingResidual (Φ : ℝ → ShootingState → ShootingState)
    (u : ℝ → State) (e f : State) (r : ℝ) (x : State) : State :=
  (Φ 1 (shootingInitial u e f r x)).2.2.2-(shootingInitial u e f r x).2.2.2

theorem shootingResidual_contDiffAt
    (Φ : ℝ → ShootingState → ShootingState) (hΦ : ContDiff ℝ 1 (Φ 1))
    (u : ℝ → State) (e f : State) (r : ℝ) (x : State)
    (hu : ContDiffAt ℝ 1 u (x 0)) :
    ContDiffAt ℝ 1 (fun p : ℝ × State => shootingResidual Φ u e f p.1 p.2) (r,x) := by
  have h0 : ContDiff ℝ 1 (fun p : ℝ × State => p.2 0) := by fun_prop
  have huc : ContDiffAt ℝ 1 (fun p : ℝ × State => u (p.2 0)) (r,x) := hu.comp (r,x) h0.contDiffAt
  have hi : ContDiffAt ℝ 1 (fun p : ℝ × State => shootingInitial u e f p.1 p.2) (r,x) := by
    unfold shootingInitial
    exact h0.contDiffAt.prodMk (contDiffAt_fst.prodMk
      ((by fun_prop : ContDiffAt ℝ 1 (fun p : ℝ × State => p.2 1) (r,x)).prodMk
        ((huc.add ((by fun_prop : ContDiffAt ℝ 1 (fun p : ℝ × State => p.2 2) (r,x)).smul contDiffAt_const)).add
          ((by fun_prop : ContDiffAt ℝ 1 (fun p : ℝ × State => p.2 3) (r,x)).smul contDiffAt_const))))
  exact ((hΦ.contDiffAt.comp (r,x) hi).snd.snd.snd).sub hi.snd.snd.snd

/-- Identify a finite-dimensional derivative from its four actual
one-variable coordinate curves. -/
theorem hasFDerivAt_of_coordinate_curves (F : State → State) (x : State)
    (D : State →L[ℝ] State) (hF : DifferentiableAt ℝ F x)
    (hc : ∀ i : Fin 4, HasDerivAt (fun s : ℝ => F (x+s • (Pi.single i 1 : State)))
      (D (Pi.single i 1)) 0) : HasFDerivAt F D x := by
  have he (i : Fin 4) : fderiv ℝ F x (Pi.single i 1)=D (Pi.single i 1) := by
    have hp : HasDerivAt (fun s : ℝ => x+s • (Pi.single i 1 : State)) (Pi.single i 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i 1 : State)).const_add x
    have hFx : HasFDerivAt F (fderiv ℝ F x) (x+(0 : ℝ) • (Pi.single i 1 : State)) := by
      simpa using hF.hasFDerivAt
    have hh := hFx.comp_hasDerivAt 0 hp
    exact hh.unique (hc i)
  have heq : fderiv ℝ F x=D := by
    apply ContinuousLinearMap.ext
    intro v
    have hv : (∑ i : Fin 4, v i • (Pi.single i 1 : State))=v := by
      ext i
      simp [Pi.single_apply]
    calc
      fderiv ℝ F x v = fderiv ℝ F x (∑ i : Fin 4, v i • (Pi.single i 1 : State)) := congrArg _ hv.symm
      _ = D (∑ i : Fin 4, v i • (Pi.single i 1 : State)) := by simp [he]
      _ = D v := congrArg D hv
  rw [← heq]
  exact hF.hasFDerivAt

end OscillatoryCores
