import proofs.OscillatoryCores.MovingModes

namespace OscillatoryCores

open Filter
open scoped ContDiff Topology Matrix

/-- A smooth, explicitly normalized moving eigenvector of the actual matrix. -/
theorem moving_eigenvector_branch {t : ℝ} (ht : 0 < t)
    (hz : crossingPolynomial t=0) :
    ∃ eig : ℝ → ℂ, ∃ q : ℝ → (Fin 4 → ℂ), ∃ d : ℂ,
      eig t=Complex.I*(spectralFrequency t : ℂ) ∧
      ContDiffAt ℝ ∞ eig t ∧ HasDerivAt eig d t ∧ 0 < d.re ∧
      ContDiffAt ℝ ∞ q t ∧ (∀ s, q s 3=1) ∧
      (∀ᶠ s in 𝓝 t, (normalizedJacobian s).map Complex.ofReal *ᵥ q s = eig s • q s) := by
  obtain ⟨ψ,hψ0,hψsmooth,hψroot,hψd⟩ := eigenvalue_branch_exists ht hz
  let eig : ℝ → ℂ := fun s => ψ (s : ℂ)
  have he : ContDiffAt ℝ ∞ eig t :=
    (hψsmooth.restrict_scalars ℝ).comp t Complex.ofRealCLM.contDiff.contDiffAt
  have h1 : eig t+1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [eig,hψ0] at hr
  have h2 : 25*eig t+2 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [eig,hψ0] at hr
  refine ⟨eig,fun s => eigenvectorFormula s (eig s),_,hψ0,he,
    hψd.comp_ofReal,implicit_root_velocity_pos ht hz,
    eigenvectorFormula_contDiffAt he (ne_of_gt ht) h1 h2,
    (fun s => eigenvectorFormula_fourth s (eig s)),?_⟩
  have hn1 : ∀ᶠ s in 𝓝 t, eig s+1 ≠ 0 :=
    (he.continuousAt.add continuousAt_const).eventually_ne h1
  have hn2 : ∀ᶠ s in 𝓝 t, 25*eig s+2 ≠ 0 :=
    ((continuousAt_const.mul he.continuousAt).add continuousAt_const).eventually_ne h2
  have hn0 : ∀ᶠ s : ℝ in 𝓝 t, s ≠ 0 := continuousAt_id.eventually_ne (ne_of_gt ht)
  have hr := Complex.continuous_ofReal.continuousAt.tendsto.eventually hψroot
  filter_upwards [hn0,hn1,hn2,hr] with s hs h1s h2s hrs
  apply eigenvectorFormula_eigen hs (eig s) h1s h2s
  simpa only [universalQuartic_real] using hrs

end OscillatoryCores
