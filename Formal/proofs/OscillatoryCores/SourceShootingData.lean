import proofs.OscillatoryCores.ShootingInverse
import proofs.OscillatoryCores.MovingBranch

namespace OscillatoryCores

open Filter
open scoped ContDiff Topology Matrix

/-- All spectral data for the shooting inverse are produced for the literal
source. Identifying this map with the nonlinear shooting derivative remains
a separate analytic obligation. -/
theorem source_shooting_data :
    ∃ t w T l m : ℝ, ∃ eig : ℝ → ℂ, ∃ q : ℝ → (Fin 4 → ℂ), ∃ d : ℂ,
    ∃ e f : State,
      0 < t ∧ 0 < w ∧ T=2*Real.pi/w ∧ 0 < T ∧
      crossingPolynomial t=0 ∧ eig t=Complex.I*(w : ℂ) ∧
      ContDiffAt ℝ ∞ eig t ∧ HasDerivAt eig d t ∧ 0 < d.re ∧
      ContDiffAt ℝ ∞ q t ∧ (∀ s, q s 3=1) ∧
      (∀ᶠ s in 𝓝 t, (normalizedJacobian s).map Complex.ofReal *ᵥ q s=eig s • q s) ∧
      l < m ∧ m < 0 ∧ e ≠ 0 ∧ f ≠ 0 ∧
      normalizedLinear t e=l • e ∧ normalizedLinear t f=m • f ∧
      (shootingLinear T w d.re d.im l m (fun i => (q t i).re)
        (fun i => (q t i).im) e f).IsInvertible := by
  obtain ⟨t,htlo,hthi,hz⟩ := crossing_exists
  have ht : 0 < t := by linarith
  let w := spectralFrequency t
  have hw : 0 < w := spectralFrequency_pos ht
  let T := 2*Real.pi/w
  have hT : 0 < T := by dsimp [T]; positivity
  obtain ⟨l,m,hlm,hm,hlroot,hmroot⟩ := distinct_stable_roots htlo hthi
  obtain ⟨e,he,hLe⟩ := stable_real_eigenvector ht hz hlroot
  obtain ⟨f,hf,hLf⟩ := stable_real_eigenvector ht hz hmroot
  obtain ⟨eig,q,d,heig,hes,hed,hdr,hqs,hq3,hqe⟩ := moving_eigenvector_branch ht hz
  have hmode := complex_eigenvector_real_modes t (eig t) (q t) hqe.self_of_nhds
  have hLu : normalizedLinear t (fun i => (q t i).re) = -w • (fun i => (q t i).im) := by
    simpa [heig,w] using hmode.1
  have hLv : normalizedLinear t (fun i => (q t i).im) = w • (fun i => (q t i).re) := by
    simpa [heig,w] using hmode.2
  have hu : (fun i => (q t i).re) ≠ (0 : State) := by
    intro h
    have h3 := congrFun h 3
    simp [hq3 t] at h3
  exact ⟨t,w,T,l,m,eig,q,d,e,f,ht,hw,rfl,hT,hz,heig,hes,hed,hdr,hqs,hq3,hqe,
    hlm,hm,he,hf,hLe,hLf,shootingLinear_invertible (normalizedLinear t) hT (ne_of_gt hw)
      (ne_of_gt hdr) (ne_of_lt hlm) (lt_trans hlm hm) hm hu he hf hLu hLv hLe hLf⟩

end OscillatoryCores
