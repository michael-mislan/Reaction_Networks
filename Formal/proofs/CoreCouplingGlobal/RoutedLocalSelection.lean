import proofs.CoreCouplingGlobal.RoutedLocalDynamics

open Filter Topology
namespace CoreCouplingGlobal
open CoreCouplingCAC

theorem routed_transformed_derivative_source (e g : ℝ) (X : ℝ → State) (t : ℝ)
    (hd : HasDerivAt (fun s => transform (X s)) (routedDynamics e g (transform (X t))) t) :
    HasDerivAt (fun s => coordinates (X s)) (routedDerivative (flagshipRates e) g (X t)) t := by
  have h := hasDerivAt_pi.1 hd
  rw [routed_dynamics_source] at h
  have hA := (h 0).add (h 1)
  have hB := (h 1).neg
  have hz := h 2
  have hH := h 3
  simp [transform] at hA hB hz hH
  rw [routed_literal_ODE]
  apply hasDerivAt_pi.2
  intro i
  fin_cases i
  · convert hA using 1
    funext s
    simp [coordinates]
  · convert hB using 1
    funext s
    simp [coordinates]
  · simpa [coordinates] using hz
  · simpa [coordinates] using hH

theorem routed_source_derivative_transformed (e g : ℝ) (X : ℝ → State) (t : ℝ)
    (hd : HasDerivAt (fun s => coordinates (X s)) (routedDerivative (flagshipRates e) g (X t)) t) :
    HasDerivAt (fun s => transform (X s)) (routedDynamics e g (transform (X t))) t := by
  have h := hasDerivAt_pi.1 hd
  rw [routed_literal_ODE] at h
  rw [routed_dynamics_source]
  apply hasDerivAt_pi.2
  intro i
  fin_cases i
  · simpa [transform,coordinates] using (h 0).add (h 1)
  · simpa [transform,coordinates] using (h 1).neg
  · simpa [transform,coordinates] using h 2
  · simpa [transform,coordinates] using h 3

/-- The decay assertion holds for every actual solution, not just the constructed one. -/
theorem routed_all_local_solutions_converge (e g : ℝ) (L R : Fin 4 → ℝ) (c lo hi : State)
    (hw : ∀ i, (1/4:ℝ) ≤ L i/R i)
    (hsub : ∀ x, energy L R (transform c) (transform x) ≤ (1/1000000000000:ℝ) → InBox x lo hi)
    (hdecay : ∀ x, InBox x lo hi →
      routedEnergyRate e g L R (transform c) (transform x) ≤
        -(1/100:ℝ)*energy L R (transform c) (transform x))
    (X : ℝ → State)
    (hX : ∀ t, 0 ≤ t → HasDerivAt (fun s => coordinates (X s))
      (routedDerivative (flagshipRates e) g (X t)) t)
    (h0 : energy L R (transform c) (transform (X 0)) ≤ (1/1000000000000:ℝ)) :
    (∀ t, 0 ≤ t → energy L R (transform c) (transform (X t)) ≤
      energy L R (transform c) (transform (X 0))*Real.exp (-(1/100:ℝ)*t)) ∧
    Tendsto (fun t => coordinates (X t)) atTop (𝓝 (coordinates c)) := by
  let F : ℝ → ℝ := fun t => energy L R (transform c) (transform (X t))
  let F' : ℝ → ℝ := fun t => routedEnergyRate e g L R (transform c) (transform (X t))
  have hd : ∀ t, 0 ≤ t → HasDerivAt F (F' t) t := by
    intro t ht
    exact energy_hasDerivAt L R (transform c) (fun s => transform (X s)) _ t
      (routed_source_derivative_transformed e g X t (hX t ht))
  have hb : ∀ t, 0 ≤ t → F t ≤ F 0*Real.exp (-(1/100:ℝ)*t) := by
    intro t ht
    exact (local_energy_barrier F F' t (1/1000000000000) (1/100)
      (by norm_num) (by norm_num)
      (fun s hs => (hd s hs.1).continuousAt.continuousWithinAt)
      (fun s hs => (hd s hs.1).hasDerivWithinAt) h0
      (fun s _ hs => hdecay (X s) (hsub (X s) hs)) t ⟨ht,le_rfl⟩).2
  exact ⟨hb,transformed_convergence_source X c
    (energy_decay_converges L R (transform c) (fun t => transform (X t)) _ hw hb)⟩

theorem routed_local_selection (e g : ℝ) (L R : Fin 4 → ℝ) (c lo hi : State)
    (hw : ∀ i, (1/4:ℝ) ≤ L i/R i)
    (hsub : ∀ x, energy L R (transform c) (transform x) ≤ (1/1000000000000:ℝ) → InBox x lo hi)
    (hnorm : ∀ x, InBox x lo hi → ‖transform x‖ ≤ 100)
    (hpos : ∀ x, InBox x lo hi → x.Positive)
    (hdecay : ∀ x, InBox x lo hi →
      routedEnergyRate e g L R (transform c) (transform x) ≤
        -(1/100:ℝ)*energy L R (transform c) (transform x))
    (x₀ : State) (h₀ : energy L R (transform c) (transform x₀) ≤ (1/1000000000000:ℝ)) :
    ∃ X : ℝ → State, X 0 = x₀ ∧
      (∀ t, 0 ≤ t →
        HasDerivAt (fun s => coordinates (X s)) (routedDerivative (flagshipRates e) g (X t)) t ∧
        (X t).Positive ∧ InBox (X t) lo hi ∧
        energy L R (transform c) (transform (X t)) ≤
          energy L R (transform c) (transform x₀)*Real.exp (-(1/100:ℝ)*t)) ∧
      Tendsto (fun t => coordinates (X t)) atTop (𝓝 (coordinates c)) := by
  obtain ⟨f,hf,hglobal⟩ := routed_global_extension e g
  obtain ⟨γ,hγ₀,hγ⟩ := hglobal (transform x₀)
  let X : ℝ → State := fun t => untransform (γ t)
  have hTX : ∀ t, transform (X t) = γ t := fun t => transform_untransform (γ t)
  let F : ℝ → ℝ := fun t => energy L R (transform c) (γ t)
  let F' : ℝ → ℝ := fun t => energyVelocity L R (transform c) (γ t) (f (γ t))
  have hFd : ∀ t, HasDerivAt F (F' t) t :=
    fun t => energy_hasDerivAt L R (transform c) γ (f (γ t)) t (hγ t)
  have hX₀ : X 0 = x₀ := by
    dsimp [X]
    rw [hγ₀,untransform_transform]
  have hall : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => transform (X s)) (routedDynamics e g (transform (X t))) t ∧
      (X t).Positive ∧ InBox (X t) lo hi ∧
      energy L R (transform c) (transform (X t)) ≤
        energy L R (transform c) (transform x₀)*Real.exp (-(1/100:ℝ)*t) := by
    intro t ht
    have hbound : ∀ s ∈ Set.Ico 0 t, F s ≤ (1/1000000000000:ℝ) → F' s ≤ -(1/100:ℝ)*F s := by
      intro s hs he
      have hbox : InBox (X s) lo hi := hsub (X s) (by simpa only [hTX] using he)
      have hnorm' : ‖γ s‖ ≤ 100 := by simpa only [hTX] using hnorm (X s) hbox
      have hfield := hf (γ s) hnorm'
      have hdec := hdecay (X s) hbox
      dsimp [F',F]
      rw [hfield]
      simpa only [hTX,routedEnergyRate,energyVelocity] using hdec
    have hb := local_energy_barrier F F' t (1/1000000000000) (1/100)
      (by norm_num) (by norm_num)
      (fun s _ => (hFd s).continuousAt.continuousWithinAt)
      (fun s _ => (hFd s).hasDerivWithinAt)
      (by simpa only [F,hγ₀] using h₀) hbound t ⟨ht,le_rfl⟩
    have hbox : InBox (X t) lo hi := hsub (X t) (by simpa only [hTX] using hb.1)
    have hnorm' : ‖γ t‖ ≤ 100 := by simpa only [hTX] using hnorm (X t) hbox
    have hfield := hf (γ t) hnorm'
    have hd : HasDerivAt γ (routedDynamics e g (γ t)) t := by rw [← hfield]; exact hγ t
    refine ⟨?_,hpos (X t) hbox,hbox,?_⟩
    · simpa only [hTX] using hd
    · simpa only [F,hγ₀,hTX] using hb.2
  refine ⟨X,hX₀,?_,?_⟩
  · intro t ht
    exact ⟨routed_transformed_derivative_source e g X t (hall t ht).1,(hall t ht).2⟩
  · exact transformed_convergence_source X c
      (energy_decay_converges L R (transform c) (fun t => transform (X t)) _ hw
        (fun t ht => (hall t ht).2.2.2))

end CoreCouplingGlobal
