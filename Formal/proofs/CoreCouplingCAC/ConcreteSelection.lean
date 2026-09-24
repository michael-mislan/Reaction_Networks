import proofs.CoreCouplingCAC.GenericSelection
import proofs.CoreCouplingCAC.InitialSets

namespace CoreCouplingCAC

/-- A quantitative forward selection statement on a nonzero-radius cube.
The ODE is the invertible linear transform of the literal source ODE. -/
def Selected (L R : Fin 4 → ℝ) (c : State) : Prop :=
  ∀ x₀, Near c x₀ → ∃ X : ℝ → State, X 0 = x₀ ∧ ∀ t, 0 ≤ t →
    HasDerivAt (fun s => transform (X s)) (dynamics witnessRates (transform (X t))) t ∧
    (X t).Positive ∧
    energy L R (transform c) (transform (X t)) ≤
      energy L R (transform c) (transform x₀)*Real.exp (-(1/100:ℝ)*t) ∧
    (1/10000:ℝ) ≤ (coreZH witnessRates (X t)).1 ∧
    (1/10000:ℝ) ≤ (coreZH witnessRates (X t)).2

theorem low_selected (c : State) (hc : InBox c lowRootLower lowRootUpper)
    (hs : Stationary witnessRates c) : Selected lowLeft lowRight c := by
  have hce : InBox c lowLower lowUpper := low_energy_inBox c c hc (by simp [energy])
  intro x₀ hx₀
  obtain ⟨X,hX₀,hX⟩ := source_local_selection witnessRates lowLeft lowRight
    c lowLower lowUpper (fun x => low_energy_inBox x c hc) low_box_norm low_box_positive
    (fun x hx => low_nonlinear_energy x c hx hce hs) low_CAC_box
    x₀ (low_near_energy c x₀ hx₀)
  refine ⟨X,hX₀,?_⟩
  intro t ht
  obtain ⟨hd,hp,_,he,ha,hb⟩ := hX t ht
  exact ⟨hd,hp,he,ha,hb⟩

theorem high_selected (c : State) (hc : InBox c highRootLower highRootUpper)
    (hs : Stationary witnessRates c) : Selected highLeft highRight c := by
  have hce : InBox c highLower highUpper := high_energy_inBox c c hc (by simp [energy])
  intro x₀ hx₀
  obtain ⟨X,hX₀,hX⟩ := source_local_selection witnessRates highLeft highRight
    c highLower highUpper (fun x => high_energy_inBox x c hc) high_box_norm high_box_positive
    (fun x hx => high_nonlinear_energy x c hx hce hs) high_CAC_box
    x₀ (high_near_energy c x₀ hx₀)
  refine ⟨X,hX₀,?_⟩
  intro t ht
  obtain ⟨hd,hp,_,he,ha,hb⟩ := hX t ht
  exact ⟨hd,hp,he,ha,hb⟩

/-- Two distinct strictly positive equilibria each attract a specified
positive-radius set and sustain both actual zH production margins. -/
theorem two_selected_active_equilibria :
    ∃ c₁ c₂ : State, c₁.Positive ∧ c₂.Positive ∧
      Stationary witnessRates c₁ ∧ Stationary witnessRates c₂ ∧ c₁.z < c₂.z ∧
      Selected lowLeft lowRight c₁ ∧ Selected highLeft highRight c₂ := by
  obtain ⟨⟨z₁,hz₁,he₁⟩,⟨z₂,hz₂,he₂⟩⟩ := narrow_outer_roots
  have hp₁ : 0 < z₁ := by linarith [hz₁.1]
  have hp₂ : 0 < z₂ := by linarith [hz₂.1]
  have hs₁ := lift_stationary witnessRates z₁ (by positivity) (by norm_num [witnessRates]) he₁
  have hs₂ := lift_stationary witnessRates z₂ (by positivity) (by norm_num [witnessRates]) he₂
  refine ⟨lift witnessRates z₁,lift witnessRates z₂,
    witness_lift_positive z₁ hp₁ (by linarith [hz₁.2]),
    witness_lift_positive z₂ hp₂ (by linarith [hz₂.2]),hs₁,hs₂,?_,?_,?_⟩
  · change z₁ < z₂
    linarith [hz₁.2,hz₂.1]
  · exact low_selected _ (low_root_enclosure z₁ (by convert hz₁ using 1; norm_num)) hs₁
  · exact high_selected _ (high_root_enclosure z₂ (by convert hz₂ using 1; norm_num)) hs₂

end CoreCouplingCAC
