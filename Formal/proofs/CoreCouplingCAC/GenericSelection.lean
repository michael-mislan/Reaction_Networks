import proofs.CoreCouplingCAC.Cutoff
import proofs.CoreCouplingCAC.EnergyCoordinates
import proofs.CoreCouplingCAC.EnergyBarrier
import proofs.CoreCouplingCAC.LocalBounds

namespace CoreCouplingCAC

theorem transform_untransform (x : Fin 4 → ℝ) : transform (untransform x) = x := by
  funext i
  fin_cases i <;> simp [transform,untransform]

/-- A globally existing trajectory of the *original* source is selected by
an explicitly certified energy sublevel. All hypotheses below are algebraic
box estimates, instantiated for the two concrete branches in the final file.
-/
theorem source_local_selection (p : Rates) (L R : Fin 4 → ℝ) (c lo hi : State)
    (hsub : ∀ x, energy L R (transform c) (transform x) ≤ (1/1000000000000:ℝ) → InBox x lo hi)
    (hnorm : ∀ x, InBox x lo hi → ‖transform x‖ ≤ 100)
    (hpos : ∀ x, InBox x lo hi → x.Positive)
    (hdecay : ∀ x, InBox x lo hi →
      energyRate p L R (transform c) (transform x) ≤ -(1/100:ℝ)*energy L R (transform c) (transform x))
    (hact : ∀ x, InBox x lo hi →
      (1/10000:ℝ) ≤ (coreZH p x).1 ∧ (1/10000:ℝ) ≤ (coreZH p x).2)
    (x₀ : State) (h₀ : energy L R (transform c) (transform x₀) ≤ (1/1000000000000:ℝ)) :
    ∃ X : ℝ → State, X 0 = x₀ ∧ ∀ t, 0 ≤ t →
      HasDerivAt (fun s => transform (X s)) (dynamics p (transform (X t))) t ∧
      (X t).Positive ∧ InBox (X t) lo hi ∧
      energy L R (transform c) (transform (X t)) ≤
        energy L R (transform c) (transform x₀)*Real.exp (-(1/100:ℝ)*t) ∧
      (1/10000:ℝ) ≤ (coreZH p (X t)).1 ∧ (1/10000:ℝ) ≤ (coreZH p (X t)).2 := by
  obtain ⟨f,hf,hglobal⟩ := exists_global_extension p
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
  refine ⟨X,hX₀,?_⟩
  intro t ht
  have hbound : ∀ s ∈ Set.Ico 0 t, F s ≤ (1/1000000000000:ℝ) → F' s ≤ -(1/100:ℝ)*F s := by
    intro s hs he
    have hbox : InBox (X s) lo hi := hsub (X s) (by simpa only [hTX] using he)
    have hnorm' : ‖γ s‖ ≤ 100 := by simpa only [hTX] using hnorm (X s) hbox
    have hfield := hf (γ s) hnorm'
    have hdec := hdecay (X s) hbox
    dsimp [F',F]
    rw [hfield]
    simpa only [hTX,energyRate,energyVelocity] using hdec
  have hb := local_energy_barrier F F' t (1/1000000000000) (1/100)
    (by norm_num) (by norm_num)
    (fun s _ => (hFd s).continuousAt.continuousWithinAt)
    (fun s _ => (hFd s).hasDerivWithinAt)
    (by simpa only [F,hγ₀] using h₀) hbound t ⟨ht,le_rfl⟩
  have hbox : InBox (X t) lo hi := hsub (X t) (by simpa only [hTX] using hb.1)
  have hnorm' : ‖γ t‖ ≤ 100 := by simpa only [hTX] using hnorm (X t) hbox
  have hfield := hf (γ t) hnorm'
  have hd : HasDerivAt γ (dynamics p (γ t)) t := by rw [← hfield]; exact hγ t
  refine ⟨?_,hpos (X t) hbox,hbox,?_,(hact (X t) hbox).1,(hact (X t) hbox).2⟩
  · simpa only [hTX] using hd
  · simpa only [F,hγ₀,hTX] using hb.2

end CoreCouplingCAC
