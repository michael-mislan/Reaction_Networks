import proofs.SerialTransferSelection.BatchSource
import proofs.ResourceLimitedCompetition.DeadlineValue

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

theorem phase_ancestral_generator_binding (γ : ℝ) (hγ : 0 ≤ γ) (Ω N W0 : ℕ)
    (zL zH : ℝ) (D : Finset PopulationState) (f : ℕ → ℕ → ℝ) (s : ActiveState D) :
    (phaseStoppedModel γ hγ Ω N W0 zL zH D).generator (ancestralObservable N f) (.inl s)=
      resourceCoefficient γ s.val.resource Ω*
        (ancestralZ true s.val.live*
          (f (ancestralMembrane true s.val.live+1) (ancestralMembrane false s.val.live)-
            f (ancestralMembrane true s.val.live) (ancestralMembrane false s.val.live))+
        ancestralZ false s.val.live*
          (f (ancestralMembrane true s.val.live) (ancestralMembrane false s.val.live+1)-
            f (ancestralMembrane true s.val.live) (ancestralMembrane false s.val.live))) := by
  classical
  have hnext (e : CellEvent s.val) :
      physicalState N (phaseStoppedNext N W0 zL zH D (.inl s) ⟨s,e⟩)=eventOutcome N ⟨s,e⟩ :=
    phase_physical_next_chosen N W0 zL zH D ⟨s,e⟩
  rw [phase_active_generator,Fintype.sum_sigma]
  simp only [ancestralObservable]
  simp only [hnext]
  simp only [event_ancestral_membrane,physicalState]
  simp_rw [Fintype.sum_sum_type]
  simp only [eventRate,add_zero,sub_self,mul_zero,Finset.sum_const_zero,zero_add]
  have hdraw (i : Fin s.val.live.length) := daughter_constant_sum
    (nextCompartment (selectedCell s.val i).compartment (.inr ())).1
    (propensity (resourceCoefficient γ s.val.resource Ω) (selectedCell s.val i).compartment (.inr ()))
    (f (ancestralMembrane true s.val.live+(if (selectedCell s.val i).high=true then 1 else 0))
      (ancestralMembrane false s.val.live+(if (selectedCell s.val i).high=false then 1 else 0))-
      f (ancestralMembrane true s.val.live) (ancestralMembrane false s.val.live))
  simp_rw [hdraw]
  rw [ancestralZ_sum_selected,ancestralZ_sum_selected,Finset.sum_mul,Finset.sum_mul,
    ← Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases (selectedCell s.val i).high <;> simp [propensity] <;> ring

theorem phase_active_ancestral_generator_le (γ : ℝ) (hγ : 0 ≤ γ) (Ω N W0 : ℕ)
    (zL zH : ℝ) (D : Finset PopulationState) (f : ℕ → ℕ → ℝ)
    (hf : ∀ H L, 0 ≤ f H L) (s : ActiveState D) :
    (phaseStoppedModel γ hγ Ω N W0 zL zH D).generator (activeAncestralObservable N f) (.inl s) ≤
      (phaseStoppedModel γ hγ Ω N W0 zL zH D).generator (ancestralObservable N f) (.inl s) := by
  classical
  have hnext (e : CellEvent s.val) :
      activeAncestralObservable N f (phaseStoppedNext N W0 zL zH D (.inl s) ⟨s,e⟩) ≤
        ancestralObservable N f (phaseStoppedNext N W0 zL zH D (.inl s) ⟨s,e⟩) := by
    generalize phaseStoppedNext N W0 zL zH D (.inl s) ⟨s,e⟩=x
    cases x with
    | inl t => exact le_rfl
    | inr e => exact hf _ _
  have h := phase_active_generator_le γ hγ Ω N W0 zL zH D (activeAncestralObservable N f) s
    (fun e => ancestralObservable N f (phaseStoppedNext N W0 zL zH D (.inl s) ⟨s,e⟩)) hnext
  exact h.trans_eq (phase_active_generator γ hγ Ω N W0 zL zH D (ancestralObservable N f) s).symm

end SerialTransferSelection
