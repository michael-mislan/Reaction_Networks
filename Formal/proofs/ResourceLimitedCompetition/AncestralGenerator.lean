import proofs.ResourceLimitedCompetition.AncestralRates

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy

theorem sum_selected_cells (F : TaggedCell → ℝ) (s : PopulationState) :
    (∑ i : Fin s.live.length, F (selectedCell s i))=(s.live.map F).sum := by
  simpa only [selectedCell,List.ofFn_getElem_eq_map] using
    (List.sum_ofFn (f := fun i : Fin s.live.length => F s.live[i.val])).symm

theorem ancestralZ_sum_selected (tag : Bool) (s : PopulationState) :
    ancestralZ tag s.live=
      ∑ i : Fin s.live.length,
        if (selectedCell s i).high=tag then ((selectedCell s i).compartment.1 2 : ℝ) else 0 :=
  (sum_selected_cells _ _).symm

noncomputable def ancestralObservable (N : ℕ) {D : Finset PopulationState}
    (f : ℕ → ℕ → ℝ) (x : StoppedPopulation D) : ℝ :=
  f (ancestralMembrane true (physicalState N x).live) (ancestralMembrane false (physicalState N x).live)

theorem ancestral_generator_binding (γ : ℝ) (hγ : 0 ≤ γ) (Ω N M : ℕ)
    (zL zH : ℝ) (D : Finset PopulationState) (f : ℕ → ℕ → ℝ) (s : ActiveState D) :
    (stoppedPopulationModel γ hγ Ω N M zL zH D).generator (ancestralObservable N f) (.inl s)=
      resourceCoefficient γ s.val.resource Ω*
        (ancestralZ true s.val.live*
          (f (ancestralMembrane true s.val.live+1) (ancestralMembrane false s.val.live)-
            f (ancestralMembrane true s.val.live) (ancestralMembrane false s.val.live))+
        ancestralZ false s.val.live*
          (f (ancestralMembrane true s.val.live) (ancestralMembrane false s.val.live+1)-
            f (ancestralMembrane true s.val.live) (ancestralMembrane false s.val.live))) := by
  classical
  have hnext (e : CellEvent s.val) :
      physicalState N (stoppedNext N M zL zH D (.inl s) ⟨s,e⟩)=eventOutcome N ⟨s,e⟩ :=
    physical_next_chosen N M zL zH D ⟨s,e⟩
  rw [active_generator,Fintype.sum_sigma]
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

end ResourceLimitedCompetition
