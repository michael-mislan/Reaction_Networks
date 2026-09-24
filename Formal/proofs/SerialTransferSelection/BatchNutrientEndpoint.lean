import proofs.SerialTransferSelection.BatchSupport
import proofs.ResourceLimitedCompetition.NutrientEndpoint

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

theorem phase_nutrient_event_resource (N W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (s : ActiveState D) (e : CellEvent s.val) (hn : phaseEventReason N W0 zL zH ⟨s,e⟩=.nutrient) :
    s.val.resource-1=W0 ∧ (eventOutcome N ⟨s,e⟩).resource=W0 ∧
      membrane (eventOutcome N ⟨s,e⟩).live=membrane s.val.live+1 := by
  classical
  rcases e with ⟨i,ch⟩
  cases ch with
  | inl r =>
    simp only [phaseEventReason] at hn
    split_ifs at hn
  | inr d =>
    have hQ : s.val.resource-1=W0 := by
      simp only [phaseEventReason] at hn
      split_ifs at hn <;> simp_all
    have hmem := growth_membrane N s.val.resource s.val.divisions (s.val.live.take i.val)
      (selectedCell s.val i) (s.val.live.drop (i.val+1)) d.val
    rw [sourceAt_selected] at hmem
    refine ⟨hQ,?_,hmem⟩
    simp only [eventOutcome,growthAt]
    split_ifs <;> exact hQ

theorem phase_nutrient_endpoint_membrane (N M W0 : ℕ) (zL zH : ℝ)
    (s : ActiveState (phaseActiveDomain N M W0 zL zH)) (e : CellEvent s.val)
    (hn : phaseEventReason N W0 zL zH ⟨s,e⟩=.nutrient) :
    membrane (eventOutcome N ⟨s,e⟩).live=4*(W0) := by
  have hs := phaseActiveDomain_safe N M W0 zL zH s.val s.property
  have h := phase_nutrient_event_resource N W0 zL zH _ s e hn
  have hq := hs.1
  have hres := hs.2.2.1
  omega

theorem phase_nutrient_division_births (N W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (s : ActiveState D) (i : Fin s.val.live.length)
    (d : {d : Counts // d ∈ daughterDraws
      (nextCompartment (selectedCell s.val i).compartment (.inr ())).1})
    (hn : phaseEventReason N W0 zL zH ⟨s,i,.inr d⟩=.nutrient)
    (hm : (nextCompartment (selectedCell s.val i).compartment (.inr ())).2=2*N) :
    cellEnergy zL zH ⟨(selectedCell s.val i).high,(d.val,N)⟩ < 4*innerEnergy ∧
      cellEnergy zL zH ⟨(selectedCell s.val i).high,
        ((fun j => (nextCompartment (selectedCell s.val i).compartment (.inr ())).1 j-d.val j),N)⟩ < 4*innerEnergy := by
  classical
  simp only [phaseEventReason] at hn
  split_ifs at hn
  simp_all

theorem phase_nutrient_event_energy (N W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (s : ActiveState D) (e : CellEvent s.val)
    (hs : ∀ c ∈ s.val.live, cellEnergy zL zH c < (8*innerEnergy))
    (hn : phaseEventReason N W0 zL zH ⟨s,e⟩=.nutrient) :
    ∀ c ∈ (eventOutcome N ⟨s,e⟩).live, cellEnergy zL zH c < (8*innerEnergy) := by
  classical
  rcases e with ⟨i,ch⟩
  have hleft := fun c (hc : c ∈ s.val.live.take i.val) => hs c (List.mem_of_mem_take hc)
  have hright := fun c (hc : c ∈ s.val.live.drop (i.val+1)) => hs c (List.mem_of_mem_drop hc)
  cases ch with
  | inl r =>
    simp only [phaseEventReason] at hn
    split_ifs at hn
  | inr d =>
    have hp : cellEnergy zL zH ⟨(selectedCell s.val i).high,
        nextCompartment (selectedCell s.val i).compartment (.inr ())⟩ < (8*innerEnergy) := by
      by_contra hh
      simp [phaseEventReason,le_of_not_gt hh] at hn
    by_cases hm : (nextCompartment (selectedCell s.val i).compartment (.inr ())).2=2*N
    · have hg := phase_nutrient_division_births N W0 zL zH D s i d hn hm
      have hsmall : 4*innerEnergy < (8*innerEnergy) := by norm_num [innerEnergy,outerEnergy]
      simpa only [eventOutcome,growthAt,hm,if_true,List.forall_mem_append,List.forall_mem_cons]
        using And.intro hleft (And.intro (hg.1.trans hsmall) (And.intro (hg.2.trans hsmall) hright))
    · simpa only [eventOutcome,growthAt,hm,if_false,List.forall_mem_append,List.forall_mem_cons]
        using And.intro hleft (And.intro hp hright)

end SerialTransferSelection
