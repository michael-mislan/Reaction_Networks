import proofs.ResourceLimitedCompetition.AncestralRates

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy

theorem event_valid_volumes (N : ℕ) (hN : 0 < N) (D : Finset PopulationState)
    (s : ActiveState D) (e : CellEvent s.val) (hv : ValidVolumes N s.val) :
    ValidVolumes N (eventOutcome N ⟨s,e⟩) := by
  classical
  rcases e with ⟨i,ch⟩
  have hleft := fun c (hc : c ∈ s.val.live.take i.val) => hv c (List.mem_of_mem_take hc)
  have hright := fun c (hc : c ∈ s.val.live.drop (i.val+1)) => hv c (List.mem_of_mem_drop hc)
  have hc := hv _ (selected_mem s.val i)
  cases ch with
  | inl r =>
    simpa only [ValidVolumes,eventOutcome,residentAt,List.forall_mem_append,List.forall_mem_cons,nextCompartment]
      using And.intro hleft (And.intro hc hright)
  | inr d =>
    by_cases hm : (nextCompartment (selectedCell s.val i).compartment (.inr ())).2=2*N
    · have hnew : N ≤ N ∧ N < 2*N := by omega
      simpa only [ValidVolumes,eventOutcome,growthAt,hm,if_true,List.forall_mem_append,List.forall_mem_cons]
        using And.intro hleft (And.intro hnew (And.intro hnew hright))
    · have hnew : N ≤ (nextCompartment (selectedCell s.val i).compartment (.inr ())).2 ∧
          (nextCompartment (selectedCell s.val i).compartment (.inr ())).2 < 2*N := by
        simp only [nextCompartment] at hm ⊢
        omega
      simpa only [ValidVolumes,eventOutcome,growthAt,hm,if_false,List.forall_mem_append,List.forall_mem_cons]
        using And.intro hleft (And.intro hnew hright)

theorem nutrient_event_resource (N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (s : ActiveState D) (e : CellEvent s.val) (hn : eventReason N M zL zH ⟨s,e⟩=.nutrient) :
    s.val.resource-1=N*M ∧ (eventOutcome N ⟨s,e⟩).resource=N*M ∧
      membrane (eventOutcome N ⟨s,e⟩).live=membrane s.val.live+1 := by
  classical
  rcases e with ⟨i,ch⟩
  cases ch with
  | inl r =>
    simp only [eventReason] at hn
    split_ifs at hn
  | inr d =>
    have hQ : s.val.resource-1=N*M := by
      simp only [eventReason] at hn
      split_ifs at hn <;> simp_all
    have hmem := growth_membrane N s.val.resource s.val.divisions (s.val.live.take i.val)
      (selectedCell s.val i) (s.val.live.drop (i.val+1)) d.val
    rw [sourceAt_selected] at hmem
    refine ⟨hQ,?_,hmem⟩
    simp only [eventOutcome,growthAt]
    split_ifs <;> exact hQ

theorem nutrient_endpoint_membrane (N M : ℕ) (zL zH : ℝ)
    (s : ActiveState (activeDomain N M zL zH)) (e : CellEvent s.val)
    (hn : eventReason N M zL zH ⟨s,e⟩=.nutrient) :
    membrane (eventOutcome N ⟨s,e⟩).live=4*(N*M) := by
  have hs := activeDomain_safe N M zL zH s.val s.property
  have h := nutrient_event_resource N M zL zH _ s e hn
  have hq := hs.1
  have hres := hs.2.2.1
  omega

theorem nutrient_division_births (N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (s : ActiveState D) (i : Fin s.val.live.length)
    (d : {d : Counts // d ∈ daughterDraws
      (nextCompartment (selectedCell s.val i).compartment (.inr ())).1})
    (hn : eventReason N M zL zH ⟨s,i,.inr d⟩=.nutrient)
    (hm : (nextCompartment (selectedCell s.val i).compartment (.inr ())).2=2*N) :
    cellEnergy zL zH ⟨(selectedCell s.val i).high,(d.val,N)⟩ < 4*innerEnergy ∧
      cellEnergy zL zH ⟨(selectedCell s.val i).high,
        ((fun j => (nextCompartment (selectedCell s.val i).compartment (.inr ())).1 j-d.val j),N)⟩ < 4*innerEnergy := by
  classical
  simp only [eventReason] at hn
  split_ifs at hn
  simp_all

theorem nutrient_event_energy (N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (s : ActiveState D) (e : CellEvent s.val)
    (hs : ∀ c ∈ s.val.live, cellEnergy zL zH c < outerEnergy)
    (hn : eventReason N M zL zH ⟨s,e⟩=.nutrient) :
    ∀ c ∈ (eventOutcome N ⟨s,e⟩).live, cellEnergy zL zH c < outerEnergy := by
  classical
  rcases e with ⟨i,ch⟩
  have hleft := fun c (hc : c ∈ s.val.live.take i.val) => hs c (List.mem_of_mem_take hc)
  have hright := fun c (hc : c ∈ s.val.live.drop (i.val+1)) => hs c (List.mem_of_mem_drop hc)
  cases ch with
  | inl r =>
    simp only [eventReason] at hn
    split_ifs at hn
  | inr d =>
    have hp : cellEnergy zL zH ⟨(selectedCell s.val i).high,
        nextCompartment (selectedCell s.val i).compartment (.inr ())⟩ < outerEnergy := by
      by_contra hh
      simp [eventReason,le_of_not_gt hh] at hn
    by_cases hm : (nextCompartment (selectedCell s.val i).compartment (.inr ())).2=2*N
    · have hg := nutrient_division_births N M zL zH D s i d hn hm
      have hsmall : 4*innerEnergy < outerEnergy := by norm_num [innerEnergy,outerEnergy]
      simpa only [eventOutcome,growthAt,hm,if_true,List.forall_mem_append,List.forall_mem_cons]
        using And.intro hleft (And.intro (hg.1.trans hsmall) (And.intro (hg.2.trans hsmall) hright))
    · simpa only [eventOutcome,growthAt,hm,if_false,List.forall_mem_append,List.forall_mem_cons]
        using And.intro hleft (And.intro hp hright)

end ResourceLimitedCompetition
