import proofs.ProductiveMemory.ExtractionSupport
import proofs.ResourceLimitedCompetition.NutrientEndpoint

namespace ProductiveMemory
noncomputable section
set_option Elab.async false
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

theorem productive_legacy_nutrient_resource (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState)
    (s : ProductiveActive D) (e : CellEvent s.val.population) (hn : productiveReason N W0 J rho zL zH ⟨s,.inl e⟩=.nutrient) :
    s.val.population.resource-1=W0 ∧ (productiveOutcome N s.val (.inl e)).population.resource=W0 ∧
      membrane (productiveOutcome N s.val (.inl e)).population.live=membrane s.val.population.live+1 := by
  classical
  rcases e with ⟨i,ch⟩
  cases ch with
  | inl r =>
    simp only [productiveReason] at hn
    split_ifs at hn
  | inr d =>
    have hQ : s.val.population.resource-1=W0 := by
      simp only [productiveReason] at hn
      split_ifs at hn <;> simp_all
    have hmem := growth_membrane N s.val.population.resource s.val.population.divisions (s.val.population.live.take i.val)
      (selectedCell s.val.population i) (s.val.population.live.drop (i.val+1)) d.val
    rw [sourceAt_selected] at hmem
    refine ⟨hQ,?_,hmem⟩
    simp only [productiveOutcome,growthAt]
    split_ifs <;> exact hQ

theorem productive_nutrient_endpoint_membrane (N M W0 J : ℕ) (rho zL zH : ℝ)
    (s : ProductiveActive (productiveActiveDomain N M W0 J rho zL zH)) (e : CellEvent s.val.population)
    (hn : productiveReason N W0 J rho zL zH ⟨s,.inl e⟩=.nutrient) :
    membrane (productiveOutcome N s.val (.inl e)).population.live=4*(W0) := by
  have hs := productive_active_safe N M W0 J rho zL zH s.val s.property
  have h := productive_legacy_nutrient_resource N W0 J rho zL zH _ s e hn
  have hq := hs.1
  have hres := hs.2.2.1
  omega

theorem productive_nutrient_division_births (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState)
    (s : ProductiveActive D) (i : Fin s.val.population.live.length)
    (d : {d : Counts // d ∈ daughterDraws
      (nextCompartment (selectedCell s.val.population i).compartment (.inr ())).1})
    (hn : productiveReason N W0 J rho zL zH ⟨s,.inl ⟨i,.inr d⟩⟩=.nutrient)
    (hm : (nextCompartment (selectedCell s.val.population i).compartment (.inr ())).2=2*N) :
    extractionCellEnergy rho zL zH ⟨(selectedCell s.val.population i).high,(d.val,N)⟩ < 4*readyLevel ∧
      extractionCellEnergy rho zL zH ⟨(selectedCell s.val.population i).high,
        ((fun j => (nextCompartment (selectedCell s.val.population i).compartment (.inr ())).1 j-d.val j),N)⟩ < 4*readyLevel := by
  classical
  simp only [productiveReason] at hn
  split_ifs at hn
  simp_all

theorem productive_legacy_nutrient_energy (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState)
    (s : ProductiveActive D) (e : CellEvent s.val.population)
    (hs : ∀ c ∈ s.val.population.live, extractionCellEnergy rho zL zH c < (8*readyLevel))
    (hn : productiveReason N W0 J rho zL zH ⟨s,.inl e⟩=.nutrient) :
    ∀ c ∈ (productiveOutcome N s.val (.inl e)).population.live, extractionCellEnergy rho zL zH c < (8*readyLevel) := by
  classical
  rcases e with ⟨i,ch⟩
  have hleft := fun c (hc : c ∈ s.val.population.live.take i.val) => hs c (List.mem_of_mem_take hc)
  have hright := fun c (hc : c ∈ s.val.population.live.drop (i.val+1)) => hs c (List.mem_of_mem_drop hc)
  cases ch with
  | inl r =>
    simp only [productiveReason] at hn
    split_ifs at hn
  | inr d =>
    have hp : extractionCellEnergy rho zL zH ⟨(selectedCell s.val.population i).high,
        nextCompartment (selectedCell s.val.population i).compartment (.inr ())⟩ < (8*readyLevel) := by
      by_contra hh
      simp [productiveReason,le_of_not_gt hh] at hn
    by_cases hm : (nextCompartment (selectedCell s.val.population i).compartment (.inr ())).2=2*N
    · have hg := productive_nutrient_division_births N W0 J rho zL zH D s i d hn hm
      have hsmall : 4*readyLevel < (8*readyLevel) := by norm_num [readyLevel,outerLevel]
      simpa only [productiveOutcome,growthAt,hm,if_true,List.forall_mem_append,List.forall_mem_cons]
        using And.intro hleft (And.intro (hg.1.trans hsmall) (And.intro (hg.2.trans hsmall) hright))
    · simpa only [productiveOutcome,growthAt,hm,if_false,List.forall_mem_append,List.forall_mem_cons]
        using And.intro hleft (And.intro hp hright)

theorem productive_nutrient_resource (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState)
    (s : ProductiveActive D) (e : ProductiveEvent s.val) (hn : productiveReason N W0 J rho zL zH ⟨s,e⟩=.nutrient) :
    s.val.population.resource-1=W0 ∧ (productiveOutcome N s.val e).population.resource=W0 ∧
      membrane (productiveOutcome N s.val e).population.live=membrane s.val.population.live+1 := by
  classical
  cases e with
  | inl e => exact productive_legacy_nutrient_resource N W0 J rho zL zH D s e hn
  | inr i => simp only [productiveReason] at hn; split_ifs at hn

theorem productive_nutrient_energy (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState)
    (s : ProductiveActive D) (e : ProductiveEvent s.val)
    (hs : ∀ c ∈ s.val.population.live, extractionCellEnergy rho zL zH c < 8*readyLevel)
    (hn : productiveReason N W0 J rho zL zH ⟨s,e⟩=.nutrient) :
    ∀ c ∈ (productiveOutcome N s.val e).population.live, extractionCellEnergy rho zL zH c < 8*readyLevel := by
  classical
  cases e with
  | inl e => exact productive_legacy_nutrient_energy N W0 J rho zL zH D s e hs hn
  | inr i => simp only [productiveReason] at hn; split_ifs at hn

theorem productive_nutrient_membrane (N M W0 J : ℕ) (rho zL zH : ℝ)
    (s : ProductiveActive (productiveActiveDomain N M W0 J rho zL zH)) (e : ProductiveEvent s.val)
    (hn : productiveReason N W0 J rho zL zH ⟨s,e⟩=.nutrient) :
    membrane (productiveOutcome N s.val e).population.live=4*W0 := by
  have hs := productive_active_safe N M W0 J rho zL zH s.val s.property
  have h := productive_nutrient_resource N W0 J rho zL zH _ s e hn
  have hq := hs.1
  have hres := hs.2.2.1
  omega

theorem productive_event_valid_volumes (N : ℕ) (hN : 0 < N) (s : ProductiveState)
    (e : ProductiveEvent s) (hv : ValidVolumes N s.population) :
    ValidVolumes N (productiveOutcome N s e).population := by
  classical
  cases e with
  | inl e =>
    let a : ActiveState ({s.population} : Finset PopulationState) := ⟨s.population,Finset.mem_singleton_self _⟩
    have h := event_valid_volumes N hN _ a e hv
    convert h using 1
    rcases e with ⟨i,r | d⟩ <;> rfl
  | inr i =>
    have hleft := fun c (hc : c ∈ s.population.live.take i.val) => hv c (List.mem_of_mem_take hc)
    have hright := fun c (hc : c ∈ s.population.live.drop (i.val+1)) => hv c (List.mem_of_mem_drop hc)
    simpa only [ValidVolumes,productiveOutcome,extractionAt,List.forall_mem_append,List.forall_mem_cons]
      using And.intro hleft (And.intro (hv _ (selected_mem s.population i)) hright)

end
end ProductiveMemory
