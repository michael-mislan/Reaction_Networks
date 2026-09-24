import proofs.ResourceLimitedCompetition.SpatialPopulationBoundary

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy

theorem positive_resident_reactants (β : ℝ) (c : Compartment) (r : Fin 13)
    (h : 0 < propensity β c (.inl r)) : reactants c.1 r := by
  by_contra hn
  have hz := disabled_density_zero (1/100000) c.2 c.1 r hn
  simp only [propensity,hz,mul_zero,lt_self_iff_false] at h

theorem positive_event_step (γ : ℝ) (Ω N : ℕ) (D : Finset PopulationState)
    (s : ActiveState D) (e : CellEvent s.val) (hv : ValidVolumes N s.val)
    (hQ : 0 < s.val.resource) (hr : 0 < eventRate γ Ω ⟨s,e⟩) :
    PopulationStep N s.val (eventOutcome N ⟨s,e⟩) := by
  classical
  rcases e with ⟨i,ch⟩
  have hs := sourceAt_selected s.val i
  have hm := (hv _ (selected_mem s.val i)).2
  cases ch with
  | inl r =>
    have hreact := positive_resident_reactants (resourceCoefficient γ s.val.resource Ω)
      (selectedCell s.val i).compartment r hr
    have hstep := PopulationStep.resident (N := N) s.val.resource s.val.divisions
      (s.val.live.take i.val) (s.val.live.drop (i.val+1))
      (selectedCell s.val i).high (selectedCell s.val i).compartment r hreact
    change PopulationStep N (sourceAt _ _ _ _ _) _ at hstep
    rw [hs] at hstep
    exact hstep
  | inr d =>
    have hz : 0 < (selectedCell s.val i).compartment.1 2 := by
      by_contra hn
      have hzero : (selectedCell s.val i).compartment.1 2=0 := by omega
      simp [eventRate,propensity,hzero] at hr
    by_cases hdiv : (selectedCell s.val i).compartment.2+1=2*N
    · have hstep := PopulationStep.division s.val.resource s.val.divisions
        (s.val.live.take i.val) (s.val.live.drop (i.val+1))
        (selectedCell s.val i).high (selectedCell s.val i).compartment hQ hz hdiv d.val d.property
      change PopulationStep N (sourceAt _ _ _ _ _) _ at hstep
      rw [hs] at hstep
      simpa [eventOutcome,growthAt,nextCompartment,hdiv] using hstep
    · have hlt : (selectedCell s.val i).compartment.2+1 < 2*N := by omega
      have hstep := PopulationStep.growth s.val.resource s.val.divisions
        (s.val.live.take i.val) (s.val.live.drop (i.val+1))
        (selectedCell s.val i).high (selectedCell s.val i).compartment hQ hz hlt
      change PopulationStep N (sourceAt _ _ _ _ _) _ at hstep
      rw [hs] at hstep
      simpa [eventOutcome,growthAt,nextCompartment,hdiv] using hstep

theorem active_event_resource (N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (s : ActiveState D) (e : CellEvent s.val) (hQ : N*M < s.val.resource)
    (ha : eventReason N M zL zH ⟨s,e⟩=.active) :
    N*M < (eventOutcome N ⟨s,e⟩).resource ∧
      (eventOutcome N ⟨s,e⟩).resource ≤ s.val.resource := by
  classical
  rcases e with ⟨i,ch⟩
  cases ch with
  | inl r => exact ⟨hQ,le_rfl⟩
  | inr d =>
    have hneq : s.val.resource-1 ≠ N*M := by
      intro he
      simp only [eventReason] at ha
      split_ifs at ha
    simp only [eventOutcome,growthAt]
    split_ifs <;> dsimp only <;> omega

theorem active_event_energy (N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (s : ActiveState D) (e : CellEvent s.val)
    (hs : ∀ c ∈ s.val.live, cellEnergy zL zH c < outerEnergy)
    (ha : eventReason N M zL zH ⟨s,e⟩=.active) :
    ∀ c ∈ (eventOutcome N ⟨s,e⟩).live, cellEnergy zL zH c < outerEnergy := by
  classical
  rcases e with ⟨i,ch⟩
  have hleft : ∀ c ∈ s.val.live.take i.val, cellEnergy zL zH c < outerEnergy :=
    fun c hc => hs c (List.mem_of_mem_take hc)
  have hright : ∀ c ∈ s.val.live.drop (i.val+1), cellEnergy zL zH c < outerEnergy :=
    fun c hc => hs c (List.mem_of_mem_drop hc)
  cases ch with
  | inl r =>
    have hp : cellEnergy zL zH ⟨(selectedCell s.val i).high,
        nextCompartment (selectedCell s.val i).compartment (.inl r)⟩ < outerEnergy := by
      simp only [eventReason] at ha
      split_ifs at ha with he
      exact lt_of_not_ge he
    simpa only [eventOutcome,residentAt,List.forall_mem_append,List.forall_mem_cons]
      using And.intro hleft (And.intro hp hright)
  | inr d =>
    have hp : cellEnergy zL zH ⟨(selectedCell s.val i).high,
        nextCompartment (selectedCell s.val i).compartment (.inr ())⟩ < outerEnergy := by
      by_contra hn
      simp [eventReason,le_of_not_gt hn] at ha
    by_cases hm : (nextCompartment (selectedCell s.val i).compartment (.inr ())).2=2*N
    · have hg := active_division_births N M zL zH D s i d ha hm
      have hsmall : 4*innerEnergy < outerEnergy := by
        norm_num [innerEnergy,outerEnergy]
      have hd1 := hg.1.trans hsmall
      have hd2 := hg.2.trans hsmall
      simpa only [eventOutcome,growthAt,hm,if_true,List.forall_mem_append,List.forall_mem_cons]
        using And.intro hleft (And.intro hd1 (And.intro hd2 hright))
    · simpa only [eventOutcome,growthAt,hm,if_false,List.forall_mem_append,List.forall_mem_cons]
        using And.intro hleft (And.intro hp hright)

theorem positive_active_domain_preserved (N M : ℕ) (hN : 1 ≤ N) (zL zH γ : ℝ)
    (hzL : zL ∈ Set.Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Set.Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (s : ActiveState (activeDomain N M zL zH)) (e : CellEvent s.val)
    (hr : 0 < eventRate γ (4*(N*M)) ⟨s,e⟩)
    (ha : eventReason N M zL zH ⟨s,e⟩=.active) :
    eventOutcome N ⟨s,e⟩ ∈ activeDomain N M zL zH := by
  have hs := activeDomain_safe N M zL zH s.val s.property
  have hstep := positive_event_step γ (4*(N*M)) N _ s e hs.2.2.2.2.1
    (Nat.zero_lt_of_lt hs.1) hr
  have hres := active_event_resource N M zL zH _ s e hs.1 ha
  apply active_mem_domain N M hN zL zH hzL hzH
  exact ⟨hres.1,hres.2.trans hs.2.1,(step_conservation hstep).trans hs.2.2.1,
    step_live_divisions hstep hs.2.2.2.1,step_valid_volumes (by omega) hstep hs.2.2.2.2.1,
    active_event_energy N M zL zH _ s e hs.2.2.2.2.2 ha⟩

end ResourceLimitedCompetition
