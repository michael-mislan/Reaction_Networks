import proofs.SerialTransferSelection.BatchSpatialBoundary
import proofs.ResourceLimitedCompetition.PopulationSupport

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

theorem phase_active_event_resource (N W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (s : ActiveState D) (e : CellEvent s.val) (hQ : W0 < s.val.resource)
    (ha : phaseEventReason N W0 zL zH ⟨s,e⟩=.active) :
    W0 < (eventOutcome N ⟨s,e⟩).resource ∧
      (eventOutcome N ⟨s,e⟩).resource ≤ s.val.resource := by
  classical
  rcases e with ⟨i,ch⟩
  cases ch with
  | inl r => exact ⟨hQ,le_rfl⟩
  | inr d =>
    have hneq : s.val.resource-1 ≠ W0 := by
      intro he
      simp only [phaseEventReason] at ha
      split_ifs at ha
    simp only [eventOutcome,growthAt]
    split_ifs <;> dsimp only <;> omega

theorem phase_active_event_energy (N W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (s : ActiveState D) (e : CellEvent s.val)
    (hs : ∀ c ∈ s.val.live, cellEnergy zL zH c < (8*innerEnergy))
    (ha : phaseEventReason N W0 zL zH ⟨s,e⟩=.active) :
    ∀ c ∈ (eventOutcome N ⟨s,e⟩).live, cellEnergy zL zH c < (8*innerEnergy) := by
  classical
  rcases e with ⟨i,ch⟩
  have hleft : ∀ c ∈ s.val.live.take i.val, cellEnergy zL zH c < (8*innerEnergy) :=
    fun c hc => hs c (List.mem_of_mem_take hc)
  have hright : ∀ c ∈ s.val.live.drop (i.val+1), cellEnergy zL zH c < (8*innerEnergy) :=
    fun c hc => hs c (List.mem_of_mem_drop hc)
  cases ch with
  | inl r =>
    have hp : cellEnergy zL zH ⟨(selectedCell s.val i).high,
        nextCompartment (selectedCell s.val i).compartment (.inl r)⟩ < (8*innerEnergy) := by
      simp only [phaseEventReason] at ha
      split_ifs at ha with he
      exact lt_of_not_ge he
    simpa only [eventOutcome,residentAt,List.forall_mem_append,List.forall_mem_cons]
      using And.intro hleft (And.intro hp hright)
  | inr d =>
    have hp : cellEnergy zL zH ⟨(selectedCell s.val i).high,
        nextCompartment (selectedCell s.val i).compartment (.inr ())⟩ < (8*innerEnergy) := by
      by_contra hn
      simp [phaseEventReason,le_of_not_gt hn] at ha
    by_cases hm : (nextCompartment (selectedCell s.val i).compartment (.inr ())).2=2*N
    · have hg := phase_active_division_births N W0 zL zH D s i d ha hm
      have hsmall : 4*innerEnergy < (8*innerEnergy) := by
        norm_num [innerEnergy,outerEnergy]
      have hd1 := hg.1.trans hsmall
      have hd2 := hg.2.trans hsmall
      simpa only [eventOutcome,growthAt,hm,if_true,List.forall_mem_append,List.forall_mem_cons]
        using And.intro hleft (And.intro hd1 (And.intro hd2 hright))
    · simpa only [eventOutcome,growthAt,hm,if_false,List.forall_mem_append,List.forall_mem_cons]
        using And.intro hleft (And.intro hp hright)

theorem phase_positive_active_domain_preserved (N M W0 : ℕ) (hN : 1 ≤ N) (hW : W0 ≤ 2*N*M) (zL zH γ : ℝ)
    (hzL : zL ∈ Set.Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Set.Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (s : ActiveState (phaseActiveDomain N M W0 zL zH)) (e : CellEvent s.val)
    (hr : 0 < eventRate γ (4*W0) ⟨s,e⟩)
    (ha : phaseEventReason N W0 zL zH ⟨s,e⟩=.active) :
    eventOutcome N ⟨s,e⟩ ∈ phaseActiveDomain N M W0 zL zH := by
  have hs := phaseActiveDomain_safe N M W0 zL zH s.val s.property
  have hstep := positive_event_step γ (4*W0) N _ s e hs.2.2.2.2.1
    (Nat.zero_lt_of_lt hs.1) hr
  have hres := phase_active_event_resource N W0 zL zH _ s e hs.1 ha
  apply phase_active_mem_domain N M W0 hN hW zL zH hzL hzH
  exact ⟨hres.1,hres.2.trans hs.2.1,(step_conservation hstep).trans hs.2.2.1,
    step_live_divisions hstep hs.2.2.2.1,step_valid_volumes (by omega) hstep hs.2.2.2.2.1,
    phase_active_event_energy N W0 zL zH _ s e hs.2.2.2.2.2 ha⟩

end SerialTransferSelection
