import proofs.ProductiveMemory.ExtractionSpatialBoundary
import proofs.ResourceLimitedCompetition.PopulationSupport

namespace ProductiveMemory
noncomputable section
set_option Elab.async false
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

theorem productive_legacy_active_event_resource (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState)
    (s : ProductiveActive D) (e : CellEvent s.val.population) (hQ : W0 < s.val.population.resource)
    (ha : productiveReason N W0 J rho zL zH ⟨s,.inl e⟩=.active) :
    W0 < (productiveOutcome N s.val (.inl e)).population.resource ∧
      (productiveOutcome N s.val (.inl e)).population.resource ≤ s.val.population.resource := by
  classical
  rcases e with ⟨i,ch⟩
  cases ch with
  | inl r => exact ⟨hQ,le_rfl⟩
  | inr d =>
    have hneq : s.val.population.resource-1 ≠ W0 := by
      intro he
      simp only [productiveReason] at ha
      split_ifs at ha
    simp only [productiveOutcome,growthAt]
    split_ifs <;> dsimp only <;> omega

theorem productive_legacy_active_event_energy (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState)
    (s : ProductiveActive D) (e : CellEvent s.val.population)
    (hs : ∀ c ∈ s.val.population.live, extractionCellEnergy rho zL zH c < (8*readyLevel))
    (ha : productiveReason N W0 J rho zL zH ⟨s,.inl e⟩=.active) :
    ∀ c ∈ (productiveOutcome N s.val (.inl e)).population.live, extractionCellEnergy rho zL zH c < (8*readyLevel) := by
  classical
  rcases e with ⟨i,ch⟩
  have hleft : ∀ c ∈ s.val.population.live.take i.val, extractionCellEnergy rho zL zH c < (8*readyLevel) :=
    fun c hc => hs c (List.mem_of_mem_take hc)
  have hright : ∀ c ∈ s.val.population.live.drop (i.val+1), extractionCellEnergy rho zL zH c < (8*readyLevel) :=
    fun c hc => hs c (List.mem_of_mem_drop hc)
  cases ch with
  | inl r =>
    have hp : extractionCellEnergy rho zL zH ⟨(selectedCell s.val.population i).high,
        nextCompartment (selectedCell s.val.population i).compartment (.inl r)⟩ < (8*readyLevel) := by
      simp only [productiveReason] at ha
      split_ifs at ha with he
      exact lt_of_not_ge he
    simpa only [productiveOutcome,residentAt,List.forall_mem_append,List.forall_mem_cons]
      using And.intro hleft (And.intro hp hright)
  | inr d =>
    have hp : extractionCellEnergy rho zL zH ⟨(selectedCell s.val.population i).high,
        nextCompartment (selectedCell s.val.population i).compartment (.inr ())⟩ < (8*readyLevel) := by
      by_contra hn
      simp [productiveReason,le_of_not_gt hn] at ha
    by_cases hm : (nextCompartment (selectedCell s.val.population i).compartment (.inr ())).2=2*N
    · have hg := productive_active_births N W0 J rho zL zH D s i d ha hm
      have hsmall : 4*readyLevel < (8*readyLevel) := by
        norm_num [readyLevel,outerLevel]
      have hd1 := hg.1.trans hsmall
      have hd2 := hg.2.trans hsmall
      simpa only [productiveOutcome,growthAt,hm,if_true,List.forall_mem_append,List.forall_mem_cons]
        using And.intro hleft (And.intro hd1 (And.intro hd2 hright))
    · simpa only [productiveOutcome,growthAt,hm,if_false,List.forall_mem_append,List.forall_mem_cons]
        using And.intro hleft (And.intro hp hright)


theorem productive_active_event_resource (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState)
    (s : ProductiveActive D) (e : ProductiveEvent s.val) (hQ : W0 < s.val.population.resource)
    (ha : productiveReason N W0 J rho zL zH ⟨s,e⟩=.active) :
    W0 < (productiveOutcome N s.val e).population.resource ∧
      (productiveOutcome N s.val e).population.resource ≤ s.val.population.resource := by
  cases e with
  | inl e => exact productive_legacy_active_event_resource N W0 J rho zL zH D s e hQ ha
  | inr i => exact ⟨hQ,le_rfl⟩

theorem productive_active_event_energy (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState)
    (s : ProductiveActive D) (e : ProductiveEvent s.val)
    (hs : ∀ c ∈ s.val.population.live, extractionCellEnergy rho zL zH c < 8*readyLevel)
    (ha : productiveReason N W0 J rho zL zH ⟨s,e⟩=.active) :
    ∀ c ∈ (productiveOutcome N s.val e).population.live, extractionCellEnergy rho zL zH c < 8*readyLevel := by
  classical
  cases e with
  | inl e => exact productive_legacy_active_event_energy N W0 J rho zL zH D s e hs ha
  | inr i =>
    have hleft : ∀ c ∈ s.val.population.live.take i.val, extractionCellEnergy rho zL zH c < 8*readyLevel :=
      fun c hc => hs c (List.mem_of_mem_take hc)
    have hright : ∀ c ∈ s.val.population.live.drop (i.val+1), extractionCellEnergy rho zL zH c < 8*readyLevel :=
      fun c hc => hs c (List.mem_of_mem_drop hc)
    have hp : extractionCellEnergy rho zL zH ⟨(selectedCell s.val.population i).high,
        (channelNext (selectedCell s.val.population i).compartment.1 (.inr ()),
          (selectedCell s.val.population i).compartment.2)⟩ < 8*readyLevel := by
      simp only [productiveReason] at ha
      split_ifs at ha with he
      exact lt_of_not_ge he
    simpa only [productiveOutcome,extractionAt,List.forall_mem_append,List.forall_mem_cons]
      using And.intro hleft (And.intro hp hright)

theorem productive_active_event_collected (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState)
    (s : ProductiveActive D) (e : ProductiveEvent s.val) (hs : s.val.collected < J)
    (ha : productiveReason N W0 J rho zL zH ⟨s,e⟩=.active) :
    (productiveOutcome N s.val e).collected < J := by
  classical
  cases e with
  | inl e => rcases e with ⟨i,r | d⟩ <;> exact hs
  | inr i =>
    change s.val.collected+1 < J
    simp only [productiveReason] at ha
    split_ifs at ha with he hJ
    exact lt_of_not_ge hJ

theorem productive_positive_event_invariants (N M : ℕ) (hN : 0 < N) (rho γ : ℝ) (Ω : ℕ)
    (s : ProductiveState) (e : ProductiveEvent s)
    (hv : ValidVolumes N s.population) (hQ : 0 < s.population.resource)
    (hlen : s.population.live.length=M+s.population.divisions)
    (hr : 0 < productiveRate rho γ Ω s e) :
    (productiveOutcome N s e).population.resource+membrane (productiveOutcome N s e).population.live =
      s.population.resource+membrane s.population.live ∧
    (productiveOutcome N s e).population.live.length=M+(productiveOutcome N s e).population.divisions ∧
    ValidVolumes N (productiveOutcome N s e).population := by
  classical
  cases e with
  | inl e =>
    let a : ActiveState ({s.population} : Finset PopulationState) := ⟨s.population,Finset.mem_singleton_self _⟩
    have hrate : 0 < eventRate γ Ω ⟨a,e⟩ := by
      simpa only [← productive_legacy_rate rho γ Ω s.collected ⟨a,e⟩] using hr
    have hstep := positive_event_step γ Ω N _ a e hv hQ hrate
    have hout : (productiveOutcome N s (.inl e)).population=eventOutcome N ⟨a,e⟩ := by
      rcases e with ⟨i,r | d⟩ <;> rfl
    rw [hout]
    exact ⟨step_conservation hstep,step_live_divisions hstep hlen,step_valid_volumes hN hstep hv⟩
  | inr i =>
    refine ⟨?_,?_,?_⟩
    · rw [productive_extraction_resource,productive_extraction_membrane]
    · have hd := congrArg List.length (selected_decomposition s.population i)
      simpa only [productiveOutcome,extractionAt,List.length_append,List.length_cons] using hd.trans hlen
    · have hleft : ∀ c ∈ s.population.live.take i.val, N ≤ c.compartment.2 ∧ c.compartment.2 < 2*N :=
        fun c hc => hv c (List.mem_of_mem_take hc)
      have hright : ∀ c ∈ s.population.live.drop (i.val+1), N ≤ c.compartment.2 ∧ c.compartment.2 < 2*N :=
        fun c hc => hv c (List.mem_of_mem_drop hc)
      simpa only [ValidVolumes,productiveOutcome,extractionAt,List.forall_mem_append,List.forall_mem_cons]
        using And.intro hleft (And.intro (hv _ (selected_mem _ _)) hright)

theorem productive_positive_active_domain_preserved (N M W0 J : ℕ) (hN : 1 ≤ N) (hW : W0 ≤ 2*N*M)
    (rho zL zH γ : ℝ) (hrho : rho ∈ Set.Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Set.Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Set.Icc (289014/100000:ℝ) (289017/100000))
    (s : ProductiveActive (productiveActiveDomain N M W0 J rho zL zH)) (e : ProductiveEvent s.val)
    (hr : 0 < productiveRate rho γ (4*W0) s.val e)
    (ha : productiveReason N W0 J rho zL zH ⟨s,e⟩=.active) :
    productiveOutcome N s.val e ∈ productiveActiveDomain N M W0 J rho zL zH := by
  have hs := productive_active_safe N M W0 J rho zL zH s.val s.property
  have hi := productive_positive_event_invariants N M (by omega) rho γ (4*W0) s.val e
    hs.2.2.2.2.1 (Nat.zero_lt_of_lt hs.1) hs.2.2.2.1 hr
  have hres := productive_active_event_resource N W0 J rho zL zH _ s e hs.1 ha
  apply productive_active_mem N M W0 J hN hW rho zL zH hrho hzL hzH
  exact ⟨hres.1,hres.2.trans hs.2.1,hi.1.trans hs.2.2.1,hi.2.1,hi.2.2,
    productive_active_event_energy N W0 J rho zL zH _ s e hs.2.2.2.2.2.1 ha,
    productive_active_event_collected N W0 J rho zL zH _ s e hs.2.2.2.2.2.2 ha⟩

end
end ProductiveMemory
