import proofs.ResourceLimitedCompetition.CellSpatial

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy

theorem sum_map_nonneg (F : TaggedCell → ℝ) (hF : ∀ c, 0 ≤ F c) (cs : List TaggedCell) :
    0 ≤ (cs.map F).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih => simpa only [List.map_cons,List.sum_cons] using add_nonneg (hF c) ih

theorem raw_selected_frame (F : TaggedCell → ℝ) (s : PopulationState)
    (i : Fin s.live.length) (r : Channel) :
    potentialSum F s-F (selectedCell s i)+
      F ⟨(selectedCell s i).high,nextCompartment (selectedCell s i).compartment r⟩ =
    ((s.live.take i.val).map F).sum+
      F ⟨(selectedCell s i).high,nextCompartment (selectedCell s i).compartment r⟩+
      ((s.live.drop (i.val+1)).map F).sum := by
  have h := congrArg (fun cs : List TaggedCell => (cs.map F).sum) (selected_decomposition s i)
  simp only [List.map_append,List.map_cons,List.sum_append,List.sum_cons] at h
  unfold potentialSum
  linarith only [h]

theorem raw_potential_nonneg (F : TaggedCell → ℝ) (hF : ∀ c, 0 ≤ F c)
    (s : PopulationState) (e : CellEvent s) : 0 ≤ rawEventPotential F s e := by
  unfold rawEventPotential
  rw [raw_selected_frame]
  exact add_nonneg (add_nonneg (sum_map_nonneg F hF _) (hF _)) (sum_map_nonneg F hF _)

theorem division_reason_bounds (N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (e : PopulationEvent D) (h : eventReason N M zL zH e=.divisionEnergy) :
    (nextCompartment (selectedCell e.1.val e.2.1).compartment (.inr ())).2=2*N ∧
      2*innerEnergy < cellEnergy zL zH
        ⟨(selectedCell e.1.val e.2.1).high,
          nextCompartment (selectedCell e.1.val e.2.1).compartment (.inr ())⟩ := by
  classical
  rcases e with ⟨s,i,ch⟩
  cases ch with
  | inl r =>
    simp only [eventReason] at h
    split_ifs at h
  | inr d =>
    simp only [eventReason] at h
    split_ifs at h
    simp_all

theorem active_division_births (N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (s : ActiveState D) (i : Fin s.val.live.length)
    (d : {d : Counts // d ∈ daughterDraws
      (nextCompartment (selectedCell s.val i).compartment (.inr ())).1})
    (h : eventReason N M zL zH ⟨s,i,.inr d⟩=.active)
    (hm : (nextCompartment (selectedCell s.val i).compartment (.inr ())).2=2*N) :
    cellEnergy zL zH ⟨(selectedCell s.val i).high,(d.val,N)⟩ < 4*innerEnergy ∧
      cellEnergy zL zH ⟨(selectedCell s.val i).high,
        ((fun j => (nextCompartment (selectedCell s.val i).compartment (.inr ())).1 j-d.val j),N)⟩ < 4*innerEnergy := by
  classical
  simp only [eventReason] at h
  split_ifs at h
  simp_all

noncomputable def spatialPopulationObservable (N M : ℕ) (zL zH : ℝ)
    (D : Finset PopulationState) : StoppedPopulation D → ℝ := by
  classical
  exact fun x => match x with
    | .inl s => potentialSum (cellSpatial N zL zH) s.val
    | .inr e => if eventReason N M zL zH e=.divisionEnergy
        then Real.exp (2*(N : ℝ)*localAlpha*innerEnergy) else 0

theorem spatial_population_nonneg (N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (x : StoppedPopulation D) : 0 ≤ spatialPopulationObservable N M zL zH D x := by
  classical
  cases x with
  | inl s => exact sum_map_nonneg _ (cellSpatial_nonneg N zL zH) _
  | inr e =>
    simp only [spatialPopulationObservable]
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl

theorem active_spatial_outcome_le (N M : ℕ)
    (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (zL zH : ℝ) (D : Finset PopulationState) (s : ActiveState D)
    (e : CellEvent s.val) (ha : eventReason N M zL zH ⟨s,e⟩=.active) :
    potentialSum (cellSpatial N zL zH) (eventOutcome N ⟨s,e⟩) ≤
      rawEventPotential (cellSpatial N zL zH) s.val e := by
  classical
  rcases e with ⟨i,ch⟩
  cases ch with
  | inl r =>
    simp only [rawEventPotential]
    rw [raw_selected_frame]
    simp [eventOutcome,residentAt,potentialSum,List.sum_append,add_assoc]
  | inr d =>
    simp only [rawEventPotential]
    rw [raw_selected_frame]
    by_cases hm : (nextCompartment (selectedCell s.val i).compartment (.inr ())).2=2*N
    · have hg := active_division_births N M zL zH D s i d ha hm
      have hr := cellSpatial_pair_reset N hlarge zL zH (selectedCell s.val i).high
        (nextCompartment (selectedCell s.val i).compartment (.inr ())).1 d.val hg
      have hp : ((nextCompartment (selectedCell s.val i).compartment (.inr ())).1,2*N)=
          nextCompartment (selectedCell s.val i).compartment (.inr ()) := by
        rw [← hm]
      rw [hp] at hr
      simp only [eventOutcome,growthAt,hm,if_true,potentialSum,List.map_append,
        List.map_cons,List.sum_append,List.sum_cons]
      linarith only [hr]
    · simp [eventOutcome,growthAt,hm,potentialSum,List.sum_append,add_assoc]

theorem division_raw_barrier (N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (s : ActiveState D) (e : CellEvent s.val)
    (hd : eventReason N M zL zH ⟨s,e⟩=.divisionEnergy) :
    Real.exp (2*(N : ℝ)*localAlpha*innerEnergy) ≤
      rawEventPotential (cellSpatial N zL zH) s.val e := by
  classical
  have hb := division_reason_bounds N M zL zH D ⟨s,e⟩ hd
  rcases e with ⟨i,ch⟩
  cases ch with
  | inl r =>
    simp only [eventReason] at hd
    split_ifs at hd
  | inr d =>
    have hp := cellSpatial_division_barrier N zL zH
      ⟨(selectedCell s.val i).high,nextCompartment (selectedCell s.val i).compartment (.inr ())⟩
      hb.1 hb.2.le
    simp only [rawEventPotential]
    rw [raw_selected_frame]
    have hleft := sum_map_nonneg _ (cellSpatial_nonneg N zL zH) (s.val.live.take i.val)
    have hright := sum_map_nonneg _ (cellSpatial_nonneg N zL zH) (s.val.live.drop (i.val+1))
    linarith only [hp,hleft,hright]

theorem spatial_next_le_raw (N M : ℕ)
    (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (zL zH : ℝ) (D : Finset PopulationState) (s : ActiveState D)
    (e : CellEvent s.val) :
    spatialPopulationObservable N M zL zH D
      (stoppedNext N M zL zH D (.inl s) ⟨s,e⟩) ≤
      rawEventPotential (cellSpatial N zL zH) s.val e := by
  classical
  have hn := raw_potential_nonneg _ (cellSpatial_nonneg N zL zH) s.val e
  simp only [stoppedNext,if_true]
  by_cases ha : eventReason N M zL zH ⟨s,e⟩=.active
  · simp only [ha,if_true]
    split_ifs
    · exact active_spatial_outcome_le N M hlarge zL zH D s e ha
    · simpa [spatialPopulationObservable,ha] using hn
  · simp only [ha,if_false,spatialPopulationObservable]
    split_ifs with hd
    · exact division_raw_barrier N M zL zH D s e hd
    · exact hn

end ResourceLimitedCompetition
