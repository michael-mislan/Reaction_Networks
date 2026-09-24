import proofs.SerialTransferSelection.BatchGeometry
import proofs.ResourceLimitedCompetition.SpatialPopulationBoundary

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

theorem phase_division_reason_bounds (N W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (e : PopulationEvent D) (h : phaseEventReason N W0 zL zH e=.divisionEnergy) :
    (nextCompartment (selectedCell e.1.val e.2.1).compartment (.inr ())).2=2*N ∧
      2*innerEnergy < cellEnergy zL zH
        ⟨(selectedCell e.1.val e.2.1).high,
          nextCompartment (selectedCell e.1.val e.2.1).compartment (.inr ())⟩ := by
  classical
  rcases e with ⟨s,i,ch⟩
  cases ch with
  | inl r =>
    simp only [phaseEventReason] at h
    split_ifs at h
  | inr d =>
    simp only [phaseEventReason] at h
    split_ifs at h
    simp_all

theorem phase_active_division_births (N W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (s : ActiveState D) (i : Fin s.val.live.length)
    (d : {d : Counts // d ∈ daughterDraws
      (nextCompartment (selectedCell s.val i).compartment (.inr ())).1})
    (h : phaseEventReason N W0 zL zH ⟨s,i,.inr d⟩=.active)
    (hm : (nextCompartment (selectedCell s.val i).compartment (.inr ())).2=2*N) :
    cellEnergy zL zH ⟨(selectedCell s.val i).high,(d.val,N)⟩ < 4*innerEnergy ∧
      cellEnergy zL zH ⟨(selectedCell s.val i).high,
        ((fun j => (nextCompartment (selectedCell s.val i).compartment (.inr ())).1 j-d.val j),N)⟩ < 4*innerEnergy := by
  classical
  simp only [phaseEventReason] at h
  split_ifs at h
  simp_all

noncomputable def phaseSpatialPopulationObservable (N W0 : ℕ) (zL zH : ℝ)
    (D : Finset PopulationState) : StoppedPopulation D → ℝ := by
  classical
  exact fun x => match x with
    | .inl s => potentialSum (cellSpatial N zL zH) s.val
    | .inr e => if phaseEventReason N W0 zL zH e=.divisionEnergy
        then Real.exp (2*(N : ℝ)*localAlpha*innerEnergy) else 0

theorem phase_spatial_population_nonneg (N W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (x : StoppedPopulation D) : 0 ≤ phaseSpatialPopulationObservable N W0 zL zH D x := by
  classical
  cases x with
  | inl s => exact sum_map_nonneg _ (cellSpatial_nonneg N zL zH) _
  | inr e =>
    simp only [phaseSpatialPopulationObservable]
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl

theorem phase_active_spatial_outcome_le (N W0 : ℕ)
    (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (zL zH : ℝ) (D : Finset PopulationState) (s : ActiveState D)
    (e : CellEvent s.val) (ha : phaseEventReason N W0 zL zH ⟨s,e⟩=.active) :
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
    · have hg := phase_active_division_births N W0 zL zH D s i d ha hm
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

theorem phase_division_raw_barrier (N W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (s : ActiveState D) (e : CellEvent s.val)
    (hd : phaseEventReason N W0 zL zH ⟨s,e⟩=.divisionEnergy) :
    Real.exp (2*(N : ℝ)*localAlpha*innerEnergy) ≤
      rawEventPotential (cellSpatial N zL zH) s.val e := by
  classical
  have hb := phase_division_reason_bounds N W0 zL zH D ⟨s,e⟩ hd
  rcases e with ⟨i,ch⟩
  cases ch with
  | inl r =>
    simp only [phaseEventReason] at hd
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

theorem phase_spatial_next_le_raw (N W0 : ℕ)
    (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (zL zH : ℝ) (D : Finset PopulationState) (s : ActiveState D)
    (e : CellEvent s.val) :
    phaseSpatialPopulationObservable N W0 zL zH D
      (phaseStoppedNext N W0 zL zH D (.inl s) ⟨s,e⟩) ≤
      rawEventPotential (cellSpatial N zL zH) s.val e := by
  classical
  have hn := raw_potential_nonneg _ (cellSpatial_nonneg N zL zH) s.val e
  simp only [phaseStoppedNext,if_true]
  by_cases ha : phaseEventReason N W0 zL zH ⟨s,e⟩=.active
  · simp only [ha,if_true]
    split_ifs
    · exact phase_active_spatial_outcome_le N W0 hlarge zL zH D s e ha
    · simpa [phaseSpatialPopulationObservable,ha] using hn
  · simp only [ha,if_false,phaseSpatialPopulationObservable]
    split_ifs with hd
    · exact phase_division_raw_barrier N W0 zL zH D s e hd
    · exact hn

end SerialTransferSelection
