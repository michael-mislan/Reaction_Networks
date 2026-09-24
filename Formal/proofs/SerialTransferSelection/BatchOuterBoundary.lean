import proofs.ResourceLimitedCompetition.CellOuter
import proofs.SerialTransferSelection.BatchSpatialBoundary

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

theorem phase_cellOuter_barrier (N : ℕ) (zL zH : ℝ) (c : TaggedCell)
    (he : 8*innerEnergy ≤ cellEnergy zL zH c) :
    Real.exp ((N : ℝ)*localAlpha*(8*innerEnergy)) ≤ cellOuter N zL zH c := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left he (by unfold localAlpha; positivity)

noncomputable def phaseOuterReserve (N M D : ℕ) : ℝ :=
  (14*(M : ℝ)-2*(D : ℝ))*Real.exp (4*(N : ℝ)*localAlpha*innerEnergy)

theorem phaseOuterReserve_nonneg (N M D : ℕ) (hD : D ≤ 7*M) : 0 ≤ phaseOuterReserve N M D := by
  unfold phaseOuterReserve
  have hd : (D : ℝ) ≤ 7*(M : ℝ) := by exact_mod_cast hD
  exact mul_nonneg (by linarith only [hd]) (Real.exp_pos _).le

noncomputable def phaseOuterPopulationObservable (N M W0 : ℕ) (zL zH : ℝ)
    (D : Finset PopulationState) : StoppedPopulation D → ℝ := by
  classical
  exact fun x => match x with
    | .inl s => potentialSum (cellOuter N zL zH) s.val+phaseOuterReserve N M s.val.divisions
    | .inr e => if phaseEventReason N W0 zL zH e=.outer
        then Real.exp ((N : ℝ)*localAlpha*(8*innerEnergy)) else 0

theorem phase_active_outer_outcome_le (N M W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (s : ActiveState D) (e : CellEvent s.val)
    (ha : phaseEventReason N W0 zL zH ⟨s,e⟩=.active) :
    potentialSum (cellOuter N zL zH) (eventOutcome N ⟨s,e⟩)+
      phaseOuterReserve N M (eventOutcome N ⟨s,e⟩).divisions ≤
      rawEventPotential (cellOuter N zL zH) s.val e+phaseOuterReserve N M s.val.divisions := by
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
      have hd1 := cellOuter_birth N zL zH _ hg.1
      have hd2 := cellOuter_birth N zL zH _ hg.2
      have hp := cellOuter_nonneg N zL zH
        ⟨(selectedCell s.val i).high,nextCompartment (selectedCell s.val i).compartment (.inr ())⟩
      simp only [eventOutcome,growthAt,hm,if_true,potentialSum,List.map_append,
        List.map_cons,List.sum_append,List.sum_cons,phaseOuterReserve,Nat.cast_add,Nat.cast_one]
      linarith only [hd1,hd2,hp]
    · simp [eventOutcome,growthAt,hm,potentialSum,List.sum_append,add_assoc]

theorem phase_outer_raw_barrier (N W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (s : ActiveState D) (e : CellEvent s.val)
    (ho : phaseEventReason N W0 zL zH ⟨s,e⟩=.outer) :
    Real.exp ((N : ℝ)*localAlpha*(8*innerEnergy)) ≤
      rawEventPotential (cellOuter N zL zH) s.val e := by
  classical
  rcases e with ⟨i,ch⟩
  have hleft := sum_map_nonneg _ (cellOuter_nonneg N zL zH) (s.val.live.take i.val)
  have hright := sum_map_nonneg _ (cellOuter_nonneg N zL zH) (s.val.live.drop (i.val+1))
  cases ch with
  | inl r =>
    have he : (8*innerEnergy) ≤ cellEnergy zL zH
        ⟨(selectedCell s.val i).high,nextCompartment (selectedCell s.val i).compartment (.inl r)⟩ := by
      simp only [phaseEventReason] at ho
      split_ifs at ho with he
      exact he
    have hp := phase_cellOuter_barrier N zL zH _ he
    simp only [rawEventPotential]
    rw [raw_selected_frame]
    linarith only [hp,hleft,hright]
  | inr d =>
    have he : (8*innerEnergy) ≤ cellEnergy zL zH
        ⟨(selectedCell s.val i).high,nextCompartment (selectedCell s.val i).compartment (.inr ())⟩ := by
      simp only [phaseEventReason] at ho
      split_ifs at ho
      simp_all
    have hp := phase_cellOuter_barrier N zL zH _ he
    simp only [rawEventPotential]
    rw [raw_selected_frame]
    linarith only [hp,hleft,hright]

theorem phase_outer_next_le_raw (N M W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (s : ActiveState D) (hD : s.val.divisions ≤ 7*M) (e : CellEvent s.val) :
    phaseOuterPopulationObservable N M W0 zL zH D
      (phaseStoppedNext N W0 zL zH D (.inl s) ⟨s,e⟩) ≤
      rawEventPotential (cellOuter N zL zH) s.val e+phaseOuterReserve N M s.val.divisions := by
  classical
  have hr := phaseOuterReserve_nonneg N M s.val.divisions hD
  have hn := add_nonneg (raw_potential_nonneg _ (cellOuter_nonneg N zL zH) s.val e) hr
  simp only [phaseStoppedNext,if_true]
  by_cases ha : phaseEventReason N W0 zL zH ⟨s,e⟩=.active
  · simp only [ha,if_true]
    split_ifs
    · exact phase_active_outer_outcome_le N M W0 zL zH D s e ha
    · simpa [phaseOuterPopulationObservable,ha] using hn
  · simp only [ha,if_false,phaseOuterPopulationObservable]
    split_ifs with ho
    · exact (phase_outer_raw_barrier N W0 zL zH D s e ho).trans (le_add_of_nonneg_right hr)
    · exact hn

end SerialTransferSelection
