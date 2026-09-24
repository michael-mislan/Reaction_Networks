import proofs.ResourceLimitedCompetition.CellOuter
import proofs.ResourceLimitedCompetition.SpatialPopulationBoundary

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy

noncomputable def outerReserve (N M D : ℕ) : ℝ :=
  (6*(M : ℝ)-2*(D : ℝ))*Real.exp (4*(N : ℝ)*localAlpha*innerEnergy)

theorem outerReserve_nonneg (N M D : ℕ) (hD : D ≤ 3*M) : 0 ≤ outerReserve N M D := by
  unfold outerReserve
  have hd : (D : ℝ) ≤ 3*(M : ℝ) := by exact_mod_cast hD
  exact mul_nonneg (by linarith only [hd]) (Real.exp_pos _).le

noncomputable def outerPopulationObservable (N M : ℕ) (zL zH : ℝ)
    (D : Finset PopulationState) : StoppedPopulation D → ℝ := by
  classical
  exact fun x => match x with
    | .inl s => potentialSum (cellOuter N zL zH) s.val+outerReserve N M s.val.divisions
    | .inr e => if eventReason N M zL zH e=.outer
        then Real.exp ((N : ℝ)*localAlpha*outerEnergy) else 0

theorem active_outer_outcome_le (N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (s : ActiveState D) (e : CellEvent s.val)
    (ha : eventReason N M zL zH ⟨s,e⟩=.active) :
    potentialSum (cellOuter N zL zH) (eventOutcome N ⟨s,e⟩)+
      outerReserve N M (eventOutcome N ⟨s,e⟩).divisions ≤
      rawEventPotential (cellOuter N zL zH) s.val e+outerReserve N M s.val.divisions := by
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
      have hd1 := cellOuter_birth N zL zH _ hg.1
      have hd2 := cellOuter_birth N zL zH _ hg.2
      have hp := cellOuter_nonneg N zL zH
        ⟨(selectedCell s.val i).high,nextCompartment (selectedCell s.val i).compartment (.inr ())⟩
      simp only [eventOutcome,growthAt,hm,if_true,potentialSum,List.map_append,
        List.map_cons,List.sum_append,List.sum_cons,outerReserve,Nat.cast_add,Nat.cast_one]
      linarith only [hd1,hd2,hp]
    · simp [eventOutcome,growthAt,hm,potentialSum,List.sum_append,add_assoc]

theorem outer_raw_barrier (N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (s : ActiveState D) (e : CellEvent s.val)
    (ho : eventReason N M zL zH ⟨s,e⟩=.outer) :
    Real.exp ((N : ℝ)*localAlpha*outerEnergy) ≤
      rawEventPotential (cellOuter N zL zH) s.val e := by
  classical
  rcases e with ⟨i,ch⟩
  have hleft := sum_map_nonneg _ (cellOuter_nonneg N zL zH) (s.val.live.take i.val)
  have hright := sum_map_nonneg _ (cellOuter_nonneg N zL zH) (s.val.live.drop (i.val+1))
  cases ch with
  | inl r =>
    have he : outerEnergy ≤ cellEnergy zL zH
        ⟨(selectedCell s.val i).high,nextCompartment (selectedCell s.val i).compartment (.inl r)⟩ := by
      simp only [eventReason] at ho
      split_ifs at ho with he
      exact he
    have hp := cellOuter_barrier N zL zH _ he
    simp only [rawEventPotential]
    rw [raw_selected_frame]
    linarith only [hp,hleft,hright]
  | inr d =>
    have he : outerEnergy ≤ cellEnergy zL zH
        ⟨(selectedCell s.val i).high,nextCompartment (selectedCell s.val i).compartment (.inr ())⟩ := by
      simp only [eventReason] at ho
      split_ifs at ho
      simp_all
    have hp := cellOuter_barrier N zL zH _ he
    simp only [rawEventPotential]
    rw [raw_selected_frame]
    linarith only [hp,hleft,hright]

theorem outer_next_le_raw (N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (s : ActiveState D) (hD : s.val.divisions ≤ 3*M) (e : CellEvent s.val) :
    outerPopulationObservable N M zL zH D
      (stoppedNext N M zL zH D (.inl s) ⟨s,e⟩) ≤
      rawEventPotential (cellOuter N zL zH) s.val e+outerReserve N M s.val.divisions := by
  classical
  have hr := outerReserve_nonneg N M s.val.divisions hD
  have hn := add_nonneg (raw_potential_nonneg _ (cellOuter_nonneg N zL zH) s.val e) hr
  simp only [stoppedNext,if_true]
  by_cases ha : eventReason N M zL zH ⟨s,e⟩=.active
  · simp only [ha,if_true]
    split_ifs
    · exact active_outer_outcome_le N M zL zH D s e ha
    · simpa [outerPopulationObservable,ha] using hn
  · simp only [ha,if_false,outerPopulationObservable]
    split_ifs with ho
    · exact (outer_raw_barrier N M zL zH D s e ho).trans (le_add_of_nonneg_right hr)
    · exact hn

end ResourceLimitedCompetition
