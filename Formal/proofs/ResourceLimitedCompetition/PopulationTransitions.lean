import proofs.ResourceLimitedCompetition.StoppedPopulation

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy

theorem selected_decomposition (s : PopulationState) (i : Fin s.live.length) :
    s.live.take i.val++selectedCell s i::s.live.drop (i.val+1)=s.live := by
  have h := List.take_append_drop (i.val+1) s.live
  rw [List.take_succ_eq_append_getElem i.isLt] at h
  simp [selectedCell]

theorem selected_mem (s : PopulationState) (i : Fin s.live.length) :
    selectedCell s i ∈ s.live := by
  have h : selectedCell s i ∈ s.live.take i.val++selectedCell s i::s.live.drop (i.val+1) := by simp
  rwa [selected_decomposition] at h

theorem sourceAt_selected (s : PopulationState) (i : Fin s.live.length) :
    sourceAt s.resource s.divisions (s.live.take i.val) (selectedCell s i)
      (s.live.drop (i.val+1))=s := by
  unfold sourceAt
  rw [selected_decomposition]

/-- Every chosen event retains its literal physical output, including failures. -/
theorem physical_next_chosen (N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (e : PopulationEvent D) :
    physicalState N (stoppedNext N M zL zH D (.inl e.1) e)=eventOutcome N e := by
  classical
  unfold stoppedNext
  dsimp only
  rw [if_pos rfl]
  split_ifs <;> rfl

end ResourceLimitedCompetition
