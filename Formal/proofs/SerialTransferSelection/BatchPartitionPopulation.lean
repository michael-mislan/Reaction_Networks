import proofs.SerialTransferSelection.BatchPartitionEvent
import proofs.ResourceLimitedCompetition.PartitionPopulation

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set

noncomputable def phasePartitionReserve (N M D : ℕ) : ℝ :=
  (7*(M : ℝ)-(D : ℝ))*partitionError N

theorem phasePartitionReserve_nonneg (N M D : ℕ) (hD : D ≤ 7*M) :
    0 ≤ phasePartitionReserve N M D := by
  have hd : (D : ℝ) ≤ 7*(M : ℝ) := by exact_mod_cast hD
  exact mul_nonneg (sub_nonneg.mpr hd) (partitionError_nonneg N)

noncomputable def phasePartitionPopulationObservable (N M W0 : ℕ) (zL zH : ℝ)
    (D : Finset PopulationState) : StoppedPopulation D → ℝ
  | .inl s => phasePartitionReserve N M s.val.divisions
  | .inr e => phasePartitionFlag N W0 zL zH e

theorem phasePartitionFlag_nonneg (N W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (e : PopulationEvent D) : 0 ≤ phasePartitionFlag N W0 zL zH e := by
  unfold phasePartitionFlag
  split_ifs <;> norm_num

theorem phase_partition_next_le (N M W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (s : ActiveState D) (hD : s.val.divisions < 7*M) (e : CellEvent s.val) :
    phasePartitionPopulationObservable N M W0 zL zH D
      (phaseStoppedNext N W0 zL zH D (.inl s) ⟨s,e⟩) ≤
      phasePartitionReserve N M (eventOutcome N ⟨s,e⟩).divisions+phasePartitionFlag N W0 zL zH ⟨s,e⟩ := by
  classical
  have hn := phasePartitionReserve_nonneg N M (eventOutcome N ⟨s,e⟩).divisions
    ((event_divisions_le_succ N D ⟨s,e⟩).trans (by change s.val.divisions+1 ≤ 7*M; omega))
  simp only [phaseStoppedNext,if_true]
  split_ifs
  · exact le_add_of_nonneg_right (phasePartitionFlag_nonneg N W0 zL zH D ⟨s,e⟩)
  · exact le_add_of_nonneg_left hn
  · exact le_add_of_nonneg_left hn

theorem phase_growth_partition_compensated (γ : ℝ) (hγ : 0 ≤ γ) (Ω N M W0 : ℕ) (hN : 0 < N)
    (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (D : Finset PopulationState) (s : ActiveState D) (i : Fin s.val.live.length) :
    (∑ d : {d : Counts // d ∈ daughterDraws
        (nextCompartment (selectedCell s.val i).compartment (.inr ())).1},
      eventRate γ Ω ⟨s,i,.inr d⟩*
        (phasePartitionReserve N M (eventOutcome N ⟨s,i,.inr d⟩).divisions+
          phasePartitionFlag N W0 zL zH ⟨s,i,.inr d⟩-phasePartitionReserve N M s.val.divisions)) ≤ 0 := by
  classical
  have ha : 0 ≤ propensity (resourceCoefficient γ s.val.resource Ω)
      (selectedCell s.val i).compartment (.inr ()) := by
    apply propensity_nonneg
    unfold resourceCoefficient
    positivity
  have h := weighted_partition_compensation _ _ _ ha
    (fun d => phasePartitionFlag N W0 zL zH ⟨s,i,.inr d⟩)
    (phase_growth_partition_average N W0 hN zL zH hzL hzH D s i)
  convert h using 1
  apply Finset.sum_congr rfl
  intro d _
  simp only [eventRate,eventOutcome,growthAt]
  split_ifs <;> simp only [phasePartitionReserve,Nat.cast_add,Nat.cast_one] <;> ring

end SerialTransferSelection
