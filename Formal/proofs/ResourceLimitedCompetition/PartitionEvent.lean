import proofs.ResourceLimitedCompetition.CellPartition

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy Set

noncomputable def partitionFlag (N M : ℕ) (zL zH : ℝ) {D : Finset PopulationState}
    (e : PopulationEvent D) : ℝ := if eventReason N M zL zH e=.partition then 1 else 0

theorem resident_partition_flag (N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (s : ActiveState D) (i : Fin s.val.live.length) (r : Fin 13) :
    partitionFlag N M zL zH ⟨s,i,.inl r⟩=0 := by
  classical
  simp only [partitionFlag,eventReason]
  split_ifs <;> simp_all

theorem growth_partition_flag (N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (s : ActiveState D) (i : Fin s.val.live.length)
    (d : {d : Counts // d ∈ daughterDraws
      (nextCompartment (selectedCell s.val i).compartment (.inr ())).1}) :
    partitionFlag N M zL zH ⟨s,i,.inr d⟩ =
      if outerEnergy ≤ cellEnergy zL zH
        ⟨(selectedCell s.val i).high,nextCompartment (selectedCell s.val i).compartment (.inr ())⟩
      then 0 else
      if (nextCompartment (selectedCell s.val i).compartment (.inr ())).2=2*N then
        if 2*innerEnergy < cellEnergy zL zH
          ⟨(selectedCell s.val i).high,nextCompartment (selectedCell s.val i).compartment (.inr ())⟩
        then 0 else if ¬goodBirths N zL zH (selectedCell s.val i).high
          (nextCompartment (selectedCell s.val i).compartment (.inr ())).1 d.val then 1 else 0
      else 0 := by
  classical
  simp only [partitionFlag,eventReason,goodBirths]
  split_ifs <;> simp_all

theorem growth_partition_average (N M : ℕ) (hN : 0 < N) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (D : Finset PopulationState) (s : ActiveState D) (i : Fin s.val.live.length) :
    (∑ d : {d : Counts // d ∈ daughterDraws
        (nextCompartment (selectedCell s.val i).compartment (.inr ())).1},
      daughterWeight (nextCompartment (selectedCell s.val i).compartment (.inr ())).1 d.val*
        partitionFlag N M zL zH ⟨s,i,.inr d⟩) ≤
      if (nextCompartment (selectedCell s.val i).compartment (.inr ())).2=2*N
        then partitionError N else 0 := by
  classical
  simp only [growth_partition_flag]
  by_cases ho : outerEnergy ≤ cellEnergy zL zH
      ⟨(selectedCell s.val i).high,nextCompartment (selectedCell s.val i).compartment (.inr ())⟩
  · simp only [ho,if_true,mul_zero,Finset.sum_const_zero]
    split_ifs
    · exact partitionError_nonneg N
    · exact le_rfl
  · simp only [ho,if_false]
    split_ifs with hm he
    · simpa using partitionError_nonneg N
    · have hp : ((nextCompartment (selectedCell s.val i).compartment (.inr ())).1,2*N)=
          nextCompartment (selectedCell s.val i).compartment (.inr ()) := by rw [← hm]
      have henergy : cellEnergy zL zH
          ⟨(selectedCell s.val i).high,
            ((nextCompartment (selectedCell s.val i).compartment (.inr ())).1,2*N)⟩ ≤ 2*innerEnergy := by
        rw [hp]
        exact le_of_not_gt he
      let n := (nextCompartment (selectedCell s.val i).compartment (.inr ())).1
      let f : Counts → ℝ := fun d => daughterWeight n d*
        (if ¬goodBirths N zL zH (selectedCell s.val i).high n d then 1 else 0)
      change (∑ d : {d : Counts // d ∈ daughterDraws n}, f d.val) ≤ partitionError N
      calc
        _ = ∑ d ∈ daughterDraws n, f d := Finset.sum_coe_sort _ f
        _ ≤ partitionError N := cell_partition_failure N hN zL zH hzL hzH _ _ henergy
    · simp

end ResourceLimitedCompetition
