import proofs.ResourceLimitedCompetition.CellPartition
import proofs.ProductiveMemory.ExtractionStoppedPopulation
import proofs.ProductiveMemory.ExtractionPartition

namespace ProductiveMemory
noncomputable section
set_option Elab.async false
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set

abbrev extractionGoodBirths (N : ℕ) (rho zL zH : ℝ) (tag : Bool) (n d : Counts) : Prop :=
  extractionCellEnergy rho zL zH ⟨tag,(d,N)⟩ < 4*readyLevel ∧
    extractionCellEnergy rho zL zH ⟨tag,((fun j => n j-d j),N)⟩ < 4*readyLevel

theorem extraction_cell_partition_failure (N : ℕ) (hN : 0 < N) (rho zL zH : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (tag : Bool) (n : Counts)
    (hp : extractionCellEnergy rho zL zH ⟨tag,(n,2*N)⟩ ≤ 2*readyLevel) :
    (∑ d ∈ daughterDraws n, daughterWeight n d*
      (if ¬extractionGoodBirths N rho zL zH tag n d then 1 else 0)) ≤ partitionError N := by
  classical
  cases tag with
  | false => exact low_extraction_partition_failure rho zL hr hzL n N hN hp
  | true => exact high_extraction_partition_failure rho zH hr hzH n N hN hp

noncomputable def productivePartitionFlag (N W0 J : ℕ) (rho zL zH : ℝ) {D : Finset ProductiveState}
    (e : ProductivePopulationEvent D) : ℝ := if productiveReason N W0 J rho zL zH e=.partition then 1 else 0

theorem productive_resident_partition_flag (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState)
    (s : ProductiveActive D) (i : Fin s.val.population.live.length) (r : Fin 13) :
    productivePartitionFlag N W0 J rho zL zH ⟨s,.inl ⟨i,.inl r⟩⟩=0 := by
  classical
  simp only [productivePartitionFlag,productiveReason]
  split_ifs <;> simp_all

theorem productive_extraction_partition_flag (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState)
    (s : ProductiveActive D) (i : Fin s.val.population.live.length) :
    productivePartitionFlag N W0 J rho zL zH ⟨s,.inr i⟩=0 := by
  classical
  simp only [productivePartitionFlag,productiveReason]
  split_ifs <;> simp_all

theorem productive_growth_partition_flag (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState)
    (s : ProductiveActive D) (i : Fin s.val.population.live.length)
    (d : {d : Counts // d ∈ daughterDraws
      (nextCompartment (selectedCell s.val.population i).compartment (.inr ())).1}) :
    productivePartitionFlag N W0 J rho zL zH ⟨s,.inl ⟨i,.inr d⟩⟩ =
      if (8*readyLevel) ≤ extractionCellEnergy rho zL zH
        ⟨(selectedCell s.val.population i).high,nextCompartment (selectedCell s.val.population i).compartment (.inr ())⟩
      then 0 else
      if (nextCompartment (selectedCell s.val.population i).compartment (.inr ())).2=2*N then
        if 2*readyLevel < extractionCellEnergy rho zL zH
          ⟨(selectedCell s.val.population i).high,nextCompartment (selectedCell s.val.population i).compartment (.inr ())⟩
        then 0 else if ¬extractionGoodBirths N rho zL zH (selectedCell s.val.population i).high
          (nextCompartment (selectedCell s.val.population i).compartment (.inr ())).1 d.val then 1 else 0
      else 0 := by
  classical
  simp only [productivePartitionFlag,productiveReason,extractionGoodBirths]
  split_ifs <;> simp_all

theorem productive_growth_partition_average (N W0 J : ℕ) (hN : 0 < N) (rho zL zH : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (D : Finset ProductiveState) (s : ProductiveActive D) (i : Fin s.val.population.live.length) :
    (∑ d : {d : Counts // d ∈ daughterDraws
        (nextCompartment (selectedCell s.val.population i).compartment (.inr ())).1},
      daughterWeight (nextCompartment (selectedCell s.val.population i).compartment (.inr ())).1 d.val*
        productivePartitionFlag N W0 J rho zL zH ⟨s,.inl ⟨i,.inr d⟩⟩) ≤
      if (nextCompartment (selectedCell s.val.population i).compartment (.inr ())).2=2*N
        then partitionError N else 0 := by
  classical
  simp only [productive_growth_partition_flag]
  by_cases ho : (8*readyLevel) ≤ extractionCellEnergy rho zL zH
      ⟨(selectedCell s.val.population i).high,nextCompartment (selectedCell s.val.population i).compartment (.inr ())⟩
  · simp only [ho,if_true,mul_zero,Finset.sum_const_zero]
    split_ifs
    · exact partitionError_nonneg N
    · exact le_rfl
  · simp only [ho,if_false]
    split_ifs with hm he
    · simpa using partitionError_nonneg N
    · have hp : ((nextCompartment (selectedCell s.val.population i).compartment (.inr ())).1,2*N)=
          nextCompartment (selectedCell s.val.population i).compartment (.inr ()) := by rw [← hm]
      have henergy : extractionCellEnergy rho zL zH
          ⟨(selectedCell s.val.population i).high,
            ((nextCompartment (selectedCell s.val.population i).compartment (.inr ())).1,2*N)⟩ ≤ 2*readyLevel := by
        rw [hp]
        exact le_of_not_gt he
      let n := (nextCompartment (selectedCell s.val.population i).compartment (.inr ())).1
      let f : Counts → ℝ := fun d => daughterWeight n d*
        (if ¬extractionGoodBirths N rho zL zH (selectedCell s.val.population i).high n d then 1 else 0)
      change (∑ d : {d : Counts // d ∈ daughterDraws n}, f d.val) ≤ partitionError N
      calc
        _ = ∑ d ∈ daughterDraws n, f d := Finset.sum_coe_sort _ f
        _ ≤ partitionError N := extraction_cell_partition_failure N hN rho zL zH hr hzL hzH _ _ henergy
    · simp

end
end ProductiveMemory
