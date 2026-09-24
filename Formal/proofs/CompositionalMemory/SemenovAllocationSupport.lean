import proofs.CompositionalMemory.SemenovInitialInventory
import proofs.CompositionalMemory.SemenovEncoding

namespace CompositionalMemory.Semenov
open MeasureTheory ProbabilityTheory

theorem fair_allocation_support (n : ℕ) : ∀ᵐ k ∂fairAllocationMeasure n,k ≤ n := by
  unfold fairAllocationMeasure
  apply Measure.ae_sum_iff.mpr
  intro k
  apply Measure.ae_smul_measure
  exact (ae_dirac_iff (Set.to_countable _).measurableSet).mpr (Nat.le_of_lt_succ k.isLt)

theorem allocation_partition_support (n : Fin 8 → ℕ) (t : Fin 8 → NNReal) :
    ∀ᵐ z ∂allocationLaw n t,∀ j,(z j).1 ≤ n j := by
  apply ae_all_iff.mpr
  intro j
  have hp : ∀ᵐ z ∂refillAllocationMeasure (n j) (t j),z.1 ≤ n j :=
    (measurePreserving_fst (μ := fairAllocationMeasure (n j)) (ν := poissonMeasure (t j))).quasiMeasurePreserving.ae
      (fair_allocation_support (n j))
  exact (measurePreserving_eval (μ := fun i => refillAllocationMeasure (n i) (t i)) j).quasiMeasurePreserving.ae hp

theorem refilled_coordinate_cap (n : Fin 8 → ℕ) (z : RawAllocation) (B K : ℕ)
    (hp : ∀ j,(z j).1 ≤ n j) (hbudget : (∑ j,n j)+K ≤ B)
    (hfeed : allocationFeedCount z < K) (j : Fin 8) : refilledCounts z j ≤ B := by
  have hn : n j ≤ ∑ i,n i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hf : (z j).2 ≤ allocationFeedCount z := by
    exact Finset.single_le_sum (f := fun i => (z i).2) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hh := hp j
  unfold refilledCounts
  omega

theorem allocation_combined_energy_comparison (n : Fin 8 → ℕ) (t : Fin 8 → NNReal)
    (B K : ℕ) (hK : 0 < K) (hbudget : (∑ j,n j)+K ≤ B)
    (E : (Fin 8 → ℕ) → ℝ) (hE : ∀ n,0 ≤ E n) (rate : ℝ)
    (hm : (∑ j,(t j : ℝ)) ≤ (K : ℝ)/2) :
    ∀ᵐ z ∂allocationLaw n t,
      reactorCombinedEnergy E (∑ j,(t j : ℝ)) rate 0
        (encodeReactor B K (refilledCounts z) (allocationFeedCount z)) ≤
      E (refilledCounts z)+centeredInventory K (∑ j,(t j : ℝ)) rate 0 (allocationFeedCount z) := by
  filter_upwards [allocation_partition_support n t] with z hz
  exact encoded_combined_energy_upper B K hK E (∑ j,(t j : ℝ)) rate 0
    (refilledCounts z) (allocationFeedCount z) (hE _) (fun hc j => refilled_coordinate_cap n z B K hz hbudget hc j)
    (by simpa only [mul_zero,add_zero] using hm)

end CompositionalMemory.Semenov
