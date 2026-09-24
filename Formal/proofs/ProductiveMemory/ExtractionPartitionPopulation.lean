import proofs.ProductiveMemory.ExtractionPartitionEvent
import proofs.ProductiveMemory.ExtractionBatchDomain
import proofs.ResourceLimitedCompetition.PartitionPopulation

namespace ProductiveMemory
noncomputable section
set_option Elab.async false
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set

noncomputable def productivePartitionReserve (N M D : ℕ) : ℝ :=
  (7*(M : ℝ)-(D : ℝ))*partitionError N

theorem productivePartitionReserve_nonneg (N M D : ℕ) (hD : D ≤ 7*M) :
    0 ≤ productivePartitionReserve N M D := by
  have hd : (D : ℝ) ≤ 7*(M : ℝ) := by exact_mod_cast hD
  exact mul_nonneg (sub_nonneg.mpr hd) (partitionError_nonneg N)

noncomputable def productivePartitionPopulationObservable (N M W0 J : ℕ) (rho zL zH : ℝ)
    (D : Finset ProductiveState) : ProductiveStopped D → ℝ
  | .inl s => productivePartitionReserve N M s.val.population.divisions
  | .inr e => productivePartitionFlag N W0 J rho zL zH e

theorem productivePartitionFlag_nonneg (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState)
    (e : ProductivePopulationEvent D) : 0 ≤ productivePartitionFlag N W0 J rho zL zH e := by
  unfold productivePartitionFlag
  split_ifs <;> norm_num

theorem productive_event_divisions_le_succ (N : ℕ) (D : Finset ProductiveState) (e : ProductivePopulationEvent D) :
    (productiveOutcome N e.1.val e.2).population.divisions ≤ e.1.val.population.divisions+1 := by
  rcases e with ⟨s,e⟩
  cases e with
  | inr i => exact Nat.le_succ _
  | inl e =>
    rcases e with ⟨i,r | d⟩
    · exact Nat.le_succ _
    · simp only [productiveOutcome,growthAt]; split_ifs <;> dsimp only <;> omega

theorem productive_active_reserve (N M W0 J : ℕ) (hN : 0 < N) (hW : W0 ≤ 2*N*M)
    (rho zL zH : ℝ) (s : ProductiveActive (productiveActiveDomain N M W0 J rho zL zH)) :
    s.val.population.divisions < 7*M := by
  have hs := productive_active_safe N M W0 J rho zL zH s.val s.property
  exact SerialTransferSelection.phase_batch_division_reserve N M W0 hN hW s.val.population hs.2.2.2.2.1
    hs.2.2.1 hs.1 hs.2.2.2.1

theorem productive_partition_next_le (N M W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState)
    (s : ProductiveActive D) (hD : s.val.population.divisions < 7*M) (e : ProductiveEvent s.val) :
    productivePartitionPopulationObservable N M W0 J rho zL zH D
      (productiveStoppedNext N W0 J rho zL zH D (.inl s) ⟨s,e⟩) ≤
      productivePartitionReserve N M (productiveOutcome N s.val e).population.divisions+productivePartitionFlag N W0 J rho zL zH ⟨s,e⟩ := by
  classical
  have hn := productivePartitionReserve_nonneg N M (productiveOutcome N s.val e).population.divisions
    ((productive_event_divisions_le_succ N D ⟨s,e⟩).trans (by change s.val.population.divisions+1 ≤ 7*M; omega))
  simp only [productiveStoppedNext,if_true]
  split_ifs
  · exact le_add_of_nonneg_right (productivePartitionFlag_nonneg N W0 J rho zL zH D ⟨s,e⟩)
  · exact le_add_of_nonneg_left hn
  · exact le_add_of_nonneg_left hn

theorem productive_growth_partition_compensated (γ : ℝ) (hγ : 0 ≤ γ) (Ω N M W0 J : ℕ) (hN : 0 < N)
    (rho zL zH : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (D : Finset ProductiveState) (s : ProductiveActive D) (i : Fin s.val.population.live.length) :
    (∑ d : {d : Counts // d ∈ daughterDraws
        (nextCompartment (selectedCell s.val.population i).compartment (.inr ())).1},
      productiveRate rho γ Ω s.val (.inl ⟨i,.inr d⟩)*
        (productivePartitionReserve N M (productiveOutcome N s.val (.inl ⟨i,.inr d⟩)).population.divisions+
          productivePartitionFlag N W0 J rho zL zH ⟨s,.inl ⟨i,.inr d⟩⟩-productivePartitionReserve N M s.val.population.divisions)) ≤ 0 := by
  classical
  have ha : 0 ≤ propensity (resourceCoefficient γ s.val.population.resource Ω)
      (selectedCell s.val.population i).compartment (.inr ()) := by
    apply propensity_nonneg
    unfold resourceCoefficient
    positivity
  have h := weighted_partition_compensation _ _ _ ha
    (fun d => productivePartitionFlag N W0 J rho zL zH ⟨s,.inl ⟨i,.inr d⟩⟩)
    (productive_growth_partition_average N W0 J hN rho zL zH hr hzL hzH D s i)
  convert h using 1
  apply Finset.sum_congr rfl
  intro d _
  simp only [productiveRate,productiveOutcome,growthAt]
  split_ifs <;> simp only [productivePartitionReserve,Nat.cast_add,Nat.cast_one] <;> ring

end
end ProductiveMemory
