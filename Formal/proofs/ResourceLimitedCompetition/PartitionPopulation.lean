import proofs.ResourceLimitedCompetition.PartitionEvent

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy Set

noncomputable def partitionReserve (N M D : ℕ) : ℝ :=
  (3*(M : ℝ)-(D : ℝ))*partitionError N

theorem partitionReserve_nonneg (N M D : ℕ) (hD : D ≤ 3*M) :
    0 ≤ partitionReserve N M D := by
  have hd : (D : ℝ) ≤ 3*(M : ℝ) := by exact_mod_cast hD
  exact mul_nonneg (sub_nonneg.mpr hd) (partitionError_nonneg N)

noncomputable def partitionPopulationObservable (N M : ℕ) (zL zH : ℝ)
    (D : Finset PopulationState) : StoppedPopulation D → ℝ
  | .inl s => partitionReserve N M s.val.divisions
  | .inr e => partitionFlag N M zL zH e

theorem partitionFlag_nonneg (N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (e : PopulationEvent D) : 0 ≤ partitionFlag N M zL zH e := by
  unfold partitionFlag
  split_ifs <;> norm_num

theorem event_divisions_le_succ (N : ℕ) (D : Finset PopulationState) (e : PopulationEvent D) :
    (eventOutcome N e).divisions ≤ e.1.val.divisions+1 := by
  rcases e with ⟨s,i,ch⟩
  cases ch with
  | inl r => exact Nat.le_succ _
  | inr d => simp only [eventOutcome,growthAt]; split_ifs <;> dsimp only <;> omega

theorem partition_next_le (N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (s : ActiveState D) (hD : s.val.divisions < 3*M) (e : CellEvent s.val) :
    partitionPopulationObservable N M zL zH D
      (stoppedNext N M zL zH D (.inl s) ⟨s,e⟩) ≤
      partitionReserve N M (eventOutcome N ⟨s,e⟩).divisions+partitionFlag N M zL zH ⟨s,e⟩ := by
  classical
  have hn := partitionReserve_nonneg N M (eventOutcome N ⟨s,e⟩).divisions
    ((event_divisions_le_succ N D ⟨s,e⟩).trans (by change s.val.divisions+1 ≤ 3*M; omega))
  simp only [stoppedNext,if_true]
  split_ifs
  · exact le_add_of_nonneg_right (partitionFlag_nonneg N M zL zH D ⟨s,e⟩)
  · exact le_add_of_nonneg_left hn
  · exact le_add_of_nonneg_left hn

theorem weighted_partition_compensation (n : Counts) (a b : ℝ) (ha : 0 ≤ a)
    (f : {d : Counts // d ∈ daughterDraws n} → ℝ)
    (hf : (∑ d, daughterWeight n d.val*f d) ≤ b) :
    (∑ d, a*daughterWeight n d.val*(f d-b)) ≤ 0 := by
  classical
  have hid : (∑ d, a*daughterWeight n d.val*(f d-b)) =
      a*(∑ d, daughterWeight n d.val*f d)-a*b := by
    rw [Finset.mul_sum,← daughter_constant_sum n a b,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [hid]
  exact sub_nonpos.mpr (mul_le_mul_of_nonneg_left hf ha)

theorem growth_partition_compensated (γ : ℝ) (hγ : 0 ≤ γ) (Ω N M : ℕ) (hN : 0 < N)
    (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (D : Finset PopulationState) (s : ActiveState D) (i : Fin s.val.live.length) :
    (∑ d : {d : Counts // d ∈ daughterDraws
        (nextCompartment (selectedCell s.val i).compartment (.inr ())).1},
      eventRate γ Ω ⟨s,i,.inr d⟩*
        (partitionReserve N M (eventOutcome N ⟨s,i,.inr d⟩).divisions+
          partitionFlag N M zL zH ⟨s,i,.inr d⟩-partitionReserve N M s.val.divisions)) ≤ 0 := by
  classical
  have ha : 0 ≤ propensity (resourceCoefficient γ s.val.resource Ω)
      (selectedCell s.val i).compartment (.inr ()) := by
    apply propensity_nonneg
    unfold resourceCoefficient
    positivity
  have h := weighted_partition_compensation _ _ _ ha
    (fun d => partitionFlag N M zL zH ⟨s,i,.inr d⟩)
    (growth_partition_average N M hN zL zH hzL hzH D s i)
  convert h using 1
  apply Finset.sum_congr rfl
  intro d _
  simp only [eventRate,eventOutcome,growthAt]
  split_ifs <;> simp only [partitionReserve,Nat.cast_add,Nat.cast_one] <;> ring

end ResourceLimitedCompetition
