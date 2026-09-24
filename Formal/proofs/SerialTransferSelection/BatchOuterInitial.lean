import proofs.SerialTransferSelection.BatchOuterProbability

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

theorem cellOuter_ready (N : ℕ) (zL zH : ℝ) (c : TaggedCell)
    (he : cellEnergy zL zH c ≤ innerEnergy) :
    cellOuter N zL zH c ≤ Real.exp ((N : ℝ)*localAlpha*innerEnergy) := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left he (by unfold localAlpha; positivity)

theorem phase_initial_outer_bound (N M : ℕ) (zL zH : ℝ) (s : PopulationState)
    (h : PhaseReadyPopulation N M zL zH s) :
    potentialSum (cellOuter N zL zH) s ≤
      (M : ℝ)*Real.exp ((N : ℝ)*localAlpha*innerEnergy) := by
  have hp (cs : List TaggedCell)
      (he : ∀ c ∈ cs, cellEnergy zL zH c ≤ innerEnergy) :
      (cs.map (cellOuter N zL zH)).sum ≤
        (cs.length : ℝ)*Real.exp ((N : ℝ)*localAlpha*innerEnergy) := by
    induction cs with
    | nil => simp
    | cons c cs ih =>
      have hc := cellOuter_ready N zL zH c (he c (by simp))
      have ht := ih (fun d hd => he d (by simp [hd]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      nlinarith only [hc,ht]
  obtain ⟨hlen,_,_,_,he⟩ := h
  have hb := hp s.live he
  rw [hlen] at hb
  exact hb

theorem phase_initial_outer_with_reserve (N M : ℕ) (zL zH : ℝ) (s : PopulationState)
    (h : PhaseReadyPopulation N M zL zH s) :
    potentialSum (cellOuter N zL zH) s+phaseOuterReserve N M s.divisions ≤
      (M : ℝ)*Real.exp ((N : ℝ)*localAlpha*innerEnergy)+
        14*(M : ℝ)*Real.exp (4*(N : ℝ)*localAlpha*innerEnergy) := by
  have hb := phase_initial_outer_bound N M zL zH s h
  simpa only [phaseOuterReserve,h.2.1,Nat.cast_zero,mul_zero,sub_zero] using
    add_le_add hb (le_refl (14*(M : ℝ)*Real.exp (4*(N : ℝ)*localAlpha*innerEnergy)))

end SerialTransferSelection
