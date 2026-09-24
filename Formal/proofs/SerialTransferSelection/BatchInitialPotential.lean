import proofs.SerialTransferSelection.BatchDomain
import proofs.ResourceLimitedCompetition.CellSpatial

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

theorem cellSpatial_ready (N : ℕ) (zL zH : ℝ) (c : TaggedCell)
    (hm : c.compartment.2 ≤ 2*N) (he : cellEnergy zL zH c ≤ innerEnergy) :
    cellSpatial N zL zH c ≤ Real.exp ((N : ℝ)*localAlpha*innerEnergy) := by
  unfold cellSpatial spatialWeight
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hmR : (c.compartment.2 : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast hm
  have h := mul_le_mul_of_nonneg_left he
    (by unfold localAlpha; positivity : 0 ≤ (N : ℝ)*localAlpha)
  nlinarith only [h,hmR]

theorem phase_initial_spatial_bound (N M : ℕ) (zL zH : ℝ) (s : PopulationState)
    (h : PhaseReadyPopulation N M zL zH s) :
    potentialSum (cellSpatial N zL zH) s ≤
      (M : ℝ)*Real.exp ((N : ℝ)*localAlpha*innerEnergy) := by
  have hp (cs : List TaggedCell)
      (hm : ∀ c ∈ cs, c.compartment.2 ≤ 2*N)
      (he : ∀ c ∈ cs, cellEnergy zL zH c ≤ innerEnergy) :
      (cs.map (cellSpatial N zL zH)).sum ≤
        (cs.length : ℝ)*Real.exp ((N : ℝ)*localAlpha*innerEnergy) := by
    induction cs with
    | nil => simp
    | cons c cs ih =>
      have hc := cellSpatial_ready N zL zH c (hm c (by simp)) (he c (by simp))
      have ht := ih (fun d hd => hm d (by simp [hd])) (fun d hd => he d (by simp [hd]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      nlinarith only [hc,ht]
  obtain ⟨hlen,_,_,hv,he⟩ := h
  have hb := hp s.live (fun c hc => (hv c hc).2.le) he
  rw [hlen] at hb
  exact hb

end SerialTransferSelection
