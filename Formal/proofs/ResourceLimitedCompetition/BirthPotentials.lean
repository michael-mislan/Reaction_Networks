import proofs.ResourceLimitedCompetition.GlobalSpatial
import proofs.ResourceLimitedCompetition.OuterFailure
import proofs.ResourceLimitedCompetition.GlobalPartition

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy

theorem list_potential_bound (F : TaggedCell → ℝ) (b : ℝ) (cs : List TaggedCell)
    (h : ∀ c ∈ cs, F c ≤ b) : (cs.map F).sum ≤ (cs.length : ℝ)*b := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hc := h c (by simp)
    have ht := ih (fun d hd => h d (by simp [hd]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith only [hc,ht]

theorem cellSpatial_birth (N : ℕ) (zL zH : ℝ) (c : TaggedCell)
    (hm : c.compartment.2=N) (he : cellEnergy zL zH c ≤ 4*innerEnergy) :
    cellSpatial N zL zH c ≤ birthSpatialCeiling N := by
  unfold cellSpatial spatialWeight birthSpatialCeiling
  rw [hm,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left he
    (by unfold localAlpha; positivity : 0 ≤ (N : ℝ)*localAlpha)
  nlinarith only [h]

theorem cellOuter_birth_closed (N : ℕ) (zL zH : ℝ) (c : TaggedCell)
    (he : cellEnergy zL zH c ≤ 4*innerEnergy) :
    cellOuter N zL zH c ≤ Real.exp (4*(N : ℝ)*localAlpha*innerEnergy) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left he
    (by unfold localAlpha; positivity : 0 ≤ (N : ℝ)*localAlpha)
  nlinarith only [h]

theorem initial_chemical_potentials (N M : ℕ) (zL zH : ℝ) (s : PopulationState)
    (hlen : s.live.length=M) (hD : s.divisions=0)
    (hm : ∀ c ∈ s.live, c.compartment.2=N)
    (he : ∀ c ∈ s.live, cellEnergy zL zH c ≤ 4*innerEnergy) :
    potentialSum (cellSpatial N zL zH) s ≤ (M : ℝ)*birthSpatialCeiling N ∧
      potentialSum (cellOuter N zL zH) s+outerReserve N M s.divisions ≤
        7*(M : ℝ)*Real.exp (4*(N : ℝ)*localAlpha*innerEnergy) ∧
      partitionReserve N M s.divisions=3*(M : ℝ)*partitionError N := by
  have hs := list_potential_bound (cellSpatial N zL zH) (birthSpatialCeiling N) s.live
    (fun c hc => cellSpatial_birth N zL zH c (hm c hc) (he c hc))
  have ho := list_potential_bound (cellOuter N zL zH)
    (Real.exp (4*(N : ℝ)*localAlpha*innerEnergy)) s.live
    (fun c hc => cellOuter_birth_closed N zL zH c (he c hc))
  rw [hlen] at hs ho
  refine ⟨hs,?_,?_⟩
  · unfold potentialSum outerReserve
    rw [hD]
    norm_num only [Nat.cast_zero,mul_zero,sub_zero]
    nlinarith only [ho]
  · simp [partitionReserve,hD]

end ResourceLimitedCompetition
