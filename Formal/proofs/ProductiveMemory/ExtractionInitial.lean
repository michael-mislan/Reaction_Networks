import proofs.ProductiveMemory.ExtractionOuterProbability
import proofs.ProductiveMemory.ExtractionSpatialProbability

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
noncomputable section
set_option Elab.async false

def ProductiveReadyPopulation (N M : ℕ) (rho zL zH : ℝ) (s : ProductiveState) : Prop :=
  s.population.live.length=M ∧ s.population.divisions=0 ∧
    s.population.resource=4*membrane s.population.live ∧ ValidVolumes N s.population ∧
    (∀ c ∈ s.population.live, extractionCellEnergy rho zL zH c ≤ readyLevel) ∧ s.collected=0

theorem productive_ready_mem_domain (N M J : ℕ) (hN : 1 ≤ N) (hM : 0 < M) (hJ : 0 < J)
    (rho zL zH : ℝ) (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (s : ProductiveState) (h : ProductiveReadyPopulation N M rho zL zH s) :
    s ∈ productiveActiveDomain N M (membrane s.population.live) J rho zL zH := by
  obtain ⟨hlen,hD,hQ,hv,he,hE⟩ := h
  have hW := membrane_upper N s.population.live (fun c hc => (hv c hc).2.le)
  have hlo := membrane_lower N s.population.live (fun c hc => (hv c hc).1)
  rw [hlen] at hW hlo
  have hpos : 0 < membrane s.population.live := (Nat.mul_pos (by omega) hM).trans_le hlo
  apply productive_active_mem N M (membrane s.population.live) J hN hW rho zL zH hr hzL hzH s
  refine ⟨?_,?_,?_,?_,hv,?_,?_⟩
  · rw [hQ]; omega
  · rw [hQ]
  · rw [hQ]; omega
  · omega
  · intro c hc
    exact (he c hc).trans_lt (by norm_num [readyLevel,outerLevel])
  · omega

theorem extraction_cell_spatial_ready (N : ℕ) (rho zL zH : ℝ) (c : TaggedCell)
    (hm : c.compartment.2 ≤ 2*N) (he : extractionCellEnergy rho zL zH c ≤ readyLevel) :
    extractionCellSpatial N rho zL zH c ≤ Real.exp ((N : ℝ)*localAlpha*readyLevel) := by
  unfold extractionCellSpatial spatialWeight
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hmR : (c.compartment.2 : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast hm
  have h := mul_le_mul_of_nonneg_left he
    (by unfold localAlpha; positivity : 0 ≤ (N : ℝ)*localAlpha)
  nlinarith only [h,hmR]

theorem productive_initial_spatial_bound (N M : ℕ) (rho zL zH : ℝ) (s : ProductiveState)
    (h : ProductiveReadyPopulation N M rho zL zH s) :
    potentialSum (extractionCellSpatial N rho zL zH) s.population ≤
      (M : ℝ)*Real.exp ((N : ℝ)*localAlpha*readyLevel) := by
  have hp (cs : List TaggedCell)
      (hm : ∀ c ∈ cs, c.compartment.2 ≤ 2*N)
      (he : ∀ c ∈ cs, extractionCellEnergy rho zL zH c ≤ readyLevel) :
      (cs.map (extractionCellSpatial N rho zL zH)).sum ≤
        (cs.length : ℝ)*Real.exp ((N : ℝ)*localAlpha*readyLevel) := by
    induction cs with
    | nil => simp
    | cons c cs ih =>
      have hc := extraction_cell_spatial_ready N rho zL zH c (hm c (by simp)) (he c (by simp))
      have ht := ih (fun d hd => hm d (by simp [hd])) (fun d hd => he d (by simp [hd]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      nlinarith only [hc,ht]
  obtain ⟨hlen,_,_,hv,he,_⟩ := h
  have hb := hp s.population.live (fun c hc => (hv c hc).2.le) he
  rw [hlen] at hb
  exact hb

theorem extraction_cell_outer_ready (N : ℕ) (rho zL zH : ℝ) (c : TaggedCell)
    (he : extractionCellEnergy rho zL zH c ≤ readyLevel) :
    extractionCellOuter N rho zL zH c ≤ Real.exp ((N : ℝ)*localAlpha*readyLevel) := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left he (by unfold localAlpha; positivity)

theorem productive_initial_outer_bound (N M : ℕ) (rho zL zH : ℝ) (s : ProductiveState)
    (h : ProductiveReadyPopulation N M rho zL zH s) :
    potentialSum (extractionCellOuter N rho zL zH) s.population ≤
      (M : ℝ)*Real.exp ((N : ℝ)*localAlpha*readyLevel) := by
  have hp (cs : List TaggedCell)
      (he : ∀ c ∈ cs, extractionCellEnergy rho zL zH c ≤ readyLevel) :
      (cs.map (extractionCellOuter N rho zL zH)).sum ≤
        (cs.length : ℝ)*Real.exp ((N : ℝ)*localAlpha*readyLevel) := by
    induction cs with
    | nil => simp
    | cons c cs ih =>
      have hc := extraction_cell_outer_ready N rho zL zH c (he c (by simp))
      have ht := ih (fun d hd => he d (by simp [hd]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      nlinarith only [hc,ht]
  obtain ⟨hlen,_,_,_,he,_⟩ := h
  have hb := hp s.population.live he
  rw [hlen] at hb
  exact hb

theorem productive_initial_outer_with_reserve (N M : ℕ) (rho zL zH : ℝ) (s : ProductiveState)
    (h : ProductiveReadyPopulation N M rho zL zH s) :
    potentialSum (extractionCellOuter N rho zL zH) s.population+productiveOuterReserve N M s.population.divisions ≤
      (M : ℝ)*Real.exp ((N : ℝ)*localAlpha*readyLevel)+
        14*(M : ℝ)*Real.exp (4*(N : ℝ)*localAlpha*readyLevel) := by
  have hb := productive_initial_outer_bound N M rho zL zH s h
  simpa only [productiveOuterReserve,h.2.1,Nat.cast_zero,mul_zero,sub_zero] using
    add_le_add hb (le_refl (14*(M : ℝ)*Real.exp (4*(N : ℝ)*localAlpha*readyLevel)))

end
end ProductiveMemory
