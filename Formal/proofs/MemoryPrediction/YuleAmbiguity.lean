import proofs.MemoryPrediction.YuleSource
import proofs.MemoryPrediction.SharedEnvironment

namespace MemoryPrediction
noncomputable section
open LowFounderPrediction MeasureTheory RandomViability

/-- Independent Bernoulli founder types give initial masses 1/4,1/2,1/4. -/
def independentSource : Measure State :=
  (1/4 : NNReal) • law yuleRates (2,0) yuleHorizon +
  (1/2 : NNReal) • law yuleRates (1,1) yuleHorizon +
  (1/4 : NNReal) • law yuleRates (0,2) yuleHorizon

/-- One Bernoulli well state gives all-slow or all-fast initial populations. -/
def sharedSource : Measure State :=
  (1/2 : NNReal) • law yuleRates (2,0) yuleHorizon +
  (1/2 : NNReal) • law yuleRates (0,2) yuleHorizon

instance independentSource_finite : IsFiniteMeasure independentSource := by
  unfold independentSource
  infer_instance
instance sharedSource_finite : IsFiniteMeasure sharedSource := by
  unfold sharedSource
  infer_instance

instance independentSource_probability : IsProbabilityMeasure independentSource := by
  constructor
  norm_num [independentSource,Measure.add_apply,Measure.smul_apply]
  have h := congrArg (fun x : NNReal => (x : ENNReal))
    (show (4 : NNReal)⁻¹+2⁻¹+4⁻¹=1 by norm_num)
  simpa only [ENNReal.coe_add,ENNReal.coe_inv (by norm_num : (4 : NNReal) ≠ 0),
    ENNReal.coe_inv_two,ENNReal.coe_ofNat,ENNReal.coe_one] using h

instance sharedSource_probability : IsProbabilityMeasure sharedSource := by
  constructor
  simp [sharedSource,Measure.add_apply,Measure.smul_apply]
  exact ENNReal.inv_two_add_inv_two

def sourceCDF (μ : Measure State) (k : ℕ) : ℝ := μ.real {x | totalCount x ≤ k}

theorem source_cdf_formula (k : ℕ) (hk : 2 ≤ k) (hk7 : k ≤ 7) :
    sourceCDF independentSource k =
      (1/4)*yuleAtHalf ⟨k-2,by omega⟩ 0 +
      (1/2)*yuleAtHalf ⟨k-1,by omega⟩ 1 +
      (1/4)*yuleAtHalf ⟨k,by omega⟩ 2 ∧
    sourceCDF sharedSource k =
      (1/2)*yuleAtHalf ⟨k-2,by omega⟩ 0 +
      (1/2)*yuleAtHalf ⟨k,by omega⟩ 2 := by
  have h0 := yule_source_exact 2 0 (by omega) ⟨k-2,by omega⟩ yuleHorizon
  have h1 := yule_source_exact 1 1 (by omega) ⟨k-1,by omega⟩ yuleHorizon
  have h2 := yule_source_exact 0 2 (by omega) ⟨k,by omega⟩ yuleHorizon
  have hsub2 : 2+(k-2)=k := by omega
  have hsub1 : 1+(k-1)=k := by omega
  simp only [hsub2,hsub1,zero_add,yule_value_half] at h0 h1 h2
  constructor
  · unfold sourceCDF independentSource
    rw [measureReal_add_apply,measureReal_add_apply]
    simp only [measureReal_nnreal_smul_apply,h0,h1,h2]
    norm_num
    rfl
  · unfold sourceCDF sharedSource
    rw [measureReal_add_apply]
    simp only [measureReal_nnreal_smul_apply,h0,h2]
    norm_num
    rfl

theorem chronological_endpoint_table :
    sourceCDF independentSource 2 = 9/16 ∧ sourceCDF sharedSource 2 = 5/8 ∧
    sourceCDF independentSource 5 = 59/64 ∧ sourceCDF independentSource 6 = 245/256 ∧
    sourceCDF sharedSource 6 = 121/128 ∧ sourceCDF sharedSource 7 = 31/32 := by
  have h2 := source_cdf_formula 2 (by norm_num) (by norm_num)
  have h5 := source_cdf_formula 5 (by norm_num) (by norm_num)
  have h6 := source_cdf_formula 6 (by norm_num) (by norm_num)
  have h7 := source_cdf_formula 7 (by norm_num) (by norm_num)
  norm_num [yuleAtHalf,yuleCoeff,Fin.sum_univ_succ,
    Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail] at h2 h5 h6 h7
  exact ⟨h2.1,h2.2,h5.1,h6.1,h6.2,h7.2⟩

theorem chronological_minimal_endpoints :
    (19/20 : ℝ) ≤ sourceCDF independentSource 6 ∧
    (∀ k < 6, sourceCDF independentSource k < 19/20) ∧
    (19/20 : ℝ) ≤ sourceCDF sharedSource 7 ∧
    (∀ k < 7, sourceCDF sharedSource k < 19/20) := by
  rcases chronological_endpoint_table with ⟨_,_,h5,h6,hw6,hw7⟩
  refine ⟨by rw [h6]; norm_num, ?_, by rw [hw7]; norm_num, ?_⟩
  · intro k hk
    have h : sourceCDF independentSource k ≤ sourceCDF independentSource 5 :=
      measureReal_mono (fun x hx => Nat.le_trans hx (by omega)) (by finiteness)
    rw [h5] at h
    linarith
  · intro k hk
    have h : sourceCDF sharedSource k ≤ sourceCDF sharedSource 6 :=
      measureReal_mono (fun x hx => Nat.le_trans hx (by omega)) (by finiteness)
    rw [hw6] at h
    linarith

/-- The full chronological trace law of a single founder is literally the same
latent mixture for independent-founder and shared-well preparations. -/
def oneFounderTrace :=
  familyMixture
    (jumpTrajectoryLaw (1,0) next (rate yuleRates) (rate_nonneg yuleRates) (total_pos yuleRates))
    (jumpTrajectoryLaw (0,1) next (rate yuleRates) (rate_nonneg yuleRates) (total_pos yuleRates))

/-- The observation may retain the entire chronological trace. The two
preparation protocols have identical laws for every such single-founder map. -/
theorem chronological_single_observation_equal {O : Type*} [MeasurableSpace O]
    (observe : (ℕ → JumpState State (Fin 7)) → O) :
    ((independentFamilies
      (jumpTrajectoryLaw (1,0) next (rate yuleRates) (rate_nonneg yuleRates) (total_pos yuleRates))
      (jumpTrajectoryLaw (0,1) next (rate yuleRates) (rate_nonneg yuleRates) (total_pos yuleRates))).map
      Prod.fst).map observe =
    ((sharedFamilies
      (jumpTrajectoryLaw (1,0) next (rate yuleRates) (rate_nonneg yuleRates) (total_pos yuleRates))
      (jumpTrajectoryLaw (0,1) next (rate yuleRates) (rate_nonneg yuleRates) (total_pos yuleRates))).map
      Prod.fst).map observe := by
  exact single_observation_law_equal _ _ observe

end
end MemoryPrediction
