import proofs.InheritedCellAssay.Resolution

namespace InheritedCellAssay
open scoped BigOperators

/-- Real mixing weights permit arbitrary probability laws, not only rational ones. -/
noncomputable def realAssayRisk (w : Fin 31 → ℝ) : ℝ :=
  ∑ k, w k * (actualSisterRisk 30 k : ℝ)

noncomputable def realPopulationTarget (w : Fin 31 → ℝ) : ℝ :=
  (∑ k, w k * (sourceExpectation k (fun s =>
    (((sisterEndpoint 30 k s).filter id).length : ℚ)) : ℝ)) /
  (∑ k, w k * (sourceExpectation k (fun s =>
    ((sisterEndpoint 30 k s).length : ℚ)) : ℝ))

theorem real_population_target (w : Fin 31 → ℝ) (hn : ∑ k, w k = 1) :
    realPopulationTarget w = 8/9 := by
  unfold realPopulationTarget
  have hr (k : Fin 31) := sister_mean_response 30 k (by omega)
  have hc (k : Fin 31) := sister_mean_count 30 k (by omega)
  simp_rw [hr, hc]
  rw [← Finset.sum_mul, ← Finset.sum_mul, hn]
  norm_num

theorem real_risk_bound (w : Fin 31 → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hn : ∑ k, w k = 1) :
    realAssayRisk w ≤ 2061197/67108864 := by
  have hb (k : Fin 31) : (actualSisterRisk 30 k : ℝ) ≤ 2061197/67108864 := by
    have h := conditional_thirty_bound k
    rw [← sister_risk_transport 30 k (by omega)] at h
    have hh : (actualSisterRisk 30 k : ℝ) ≤ ((2061197/67108864 : ℚ) : ℝ) :=
      Rat.cast_le.mpr h
    norm_num at hh ⊢
    exact hh
  calc
    realAssayRisk w ≤ ∑ k, w k * (2061197/67108864) := by
      exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hb k) (hw k))
    _ = 2061197/67108864 := by rw [← Finset.sum_mul, hn, one_mul]

/-- Final finite-assay result for every real probability distribution of pair types. -/
theorem real_resolution (w : Fin 31 → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hn : ∑ k, w k = 1) :
    realPopulationTarget w = 8/9 ∧
    realAssayRisk w ≤ 2061197/67108864 ∧ realAssayRisk w < 1/20 ∧
    (∀ k : Fin 31, ∀ s : Finset (Fin k.val), 0 < (sisterEndpoint 30 k s).length) := by
  exact ⟨real_population_target w hn, real_risk_bound w hw hn,
    (real_risk_bound w hw hn).trans_lt (by norm_num), sister_endpoint_nonempty⟩

end InheritedCellAssay
