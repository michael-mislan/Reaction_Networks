import proofs.RAF.Frankl.SupplierWeightedCounting

namespace RAF.Frankl
open RAF
variable {M R : Type*} [DecidableEq M] [Fintype R] [DecidableEq R]

theorem local_supplier_actual_fibre_average (Q : CRS M R) (C : Catalysis M R)
    (U : Finset R) (rank : R → ℕ) (hrank : InternalSubstrateRank Q U rank)
    (hU : SupplierCore Q C U) (T : Finset R) :
    ((fixedFamily Q C).filter (fun W => W \ U = T)).card * Fintype.card {r // r ∈ U} ≤
      2 * ∑ W ∈ (fixedFamily Q C).filter (fun W => W \ U = T), (toRestricted U W).card := by
  classical
  by_cases hT : Disjoint T U
  · have hh := localSupplierFibre_average Q C U rank hrank T hU
    rw [← core_fibre_image Q C U T hT] at hh
    rw [Finset.card_image_iff.mpr (core_restrict_injOn Q C U T),
      Finset.sum_image (core_restrict_injOn Q C U T)] at hh
    exact hh
  · have he : (fixedFamily Q C).filter (fun W => W \ U = T) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro W hw
      apply hT
      rw [← (Finset.mem_filter.mp hw).2]
      exact Finset.sdiff_disjoint
    simp [he]

/-- Unnormalized source-level bounded-distortion theorem. Dividing by positive
total mass gives the probability and expectation statements. -/
theorem local_supplier_bounded_weights (Q : CRS M R) (C : Catalysis M R)
    (U : Finset R) (rank : R → ℕ) (hrank : InternalSubstrateRank Q U rank)
    (hU : SupplierCore Q C U) (w : Finset R → ℝ) (lo : Finset R → ℝ) (k : ℝ)
    (hlo : ∀ T, 0 ≤ lo T) (hk : 0 ≤ k)
    (hw : ∀ W ∈ fixedFamily Q C, lo (W \ U) ≤ w W ∧ w W ≤ k*lo (W \ U)) :
    (U.card : ℝ)*(∑ W ∈ fixedFamily Q C, w W) ≤
      (1+k)*∑ W ∈ fixedFamily Q C, w W*(toRestricted U W).card ∧
    ∃ r ∈ U, (∑ W ∈ fixedFamily Q C, w W) ≤
      (1+k)*∑ W ∈ (fixedFamily Q C).filter (fun W => r ∈ W), w W := by
  classical
  have h := weighted_fibre_aggregation (fixedFamily Q C) (fun W => W \ U)
    (fun W => ((toRestricted U W).card : ℝ)) w (Fintype.card {r // r ∈ U}) k lo hlo hk ?_ hw ?_
  · refine ⟨by simpa using h,?_⟩
    have hn : Nonempty {r // r ∈ U} := by
      obtain ⟨r,hr⟩ := hU.1
      exact ⟨⟨r,hr⟩⟩
    letI := hn
    obtain ⟨r,hr⟩ := weighted_coordinate_witness (fixedFamily Q C) (toRestricted U) w k h
    exact ⟨r.1,r.2,by simpa using hr⟩
  · intro W _
    refine ⟨by positivity,?_⟩
    dsimp only
    exact_mod_cast (Finset.card_le_univ (toRestricted U W))
  · intro T
    have hn := local_supplier_actual_fibre_average Q C U rank hrank hU T
    have hc : (((fixedFamily Q C).filter (fun W => W \ U=T)).card : ℝ) *
        Fintype.card {r // r ∈ U} ≤
        2 * ∑ W ∈ (fixedFamily Q C).filter (fun W => W \ U=T), ((toRestricted U W).card : ℝ) := by
      exact_mod_cast hn
    nlinarith

theorem local_supplier_exterior_weights (Q : CRS M R) (C : Catalysis M R)
    (U : Finset R) (rank : R → ℕ) (hrank : InternalSubstrateRank Q U rank)
    (hU : SupplierCore Q C U) (h : Finset R → ℝ) (hh : ∀ T, 0 ≤ h T) :
    (U.card : ℝ)*(∑ W ∈ fixedFamily Q C, h (W \ U)) ≤
      2*∑ W ∈ fixedFamily Q C, h (W \ U)*(toRestricted U W).card ∧
    ∃ r ∈ U, (∑ W ∈ fixedFamily Q C, h (W \ U)) ≤
      2*∑ W ∈ (fixedFamily Q C).filter (fun W => r ∈ W), h (W \ U) := by
  have hresult := local_supplier_bounded_weights Q C U rank hrank hU
    (fun W => h (W \ U)) h 1 hh (by norm_num) (by intro W _; simp)
  simpa only [show (1:ℝ)+1=2 by norm_num] using hresult

end RAF.Frankl
