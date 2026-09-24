import proofs.OverlapCorrectedRAF.Overlap.FinitePartition

namespace OverlapCorrectedRAF.Overlap

/-- In the coordinate-disjoint model, every core has its own copy of each
channel label.  Hence coordinates belonging to distinct cores are disjoint by
construction. -/
def dedicatedRequirements
    {M J K : Type*} [DecidableEq M] [DecidableEq K]
    (eligible : K → Finset M) (k : K) (channel : K × J) : Finset M :=
  if channel.1 = k then eligible k else ∅

theorem selectedRequirementFamily_dedicated
    {M J K : Type*} [DecidableEq M] [DecidableEq K]
    (eligible : K → Finset M) (hnonempty : ∀ k, (eligible k).Nonempty)
    (selected : Finset K) (owner : K) (j : J) :
    selectedRequirementFamily selected (dedicatedRequirements eligible) (owner, j) =
      if owner ∈ selected then {eligible owner} else ∅ := by
  ext W
  simp only [selectedRequirementFamily, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨a, ⟨ha, hactive⟩, hW⟩
    by_cases hoa : owner = a
    · subst a
      simp [ha, dedicatedRequirements] at hW ⊢
      exact hW.symm
    · simp [dedicatedRequirements, hoa] at hactive
  · intro hW
    by_cases ho : owner ∈ selected
    · have hEq : W = eligible owner := by simpa [ho] using hW
      subst W
      exact ⟨owner, ⟨ho, by simp [dedicatedRequirements, hnonempty owner]⟩,
        by simp [dedicatedRequirements]⟩
    · simp [ho] at hW

theorem jointBernoulliHitProbability_dedicated
    {M J K : Type*} [DecidableEq M] [DecidableEq J] [DecidableEq K]
    (p : ℝ) (cores : Finset K) (fibres : Finset J)
    (eligible : K → Finset M) (hnonempty : ∀ k, (eligible k).Nonempty)
    (selected : Finset K) (hselected : selected ⊆ cores) :
    jointBernoulliHitProbability p (cores.product fibres)
        (dedicatedRequirements eligible) selected =
      ∏ k ∈ selected,
        localHitProbability (1 - p) {eligible k} ^ fibres.card := by
  rw [jointBernoulliHitProbability]
  simp_rw [selectedRequirementFamily_dedicated eligible hnonempty]
  calc
    _ = ∏ k ∈ cores, ∏ _j ∈ fibres,
        localHitProbability (1 - p)
          (if k ∈ selected then {eligible k} else ∅) :=
      Finset.prod_product cores fibres fun x =>
        localHitProbability (1 - p)
          (if x.1 ∈ selected then {eligible x.1} else ∅)
    _ = _ := by
      simp_rw [apply_ite (fun family =>
        localHitProbability (1 - p) family), localHitProbability_empty]
      simp_rw [Finset.prod_const]
      simp_rw [apply_ite (fun x : ℝ => x ^ fibres.card), one_pow]
      rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hselected]

theorem dedicated_intersections_factorize
    {M J K : Type*} [DecidableEq M] [DecidableEq J] [DecidableEq K]
    (p : ℝ) (cores : Finset K) (fibres : Finset J)
    (eligible : K → Finset M) (hnonempty : ∀ k, (eligible k).Nonempty)
    (selected : Finset K) (hselected : selected ∈ cores.powerset) :
    jointBernoulliHitProbability p (cores.product fibres)
        (dedicatedRequirements eligible) selected =
      ∏ k ∈ selected,
        jointBernoulliHitProbability p (cores.product fibres)
          (dedicatedRequirements eligible) {k} := by
  rw [jointBernoulliHitProbability_dedicated p cores fibres eligible hnonempty
    selected (Finset.mem_powerset.mp hselected)]
  apply Finset.prod_congr rfl
  intro k hk
  rw [jointBernoulliHitProbability_dedicated p cores fibres eligible hnonempty {k}]
  · simp
  · exact Finset.singleton_subset_iff.mpr (Finset.mem_powerset.mp hselected hk)

theorem rafBernoulliProbability_dedicated_nonoverlap
    {M J K : Type*} [DecidableEq M] [DecidableEq J] [DecidableEq K]
    (p : ℝ) (cores : Finset K) (fibres : Finset J)
    (eligible : K → Finset M) (hnonempty : ∀ k, (eligible k).Nonempty) :
    rafBernoulliProbability p (cores.product fibres) cores
        (dedicatedRequirements eligible) =
      1 - ∏ k ∈ cores,
        (1 - (1 - (1 - p) ^ (eligible k).card) ^ fibres.card) := by
  apply rafBernoulliProbability_eq_source_nonoverlap
    p (cores.product fibres) cores (dedicatedRequirements eligible)
      (fun k => (eligible k).card) (fun _ => fibres.card)
  · exact dedicated_intersections_factorize p cores fibres eligible hnonempty
  · intro k hk
    rw [jointBernoulliHitProbability_dedicated p cores fibres eligible hnonempty {k}]
    · rw [OverlapCorrectedRAF.Core.oneCoreBernoulliProbability_exact]
      simp only [Finset.prod_singleton]
      rw [localHitProbability_singleton]
    · exact Finset.singleton_subset_iff.mpr hk

end OverlapCorrectedRAF.Overlap
