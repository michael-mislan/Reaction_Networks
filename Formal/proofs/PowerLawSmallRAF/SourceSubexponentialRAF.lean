import proofs.PowerLawSmallRAF.SourceTwoBandBudgetScale

namespace PowerLawSmallRAF
open RAF RAF.Polymer RAF.Concrete Filter Topology
noncomputable section

theorem sourceBoundedRevRAFProbability_mono_size (a : ℝ) (n m k : Nat)
    (ha : 1<a) (hmk : m ≤ k) :
    sourceBoundedRevRAFProbability a n m ≤ sourceBoundedRevRAFProbability a n k := by
  classical
  unfold sourceBoundedRevRAFProbability
  apply Finset.sum_le_sum
  intro config _
  by_cases hm : ∃ S : Finset (Reaction n), S.card ≤ m ∧
      IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig config) S
  · have hk : ∃ S : Finset (Reaction n), S.card ≤ k ∧
        IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig config) S := by
      obtain ⟨S,hS,hraf⟩ := hm
      exact ⟨S,hS.trans hmk,hraf⟩
    simp only [if_pos hm,if_pos hk,le_refl]
  · rw [if_neg hm]
    split_ifs
    · exact sourcePowerLawConfigWeight_nonneg a n ha config
    · exact le_rfl

/-- Positive-probability subexponential RAFs under the exact source law at
a_n=2-2/n. This is not a conditional typical-minimum theorem. -/
theorem source_subexponential_RAF_positive_probability :
    ∃ (m : Nat → Nat) (ε : ℝ), 0<ε ∧
      (∀ c : ℝ, 0<c → ∀ᶠ n : Nat in atTop, (m n : ℝ)<(2 : ℝ)^(c*(n : ℝ))) ∧
      (∀ᶠ n : Nat in atTop, ε ≤ sourceBoundedRevRAFProbability (2-2/(n : ℝ)) n (m n)) := by
  exact ⟨sourceTwoBandConstructionBudget,sourceNucleusProbabilityFloor/4,
    div_pos sourceNucleusProbabilityFloor_pos (by norm_num),
    fun _ hc => sourceTwoBandConstructionBudget_subexponential hc,
    sourceTwoBand_boundedRAF_eventually_positive⟩

/-- The replacement guide's proposed exponential extinction conclusion is
false for this same source parameter sequence. The broader classification
question remains separate. -/
theorem source_exponential_smallRAF_extinction_false :
    ¬ ∃ c : ℝ, 0<c ∧ Tendsto
      (fun n : Nat => sourceBoundedRevRAFProbability (2-2/(n : ℝ)) n ⌊(2 : ℝ)^(c*(n : ℝ))⌋₊)
      atTop (𝓝 0) := by
  rintro ⟨c,hc,ht⟩
  have he := ht.eventually (gt_mem_nhds
    (div_pos sourceNucleusProbabilityFloor_pos (by norm_num : (0 : ℝ)<4)))
  have hsize := sourceTwoBandConstructionBudget_subexponential hc
  have hboth : ∀ᶠ n : Nat in atTop, False := by
    filter_upwards [he,hsize,sourceTwoBand_boundedRAF_eventually_positive,eventually_ge_atTop 4]
      with n hsmall hbudget hpositive hn
    have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have ha : 1 < 2-2/(n : ℝ) := by
      have hh := (div_lt_one hn0).mpr (show (2 : ℝ)<n by exact_mod_cast (show 2<n by omega))
      linarith
    have hm := sourceBoundedRevRAFProbability_mono_size _ n _ _ ha (Nat.le_floor hbudget.le)
    linarith
  obtain ⟨n,hn⟩ := hboth.exists
  exact hn

end
end PowerLawSmallRAF
