import proofs.PowerLawSmallRAF.SourceSplitBlockTailAssembly
import proofs.PowerLawSmallRAF.SourceGatewayFactorization
import proofs.PowerLawSmallRAF.GrowingCutoffExtinction

namespace PowerLawSmallRAF

noncomputable section

open Filter Topology
open RAF RAF.Polymer RAF.Concrete

/-- The split-core event is a literal subevent of existence of an actual
source reversible RAF. -/
theorem sourceCatalyzedSplitCoreWeight_le_fullRAFProbability
    (a : ℝ) (ha : 1 < a) {n : Nat} (hn : 3 ≤ n) :
    sourceCatalyzedSplitCoreWeight a n ≤ sourceFullRAFProbability a n := by
  classical
  rw [sourceCatalyzedSplitCoreWeight, sourceFullRAFProbability,
    sourceBoundedRevRAFProbability]
  apply Finset.sum_le_sum
  intro config hconfig
  change (if SourceCatalyzedSplitCore config then
      sourcePowerLawConfigWeight a n config else 0) ≤
    (if ∃ S : Finset (Reaction n),
        S.card ≤ Fintype.card (Reaction n) ∧
          IsRevRAF (binaryPolymerCRS n 2)
            (sourceCatalysisOfConfig config) S then
      sourcePowerLawConfigWeight a n config else 0)
  by_cases hcore : SourceCatalyzedSplitCore config
  · obtain ⟨S, hScard, hSraf⟩ :=
      exists_source_revRAF_of_catalyzedSplitCore hn hcore
    have hcard : S.card ≤ Fintype.card (Reaction n) := by
      rw [card_binaryReaction_eq_sourceReactionCount (by omega)]
      exact hScard
    have hex : ∃ T : Finset (Reaction n),
        T.card ≤ Fintype.card (Reaction n) ∧
          IsRevRAF (binaryPolymerCRS n 2)
            (sourceCatalysisOfConfig config) T := ⟨S, hcard, hSraf⟩
    rw [if_pos hcore, if_pos hex]
  · rw [if_neg hcore]
    split_ifs
    · exact sourcePowerLawConfigWeight_nonneg a n ha config
    · exact le_rfl

/-- Above `log 2`, actual source RAF existence has a fixed positive liminf
under exact mean-linear calibration. -/
theorem calibrated_sourceFullRAFProbability_eventually_ge_pos
    (lam : ℝ) (hlam2 : Real.log 2 < lam) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : Nat in atTop,
      δ ≤ sourceFullRAFProbability
        (calibrationExponent lam
          (lt_trans (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hlam2) n) n := by
  let hlam : 0 < lam :=
    lt_trans (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hlam2
  obtain ⟨δ, hδ, hcore⟩ :=
    calibrated_sourceCatalyzedSplitCoreWeight_eventually_ge_pos lam hlam2
  refine ⟨δ, hδ, ?_⟩
  have ha : ∀ᶠ n : Nat in atTop, 1 < calibrationExponent lam hlam n :=
    (calibrationExponent_tendsto_two lam hlam) (Ioi_mem_nhds one_lt_two)
  filter_upwards [hcore, ha, eventually_ge_atTop 3] with n hncore han hn
  exact hncore.trans
    (sourceCatalyzedSplitCoreWeight_le_fullRAFProbability
      (calibrationExponent lam hlam n) han hn)

noncomputable def sourceConditionalBoundedRevRAFProbability
    (a : ℝ) (n m : Nat) : ℝ :=
  sourceBoundedRevRAFProbability a n m / sourceFullRAFProbability a n

/-- In the positive split-core regime, conditioning on RAF existence preserves
the certified divergence of the smallest RAF size. -/
theorem calibrated_sourceConditionalCertifiedCutoff_extinction
    (lam : ℝ) (hlam2 : Real.log 2 < lam) :
    Tendsto (fun n : Nat => sourceConditionalBoundedRevRAFProbability
      (calibrationExponent lam
        (lt_trans (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hlam2) n)
      n (sourceCertifiedGrowingCutoff lam
        (lt_trans (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hlam2) n))
      atTop (nhds 0) := by
  let hlam : 0 < lam :=
    lt_trans (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hlam2
  let num : Nat → ℝ := fun n => sourceBoundedRevRAFProbability
    (calibrationExponent lam hlam n) n
    (sourceCertifiedGrowingCutoff lam hlam n)
  let den : Nat → ℝ := fun n => sourceFullRAFProbability
    (calibrationExponent lam hlam n) n
  obtain ⟨δ, hδ, hden⟩ :=
    calibrated_sourceFullRAFProbability_eventually_ge_pos lam hlam2
  have hnumzero : Tendsto num atTop (nhds 0) := by
    simpa [num] using calibrated_sourceCertifiedGrowingCutoff_extinction lam hlam
  have hupper : Tendsto (fun n => num n / δ) atTop (nhds 0) := by
    simpa using hnumzero.div_const δ
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (nhds 0))
    hupper
  · filter_upwards [eventually_ge_atTop 4,
        (calibrationExponent_tendsto_two lam hlam)
          (Ioi_mem_nhds one_lt_two), hden] with n hn han hdenn
    have hnum0 : 0 ≤ num n := by
      dsimp [num, sourceBoundedRevRAFProbability]
      apply Finset.sum_nonneg
      intro config hconfig
      split_ifs
      · exact sourcePowerLawConfigWeight_nonneg
          (calibrationExponent lam hlam n) n han config
      · exact le_rfl
    have hden0 : 0 ≤ den n := hδ.le.trans hdenn
    exact div_nonneg hnum0 hden0
  · filter_upwards [eventually_ge_atTop 4,
        (calibrationExponent_tendsto_two lam hlam)
          (Ioi_mem_nhds one_lt_two), hden] with n hn han hdenn
    have hnum0 : 0 ≤ num n := by
      dsimp [num, sourceBoundedRevRAFProbability]
      apply Finset.sum_nonneg
      intro config hconfig
      split_ifs
      · exact sourcePowerLawConfigWeight_nonneg
          (calibrationExponent lam hlam n) n han config
      · exact le_rfl
    exact div_le_div_of_nonneg_left hnum0 hδ hdenn

end

end PowerLawSmallRAF
