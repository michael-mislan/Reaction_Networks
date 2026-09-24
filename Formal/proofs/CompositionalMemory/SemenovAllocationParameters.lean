import proofs.CompositionalMemory.SemenovScaledAllocation
import proofs.CompositionalMemory.SemenovRecoveryPiece

namespace CompositionalMemory.Semenov
open MeasureTheory

noncomputable def recoveryFeedMeans (j : Fin 8) : NNReal :=
  ⟨(recoveryVolume : ℝ)*nominalFeed j/2,
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (nominalFeed_nonneg _)) (by norm_num)⟩

theorem recovery_feed_mean_sum :
    (∑ j,(recoveryFeedMeans j : ℝ))=(recoveryVolume : ℝ)*(15231/100000)/2 := by
  have hf (j : Fin 8) : (recoveryFeedMeans j : ℝ)=(recoveryVolume : ℝ)*nominalFeed j/2 := rfl
  simp_rw [hf]
  norm_num [recoveryVolume,nominalFeed,feed,Fin.sum_univ_succ]

noncomputable def recoveryAllocationScale (high : Bool) : ℝ :=
  (recoveryVolume : ℝ)^2*(recoveryEta high : ℝ)

noncomputable def recoveryMoment1 (high : Bool) : ℝ :=
  (recoveryInitialL high : ℝ)/recoveryAllocationScale high*
    ((recoveryVolume : ℝ)*(recoveryVariance high : ℝ))

noncomputable def recoveryMoment2 (high : Bool) : ℝ :=
  ((recoveryInitialL high : ℝ)/recoveryAllocationScale high)^2*8*
    (3*((recoveryVolume : ℝ)*(recoveryVariance high : ℝ))^2+
      (recoveryVolume : ℝ)*(recoveryVariance high : ℝ))

theorem recovery_allocation_parameters_positive (high : Bool) :
    0 < recoveryAllocationScale high ∧ 0 ≤ (recoveryInitialL high : ℝ) := by
  cases high <;> norm_num [recoveryAllocationScale,recoveryVolume,recoveryEta,recoveryInitialL]

theorem recovery_allocation_moment_bounds (high : Bool) (S : ℝ) (hS : 0 ≤ S)
    (hV : S ≤ (recoveryVolume : ℝ)*(recoveryVariance high : ℝ)) :
    (recoveryInitialL high : ℝ)/recoveryAllocationScale high*S ≤ recoveryMoment1 high ∧
      ((recoveryInitialL high : ℝ)/recoveryAllocationScale high)^2*8*(3*S^2+S) ≤ recoveryMoment2 high := by
  have hp := recovery_allocation_parameters_positive high
  constructor
  · exact mul_le_mul_of_nonneg_left hV (div_nonneg hp.2 hp.1.le)
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hS hV 2) (by norm_num)) hV

theorem recovery_total_error_budget (high : Bool) :
    smoothQuadraticCap ((recoveryRefillRatio high : ℝ)^6)+
      (4+48*(recoveryRefillRatio high : ℝ))*recoveryMoment1 high+12*recoveryMoment2 high+
      64*((recoveryVolume : ℝ)*(15231/100000)/2)/(recoveryFeedQuota : ℝ)^2+
      1000*RecoveryPiece.driftCost ≤ (1/250 : ℝ) := by
  cases high <;> norm_num [smoothQuadraticCap,recoveryRefillRatio,recoveryMoment1,recoveryMoment2,
    recoveryInitialL,recoveryAllocationScale,recoveryEta,recoveryVolume,recoveryVariance,
    recoveryFeedQuota,RecoveryPiece.driftCost]

theorem allocation_variance_from_total (n : Fin 8 → ℕ) (vs : ℝ)
    (ht : (∑ j,(n j : ℝ)/(recoveryVolume : ℝ))/4+(15231/100000 : ℝ)/2 ≤ vs) :
    (∑ j,((n j : ℝ)/4+(recoveryFeedMeans j : ℝ))) ≤ (recoveryVolume : ℝ)*vs := by
  have hv : (0 : ℝ) < recoveryVolume := by norm_num [recoveryVolume]
  have hh := mul_le_mul_of_nonneg_left ht hv.le
  have he : (∑ j,((n j : ℝ)/4+(recoveryFeedMeans j : ℝ)))=
      (recoveryVolume : ℝ)*((∑ j,(n j : ℝ)/(recoveryVolume : ℝ))/4+(15231/100000 : ℝ)/2) := by
    rw [Finset.sum_add_distrib,recovery_feed_mean_sum,← Finset.sum_div,← Finset.sum_div]
    field_simp
  rw [he]
  exact hh

end CompositionalMemory.Semenov
