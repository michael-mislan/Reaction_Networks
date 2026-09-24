import proofs.CompositionalMemory.SemenovParentRegion

namespace CompositionalMemory.Semenov
open MeasureTheory

noncomputable def initialChemicalEnergy (high : Bool) (n : Fin 8 → ℕ) : ℝ :=
  (matrixEnergy (rationalMatrix (initialRecoveryPiece high).pLeft)
    ((fun j => (n j : ℝ)/(recoveryVolume : ℝ))-
      (fun j => ((initialRecoveryPiece high).zLeft j : ℝ)))/(recoveryEta high : ℝ))^6

theorem parent_allocation_base_bound (high : Bool) (n : Fin 8 → ℕ) (hn : GoodRecoveryParent high n) :
    matrixEnergy (rationalMatrix (initialRecoveryPiece high).pLeft)
      (allocationBase n recoveryFeedMeans recoveryVolume
        (fun j => ((initialRecoveryPiece high).zLeft j : ℝ)))/recoveryAllocationScale high ≤
      (recoveryRefillRatio high : ℝ) := by
  have hv : (recoveryVolume : ℝ) ≠ 0 := by norm_num [recoveryVolume]
  have he : (0 : ℝ) < recoveryEta high := by exact_mod_cast (recovery_parameter_checks high).1
  have hr : (0 : ℝ) ≤ recoveryRefillRatio high := by
    exact_mod_cast (recovery_parameter_checks high).2.2.2.2.1
  have hid := allocation_base_refill_identity n recoveryFeedMeans recoveryVolume hv
    (fun j => ((initialRecoveryPiece high).zLeft j : ℝ))
    (fun j => ((terminalRecoveryPiece high).zRight j : ℝ)) nominalFeed
    (fun _ => rfl) (initial_refill_center high)
  rw [hid,matrix_energy_smul]
  have hh := (parent_refill_energy high (parentDeviation high n)).trans
    (mul_le_mul_of_nonneg_left hn hr)
  have hdiv := (div_le_iff₀ he).mpr hh
  convert hdiv using 1
  unfold recoveryAllocationScale parentDeviation
  field_simp

theorem initial_chemical_cap_bound (high : Bool) (n : Fin 8 → ℕ) (hn : GoodRecoveryParent high n) :
    (∫ z,smoothQuadraticCap (initialChemicalEnergy high (refilledCounts z)) ∂allocationLaw n recoveryFeedMeans) ≤
      smoothQuadraticCap ((recoveryRefillRatio high : ℝ)^6)+
        (4+48*(recoveryRefillRatio high : ℝ))*recoveryMoment1 high+12*recoveryMoment2 high := by
  have hp := recovery_allocation_parameters_positive high
  have hm := recovery_allocation_moment_bounds high
    (∑ j,((n j : ℝ)/4+(recoveryFeedMeans j : ℝ))) (by positivity)
    (parent_allocation_variance high n hn)
  have hr : (recoveryRefillRatio high : ℝ) ≤ 1 := by
    exact_mod_cast (recovery_parameter_checks high).2.2.2.2.2
  have hh := allocation_energy_uniform_bound n recoveryFeedMeans
    (rationalMatrix (initialRecoveryPiece high).pLeft)
    (allocationBase n recoveryFeedMeans recoveryVolume (fun j => ((initialRecoveryPiece high).zLeft j : ℝ)))
    (recoveryAllocationScale high) (recoveryInitialL high : ℝ) (recoveryRefillRatio high : ℝ)
    (recoveryMoment1 high) (recoveryMoment2 high) hp.1 hp.2 (initial_recovery_symmetric high)
    (fun v => ((initialRecoveryPiece high).left_metric_bounds v).1)
    (initial_recovery_upper high) (parent_allocation_base_bound high n hn) hr hm.1 hm.2
  have hv : (recoveryVolume : ℝ) ≠ 0 := by norm_num [recoveryVolume]
  have he : (recoveryEta high : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (recovery_parameter_checks high).1
  have hid (z : RawAllocation) := allocation_concentration_energy n recoveryFeedMeans
    (rationalMatrix (initialRecoveryPiece high).pLeft)
    (fun j => ((initialRecoveryPiece high).zLeft j : ℝ)) recoveryVolume (recoveryEta high) hv he z
  unfold initialChemicalEnergy
  simp_rw [hid]
  exact hh

theorem initial_recovery_error_bound (high : Bool) (n : Fin 8 → ℕ) (hn : GoodRecoveryParent high n) :
    (∫ z,smoothQuadraticCap (boundaryEnergy high (initialRecoveryPiece high).zLeft
      (initialRecoveryPiece high).pLeft 0
      (encodeReactor recoveryCountCap recoveryFeedQuota (refilledCounts z) (allocationFeedCount z)))
      ∂allocationLaw n recoveryFeedMeans)+1000*RecoveryPiece.driftCost ≤ (1/250 : ℝ) := by
  have hK : 0 < recoveryFeedQuota := by norm_num [recoveryFeedQuota]
  have hm : (∑ j,(recoveryFeedMeans j : ℝ)) ≤ (recoveryFeedQuota : ℝ)/2 := by
    rw [recovery_feed_mean_sum]
    norm_num [recoveryVolume,recoveryFeedQuota]
  have hh := allocation_combined_cap_bound n recoveryFeedMeans recoveryCountCap recoveryFeedQuota hK
    (parent_inventory_budget high n hn) (initialChemicalEnergy high) (fun _ => by unfold initialChemicalEnergy; positivity)
    ((recoveryVolume : ℝ)*(1/500)*(15231/100000)) hm
  rw [recovery_feed_mean_sum] at hh
  have hc := initial_chemical_cap_bound high n hn
  have he := recovery_total_error_budget high
  have hbound := add_le_add (hh.trans (add_le_add hc le_rfl))
    (le_rfl : 1000*RecoveryPiece.driftCost ≤ 1000*RecoveryPiece.driftCost)
  exact hbound.trans he

end CompositionalMemory.Semenov
