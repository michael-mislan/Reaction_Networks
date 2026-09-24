import proofs.CompositionalMemory.SemenovEndpointBounds
import proofs.CompositionalMemory.SemenovAllocationParameters

namespace CompositionalMemory.Semenov
open SemenovRecoveryPieces SemenovEndpointBounds

def initialRecoveryPiece : (high : Bool) → RecoveryPiece high
  | false => lowPiece00
  | true => highPiece00

def terminalRecoveryPiece : (high : Bool) → RecoveryPiece high
  | false => lowPiece15
  | true => highPiece21

noncomputable def parentDeviation (high : Bool) (n : Fin 8 → ℕ) : Fin 8 → ℝ :=
  (fun j => (n j : ℝ)/(recoveryVolume : ℝ))-
    (fun j => ((terminalRecoveryPiece high).zRight j : ℝ))

def GoodRecoveryParent (high : Bool) (n : Fin 8 → ℕ) : Prop :=
  matrixEnergy (rationalMatrix (terminalRecoveryPiece high).pRight) (parentDeviation high n) ≤
    (recoveryEta high : ℝ)

theorem parent_region_radius (high : Bool) (n : Fin 8 → ℕ) (hn : GoodRecoveryParent high n) :
    vectorSquares (parentDeviation high n) ≤ ((terminalRecoveryPiece high).radius : ℝ)^2 :=
  (terminalRecoveryPiece high).right_radius_bound _ hn

theorem terminal_parent_total_check (high : Bool) :
    (∑ j,((terminalRecoveryPiece high).zRight j : ℝ))+
      8*((terminalRecoveryPiece high).radius : ℝ) ≤ (1/5 : ℝ) := by
  cases high
  · change (∑ j,(SemenovLowMetric15.zr j : ℝ))+8*(SemenovLowMetric15.radius : ℝ) ≤ (1/5 : ℝ)
    have hh := Rat.cast_mono (K := ℝ) SemenovLowEndpoint.finite_checks.2.2.2.2.2.2.2.1
    simp only [Rat.cast_add,Rat.cast_sum,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div,Rat.cast_one] at hh
    exact hh
  · change (∑ j,(SemenovHighMetric21.zr j : ℝ))+8*(SemenovHighMetric21.radius : ℝ) ≤ (1/5 : ℝ)
    have hh := Rat.cast_mono (K := ℝ) SemenovHighEndpoint.finite_checks.2.2.2.2.2.2.2.1
    simp only [Rat.cast_add,Rat.cast_sum,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div,Rat.cast_one] at hh
    exact hh

theorem terminal_parent_variance_check (high : Bool) :
    (∑ j,((terminalRecoveryPiece high).zRight j : ℝ))/4+
      2*((terminalRecoveryPiece high).radius : ℝ)+(15231/100000 : ℝ)/2 ≤
        (recoveryVariance high : ℝ) := by
  have hf : (∑ j,feedRational j)=(15231/100000 : ℚ) := by
    norm_num [feedRational,Fin.sum_univ_succ]
  cases high
  · have hh := SemenovLowEndpoint.finite_checks.2.2.2.2.2.2.2.2.1
    rw [hf] at hh
    change (∑ j,(SemenovLowMetric15.zr j : ℝ))/4+2*(SemenovLowMetric15.radius : ℝ)+
      (15231/100000 : ℝ)/2 ≤ ((23/200 : ℚ) : ℝ)
    have hc := Rat.cast_mono (K := ℝ) hh
    simp only [Rat.cast_add,Rat.cast_sum,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div] at hc ⊢
    exact hc
  · have hh := SemenovHighEndpoint.finite_checks.2.2.2.2.2.2.2.2.1
    rw [hf] at hh
    change (∑ j,(SemenovHighMetric21.zr j : ℝ))/4+2*(SemenovHighMetric21.radius : ℝ)+
      (15231/100000 : ℝ)/2 ≤ ((57/500 : ℚ) : ℝ)
    have hc := Rat.cast_mono (K := ℝ) hh
    simp only [Rat.cast_add,Rat.cast_sum,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div] at hc ⊢
    exact hc

theorem parent_concentration_total (high : Bool) (n : Fin 8 → ℕ) (hn : GoodRecoveryParent high n) :
    (∑ j,(n j : ℝ)/(recoveryVolume : ℝ)) ≤ (1/5 : ℝ) := by
  have hr : (0 : ℝ) ≤ (terminalRecoveryPiece high).radius := by
    exact_mod_cast (terminalRecoveryPiece high).geometry.1.2.1.le
  exact (terminal_total_upper _ _ _ hr (parent_region_radius high n hn)).trans
    (terminal_parent_total_check high)

theorem parent_allocation_variance (high : Bool) (n : Fin 8 → ℕ) (hn : GoodRecoveryParent high n) :
    (∑ j,((n j : ℝ)/4+(recoveryFeedMeans j : ℝ))) ≤
      (recoveryVolume : ℝ)*(recoveryVariance high : ℝ) := by
  have hr : (0 : ℝ) ≤ (terminalRecoveryPiece high).radius := by
    exact_mod_cast (terminalRecoveryPiece high).geometry.1.2.1.le
  have ht := terminal_total_upper _ _ _ hr (parent_region_radius high n hn)
  have hv := terminal_parent_variance_check high
  apply allocation_variance_from_total
  linarith only [ht,hv]

theorem parent_inventory_budget (high : Bool) (n : Fin 8 → ℕ) (hn : GoodRecoveryParent high n) :
    (∑ j,n j)+recoveryFeedQuota ≤ recoveryCountCap := by
  have ht := parent_concentration_total high n hn
  rw [← Finset.sum_div] at ht
  have hv : (0 : ℝ) < recoveryVolume := by norm_num [recoveryVolume]
  have hh := (div_le_iff₀ hv).mp ht
  have hcast : ((∑ j,n j) : ℝ)+(recoveryFeedQuota : ℝ) ≤ (recoveryCountCap : ℝ) := by
    norm_num [recoveryVolume,recoveryFeedQuota,recoveryCountCap] at hh ⊢
    linarith only [hh]
  exact_mod_cast hcast

theorem initial_refill_center (high : Bool) (j : Fin 8) :
    ((initialRecoveryPiece high).zLeft j : ℝ)=
      (((terminalRecoveryPiece high).zRight j : ℝ)+nominalFeed j)/2 := by
  rw [← feedRational_cast]
  cases high
  · exact_mod_cast SemenovLowEndpoint.finite_checks.2.2.2.2.2.2.1 j
  · exact_mod_cast SemenovHighEndpoint.finite_checks.2.2.2.2.2.2.1 j

theorem parent_refill_energy (high : Bool) (v : Fin 8 → ℝ) :
    matrixEnergy (rationalMatrix (initialRecoveryPiece high).pLeft) ((1/2 : ℝ) • v) ≤
      (recoveryRefillRatio high : ℝ)*matrixEnergy (rationalMatrix (terminalRecoveryPiece high).pRight) v := by
  cases high
  · exact low_refill_comparison v
  · exact high_refill_comparison v

theorem initial_recovery_upper (high : Bool) (v : Fin 8 → ℝ) :
    matrixEnergy (rationalMatrix (initialRecoveryPiece high).pLeft) v ≤
      (recoveryInitialL high : ℝ)*vectorSquares v := by
  cases high
  · exact low_initial_upper v
  · exact high_initial_upper v

theorem initial_recovery_symmetric (high : Bool) :
    ∀ i j,rationalMatrix (initialRecoveryPiece high).pLeft i j=
      rationalMatrix (initialRecoveryPiece high).pLeft j i := by
  cases high
  · exact low_initial_symmetric
  · exact high_initial_symmetric

end CompositionalMemory.Semenov
