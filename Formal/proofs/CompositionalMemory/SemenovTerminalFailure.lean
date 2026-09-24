import proofs.CompositionalMemory.SemenovParentRegion

namespace CompositionalMemory.Semenov

noncomputable def recoveryFailure (high : Bool) : ReactorState recoveryCountCap recoveryFeedQuota → ℝ := by
  classical
  exact fun s => match s with
    | none => 1
    | some (n,_) => if GoodRecoveryParent high (fun j => (n j).val) then 0 else 1

theorem recovery_failure_bounds (high : Bool) (s : ReactorState recoveryCountCap recoveryFeedQuota) :
    0 ≤ recoveryFailure high s ∧ recoveryFailure high s ≤ 1 := by
  classical
  cases s with
  | none => norm_num [recoveryFailure]
  | some p => simp only [recoveryFailure]; split_ifs <;> norm_num

theorem recovery_failure_cap (high : Bool) (s : ReactorState recoveryCountCap recoveryFeedQuota) :
    recoveryFailure high s ≤ smoothQuadraticCap
      (boundaryEnergy high (terminalRecoveryPiece high).zRight (terminalRecoveryPiece high).pRight 500 s) := by
  classical
  cases s with
  | none => norm_num [recoveryFailure,boundaryEnergy,reactorCombinedEnergy,smoothQuadraticCap]
  | some p =>
    rcases p with ⟨n,c⟩
    by_cases hn : GoodRecoveryParent high (fun j => (n j).val)
    · simp only [recoveryFailure,if_pos hn]
      exact smoothQuadraticCap_nonneg _
        (reactor_combined_energy_nonneg _ (fun _ => by positivity) _ _ _ _)
    · simp only [recoveryFailure,if_neg hn]
      let D := matrixEnergy (rationalMatrix (terminalRecoveryPiece high).pRight)
        (parentDeviation high (fun j => (n j).val))/(recoveryEta high : ℝ)
      have he : (0 : ℝ) < recoveryEta high := by exact_mod_cast (recovery_parameter_checks high).1
      have hD : 0 ≤ D := div_nonneg
        ((terminalRecoveryPiece high).right_metric_bounds _).1 he.le
      have hnot : ¬boundaryEnergy high (terminalRecoveryPiece high).zRight
          (terminalRecoveryPiece high).pRight 500 (some (n,c)) ≤ 1 := by
        intro hb
        have hc := centeredInventory_nonneg (recoveryFeedQuota : ℝ)
          ((recoveryVolume : ℝ)*(15231/100000)/2)
          ((recoveryVolume : ℝ)*(1/500)*(15231/100000)) 500 c.val
        change D^6+centeredInventory _ _ _ _ _ ≤ 1 at hb
        have hp : D^6 ≤ 1 := by linarith only [hb,hc]
        have hD1 := (pow_le_one_iff_of_nonneg hD (by norm_num : (6 : ℕ) ≠ 0)).mp hp
        exact hn ((div_le_one he).mp hD1)
      simp only [smoothQuadraticCap,if_neg hnot,le_refl]

end CompositionalMemory.Semenov
