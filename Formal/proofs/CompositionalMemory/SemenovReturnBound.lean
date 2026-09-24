import proofs.CompositionalMemory.SemenovInitialRecoveryBound
import proofs.CompositionalMemory.SemenovTerminalFailure
import proofs.CompositionalMemory.SemenovRecoveryCover

namespace CompositionalMemory.Semenov
open MeasureTheory

theorem initial_recovery_time (high : Bool) : (initialRecoveryPiece high).left=0 := by
  cases high
  · exact SemenovCoverChecks.low_checks.1.1
  · exact SemenovCoverChecks.high_checks.1.1

theorem terminal_recovery_time (high : Bool) : (terminalRecoveryPiece high).right=500 := by
  cases high
  · exact SemenovCoverChecks.low_checks.1.2
  · exact SemenovCoverChecks.high_checks.1.2

theorem full_recovery_cap_bound (high : Bool) (s : ReactorState recoveryCountCap recoveryFeedQuota) :
    finiteTimeExpectation (nominalReactor recoveryCountCap recoveryFeedQuota recoveryVolume (Nat.cast_nonneg _))
      500 (fun y => smoothQuadraticCap (boundaryEnergy high (terminalRecoveryPiece high).zRight
        (terminalRecoveryPiece high).pRight 500 y)) s ≤
      smoothQuadraticCap (boundaryEnergy high (initialRecoveryPiece high).zLeft
        (initialRecoveryPiece high).pLeft 0 s)+1000*RecoveryPiece.driftCost := by
  have hh : finiteTimeExpectation (nominalReactor recoveryCountCap recoveryFeedQuota recoveryVolume (Nat.cast_nonneg _))
      500 (rightObservable (terminalRecoveryPiece high)) s ≤
        leftObservable (initialRecoveryPiece high) s+1000*RecoveryPiece.driftCost := by
    cases high
    · exact SemenovRecoveryCover.low_recovery s
    · exact SemenovRecoveryCover.high_recovery s
  have hl : leftObservable (initialRecoveryPiece high)=fun y =>
      smoothQuadraticCap (boundaryEnergy high (initialRecoveryPiece high).zLeft (initialRecoveryPiece high).pLeft 0 y) := by
    funext y
    unfold leftObservable
    rw [initial_recovery_time]
    norm_num only [Rat.cast_zero]
  have hr : rightObservable (terminalRecoveryPiece high)=fun y =>
      smoothQuadraticCap (boundaryEnergy high (terminalRecoveryPiece high).zRight (terminalRecoveryPiece high).pRight 500 y) := by
    funext y
    unfold rightObservable
    rw [terminal_recovery_time]
    norm_num only [Rat.cast_ofNat]
  rw [hl,hr] at hh
  exact hh

noncomputable def daughterFailureProbability (high : Bool) (n : Fin 8 → ℕ) : ℝ :=
  ∫ z,finiteTimeExpectation
    (nominalReactor recoveryCountCap recoveryFeedQuota recoveryVolume (Nat.cast_nonneg _))
    500 (recoveryFailure high)
    (encodeReactor recoveryCountCap recoveryFeedQuota (refilledCounts z) (allocationFeedCount z))
    ∂allocationLaw n recoveryFeedMeans

theorem daughter_failure_bound (high : Bool) (n : Fin 8 → ℕ) (hn : GoodRecoveryParent high n) :
    daughterFailureProbability high n ≤ (1/250 : ℝ) := by
  let M := nominalReactor recoveryCountCap recoveryFeedQuota recoveryVolume (Nat.cast_nonneg _)
  let encoded (z : RawAllocation) := encodeReactor recoveryCountCap recoveryFeedQuota
    (refilledCounts z) (allocationFeedCount z)
  let E (z : RawAllocation) := boundaryEnergy high (initialRecoveryPiece high).zLeft
    (initialRecoveryPiece high).pLeft 0 (encoded z)
  have hE (z : RawAllocation) : 0 ≤ E z :=
    reactor_combined_energy_nonneg _ (fun _ => by positivity) _ _ _ _
  have hcap := cap_integrable_countable (allocationLaw n recoveryFeedMeans) E hE
  have hf : Integrable (fun z => finiteTimeExpectation M 500 (recoveryFailure high) (encoded z))
      (allocationLaw n recoveryFeedMeans) := by
    apply (integrable_const (1 : ℝ)).mono_nonneg (measurable_of_countable _).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun z => (finite_time_bounds M 500 _ (recovery_failure_bounds high) (encoded z)).1)
    · exact Filter.Eventually.of_forall (fun z => (finite_time_bounds M 500 _ (recovery_failure_bounds high) (encoded z)).2)
  have hpoint (z : RawAllocation) :
      finiteTimeExpectation M 500 (recoveryFailure high) (encoded z) ≤
        smoothQuadraticCap (E z)+1000*RecoveryPiece.driftCost := by
    exact (finite_time_expectation_mono M 500 _ _ (recovery_failure_cap high) (encoded z)).trans
      (full_recovery_cap_bound high (encoded z))
  have hh := integral_mono hf (hcap.add (integrable_const (1000*RecoveryPiece.driftCost))) hpoint
  simp only [Pi.add_apply] at hh
  rw [integral_add hcap (integrable_const _),integral_const] at hh
  norm_num only [probReal_univ,one_smul] at hh
  exact hh.trans (initial_recovery_error_bound high n hn)

end CompositionalMemory.Semenov
