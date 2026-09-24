import proofs.RandomViability.BindingCompetitionContractModel
import proofs.RandomViability.BindingCompetitionServiceBinding

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal

abbrev CompetitionJointState (V C : ℕ) :=
  (CompetitionWindowState V (competitionWindowCap V) × CompetitionGrossCounters C) × Bool

def competitionJointForget {V C : ℕ} (X : CompetitionJointState V C) :
    CompetitionMonitorState V (competitionWindowCap V) := (X.1.1,X.2)

def competitionJointBoundary {V C : ℕ}
    (Y : CompetitionWindowState V (competitionWindowCap V) × CompetitionGrossCounters C)
    (passed : Bool) : CompetitionJointState V C :=
  (((Y.1.1,0),Y.2),if competitionWindowCap V≤Y.1.2.val then passed else false)

def competitionJointAdvance {V C : ℕ}
    (Q : FiniteKernel (CompetitionWindowState V (competitionWindowCap V) × CompetitionGrossCounters C))
    (t : ℝ≥0) (f : CompetitionJointState V C → ℝ) (X : CompetitionJointState V C) : ℝ :=
  Q.poissonized t (fun Y => f (competitionJointBoundary Y X.2)) X.1

def competitionJointSteps {V C : ℕ}
    (Q : FiniteKernel (CompetitionWindowState V (competitionWindowCap V) × CompetitionGrossCounters C))
    (t : ℝ≥0) : ℕ → (CompetitionJointState V C → ℝ) → CompetitionJointState V C → ℝ
  | 0,f => f
  | n+1,f => competitionJointAdvance Q t (competitionJointSteps Q t n f)

def competitionJointFinal {V C : ℕ}
    (Q : FiniteKernel (CompetitionWindowState V (competitionWindowCap V) × CompetitionGrossCounters C))
    (q s : ℝ≥0) (f : CompetitionJointState V C → ℝ) (X : CompetitionJointState V C) : ℝ :=
  Q.poissonized (q*s) (fun Y => f (Y,X.2)) X.1

def competitionJointLaw {V C : ℕ}
    (S : FiniteKernel (CompetitionCounts V × CompetitionGrossCounters C))
    (Q : FiniteKernel (CompetitionWindowState V (competitionWindowCap V) × CompetitionGrossCounters C))
    (q s : ℝ≥0) (m : ℕ) (f : CompetitionJointState V C → ℝ)
    (X : CompetitionCounts V × CompetitionGrossCounters C) : ℝ :=
  S.poissonized (q*500) (fun Y => competitionJointSteps Q q m
    (competitionJointFinal Q q s f) (((Y.1,0),Y.2),true)) X

def competitionJointStartupKernel (V C : ℕ) (p : CompetitionRateBox) (hV : 0 < (V:ℝ)) :
    FiniteKernel (CompetitionCounts V × CompetitionGrossCounters C) :=
  (competitionCountedModel C (competitionContractModel V p hV) competitionServiceLabel).uniformize
    (competitionClock V) (by exact_mod_cast competitionClock_pos V hV)
    (fun X => competition_contract_total V p hV X.1)

def competitionJointWindowKernel (V C : ℕ) (p : CompetitionRateBox) (hV : 0 < (V:ℝ)) :
    FiniteKernel (CompetitionWindowState V (competitionWindowCap V) × CompetitionGrossCounters C) :=
  (competitionCountedModel C (competitionContractWindowModel V p hV) competitionServiceLabel).uniformize
    (competitionClock V) (by exact_mod_cast competitionClock_pos V hV)
    (fun X => competition_contract_window_total V p hV X.1)

theorem competition_joint_steps_projection (V C : ℕ) (p : CompetitionRateBox) (hV : 0 < (V:ℝ))
    (t : ℝ≥0) (n : ℕ) (f : CompetitionMonitorState V (competitionWindowCap V) → ℝ)
    (X : CompetitionJointState V C) :
    competitionJointSteps (competitionJointWindowKernel V C p hV) t n (fun Z => f (competitionJointForget Z)) X=
      competitionMonitorSteps (competitionContractWindowKernel V p hV) t n f (competitionJointForget X) := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    change (competitionJointWindowKernel V C p hV).poissonized t
      (fun Y => competitionJointSteps (competitionJointWindowKernel V C p hV) t n
        (fun Z => f (competitionJointForget Z)) (competitionJointBoundary Y X.2)) X.1 = _
    simp_rw [ih]
    exact competition_counted_poisson C (competitionContractWindowModel V p hV) competitionServiceLabel
      (competitionClock V) (by exact_mod_cast competitionClock_pos V hV) (competition_contract_window_total V p hV)
      t (fun Y => competitionMonitorSteps (competitionContractWindowKernel V p hV) t n f (competitionWindowBoundary Y X.2)) X.1

theorem competition_joint_final_projection (V C : ℕ) (p : CompetitionRateBox) (hV : 0 < (V:ℝ))
    (q s : ℝ≥0) (X : CompetitionJointState V C) :
    competitionJointFinal (competitionJointWindowKernel V C p hV) q s
      (fun Z => competitionOperatingFailure (competitionJointForget Z)) X=
      competitionFinalFailure (competitionContractWindowKernel V p hV) q s (competitionJointForget X) := by
  exact competition_counted_poisson C (competitionContractWindowModel V p hV) competitionServiceLabel
    (competitionClock V) (by exact_mod_cast competitionClock_pos V hV) (competition_contract_window_total V p hV)
    (q*s) (fun Y => competitionOperatingFailure (Y,X.2)) X.1

/-- Actual same-law projection, including startup, every boundary and final fraction. -/
theorem competition_joint_operating_projection (V C : ℕ) (p : CompetitionRateBox) (hV : 0 < (V:ℝ))
    (s : ℝ≥0) (m : ℕ) (X : CompetitionCounts V × CompetitionGrossCounters C) :
    competitionJointLaw (competitionJointStartupKernel V C p hV) (competitionJointWindowKernel V C p hV)
      (competitionClock V) s m (fun Z => competitionOperatingFailure (competitionJointForget Z)) X=
      competitionHorizonFailure V (competitionContractKernel V p hV) (competitionContractWindowKernel V p hV)
        (competitionClock V) s m X.1 := by
  unfold competitionJointLaw
  rw [show competitionJointFinal (competitionJointWindowKernel V C p hV) (competitionClock V) s
    (fun Z => competitionOperatingFailure (competitionJointForget Z)) =
    (fun Z => competitionFinalFailure (competitionContractWindowKernel V p hV) (competitionClock V) s (competitionJointForget Z))
    from funext (competition_joint_final_projection V C p hV (competitionClock V) s)]
  simp_rw [competition_joint_steps_projection]
  exact competition_counted_poisson C (competitionContractModel V p hV) competitionServiceLabel
    (competitionClock V) (by exact_mod_cast competitionClock_pos V hV) (competition_contract_total V p hV)
    ((competitionClock V:ℝ≥0)*500)
    (fun Y => competitionMonitorSteps (competitionContractWindowKernel V p hV) (competitionClock V) m
      (competitionFinalFailure (competitionContractWindowKernel V p hV) (competitionClock V) s) ((Y,0),true)) X

end
end RandomViability.Binding
