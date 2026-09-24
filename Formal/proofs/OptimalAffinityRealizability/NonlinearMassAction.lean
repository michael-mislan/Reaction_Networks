import proofs.OptimalAffinityRealizability.ImplicitBranch
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OptimalAffinityRealizability

noncomputable section

/-- Reconstructed forward mass-action flow in log-concentration coordinates. -/
def reconstructedLogForwardFlow {n : ℕ} (source : SquareSource n) (J : ℝ)
    (g q z : Fin n → ℝ) : Fin n → ℝ := fun i =>
  reconstructedForwardFlow J g q i *
    Real.exp (source.reactant.transpose.mulVec z i)

/-- Reconstructed reverse mass-action flow in log-concentration coordinates. -/
def reconstructedLogReverseFlow {n : ℕ} (source : SquareSource n) (J : ℝ)
    (g q z : Fin n → ℝ) : Fin n → ℝ := fun i =>
  reconstructedReverseFlow J g q i *
    Real.exp (source.product.transpose.mulVec z i)

def reconstructedLogReactionCurrent {n : ℕ} (source : SquareSource n) (J : ℝ)
    (g q z : Fin n → ℝ) : Fin n → ℝ :=
  reconstructedLogForwardFlow source J g q z -
    reconstructedLogReverseFlow source J g q z

def reconstructedLogSourceDrift {n : ℕ} (source : SquareSource n) (J : ℝ)
    (g q z : Fin n → ℝ) : Fin n → ℝ :=
  source.netStoich.mulVec (reconstructedLogReactionCurrent source J g q z)

/-- A square stationarity map: its controlled row fixes the log concentration,
and every other row is the literal source drift. -/
def augmentedLogStationarity {n : ℕ} (source : SquareSource n) (J : ℝ)
    (g q z : Fin n → ℝ) : Fin n → ℝ := fun i =>
  if i = source.controlled then z i else reconstructedLogSourceDrift source J g q z i

theorem reconstructedLogReactionCurrent_zero {n : ℕ} (source : SquareSource n)
    (J : ℝ) (g q : Fin n → ℝ) :
    reconstructedLogReactionCurrent source J g q 0 = fun i =>
      reconstructedForwardFlow J g q i - reconstructedReverseFlow J g q i := by
  funext i
  simp [reconstructedLogReactionCurrent, reconstructedLogForwardFlow,
    reconstructedLogReverseFlow]

theorem reconstructedLogSourceDrift_zero {n : ℕ} (source : SquareSource n)
    (J : ℝ) (g q : Fin n → ℝ) :
    reconstructedLogSourceDrift source J g q 0 = netUnitStateDrift source J g q := by
  rw [reconstructedLogSourceDrift, reconstructedLogReactionCurrent_zero]
  rfl

theorem augmentedLogStationarity_zero {n : ℕ} (source : SquareSource n)
    (J : ℝ) (g q : Fin n → ℝ)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i) (hq : ∀ i, 1 < q i)
    (hmode : ControlledProductionMode source g) :
    augmentedLogStationarity source J g q 0 = 0 := by
  funext i
  by_cases hi : i = source.controlled
  · simp [augmentedLogStationarity, hi]
  · rw [augmentedLogStationarity, if_neg hi, reconstructedLogSourceDrift_zero]
    exact reconstructedSource_noncontrolled_stationary source J g q hJ hg hq hmode i hi

theorem reconstructedLogFlows_positive {n : ℕ} (source : SquareSource n)
    (J : ℝ) (g q z : Fin n → ℝ)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i) (hq : ∀ i, 1 < q i) :
    (∀ i, 0 < reconstructedLogForwardFlow source J g q z i) ∧
      (∀ i, 0 < reconstructedLogReverseFlow source J g q z i) := by
  constructor <;> intro i
  · exact mul_pos ((reconstructedFlows_positive J g q hJ hg hq).2 i) (Real.exp_pos _)
  · exact mul_pos ((reconstructedFlows_positive J g q hJ hg hq).1 i) (Real.exp_pos _)

end
end OptimalAffinityRealizability
