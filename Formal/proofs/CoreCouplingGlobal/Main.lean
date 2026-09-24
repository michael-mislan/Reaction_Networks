import proofs.CoreCouplingGlobal.GEndpoint
import proofs.CoreCouplingGlobal.CouplingEndpoint
import proofs.CoreCouplingGlobal.ActivityEndpoint

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter
open scoped Topology ContDiff

/-- Actual-current eventual activity, transient duration, and the inability of
these activity labels to distinguish the two outer selected concentrations. -/
def FlagshipAResolution (e : ℝ) : Prop :=
(∀ x₀ : State, x₀.Positive → ∃ X : ℝ → State, X 0 = x₀ ∧
      IsPositiveTrajectory e X ∧ ∃ s : State, s.Positive ∧
        Stationary (flagshipRates e) s ∧
        Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState s)) ∧
        ActivitySignature e s ∧
        (∀ᶠ t in atTop, ActivitySignature e (X t)) ∧
        (∀ᶠ t in atTop, (coreAB (flagshipRates e) (X t)).2 < -3 ∧
          2 < (coreZH (flagshipRates e) (X t)).1 ∧
          (1/4000:ℝ) < (coreZH (flagshipRates e) (X t)).2)) ∧
    (∀ X : ℝ → State, IsPositiveTrajectory e X →
      ∀ η a b : ℝ, 0 < η → 0 ≤ a → a ≤ b → (X b).z ≤ 12 →
      (∀ t ∈ Icc a b, η ≤ (coreAB (flagshipRates e) (X t)).1 ∧
        η ≤ (coreAB (flagshipRates e) (X t)).2 ∧
        η ≤ (coreZH (flagshipRates e) (X t)).1) → b-a ≤ 3/η) ∧
    (∃ x y : State, x.Positive ∧ y.Positive ∧
      Stationary (flagshipRates e) x ∧ Stationary (flagshipRates e) y ∧
      x.z < y.z ∧ ActivitySignature e x ∧ ActivitySignature e y)

/-- The phase-two scope retains distinct quantified regimes: G/A on the literal
flagship interval, and C on the nonempty open routed family. It does not assert
flagship global selection for every member of the routed family. -/
def PhaseTwoResolution : Prop :=
  (∀ e ∈ Icc (1/200000:ℝ) (1/50000), FlagshipGResolution e ∧ FlagshipAResolution e) ∧
  IsOpen routedBistableRegion ∧ routedBistableRegion.Nonempty ∧
  Function.Injective (fun p : ℝ × ℝ =>
    routedDynamics p.1 p.2 (transform (⟨1,2,1,8⟩ : State))) ∧
  ∀ p ∈ routedBistableRegion, RoutedCResolution p.1 p.2

/-- Complete G/C/A conjunction at the guide's explicit literal model scopes.
Every dynamical and geometric field is populated by a proved theorem. -/
theorem phaseTwoResolution : PhaseTwoResolution := by
  refine ⟨?_,core_coupling_C_endpoint⟩
  intro e he
  exact ⟨flagship_G_endpoint e he.1 he.2,flagship_activity_endpoint e he.1 he.2⟩

end CoreCouplingGlobal
