import proofs.OptimalAffinityCorrected.SourceClosure
import proofs.OptimalAffinityCorrected.FirstOrderRealizability
import proofs.OptimalAffinityRealizability.ResponseJet
import proofs.OptimalAffinityRealizability.FlowReconstruction
import proofs.OptimalAffinityRealizability.ResponseLaplacian
import proofs.OptimalAffinityRealizability.RoutingMatrix
import proofs.OptimalAffinityRealizability.RoutingCorank
import proofs.OptimalAffinityRealizability.ReducedJacobian
import proofs.OptimalAffinityRealizability.ImplicitBranch
import proofs.OptimalAffinityRealizability.NonlinearMassAction
import proofs.OptimalAffinityRealizability.AugmentedJacobian
import proofs.OptimalAffinityRealizability.LocalBranch
import proofs.OptimalAffinityRealizability.Curvature
import proofs.OptimalAffinityRealizability.SmoothBranch
import proofs.OptimalAffinityRealizability.StrictLocalMaximum
import proofs.OptimalAffinityRealizability.SourceLocalRealization
import proofs.OptimalAffinityRealizability.Capacity
import proofs.OptimalAffinityRealizability.RoutingStationary
import proofs.OptimalAffinityRealizability.BoundaryGauge
import proofs.OptimalAffinityRealizability.CapacityEquality
import proofs.OptimalAffinityRealizability.MatrixScalingKKT
import proofs.OptimalAffinityRealizability.GlobalRealizability
import proofs.OptimalAffinityRealizability.ExactGlobalFixture
import proofs.OptimalAffinityRealizability.PowerGlobalFamily
import proofs.OptimalAffinityRealizability.GlobalInvariant
import proofs.OptimalAffinityRealizability.InteractingCoreCompatibility
import proofs.OptimalAffinityRealizability.SharpCapacity
import proofs.OptimalAffinityRealizability.CurvatureAverage
import proofs.OptimalAffinityRealizability.MatrixScalingDual
import proofs.OptimalAffinityRealizability.TangentGapGlobality

namespace OptimalAffinityRealizability

noncomputable section

/-- Baseline adapter: the new campaign begins from the warning-free inherited
response/source closure and reactionwise flow reconstruction, without claiming
network-wide kinetic realizability. -/
theorem baselineInheritedInterfaces :
    OptimalAffinityCorrected.SourceClosurePackage ∧
    (∀ J g q : ℝ, 0 < J → 0 < g → 1 < q →
      0 < OptimalAffinityCorrected.reconstructedReverseFlux J g q ∧
      0 < OptimalAffinityCorrected.reconstructedForwardFlux J g q) := by
  refine ⟨OptimalAffinityCorrected.sourceClosurePackage, ?_⟩
  intro J g q hJ hg hq
  exact ⟨(OptimalAffinityCorrected.reconstructedFluxes_firstOrder J g q hJ hg hq).1,
    (OptimalAffinityCorrected.reconstructedFluxes_firstOrder J g q hJ hg hq).2.1⟩

/-- Literal raw-source adapter for the local kinetic capacity theorem. -/
theorem rawSquareSource_capacityEquality {n : ℕ} [Nonempty (Fin n)]
    (source : SquareSource n) (weights : Fin n → ℕ)
    (J : ℝ) (production : Fin n → ℝ)
    (hclass : AccessibleIrreducibleResponseClass source)
    (hJ : 0 < J) (hproduction : ∀ i, 0 < production i)
    (hmode : ControlledProductionMode source production) :
    responseLayerCapacity (responseMatrix source) weights =
      strictLocalCapacity source weights J production :=
  responseLayerCapacity_eq_strictLocalCapacity_of_accessibleIrreducible
    source weights J production hclass hJ hproduction hmode

/-- Publication-strengthened raw-source adapter.  The common-reachable routing
condition permits transient states and is the primitive one-final-class form
of the sharp local theorem. -/
theorem rawSquareSource_sharpCapacityEquality {n : ℕ} [Nonempty (Fin n)]
    (source : SquareSource n) (weights : Fin n → ℕ)
    (J : ℝ) (production : Fin n → ℝ)
    (hclass : AccessibleRootedResponseClass source)
    (hJ : 0 < J) (hproduction : ∀ i, 0 < production i)
    (hmode : ControlledProductionMode source production) :
    responseLayerCapacity (responseMatrix source) weights =
      strictLocalCapacity source weights J production :=
  responseLayerCapacity_eq_strictLocalCapacity_of_accessibleRooted
    source weights J production hclass hJ hproduction hmode

def LiteralLocalCapacityResolution : Prop :=
  ∀ {n : ℕ} [Nonempty (Fin n)]
    (source : SquareSource n) (weights : Fin n → ℕ)
    (J : ℝ) (production : Fin n → ℝ),
    AccessibleIrreducibleResponseClass source →
    0 < J → (∀ i, 0 < production i) →
    ControlledProductionMode source production →
    responseLayerCapacity (responseMatrix source) weights =
      strictLocalCapacity source weights J production

def SharpLiteralLocalCapacityResolution : Prop :=
  ∀ {n : ℕ} [Nonempty (Fin n)]
    (source : SquareSource n) (weights : Fin n → ℕ)
    (J : ℝ) (production : Fin n → ℝ),
    AccessibleRootedResponseClass source →
    0 < J → (∀ i, 0 < production i) →
    ControlledProductionMode source production →
    responseLayerCapacity (responseMatrix source) weights =
      strictLocalCapacity source weights J production

def PowerFamilyGlobalResolution : Prop :=
  (∀ d : ℕ, 2 ≤ d → PowerFamilyUniqueGlobal d) ∧
    powerFamilyGlobalCapacity = powerFamilyLocalCapacity

def InteractingCoreBoundaryResolution : Prop :=
  (¬ (∀ F : ThermoCoreCompatibility.CoreFamily
      (Core := ThermoCoreCompatibility.MagnitudePair.Core)
      ThermoCoreCompatibility.MagnitudePair.network,
    F.MultiPAC → F.DirectionCompatible → F.LinearComplexCompatible)) ∧
  (¬ (∀ F : ThermoCoreCompatibility.CoreFamily
      (Core := ThermoCoreCompatibility.ToricPair.Core)
      ThermoCoreCompatibility.ToricPair.network,
    F.MultiPAC → F.DirectionCompatible → F.LinearComplexCompatible → F.MultiCAC))

/-- Root theorem for the kinetic-realizability campaign.  It closes the
literature gap in its proved form: local capacity equality on an explicit
literal square-source class, a new infinite globally realizable class with
global/local capacity equality, and exact counterboundaries preventing invalid
composition-level strengthening. -/
theorem optimalAffinityKineticRealizabilityResolution :
    LiteralLocalCapacityResolution ∧
      PowerFamilyGlobalResolution ∧
      InteractingCoreBoundaryResolution := by
  refine ⟨?_, ?_, ?_⟩
  · intro n inst source weights J production hclass hJ hproduction hmode
    exact rawSquareSource_capacityEquality source weights J production
      hclass hJ hproduction hmode
  · exact ⟨powerFamily_uniqueGlobal,
      powerFamilyGlobalCapacity_eq_localCapacity⟩
  · exact ⟨directionOnly_articulation_refuted,
      linearComplexOnly_articulation_refuted⟩

/-- Publication root theorem after the sharp-routing follow-up.  It strictly
strengthens the local component from irreducible routing to the primitive
one-final-class/common-reachable condition, while preserving the independently
proved global family and interacting-core boundaries. -/
theorem optimalAffinityKineticRealizabilityPublicationResolution :
    SharpLiteralLocalCapacityResolution ∧
      PowerFamilyGlobalResolution ∧
      InteractingCoreBoundaryResolution := by
  refine ⟨?_, ?_, ?_⟩
  · intro n inst source weights J production hclass hJ hproduction hmode
    exact rawSquareSource_sharpCapacityEquality source weights J production
      hclass hJ hproduction hmode
  · exact ⟨powerFamily_uniqueGlobal,
      powerFamilyGlobalCapacity_eq_localCapacity⟩
  · exact ⟨directionOnly_articulation_refuted,
      linearComplexOnly_articulation_refuted⟩

end
end OptimalAffinityRealizability
