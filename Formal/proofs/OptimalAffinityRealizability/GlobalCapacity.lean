import proofs.OptimalAffinityRealizability.GlobalEquality
import proofs.OptimalAffinityRealizability.SharpCapacity

namespace OptimalAffinityRealizability
noncomputable section

structure GlobalRealizationWitness {n : ℕ} (source : SquareSource n) (J : ℝ)
    (g f : Fin n → ℝ) where
  localWitness : StrictLocalRealizationWitness source J g f
  globalBound : ∀ z, GlobalStationaryFiber source J g localWitness.q z →
    controlledFluxAtLogState source J g localWitness.q z ≤ J

def GlobalRealizable {n : ℕ} (source : SquareSource n) (J : ℝ)
    (g f : Fin n → ℝ) : Prop := Nonempty (GlobalRealizationWitness source J g f)

theorem strictLocal_globalRealizable {n : ℕ} [Nonempty (Fin n)]
    (source : SquareSource n) (J : ℝ) (g f : Fin n → ℝ)
    (hT : ∀ i j, 0 ≤ responseMatrix source i j)
    (hw : StrictLocalRealizable source J g f) : GlobalRealizable source J g f := by
  obtain ⟨w⟩ := hw
  refine ⟨{ localWitness := w, globalBound := ?_ }⟩
  intro z hz
  apply reconstructedSource_globalMaximum source J g f w.q
    w.certificate.positiveCurrent w.certificate.positiveProduction
    w.certificate.productionMode hT w.certificate.positiveResponse
    w.certificate.positiveRatio _ z hz
  intro i
  rw [← productResponse_eq_responseMatrix_transpose_mulVec]
  have hu : responseTangent source f = w.u :=
    reactantTranspose_mulVec_injective source (by
      rw [reactantResponse_responseTangent, w.certificate.reactantResponse])
  change source.product.transpose.mulVec (responseTangent source f) i = _
  rw [hu, w.certificate.productResponse, w.certificate.responseRatio]

theorem strictLocal_uniqueGlobalRealizable {n : ℕ} [Nonempty (Fin n)]
    (source : SquareSource n) (J : ℝ) (g f : Fin n → ℝ)
    (hT : ∀ i j, 0 ≤ responseMatrix source i j)
    (hconn : ResponseStronglyConnected (responseMatrix source))
    (hw : StrictLocalRealizable source J g f) : UniqueGlobalRealizable source J g f := by
  obtain ⟨v⟩ := strictLocal_globalRealizable source J g f hT hw
  let w := v.localWitness
  refine ⟨{ localWitness := w, globalBound := v.globalBound, uniqueEquality := ?_ }⟩
  intro z hz heq
  apply reconstructedSource_uniqueGlobal source J g f w.q
    w.certificate.positiveCurrent w.certificate.positiveProduction
    w.certificate.productionMode hT w.certificate.positiveResponse
    w.certificate.positiveRatio _ hconn z hz heq
  intro i
  rw [← productResponse_eq_responseMatrix_transpose_mulVec]
  have hu : responseTangent source f = w.u :=
    reactantTranspose_mulVec_injective source (by
      rw [reactantResponse_responseTangent, w.certificate.reactantResponse])
  change source.product.transpose.mulVec (responseTangent source f) i = _
  rw [hu, w.certificate.productResponse, w.certificate.responseRatio]

theorem globalValueSet_eq_localValueSet {n : ℕ} [Nonempty (Fin n)]
    (source : SquareSource n) (weights : Fin n → ℕ) (J : ℝ) (g : Fin n → ℝ)
    (hT : ∀ i j, 0 ≤ responseMatrix source i j) :
    realizationValueSet (responseMatrix source) weights (GlobalRealizable source J g) =
      realizationValueSet (responseMatrix source) weights (StrictLocalRealizable source J g) := by
  ext v
  constructor
  · rintro ⟨f, ⟨w⟩, heq⟩
    exact ⟨f, ⟨w.localWitness⟩, heq⟩
  · rintro ⟨f, hw, heq⟩
    exact ⟨f, strictLocal_globalRealizable source J g f hT hw, heq⟩

theorem rawSquareSource_globalValueSetEquality {n : ℕ} [Nonempty (Fin n)]
    (source : SquareSource n) (weights : Fin n → ℕ) (J : ℝ) (g : Fin n → ℝ)
    (hclass : AccessibleRootedResponseClass source)
    (hT : ∀ i j, 0 ≤ responseMatrix source i j)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i) (hmode : ControlledProductionMode source g) :
    realizationValueSet (responseMatrix source) weights (GlobalRealizable source J g) =
      realizationValueSet (responseMatrix source) weights (ResponseFeasible (responseMatrix source)) := by
  rw [globalValueSet_eq_localValueSet source weights J g hT]
  exact (responseValueSet_eq_strictLocalValueSet_of_accessibleRooted
    source weights J g hclass hJ hg hmode).symm

theorem rawSquareSource_globalCapacityEquality {n : ℕ} [Nonempty (Fin n)]
    (source : SquareSource n) (weights : Fin n → ℕ) (J : ℝ) (g : Fin n → ℝ)
    (hclass : AccessibleRootedResponseClass source)
    (hT : ∀ i j, 0 ≤ responseMatrix source i j)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i) (hmode : ControlledProductionMode source g)
    (hne : ∃ f, ResponseFeasible (responseMatrix source) f) :
    (∃ f, GlobalRealizable source J g f) ∧
    realizationCapacity (responseMatrix source) weights (GlobalRealizable source J g) =
      responseLayerCapacity (responseMatrix source) weights := by
  constructor
  · obtain ⟨f, hf⟩ := hne
    obtain ⟨f', _, hw⟩ := accessibleRootedResponseClass_rayStrictLocal source J g
      hclass hJ hg hmode f hf
    exact ⟨f', strictLocal_globalRealizable source J g f' hT hw⟩
  · unfold realizationCapacity responseLayerCapacity
    rw [rawSquareSource_globalValueSetEquality source weights J g hclass hT hJ hg hmode]
    rfl

theorem rawSquareSource_uniqueGlobalValueSetEquality {n : ℕ} [Nonempty (Fin n)]
    (source : SquareSource n) (weights : Fin n → ℕ) (J : ℝ) (g : Fin n → ℝ)
    (hclass : AccessibleRootedResponseClass source)
    (hT : ∀ i j, 0 ≤ responseMatrix source i j)
    (hconn : ResponseStronglyConnected (responseMatrix source))
    (hJ : 0 < J) (hg : ∀ i, 0 < g i) (hmode : ControlledProductionMode source g) :
    realizationValueSet (responseMatrix source) weights (UniqueGlobalRealizable source J g) =
      realizationValueSet (responseMatrix source) weights (ResponseFeasible (responseMatrix source)) := by
  rw [responseValueSet_eq_strictLocalValueSet_of_accessibleRooted source weights J g hclass hJ hg hmode]
  ext v
  constructor
  · rintro ⟨f, hw, heq⟩
    exact ⟨f, uniqueGlobalRealizable_strictLocal source J g f hw, heq⟩
  · rintro ⟨f, hw, heq⟩
    exact ⟨f, strictLocal_uniqueGlobalRealizable source J g f hT hconn hw, heq⟩

end
end OptimalAffinityRealizability
