import proofs.OptimalAffinityRealizability.CapacityEquality
import proofs.OptimalAffinityRealizability.SharpRouting

namespace OptimalAffinityRealizability

open scoped BigOperators
noncomputable section

/-- Publication-facing expansion of the original class predicate. -/
theorem accessibleIrreducibleResponseClass_iff_primitive {n : ℕ}
    [Nonempty (Fin n)] (source : SquareSource n) :
    AccessibleIrreducibleResponseClass source ↔
      ∀ f : Fin n → ℝ, ResponseFeasible (responseMatrix source) f →
        ControlAccessible source f ∧
        (∀ i j, 0 ≤ routingMatrix (responseMatrix source)
          (fun k => OptimalAffinityCorrected.responseRatio
            (responseMatrix source) f k) f i j) ∧
        (routingMatrix (responseMatrix source)
          (fun k => OptimalAffinityCorrected.responseRatio
            (responseMatrix source) f k) f).IsIrreducible := by
  rfl

/-- The sharpened primitive source class: every feasible response ray is
control-accessible, has nonnegative routing, and has one common reachable
routing state (equivalently one final communicating class). -/
def AccessibleRootedResponseClass {n : ℕ} [Nonempty (Fin n)]
    (source : SquareSource n) : Prop :=
  ∀ f : Fin n → ℝ, ResponseFeasible (responseMatrix source) f →
    ControlAccessible source f ∧
    (∀ i j, 0 ≤ routingMatrix (responseMatrix source)
      (fun k => OptimalAffinityCorrected.responseRatio (responseMatrix source) f k)
      f i j) ∧
    HasCommonReachableState
      (routingMatrix (responseMatrix source)
        (fun k => OptimalAffinityCorrected.responseRatio
          (responseMatrix source) f k) f)

theorem accessibleRootedResponseClass_iff_primitive {n : ℕ}
    [Nonempty (Fin n)] (source : SquareSource n) :
    AccessibleRootedResponseClass source ↔
      ∀ f : Fin n → ℝ, ResponseFeasible (responseMatrix source) f →
        ControlAccessible source f ∧
        (∀ i j, 0 ≤ routingMatrix (responseMatrix source)
          (fun k => OptimalAffinityCorrected.responseRatio
            (responseMatrix source) f k) f i j) ∧
        HasCommonReachableState
          (routingMatrix (responseMatrix source)
            (fun k => OptimalAffinityCorrected.responseRatio
              (responseMatrix source) f k) f) := by
  rfl

theorem irreducible_hasCommonReachableState {n : ℕ} [Nonempty (Fin n)]
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (hirr : P.IsIrreducible) : HasCommonReachableState P := by
  let root : Fin n := Classical.choice (inferInstance : Nonempty (Fin n))
  refine ⟨root, ?_⟩
  intro i
  obtain ⟨k, _, hk⟩ :=
    (Matrix.isIrreducible_iff_exists_pow_pos hP).mp hirr i root
  exact ⟨k, hk⟩

/-- The old irreducible class embeds in the strictly more general rooted class. -/
theorem accessibleIrreducibleResponseClass_implies_rooted {n : ℕ}
    [Nonempty (Fin n)] (source : SquareSource n)
    (hclass : AccessibleIrreducibleResponseClass source) :
    AccessibleRootedResponseClass source := by
  intro f hf
  obtain ⟨haccessible, hP, hirr⟩ := hclass f hf
  exact ⟨haccessible, hP,
    irreducible_hasCommonReachableState _ hP hirr⟩

theorem accessibleRootedResponseClass_rayStrictLocal {n : ℕ}
    [Nonempty (Fin n)] (source : SquareSource n) (J : ℝ)
    (production : Fin n → ℝ)
    (hclass : AccessibleRootedResponseClass source)
    (hJ : 0 < J) (hproduction : ∀ i, 0 < production i)
    (hmode : ControlledProductionMode source production)
    (f : Fin n → ℝ) (hf : ResponseFeasible (responseMatrix source) f) :
    RayStrictLocalRealizable source J production f := by
  let q := fun k => OptimalAffinityCorrected.responseRatio
    (responseMatrix source) f k
  let h := OptimalAffinityCorrected.responseImage (responseMatrix source) f
  have hfpos : ∀ i, 0 < f i := fun i => (hf i).1
  have hq : ∀ i, 1 < q i := fun i => (hf i).2
  have hresponse : (responseMatrix source).transpose.mulVec f = h := by
    rw [← responseImage_eq_transpose_mulVec]
  have hratio : ∀ i, h i = q i * f i := by
    intro i
    unfold h q OptimalAffinityCorrected.responseRatio
    exact (div_mul_cancel₀ _ (ne_of_gt (hfpos i))).symm
  obtain ⟨haccessible, hP, hroot⟩ := hclass f hf
  exact controlAccessible_commonReachableRouting_rayStrictLocalRealizable
    source J production q f h hJ hproduction hq hfpos hresponse hratio
      hmode hP hroot haccessible

theorem responseValueSet_eq_strictLocalValueSet_of_accessibleRooted {n : ℕ}
    [Nonempty (Fin n)] (source : SquareSource n) (weights : Fin n → ℕ)
    (J : ℝ) (production : Fin n → ℝ)
    (hclass : AccessibleRootedResponseClass source)
    (hJ : 0 < J) (hproduction : ∀ i, 0 < production i)
    (hmode : ControlledProductionMode source production) :
    realizationValueSet (responseMatrix source) weights
        (ResponseFeasible (responseMatrix source)) =
      realizationValueSet (responseMatrix source) weights
        (StrictLocalRealizable source J production) := by
  rw [← rayStrictLocalValueSet_eq_strictLocalValueSet]
  ext z
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, accessibleRootedResponseClass_rayStrictLocal source J production
      hclass hJ hproduction hmode f hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, rayStrictLocalRealizable_responseFeasible source J production f hf, rfl⟩

/-- Sharp local-capacity theorem: irreducibility is replaced by the exact
one-final-class routing condition. -/
theorem responseLayerCapacity_eq_strictLocalCapacity_of_accessibleRooted {n : ℕ}
    [Nonempty (Fin n)] (source : SquareSource n) (weights : Fin n → ℕ)
    (J : ℝ) (production : Fin n → ℝ)
    (hclass : AccessibleRootedResponseClass source)
    (hJ : 0 < J) (hproduction : ∀ i, 0 < production i)
    (hmode : ControlledProductionMode source production) :
    responseLayerCapacity (responseMatrix source) weights =
      strictLocalCapacity source weights J production := by
  unfold responseLayerCapacity strictLocalCapacity realizationCapacity
  rw [responseValueSet_eq_strictLocalValueSet_of_accessibleRooted
    source weights J production hclass hJ hproduction hmode]

end
end OptimalAffinityRealizability
