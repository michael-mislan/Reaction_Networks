import proofs.OptimalAffinityRealizability.RoutingStationary

namespace OptimalAffinityRealizability

open scoped BigOperators
noncomputable section

theorem responseImage_smul {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (a : ℝ) (f : Fin n → ℝ) (j : Fin n) :
    OptimalAffinityCorrected.responseImage T (a • f) j =
      a * OptimalAffinityCorrected.responseImage T f j := by
  simp only [OptimalAffinityCorrected.responseImage, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem responseRatio_smul {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (a : ℝ) (f : Fin n → ℝ) (j : Fin n) (ha : a ≠ 0) :
    OptimalAffinityCorrected.responseRatio T (a • f) j =
      OptimalAffinityCorrected.responseRatio T f j := by
  rw [OptimalAffinityCorrected.responseRatio,
    OptimalAffinityCorrected.responseRatio, responseImage_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ ha

theorem responseObjective_smul {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (weights : Fin n → ℕ) (a : ℝ) (f : Fin n → ℝ) (ha : a ≠ 0) :
    responseObjective T weights (a • f) = responseObjective T weights f := by
  unfold responseObjective OptimalAffinityCorrected.responseObjective
  apply Finset.prod_congr rfl
  intro j hj
  rw [responseRatio_smul T a f j ha]

theorem sameResponseRay_responseObjective {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (weights : Fin n → ℕ)
    (f f' : Fin n → ℝ) (hray : SameResponseRay f f') :
    responseObjective T weights f' = responseObjective T weights f := by
  rcases hray with ⟨a, ha, rfl⟩
  exact responseObjective_smul T weights a f (ne_of_gt ha)

theorem responseFeasible_smul_iff {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) (f : Fin n → ℝ) (ha : 0 < a) :
    ResponseFeasible T (a • f) ↔ ResponseFeasible T f := by
  constructor
  · intro hf j
    have hj := hf j
    constructor
    · simp only [Pi.smul_apply, smul_eq_mul] at hj
      nlinarith [hj.1]
    · simpa only [responseRatio_smul T a f j (ne_of_gt ha)] using hj.2
  · intro hf j
    refine ⟨?_, ?_⟩
    · simpa only [Pi.smul_apply, smul_eq_mul] using mul_pos ha (hf j).1
    · simpa only [responseRatio_smul T a f j (ne_of_gt ha)] using (hf j).2

theorem sameResponseRay_responseFeasible_iff {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (f f' : Fin n → ℝ)
    (hray : SameResponseRay f f') :
    ResponseFeasible T f' ↔ ResponseFeasible T f := by
  rcases hray with ⟨a, ha, rfl⟩
  exact responseFeasible_smul_iff T a f ha

theorem rayStrictLocalRealizable_responseFeasible {n : ℕ}
    (source : SquareSource n) (J : ℝ) (production f : Fin n → ℝ)
    (hray : RayStrictLocalRealizable source J production f) :
    ResponseFeasible (responseMatrix source) f := by
  rcases hray with ⟨f', hff', hstrict⟩
  exact (sameResponseRay_responseFeasible_iff (responseMatrix source) f f' hff').mp
    (firstOrderRealizable_responseFeasible source J production f'
      (regularBranchRealizable_firstOrder source J production f'
        (strictLocalRealizable_regularBranch source J production f' hstrict)))

def rayStrictLocalCapacity {n : ℕ} (source : SquareSource n)
    (weights : Fin n → ℕ) (J : ℝ) (production : Fin n → ℝ) : ℝ :=
  realizationCapacity (responseMatrix source) weights
    (RayStrictLocalRealizable source J production)

theorem rayStrictLocalValueSet_eq_strictLocalValueSet {n : ℕ}
    (source : SquareSource n) (weights : Fin n → ℕ) (J : ℝ)
    (production : Fin n → ℝ) :
    realizationValueSet (responseMatrix source) weights
        (RayStrictLocalRealizable source J production) =
      realizationValueSet (responseMatrix source) weights
        (StrictLocalRealizable source J production) := by
  ext z
  constructor
  · rintro ⟨f, ⟨f', hff', hstrict⟩, rfl⟩
    exact ⟨f', hstrict, (sameResponseRay_responseObjective
      (responseMatrix source) weights f f' hff').symm⟩
  · rintro ⟨f, hstrict, rfl⟩
    refine ⟨f, ⟨f, ?_, hstrict⟩, rfl⟩
    exact ⟨1, zero_lt_one, by simp⟩

theorem rayStrictLocalCapacity_eq_strictLocalCapacity {n : ℕ}
    (source : SquareSource n) (weights : Fin n → ℕ) (J : ℝ)
    (production : Fin n → ℝ) :
    rayStrictLocalCapacity source weights J production =
      strictLocalCapacity source weights J production := by
  unfold rayStrictLocalCapacity strictLocalCapacity realizationCapacity
  rw [rayStrictLocalValueSet_eq_strictLocalValueSet]

/-- A literal source class on which every response-feasible ray enters the
Perron-realizable irreducible routing regime. -/
def AccessibleIrreducibleResponseClass {n : ℕ} [Nonempty (Fin n)]
    (source : SquareSource n) : Prop :=
  ∀ f : Fin n → ℝ, ResponseFeasible (responseMatrix source) f →
    ControlAccessible source f ∧
    (∀ i j, 0 ≤ routingMatrix (responseMatrix source)
      (fun k => OptimalAffinityCorrected.responseRatio (responseMatrix source) f k)
      f i j) ∧
    (routingMatrix (responseMatrix source)
      (fun k => OptimalAffinityCorrected.responseRatio (responseMatrix source) f k)
      f).IsIrreducible

theorem accessibleIrreducibleResponseClass_rayStrictLocal {n : ℕ}
    [Nonempty (Fin n)] (source : SquareSource n) (J : ℝ)
    (production : Fin n → ℝ)
    (hclass : AccessibleIrreducibleResponseClass source)
    (hJ : 0 < J) (hproduction : ∀ i, 0 < production i)
    (hmode : ControlledProductionMode source production)
    (f : Fin n → ℝ) (hf : ResponseFeasible (responseMatrix source) f) :
    RayStrictLocalRealizable source J production f := by
  let q := fun k => OptimalAffinityCorrected.responseRatio (responseMatrix source) f k
  let h := OptimalAffinityCorrected.responseImage (responseMatrix source) f
  have hfpos : ∀ i, 0 < f i := fun i => (hf i).1
  have hq : ∀ i, 1 < q i := fun i => (hf i).2
  have hresponse : (responseMatrix source).transpose.mulVec f = h := by
    rw [← responseImage_eq_transpose_mulVec]
  have hratio : ∀ i, h i = q i * f i := by
    intro i
    unfold h q OptimalAffinityCorrected.responseRatio
    exact (div_mul_cancel₀ _ (ne_of_gt (hfpos i))).symm
  obtain ⟨haccessible, hP, hirr⟩ := hclass f hf
  exact controlAccessible_irreducibleRouting_rayStrictLocalRealizable
    source J production q f h hJ hproduction hq hfpos hresponse hratio
      hmode hP hirr haccessible

theorem responseValueSet_eq_strictLocalValueSet_of_accessibleIrreducible {n : ℕ}
    [Nonempty (Fin n)] (source : SquareSource n) (weights : Fin n → ℕ)
    (J : ℝ) (production : Fin n → ℝ)
    (hclass : AccessibleIrreducibleResponseClass source)
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
    exact ⟨f, accessibleIrreducibleResponseClass_rayStrictLocal source J
      production hclass hJ hproduction hmode f hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, rayStrictLocalRealizable_responseFeasible source J production f hf, rfl⟩

theorem responseLayerCapacity_eq_strictLocalCapacity_of_accessibleIrreducible {n : ℕ}
    [Nonempty (Fin n)] (source : SquareSource n) (weights : Fin n → ℕ)
    (J : ℝ) (production : Fin n → ℝ)
    (hclass : AccessibleIrreducibleResponseClass source)
    (hJ : 0 < J) (hproduction : ∀ i, 0 < production i)
    (hmode : ControlledProductionMode source production) :
    responseLayerCapacity (responseMatrix source) weights =
      strictLocalCapacity source weights J production := by
  unfold responseLayerCapacity strictLocalCapacity realizationCapacity
  rw [responseValueSet_eq_strictLocalValueSet_of_accessibleIrreducible
    source weights J production hclass hJ hproduction hmode]

end
end OptimalAffinityRealizability
