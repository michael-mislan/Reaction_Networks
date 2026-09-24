import proofs.OptimalAffinityRealizability.SourceLocalRealization

namespace OptimalAffinityRealizability

open scoped BigOperators
noncomputable section

/-- The inherited response-cone feasibility layer. -/
abbrev ResponseFeasible {n : ℕ} (T : Fin n → Fin n → ℝ)
    (f : Fin n → ℝ) : Prop :=
  OptimalAffinityCorrected.ForwardResponse T f

/-- The response ray points in the positive controlled direction. -/
def ControlAccessible {n : ℕ} (source : SquareSource n)
    (f : Fin n → ℝ) : Prop :=
  0 < controlCovector source f

/-- A response profile together with a literal first-order source witness. -/
structure FirstOrderRealizationWitness {n : ℕ} (source : SquareSource n) (J : ℝ)
    (production f : Fin n → ℝ) where
  q : Fin n → ℝ
  h : Fin n → ℝ
  positiveResponse : ∀ i, 0 < f i
  positiveRatio : ∀ i, 1 < q i
  responseEquation : (responseMatrix source).transpose.mulVec f = h
  ratioEquation : ∀ i, h i = q i * f i
  realization : FirstOrderSourceRealization source J production q f h

/-- A response profile with the finite algebraic regularity certificate needed
for a normalized local branch. -/
structure RegularBranchRealizationWitness {n : ℕ} (source : SquareSource n) (J : ℝ)
    (production f : Fin n → ℝ) where
  q : Fin n → ℝ
  h : Fin n → ℝ
  u : Fin n → ℝ
  lambda : Fin n → ℝ
  positiveResponse : ∀ i, 0 < f i
  positiveRatio : ∀ i, 1 < q i
  responseEquation : (responseMatrix source).transpose.mulVec f = h
  ratioEquation : ∀ i, h i = q i * f i
  reactantResponse : source.reactant.transpose.mulVec u = f
  normalizedControl : u source.controlled = 1
  algebraic : AlgebraicBranchCertificate source J production q f h u lambda

/-- A response profile with the full certificate already proved to yield an
actual strict local controlled-flux maximum. -/
structure StrictLocalRealizationWitness {n : ℕ} (source : SquareSource n) (J : ℝ)
    (production f : Fin n → ℝ) where
  q : Fin n → ℝ
  h : Fin n → ℝ
  u : Fin n → ℝ
  lambda : Fin n → ℝ
  certificate : RegularStrictLocalSourceCertificate source J production q
    f h u lambda

def FirstOrderRealizable {n : ℕ} (source : SquareSource n) (J : ℝ)
    (production f : Fin n → ℝ) : Prop :=
  Nonempty (FirstOrderRealizationWitness source J production f)

def RegularBranchRealizable {n : ℕ} (source : SquareSource n) (J : ℝ)
    (production f : Fin n → ℝ) : Prop :=
  Nonempty (RegularBranchRealizationWitness source J production f)

def StrictLocalRealizable {n : ℕ} (source : SquareSource n) (J : ℝ)
    (production f : Fin n → ℝ) : Prop :=
  Nonempty (StrictLocalRealizationWitness source J production f)

/-- Realizability is physically a property of a positive response ray; the
representative with controlled tangent one carries the kinetic certificate. -/
def RayStrictLocalRealizable {n : ℕ} (source : SquareSource n) (J : ℝ)
    (production f : Fin n → ℝ) : Prop :=
  ∃ f', SameResponseRay f f' ∧ StrictLocalRealizable source J production f'

theorem responseImage_eq_transpose_mulVec {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → ℝ) :
    OptimalAffinityCorrected.responseImage T f = T.transpose.mulVec f := by
  funext i
  change (∑ x, f x * T x i) = ∑ x, T x i * f x
  apply Finset.sum_congr rfl
  intro x hx
  exact mul_comm _ _

theorem firstOrderRealizable_responseFeasible {n : ℕ}
    (source : SquareSource n) (J : ℝ) (production f : Fin n → ℝ)
    (r : FirstOrderRealizable source J production f) :
    ResponseFeasible (responseMatrix source) f := by
  obtain ⟨r⟩ := r
  intro i
  refine ⟨r.positiveResponse i, ?_⟩
  calc
    1 < r.q i := r.positiveRatio i
    _ = OptimalAffinityCorrected.responseRatio (responseMatrix source) f i := by
      rw [OptimalAffinityCorrected.responseRatio,
        responseImage_eq_transpose_mulVec, r.responseEquation,
        r.ratioEquation i]
      exact (mul_div_cancel_right₀ (r.q i) (ne_of_gt (r.positiveResponse i))).symm

theorem regularBranchRealizable_firstOrder {n : ℕ}
    (source : SquareSource n) (J : ℝ) (production f : Fin n → ℝ)
    (r : RegularBranchRealizable source J production f) :
    FirstOrderRealizable source J production f := by
  obtain ⟨r⟩ := r
  exact ⟨{
    q := r.q
    h := r.h
    positiveResponse := r.positiveResponse
    positiveRatio := r.positiveRatio
    responseEquation := r.responseEquation
    ratioEquation := r.ratioEquation
    realization := r.algebraic.firstOrder
  }⟩

theorem strictLocalRealizable_regularBranch {n : ℕ}
    (source : SquareSource n) (J : ℝ) (production f : Fin n → ℝ)
    (r : StrictLocalRealizable source J production f) :
    RegularBranchRealizable source J production f := by
  obtain ⟨r⟩ := r
  let cert := r.certificate
  have hu : r.u = responseTangent source f := by
    apply reactantTranspose_mulVec_injective source
    rw [cert.reactantResponse, reactantResponse_responseTangent]
  have hresponse : (responseMatrix source).transpose.mulVec f = r.h := by
    calc
      (responseMatrix source).transpose.mulVec f = productResponse source f :=
        (productResponse_eq_responseMatrix_transpose_mulVec source f).symm
      _ = source.product.transpose.mulVec r.u := by
        simp only [productResponse]
        rw [← hu]
      _ = r.h := cert.productResponse
  exact ⟨{
    q := r.q
    h := r.h
    u := r.u
    lambda := r.lambda
    positiveResponse := cert.positiveResponse
    positiveRatio := cert.positiveRatio
    responseEquation := hresponse
    ratioEquation := cert.responseRatio
    reactantResponse := cert.reactantResponse
    normalizedControl := cert.normalizedControl
    algebraic := cert.algebraic
  }⟩

/-- Objective values admitted by an arbitrary profile layer. -/
def realizationValueSet {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (weights : Fin n → ℕ) (P : (Fin n → ℝ) → Prop) : Set ℝ :=
  {z | ∃ f, P f ∧ z = responseObjective T weights f}

/-- The infimum at an arbitrary realizability layer. -/
noncomputable def realizationCapacity {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (weights : Fin n → ℕ) (P : (Fin n → ℝ) → Prop) : ℝ :=
  sInf (realizationValueSet T weights P)

/-- The inherited response capacity expressed through the generic layer API. -/
noncomputable def responseLayerCapacity {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (weights : Fin n → ℕ) : ℝ :=
  realizationCapacity T weights (ResponseFeasible T)

/-- The source- and control-aware regular local capacity. -/
noncomputable def regularCapacity {n : ℕ} (source : SquareSource n)
    (weights : Fin n → ℕ) (J : ℝ) (production : Fin n → ℝ) : ℝ :=
  realizationCapacity (responseMatrix source) weights
    (RegularBranchRealizable source J production)

/-- The certified strict-local kinetic capacity. -/
noncomputable def strictLocalCapacity {n : ℕ} (source : SquareSource n)
    (weights : Fin n → ℕ) (J : ℝ) (production : Fin n → ℝ) : ℝ :=
  realizationCapacity (responseMatrix source) weights
    (StrictLocalRealizable source J production)

theorem responseLayerCapacity_eq_responseProfileBound {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (weights : Fin n → ℕ) :
    responseLayerCapacity T weights = responseProfileBound T weights := by
  rfl

/-- First-order source realizability cannot beat the inherited response
relaxation. -/
theorem responseBound_le_firstOrderObjective {n : ℕ}
    (source : SquareSource n) (weights : Fin n → ℕ) (J : ℝ)
    (production f : Fin n → ℝ)
    (r : FirstOrderRealizable source J production f) :
    responseProfileBound (responseMatrix source) weights ≤
      responseObjective (responseMatrix source) weights f :=
  inheritedResponseBound (responseMatrix source) weights f
    (firstOrderRealizable_responseFeasible source J production f r)

/-- Regular local branch realizability inherits the response lower bound. -/
theorem responseBound_le_regularObjective {n : ℕ}
    (source : SquareSource n) (weights : Fin n → ℕ) (J : ℝ)
    (production f : Fin n → ℝ)
    (r : RegularBranchRealizable source J production f) :
    responseProfileBound (responseMatrix source) weights ≤
      responseObjective (responseMatrix source) weights f :=
  responseBound_le_firstOrderObjective source weights J production f
    (regularBranchRealizable_firstOrder source J production f r)

/-- Certified strict-local kinetic realizability inherits the response lower
bound through the explicit layer adapters. -/
theorem responseBound_le_strictLocalObjective {n : ℕ}
    (source : SquareSource n) (weights : Fin n → ℕ) (J : ℝ)
    (production f : Fin n → ℝ)
    (r : StrictLocalRealizable source J production f) :
    responseProfileBound (responseMatrix source) weights ≤
      responseObjective (responseMatrix source) weights f :=
  responseBound_le_regularObjective source weights J production f
    (strictLocalRealizable_regularBranch source J production f r)

theorem responseBound_le_regularCapacity {n : ℕ}
    (source : SquareSource n) (weights : Fin n → ℕ) (J : ℝ)
    (production : Fin n → ℝ)
    (hne : (realizationValueSet (responseMatrix source) weights
      (RegularBranchRealizable source J production)).Nonempty) :
    responseProfileBound (responseMatrix source) weights ≤
      regularCapacity source weights J production := by
  unfold regularCapacity realizationCapacity
  apply le_csInf hne
  intro z hz
  rcases hz with ⟨f, hf, rfl⟩
  exact responseBound_le_regularObjective source weights J production f hf

theorem responseBound_le_strictLocalCapacity {n : ℕ}
    (source : SquareSource n) (weights : Fin n → ℕ) (J : ℝ)
    (production : Fin n → ℝ)
    (hne : (realizationValueSet (responseMatrix source) weights
      (StrictLocalRealizable source J production)).Nonempty) :
    responseProfileBound (responseMatrix source) weights ≤
      strictLocalCapacity source weights J production := by
  unfold strictLocalCapacity realizationCapacity
  apply le_csInf hne
  intro z hz
  rcases hz with ⟨f, hf, rfl⟩
  exact responseBound_le_strictLocalObjective source weights J production f hf

end
end OptimalAffinityRealizability
