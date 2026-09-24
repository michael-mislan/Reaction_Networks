import proofs.OptimalAffinityRealizability.StrictLocalMaximum

namespace OptimalAffinityRealizability

open Filter
noncomputable section

/-- Source-level data sufficient for a regular positive kinetic branch whose
controlled production current has a strict local maximum.  The response
vectors are retained explicitly so the certificate can be checked directly
from the source matrices. -/
structure RegularStrictLocalSourceCertificate {n : ℕ} (source : SquareSource n)
    (J : ℝ) (g q f h u lambda : Fin n → ℝ) : Prop where
  positiveCurrent : 0 < J
  positiveProduction : ∀ i, 0 < g i
  positiveRatio : ∀ i, 1 < q i
  positiveResponse : ∀ i, 0 < f i
  productionMode : ControlledProductionMode source g
  algebraic : AlgebraicBranchCertificate source J g q f h u lambda
  reactantResponse : source.reactant.transpose.mulVec u = f
  productResponse : source.product.transpose.mulVec u = h
  responseRatio : ∀ i, h i = q i * f i
  leftNonnegative : ∀ i, 0 ≤ lambda i
  leftNonzero : lambda ≠ 0
  normalizedControl : u source.controlled = 1

/-- The primitive response/routing hypotheses assemble the full source-level
certificate.  Positivity of the left nullvector pairing supplies the
transversality condition rather than requiring it as an extra assumption. -/
theorem exists_regularStrictLocalSourceCertificate {n : ℕ} [Nonempty (Fin n)]
    (source : SquareSource n) (J : ℝ) (g q f h u lambda : Fin n → ℝ)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i) (hq : ∀ i, 1 < q i)
    (hf : ∀ i, 0 < f i)
    (hresponse : (responseMatrix source).transpose.mulVec f = h)
    (hratio : ∀ i, h i = q i * f i)
    (hmode : ControlledProductionMode source g)
    (hP : ∀ i j, 0 ≤ routingMatrix (responseMatrix source) q f i j)
    (hirr : (routingMatrix (responseMatrix source) q f).IsIrreducible)
    (hreactant : source.reactant.transpose.mulVec u = f)
    (hleft : (literalCurrentJacobian source J g q).transpose.mulVec lambda = 0)
    (hlambda : ∀ i, 0 ≤ lambda i) (hlambda0 : lambda ≠ 0)
    (hcontrol : u source.controlled = 1) :
    RegularStrictLocalSourceCertificate source J g q f h u lambda := by
  have htransverse : dotProduct lambda g ≠ 0 :=
    ne_of_gt (dotProduct_pos_of_nonnegative_nonzero_left lambda g
      hlambda hlambda0 hg)
  have hcontrol0 : u source.controlled ≠ 0 := by
    rw [hcontrol]
    norm_num
  have halgebraic : AlgebraicBranchCertificate source J g q f h u lambda :=
    exists_algebraicBranchCertificate source J g q f h u lambda
      hJ hg hq hf hresponse hratio hmode hP hirr hreactant hleft
        htransverse hcontrol0
  have hu : u = responseTangent source f := by
    apply reactantTranspose_mulVec_injective source
    rw [hreactant, reactantResponse_responseTangent]
  have hproduct : source.product.transpose.mulVec u = h := by
    calc
      source.product.transpose.mulVec u =
          source.product.transpose.mulVec (responseTangent source f) := by rw [hu]
      _ = productResponse source f := rfl
      _ = (responseMatrix source).transpose.mulVec f :=
        productResponse_eq_responseMatrix_transpose_mulVec source f
      _ = h := hresponse
  exact {
    positiveCurrent := hJ
    positiveProduction := hg
    positiveRatio := hq
    positiveResponse := hf
    productionMode := hmode
    algebraic := halgebraic
    reactantResponse := hreactant
    productResponse := hproduct
    responseRatio := hratio
    leftNonnegative := hlambda
    leftNonzero := hlambda0
    normalizedControl := hcontrol
  }

/-- A checkable regular source certificate realizes a positive stationary
local log-concentration branch, and the actual controlled production current
on the canonical smooth branch has a strict punctured-neighborhood maximum. -/
theorem regularStrictLocalSourceRealization {n : ℕ} (source : SquareSource n)
    (J : ℝ) (g q f h u lambda : Fin n → ℝ)
    (cert : RegularStrictLocalSourceCertificate source J g q f h u lambda) :
    Nonempty (LocalPositiveLogBranch source J g q) ∧
      IsStrictLocalMaxAt (controlledBranchFlux source J g q
        (smoothLocalBranch source J g q cert.algebraic.reducedSteady)) 0 := by
  have hkernel : (literalCurrentJacobian source J g q).mulVec u = 0 :=
    (cert.algebraic.currentKernel u).2 ⟨1, by simp⟩
  have hfsource : ∀ i, 0 < source.reactant.transpose.mulVec u i := by
    intro i
    rw [cert.reactantResponse]
    exact cert.positiveResponse i
  have hhsource : ∀ i, 0 < source.product.transpose.mulVec u i := by
    intro i
    rw [cert.productResponse, cert.responseRatio i]
    exact mul_pos (lt_trans zero_lt_one (cert.positiveRatio i))
      (cert.positiveResponse i)
  have hratioSource : ∀ i, source.product.transpose.mulVec u i =
      q i * source.reactant.transpose.mulVec u i := by
    intro i
    rw [cert.productResponse, cert.reactantResponse, cert.responseRatio i]
  have hannih : ∀ w : Fin n → ℝ,
      dotProduct lambda ((literalCurrentJacobian source J g q).mulVec w) = 0 := by
    intro w
    calc
      dotProduct lambda ((literalCurrentJacobian source J g q).mulVec w) =
          dotProduct w
            ((literalCurrentJacobian source J g q).transpose.mulVec lambda) := by
              exact (Matrix.dotProduct_transpose_mulVec
                (literalCurrentJacobian source J g q) w lambda).symm
      _ = 0 := by rw [cert.algebraic.leftNull]; simp
  constructor
  · exact exists_localPositiveLogBranch source J g q cert.positiveCurrent
      cert.positiveProduction cert.positiveRatio cert.productionMode
      cert.algebraic.reducedSteady
  · exact smoothLocalBranch_flux_isStrictLocalMax source J g q u lambda
      cert.positiveCurrent cert.positiveProduction hfsource hhsource
      cert.leftNonnegative cert.leftNonzero cert.positiveRatio hratioSource
      cert.productionMode cert.algebraic.reducedSteady hkernel
      cert.normalizedControl hannih

end
end OptimalAffinityRealizability
