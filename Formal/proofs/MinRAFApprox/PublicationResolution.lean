import proofs.MinRAFApprox.Resolution
import proofs.MinRAFApprox.Gadgets.FiniteSupport
import proofs.MinRAFApprox.EncodingSize
import proofs.MinRAFApprox.NumericalEstimates
import proofs.MinRAFApprox.UnboundedIrreducible

/-!
This is the warning-free publication entry point.  Its imports jointly check
the exact SET COVER/RAF correspondence, affine objective identity,
approximation and complexity transfer, finite-support and encoding bounds,
gap arithmetic, and the irreducible-RAF corollaries used in the paper.
-/

namespace MinRAFApprox.SetCoverSource

open RAF MinRAFApprox.Reaction

/-- Publication-level restatement of the principal resolution theorem. -/
theorem publication_constant_factor_resolution
    (P_eq_NP : Prop)
    (PolynomialCover : CoverAlgorithm → Prop)
    (PolynomialRAF : SourceRAFAlgorithm → Prop)
    (setCoverHardness : ¬ P_eq_NP →
      NoPolynomialCoverConstApprox PolynomialCover)
    (reductionPolynomial : ∀ A, PolynomialRAF A →
      PolynomialCover (inducedCover A)) :
    ¬ P_eq_NP → NoPolynomialSourceRAFConstApprox PolynomialRAF :=
  constant_factor_approximation_resolution P_eq_NP PolynomialCover
    PolynomialRAF setCoverHardness reductionPolynomial

end MinRAFApprox.SetCoverSource
