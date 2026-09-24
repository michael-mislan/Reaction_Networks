import proofs.IrrRAFEnumeration.CompletionOriginalInput
import proofs.IrrRAFEnumeration.CompletionLabelTransport
import proofs.IrrRAFEnumeration.NegativeClassification

namespace IrrRAFEnumeration
open EnumerationContract CompletionQuery

/-- Under P=NP one fixed machine starts from the original CRS encoding,
writes exactly its irreducible RAFs, and has an output-polynomial total runtime. -/
theorem outputPolynomialEnumeration_of_P_eq_NP
    (h : Complexity.P = Complexity.NP) : OutputPolynomialEnumeration := by
  exact outputPolynomialEnumeration_of_initializer h
    (fun k => ⟨24,originalInitializerTM k,originalInitializerPolynomial,
      originalInitializer_correct k⟩)
    (fun _ E p hE => enumerates_of_finEnumerates E p hE)

/-- Exact classification for all finite ordinary catalytic reaction systems. -/
theorem outputPolynomialEnumeration_iff_P_eq_NP :
    EnumerationContract.OutputPolynomialEnumeration ↔ Complexity.P = Complexity.NP :=
  ⟨P_eq_NP_of_outputPolynomialEnumeration,outputPolynomialEnumeration_of_P_eq_NP⟩

end IrrRAFEnumeration
