import proofs.IrrRAFEnumeration.EnumerationContract
import proofs.IrrRAFEnumeration.SATMembership
import proofs.Complexitylib.SAT.CookLevin.Assembly

namespace IrrRAFEnumeration
open Complexity EnumerationContract

/-- Exact output-polynomial enumeration of all ordinary irrRAFs would collapse
the actual machine-based P and NP classes. -/
theorem P_eq_NP_of_outputPolynomialEnumeration
    (h : OutputPolynomialEnumeration) : Complexity.P = Complexity.NP := by
  obtain ⟨k,E,p,hE⟩ := h
  exact SAT.NPComplete_language.2.P_eq_NP_of_mem_P
    (SATSource.SAT_mem_P_of_sourceCountBound E p hE.sourceCountBound)

end IrrRAFEnumeration
