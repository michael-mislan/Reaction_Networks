import proofs.IrrRAFEnumeration.SATCountMachine
import proofs.IrrRAFEnumeration.SyntaxGuard
import proofs.Complexitylib.Classes.P.NormalForm

namespace IrrRAFEnumeration.SATSource
open Complexity Complexity.TM InitializedCountDecision SyntaxGuard

/-- This weaker, necessary consequence of exact source enumeration already
places the actual SAT language in P. No simulator or verifier is an axiom. -/
theorem SAT_mem_P_of_sourceCountBound {k : Nat} (E : TM k) (p : Polynomial Nat)
    (hE : SourceCountBound E p) : SAT.language ∈ Complexity.P := by
  have hne : (rawSATDecision E p).qstart ≠ (rawSATDecision E p).qhalt := by
    intro h
    cases h
  have hd := guarded_correct (rawSATDecision E p) hne
    (decisionPolynomial (sourceDeadline p)).eval (rawSATDecision_correct E p hE.start_ne_halt hE)
  apply mem_P_iff_decidesInTime_polynomial.mpr
  refine ⟨_,guardedTM (rawSATDecision E p),
    decisionPolynomial (sourceDeadline p)+Polynomial.C 2*Polynomial.X+Polynomial.C 14,?_⟩
  simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using hd

end IrrRAFEnumeration.SATSource
