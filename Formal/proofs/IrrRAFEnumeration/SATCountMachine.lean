import proofs.IrrRAFEnumeration.SourceEnumeratorRun
import proofs.IrrRAFEnumeration.InitializedCountDecision

namespace IrrRAFEnumeration.SATSource
open Complexity SAT Complexity.TM InitializedCountDecision

noncomputable def rawSATDecision {k : Nat} (E : TM k) (p : Polynomial Nat) :=
  countDecisionTM (sourceEnumeratorTM E) (sourceDeadline p)

/-- On every valid raw formula, an output-polynomial source enumerator gives
a genuine polynomial-time SAT decision run, including all machine overhead. -/
theorem rawSATDecision_correct {k : Nat} (E : TM k) (p : Polynomial Nat)
    (hne : E.qstart ≠ E.qhalt) (hE : SourceCountBound E p) (φ : CNF) :
    ∃ c t, t ≤ (decisionPolynomial (sourceDeadline p)).eval φ.encode.length ∧
      (rawSATDecision E p).reachesIn t ((rawSATDecision E p).initCfg φ.encode) c ∧
      (rawSATDecision E p).halted c ∧
      (φ.Satisfiable → c.output.cells 1 = Γ.one) ∧
      (¬ φ.Satisfiable → c.output.cells 1 = Γ.zero) := by
  have hstart : (sourceEnumeratorTM E).qstart ≠ (sourceEnumeratorTM E).qhalt := by
    intro h
    cases h
  obtain ⟨c,t,b,ht,hr,hh,hb,hv⟩ := initialized_count_correct (sourceEnumeratorTM E)
    hstart (sourceDeadline p) φ.encode (sourceCount (libraryRect φ (φ.encode.length+2)))
    (source_enumerator_header E p hne hE φ)
  have heq : sourceCount (libraryRect φ (φ.encode.length+2)) = φ.encode.length+2 ↔
      ¬ φ.Satisfiable := by
    rw [sourceCount_eq_baseline (by omega),libraryRect_encode_satisfiable]
  refine ⟨c,t,?_,hr,hh,?_,?_⟩
  · simpa only [decisionPolynomial_eval] using ht
  · intro hy
    have hn : sourceCount (libraryRect φ (φ.encode.length+2)) ≠ φ.encode.length+2 :=
      fun h => heq.mp h hy
    simpa [hn,Γ.ofBool] using hv
  · intro hn
    obtain ⟨d,u,hu,hd,hhd⟩ := source_enumerator_no_case E p hne hE φ hn
    have hbtrue : b = true := hb.mpr ⟨d,u,by omega,hd,hhd⟩
    simpa [hbtrue,heq.mpr hn,Γ.ofBool] using hv

end IrrRAFEnumeration.SATSource
