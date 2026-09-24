import proofs.IrrRAFEnumeration.SourceCountContract
import proofs.IrrRAFEnumeration.SATRawSourceCompiler
import proofs.IrrRAFEnumeration.SourceDeadlineBudget
import proofs.IrrRAFEnumeration.AxiomHeaderDecision

namespace IrrRAFEnumeration.SATSource
open Complexity SAT Complexity.TM SATCompletion HeaderComparison PointwiseComposition

def sourceEnumeratorTM {k : Nat} (E : TM k) := compositionTM rawSourceCompilerTM E

theorem source_enumerator_run {k : Nat} (E : TM k) (p : Polynomial Nat)
    (hne : E.qstart ≠ E.qhalt) (hE : SourceCountBound E p) (φ : CNF) :
    ∃ (body : List Bool) (c : Cfg _ (sourceEnumeratorTM E).Q) (t : Nat),
      t ≤ 2*(1000000000000000*(φ.encode.length+2)^10)+
        2*(sourceBits (libraryRect φ (φ.encode.length+2))).length+11+
        p.eval ((sourceBits (libraryRect φ (φ.encode.length+2))).length+
          fixedWidthOutputLength (reactionCount (φ.encode.length+2) φ.length)
            (sourceCount (libraryRect φ (φ.encode.length+2)))) ∧
      (sourceEnumeratorTM E).reachesIn t ((sourceEnumeratorTM E).initCfg φ.encode) c ∧
      (sourceEnumeratorTM E).halted c ∧
      c.output.HasOutput (List.replicate (sourceCount (libraryRect φ (φ.encode.length+2))) true ++ false :: body) := by
  obtain ⟨body,c,t,_,ht,hr,hh,ho⟩ := hE (φ.encode.length+2) φ.length
    (libraryRect φ (φ.encode.length+2)) (by omega)
  obtain ⟨d,u,hu,hd,hh',ho'⟩ := compose_runs rawSourceCompilerTM E hne φ.encode
    (sourceBits (libraryRect φ (φ.encode.length+2)))
    (List.replicate (sourceCount (libraryRect φ (φ.encode.length+2))) true ++ false :: body)
    _ _ (rawSourceCompilerTM_correct φ) ⟨c,t,ht,hr,hh,ho⟩
  exact ⟨body,d,u,hu,hd,hh',ho'⟩

theorem source_enumerator_header {k : Nat} (E : TM k) (p : Polynomial Nat)
    (hne : E.qstart ≠ E.qhalt) (hE : SourceCountBound E p) (φ : CNF)
    (c : Cfg _ (sourceEnumeratorTM E).Q) (t : Nat)
    (hr : (sourceEnumeratorTM E).reachesIn t ((sourceEnumeratorTM E).initCfg φ.encode) c)
    (hh : (sourceEnumeratorTM E).halted c) :
    UnaryPrefix (parkOutput c.output) (sourceCount (libraryRect φ (φ.encode.length+2))) Γ.zero := by
  obtain ⟨body,d,u,_,hd,hhd,ho⟩ := source_enumerator_run E p hne hE φ
  have he := halted_runs_equal (sourceEnumeratorTM E) hr hd hh hhd
  subst d
  exact AxiomSource.output_has_unary_prefix _ _ body ho

theorem source_enumerator_no_case {k : Nat} (E : TM k) (p : Polynomial Nat)
    (hne : E.qstart ≠ E.qhalt) (hE : SourceCountBound E p) (φ : CNF)
    (hno : ¬ φ.Satisfiable) :
    ∃ c t, t ≤ (sourceDeadline p).eval φ.encode.length ∧
      (sourceEnumeratorTM E).reachesIn t ((sourceEnumeratorTM E).initCfg φ.encode) c ∧
      (sourceEnumeratorTM E).halted c := by
  obtain ⟨_,c,t,ht,hr,hh,_⟩ := source_enumerator_run E p hne hE φ
  have hcount : sourceCount (libraryRect φ (φ.encode.length+2)) = φ.encode.length+2 :=
    (sourceCount_eq_baseline (by omega) _).mpr (fun h => hno ((libraryRect_encode_satisfiable φ).mp h))
  rw [hcount] at ht
  have hlen : fixedWidthOutputLength (reactionCount (φ.encode.length+2) φ.length)
      (φ.encode.length+2) = (baselineBits (φ.encode.length+2) φ.length).length := by
    rw [baselineBits_length]
    rfl
  rw [hlen] at ht
  exact ⟨c,t,ht.trans (composed_no_case_deadline p φ),hr,hh⟩

end IrrRAFEnumeration.SATSource
