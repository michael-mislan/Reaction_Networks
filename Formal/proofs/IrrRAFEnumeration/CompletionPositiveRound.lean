import proofs.IrrRAFEnumeration.CompletionOuterQuery

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM PolynomialClockSetup

def positiveRoundTM {k : Nat} (q : Polynomial Nat) (M : TM k) :=
  seqTM (clearRegTM (enumFlag k)) (seqTM (minimizeCommitTM q M) (roundResetTM k))

/-- A positive completion verdict drives an actual successful round and returns
to the same full-universe query boundary with one additional recorded minimum. -/
theorem positiveRoundTM_correct {d r k : Nat} (q : Polynomial Nat)
    (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r)))
    (hU : PositiveCompletion.Available (IsRAF Q C) G.toFinset Finset.univ)
    (M : TM k) (T : Nat → Nat) (hM : M.DecidesInTime SAT.language T)
    (hq : ∀ L, q.eval L = T L+L+2) (inp : Tape) (hp : Parked inp) :
    let base := SAT.CNF.encode (assembledBase Q C)
    let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
    ∃ (cost : Fin r → Nat) (V : Finset (Fin r)),
      (∀ i, ∃ W : Finset (Fin r), cost i = completionCallTime k q T r base.length blocks.length
        (SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
          PositiveCompletionCNF.containerExclusions W)).length) ∧
      Minimal (IsRAF Q C) V ∧ V ∉ G.toFinset ∧
      (positiveRoundTM q M).HoareTime
        (EmitPred inp (enumFlagWork k (Finset.univ : Finset (Fin r)) base blocks (storedMasks G) 0 G.length 1) [])
        (EmitPred inp (enumWork k (Finset.univ : Finset (Fin r)) base
          (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers (G++[V])))
          (storedMasks (G++[V])) 0 (G++[V]).length) [])
        (6+1+(r*((∑ i, cost i)+12*r+33)+(r+2)+1+
          (2*r+6+blockerCommitTime r blocks.length (SAT.CNF.encode [blockerClause V]).length+
            1+2*G.length+4))+1+(7*r*r+20*r+12)) := by
  dsimp only
  let base := SAT.CNF.encode (assembledBase Q C)
  let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
  obtain ⟨cost,V,hcost,hV,hnew,hm⟩ := minimizeCommitTM_correct q Q C G Finset.univ hU M T hM hq inp hp
  have hc := clearRegTM_hoareTime (enumFlag k) 1 inp
    (enumFlagWork k (Finset.univ : Finset (Fin r)) base blocks (storedMasks G) 0 G.length 1) [] hp
    (fun i _ => enumFlagWork_parked _ _ _ _ _ _ _ _ i) (enumFlagWork_flag _ _ _ _ _ _ _ _)
  rw [enumFlagWork_update_flag] at hc
  have hr := roundResetTM_correct k V base
    (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers (G++[V])))
    (storedMasks (G++[V])) r (G++[V]).length inp hp
  have he : 2*r+4+1+(r*(7*r+15)+(r+2))+1+(2*r+4) = 7*r*r+20*r+12 := by ring
  rw [he] at hr
  have hmr := seqTM_hoareTime _ _ hm (emitPred_transition hp (enumWork_parked _ _ _ _ _ _ _) []) hr
  have h := seqTM_hoareTime _ _ hc (emitPred_transition hp (enumWork_parked _ _ _ _ _ _ _) []) hmr
  refine ⟨cost,V,hcost,hV,hnew,?_⟩
  convert h using 1
  omega

end IrrRAFEnumeration.CompletionQuery
