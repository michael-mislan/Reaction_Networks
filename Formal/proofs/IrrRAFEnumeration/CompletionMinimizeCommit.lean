import proofs.IrrRAFEnumeration.CompletionCommitCount

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM PolynomialClockSetup

def minimizeCommitTM {k : Nat} (q : Polynomial Nat) (M : TM k) :
    TM ((((bufferedCount k+1)+1)+1)+1) :=
  seqTM (((minimizeTM (restoredCompletionTM q M)).liftTM 1).liftTM 1) (commitOutputTM k)

/-- One actual successful search-and-commit round. The same newly minimal mask is
recorded, blocked, and counted; the cost retains the r generated SAT query costs. -/
theorem minimizeCommitTM_correct {d r k : Nat} (q : Polynomial Nat)
    (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r))
    (hU : PositiveCompletion.Available (IsRAF Q C) G.toFinset U)
    (M : TM k) (T : Nat → Nat) (hM : M.DecidesInTime SAT.language T)
    (hq : ∀ L, q.eval L = T L+L+2) (inp : Tape) (hp : Parked inp) :
    let base := SAT.CNF.encode (assembledBase Q C)
    let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
    ∃ (cost : Fin r → Nat) (V : Finset (Fin r)),
      (∀ i, ∃ W : Finset (Fin r), cost i = completionCallTime k q T r base.length blocks.length
        (SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
          PositiveCompletionCNF.containerExclusions W)).length) ∧
      Minimal (IsRAF Q C) V ∧ V ∉ G.toFinset ∧
      (minimizeCommitTM q M).HoareTime
        (EmitPred inp (enumWork k U base blocks (storedMasks G) 0 G.length) [])
        (EmitPred inp (enumWork k V base
          (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers (G++[V])))
          (storedMasks (G++[V])) r (G++[V]).length) [])
        (r*((∑ i, cost i)+12*r+33)+(r+2)+1+
          (2*r+6+blockerCommitTime r blocks.length (SAT.CNF.encode [blockerClause V]).length+
            1+2*G.length+4)) := by
  dsimp only
  let base := SAT.CNF.encode (assembledBase Q C)
  let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
  obtain ⟨b,⟨cost,hcost,hb⟩,hm⟩ := satMinimize_correct q Q C G U hU M T hM hq inp hp
  obtain ⟨c,t,ht,hr,hh,V,hV,hnew,ha,hw,ho⟩ :=
    hm inp (minimizeWork k U base blocks 0) (accumulatorTape [])
      ⟨rfl,rfl,accumulatorTape_outAcc []⟩
  have hexact : (minimizeTM (restoredCompletionTM q M)).HoareTime
      (EmitPred inp (minimizeWork k U base blocks 0) [])
      (EmitPred inp (minimizeWork k V base blocks r) []) b := by
    rintro a w out ⟨hai,hwi,hoi⟩
    subst a
    subst w
    have he := hoi.eq (accumulatorTape_outAcc [])
    subst out
    exact ⟨c,t,ht,hr,hh,ha,hw,ho⟩
  have h1 := liftTM_frame_correct _ 1 (fun _ => accumulatorTape (storedMasks G))
    (fun _ _ => (accumulatorTape_outAcc _).parked) inp inp _ _ [] [] _ hexact
  have h2 := liftTM_frame_correct _ 1 (fun _ => regTape G.length)
    (fun _ _ => parked_regTape _) inp inp _ _ [] [] _ h1
  have hc := commitKnownOutput_correct k G V base r inp hp
  have hall := seqTM_hoareTime _ _ h2 (emitPred_transition hp (enumWork_parked _ _ _ _ _ _ _) []) hc
  refine ⟨cost,V,hcost,hV,hnew,?_⟩
  rw [hb] at hall
  exact hall

end IrrRAFEnumeration.CompletionQuery
