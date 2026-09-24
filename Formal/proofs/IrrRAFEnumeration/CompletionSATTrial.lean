import proofs.IrrRAFEnumeration.CompletionTrial

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM PolynomialClockSetup

/-- The concrete trial invokes the actual reusable SAT program, with all of its
query construction, clock setup, scratch cleanup and restoration costs included. -/
theorem satDeletionTrial_correct {d r k : Nat} (q : Polynomial Nat)
    (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) (j : Fin r)
    (hU : PositiveCompletion.Available (IsRAF Q C) G.toFinset U)
    (M : TM k) (T : Nat → Nat) (hM : M.DecidesInTime SAT.language T)
    (hq : ∀ L, q.eval L = T L+L+2) (inp : Tape) (hp : Parked inp) :
    let base := SAT.CNF.encode (assembledBase Q C)
    let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
    let query := SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
      PositiveCompletionCNF.containerExclusions (U.erase j))
    (deletionTrialTM (restoredCompletionTM q M)).HoareTime
      (EmitPred inp (trialWork k U base blocks j.val 0) [])
      (trialPost k (PositiveCompletion.Available (IsRAF Q C) G.toFinset) U j base blocks inp)
      (completionCallTime k q T r base.length blocks.length query.length+12*j.val+31) := by
  dsimp only
  exact deletionTrialTM_correct (restoredCompletionTM q M)
    (PositiveCompletion.Available (IsRAF Q C) G.toFinset) U j hU _ _ inp hp _
    (reusableCompletionTM_correct q Q C G (U.erase j) M T hM hq inp hp)

end IrrRAFEnumeration.CompletionQuery
