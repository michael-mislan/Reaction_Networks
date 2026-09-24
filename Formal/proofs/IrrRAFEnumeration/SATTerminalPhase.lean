import proofs.IrrRAFEnumeration.SATTerminalBodies

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

def terminalTM : TM 13 := seqTM finishSetupTM
  (seqTM finishBodyTM (seqTM resetSetupTM resetBodyTM))

theorem terminalTM_correct (n m W Q M : Nat) (stream inp : Tape) (ys : List Bool)
    (hs : Parked stream) (hp : Parked inp) (hQ : 1 ≤ Q) :
    terminalTM.HoareTime (EmitPred inp (terminalWork n m W Q M stream) ys)
      (EmitPred inp (resetWork n m W Q M stream)
        (ys ++ (finishPattern n m W Q M ++ resetPattern W Q)))
      (10000*(n+m+W+Q+M+1)^2) := by
  have hw1 : ∀ i, Parked (finishWork n m W Q M 1 stream i) := by
    intro i
    fin_cases i <;> first | exact parked_regTape _ | exact hs
  have hw0 : ∀ i, Parked (finishWork n m W Q M 0 stream i) := by
    intro i
    fin_cases i <;> first | exact parked_regTape _ | exact hs
  have hwr : ∀ i, Parked (resetWork n m W Q M stream i) := by
    intro i
    fin_cases i <;> first | exact parked_regTape _ | exact hs
  have h34 := seqTM_hoareTime _ _
    (resetSetupTM_correct n m W Q M stream inp (ys ++ finishPattern n m W Q M) hs hp hQ)
    (emitPred_transition hp hwr _)
    (resetBodyTM_correct n m W Q M stream inp (ys ++ finishPattern n m W Q M) hs hp)
  have h234 := seqTM_hoareTime _ _ (finishBodyTM_correct n m W Q M stream inp ys hs hp)
    (emitPred_transition hp hw0 _) h34
  have h := seqTM_hoareTime _ _ (finishSetupTM_correct n m W Q M stream inp ys hs hp)
    (emitPred_transition hp hw1 ys) h234
  rw [List.append_assoc] at h
  apply h.mono_bound
  let B := n+m+W+Q+M+1
  have hB : 1 ≤ B := by dsimp [B]; omega
  change 4096*B^2+1+(100*B+1+(4096*B^2+1+100*B)) ≤ 10000*B^2
  nlinarith

end IrrRAFEnumeration.SATSource
