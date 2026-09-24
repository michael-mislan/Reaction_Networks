import proofs.IrrRAFEnumeration.SATTerminalSetup
import proofs.IrrRAFEnumeration.SATRowMachines

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

def finishPattern (n m W Q M : Nat) : List Bool :=
  spanRow (2*n+1) (n+m) (Q+2) ++ markedRow W (Q-1) 1 true ++ spanRow (M-1) 1 0

def resetPattern (W Q : Nat) : List Bool :=
  spanRow W 1 (Q+1) ++ blockLastRow 1 W Q ++ spanRow (W+1) 1 Q

def finishBodyTM : TM 13 :=
  seqTM (spanRowTM 0 6 1) (seqTM (twoMarkRowTM 2 3 4)
    (seqTM (decRegTM 4) (fixedSpanRowTM 1 5 4)))

theorem finishBodyTM_correct (n m W Q M : Nat) (stream inp : Tape) (ys : List Bool)
    (hs : Parked stream) (hp : Parked inp) :
    finishBodyTM.HoareTime (EmitPred inp (finishWork n m W Q M 1 stream) ys)
      (EmitPred inp (finishWork n m W Q M 0 stream) (ys ++ finishPattern n m W Q M))
      (100*(n+m+W+Q+M+1)) := by
  let w := finishWork n m W Q M 1 stream
  let v := finishWork n m W Q M 0 stream
  have hw : ∀ i, Parked (w i) := by
    intro i
    fin_cases i <;> first | exact parked_regTape _ | exact hs
  have hv : ∀ i, Parked (v i) := by
    intro i
    fin_cases i <;> first | exact parked_regTape _ | exact hs
  have h1 := spanRowTM_correct (0 : Fin 13) 6 1 (2*n+1) (n+m) (Q+2)
    inp w ys hp hw rfl rfl rfl
  have h2 := twoMarkRowTM_correct (2 : Fin 13) 3 4 W (Q-1) 1
    inp w (ys ++ spanRow (2*n+1) (n+m) (Q+2)) hp hw rfl rfl rfl
  let bits := (ys ++ spanRow (2*n+1) (n+m) (Q+2)) ++ markedRow W (Q-1) 1 true
  have hd := decRegTM_hoareTime (4 : Fin 13) 1 inp w bits hp (fun i _ => hw i) rfl
  have he : Function.update w 4 (regTape (1-1)) = v := by
    funext i
    fin_cases i <;> simp [w,v,finishWork]
  rw [he] at hd
  have h3 := fixedSpanRowTM_correct 1 (5 : Fin 13) 4 (M-1) 0 inp v bits hp hv rfl rfl
  have hd3 := seqTM_hoareTime _ _ hd (emitPred_transition hp hv bits) h3
  have h2end := seqTM_hoareTime _ _ h2 (emitPred_transition hp hw bits) hd3
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp hw _) h2end
  have hb : bits ++ spanRow (M-1) 1 0 = ys ++ finishPattern n m W Q M := by
    simp [bits,finishPattern,List.append_assoc]
  change finishBodyTM.HoareTime _ (EmitPred inp v (bits ++ spanRow (M-1) 1 0)) _ at h
  rw [hb] at h
  apply h.mono_bound
  nlinarith [Nat.sub_le Q 1,Nat.sub_le M 1]

def resetBodyTM : TM 13 :=
  seqTM (fixedSpanRowTM 1 2 1) (seqTM (blockLastRowTM 0 2 3) (fixedSpanRowTM 1 5 3))

theorem resetBodyTM_correct (n m W Q M : Nat) (stream inp : Tape) (ys : List Bool)
    (hs : Parked stream) (hp : Parked inp) :
    resetBodyTM.HoareTime (EmitPred inp (resetWork n m W Q M stream) ys)
      (EmitPred inp (resetWork n m W Q M stream) (ys ++ resetPattern W Q))
      (100*(n+m+W+Q+M+1)) := by
  let w := resetWork n m W Q M stream
  have hw : ∀ i, Parked (w i) := by
    intro i
    fin_cases i <;> first | exact parked_regTape _ | exact hs
  have h1 := fixedSpanRowTM_correct 1 (2 : Fin 13) 1 W (Q+1) inp w ys hp hw rfl rfl
  have h2 := blockLastRowTM_correct (0 : Fin 13) 2 3 1 W Q inp w
    (ys ++ spanRow W 1 (Q+1)) hp hw rfl rfl rfl
  have h3 := fixedSpanRowTM_correct 1 (5 : Fin 13) 3 (W+1) Q inp w
    ((ys ++ spanRow W 1 (Q+1)) ++ blockLastRow 1 W Q) hp hw rfl rfl
  have h23 := seqTM_hoareTime _ _ h2 (emitPred_transition hp hw _) h3
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp hw _) h23
  have hb : ((ys ++ spanRow W 1 (Q+1)) ++ blockLastRow 1 W Q) ++ spanRow (W+1) 1 Q =
      ys ++ resetPattern W Q := by simp [resetPattern,List.append_assoc]
  change resetBodyTM.HoareTime _ (EmitPred inp w _) _ at h
  rw [hb] at h
  apply h.mono_bound
  omega

end IrrRAFEnumeration.SATSource
