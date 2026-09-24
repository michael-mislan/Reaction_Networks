import proofs.IrrRAFEnumeration.SATRowMachines
import proofs.Complexitylib.Models.TuringMachine.Registers.DecReg

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

def sourceHeaderTM {k : Nat} (rm rr : Fin k) : TM k :=
  seqTM (emitRunTM true rm) (seqTM (emitBitsTM [false])
    (seqTM (emitRunTM true rr) (emitBitsTM [false])))

def sourceHeader (M R : Nat) : List Bool :=
  List.replicate M true ++ [false] ++ List.replicate R true ++ [false]

theorem sourceHeaderTM_correct {k : Nat} (rm rr : Fin k) (M R : Nat)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (hm : work rm = regTape M) (hr : work rr = regTape R) :
    (sourceHeaderTM rm rr).HoareTime (EmitPred inp work ys)
      (EmitPred inp work (ys ++ sourceHeader M R)) (4*M+4*R+9) := by
  have h₁ := emitRunTM_correct true rm M inp work ys hp hw hm
  have h₂ := emitBitsTM_hoareTime [false] inp work (ys ++ List.replicate M true) hp hw
  have h₃ := emitRunTM_correct true rr R inp work
    ((ys ++ List.replicate M true) ++ [false]) hp hw hr
  have h₄ := emitBitsTM_hoareTime [false] inp work
    (((ys ++ List.replicate M true) ++ [false]) ++ List.replicate R true) hp hw
  have h₃₄ := seqTM_hoareTime _ _ h₃ (emitPred_transition hp hw _) h₄
  have h₂₃₄ := seqTM_hoareTime _ _ h₂ (emitPred_transition hp hw _) h₃₄
  have h := seqTM_hoareTime _ _ h₁ (emitPred_transition hp hw _) h₂₃₄
  have ht : (4*M+2)+1+(1+1+((4*R+2)+1+1)) = 4*M+4*R+9 := by omega
  simpa only [sourceHeaderTM,sourceHeader,List.length_singleton,List.append_assoc,ht] using h

def foodRowTM {k : Nat} (rm : Fin k) : TM k :=
  seqTM (emitBitsTM [true]) (seqTM (decRegTM rm)
    (seqTM (emitRunTM false rm) (incRegTM rm)))

/-- Emit the singleton-food incidence row, restoring its dimension register. -/
theorem foodRowTM_correct {k : Nat} (rm : Fin k) (M : Nat) (hM : 1 ≤ M)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i)) (hm : work rm = regTape M) :
    (foodRowTM rm).HoareTime (EmitPred inp work ys)
      (EmitPred inp work (ys ++ ([true] ++ List.replicate (M-1) false))) (8*M+20) := by
  let w := Function.update work rm (regTape (M-1))
  have hwp : ∀ i, Parked (w i) := updateReg_parked work hw rm (M-1)
  have h₁ := emitBitsTM_hoareTime [true] inp work ys hp hw
  have h₂ := decRegTM_hoareTime rm M inp work (ys ++ [true]) hp (fun i _ => hw i) hm
  have h₃ := emitRunTM_correct false rm (M-1) inp w (ys ++ [true]) hp hwp
    (by simp [w])
  have h₄ := incRegTM_hoareTime rm (M-1) inp w
    ((ys ++ [true]) ++ List.replicate (M-1) false) hp (fun i _ => hwp i) (by simp [w])
  have h₃₄ := seqTM_hoareTime _ _ h₃ (emitPred_transition hp hwp _) h₄
  have h₂₃₄ := seqTM_hoareTime _ _ h₂ (emitPred_transition hp hwp _) h₃₄
  have h := seqTM_hoareTime _ _ h₁ (emitPred_transition hp hw _) h₂₃₄
  have he : Function.update w rm (regTape (M-1+1)) = work := by
    have hval : M-1+1 = M := by omega
    rw [hval]
    simp only [w,Function.update_idem]
    funext i
    by_cases hi : i = rm
    · subst i
      simpa using hm.symm
    · simp only [Function.update_of_ne hi]
  rw [he] at h
  simp only [List.length_singleton,List.append_assoc] at h
  apply h.mono_bound
  omega

end IrrRAFEnumeration.SATSource
