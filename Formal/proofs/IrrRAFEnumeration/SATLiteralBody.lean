import proofs.IrrRAFEnumeration.SATTapeFrame
import proofs.IrrRAFEnumeration.SATRowMachines
import proofs.Complexitylib.Models.TuringMachine.Registers.DecReg

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

def literalRows (edge pos tail : Nat) : List Bool :=
  spanRow 0 1 edge ++ spanRow pos 1 tail ++ spanRow edge 1 0

def literalBodyTM {k : Nat} (zero one edge pos tail : Fin k) : TM k :=
  seqTM (spanRowTM zero one edge)
    (seqTM (spanRowTM pos one tail)
      (seqTM (spanRowTM edge one zero) (seqTM (incRegTM pos) (decRegTM tail))))

theorem literalBodyTM_correct {k : Nat} (rz ro re rp rs : Fin k) (hne : rs ≠ rp)
    (e p s : Nat) (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (hz : work rz = regTape 0) (ho : work ro = regTape 1) (he : work re = regTape e)
    (hpos : work rp = regTape p) (htail : work rs = regTape s) :
    (literalBodyTM rz ro re rp rs).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update (Function.update work rp (regTape (p+1)))
        rs (regTape (s-1))) (ys ++ literalRows e p s))
      (8*e+6*p+6*s+48) := by
  let y₁ := ys ++ spanRow 0 1 e
  let y₂ := y₁ ++ spanRow p 1 s
  let y₃ := y₂ ++ spanRow e 1 0
  let W := Function.update work rp (regTape (p+1))
  have hw' : ∀ i, Parked (W i) := updateReg_parked work hw rp (p+1)
  have h₁ := spanRowTM_correct rz ro re 0 1 e inp work ys hp hw hz ho he
  have h₂ := spanRowTM_correct rp ro rs p 1 s inp work y₁ hp hw hpos ho htail
  have h₃ := spanRowTM_correct re ro rz e 1 0 inp work y₂ hp hw he ho hz
  have h₄ := incRegTM_hoareTime rp p inp work y₃ hp (fun i _ => hw i) hpos
  have h₅ := decRegTM_hoareTime rs s inp W y₃ hp (fun i _ => hw' i)
    (by simpa [W, Function.update_of_ne hne] using htail)
  have h₄₅ := seqTM_hoareTime _ _ h₄ (emitPred_transition hp hw' y₃) h₅
  have h₃₄₅ := seqTM_hoareTime _ _ h₃ (emitPred_transition hp hw y₃) h₄₅
  have h₂₃₄₅ := seqTM_hoareTime _ _ h₂ (emitPred_transition hp hw y₂) h₃₄₅
  have hall := seqTM_hoareTime _ _ h₁ (emitPred_transition hp hw y₁) h₂₃₄₅
  have htime : (4*(0+1+e)+8)+1+((4*(p+1+s)+8)+1+
      ((4*(e+1+0)+8)+1+((2*p+4)+1+(2*s+4)))) = 8*e+6*p+6*s+48 := by omega
  simpa only [literalBodyTM, literalRows, y₁,y₂,y₃,W,List.append_assoc,htime] using hall

end IrrRAFEnumeration.SATSource
