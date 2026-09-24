import proofs.IrrRAFEnumeration.SATRunRows
import proofs.IrrRAFEnumeration.SATMachineRuns

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

def fixedSpanRowTM {k : Nat} (count : Nat) (before after : Fin k) : TM k :=
  seqTM (emitRunTM false before)
    (seqTM (emitBitsTM (List.replicate count true)) (emitRunTM false after))

theorem fixedSpanRowTM_correct {k : Nat} (count : Nat) (ra rc : Fin k) (a c : Nat)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (ha : work ra = regTape a) (hc : work rc = regTape c) :
    (fixedSpanRowTM count ra rc).HoareTime (EmitPred inp work ys)
      (EmitPred inp work (ys ++ spanRow a count c)) (4*(a+c)+count+6) := by
  have h1 := emitRunTM_correct false ra a inp work ys hp hw ha
  have h2 := emitBitsTM_hoareTime (List.replicate count true) inp work
    (ys ++ List.replicate a false) hp hw
  have h3 := emitRunTM_correct false rc c inp work
    ((ys ++ List.replicate a false) ++ List.replicate count true) hp hw hc
  have h23 := seqTM_hoareTime _ _ h2 (emitPred_transition hp hw _) h3
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp hw _) h23
  have ht : (4*a+2)+1+(count+1+(4*c+2)) = 4*(a+c)+count+6 := by omega
  simpa only [fixedSpanRowTM,spanRow,List.length_replicate,List.append_assoc,ht] using h

def twoMarkRowTM {k : Nat} (before between after : Fin k) : TM k :=
  seqTM (emitRunTM false before) (seqTM (emitBitsTM [true]) (fixedSpanRowTM 1 between after))

theorem twoMarkRowTM_correct {k : Nat} (ra rb rc : Fin k) (a b c : Nat)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (ha : work ra = regTape a) (hb : work rb = regTape b) (hc : work rc = regTape c) :
    (twoMarkRowTM ra rb rc).HoareTime (EmitPred inp work ys)
      (EmitPred inp work (ys ++ markedRow a b c true)) (4*(a+b+c)+12) := by
  have h1 := emitRunTM_correct false ra a inp work ys hp hw ha
  have h2 := emitBitsTM_hoareTime [true] inp work (ys ++ List.replicate a false) hp hw
  have h3 := fixedSpanRowTM_correct 1 rb rc b c inp work
    ((ys ++ List.replicate a false) ++ [true]) hp hw hb hc
  have h23 := seqTM_hoareTime _ _ h2 (emitPred_transition hp hw _) h3
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp hw _) h23
  have ht : (4*a+2)+1+(1+1+(4*(b+c)+1+6)) = 4*(a+b+c)+12 := by omega
  simpa only [twoMarkRowTM,spanRow,markedRow,List.length_singleton,List.replicate_one,
    List.append_assoc,ht] using h

end IrrRAFEnumeration.SATSource
