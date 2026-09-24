import proofs.IrrRAFEnumeration.CompletionFillContainer

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def enumMask (k : Nat) := Fin.castAdd 1 (Fin.castAdd 1 (minMask k))
def enumAddress (k : Nat) := Fin.castAdd 1 (Fin.castAdd 1 (Fin.castAdd 1 (trialAddress k)))
def enumFuel (k : Nat) := Fin.castAdd 1 (Fin.castAdd 1 (minimizeFuel k))

theorem enumWork_address {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks records : List Bool) (j count : Nat) :
    enumWork k U base blocks records j count (enumAddress k) = regTape j := by
  simp [enumWork,enumAddress,minimizeWork,frameWork,trialAddress]
  exact trialWork_address _ _ _ _ _ _

theorem enumWork_mask {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks records : List Bool) (j count : Nat) :
    enumWork k U base blocks records j count (enumMask k) = parkedInput (containerMask U) := by
  simp only [enumWork,enumMask,frameWork,Fin.val_castAdd,
    dif_pos (minMask k).isLt]
  exact minimizeWork_mask _ _ _ _ _

theorem enumWork_fuel {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks records : List Bool) (j count : Nat) :
    enumWork k U base blocks records j count (enumFuel k) = regTape r := by
  simp [enumWork,enumFuel,minimizeWork,minimizeFuel,frameWork]

theorem enumWork_update_address {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks records : List Bool) (j count v : Nat) :
    Function.update (enumWork k U base blocks records j count) (enumAddress k) (regTape v) =
      enumWork k U base blocks records v count := by
  unfold enumWork enumAddress minimizeWork
  rw [← frameWork_update,← frameWork_update,← frameWork_update,trialWork_update_address]

theorem enumWork_update_mask {r : Nat} (k : Nat) (U V : Finset (Fin r))
    (base blocks records : List Bool) (j count : Nat) :
    Function.update (enumWork k U base blocks records j count) (enumMask k) (parkedInput (containerMask V)) =
      enumWork k V base blocks records j count := by
  unfold enumWork enumMask minMask minimizeWork
  rw [← frameWork_update,← frameWork_update,← frameWork_update,trialWork_update_mask]

def roundResetTM (k : Nat) : TM ((((bufferedCount k+1)+1)+1)+1) :=
  seqTM (clearRegTM (enumAddress k))
    (seqTM (fillContainerTM (enumFuel k) (enumAddress k) (enumMask k)) (clearRegTM (enumAddress k)))

/-- Reset for the next full-universe completion test, preserving the committed
mask records, blockers, chemistry and output count exactly. -/
theorem roundResetTM_correct {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks records : List Bool) (j count : Nat) (inp : Tape) (hp : Parked inp) :
    (roundResetTM k).HoareTime (EmitPred inp (enumWork k U base blocks records j count) [])
      (EmitPred inp (enumWork k (Finset.univ : Finset (Fin r)) base blocks records 0 count) [])
      (2*j+4+1+(r*(7*r+15)+(r+2))+1+(2*r+4)) := by
  have hda : enumMask k ≠ enumAddress k := by
    intro h
    have he := congrArg (fun i => i.val) h
    change 4 = bufferedCount k at he
    unfold bufferedCount at he
    omega
  have hdf : enumMask k ≠ enumFuel k := by
    intro h
    have he := congrArg (fun i => i.val) h
    change 4 = bufferedCount k+1 at he
    unfold bufferedCount at he
    omega
  have haf : enumAddress k ≠ enumFuel k := by
    intro h
    have he := congrArg (fun i => i.val) h
    change bufferedCount k = bufferedCount k+1 at he
    omega
  have h1 := clearRegTM_hoareTime (enumAddress k) j inp (enumWork k U base blocks records j count) [] hp
    (fun i _ => enumWork_parked _ _ _ _ _ _ _ i) (enumWork_address _ _ _ _ _ _ _)
  rw [enumWork_update_address] at h1
  have h2 := fillContainerTM_correct (enumFuel k) (enumAddress k) (enumMask k) hda hdf haf U inp
    (enumWork k U base blocks records 0 count) [] hp (enumWork_parked _ _ _ _ _ _ _)
    (enumWork_fuel _ _ _ _ _ _ _) (enumWork_address _ _ _ _ _ _ _) (enumWork_mask _ _ _ _ _ _ _)
  rw [enumWork_update_mask,enumWork_update_address] at h2
  have h3 := clearRegTM_hoareTime (enumAddress k) r inp
    (enumWork k (Finset.univ : Finset (Fin r)) base blocks records r count) [] hp
    (fun i _ => enumWork_parked _ _ _ _ _ _ _ i) (enumWork_address _ _ _ _ _ _ _)
  rw [enumWork_update_address] at h3
  have h23 := seqTM_hoareTime _ _ h2 (emitPred_transition hp (enumWork_parked _ _ _ _ _ _ _) []) h3
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp (enumWork_parked _ _ _ _ _ _ _) []) h23
  convert h using 1
  omega

end IrrRAFEnumeration.CompletionQuery
