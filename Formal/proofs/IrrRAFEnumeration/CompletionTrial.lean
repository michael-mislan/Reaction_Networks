import proofs.IrrRAFEnumeration.CompletionTrialFrame

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM PolynomialClockSetup

def trialTailTM (k : Nat) : TM (bufferedCount k+1) :=
  seqTM (restoreRejectedTM (trialAddress k) (trialMask k) (trialFlag k))
    (seqTM (clearRegTM (trialFlag k)) (incRegTM (trialAddress k)))

def deletionTrialTM {k : Nat} (call : TM (bufferedCount k)) : TM (bufferedCount k+1) :=
  seqTM (editWorkTM (trialAddress k) (trialMask k) Γw.zero)
    (seqTM (call.liftTM 1) (trialTailTM k))

theorem trialMask_ne_address (k : Nat) : trialMask k ≠ trialAddress k := by
  intro h
  have he := congrArg (fun i : Fin (bufferedCount k+1) => i.val) h
  change 4 = bufferedCount k at he
  unfold bufferedCount at he
  omega

theorem trialTailTM_correct {r : Nat} (k : Nat) (P : Finset (Fin r) → Prop)
    (U : Finset (Fin r)) (j : Fin r) (hU : P U) (v : Nat) (hv : v ≤ 1)
    (ha : v = 1 ↔ P (U.erase j)) (base blocks : List Bool) (inp : Tape) (hp : Parked inp) :
    let V := if v = 1 then U.erase j else U
    (trialTailTM k).HoareTime
      (EmitPred inp (trialWork k (U.erase j) base blocks j.val v) [])
      (EmitPred inp (trialWork k V base blocks (j.val+1) 0) []) (7*j.val+21) := by
  dsimp only
  let V := if v = 1 then U.erase j else U
  have hr := restoreRejectedTM_correct (trialAddress k) (trialMask k) (trialFlag k)
    (trialMask_ne_address k) P U j hU v hv ha inp
    (trialWork k (U.erase j) base blocks j.val v) [] hp
    (trialWork_parked _ _ _ _ _ _) (trialWork_address _ _ _ _ _ _)
    (trialWork_mask _ _ _ _ _ _) (trialWork_flag _ _ _ _ _ _)
  rw [trialWork_update_mask] at hr
  have hc := clearRegTM_hoareTime (trialFlag k) v inp (trialWork k V base blocks j.val v) [] hp
    (fun i _ => trialWork_parked _ _ _ _ _ _ i) (trialWork_flag _ _ _ _ _ _)
  rw [trialWork_update_flag] at hc
  have hc6 := hc.mono_bound (show 2*v+4 ≤ 6 by omega)
  have hi := incRegTM_hoareTime (trialAddress k) j.val inp (trialWork k V base blocks j.val 0) [] hp
    (fun i _ => trialWork_parked _ _ _ _ _ _ i) (trialWork_address _ _ _ _ _ _)
  rw [trialWork_update_address] at hi
  have hci := seqTM_hoareTime _ _ hc6
    (emitPred_transition hp (trialWork_parked _ _ _ _ _ _) []) hi
  have h := seqTM_hoareTime _ _ hr
    (emitPred_transition hp (trialWork_parked _ _ _ _ _ _) []) hci
  convert h using 1
  omega

def trialPost {r : Nat} (k : Nat) (P : Finset (Fin r) → Prop)
    (U : Finset (Fin r)) (j : Fin r) (base blocks : List Bool) (inp : Tape) :
    TM.TapePred (bufferedCount k+1) := fun a w out =>
  ∃ v : Nat, v ≤ 1 ∧ (v = 1 ↔ P (U.erase j)) ∧
    P (if v = 1 then U.erase j else U) ∧
    EmitPred inp (trialWork k (if v = 1 then U.erase j else U) base blocks (j.val+1) 0) [] a w out

/-- An actual deletion, actual decision call, conditional undo, result consumption,
and index increment. The predicate occurs only in the specification. -/
theorem deletionTrialTM_correct {r k : Nat} (call : TM (bufferedCount k))
    (P : Finset (Fin r) → Prop) (U : Finset (Fin r)) (j : Fin r) (hU : P U)
    (base blocks : List Bool) (inp : Tape) (hp : Parked inp) (b : Nat)
    (hc : call.HoareTime (EmitPred inp (completionWork k (U.erase j) base blocks) [])
      (completionResult k (U.erase j) base blocks inp (P (U.erase j))) b) :
    (deletionTrialTM call).HoareTime (EmitPred inp (trialWork k U base blocks j.val 0) [])
      (trialPost k P U j base blocks inp) (b+12*j.val+31) := by
  have he := editContainerTM_correct (trialAddress k) (trialMask k) (trialMask_ne_address k)
    U j false inp (trialWork k U base blocks j.val 0) [] hp
    (trialWork_parked _ _ _ _ _ _) (trialWork_address _ _ _ _ _ _) (trialWork_mask _ _ _ _ _ _)
  simp only [Bool.false_eq_true,ite_false,trialWork_update_mask] at he
  have hl := liftCompletionResult_correct call (U.erase j) base blocks j.val inp (P (U.erase j)) b hc
  have ht : (trialTailTM k).HoareTime
      (trialResult k (U.erase j) base blocks j.val inp (P (U.erase j)))
      (trialPost k P U j base blocks inp) (7*j.val+21) := by
    rintro a w out ⟨v,hv,ha,hpre⟩
    have hV : P (if v = 1 then U.erase j else U) := by
      split
      · exact ha.mp ‹v = 1›
      · exact hU
    obtain ⟨c,t,ht,hr,hh,hs⟩ := trialTailTM_correct k P U j hU v hv ha base blocks inp hp a w out hpre
    exact ⟨c,t,ht,hr,hh,v,hv,ha,hV,hs⟩
  have hlt := seqTM_hoareTime _ _ hl (by
    rintro a w out ⟨v,hv,ha,hpre⟩
    exact ⟨v,hv,ha,emitPred_transition hp (trialWork_parked _ _ _ _ _ _) [] a w out hpre⟩) ht
  have h := seqTM_hoareTime _ _ he
    (emitPred_transition hp (trialWork_parked _ _ _ _ _ _) []) hlt
  convert h using 1
  omega

end IrrRAFEnumeration.CompletionQuery
