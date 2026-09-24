import proofs.IrrRAFEnumeration.CompletionDeletionBranch

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM PolynomialClockSetup

def trialAddress (k : Nat) : Fin (bufferedCount k+1) := Fin.last (bufferedCount k)
def trialMask (k : Nat) : Fin (bufferedCount k+1) := Fin.castAdd 1 (lowTape k 4)
def trialFlag (k : Nat) : Fin (bufferedCount k+1) := Fin.castAdd 1 (completionFlag k)
def trialWork {r : Nat} (k : Nat) (U : Finset (Fin r)) (base blocks : List Bool) (j bit : Nat) :=
  frameWork (m := 1)
    (Function.update (completionWork k U base blocks) (completionFlag k) (regTape bit))
    (fun _ => regTape j)

theorem frameWork_update {n m : Nat} (w : Fin n → Tape) (extra : Fin (n+m) → Tape)
    (idx : Fin n) (t : Tape) : frameWork (Function.update w idx t) extra =
      Function.update (frameWork w extra) (Fin.castAdd m idx) t := by
  funext i
  by_cases hi : i.val < n
  · by_cases he : (⟨i.val,hi⟩ : Fin n) = idx
    · have he' : i = Fin.castAdd m idx := by
        apply Fin.ext
        exact congrArg (fun x : Fin n => x.val) he
      subst i
      simp [frameWork]
    · have he' : i ≠ Fin.castAdd m idx := by
        intro h
        apply he
        exact Fin.ext (congrArg (fun x : Fin (n+m) => x.val) h)
      simp [frameWork,hi,Function.update_of_ne he,Function.update_of_ne he']
  · have he : i ≠ Fin.castAdd m idx := by
      intro h
      have hv := congrArg (fun x : Fin (n+m) => x.val) h
      have := idx.isLt
      simp only [Fin.val_castAdd] at hv
      omega
    simp [frameWork,hi,Function.update_of_ne he]

theorem completionWork_high {r : Nat} (k : Nat) (U : Finset (Fin r)) (base blocks : List Bool)
    (i : Fin (bufferedCount k)) (hi : 10 ≤ i.val) : completionWork k U base blocks i = parkedInput [] := by
  have h7 : ¬i.val < 7 := by omega
  simp [completionWork,bufferedWork,queryDecisionWork,queryPrefix,frameWork,h7,
    regTape_zero_eq_parked,accumulatorTape,advanceInput]

theorem completionWork_update_mask {r : Nat} (k : Nat) (U V : Finset (Fin r)) (base blocks : List Bool) :
    Function.update (completionWork k U base blocks) (lowTape k 4) (parkedInput (containerMask V)) =
      completionWork k V base blocks := by
  funext i
  by_cases hi : i.val < 10
  · let j : Fin 10 := ⟨i.val,hi⟩
    have he : i = lowTape k j := by apply Fin.ext; rfl
    rw [he]
    clear he
    clear_value j
    fin_cases j <;> simp [lowTape_eq_iff,completionWork_low] <;> rfl
  · have hge : 10 ≤ i.val := by omega
    have he : i ≠ lowTape k 4 := by
      intro h
      have hv := congrArg (fun x : Fin (bufferedCount k) => x.val) h
      change i.val = 4 at hv
      omega
    rw [Function.update_of_ne he,completionWork_high k U base blocks i hge,
      completionWork_high k V base blocks i hge]

theorem trialWork_update_mask {r : Nat} (k : Nat) (U V : Finset (Fin r))
    (base blocks : List Bool) (j bit : Nat) :
    Function.update (trialWork k U base blocks j bit) (trialMask k) (parkedInput (containerMask V)) =
      trialWork k V base blocks j bit := by
  have hne : completionFlag k ≠ lowTape k 4 := by
    intro h
    have := congrArg (fun x : Fin (bufferedCount k) => x.val) h
    change 3 = 4 at this
    contradiction
  unfold trialWork trialMask
  rw [← frameWork_update,Function.update_comm hne,completionWork_update_mask]

theorem trialWork_parked {r : Nat} (k : Nat) (U : Finset (Fin r)) (base blocks : List Bool)
    (j bit : Nat) : ∀ i, Parked (trialWork k U base blocks j bit i) := by
  have hw := updateReg_parked _ (completionWork_parked k U base blocks) (completionFlag k) bit
  intro i
  unfold trialWork frameWork
  split
  · exact hw _
  · exact parked_regTape _

theorem trialWork_address {r : Nat} (k : Nat) (U : Finset (Fin r)) (base blocks : List Bool)
    (j bit : Nat) : trialWork k U base blocks j bit (trialAddress k) = regTape j := by
  simp [trialWork,trialAddress,frameWork]

theorem trialWork_flag {r : Nat} (k : Nat) (U : Finset (Fin r)) (base blocks : List Bool)
    (j bit : Nat) : trialWork k U base blocks j bit (trialFlag k) = regTape bit := by
  simp only [trialWork,trialFlag,frameWork,Fin.val_castAdd,
    dif_pos (completionFlag k).isLt,Function.update_self]

theorem trialWork_update_flag {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks : List Bool) (j bit v : Nat) :
    Function.update (trialWork k U base blocks j bit) (trialFlag k) (regTape v) =
      trialWork k U base blocks j v := by
  unfold trialWork trialFlag
  rw [← frameWork_update,Function.update_idem]

theorem trialWork_update_address {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks : List Bool) (j bit v : Nat) :
    Function.update (trialWork k U base blocks j bit) (trialAddress k) (regTape v) =
      trialWork k U base blocks v bit := by
  funext i
  by_cases hi : i.val < bufferedCount k
  · have hn : i ≠ trialAddress k := by
      intro h
      have he := congrArg (fun x : Fin (bufferedCount k+1) => x.val) h
      change i.val = bufferedCount k at he
      omega
    simp [Function.update_of_ne hn,trialWork,frameWork,hi]
  · have he : i = trialAddress k := by
      apply Fin.ext
      change i.val = bufferedCount k
      have := i.isLt
      change i.val < bufferedCount k+1 at this
      omega
    subst i
    simp [trialWork_address]

theorem trialWork_mask {r : Nat} (k : Nat) (U : Finset (Fin r)) (base blocks : List Bool)
    (j bit : Nat) : trialWork k U base blocks j bit (trialMask k) = parkedInput (containerMask U) := by
  have hn : lowTape k 4 ≠ completionFlag k := by
    intro h
    have := congrArg (fun x : Fin (bufferedCount k) => x.val) h
    change 4 = 3 at this
    contradiction
  simp only [trialWork,trialMask,frameWork,Fin.val_castAdd,dif_pos (lowTape k 4).isLt,
    Function.update_of_ne hn]
  exact (completionWork_low k U base blocks (4 : Fin 10)).trans (by rfl)

theorem trialWork_zero {r : Nat} (k : Nat) (U : Finset (Fin r)) (base blocks : List Bool) (j : Nat) :
    trialWork k U base blocks j 0 = frameWork (m := 1) (completionWork k U base blocks) (fun _ => regTape j) := by
  have he : Function.update (completionWork k U base blocks) (completionFlag k) (regTape 0) =
      completionWork k U base blocks := by
    funext i
    by_cases hi : i = completionFlag k
    · subst i
      simp [completionWork_flag]
    · simp [Function.update_of_ne hi]
  simp [trialWork,he]

def trialResult {r : Nat} (k : Nat) (U : Finset (Fin r)) (base blocks : List Bool)
    (j : Nat) (inp : Tape) (answer : Prop) : TM.TapePred (bufferedCount k+1) := fun a w out =>
  ∃ bit : Nat, bit ≤ 1 ∧ (bit = 1 ↔ answer) ∧ EmitPred inp (trialWork k U base blocks j bit) [] a w out

theorem liftCompletionResult_correct {r k : Nat} (call : TM (bufferedCount k))
    (U : Finset (Fin r)) (base blocks : List Bool) (j : Nat) (inp : Tape) (answer : Prop) (b : Nat)
    (h : call.HoareTime (EmitPred inp (completionWork k U base blocks) [])
      (completionResult k U base blocks inp answer) b) :
    (call.liftTM 1).HoareTime (EmitPred inp (trialWork k U base blocks j 0) [])
      (trialResult k U base blocks j inp answer) b := by
  rw [trialWork_zero]
  rintro a w out ⟨ha,hw,ho⟩
  subst a
  subst w
  obtain ⟨c,t,ht,hr,hh,bit,hb,hv,ha,hw,ho⟩ := h inp (completionWork k U base blocks) out ⟨rfl,rfl,ho⟩
  have hrun := liftTM_reaches_frame call 1 (fun _ => regTape j) (fun _ _ => parked_regTape _) hr
  refine ⟨frameCfg call 1 (fun _ => regTape j) c,t,ht,hrun,hh,bit,hb,hv,ha,?_,ho⟩
  change frameWork c.work (fun _ => regTape j) = trialWork k U base blocks j bit
  rw [hw]
  rfl

def completionCallTime (k : Nat) (q : Polynomial Nat) (T : Nat → Nat)
    (r baseLen blockLen L : Nat) : Nat :=
  let b := T L+L+2
  dynamicQueryTime baseLen blockLen r+L+6+setupTime q L+T L+1+6*b+11+1+
    (k+2)*(6*b+10)+1+1+4*r+2*L+4*b+35

end IrrRAFEnumeration.CompletionQuery
