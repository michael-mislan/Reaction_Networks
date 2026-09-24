import proofs.IrrRAFEnumeration.CompletionReusable

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

theorem completionWork_parked {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks : List Bool) : ∀ i, Parked (completionWork k U base blocks i) := by
  intro i
  unfold completionWork bufferedWork queryDecisionWork queryPrefix frameWork
  split
  · split
    · split
      · exact dynamicWork_parked _ _ _ _ _ _
      · exact parked_regTape _
    · exact parkedInput_parked _
  · exact (accumulatorTape_outAcc []).parked

theorem completionWork_flag {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks : List Bool) : completionWork k U base blocks (completionFlag k) = regTape 0 := by
  exact (completionWork_low k U base blocks (3 : Fin 10)).trans (by rfl)

theorem completionResult_transition {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks : List Bool) (inp : Tape) (hp : Parked inp) (answer : Prop) :
    ∀ a w out, completionResult k U base blocks inp answer a w out →
      completionResult k U base blocks inp answer (transitionInput a)
        (fun i => transitionTape (w i)) (transitionTape out) := by
  rintro a w out ⟨bit,hb,hv,he⟩
  refine ⟨bit,hb,hv,?_⟩
  exact emitPred_transition hp
    (updateReg_parked _ (completionWork_parked k U base blocks) (completionFlag k) bit) [] a w out he

/-- After the caller has used the result, clearing its flag restores the exact
next-call precondition in at most six actual transitions. -/
theorem clearCompletionResult_correct {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks : List Bool) (inp : Tape) (hp : Parked inp) (answer : Prop) :
    (clearRegTM (completionFlag k)).HoareTime (completionResult k U base blocks inp answer)
      (EmitPred inp (completionWork k U base blocks) []) 6 := by
  rintro a w out ⟨bit,hb,hv,ha,hw,ho⟩
  subst a
  subst w
  let W := Function.update (completionWork k U base blocks) (completionFlag k) (regTape bit)
  have hwp := updateReg_parked _ (completionWork_parked k U base blocks) (completionFlag k) bit
  have hc := clearRegTM_hoareTime (completionFlag k) bit inp W [] hp (fun i _ => hwp i)
    (by simp [W])
  have he : Function.update W (completionFlag k) (regTape 0) = completionWork k U base blocks := by
    funext i
    by_cases hi : i = completionFlag k
    · subst i
      simp [completionWork_flag]
    · simp [W,Function.update_of_ne hi]
  rw [he] at hc
  obtain ⟨c,t,ht,hr,hh,hpost⟩ := hc inp W out ⟨rfl,rfl,ho⟩
  exact ⟨c,t,by omega,hr,hh,hpost⟩

end IrrRAFEnumeration.CompletionQuery
