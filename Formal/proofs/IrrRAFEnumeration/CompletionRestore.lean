import proofs.IrrRAFEnumeration.CompletionReturnState

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM PolynomialClockSetup

def restoreRegistersWork {k : Nat} (w : Fin (bufferedCount k) → Tape) :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update w (lowTape k 1) (regTape 1)) (lowTape k 2) (regTape 0))
    (lowTape k 7) (regTape 0)) (lowTape k 8) (regTape 0)) (lowTape k 9) (regTape 0)

def restoreRegistersTM (k : Nat) : TM (bufferedCount k) :=
  seqTM (setConstTM (lowTape k 1) 1)
    (seqTM (clearRegTM (lowTape k 2))
      (seqTM (clearRegTM (lowTape k 7))
        (seqTM (clearRegTM (lowTape k 8)) (clearRegTM (lowTape k 9)))))

theorem updateReg_parked {n : Nat} (w : Fin n → Tape) (hw : ∀ i, Parked (w i))
    (i : Fin n) (v : Nat) : ∀ j, Parked (Function.update w i (regTape v) j) := by
  intro j
  by_cases he : j = i
  · subst j
    simpa using parked_regTape v
  · simpa [Function.update_of_ne he] using hw j

theorem restoreRegistersTM_correct {k : Nat} (r L B : Nat) (inp : Tape)
    (w : Fin (bufferedCount k) → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (w i))
    (h1 : w (lowTape k 1) = regTape (1+r)) (h2 : w (lowTape k 2) = regTape r)
    (h7 : w (lowTape k 7) = regTape L) (h8 : w (lowTape k 8) = regTape B)
    (h9 : w (lowTape k 9) = regTape B) :
    (restoreRegistersTM k).HoareTime (EmitPred inp w ys)
      (EmitPred inp (restoreRegistersWork w) ys) (4*r+2*L+4*B+35) := by
  let W1 := Function.update w (lowTape k 1) (regTape 1)
  let W2 := Function.update W1 (lowTape k 2) (regTape 0)
  let W3 := Function.update W2 (lowTape k 7) (regTape 0)
  let W4 := Function.update W3 (lowTape k 8) (regTape 0)
  have hw1 := updateReg_parked w hw (lowTape k 1) 1
  have hw2 := updateReg_parked W1 hw1 (lowTape k 2) 0
  have hw3 := updateReg_parked W2 hw2 (lowTape k 7) 0
  have hw4 := updateReg_parked W3 hw3 (lowTape k 8) 0
  have ha := setConstTM_hoareTime (lowTape k 1) 1 (1+r) inp w ys hp hw h1
  have hb := clearRegTM_hoareTime (lowTape k 2) r inp W1 ys hp (fun i _ => hw1 i)
    (by simpa [W1,lowTape] using h2)
  have hc := clearRegTM_hoareTime (lowTape k 7) L inp W2 ys hp (fun i _ => hw2 i)
    (by simpa [W2,W1,lowTape] using h7)
  have hd := clearRegTM_hoareTime (lowTape k 8) B inp W3 ys hp (fun i _ => hw3 i)
    (by simpa [W3,W2,W1,lowTape] using h8)
  have he := clearRegTM_hoareTime (lowTape k 9) B inp W4 ys hp (fun i _ => hw4 i)
    (by simpa [W4,W3,W2,W1,lowTape] using h9)
  have hde := seqTM_hoareTime _ _ hd (emitPred_transition hp hw4 ys) he
  have hcde := seqTM_hoareTime _ _ hc (emitPred_transition hp hw3 ys) hde
  have hbcde := seqTM_hoareTime _ _ hb (emitPred_transition hp hw2 ys) hcde
  have hall := seqTM_hoareTime _ _ ha (emitPred_transition hp hw1 ys) hbcde
  exact hall.mono_bound (by omega)

def restoredPost {r : Nat} (q : Polynomial Nat) (k : Nat) (U : Finset (Fin r))
    (base blocks query : List Bool) (inp : Tape) (bound : Nat) (answer : Prop) :
    TM.TapePred (bufferedCount k) := fun a w out =>
  ∃ inner : Fin (7+(3+k)+1) → Tape, ∃ verdict : Tape,
    clockedSATPost q k U base blocks query inp bound answer inp inner verdict ∧
    w = restoreRegistersWork (resetWork inner verdict) ∧ a = inp ∧ OutAcc [] out

theorem restoreAfterReset_correct {r k : Nat} (q : Polynomial Nat) (U : Finset (Fin r))
    (base blocks query : List Bool) (inp : Tape) (hp : Parked inp)
    (bound : Nat) (hb : 1 ≤ bound) (hq : q.eval query.length = bound) (answer : Prop) :
    (restoreRegistersTM k).HoareTime (resetPost q k U base blocks query inp bound answer)
      (restoredPost q k U base blocks query inp bound answer) (4*r+2*query.length+4*bound+35) := by
  rintro a w out ⟨inner,verdict,hsat,hw,ha,ho⟩
  subst a
  subst w
  have hwp := resetWork_parked q U base blocks query inp verdict bound answer hb hq inner hsat
  obtain ⟨h1,h2,h7,h8,h9⟩ := resetWork_registers q U base blocks query inp verdict bound answer inner hsat
  rw [hq] at h8 h9
  have hc := restoreRegistersTM_correct r query.length bound inp (resetWork inner verdict) [] hp
    hwp h1 h2 h7 h8 h9
  obtain ⟨c,t,ht,hr,hh,ha,hw,ho⟩ := hc inp (resetWork inner verdict) out ⟨rfl,rfl,ho⟩
  exact ⟨c,t,ht,hr,hh,inner,verdict,hsat,hw,ha,ho⟩

def restoredCompletionTM {k : Nat} (q : Polynomial Nat) (M : TM k) :=
  seqTM (resettingCompletionTM q M) (restoreRegistersTM k)

theorem restoredCompletionTM_correct {d r k : Nat} (q : Polynomial Nat)
    (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r))
    (M : TM k) (T : Nat → Nat) (hM : M.DecidesInTime SAT.language T)
    (hq : ∀ L, q.eval L = T L+L+2) (inp : Tape) (hp : Parked inp) :
    let base := SAT.CNF.encode (assembledBase Q C)
    let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
    let query := SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
      PositiveCompletionCNF.containerExclusions U)
    let bound := T query.length+query.length+2
    (restoredCompletionTM q M).HoareTime
      (EmitPred inp (frameWork (m := 1) (queryDecisionWork (3+k) U 1 0 base blocks [])
        (fun _ => accumulatorTape [])) [])
      (restoredPost q k U base blocks query inp bound
        (PositiveCompletion.Available (IsRAF Q C) G.toFinset U))
      (dynamicQueryTime base.length blocks.length r+query.length+6+
        setupTime q query.length+T query.length+1+6*bound+11+1+(k+2)*(6*bound+10)+1+
        1+4*r+2*query.length+4*bound+35) := by
  dsimp only
  have h1 := resettingCompletionTM_correct q Q C G U M T hM hq inp hp
  have h2 := restoreAfterReset_correct (k := k) q U
    (SAT.CNF.encode (assembledBase Q C)) (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G))
    (SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
      PositiveCompletionCNF.containerExclusions U)) inp hp _ (by omega) (hq _)
    (PositiveCompletion.Available (IsRAF Q C) G.toFinset U)
  apply (seqTM_hoareTime _ _ h1 ?_ h2).mono_bound (by omega)
  rintro a w out ⟨inner,verdict,hsat,hw,ha,ho⟩
  subst a
  subst w
  have hwp := resetWork_parked q U _ _ _ inp verdict _ _ (by omega) (hq _) inner hsat
  refine ⟨inner,verdict,hsat,?_,hp.transitionInput_eq_self,?_⟩
  · funext i
    exact (hwp i).transitionTape_eq_self
  · rw [ho.parked.transitionTape_eq_self]
    exact ho

end IrrRAFEnumeration.CompletionQuery
