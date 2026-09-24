import proofs.IrrRAFEnumeration.CompletionRoundReset

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM PolynomialClockSetup

def enumFlag (k : Nat) := Fin.castAdd 1 (Fin.castAdd 1 (Fin.castAdd 1 (trialFlag k)))

def enumFlagWork {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks records : List Bool) (j count bit : Nat) :=
  frameWork (m := 1)
    (frameWork (m := 1)
      (frameWork (m := 1) (trialWork k U base blocks j bit) (fun _ => regTape r))
      (fun _ => accumulatorTape records))
    (fun _ => regTape count)

def enumCompletionTM {k : Nat} (q : Polynomial Nat) (M : TM k) :=
  ((((restoredCompletionTM q M).liftTM 1).liftTM 1).liftTM 1).liftTM 1

def enumResult {r : Nat} (k : Nat) (U : Finset (Fin r)) (base blocks records : List Bool)
    (j count : Nat) (inp : Tape) (answer : Prop) :
    TM.TapePred ((((bufferedCount k+1)+1)+1)+1) := fun a w out =>
  ∃ bit : Nat, bit ≤ 1 ∧ (bit = 1 ↔ answer) ∧
    EmitPred inp (enumFlagWork k U base blocks records j count bit) [] a w out

theorem enumFlagWork_parked {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks records : List Bool) (j count bit : Nat) :
    ∀ i, Parked (enumFlagWork k U base blocks records j count bit i) := by
  intro i
  unfold enumFlagWork frameWork
  split
  · split
    · split
      · exact trialWork_parked _ _ _ _ _ _ _
      · exact parked_regTape _
    · exact (accumulatorTape_outAcc _).parked
  · exact parked_regTape _

theorem enumFlagWork_flag {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks records : List Bool) (j count bit : Nat) :
    enumFlagWork k U base blocks records j count bit (enumFlag k) = regTape bit := by
  simp only [enumFlagWork,enumFlag,frameWork,Fin.val_castAdd,
    dif_pos (trialFlag k).isLt]
  exact trialWork_flag _ _ _ _ _ _

theorem enumFlagWork_update_flag {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks records : List Bool) (j count bit v : Nat) :
    Function.update (enumFlagWork k U base blocks records j count bit) (enumFlag k) (regTape v) =
      enumFlagWork k U base blocks records j count v := by
  unfold enumFlagWork enumFlag
  rw [← frameWork_update,← frameWork_update,← frameWork_update,trialWork_update_flag]

/-- The real completion query preserves the entire enumerator state, including
records and count, and exposes its result only in the saved Boolean register. -/
theorem enumCompletionTM_correct {d r k : Nat} (q : Polynomial Nat)
    (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) (j : Nat)
    (M : TM k) (T : Nat → Nat) (hM : M.DecidesInTime SAT.language T)
    (hq : ∀ L, q.eval L = T L+L+2) (inp : Tape) (hp : Parked inp) :
    let base := SAT.CNF.encode (assembledBase Q C)
    let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
    let query := SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
      PositiveCompletionCNF.containerExclusions U)
    (enumCompletionTM q M).HoareTime
      (EmitPred inp (enumWork k U base blocks (storedMasks G) j G.length) [])
      (enumResult k U base blocks (storedMasks G) j G.length inp
        (PositiveCompletion.Available (IsRAF Q C) G.toFinset U))
      (completionCallTime k q T r base.length blocks.length query.length) := by
  dsimp only
  let base := SAT.CNF.encode (assembledBase Q C)
  let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
  let call := restoredCompletionTM q M
  have h := liftCompletionResult_correct call U base blocks j inp _ _
    (reusableCompletionTM_correct q Q C G U M T hM hq inp hp)
  rintro a w out ⟨ha,hw,ho⟩
  subst a
  subst w
  obtain ⟨c,t,ht,hr,hh,bit,hbit,hans,ha,hw,ho'⟩ :=
    h inp (trialWork k U base blocks j 0) out ⟨rfl,rfl,ho⟩
  have h1 := liftTM_reaches_frame (call.liftTM 1) 1 (fun _ => regTape r)
    (fun _ _ => parked_regTape _) hr
  have h2 := liftTM_reaches_frame ((call.liftTM 1).liftTM 1) 1
    (fun _ => accumulatorTape (storedMasks G)) (fun _ _ => (accumulatorTape_outAcc _).parked) h1
  have h3 := liftTM_reaches_frame (((call.liftTM 1).liftTM 1).liftTM 1) 1
    (fun _ => regTape G.length) (fun _ _ => parked_regTape _) h2
  refine ⟨_,t,ht,h3,hh,bit,hbit,hans,ha,?_,ho'⟩
  change frameWork (frameWork (frameWork c.work (fun _ => regTape r))
    (fun _ => accumulatorTape (storedMasks G))) (fun _ => regTape G.length) = _
  rw [hw]
  rfl

theorem clearEnumResult_correct {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks records : List Bool) (j count : Nat) (inp : Tape) (hp : Parked inp) (answer : Prop) :
    (clearRegTM (enumFlag k)).HoareTime (enumResult k U base blocks records j count inp answer)
      (EmitPred inp (enumWork k U base blocks records j count) []) 6 := by
  rintro a w out ⟨bit,hbit,hans,hpre⟩
  have h := clearRegTM_hoareTime (enumFlag k) bit inp
    (enumFlagWork k U base blocks records j count bit) [] hp
    (fun i _ => enumFlagWork_parked _ _ _ _ _ _ _ _ i) (enumFlagWork_flag _ _ _ _ _ _ _ _)
  rw [enumFlagWork_update_flag] at h
  exact h.mono_bound (by omega) a w out hpre

end IrrRAFEnumeration.CompletionQuery
