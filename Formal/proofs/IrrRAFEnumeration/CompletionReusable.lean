import proofs.IrrRAFEnumeration.CompletionRestore

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM PolynomialClockSetup

def completionWork {r : Nat} (k : Nat) (U : Finset (Fin r)) (base blocks : List Bool) :=
  bufferedWork (queryDecisionWork (3+k) U 1 0 base blocks []) (accumulatorTape [])

theorem lowTape_eq_iff (k : Nat) (i j : Fin 10) : lowTape k i = lowTape k j ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    exact congrArg (fun x : Fin (bufferedCount k) => x.val) h
  · exact congrArg (lowTape k)

theorem completionWork_low {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks : List Bool) (j : Fin 10) :
    completionWork k U base blocks (lowTape k j) =
      if h : j.val < 7 then dynamicWork U 1 0 base blocks ⟨j.val,h⟩ else regTape 0 := by
  have hj := j.isLt
  have h1 : j.val < 7+(3+k)+1 := by omega
  have h2 : j.val < 7+(3+k) := by omega
  simp [completionWork,bufferedWork,queryDecisionWork,queryPrefix,frameWork,lowTape,h1,h2]

theorem regTape_zero_eq_parked : regTape 0 = parkedInput [] := by
  apply Tape.ext
  · rfl
  · funext j
    by_cases hj : j = 0 <;> simp [regTape,regCells,parkedInput,Tape.init,hj]

theorem resetWork_flag {k : Nat} (inner : Fin (7+(3+k)+1) → Tape) (verdict : Tape) :
    resetWork inner verdict (lowTape k 3) = regTape (verdictNat (verdict.cells 1)) := by
  have ho : lowTape k 3 ≠ completionOutput k := by
    intro he
    have := congrArg Fin.val he
    simp [lowTape,completionOutput] at this
    omega
  have hn : lowTape k 3 ∉ completionScratch k := by
    rw [completionScratch_mem_iff]
    simp [lowTape]
  simp only [resetWork,clearedWork,if_neg hn,capturedWork,Function.update_of_ne ho]
  rfl

/-- Every scratch tape and counter returns exactly to the entry workspace;
only the designated verdict flag differs. -/
theorem restoredWork_eq_entry {r k : Nat} (q : Polynomial Nat) (U : Finset (Fin r))
    (base blocks query : List Bool) (inp verdict : Tape) (bound : Nat) (answer : Prop)
    (inner : Fin (7+(3+k)+1) → Tape)
    (h : clockedSATPost q k U base blocks query inp bound answer inp inner verdict) :
    restoreRegistersWork (resetWork inner verdict) =
      Function.update (completionWork k U base blocks) (completionFlag k)
        (regTape (verdictNat (verdict.cells 1))) := by
  have hpref := bufferedWork_prefix q U base blocks query inp verdict bound answer inner h
  funext i
  by_cases hi : i.val < 10
  · let j : Fin 10 := ⟨i.val,hi⟩
    have he : i = lowTape k j := by apply Fin.ext; rfl
    rw [he]
    clear he
    clear_value j
    have hflag : completionFlag k = lowTape k 3 := rfl
    fin_cases j
    · have hv : resetWork inner verdict (lowTape k 0) = regTape r := by
        rw [resetWork_low _ _ _ (by decide)]
        have hh := hpref (0 : Fin 7)
        change bufferedWork inner verdict (lowTape k 0) = regTape r at hh
        rw [hh]
        exact normalizeScratchHead_eq _ (parked_regTape _)
      simpa [restoreRegistersWork,hflag,lowTape_eq_iff,completionWork_low] using hv
    · simp [restoreRegistersWork,hflag,lowTape_eq_iff,completionWork_low]
      rfl
    · simp [restoreRegistersWork,hflag,lowTape_eq_iff,completionWork_low]
      rfl
    · simpa [restoreRegistersWork,hflag,lowTape_eq_iff] using resetWork_flag inner verdict
    · have hv : resetWork inner verdict (lowTape k 4) = parkedInput (containerMask U) := by
        rw [resetWork_low _ _ _ (by decide)]
        have hh := hpref (4 : Fin 7)
        change bufferedWork inner verdict (lowTape k 4) = parkedInput (containerMask U) at hh
        rw [hh]
        exact normalizeScratchHead_eq _ (parkedInput_parked _)
      simpa [restoreRegistersWork,hflag,lowTape_eq_iff,completionWork_low] using hv
    · have hv : resetWork inner verdict (lowTape k 5) = parkedInput base := by
        rw [resetWork_low _ _ _ (by decide)]
        have hh := hpref (5 : Fin 7)
        change bufferedWork inner verdict (lowTape k 5) = parkedInput base at hh
        rw [hh]
        exact normalizeScratchHead_eq _ (parkedInput_parked _)
      simpa [restoreRegistersWork,hflag,lowTape_eq_iff,completionWork_low] using hv
    · have hv : resetWork inner verdict (lowTape k 6) = parkedInput blocks := by
        rw [resetWork_low _ _ _ (by decide)]
        have hh := hpref (6 : Fin 7)
        change bufferedWork inner verdict (lowTape k 6) = parkedInput blocks at hh
        rw [hh]
        exact normalizeScratchHead_eq _ (parkedInput_parked _)
      simpa [restoreRegistersWork,hflag,lowTape_eq_iff,completionWork_low] using hv
    · simp [restoreRegistersWork,hflag,lowTape_eq_iff,completionWork_low]
    · simp [restoreRegistersWork,hflag,lowTape_eq_iff,completionWork_low]
    · simp [restoreRegistersWork,hflag,lowTape_eq_iff,completionWork_low]
  · have hge : 10 ≤ i.val := by omega
    have h1 : i ≠ lowTape k 1 := by intro he; have := congrArg Fin.val he; change i.val = 1 at this; omega
    have h2 : i ≠ lowTape k 2 := by intro he; have := congrArg Fin.val he; change i.val = 2 at this; omega
    have h7 : i ≠ lowTape k 7 := by intro he; have := congrArg Fin.val he; change i.val = 7 at this; omega
    have h8 : i ≠ lowTape k 8 := by intro he; have := congrArg Fin.val he; change i.val = 8 at this; omega
    have h9 : i ≠ lowTape k 9 := by intro he; have := congrArg Fin.val he; change i.val = 9 at this; omega
    have hf : i ≠ completionFlag k := by intro he; have := congrArg Fin.val he; change i.val = 3 at this; omega
    have hm := (completionScratch_mem_iff i).mpr hge
    simp only [restoreRegistersWork,Function.update_of_ne h1,Function.update_of_ne h2,
      Function.update_of_ne h7,Function.update_of_ne h8,Function.update_of_ne h9,
      Function.update_of_ne hf,resetWork,clearedWork,if_pos hm]
    have hnot7 : ¬i.val < 7 := by omega
    simp [completionWork,bufferedWork,queryDecisionWork,queryPrefix,frameWork,hnot7,
      regTape_zero_eq_parked,accumulatorTape,advanceInput]

def completionResult {r : Nat} (k : Nat) (U : Finset (Fin r)) (base blocks : List Bool)
    (inp : Tape) (answer : Prop) : TM.TapePred (bufferedCount k) := fun a w out =>
  ∃ bit : Nat, bit ≤ 1 ∧ (bit = 1 ↔ answer) ∧
    EmitPred inp (Function.update (completionWork k U base blocks) (completionFlag k) (regTape bit)) [] a w out

theorem restoredPost_result {r k : Nat} (q : Polynomial Nat) (U : Finset (Fin r))
    (base blocks query : List Bool) (inp : Tape) (bound : Nat) (answer : Prop)
    (a : Tape) (w : Fin (bufferedCount k) → Tape) (out : Tape)
    (h : restoredPost q k U base blocks query inp bound answer a w out) :
    completionResult k U base blocks inp answer a w out := by
  obtain ⟨inner,verdict,hsat,hw,ha,ho⟩ := h
  have he := restoredWork_eq_entry q U base blocks query inp verdict bound answer inner hsat
  obtain ⟨_,inside,_,_,hv,_,_,_⟩ := hsat
  refine ⟨verdictNat (verdict.cells 1),?_,?_,ha,hw.trans he,ho⟩
  · unfold verdictNat
    split <;> omega
  · simpa [verdictNat] using hv

/-- The actual completion call returns to its initial workspace, with one
Boolean result register for the caller to consume. -/
theorem reusableCompletionTM_correct {d r k : Nat} (q : Polynomial Nat)
    (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r))
    (M : TM k) (T : Nat → Nat) (hM : M.DecidesInTime SAT.language T)
    (hq : ∀ L, q.eval L = T L+L+2) (inp : Tape) (hp : Parked inp) :
    let base := SAT.CNF.encode (assembledBase Q C)
    let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
    let query := SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
      PositiveCompletionCNF.containerExclusions U)
    let bound := T query.length+query.length+2
    (restoredCompletionTM q M).HoareTime (EmitPred inp (completionWork k U base blocks) [])
      (completionResult k U base blocks inp (PositiveCompletion.Available (IsRAF Q C) G.toFinset U))
      (dynamicQueryTime base.length blocks.length r+query.length+6+
        setupTime q query.length+T query.length+1+6*bound+11+1+(k+2)*(6*bound+10)+1+
        1+4*r+2*query.length+4*bound+35) := by
  dsimp only
  have h := restoredCompletionTM_correct q Q C G U M T hM hq inp hp
  exact h.strengthen_post (restoredPost_result q U _ _ _ inp _ _)

end IrrRAFEnumeration.CompletionQuery
