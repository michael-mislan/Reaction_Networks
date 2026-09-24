import proofs.IrrRAFEnumeration.CompletionClearMany

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM PolynomialClockSetup

def completionScratch (k : Nat) : List (Fin (bufferedCount k)) :=
  (List.finRange (k+2)).map (fun i => ⟨10+i.val,by unfold bufferedCount; omega⟩)

theorem completionScratch_ge {k : Nat} {i : Fin (bufferedCount k)}
    (h : i ∈ completionScratch k) : 10 ≤ i.val := by
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp h
  simp

theorem completionScratch_no_fuel (k : Nat) : completionFuel k ∉ completionScratch k := by
  intro h
  have := completionScratch_ge h
  simp [completionFuel] at this

theorem normalized_footprint {b : Nat} {t : Tape} (hb : 1 ≤ b)
    (h : ScratchFootprint b t) : ScratchFootprint b (normalizeScratchHead t) :=
  ⟨h.1,max_le hb h.2.1,h.2.2⟩

theorem bufferedWork_scratch {r k : Nat} (q : Polynomial Nat) (U : Finset (Fin r))
    (base blocks query : List Bool) (inp a verdict : Tape) (bound : Nat) (answer : Prop)
    (inner : Fin (7+(3+k)+1) → Tape)
    (h : clockedSATPost q k U base blocks query inp bound answer a inner verdict)
    (i : Fin (bufferedCount k)) (hi : 10 ≤ i.val) :
    ScratchFootprint bound (bufferedWork inner verdict i) := by
  obtain ⟨_,inside,he,_,_,_,hfoot,hout⟩ := h
  by_cases hn : i.val < 7+(3+k)+1
  · have hl : 7 ≤ i.val := by omega
    have hu : i.val < 7+(3+k+1) := by omega
    have hc : i.val-7 < 3+k+1 := by omega
    have hf := hfoot ⟨i.val-7,hc⟩ (by dsimp; omega)
    simpa [bufferedWork,frameWork,hn,he,placedClockWork,placeWorkInMiddle,
      placeWorkCoord,hl,hu] using hf
  · simpa [bufferedWork,frameWork,hn] using hout

def capturedWork {k : Nat} (inner : Fin (7+(3+k)+1) → Tape) (verdict : Tape) :=
  Function.update
    (Function.update (fun i => normalizeScratchHead (bufferedWork inner verdict i))
      (completionFlag k) (regTape (verdictNat (verdict.cells 1))))
    (completionOutput k) (parkedInput [])

theorem capturedWork_ready {r k : Nat} (q : Polynomial Nat) (U : Finset (Fin r))
    (base blocks query : List Bool) (inp verdict : Tape) (bound : Nat) (answer : Prop)
    (hb : 1 ≤ bound) (hq : q.eval query.length = bound)
    (inner : Fin (7+(3+k)+1) → Tape)
    (h : clockedSATPost q k U base blocks query inp bound answer inp inner verdict) :
    (∀ i, Parked (capturedWork inner verdict i)) ∧
    capturedWork inner verdict (completionFuel k) = regTape bound ∧
    (∀ i ∈ completionScratch k, ScratchFootprint bound (capturedWork inner verdict i)) := by
  obtain ⟨hinv,hfuel,_,_⟩ := bufferedWork_ready q U base blocks query inp inp verdict
    bound answer inner h
  have hfo : completionFuel k ≠ completionOutput k := by
    intro he; have := congrArg Fin.val he; simp [completionFuel,completionOutput] at this; omega
  have hff : completionFuel k ≠ completionFlag k := by
    intro he; have := congrArg Fin.val he; simp [completionFuel,completionFlag] at this
  refine ⟨?_,?_,?_⟩
  · intro i
    by_cases ho : i = completionOutput k
    · subst i
      simpa [capturedWork] using parkedInput_parked ([] : List Bool)
    · by_cases hf : i = completionFlag k
      · subst i
        simpa [capturedWork,Function.update_of_ne ho] using parked_regTape (verdictNat (verdict.cells 1))
      · simpa [capturedWork,Function.update_of_ne ho,Function.update_of_ne hf] using
          normalizeScratchHead_parked _ (hinv i)
  · simp only [capturedWork,Function.update_of_ne hfo,Function.update_of_ne hff,hfuel,hq]
    exact normalizeScratchHead_eq _ (parked_regTape _)
  · intro i hi
    have hge := completionScratch_ge hi
    have hf : i ≠ completionFlag k := by
      intro he; subst i; simp [completionFlag] at hge
    by_cases ho : i = completionOutput k
    · subst i
      simpa [capturedWork] using blank_footprint hb
    · simpa [capturedWork,Function.update_of_ne ho,Function.update_of_ne hf] using
        normalized_footprint hb (bufferedWork_scratch q U base blocks query inp inp verdict
          bound answer inner h i hge)

def resetPost {r : Nat} (q : Polynomial Nat) (k : Nat) (U : Finset (Fin r))
    (base blocks query : List Bool) (inp : Tape) (bound : Nat) (answer : Prop) :
    TM.TapePred (bufferedCount k) := fun a w out =>
  ∃ inner : Fin (7+(3+k)+1) → Tape, ∃ verdict : Tape,
    clockedSATPost q k U base blocks query inp bound answer inp inner verdict ∧
    w = clearedWork (capturedWork inner verdict) (completionScratch k) ∧ a = inp ∧ OutAcc [] out

theorem clearCaptured_correct {r k : Nat} (q : Polynomial Nat) (U : Finset (Fin r))
    (base blocks query : List Bool) (inp : Tape) (hp : Parked inp)
    (bound : Nat) (hb : 1 ≤ bound) (hq : q.eval query.length = bound) (answer : Prop) :
    (clearManyTM (completionFuel k) (completionScratch k)).HoareTime
      (capturedPost q k U base blocks query inp bound answer)
      (resetPost q k U base blocks query inp bound answer) ((k+2)*(6*bound+10)+1) := by
  rintro a w out ⟨inner,verdict,hsat,hw,ha,ho⟩
  subst a
  subst w
  obtain ⟨hwp,hf,hs⟩ := capturedWork_ready q U base blocks query inp verdict bound answer hb hq inner hsat
  have hc := clearManyTM_correct (completionFuel k) (completionScratch k) bound hb
    (completionScratch_no_fuel k) inp (capturedWork inner verdict) [] hp hwp hf hs
  obtain ⟨c,t,ht,hr,hh,ha,hw,ho⟩ := hc inp (capturedWork inner verdict) out ⟨rfl,rfl,ho⟩
  refine ⟨c,t,?_,hr,hh,inner,verdict,hsat,hw,ha,ho⟩
  simpa [completionScratch] using ht

def resettingCompletionTM {k : Nat} (q : Polynomial Nat) (M : TM k) :=
  seqTM (capturingCompletionTM q M) (clearManyTM (completionFuel k) (completionScratch k))

theorem resettingCompletionTM_correct {d r k : Nat} (q : Polynomial Nat)
    (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r))
    (M : TM k) (T : Nat → Nat) (hM : M.DecidesInTime SAT.language T)
    (hq : ∀ L, q.eval L = T L+L+2) (inp : Tape) (hp : Parked inp) :
    let base := SAT.CNF.encode (assembledBase Q C)
    let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
    let query := SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
      PositiveCompletionCNF.containerExclusions U)
    let bound := T query.length+query.length+2
    (resettingCompletionTM q M).HoareTime
      (EmitPred inp (frameWork (m := 1) (queryDecisionWork (3+k) U 1 0 base blocks [])
        (fun _ => accumulatorTape [])) [])
      (resetPost q k U base blocks query inp bound
        (PositiveCompletion.Available (IsRAF Q C) G.toFinset U))
      (dynamicQueryTime base.length blocks.length r+query.length+6+
        setupTime q query.length+T query.length+1+6*bound+11+1+(k+2)*(6*bound+10)+1) := by
  dsimp only
  have h1 := capturingCompletionTM_correct q Q C G U M T hM hq inp hp
  have h2 := clearCaptured_correct (k := k) q U
    (SAT.CNF.encode (assembledBase Q C)) (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G))
    (SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
      PositiveCompletionCNF.containerExclusions U)) inp hp _ (by omega) (hq _)
    (PositiveCompletion.Available (IsRAF Q C) G.toFinset U)
  apply (seqTM_hoareTime _ _ h1 ?_ h2).mono_bound (by omega)
  rintro a w out ⟨inner,verdict,hsat,hw,ha,ho⟩
  subst a
  subst w
  obtain ⟨hwp,_,_⟩ := capturedWork_ready q U _ _ _ inp verdict _ _ (by omega) (hq _) inner hsat
  refine ⟨inner,verdict,hsat,?_,hp.transitionInput_eq_self,?_⟩
  · funext i
    exact (hwp i).transitionTape_eq_self
  · rw [ho.parked.transitionTape_eq_self]
    exact ho

end IrrRAFEnumeration.CompletionQuery
