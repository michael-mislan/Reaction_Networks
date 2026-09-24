import proofs.IrrRAFEnumeration.CompletionBufferedSAT

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM PolynomialClockSetup

abbrev bufferedCount (k : Nat) := 7+(3+k)+1+1
def completionFuel (k : Nat) : Fin (bufferedCount k) := ⟨9,by unfold bufferedCount; omega⟩
def completionFlag (k : Nat) : Fin (bufferedCount k) := ⟨3,by unfold bufferedCount; omega⟩
def completionOutput (k : Nat) : Fin (bufferedCount k) := Fin.last (7+(3+k)+1)
def bufferedWork {k : Nat} (inner : Fin (7+(3+k)+1) → Tape) (verdict : Tape) :=
  frameWork (m := 1) inner (fun _ => verdict)

theorem dynamicWork_invariant {r : Nat} (U : Finset (Fin r)) (pos index : Nat)
    (base blocks : List Bool) : ∀ i, (dynamicWork U pos index base blocks i).StartInvariant := by
  intro i
  exact ⟨by fin_cases i <;> rfl,(dynamicWork_parked U pos index base blocks i).2⟩

theorem queryDecisionWork_invariant {r : Nat} (k : Nat) (U : Finset (Fin r))
    (pos index : Nat) (base blocks query : List Bool) :
    ∀ i, (queryDecisionWork k U pos index base blocks query i).StartInvariant := by
  intro i
  unfold queryDecisionWork queryPrefix frameWork
  split
  · split
    · exact dynamicWork_invariant _ _ _ _ _ _
    · exact ⟨rfl,(parked_regTape _).2⟩
  · exact (Tape.StartInvariant.init_ofBool query).move Dir3.right

/-- The sequence boundary already performs the required head normalization. -/
theorem transitionTape_normalizes (t : Tape) (h : t.StartInvariant) :
    transitionTape t = normalizeScratchHead t := by
  exact normalizeScratchHead_action t h

theorem bufferedWork_ready {r k : Nat} (q : Polynomial Nat) (U : Finset (Fin r))
    (base blocks query : List Bool) (inp a verdict : Tape) (bound : Nat) (answer : Prop)
    (inner : Fin (7+(3+k)+1) → Tape)
    (h : clockedSATPost q k U base blocks query inp bound answer a inner verdict) :
    (∀ i, (bufferedWork inner verdict i).StartInvariant) ∧
    bufferedWork inner verdict (completionFuel k) = regTape (q.eval query.length) ∧
    bufferedWork inner verdict (completionFlag k) = regTape 0 ∧
    bufferedWork inner verdict (completionOutput k) = verdict := by
  obtain ⟨ha,inside,he,hclock,hv,hinv,hfoot,hout⟩ := h
  have hn9 : 9 < 7+(3+k)+1 := by omega
  have hn3 : 3 < 7+(3+k)+1 := by omega
  have hm9 : 9 < 7+(3+k+1) := by omega
  have hm3 : 3 < 7+(3+k) := by omega
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    unfold bufferedWork frameWork
    split
    · rw [he]
      unfold placedClockWork
      split
      · exact hinv _
      · exact queryDecisionWork_invariant _ _ _ _ _ _ _ _
    · exact hout.1
  · have hc := hclock (2 : Fin 3)
    change inside ⟨2,by omega⟩ = regTape (q.eval query.length) at hc
    simpa [bufferedWork,frameWork,completionFuel,hn9,hm9,he,placedClockWork,
      placeWorkInMiddle,placeWorkCoord] using hc
  · simp [bufferedWork,frameWork,completionFlag,hn3,hm3,he,placedClockWork,
      placeWorkInMiddle,queryDecisionWork,queryPrefix,dynamicWork,maskWork]
  · simp [bufferedWork,frameWork,completionOutput]

def captureEntry {r : Nat} (q : Polynomial Nat) (k : Nat) (U : Finset (Fin r))
    (base blocks query : List Bool) (inp : Tape) (bound : Nat) (answer : Prop) :
    TM.TapePred (bufferedCount k) := fun a w out =>
  ∃ inner : Fin (7+(3+k)+1) → Tape, ∃ verdict : Tape,
    clockedSATPost q k U base blocks query inp bound answer a inner verdict ∧
    w = (fun i => normalizeScratchHead (bufferedWork inner verdict i)) ∧ OutAcc [] out

def capturedPost {r : Nat} (q : Polynomial Nat) (k : Nat) (U : Finset (Fin r))
    (base blocks query : List Bool) (inp : Tape) (bound : Nat) (answer : Prop) :
    TM.TapePred (bufferedCount k) := fun a w out =>
  ∃ inner : Fin (7+(3+k)+1) → Tape, ∃ verdict : Tape,
    clockedSATPost q k U base blocks query inp bound answer inp inner verdict ∧
    w = Function.update
      (Function.update (fun i => normalizeScratchHead (bufferedWork inner verdict i))
        (completionFlag k) (regTape (verdictNat (verdict.cells 1))))
      (completionOutput k) (parkedInput []) ∧ a = inp ∧ OutAcc [] out

theorem captureOutput_correct {r k : Nat} (q : Polynomial Nat) (U : Finset (Fin r))
    (base blocks query : List Bool) (inp : Tape) (hp : Parked inp)
    (bound : Nat) (hb : 1 ≤ bound) (hq : q.eval query.length = bound) (answer : Prop) :
    (verdictResetTM (completionFuel k) (completionOutput k) (completionFlag k)).HoareTime
      (captureEntry q k U base blocks query inp bound answer)
      (capturedPost q k U base blocks query inp bound answer) (6*bound+11) := by
  rintro a w out ⟨inner,verdict,hsat,hw,ho⟩
  have ha := hsat.1
  subst a
  subst w
  obtain ⟨hinv,hfuel,hflag,hsrc⟩ := bufferedWork_ready q U base blocks query inp inp verdict
    bound answer inner hsat
  have hs : ScratchFootprint bound verdict := by
    obtain ⟨_,inside,_,_,_,_,_,hv⟩ := hsat
    exact hv
  let W := fun i => normalizeScratchHead (bufferedWork inner verdict i)
  have hwp : ∀ i, Parked (W i) := fun i => normalizeScratchHead_parked _ (hinv i)
  have hf : W (completionFuel k) = regTape bound := by
    simp only [W,hfuel,hq]
    exact normalizeScratchHead_eq _ (parked_regTape _)
  have hfl : W (completionFlag k) = regTape 0 := by
    simp only [W,hflag]
    exact normalizeScratchHead_eq _ (parked_regTape _)
  have hsource : W (completionOutput k) = normalizeScratchHead verdict := by simp [W,hsrc]
  have hhead : (W (completionOutput k)).head ≤ bound := by
    rw [hsource]
    exact max_le hb hs.2.1
  have hc := verdictResetTM_correct (completionFuel k) (completionOutput k) (completionFlag k)
    (by intro h; have := congrArg Fin.val h; simp [completionOutput,completionFuel] at this; omega)
    (by intro h; have := congrArg Fin.val h; simp [completionFlag,completionFuel] at this)
    (by intro h; have := congrArg Fin.val h; simp [completionOutput,completionFlag] at this; omega)
    bound inp W [] hp hwp hf hfl
    (by simpa [hsource,normalizeScratchHead] using hs.1.1)
    (by simpa [hsource,normalizeScratchHead] using hs.2.2)
  obtain ⟨c,t,ht,hr,hh,ha,hw,ho⟩ := hc inp W out ⟨rfl,rfl,ho⟩
  refine ⟨c,t,by omega,hr,hh,inner,verdict,hsat,?_,ha,ho⟩
  simpa only [hsource,normalizeScratchHead] using hw

def capturingCompletionTM {k : Nat} (q : Polynomial Nat) (M : TM k) :=
  seqTM (bufferedCompletionTM q M)
    (verdictResetTM (completionFuel k) (completionOutput k) (completionFlag k))

theorem capturingCompletionTM_correct {d r k : Nat} (q : Polynomial Nat)
    (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r))
    (M : TM k) (T : Nat → Nat) (hM : M.DecidesInTime SAT.language T)
    (hq : ∀ L, q.eval L = T L+L+2) (inp : Tape) (hp : Parked inp) :
    let base := SAT.CNF.encode (assembledBase Q C)
    let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
    let query := SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
      PositiveCompletionCNF.containerExclusions U)
    (capturingCompletionTM q M).HoareTime
      (EmitPred inp (frameWork (m := 1) (queryDecisionWork (3+k) U 1 0 base blocks [])
        (fun _ => accumulatorTape [])) [])
      (capturedPost q k U base blocks query inp (T query.length+query.length+2)
        (PositiveCompletion.Available (IsRAF Q C) G.toFinset U))
      (dynamicQueryTime base.length blocks.length r+query.length+6+
        setupTime q query.length+T query.length+1+6*(T query.length+query.length+2)+11) := by
  dsimp only
  have h1 := bufferedCompletionTM_correct q Q C G U M T hM inp hp
  have h2 := captureOutput_correct (k := k) q U
    (SAT.CNF.encode (assembledBase Q C)) (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G))
    (SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
      PositiveCompletionCNF.containerExclusions U)) inp hp _ (by omega) (hq _)
    (PositiveCompletion.Available (IsRAF Q C) G.toFinset U)
  apply (seqTM_hoareTime _ _ h1 ?_ h2).mono_bound (by omega)
  rintro a w out ⟨inner,verdict,hw,hsat,ho⟩
  have ha := hsat.1
  subst a
  subst w
  obtain ⟨hinv,_,_,_⟩ := bufferedWork_ready q U _ _ _ inp inp verdict _ _ inner hsat
  refine ⟨inner,verdict,?_,?_,?_⟩
  · rw [hp.transitionInput_eq_self]
    exact hsat
  · funext i
    exact transitionTape_normalizes _ (hinv i)
  · rw [ho.parked.transitionTape_eq_self]
    exact ho

end IrrRAFEnumeration.CompletionQuery
