import proofs.IrrRAFEnumeration.CompletionClockedQuery

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM PolynomialClockSetup

def clockedSATPhase {k : Nat} (M : TM k) : TM (7+(3+k)+1) :=
  placeWorkTM 7 0 (placeWorkTM 3 0 (retargetInputStarted M))

theorem clockedSATPhase_preserves_real {k : Nat} (M : TM k)
    {c c' : Cfg (7+(3+k)+1) (clockedSATPhase M).Q} {t : Nat}
    (hr : (clockedSATPhase M).reachesIn t c c') (hp : Parked c.input) : c'.input = c.input := by
  induction hr with
  | zero => rfl
  | @step a b c t hs _ ih =>
    have he : b.input = a.input := by
      simp only [TM.step] at hs
      split at hs
      · contradiction
      · cases hs
        exact hp.move_idle
    exact (ih (he.symm ▸ hp)).trans he

theorem clockWork_parked (p : Polynomial Nat) (L : Nat) :
    ∀ i, Parked (clockWork p L i) := by
  intro i
  fin_cases i <;> exact parked_regTape _

theorem clockWork_invariant (p : Polynomial Nat) (L : Nat) :
    ∀ i, (clockWork p L i).StartInvariant := by
  intro i
  exact ⟨by fin_cases i <;> rfl,(clockWork_parked p L i).2⟩

/-- Mutable tapes retain valid sentinels even when they halt with head zero. -/
theorem run_work_output_invariant {n : Nat} {M : TM n}
    {c c' : Cfg n M.Q} {t : Nat} (hr : M.reachesIn t c c')
    (hw : ∀ i, (c.work i).StartInvariant) (ho : c.output.StartInvariant) :
    (∀ i, (c'.work i).StartInvariant) ∧ c'.output.StartInvariant := by
  induction hr with
  | zero => exact ⟨hw,ho⟩
  | @step a b c t hs _ ih =>
    apply ih
    · intro i
      simp only [TM.step] at hs
      split at hs
      · contradiction
      · simp only [Option.some.injEq] at hs
        rw [← hs]
        exact (hw i).writeAndMove _ _
    · simp only [TM.step] at hs
      split at hs
      · contradiction
      · simp only [Option.some.injEq] at hs
        rw [← hs]
        exact ho.writeAndMove _ _

/-- Only this finite footprint, not the contents of scratch, is needed by reset. -/
def ScratchFootprint (bound : Nat) (t : Tape) : Prop :=
  t.StartInvariant ∧ t.head ≤ bound ∧ ∀ j, bound < j → t.cells j = Γ.blank

def clockedSATPost {r : Nat} (p : Polynomial Nat) (k : Nat)
    (U : Finset (Fin r)) (base blocks query : List Bool) (inp : Tape)
    (bound : Nat) (answer : Prop) : TM.TapePred (7+(3+k)+1) := fun a w out =>
  a = inp ∧ ∃ inner : Fin (3+k+1) → Tape,
    w = placedClockWork 7 0 (queryDecisionWork (3+k) U (1+r) r base blocks query) inner ∧
    (∀ i : Fin 3, inner (Fin.castAdd (k+1) i) = clockWork p query.length i) ∧
    (out.cells 1 = Γ.one ↔ answer) ∧
    (∀ i, (inner i).StartInvariant) ∧
    (∀ i : Fin (3+k+1), 3 ≤ i.val → ScratchFootprint bound (inner i)) ∧
    ScratchFootprint bound out

theorem clockedSATPhase_correct {d r k : Nat} (p : Polynomial Nat)
    (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r))
    (M : TM k) (T : Nat → Nat) (hM : M.DecidesInTime SAT.language T)
    (inp : Tape) (hp : Parked inp) :
    let base := SAT.CNF.encode (assembledBase Q C)
    let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
    let query := SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
      PositiveCompletionCNF.containerExclusions U)
    (clockedSATPhase M).HoareTime
      (EmitPred inp (clockedQueryWork p k U (1+r) r base blocks query) [])
      (clockedSATPost p k U base blocks query inp (T query.length+query.length+2)
        (PositiveCompletion.Available (IsRAF Q C) G.toFinset U)) (T query.length) := by
  dsimp only
  let base := SAT.CNF.encode (assembledBase Q C)
  let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
  let query := SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
    PositiveCompletionCNF.containerExclusions U)
  let W := clockQueryInner k (clockWork p query.length) query
  let E := queryDecisionWork (3+k) U (1+r) r base blocks query
  rintro a w out ⟨ha,hw,ho⟩
  subst a
  subst w
  have hout : out = (Tape.init []).move Dir3.right := ho.eq outAcc_nil_init
  subst out
  have hwP : ∀ i, Parked (W i) := by
    intro i
    unfold W clockQueryInner frameWork
    split
    · split
      · exact clockWork_parked _ _ _
      · exact parked_regTape _
    · exact parkedInput_parked _
  have hinv : ∀ i : Fin (3+k+1), ¬placeWorkInMiddle (post := 0) 3 (k+1) i →
      (W i).StartInvariant := by
    intro i hi
    have hi3 : i.val < 3 := by unfold placeWorkInMiddle at hi; omega
    have hik : i.val < 3+k := by omega
    simpa [W,clockQueryInner,frameWork,hik,hi3] using clockWork_invariant p query.length ⟨i.val,hi3⟩
  obtain ⟨c,t,ht,hr,hh,hframe,hverdict⟩ := completionSAT_run Q C G U M T hM 3 0 W
    hinv (fun i _ => (hwP i).1) inp
  have hentry : placeWorkCfg (retargetInputStarted M) 3 0 W
      (retargetInputStartedCfg M query inp) =
      (⟨(placeWorkTM 3 0 (retargetInputStarted M)).qstart,inp,W,
        (Tape.init []).move Dir3.right⟩ : Cfg (3+k+1) M.Q) := by
    refine Cfg.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · funext i
      by_cases hi : placeWorkInMiddle (post := 0) 3 (k+1) i
      · have hlo : ¬i.val < 3 := by unfold placeWorkInMiddle at hi; omega
        by_cases hik : i.val < 3+k
        · have hsub : i.val-3 < k := by unfold placeWorkInMiddle at hi; omega
          simp [placeWorkCfg,hi,retargetInputStartedCfg,placeWorkCoord,W,
            clockQueryInner,frameWork,hik,hlo,hsub,regTape,Tape.init,Tape.move]
          funext j
          by_cases hj : j = 0 <;> simp [regCells,hj]
        · have hsub : ¬i.val-3 < k := by omega
          simp [placeWorkCfg,hi,retargetInputStartedCfg,placeWorkCoord,W,
            clockQueryInner,frameWork,hik,hsub,parkedInput]
          rfl
      · exact placeWorkCfg_work_extra _ _ _ _ _ i hi
    · rfl
  rw [hentry] at hr
  have he : ∀ i, ¬placeWorkInMiddle (post := 0) 7 (3+k+1) i → (E i).read ≠ Γ.start := by
    intro i hi
    have hi7 : i.val < 7 := by unfold placeWorkInMiddle at hi; omega
    have hik : i.val < 7+(3+k) := by omega
    have hp' := dynamicWork_parked U (1+r) r base blocks ⟨i.val,hi7⟩
    simpa [E,queryDecisionWork,queryPrefix,frameWork,hik,hi7] using hp'.read_ne_start
  have hrun := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    (placeWorkTM 3 0 (retargetInputStarted M)) 7 0 E hr he
  have hwInv : ∀ i, (W i).StartInvariant := by
    intro i
    unfold W clockQueryInner frameWork
    split
    · split
      · exact clockWork_invariant _ _ _
      · exact ⟨rfl,(parked_regTape _).2⟩
    · exact (Tape.StartInvariant.init_ofBool query).move Dir3.right
  have houtInv : ((Tape.init []).move Dir3.right).StartInvariant :=
    Tape.StartInvariant.init_nil.move Dir3.right
  obtain ⟨hwEnd,hoEnd⟩ := run_work_output_invariant hr hwInv houtInv
  have hsupport : ∀ i : Fin (3+k+1), 3 ≤ i.val →
      ScratchFootprint (T query.length+query.length+2) (c.work i) := by
    intro i hi
    have hhead : (W i).head = 1 := by
      unfold W clockQueryInner frameWork
      split
      · split
        · rename_i h
          change i.val < 3 at h
          omega
        · rfl
      · rfl
    have htail : ∀ j, T query.length+query.length+2 < j → (W i).cells j = Γ.blank := by
      intro j hj
      have hj0 : j ≠ 0 := by omega
      have hjlen : query.length ≤ j-1 := by omega
      unfold W clockQueryInner frameWork
      split
      · split
        · rename_i h
          change i.val < 3 at h
          omega
        · simp [regTape,regCells,hj0]
      · change (Tape.init (query.map Γ.ofBool)).cells j = Γ.blank
        have hhj : j = (j-1)+1 := by omega
        rw [hhj]
        exact Tape.init_ofBool_cells_ge query (j-1) hjlen
    refine ⟨hwEnd i,?_,workCells_blank_after_run i hr ?_ htail⟩
    · have hb := (placeWorkTM 3 0 (retargetInputStarted M)).work_head_reachesIn_bound hr i
      change (c.work i).head ≤ (W i).head+t at hb
      dsimp only [query] at hhead ⊢
      omega
    · change (W i).head+t ≤ _
      rw [hhead]
      dsimp only [query] at ht ⊢
      omega
  have houtput : ScratchFootprint (T query.length+query.length+2) c.output := by
    refine ⟨hoEnd,?_,?_⟩
    · have hb := (placeWorkTM 3 0 (retargetInputStarted M)).output_head_reachesIn_bound hr
      change c.output.head ≤ 1+t at hb
      dsimp only [query] at ht ⊢
      omega
    · intro j hj
      rw [TM.reachesIn_output_cells_far hr j (by
        change 1+t < j
        dsimp only [query] at ht hj
        omega)]
      change (Tape.init []).cells j = Γ.blank
      have hj0 : j ≠ 0 := by omega
      simp [Tape.init,hj0]
  refine ⟨_,t,ht,hrun,hh,clockedSATPhase_preserves_real M hrun hp,c.work,rfl,?_,
    hverdict,?_,?_,?_⟩
  · intro i
    have hi : ¬placeWorkInMiddle (post := 0) 3 (k+1) (Fin.castAdd (k+1) i) := by
      simp [placeWorkInMiddle]
    rw [hframe _ hi]
    have hik : i.val < 3+k := by have := i.isLt; omega
    simp [W,clockQueryInner,frameWork,i.isLt,hik,query,List.append_assoc]
  · exact hwEnd
  · simpa only [query,List.append_assoc] using hsupport
  · simpa only [query,List.append_assoc] using houtput

theorem clockedQueryWork_parked {r : Nat} (p : Polynomial Nat) (k : Nat)
    (U : Finset (Fin r)) (pos index : Nat) (base blocks query : List Bool) :
    ∀ i, Parked (clockedQueryWork p k U pos index base blocks query i) := by
  intro i
  unfold clockedQueryWork placedClockWork
  split
  · unfold clockQueryInner frameWork
    split
    · split
      · exact clockWork_parked _ _ _
      · exact parked_regTape _
    · exact parkedInput_parked _
  · unfold queryDecisionWork queryPrefix frameWork
    split
    · split
      · exact dynamicWork_parked _ _ _ _ _ _
      · exact parked_regTape _
    · exact parkedInput_parked _

def clockedCompletionTM {k : Nat} (q : Polynomial Nat) (M : TM k) : TM (7+(3+k)+1) :=
  seqTM (clockedQueryPrepareTM q k) (clockedSATPhase M)

/-- Query construction, executable clock initialization, and SAT execution in
one machine. The initialized clock survives the SAT call for cleanup. -/
theorem clockedCompletionTM_correct {d r k : Nat} (q : Polynomial Nat)
    (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r))
    (M : TM k) (T : Nat → Nat) (hM : M.DecidesInTime SAT.language T)
    (inp : Tape) (hp : Parked inp) :
    let base := SAT.CNF.encode (assembledBase Q C)
    let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
    let query := SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
      PositiveCompletionCNF.containerExclusions U)
    (clockedCompletionTM q M).HoareTime
      (EmitPred inp (queryDecisionWork (3+k) U 1 0 base blocks []) [])
      (clockedSATPost q k U base blocks query inp (T query.length+query.length+2)
        (PositiveCompletion.Available (IsRAF Q C) G.toFinset U))
      (dynamicQueryTime base.length blocks.length r+query.length+6+
        setupTime q query.length+T query.length) := by
  dsimp only
  have h1 := clockedQueryPrepareTM_correct q k Q C G U inp hp
  have h2 := clockedSATPhase_correct q Q C G U M T hM inp hp
  have hw := clockedQueryWork_parked q k U (1+r) r
    (SAT.CNF.encode (assembledBase Q C)) (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G))
    (SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
      PositiveCompletionCNF.containerExclusions U))
  exact (seqTM_hoareTime _ _ h1 (emitPred_transition hp hw []) h2).mono_bound (by omega)

end IrrRAFEnumeration.CompletionQuery
