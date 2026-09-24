import proofs.IrrRAFEnumeration.CompletionSizeBounds

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

/-- Test first, read its saved work-tape verdict, and repeat the body on one.
The external output is never used as a control channel. -/
def workWhileTM {n : Nat} (test body : TM n) (flag : Fin n) : TM n where
  Q := test.Q ⊕ (body.Q ⊕ Unit)
  qstart := .inl test.qstart
  qhalt := .inr (.inr ())
  δ := fun q i w o => match q with
    | .inl s =>
      if s = test.qhalt then
        (if w flag = Γ.one then .inr (.inl body.qstart) else .inr (.inr ()),
          fun j => readBackWrite (w j), readBackWrite o,
          idleDir i, fun j => idleDir (w j), idleDir o)
      else let (s',w',o',di,dw,do') := test.δ s i w o
           (.inl s',w',o',di,dw,do')
    | .inr (.inl s) =>
      if s = body.qhalt then
        (.inl test.qstart, fun j => readBackWrite (w j), readBackWrite o,
          idleDir i, fun j => idleDir (w j), idleDir o)
      else let (s',w',o',di,dw,do') := body.δ s i w o
           (.inr (.inl s'),w',o',di,dw,do')
    | .inr (.inr _) =>
        (.inr (.inr ()), fun j => readBackWrite (w j), readBackWrite o,
          idleDir i, fun j => idleDir (w j), idleDir o)
  δ_right_of_start := by
    intro q i w o
    rcases q with s | (s | u)
    · by_cases hs : s = test.qhalt
      · simp only [hs,↓reduceIte]
        exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,idleDir_right_of_start⟩
      · simp only [hs,↓reduceIte]
        exact test.δ_right_of_start s i w o
    · by_cases hs : s = body.qhalt
      · simp only [hs,↓reduceIte]
        exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,idleDir_right_of_start⟩
      · simp only [hs,↓reduceIte]
        exact body.δ_right_of_start s i w o
    · exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,idleDir_right_of_start⟩

def whileTestCfg {n : Nat} (test body : TM n) (flag : Fin n) (c : Cfg n test.Q) :
    Cfg n (workWhileTM test body flag).Q := ⟨.inl c.state,c.input,c.work,c.output⟩

def whileBodyCfg {n : Nat} (test body : TM n) (flag : Fin n) (c : Cfg n body.Q) :
    Cfg n (workWhileTM test body flag).Q := ⟨.inr (.inl c.state),c.input,c.work,c.output⟩

theorem whileTest_step {n : Nat} (test body : TM n) (flag : Fin n)
    {c c' : Cfg n test.Q} (h : test.step c = some c') :
    (workWhileTM test body flag).step (whileTestCfg test body flag c) =
      some (whileTestCfg test body flag c') := by
  have hn := state_ne_qhalt_of_step h
  simp only [TM.step,hn,↓reduceIte,Option.some.injEq] at h
  subst c'
  simp [TM.step,workWhileTM,whileTestCfg,hn]

theorem whileBody_step {n : Nat} (test body : TM n) (flag : Fin n)
    {c c' : Cfg n body.Q} (h : body.step c = some c') :
    (workWhileTM test body flag).step (whileBodyCfg test body flag c) =
      some (whileBodyCfg test body flag c') := by
  have hn := state_ne_qhalt_of_step h
  simp only [TM.step,hn,↓reduceIte,Option.some.injEq] at h
  subst c'
  simp [TM.step,workWhileTM,whileBodyCfg,hn]

theorem whileTest_exit {n : Nat} (test body : TM n) (flag : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hp : Parked inp) (hw : ∀ i, Parked (work i)) (ho : Parked out) :
    (workWhileTM test body flag).step ⟨.inl test.qhalt,inp,work,out⟩ = some
      ⟨if (work flag).read = Γ.one then .inr (.inl body.qstart) else .inr (.inr ()),inp,work,out⟩ := by
  simp only [TM.step,workWhileTM,reduceCtorEq,↓reduceIte]
  apply congrArg some
  refine Cfg.ext rfl hp.move_idle ?_ ho.writeAndMove_readBack_idle
  funext i
  exact (hw i).writeAndMove_readBack_idle

theorem whileBody_exit {n : Nat} (test body : TM n) (flag : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hp : Parked inp) (hw : ∀ i, Parked (work i)) (ho : Parked out) :
    (workWhileTM test body flag).step ⟨.inr (.inl body.qhalt),inp,work,out⟩ = some
      ⟨.inl test.qstart,inp,work,out⟩ := by
  simp only [TM.step,workWhileTM,↓reduceIte]
  apply congrArg some
  refine Cfg.ext rfl hp.move_idle ?_ ho.writeAndMove_readBack_idle
  funext i
  exact (hw i).writeAndMove_readBack_idle

def enumLoopTM {k : Nat} (q : Polynomial Nat) (M : TM k) :=
  workWhileTM (enumCompletionTM q M) (positiveRoundTM q M) (enumFlag k)

end IrrRAFEnumeration.CompletionQuery
