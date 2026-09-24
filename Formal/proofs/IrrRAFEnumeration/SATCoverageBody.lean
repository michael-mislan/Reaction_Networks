import proofs.IrrRAFEnumeration.SATConflictBody

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

def coveragePattern (p s v g l c : Nat) : List Bool :=
  spanRow p 1 s ++ markedRow v g l true ++ spanRow c 1 (l-1)

def coverageAdvance (work : Fin 13 → Tape) (p s v g l c : Nat) (b : Bool) : Fin 13 → Tape :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update work 0 (regTape (p+1))) 1 (regTape (s-1)))
      2 (regTape (v+if b then 1 else 0))) 3 (regTape (g+if b then 0 else 1)))
        4 (regTape (l-1))) 5 (regTape (c+1))

def coverageBodyTM (b : Bool) : TM 13 :=
  seqTM (fixedSpanRowTM 1 0 1) (seqTM (twoMarkRowTM 2 3 4)
    (seqTM (decRegTM 4) (seqTM (fixedSpanRowTM 1 5 4)
      (seqTM (incRegTM 0) (seqTM (decRegTM 1)
        (seqTM (incRegTM 5) (incRegTM (if b then 2 else 3))))))))

/-- The output and catalyst rows share one tail register. The decrement
between them also prepares that register for the next coverage reaction. -/
theorem coverageBodyTM_correct (b : Bool) (p s v g l c B : Nat)
    (inp : Tape) (work : Fin 13 → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (h0 : work 0 = regTape p) (h1 : work 1 = regTape s)
    (h2 : work 2 = regTape v) (h3 : work 3 = regTape g)
    (h4 : work 4 = regTape l) (h5 : work 5 = regTape c)
    (hB : p ≤ B ∧ s ≤ B ∧ v ≤ B ∧ g ≤ B ∧ l ≤ B ∧ c ≤ B) :
    (coverageBodyTM b).HoareTime (EmitPred inp work ys)
      (EmitPred inp (coverageAdvance work p s v g l c b) (ys ++ coveragePattern p s v g l c))
      (100*(B+1)) := by
  have hr1 := fixedSpanRowTM_correct 1 (0 : Fin 13) 1 p s inp work ys hp hw h0 h1
  have hr2 := twoMarkRowTM_correct (2 : Fin 13) 3 4 v g l inp work
    (ys ++ spanRow p 1 s) hp hw h2 h3 h4
  let v1 := Function.update work (4 : Fin 13) (regTape (l-1))
  have hp1 : ∀ i, Parked (v1 i) := updateReg_parked work hw _ _
  have hd := decRegTM_hoareTime (4 : Fin 13) l inp work
    ((ys ++ spanRow p 1 s) ++ markedRow v g l true) hp (fun i _ => hw i) h4
  have hr3 := fixedSpanRowTM_correct 1 (5 : Fin 13) 4 c (l-1) inp v1
    ((ys ++ spanRow p 1 s) ++ markedRow v g l true) hp hp1
    (by simpa [v1] using h5) rfl
  let bits := ((ys ++ spanRow p 1 s) ++ markedRow v g l true) ++ spanRow c 1 (l-1)
  let v2 := Function.update v1 (0 : Fin 13) (regTape (p+1))
  have hp2 : ∀ i, Parked (v2 i) := updateReg_parked v1 hp1 _ _
  have hu2 := incRegTM_hoareTime (0 : Fin 13) p inp v1 bits hp
    (fun i _ => hp1 i) (by simpa [v1] using h0)
  let v3 := Function.update v2 (1 : Fin 13) (regTape (s-1))
  have hp3 : ∀ i, Parked (v3 i) := updateReg_parked v2 hp2 _ _
  have hu3 := decRegTM_hoareTime (1 : Fin 13) s inp v2 bits hp
    (fun i _ => hp2 i) (by simpa [v2,v1] using h1)
  let v4 := Function.update v3 (5 : Fin 13) (regTape (c+1))
  have hp4 : ∀ i, Parked (v4 i) := updateReg_parked v3 hp3 _ _
  have hu4 := incRegTM_hoareTime (5 : Fin 13) c inp v3 bits hp
    (fun i _ => hp3 i) (by simpa [v3,v2,v1] using h5)
  let v5 := Function.update v4 (if b then 2 else 3) (regTape ((if b then v else g)+1))
  have hu5 := incRegTM_hoareTime (if b then (2 : Fin 13) else 3) (if b then v else g)
    inp v4 bits hp (fun i _ => hp4 i) (by cases b <;> simp [v4,v3,v2,v1,h2,h3])
  have hu45 := seqTM_hoareTime _ _ hu4 (emitPred_transition hp hp4 bits) hu5
  have hu345 := seqTM_hoareTime _ _ hu3 (emitPred_transition hp hp3 bits) hu45
  have hu2345 := seqTM_hoareTime _ _ hu2 (emitPred_transition hp hp2 bits) hu345
  have hr3end := seqTM_hoareTime _ _ hr3 (emitPred_transition hp hp1 bits) hu2345
  have hdend := seqTM_hoareTime _ _ hd (emitPred_transition hp hp1 _) hr3end
  have hr2end := seqTM_hoareTime _ _ hr2 (emitPred_transition hp hw _) hdend
  have hall := seqTM_hoareTime _ _ hr1 (emitPred_transition hp hw _) hr2end
  have he : v5 = coverageAdvance work p s v g l c b := by
    funext i
    cases b <;> fin_cases i <;> simp [v5,v4,v3,v2,v1,coverageAdvance,h2,h3]
  change (coverageBodyTM b).HoareTime _ (EmitPred inp v5 bits) _ at hall
  rw [he] at hall
  have hb : bits = ys ++ coveragePattern p s v g l c := by
    simp [bits,coveragePattern,List.append_assoc]
  rw [hb] at hall
  apply hall.mono_bound
  rcases hB with ⟨hpB,hsB,hvB,hgB,hlB,hcB⟩
  cases b <;> simp only [Bool.false_eq_true,↓reduceIte] <;> nlinarith [Nat.sub_le l 1]

end IrrRAFEnumeration.SATSource
