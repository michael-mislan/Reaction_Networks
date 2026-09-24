import proofs.IrrRAFEnumeration.SATCoverageBody
import proofs.IrrRAFEnumeration.SATStreamRows

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

def clausePattern (p s v g l c : Nat) (bit : Bool) : List Bool :=
  spanRow p 1 s ++ markedRow v g l bit ++ spanRow c 1 (l-1)

def clauseAdvance (work : Fin 13 → Tape) (p s g l c : Nat) : Fin 13 → Tape :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update work 12 ((work 12).move .right))
      0 (regTape (p+1))) 1 (regTape (s-1))) 3 (regTape (g+1)))
        4 (regTape (l-1))) 5 (regTape (c+1))

def clauseBodyTM : TM 13 :=
  seqTM (fixedSpanRowTM 1 0 1) (seqTM (streamMarkedRowTM 2 12 3 4)
    (seqTM (decRegTM 4) (seqTM (fixedSpanRowTM 1 5 4)
      (seqTM (incRegTM 0) (seqTM (decRegTM 1)
        (seqTM (incRegTM 5) (incRegTM 3)))))))

/-- One clause reaction consumes precisely one incidence bit. All saved
registers and the clause's signal position remain framed. -/
theorem clauseBodyTM_correct (p s v g l c B : Nat) (bit : Bool)
    (inp : Tape) (work : Fin 13 → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (h0 : work 0 = regTape p) (h1 : work 1 = regTape s)
    (h2 : work 2 = regTape v) (h3 : work 3 = regTape g)
    (h4 : work 4 = regTape l) (h5 : work 5 = regTape c)
    (hbit : (work 12).read = Γ.ofBool bit)
    (hB : p ≤ B ∧ s ≤ B ∧ v ≤ B ∧ g ≤ B ∧ l ≤ B ∧ c ≤ B) :
    clauseBodyTM.HoareTime (EmitPred inp work ys)
      (EmitPred inp (clauseAdvance work p s g l c) (ys ++ clausePattern p s v g l c bit))
      (100*(B+1)) := by
  have hr1 := fixedSpanRowTM_correct 1 (0 : Fin 13) 1 p s inp work ys hp hw h0 h1
  have hr2 := streamMarkedRowTM_correct (2 : Fin 13) 12 3 4 (by decide) (by decide)
    v g l bit inp work (ys ++ spanRow p 1 s) hp hw h2 h3 h4 hbit
  let w0 := Function.update work (12 : Fin 13) ((work 12).move .right)
  have hpw0 : ∀ i, Parked (w0 i) := by
    intro i
    by_cases hi : i = 12
    · subst i
      simpa [w0] using parked_move_right (work 12) (hw 12)
    · simpa [w0,hi] using hw i
  let v1 := Function.update w0 (4 : Fin 13) (regTape (l-1))
  have hp1 : ∀ i, Parked (v1 i) := updateReg_parked w0 hpw0 _ _
  have hd := decRegTM_hoareTime (4 : Fin 13) l inp w0
    ((ys ++ spanRow p 1 s) ++ markedRow v g l bit) hp (fun i _ => hpw0 i)
    (by simpa [w0] using h4)
  have hr3 := fixedSpanRowTM_correct 1 (5 : Fin 13) 4 c (l-1) inp v1
    ((ys ++ spanRow p 1 s) ++ markedRow v g l bit) hp hp1
    (by simpa [v1,w0] using h5) rfl
  let bits := ((ys ++ spanRow p 1 s) ++ markedRow v g l bit) ++ spanRow c 1 (l-1)
  let v2 := Function.update v1 (0 : Fin 13) (regTape (p+1))
  have hp2 : ∀ i, Parked (v2 i) := updateReg_parked v1 hp1 _ _
  have hu2 := incRegTM_hoareTime (0 : Fin 13) p inp v1 bits hp
    (fun i _ => hp1 i) (by simpa [v1,w0] using h0)
  let v3 := Function.update v2 (1 : Fin 13) (regTape (s-1))
  have hp3 : ∀ i, Parked (v3 i) := updateReg_parked v2 hp2 _ _
  have hu3 := decRegTM_hoareTime (1 : Fin 13) s inp v2 bits hp
    (fun i _ => hp2 i) (by simpa [v2,v1,w0] using h1)
  let v4 := Function.update v3 (5 : Fin 13) (regTape (c+1))
  have hp4 : ∀ i, Parked (v4 i) := updateReg_parked v3 hp3 _ _
  have hu4 := incRegTM_hoareTime (5 : Fin 13) c inp v3 bits hp
    (fun i _ => hp3 i) (by simpa [v3,v2,v1,w0] using h5)
  let v5 := Function.update v4 (3 : Fin 13) (regTape (g+1))
  have hu5 := incRegTM_hoareTime (3 : Fin 13) g inp v4 bits hp
    (fun i _ => hp4 i) (by simpa [v4,v3,v2,v1,w0] using h3)
  have hu45 := seqTM_hoareTime _ _ hu4 (emitPred_transition hp hp4 bits) hu5
  have hu345 := seqTM_hoareTime _ _ hu3 (emitPred_transition hp hp3 bits) hu45
  have hu2345 := seqTM_hoareTime _ _ hu2 (emitPred_transition hp hp2 bits) hu345
  have hr3end := seqTM_hoareTime _ _ hr3 (emitPred_transition hp hp1 bits) hu2345
  have hdend := seqTM_hoareTime _ _ hd (emitPred_transition hp hp1 _) hr3end
  have hr2end := seqTM_hoareTime _ _ hr2 (emitPred_transition hp hpw0 _) hdend
  have hall := seqTM_hoareTime _ _ hr1 (emitPred_transition hp hw _) hr2end
  have he : v5 = clauseAdvance work p s g l c := by
    funext i
    fin_cases i <;> simp [v5,v4,v3,v2,v1,w0,clauseAdvance]
  change clauseBodyTM.HoareTime _ (EmitPred inp v5 bits) _ at hall
  rw [he] at hall
  have hb : bits = ys ++ clausePattern p s v g l c bit := by
    simp [bits,clausePattern,List.append_assoc]
  rw [hb] at hall
  apply hall.mono_bound
  rcases hB with ⟨hpB,hsB,hvB,hgB,hlB,hcB⟩
  nlinarith [Nat.sub_le l 1]

end IrrRAFEnumeration.SATSource
