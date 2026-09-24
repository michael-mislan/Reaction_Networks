import proofs.IrrRAFEnumeration.SATCoverageBody

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

def coveragePairPattern (p s v g l c : Nat) : List Bool :=
  coveragePattern p s v g l c ++ coveragePattern (p+1) (s-1) v (g+1) (l-1) (c+1)

def coveragePairAdvance (work : Fin 13 → Tape) (p s v g l c : Nat) : Fin 13 → Tape :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update work 0 (regTape (p+2))) 1 (regTape (s-2)))
      2 (regTape (v+1))) 3 (regTape (g+1))) 4 (regTape (l-2))) 5 (regTape (c+2))

def coveragePairTM : TM 13 := seqTM (coverageBodyTM false) (coverageBodyTM true)

theorem coveragePairTM_correct (p s v g l c B : Nat)
    (inp : Tape) (work : Fin 13 → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (h0 : work 0 = regTape p) (h1 : work 1 = regTape s)
    (h2 : work 2 = regTape v) (h3 : work 3 = regTape g)
    (h4 : work 4 = regTape l) (h5 : work 5 = regTape c)
    (hB : p ≤ B ∧ s ≤ B ∧ v ≤ B ∧ g ≤ B ∧ l ≤ B ∧ c ≤ B) :
    coveragePairTM.HoareTime (EmitPred inp work ys)
      (EmitPred inp (coveragePairAdvance work p s v g l c)
        (ys ++ coveragePairPattern p s v g l c)) (400*(B+1)) := by
  have hfalse := coverageBodyTM_correct false p s v g l c B inp work ys hp hw h0 h1 h2 h3 h4 h5 hB
  let V := coverageAdvance work p s v g l c false
  have hv : ∀ i, Parked (V i) := by
    intro i
    fin_cases i <;> first | exact parked_regTape _ | exact hw _
  have htrue := coverageBodyTM_correct true (p+1) (s-1) v (g+1) (l-1) (c+1) (B+1)
    inp V (ys ++ coveragePattern p s v g l c) hp hv rfl rfl rfl rfl rfl rfl (by omega)
  have hall := seqTM_hoareTime _ _ hfalse (emitPred_transition hp hv _) htrue
  have he : coverageAdvance V (p+1) (s-1) v (g+1) (l-1) (c+1) true =
      coveragePairAdvance work p s v g l c := by
    funext i
    fin_cases i <;> simp [V,coverageAdvance,coveragePairAdvance,Nat.sub_sub,Nat.add_assoc]
  rw [he] at hall
  have ho : (ys ++ coveragePattern p s v g l c) ++
      coveragePattern (p+1) (s-1) v (g+1) (l-1) (c+1) = ys ++ coveragePairPattern p s v g l c := by
    simp [coveragePairPattern,List.append_assoc]
  rw [ho] at hall
  apply hall.mono_bound
  omega

end IrrRAFEnumeration.SATSource
