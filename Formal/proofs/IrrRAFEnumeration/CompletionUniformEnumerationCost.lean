import proofs.IrrRAFEnumeration.CompletionUniformQueryCost

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

theorem roundTimeBound_mono {r K x : Nat} (a : Nat) (hr : r ≤ x) (hK : K ≤ x) :
    roundTimeBound r K a ≤ roundTimeBound x x a := by
  unfold roundTimeBound blockerCommitTime blockerSizeBound
  gcongr

noncomputable def roundTimePolynomial (a : Polynomial Nat) : Polynomial Nat :=
  let x := Polynomial.X
  let c := blockerSizePolynomial
  let commit := x*c+1+1+c+1+(x*c+c)+3+1+(4*x+20)
  6+1+(x*(x*a+12*x+33)+(x+2)+1+(2*x+6+commit+1+2*x+4))+1+(7*x*x+20*x+12)

theorem roundTimePolynomial_eval (a : Polynomial Nat) (x : Nat) :
    (roundTimePolynomial a).eval x = roundTimeBound x x (a.eval x) := by
  simp [roundTimePolynomial,blockerSizePolynomial,roundTimeBound,blockerCommitTime,blockerSizeBound]

noncomputable def enumerationTimePolynomial (k : Nat) (q p : Polynomial Nat) : Polynomial Nat :=
  let a := callTimePolynomial k q p
  (Polynomial.X+1)*(a+roundTimePolynomial a+2)+1+
    (3*(Polynomial.X*Polynomial.X)+4*Polynomial.X+14)

theorem enumerationTimePolynomial_eval (k : Nat) (q p : Polynomial Nat) (x : Nat) :
    (enumerationTimePolynomial k q p).eval x =
      (x+1)*((callTimePolynomial k q p).eval x+
        roundTimeBound x x ((callTimePolynomial k q p).eval x)+2)+1+(3*(x*x)+4*x+14) := by
  simp [enumerationTimePolynomial,roundTimePolynomial_eval]

/-- The complete prepared-state machine has one fixed polynomial in input plus
required output length. The generated-call cost premise has been discharged. -/
theorem preparedEnumeration_polynomial {d r k : Nat} (p : Polynomial Nat)
    (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (M : TM k) (hM : M.DecidesInTime SAT.language p.eval)
    (inp : Tape) (hp : Parked inp) :
    (preparedEnumerationTM (p+Polynomial.X+2) M).HoareTime
      (EmitPred inp (enumWork k (Finset.univ : Finset (Fin r))
        (SAT.CNF.encode (assembledBase Q C)) [] [] 0 0) [])
      (fun x _ out => x = inp ∧ ∃ G : List (Finset (Fin r)),
        GoodFamily (irrRAFFamily Q C) G ∧ G.toFinset = irrRAFFamily Q C ∧
        OutAcc (outputBits (Equiv.refl (Fin r)) G) out)
      ((enumerationTimePolynomial k (p+Polynomial.X+2) p).eval
        ((inputBits Q C (Equiv.refl _) (Equiv.refl _)).length+
          fixedWidthOutputLength r (irrRAFFamily Q C).card)) := by
  let N := (inputBits Q C (Equiv.refl _) (Equiv.refl _)).length
  let K := (irrRAFFamily Q C).card
  let x := N+fixedWidthOutputLength r K
  let q := p+Polynomial.X+2
  let a := (callTimePolynomial k q p).eval x
  have hN : N ≤ x := Nat.le_add_right _ _
  have hK : K ≤ x := by dsimp [x,fixedWidthOutputLength]; omega
  have hr : r ≤ x := by
    have h : r ≤ N := by
      simp only [N,inputBits,List.length_append,List.length_replicate,List.length_singleton,List.length_ofFn]
      omega
    exact h.trans hN
  have hq : ∀ L, q.eval L = p.eval L+L+2 := by intro L; simp [q]
  have hc : ∀ G, GoodFamily (irrRAFFamily Q C) G →
      ∀ U, fullQueryCost (k := k) q p.eval Q C G U ≤ a := by
    intro G hG U
    exact fullQueryCost_le_polynomial q p Q C G U x hN ((goodFamily_length_le hG).trans hK)
  have h := preparedEnumerationTM_correct q Q C M p.eval hM hq a hc inp hp
  apply h.mono_bound
  rw [enumerationTimePolynomial_eval]
  change (K+1)*(a+roundTimeBound r K a+2)+1+(3*(r*K)+4*K+14) ≤
    (x+1)*(a+roundTimeBound x x a+2)+1+(3*(x*x)+4*x+14)
  have hb := roundTimeBound_mono a hr hK
  gcongr

end IrrRAFEnumeration.CompletionQuery
