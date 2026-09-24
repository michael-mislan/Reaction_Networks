import proofs.IrrRAFEnumeration.CompletionPreparedEnumeration

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM PolynomialClockSetup

def baseSizeBound (x : Nat) := 10000000*(x+1)^6
def querySizeBound (x : Nat) := dynamicQueryTime (baseSizeBound x) (x*blockerSizeBound x) x

noncomputable def blockerSizePolynomial : Polynomial Nat :=
  Polynomial.X*(10*Polynomial.X+58)+Polynomial.X+6

noncomputable def querySizePolynomial : Polynomial Nat :=
  2*(10000000*(Polynomial.X+1)^6)+2*Polynomial.X*blockerSizePolynomial+
    Polynomial.X*(10*Polynomial.X+58)+Polynomial.X+14

theorem querySizePolynomial_eval (x : Nat) : querySizePolynomial.eval x = querySizeBound x := by
  simp [querySizePolynomial,blockerSizePolynomial,querySizeBound,baseSizeBound,
    dynamicQueryTime,blockerSizeBound]
  ring

theorem dynamicQueryTime_mono {r s b c u v : Nat}
    (hr : r ≤ s) (hb : b ≤ c) (hu : u ≤ v) :
    dynamicQueryTime b u r ≤ dynamicQueryTime c v s := by
  unfold dynamicQueryTime
  gcongr

/-- Both persistent buffers and every generated query fit one input/output-size
envelope, without constructing the unknown family of all outputs. -/
theorem generatedQuery_size_bounds {d r : Nat}
    (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) (x : Nat)
    (hN : (inputBits Q C (Equiv.refl _) (Equiv.refl _)).length ≤ x)
    (hG : G.length ≤ x) :
    r ≤ x ∧ (SAT.CNF.encode (assembledBase Q C)).length ≤ baseSizeBound x ∧
    (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)).length ≤ x*blockerSizeBound x ∧
    (SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
      PositiveCompletionCNF.containerExclusions U)).length ≤ querySizeBound x := by
  have hrN : r ≤ (inputBits Q C (Equiv.refl _) (Equiv.refl _)).length := by
    simp only [inputBits,List.length_append,List.length_replicate,List.length_singleton,List.length_ofFn]
    omega
  have hr := hrN.trans hN
  have hb : (SAT.CNF.encode (assembledBase Q C)).length ≤ baseSizeBound x := by
    apply (assembledBase_encode_length_le Q C).trans
    unfold baseSizeBound
    gcongr
  have hbl : (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)).length ≤ x*blockerSizeBound x := by
    apply (outputBlockers_encode_length_le G).trans
    unfold blockerSizeBound
    gcongr
  exact ⟨hr,hb,hbl,(dynamicQuery_encode_length_le Q C G U).trans
    (dynamicQueryTime_mono hr hb hbl)⟩

theorem completionCallTime_mono (k : Nat) (q p : Polynomial Nat)
    {r s b c u v L H : Nat} (hr : r ≤ s) (hb : b ≤ c) (hu : u ≤ v) (hL : L ≤ H) :
    completionCallTime k q p.eval r b u L ≤ completionCallTime k q p.eval s c v H := by
  have hd := dynamicQueryTime_mono hr hb hu
  have ht := polynomial_eval_mono_nat p hL
  have hs := polynomial_eval_mono_nat (setupPolynomial q) hL
  dsimp only at ht hs
  rw [← setupTime_eq_polynomial,← setupTime_eq_polynomial] at hs
  have hf : p.eval L+L+2 ≤ p.eval H+H+2 := by omega
  have hk := Nat.mul_le_mul_left (k+2) (show 6*(p.eval L+L+2)+10 ≤ 6*(p.eval H+H+2)+10 by omega)
  dsimp only [completionCallTime]
  omega

noncomputable def callTimePolynomial (k : Nat) (q p : Polynomial Nat) : Polynomial Nat :=
  let s := querySizePolynomial
  let t := p.comp s
  let b := t+s+2
  s+s+6+(setupPolynomial q).comp s+t+1+6*b+11+1+
    Polynomial.C (k+2)*(6*b+10)+1+1+4*Polynomial.X+2*s+4*b+35

theorem callTimePolynomial_eval (k : Nat) (q p : Polynomial Nat) (x : Nat) :
    (callTimePolynomial k q p).eval x =
      completionCallTime k q p.eval x (baseSizeBound x) (x*blockerSizeBound x) (querySizeBound x) := by
  simp only [callTimePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,
    Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_C,Polynomial.eval_X,
    querySizePolynomial_eval]
  rw [← setupTime_eq_polynomial]
  rfl

/-- This discharges the generated-call cost premise using a fixed polynomial.
No per-instance solver, nonuniform advice, or output-family computation occurs. -/
theorem fullQueryCost_le_polynomial {d r k : Nat} (q p : Polynomial Nat)
    (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) (x : Nat)
    (hN : (inputBits Q C (Equiv.refl _) (Equiv.refl _)).length ≤ x)
    (hG : G.length ≤ x) :
    fullQueryCost (k := k) q p.eval Q C G U ≤ (callTimePolynomial k q p).eval x := by
  obtain ⟨hr,hb,hbl,hL⟩ := generatedQuery_size_bounds Q C G U x hN hG
  rw [callTimePolynomial_eval]
  exact completionCallTime_mono k q p hr hb hbl hL

end IrrRAFEnumeration.CompletionQuery
