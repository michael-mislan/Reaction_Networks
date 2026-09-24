import proofs.IrrRAFEnumeration.CompletionUniformEnumerationCost
import proofs.Complexitylib.Classes.P.NormalForm
import proofs.Complexitylib.SAT.Headline

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

/-- Exact prepared-machine interface, named to keep existential export metadata
separate from the nested implication in its specification. -/
def PreparedEnumerationSpec (k : Nat)
    (E : TM ((((bufferedCount k+1)+1)+1)+1)) (p : Polynomial Nat) : Prop :=
      ∀ (d r : Nat) (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r))
        [DecidableRel C] (inp : Tape), Parked inp →
        E.HoareTime
          (EmitPred inp (enumWork k (Finset.univ : Finset (Fin r))
            (SAT.CNF.encode (assembledBase Q C)) [] [] 0 0) [])
          (fun x _ out => x = inp ∧ ∃ G : List (Finset (Fin r)),
            GoodFamily (irrRAFFamily Q C) G ∧ G.toFinset = irrRAFFamily Q C ∧
            OutAcc (outputBits (Equiv.refl (Fin r)) G) out)
          (p.eval ((inputBits Q C (Equiv.refl _) (Equiv.refl _)).length+
            fixedWidthOutputLength r (irrRAFFamily Q C).card))

/-- P = NP supplies one fixed machine and polynomial for the entire prepared
enumeration problem. No SAT oracle or per-instance runtime bound remains.
The original-input persistent-state initialization is still to be composed. -/
theorem preparedEnumeration_of_P_eq_NP (hPNP : Complexity.P = Complexity.NP) :
    ∃ (k : Nat) (E : TM ((((bufferedCount k+1)+1)+1)+1)) (p : Polynomial Nat),
      PreparedEnumerationSpec k E p := by
  have hs : SAT.language ∈ Complexity.P := by
    rw [hPNP]
    exact SAT.language_mem_NP
  obtain ⟨k,M,p,hM⟩ := mem_P_iff_decidesInTime_polynomial.mp hs
  refine ⟨k,preparedEnumerationTM (p+Polynomial.X+2) M,
    enumerationTimePolynomial k (p+Polynomial.X+2) p,?_⟩
  intro d r Q C _ inp hp
  exact preparedEnumeration_polynomial p Q C M hM inp hp

end IrrRAFEnumeration.CompletionQuery
