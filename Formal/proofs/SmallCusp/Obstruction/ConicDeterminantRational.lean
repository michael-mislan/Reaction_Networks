import proofs.SmallCusp.Obstruction.ConicDeterminantChecker
import proofs.SmallCusp.Source.Enumeration

/-!
# Rational finite checker for conic determinant obstructions

The large certificate table is evaluated over `ℚ`.  This file proves once that
the computed rational coefficients cast to the real coefficients used by the
analytic obstruction theorem.
-/

namespace SmallCusp

theorem BimolComplexCode.decode_injective :
    Function.Injective BimolComplexCode.decode := by
  intro a b h
  cases a <;> cases b <;>
    simp [BimolComplexCode.decode] at h ⊢

structure CodedBimolNetwork where
  reaction : Fin 5 → BimolReactionCode
  noSelf : ∀ r, (reaction r).1 ≠ (reaction r).2
  injective : Function.Injective reaction

def CodedBimolNetwork.toNetwork (C : CodedBimolNetwork) : SmallPlanarNetwork 5 where
  reactant r := (C.reaction r).1.decode
  product r := (C.reaction r).2.decode
  noSelfReaction := by
    intro r h
    exact C.noSelf r (BimolComplexCode.decode_injective h)
  reactionInjective := by
    intro r s h
    apply C.injective
    apply Prod.ext
    · apply BimolComplexCode.decode_injective
      exact congrArg Prod.fst h
    · apply BimolComplexCode.decode_injective
      exact congrArg Prod.snd h

def codedStoich (C : CodedBimolNetwork) (i : Species) (r : Fin 5) : ℤ :=
  ((C.reaction r).2.decode i : ℤ) - ((C.reaction r).1.decode i : ℤ)

def ratUnitJacobianEntryCoeff (C : CodedBimolNetwork)
    (i j : Species) (r : Fin 5) : ℚ :=
  (codedStoich C i r : ℚ) * ((C.reaction r).1.decode j : ℚ)

def ratOrderedUnitDetCoeff (C : CodedBimolNetwork) (r s : Fin 5) : ℚ :=
  ratUnitJacobianEntryCoeff C 0 0 r * ratUnitJacobianEntryCoeff C 1 1 s -
    ratUnitJacobianEntryCoeff C 0 1 r * ratUnitJacobianEntryCoeff C 1 0 s

def ratRawConicCoeff (C : CodedBimolNetwork) (sign : ℚ)
    (multiplier : Species → Fin 5 → ℚ) (r s : Fin 5) : ℚ :=
  sign * ratOrderedUnitDetCoeff C r s -
    ∑ i : Species, multiplier i r * (codedStoich C i s : ℚ)

def ratUpperConicCoeff (C : CodedBimolNetwork) (sign : ℚ)
    (multiplier : Species → Fin 5 → ℚ) (r s : Fin 5) : ℚ :=
  if r < s then ratRawConicCoeff C sign multiplier r s +
      ratRawConicCoeff C sign multiplier s r
  else if r = s then ratRawConicCoeff C sign multiplier r r
  else 0

theorem ratUpperConicCoeff_cast (C : CodedBimolNetwork) (sign : ℚ)
    (multiplier : Species → Fin 5 → ℚ) (r s : Fin 5) :
    ((ratUpperConicCoeff C sign multiplier r s : ℚ) : ℝ) =
      upperConicCoeff C.toNetwork (sign : ℝ)
        (fun i t ↦ (multiplier i t : ℝ)) r s := by
  by_cases hlt : r < s
  · simp [ratUpperConicCoeff, upperConicCoeff, hlt, ratRawConicCoeff,
      rawConicCoeff, ratOrderedUnitDetCoeff, orderedUnitDetCoeff,
      ratUnitJacobianEntryCoeff, unitJacobianEntryCoeff, codedStoich,
      CodedBimolNetwork.toNetwork, SmallPlanarNetwork.stoich]
  · by_cases heq : r = s
    · simp [ratUpperConicCoeff, upperConicCoeff, heq,
        ratRawConicCoeff, rawConicCoeff, ratOrderedUnitDetCoeff,
        orderedUnitDetCoeff, ratUnitJacobianEntryCoeff,
        unitJacobianEntryCoeff, codedStoich, CodedBimolNetwork.toNetwork,
        SmallPlanarNetwork.stoich]
    · simp [ratUpperConicCoeff, upperConicCoeff, hlt, heq]

theorem rationalUpperConicCertificate_excludes_cusp
    (C : CodedBimolNetwork) (sign : ℚ)
    (multiplier : Species → Fin 5 → ℚ)
    (hc : ∀ r s, 0 ≤ ratUpperConicCoeff C sign multiplier r s)
    (hw : ∃ r s, 0 < ratUpperConicCoeff C sign multiplier r s) :
    ¬ AdmitsTransverseCusp C.toNetwork := by
  apply upperConicCertificate_excludes_cusp C.toNetwork (sign : ℝ)
    (fun i r ↦ (multiplier i r : ℝ))
  · intro r s
    rw [← ratUpperConicCoeff_cast]
    exact_mod_cast hc r s
  · rcases hw with ⟨r, s, hrs⟩
    refine ⟨r, s, ?_⟩
    rw [← ratUpperConicCoeff_cast]
    exact_mod_cast hrs

structure RationalConicRecord where
  network : CodedBimolNetwork
  sign : ℚ
  multiplier : Species → Fin 5 → ℚ

def RationalConicRecord.Valid (R : RationalConicRecord) : Prop :=
  (∀ r s, 0 ≤ ratUpperConicCoeff R.network R.sign R.multiplier r s) ∧
  ∃ r s, 0 < ratUpperConicCoeff R.network R.sign R.multiplier r s

def RationalConicRecord.check (R : RationalConicRecord) : Bool :=
  (List.ofFn fun r : Fin 5 ↦
    (List.ofFn fun s : Fin 5 ↦
      decide (0 ≤ ratUpperConicCoeff R.network R.sign R.multiplier r s)).all id).all id &&
  (List.ofFn fun r : Fin 5 ↦
    (List.ofFn fun s : Fin 5 ↦
      decide (0 < ratUpperConicCoeff R.network R.sign R.multiplier r s)).any id).any id

theorem RationalConicRecord.check_eq_true_iff (R : RationalConicRecord) :
    R.check = true ↔ R.Valid := by
  simp [RationalConicRecord.check, RationalConicRecord.Valid,
    Fin.forall_fin_succ, Fin.exists_fin_succ]

theorem RationalConicRecord.excludes_cusp (R : RationalConicRecord)
    (hR : R.Valid) : ¬ AdmitsTransverseCusp R.network.toNetwork :=
  rationalUpperConicCertificate_excludes_cusp R.network R.sign R.multiplier
    hR.1 hR.2

theorem RationalConicRecord.valid_of_mem_of_all_checked
    (L : List RationalConicRecord) (hL : L.all RationalConicRecord.check = true)
    {R : RationalConicRecord} (hR : R ∈ L) : R.Valid := by
  have hall : ∀ S ∈ L, S.check = true := by
    simpa using hL
  exact R.check_eq_true_iff.mp (hall R hR)

end SmallCusp
