import proofs.PowerLawSmallRAF.LigationProgramEvaluation
import proofs.RAF.Concrete.PolymerCRS
import Mathlib.Data.Fintype.EquivFin

namespace PowerLawSmallRAF

open RAF.Polymer RAF.Concrete

/-- A fixed enumeration of the actual binary-polymer food set. -/
noncomputable def binaryFoodEnumeration (n t : Nat) :
    Fin (binaryFood n t).card → Molecule n :=
  fun index => ((binaryFood n t).equivFin.symm index).1

theorem binaryFoodEnumeration_mem (n t : Nat)
    (index : Fin (binaryFood n t).card) :
    binaryFoodEnumeration n t index ∈ binaryFood n t :=
  ((binaryFood n t).equivFin.symm index).2

theorem exists_binaryFoodEnumeration_eq (n t : Nat)
    {x : Molecule n} (hx : x ∈ binaryFood n t) :
    ∃ index, binaryFoodEnumeration n t index = x := by
  let member : ↥(binaryFood n t) := ⟨x, hx⟩
  refine ⟨(binaryFood n t).equivFin member, ?_⟩
  exact congrArg Subtype.val
    ((binaryFood n t).equivFin.symm_apply_apply member)

/-- Total semantics for a proposed ligation step.  Legal source shellings only
use the first branch; the fallback merely makes program evaluation total on
all syntactic codes. -/
def boundedBinaryConcat {n : Nat} (fallback : Molecule n)
    (left right : Molecule n) : Molecule n :=
  if h : molLength left + molLength right ≤ n then
    concatMolecule left right h
  else
    fallback

theorem boundedBinaryConcat_eq_concatMolecule {n : Nat}
    (fallback left right : Molecule n)
    (hvalid : molLength left + molLength right ≤ n) :
    boundedBinaryConcat fallback left right =
      concatMolecule left right hvalid := by
  simp only [boundedBinaryConcat, dif_pos hvalid]

/-- Source-specific exact-`s` constructibility under valid-or-fallback binary
concatenation. -/
def BinaryLigationConstructible {n : Nat} (t : Nat)
    (fallback : Molecule n) (instructionCount : Nat)
    (hpositive : 0 < instructionCount) (target : Molecule n) : Prop :=
  LegalLigationConstructible (binaryFoodEnumeration n t)
    (boundedBinaryConcat fallback) hpositive target

noncomputable instance binaryLigationConstructibleDecidable {n : Nat} (t : Nat)
    (fallback : Molecule n) (instructionCount : Nat)
    (hpositive : 0 < instructionCount) :
    DecidablePred
      (BinaryLigationConstructible t fallback instructionCount hpositive) := by
  intro target
  unfold BinaryLigationConstructible
  infer_instance

/-- Exact finite grammar bound in the split-position binary-polymer universe. -/
theorem card_binaryLigationConstructible_le {n : Nat} (t : Nat)
    (fallback : Molecule n) (instructionCount : Nat)
    (hpositive : 0 < instructionCount) :
    (Finset.univ.filter
      (BinaryLigationConstructible t fallback instructionCount hpositive)).card ≤
      ((binaryFood n t).card + instructionCount) ^
        (2 * instructionCount) := by
  exact card_legalLigationConstructible_le
    (binaryFoodEnumeration n t) (boundedBinaryConcat fallback) hpositive

/-- A legal program together with the chronological split-position reactions
that it realizes.  The realization equation is deliberately stated against
the exact sequential evaluator, so it cannot hide a forward reference. -/
structure BinaryLigationRealization {n : Nat} (t : Nat)
    (fallback : Molecule n) (instructionCount : Nat) where
  program : LegalLigationProgramCode (binaryFood n t).card instructionCount
  reaction : Fin instructionCount → Reaction n
  realizes : ∀ i : Fin instructionCount,
    boundedBinaryConcat fallback
        (legalLigationState (binaryFoodEnumeration n t)
          (boundedBinaryConcat fallback) program i.val
          (Nat.le_of_lt i.isLt) (program i).1)
        (legalLigationState (binaryFoodEnumeration n t)
          (boundedBinaryConcat fallback) program i.val
          (Nat.le_of_lt i.isLt) (program i).2) =
      reactionProduct (reaction i)

/-- The final reaction product of every nonempty realized shelling is in the
exact source constructible family. -/
theorem binaryLigationConstructible_lastProduct_of_realization
    {n : Nat} (t : Nat) (fallback : Molecule n)
    (instructionCount : Nat) (hpositive : 0 < instructionCount)
    (realization : BinaryLigationRealization t fallback instructionCount) :
    BinaryLigationConstructible t fallback instructionCount hpositive
      (reactionProduct
        (realization.reaction ⟨instructionCount - 1, by omega⟩)) := by
  refine ⟨realization.program, ?_⟩
  rw [legalLigationProgramOutput_eq_last]
  exact realization.realizes ⟨instructionCount - 1, by omega⟩

end PowerLawSmallRAF
