import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Image
import Mathlib.Tactic

namespace PowerLawSmallRAF

/-- A deliberately permissive code for a straight-line ligation program.
At each of `s` instructions both inputs may be any food item or any of the
`s` instruction outputs.  Legal acyclic programs form a subtype, so counting
these permissive codes is a valid upper bound. -/
abbrev LigationProgramCode (foodCount instructionCount : Nat) :=
  Fin instructionCount →
    Fin (foodCount + instructionCount) × Fin (foodCount + instructionCount)

/-- A legal straight-line code only points to food or to outputs of earlier
instructions. -/
abbrev LegalLigationProgramCode (foodCount instructionCount : Nat) :=
  (i : Fin instructionCount) →
    Fin (foodCount + i.val) × Fin (foodCount + i.val)

/-- Forget the backwards-reference restriction. -/
def relaxLegalLigationProgramCode (foodCount instructionCount : Nat) :
    LegalLigationProgramCode foodCount instructionCount →
      LigationProgramCode foodCount instructionCount :=
  fun program i =>
    let hi : foodCount + i.val ≤ foodCount + instructionCount :=
      Nat.add_le_add_left (Nat.le_of_lt i.isLt) foodCount
    (Fin.castLE hi (program i).1, Fin.castLE hi (program i).2)

theorem relaxLegalLigationProgramCode_injective
    (foodCount instructionCount : Nat) :
    Function.Injective
      (relaxLegalLigationProgramCode foodCount instructionCount) := by
  intro left right heq
  funext i
  have hi := congrFun heq i
  apply Prod.ext
  · apply Fin.ext
    exact congrArg (fun pair => pair.1.val) hi
  · apply Fin.ext
    exact congrArg (fun pair => pair.2.val) hi

/-- Exact entropy of the permissive straight-line grammar. -/
theorem card_ligationProgramCode (foodCount instructionCount : Nat) :
    Fintype.card (LigationProgramCode foodCount instructionCount) =
      (foodCount + instructionCount) ^ (2 * instructionCount) := by
  simp only [LigationProgramCode, Fintype.card_fun, Fintype.card_prod,
    Fintype.card_fin]
  rw [mul_pow, ← pow_add]
  congr 1
  omega

/-- Legal acyclic programs obey the same simple entropy upper bound. -/
theorem card_legalLigationProgramCode_le
    (foodCount instructionCount : Nat) :
    Fintype.card (LegalLigationProgramCode foodCount instructionCount) ≤
      (foodCount + instructionCount) ^ (2 * instructionCount) := by
  calc
    Fintype.card (LegalLigationProgramCode foodCount instructionCount) ≤
      Fintype.card (LigationProgramCode foodCount instructionCount) :=
      Fintype.card_le_of_injective
        (relaxLegalLigationProgramCode foodCount instructionCount)
        (relaxLegalLigationProgramCode_injective foodCount instructionCount)
    _ = (foodCount + instructionCount) ^ (2 * instructionCount) :=
      card_ligationProgramCode foodCount instructionCount

/-- Critical-path finite encoder interface.  If each target satisfying `P`
has a distinct legal construction code, the number of such targets has the
straight-line grammar bound. -/
theorem card_constructible_le_of_injective_legalCode
    {A : Type*} [Fintype A] [DecidableEq A]
    (P : A → Prop) [DecidablePred P]
    (foodCount instructionCount : Nat)
    (encode : {x : A // P x} →
      LegalLigationProgramCode foodCount instructionCount)
    (hinjective : Function.Injective encode) :
    (Finset.univ.filter P).card ≤
      (foodCount + instructionCount) ^ (2 * instructionCount) := by
  calc
    (Finset.univ.filter P).card = Fintype.card {x : A // P x} :=
      (Fintype.card_subtype P).symm
    _ ≤ Fintype.card
        (LegalLigationProgramCode foodCount instructionCount) :=
      Fintype.card_le_of_injective encode hinjective
    _ ≤ (foodCount + instructionCount) ^ (2 * instructionCount) :=
      card_legalLigationProgramCode_le foodCount instructionCount

/-- Whatever semantics is assigned to a program, the number of distinct
outputs cannot exceed the number of program codes.  This is the finite
counting interface needed for the incompressibility half of PL43. -/
theorem card_ligationProgramOutputs_le
    {A : Type*} [Fintype A] [DecidableEq A]
    (foodCount instructionCount : Nat)
    (output : LigationProgramCode foodCount instructionCount → A) :
    (Finset.univ.image output).card ≤
      (foodCount + instructionCount) ^ (2 * instructionCount) := by
  calc
    (Finset.univ.image output).card ≤
        (Finset.univ : Finset
          (LigationProgramCode foodCount instructionCount)).card :=
      Finset.card_image_le
    _ = Fintype.card (LigationProgramCode foodCount instructionCount) :=
      Finset.card_univ
    _ = (foodCount + instructionCount) ^ (2 * instructionCount) :=
      card_ligationProgramCode foodCount instructionCount

/-- A normalized finite incompressibility bound: under the uniform law on
targets, the mass of every program-image family is at most code count divided
by the ambient target count. -/
theorem uniform_ligationProgramOutput_mass_le
    {A : Type*} [Fintype A] [DecidableEq A]
    (foodCount instructionCount : Nat)
    (output : LigationProgramCode foodCount instructionCount → A) :
    ((Finset.univ.image output).card : ℝ) / Fintype.card A ≤
      (((foodCount + instructionCount) ^ (2 * instructionCount) : Nat) : ℝ) /
        (Fintype.card A : ℝ) := by
  exact div_le_div_of_nonneg_right
    (by
      exact_mod_cast
        (card_ligationProgramOutputs_le foodCount instructionCount output))
    (by positivity)

end PowerLawSmallRAF
