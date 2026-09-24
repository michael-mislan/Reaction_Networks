import proofs.PowerLawSmallRAF.LigationGrammarCount

namespace PowerLawSmallRAF

/-- Evaluate the first `i` instructions of a legal straight-line program.
The state is indexed by the `F+i` available values: first the food values,
then the instruction outputs in chronological order. -/
def legalLigationState {A : Type*} {foodCount instructionCount : Nat}
    (food : Fin foodCount → A) (ligate : A → A → A)
    (program : LegalLigationProgramCode foodCount instructionCount) :
    (i : Nat) → i ≤ instructionCount → Fin (foodCount + i) → A
  | 0, _ => fun index => food (Fin.cast (by omega) index)
  | i + 1, hi =>
      let previous := legalLigationState food ligate program i (by omega)
      let step := program ⟨i, by omega⟩
      let product := ligate (previous step.1) (previous step.2)
      fun index =>
        if hindex : index.val < foodCount + i then
          previous ⟨index.val, hindex⟩
        else
          product

/-- The output of a nonempty legal program is its last instruction value. -/
def legalLigationProgramOutput {A : Type*} {foodCount instructionCount : Nat}
    (food : Fin foodCount → A) (ligate : A → A → A)
    (hpositive : 0 < instructionCount)
    (program : LegalLigationProgramCode foodCount instructionCount) : A :=
  legalLigationState food ligate program instructionCount le_rfl
    ⟨foodCount + instructionCount - 1, by omega⟩

/-- The newly appended state coordinate is exactly the current instruction
output. -/
theorem legalLigationState_succ_last {A : Type*}
    {foodCount instructionCount i : Nat}
    (food : Fin foodCount → A) (ligate : A → A → A)
    (program : LegalLigationProgramCode foodCount instructionCount)
    (hi : i + 1 ≤ instructionCount) :
    legalLigationState food ligate program (i + 1) hi
        ⟨foodCount + i, by omega⟩ =
      ligate
        (legalLigationState food ligate program i (by omega)
          (program ⟨i, by omega⟩).1)
        (legalLigationState food ligate program i (by omega)
          (program ⟨i, by omega⟩).2) := by
  simp only [legalLigationState]
  split
  · omega
  · rfl

/-- A nonempty program output is the value of its final instruction. -/
theorem legalLigationProgramOutput_eq_last {A : Type*}
    {foodCount instructionCount : Nat}
    (food : Fin foodCount → A) (ligate : A → A → A)
    (hpositive : 0 < instructionCount)
    (program : LegalLigationProgramCode foodCount instructionCount) :
    legalLigationProgramOutput food ligate hpositive program =
      ligate
        (legalLigationState food ligate program (instructionCount - 1)
          (by omega) (program ⟨instructionCount - 1, by omega⟩).1)
        (legalLigationState food ligate program (instructionCount - 1)
          (by omega) (program ⟨instructionCount - 1, by omega⟩).2) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpositive)
  exact legalLigationState_succ_last food ligate program (i := i) le_rfl

/-- Exact finite constructibility predicate induced by legal programs of a
fixed instruction count. -/
def LegalLigationConstructible {A : Type*} {foodCount instructionCount : Nat}
    (food : Fin foodCount → A) (ligate : A → A → A)
    (hpositive : 0 < instructionCount) (target : A) : Prop :=
  ∃ program : LegalLigationProgramCode foodCount instructionCount,
    legalLigationProgramOutput food ligate hpositive program = target

instance legalLigationConstructibleDecidable
    {A : Type*} [Fintype A] [DecidableEq A]
    {foodCount instructionCount : Nat}
    (food : Fin foodCount → A) (ligate : A → A → A)
    (hpositive : 0 < instructionCount) :
    DecidablePred (LegalLigationConstructible food ligate hpositive) := by
  intro target
  unfold LegalLigationConstructible
  infer_instance

/-- The number of targets constructible by exactly `s` legal ligations is at
most `(F+s)^(2s)`. -/
theorem card_legalLigationConstructible_le
    {A : Type*} [Fintype A] [DecidableEq A]
    {foodCount instructionCount : Nat}
    (food : Fin foodCount → A) (ligate : A → A → A)
    (hpositive : 0 < instructionCount) :
    (Finset.univ.filter
      (LegalLigationConstructible food ligate hpositive)).card ≤
      (foodCount + instructionCount) ^ (2 * instructionCount) := by
  let output : LegalLigationProgramCode foodCount instructionCount → A :=
    legalLigationProgramOutput food ligate hpositive
  calc
    (Finset.univ.filter
      (LegalLigationConstructible food ligate hpositive)).card ≤
        (Finset.univ.image output).card := by
      apply Finset.card_le_card
      intro target htarget
      rw [Finset.mem_filter] at htarget
      obtain ⟨program, hprogram⟩ := htarget.2
      exact Finset.mem_image.mpr ⟨program, Finset.mem_univ program,
        hprogram⟩
    _ ≤ Fintype.card
        (LegalLigationProgramCode foodCount instructionCount) :=
      Finset.card_image_le
    _ ≤ (foodCount + instructionCount) ^ (2 * instructionCount) :=
      card_legalLigationProgramCode_le foodCount instructionCount

end PowerLawSmallRAF
