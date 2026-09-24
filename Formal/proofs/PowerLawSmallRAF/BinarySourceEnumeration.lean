import proofs.PowerLawSmallRAF.BinaryLigationPrograms
import proofs.PowerLawSmallRAF.SourceLowDegreeCertificateEvent
import proofs.RAF.Polymer.Food

namespace PowerLawSmallRAF

open RAF.Polymer RAF.Concrete

/-- The concrete sigma-type of nonempty binary words has exactly the source
molecule count used in the asymptotic model. -/
theorem card_binaryMolecule_eq_sourceMoleculeCount (n : Nat) :
    Fintype.card (Molecule n) = sourceMoleculeCount n := by
  rw [card_molecule_sigma,
    Fin.sum_univ_eq_sum_range (fun k : Nat => 2 ^ (k + 1))]
  dsimp [sourceMoleculeCount]
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have hpow : 2 ≤ 2 ^ (n + 1) := by
        rw [pow_succ]
        have hp : 0 < 2 ^ n := by positivity
        omega
      omega

/-- Canonical exact enumeration of all source molecules by `Fin X_n`. -/
noncomputable def binaryMoleculeEquivFin (n : Nat) :
    Molecule n ≃ Fin (sourceMoleculeCount n) :=
  (Fintype.equivFin (Molecule n)).trans
    (finCongr (card_binaryMolecule_eq_sourceMoleculeCount n))

/-- Length-preserving inclusion of a molecule universe into a larger cutoff. -/
def liftBinaryMolecule {m n : Nat} (hmn : m ≤ n) : Molecule m → Molecule n
  | ⟨length, word⟩ =>
      ⟨⟨length.val, length.isLt.trans_le hmn⟩, word⟩

/-- The six binary words of lengths one and two, included into the cutoff-`n`
universe when `n ≥ 2`.  At the two irrelevant small cutoffs this total
definition uses the supplied fallback molecule. -/
noncomputable def sourceBinaryFood (n : Nat) (fallback : Molecule n) :
    Fin 6 → Molecule n :=
  if hn : 2 ≤ n then
    fun index =>
      liftBinaryMolecule hn
        ((Fintype.equivFin (FoodMolecule 2)).symm
          ((finCongr card_food_binary_t2).symm index))
  else
    fun _ => fallback

/-- Concrete source output code for every syntactic legal program.  Positive
length programs are evaluated using actual binary concatenation with the
source food set; the zero-length case is assigned the harmless fallback. -/
noncomputable def sourceBinaryProgramOutput (n : Nat)
    (fallback : Molecule n) (instructionCount : Nat) :
    LegalLigationProgramCode 6 instructionCount →
      Fin (sourceMoleculeCount n) :=
  if hpositive : 0 < instructionCount then
    fun program => binaryMoleculeEquivFin n
      (legalLigationProgramOutput (sourceBinaryFood n fallback)
        (boundedBinaryConcat fallback) hpositive program)
  else
    fun _ => binaryMoleculeEquivFin n fallback

theorem sourceBinaryProgramOutput_eq_evaluation {n instructionCount : Nat}
    (fallback : Molecule n) (hpositive : 0 < instructionCount)
    (program : LegalLigationProgramCode 6 instructionCount) :
    sourceBinaryProgramOutput n fallback instructionCount program =
      binaryMoleculeEquivFin n
        (legalLigationProgramOutput (sourceBinaryFood n fallback)
          (boundedBinaryConcat fallback) hpositive program) := by
  simp only [sourceBinaryProgramOutput, dif_pos hpositive]

end PowerLawSmallRAF
