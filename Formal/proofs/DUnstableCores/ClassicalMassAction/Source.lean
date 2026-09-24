import proofs.DUnstableCores.Minimality

/-!
# The explicit classical catalytic-padding source

The padding changes literal reactant multiplicities but preserves both net
stoichiometry and reactant incidence.  Hence its child matrices are exactly
those of the compiled parameter-rich counterexample source.
-/

namespace DUnstableCores

abbrev classicalPaddingN : ℕ := 5187522222797
abbrev classicalPaddingM : ℕ := 28200219703

/-- The original no-padding literal complexes. -/
def classicalBaseCounterexampleSource : SourceNetwork (Fin 4) (Fin 5) where
  reactant := !![1, 0, 0, 0, 0;
                 0, 4, 0, 0, 0;
                 0, 2, 4, 0, 0;
                 2, 0, 0, 2, 0]
  product := !![0, 0, 0, 1, 0;
                0, 0, 0, 6, 0;
                4, 0, 0, 1, 2;
                0, 0, 2, 0, 2]
  catalyst := 0
  catalyst_le_reactant := by intros; simp
  catalyst_le_product := by intros; simp

/-- Stoichiometrically silent copies added on both sides. -/
def classicalPadding : Matrix (Fin 4) (Fin 5) ℕ :=
  !![0, 0, 0, 0, 0;
     0, 0, 0, 0, 0;
     0, 9, 7496, 0, 0;
     classicalPaddingN - 2, 0, 0, classicalPaddingM - 2, 0]

/-- The exact large-exponent lift from the campaign preflight. -/
def classicalPaddedCounterexampleSource : SourceNetwork (Fin 4) (Fin 5) where
  reactant := fun s r =>
    classicalBaseCounterexampleSource.reactant s r + classicalPadding s r
  product := fun s r =>
    classicalBaseCounterexampleSource.product s r + classicalPadding s r
  catalyst := classicalPadding
  catalyst_le_reactant := by intros; simp
  catalyst_le_product := by intros; simp

theorem classicalPadded_stoich_eq_base :
    classicalPaddedCounterexampleSource.stoich =
      classicalBaseCounterexampleSource.stoich := by
  ext s r
  simp [SourceNetwork.stoich, classicalPaddedCounterexampleSource]

theorem classicalPadded_reactant_iff_base (s : Fin 4) (r : Fin 5) :
    classicalPaddedCounterexampleSource.Reactant s r ↔
      classicalBaseCounterexampleSource.Reactant s r := by
  fin_cases s <;> fin_cases r <;>
    norm_num [SourceNetwork.Reactant, classicalPaddedCounterexampleSource,
      classicalBaseCounterexampleSource, classicalPadding,
      classicalPaddingN, classicalPaddingM]

end DUnstableCores
