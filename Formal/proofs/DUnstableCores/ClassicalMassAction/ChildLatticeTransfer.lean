import proofs.DUnstableCores.ClassicalMassAction.Source
import proofs.DUnstableCores.ParameterRichCounterexample

namespace DUnstableCores

theorem classicalPadded_stoich_eq_parameterRich :
    classicalPaddedCounterexampleSource.stoich =
      parameterRichCounterexampleSource.stoich := by
  rw [classicalPadded_stoich_eq_base]
  rfl

theorem classicalPadded_reactant_iff_parameterRich (s : Fin 4) (r : Fin 5) :
    classicalPaddedCounterexampleSource.Reactant s r ↔
      parameterRichCounterexampleSource.Reactant s r := by
  rw [classicalPadded_reactant_iff_base]
  rfl

def classicalPaddedChildToParameterRich
    (κ : ChildSelection classicalPaddedCounterexampleSource) :
    ChildSelection parameterRichCounterexampleSource where
  species := κ.species
  reactions := κ.reactions
  assign := κ.assign
  reactant_match := by
    intro x
    exact (classicalPadded_reactant_iff_parameterRich
      x.1 (κ.assign x).1).mp (κ.reactant_match x)

theorem classicalPadded_child_realMatrix_eq
    (κ : ChildSelection classicalPaddedCounterexampleSource) :
    κ.realMatrix = (classicalPaddedChildToParameterRich κ).realMatrix := by
  ext i j
  change ((classicalPaddedCounterexampleSource.stoich i.1
    (κ.assign j).1 : ℤ) : ℝ) =
    ((parameterRichCounterexampleSource.stoich i.1
      (κ.assign j).1 : ℤ) : ℝ)
  rw [classicalPadded_stoich_eq_parameterRich]

theorem classicalPadded_all_children_dNonUnstable
    (κ : ChildSelection classicalPaddedCounterexampleSource) :
    DNonUnstable κ.realMatrix := by
  rw [classicalPadded_child_realMatrix_eq κ]
  exact parameterRichCounterexample_all_children_dNonUnstable
    (classicalPaddedChildToParameterRich κ)

theorem classicalPadded_no_dUnstableCore :
    ¬ ∃ core : ChildSelection classicalPaddedCounterexampleSource,
      IsDUnstableCore core := by
  rintro ⟨core, hcore⟩
  obtain ⟨d, hd, hunstable⟩ := hcore.1
  exact classicalPadded_all_children_dNonUnstable core d hd hunstable

end DUnstableCores
