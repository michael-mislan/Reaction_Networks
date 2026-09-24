import proofs.DUnstableCores.ClassicalMassAction.Rate
import proofs.DUnstableCores.ClassicalMassAction.ChildLatticeTransfer

/-!
# Exact classical mass-action counterexample by catalytic padding

The rate constants are represented by the reconstruction formula `v / x^Y`.
The generic lemma in `Rate.lean` cancels the monomial symbolically, so the huge
exponents are never expanded.
-/

namespace DUnstableCores

noncomputable def classicalPaddedConcentration : Fin 4 → ℝ :=
  ![2, 600, 33000, 93316000000]

def classicalPaddedFlux : Fin 5 → ℝ := ![2, 3, 2, 2, 2]

theorem classicalPaddedConcentration_pos (s : Fin 4) :
    0 < classicalPaddedConcentration s := by
  fin_cases s <;> norm_num [classicalPaddedConcentration]

theorem classicalPaddedFlux_pos (r : Fin 5) : 0 < classicalPaddedFlux r := by
  fin_cases r <;> norm_num [classicalPaddedFlux]

/-- The old exact reactivity, now authenticated against the padded literal
reactant complexes. -/
noncomputable def classicalPaddedReactivity :
    Reactivity classicalPaddedCounterexampleSource where
  value := parameterRichCounterexampleReactivity.value
  nonneg := parameterRichCounterexampleReactivity.nonneg
  positive_of_reactant := by
    intro r s h
    exact parameterRichCounterexampleReactivity.positive_of_reactant r s
      ((classicalPadded_reactant_iff_parameterRich s r).mp h)
  zero_of_not_reactant := by
    intro r s h
    apply parameterRichCounterexampleReactivity.zero_of_not_reactant
    exact fun hold => h ((classicalPadded_reactant_iff_parameterRich s r).mpr hold)

noncomputable def classicalPaddedMassActionInstance :
    ClassicalMassActionInstance classicalPaddedCounterexampleSource where
  concentration := classicalPaddedConcentration
  rateConstant := reconstructedRate classicalPaddedCounterexampleSource
    classicalPaddedConcentration classicalPaddedFlux
  concentration_pos := classicalPaddedConcentration_pos
  rateConstant_pos := reconstructedRate_pos _ _ _
    classicalPaddedConcentration_pos classicalPaddedFlux_pos
  reactivity := classicalPaddedReactivity
  derivative_formula := by
    intro r s
    change classicalPaddedReactivity.value r s =
      (classicalPaddedCounterexampleSource.reactant s r : ℝ) *
        (reconstructedRate classicalPaddedCounterexampleSource
          classicalPaddedConcentration classicalPaddedFlux r *
          massActionMonomial classicalPaddedCounterexampleSource
            classicalPaddedConcentration r) /
        classicalPaddedConcentration s
    rw [reconstructedRate_mul_monomial _ _ _
      classicalPaddedConcentration_pos r]
    fin_cases r <;> fin_cases s <;>
      simp [classicalPaddedReactivity,
        parameterRichCounterexampleReactivity,
        classicalPaddedCounterexampleSource, classicalPaddedConcentration,
        classicalPaddedFlux, classicalPaddingN, classicalPaddingM,
        classicalBaseCounterexampleSource, classicalPadding,
        parameterRichCounterexampleE, parameterRichCounterexampleF] <;>
      norm_num [classicalPaddingN, classicalPaddingM,
        parameterRichCounterexampleE, parameterRichCounterexampleF]

theorem classicalPadded_reactionFlux_eq (r : Fin 5) :
    classicalReactionFlux classicalPaddedMassActionInstance r =
      classicalPaddedFlux r := by
  exact reconstructedRate_mul_monomial _ _ _
    classicalPaddedConcentration_pos r

theorem classicalPadded_stationary :
    ClassicalStationary classicalPaddedMassActionInstance := by
  intro s
  simp_rw [classicalPadded_reactionFlux_eq]
  fin_cases s <;>
    simp [classicalPaddedCounterexampleSource, classicalPaddedFlux,
      classicalBaseCounterexampleSource, classicalPadding,
      SourceNetwork.stoich, Fin.sum_univ_succ] <;>
    norm_num

theorem classicalPadded_jacobian_eq_parameterRich :
    classicalPaddedCounterexampleSource.jacobian classicalPaddedReactivity =
      parameterRichCounterexampleSource.jacobian
        parameterRichCounterexampleReactivity := by
  ext i j
  change (∑ r : Fin 5,
      (classicalPaddedCounterexampleSource.stoich i r : ℝ) *
        parameterRichCounterexampleReactivity.value r j) =
    ∑ r : Fin 5, (parameterRichCounterexampleSource.stoich i r : ℝ) *
      parameterRichCounterexampleReactivity.value r j
  rw [classicalPadded_stoich_eq_parameterRich]

theorem classicalPadded_hurwitzUnstable :
    HurwitzUnstable
      (classicalPaddedCounterexampleSource.jacobian
        classicalPaddedMassActionInstance.reactivity) := by
  change HurwitzUnstable
    (classicalPaddedCounterexampleSource.jacobian classicalPaddedReactivity)
  rw [classicalPadded_jacobian_eq_parameterRich]
  exact parameterRichCounterexample_hurwitzUnstable

/-- Source-faithful exact classical counterexample: positive concentrations
and rate constants, exact stationarity, strict RHP instability, and no literal
supported D-unstable core. -/
theorem classicalPadded_counterexample :
    ClassicalStationary classicalPaddedMassActionInstance ∧
      HurwitzUnstable
        (classicalPaddedCounterexampleSource.jacobian
          classicalPaddedMassActionInstance.reactivity) ∧
      ¬ ∃ core : ChildSelection classicalPaddedCounterexampleSource,
        IsDUnstableCore core :=
  ⟨classicalPadded_stationary, classicalPadded_hurwitzUnstable,
    classicalPadded_no_dUnstableCore⟩

def ClassicalMassActionCoreNecessityFin4Fin5 : Prop :=
  ∀ (Q : SourceNetwork (Fin 4) (Fin 5)),
    ∀ M : ClassicalMassActionInstance Q,
      ClassicalStationary M →
      HurwitzUnstable (Q.jacobian M.reactivity) →
      ∃ core : ChildSelection Q, IsDUnstableCore core

/-- Terminal truth-value result: universal classical mass-action localization
already fails for four species and five reactions. -/
theorem classicalMassAction_core_necessity_fin4_fin5_false :
    ¬ ClassicalMassActionCoreNecessityFin4Fin5 := by
  intro h
  exact classicalPadded_no_dUnstableCore
    (h classicalPaddedCounterexampleSource classicalPaddedMassActionInstance
      classicalPadded_stationary classicalPadded_hurwitzUnstable)

end DUnstableCores
