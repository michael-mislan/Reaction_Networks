import proofs.DUnstableCores.ClassicalMassAction.PaddedCounterexample
import proofs.DUnstableCores.ClassicalMassAction.RationalLift
import proofs.DUnstableCores.ClassicalMassAction.UnpaddedStability

/-!
# Classical mass-action D-instability localization: final result
-/

namespace DUnstableCores

/-- The literature-facing universal classical localization claim is false:
already at four species and five reactions there is a positive stationary
classical mass-action instance with a strict RHP eigenvalue and no literal
supported D-unstable core. -/
theorem classicalMassAction_localization_false :
    ¬ ClassicalMassActionCoreNecessityFin4Fin5 :=
  classicalMassAction_core_necessity_fin4_fin5_false

/-- The publication-level comparison theorem.  The unpadded source is stable
at every positive stationary classical mass-action instance, while catalytic
padding preserves every stoichiometric column and every reactant-support
incidence and produces an unstable stationary instance with no supported
D-unstable core. -/
theorem classical_sameSkeleton_stableBefore_unstableAfter :
    (∀ M : ClassicalMassActionInstance classicalBaseCounterexampleSource,
      ClassicalStationary M →
        HurwitzStable
          (classicalBaseCounterexampleSource.jacobian M.reactivity)) ∧
    classicalPaddedCounterexampleSource.stoich =
      classicalBaseCounterexampleSource.stoich ∧
    (∀ s r,
      classicalPaddedCounterexampleSource.Reactant s r ↔
        classicalBaseCounterexampleSource.Reactant s r) ∧
    ClassicalStationary classicalPaddedMassActionInstance ∧
    HurwitzUnstable
      (classicalPaddedCounterexampleSource.jacobian
        classicalPaddedMassActionInstance.reactivity) ∧
    ¬ ∃ core : ChildSelection classicalPaddedCounterexampleSource,
      IsDUnstableCore core := by
  refine ⟨?_, classicalPadded_stoich_eq_base, ?_,
    classicalPadded_stationary, classicalPadded_hurwitzUnstable,
    classicalPadded_no_dUnstableCore⟩
  · intro M hM
    exact classicalBase_every_positive_equilibrium_hurwitzStable M hM
  · intro s r
    exact classicalPadded_reactant_iff_base s r

end DUnstableCores
