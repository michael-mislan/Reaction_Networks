import proofs.DUnstableCores.Elementary.ReactionMultiplication
import proofs.DUnstableCores.ParameterRichCounterexample

namespace DUnstableCores

def cfMultiplier : Fin 5 → ℕ := ![5187522222797, 11, 3750, 28200219703, 1]

theorem cfMultiplier_pos (r : Fin 5) : 0 < cfMultiplier r := by
  fin_cases r <;> norm_num [cfMultiplier]

def cfSource := multiplyReactions parameterRichCounterexampleSource cfMultiplier

theorem cfSource_catalystFree (s : Fin 4) (r : Fin 5) :
    cfSource.reactant s r * cfSource.product s r = 0 := by
  apply multiplyReactions_catalystFree
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [parameterRichCounterexampleSource]

noncomputable def cfConcentration : Fin 4 → ℝ :=
  ![10375044445594, 6600, 66000, 186632000000]

noncomputable def cfFlux : Fin 5 → ℝ :=
  ![2/5187522222797, 3/11, 1/1875, 2/28200219703, 2]

theorem cfConcentration_pos (s : Fin 4) : 0 < cfConcentration s := by
  fin_cases s <;> norm_num [cfConcentration]

theorem cfFlux_pos (r : Fin 5) : 0 < cfFlux r := by
  fin_cases r <;> norm_num [cfFlux]

noncomputable def cfReactivity : Reactivity cfSource where
  value := fun r s => parameterRichCounterexampleReactivity.value r s / (cfMultiplier r : ℝ)
  nonneg := fun r s => div_nonneg (parameterRichCounterexampleReactivity.nonneg r s)
    (Nat.cast_nonneg _)
  positive_of_reactant := by
    intro r s h
    apply div_pos
    · apply parameterRichCounterexampleReactivity.positive_of_reactant
      exact (multiplyReactions_reactant_iff _ _ cfMultiplier_pos s r).mp h
    · exact Nat.cast_pos.mpr (cfMultiplier_pos r)
  zero_of_not_reactant := by
    intro r s h
    rw [parameterRichCounterexampleReactivity.zero_of_not_reactant r s
      (fun hbase => h ((multiplyReactions_reactant_iff _ _ cfMultiplier_pos s r).mpr hbase))]
    exact zero_div _

noncomputable def cfMassAction : ClassicalMassActionInstance cfSource where
  concentration := cfConcentration
  rateConstant := reconstructedRate cfSource cfConcentration cfFlux
  concentration_pos := cfConcentration_pos
  rateConstant_pos := reconstructedRate_pos _ _ _ cfConcentration_pos cfFlux_pos
  reactivity := cfReactivity
  derivative_formula := by
    intro r s
    change cfReactivity.value r s = (cfSource.reactant s r : ℝ) *
      (reconstructedRate cfSource cfConcentration cfFlux r *
      massActionMonomial cfSource cfConcentration r) / cfConcentration s
    rw [reconstructedRate_mul_monomial _ _ _ cfConcentration_pos r]
    fin_cases r <;> fin_cases s <;>
      norm_num [cfReactivity, cfSource, multiplyReactions, cfMultiplier,
        parameterRichCounterexampleSource, parameterRichCounterexampleReactivity,
        parameterRichCounterexampleE, parameterRichCounterexampleF,
        cfConcentration, cfFlux]

theorem cfMassAction_flux (r : Fin 5) :
    classicalReactionFlux cfMassAction r = cfFlux r :=
  reconstructedRate_mul_monomial _ _ _ cfConcentration_pos r

theorem cfMassAction_stationary : ClassicalStationary cfMassAction := by
  intro s
  simp_rw [cfMassAction_flux]
  fin_cases s <;>
    norm_num [cfSource, multiplyReactions, cfMultiplier, cfFlux,
      parameterRichCounterexampleSource, SourceNetwork.stoich, Fin.sum_univ_succ]

theorem cfMassAction_jacobian : cfSource.jacobian cfReactivity =
    parameterRichCounterexampleSource.jacobian parameterRichCounterexampleReactivity := by
  ext i j
  apply Finset.sum_congr rfl
  intro r _
  change ((multiplyReactions parameterRichCounterexampleSource cfMultiplier).stoich i r : ℝ) *
    (parameterRichCounterexampleReactivity.value r j / (cfMultiplier r : ℝ)) = _
  rw [multiplyReactions_stoich]
  push_cast
  have hc : (cfMultiplier r : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (cfMultiplier_pos r))
  field_simp

theorem cfMassAction_unstable : HurwitzUnstable (cfSource.jacobian cfMassAction.reactivity) := by
  change HurwitzUnstable (cfSource.jacobian cfReactivity)
  rw [cfMassAction_jacobian]
  exact parameterRichCounterexample_hurwitzUnstable

theorem cfSource_all_children (κ : ChildSelection cfSource) : DNonUnstable κ.realMatrix :=
  multiplyReactions_all_children _ _ cfMultiplier_pos
    parameterRichCounterexample_all_children_dNonUnstable κ

theorem cfSource_no_core : ¬ ∃ κ : ChildSelection cfSource, IsDUnstableCore κ := by
  rintro ⟨κ, hκ⟩
  obtain ⟨d, hd, hu⟩ := hκ.1
  exact cfSource_all_children κ d hd hu

/-- Catalyst-free ordinary mass action can be unstable without a D-unstable core.
This theorem has no molecularity-two claim. -/
theorem catalystFree_massAction_counterexample :
    (∀ s r, cfSource.reactant s r * cfSource.product s r = 0) ∧
    ClassicalStationary cfMassAction ∧
    HurwitzUnstable (cfSource.jacobian cfMassAction.reactivity) ∧
    (∀ κ : ChildSelection cfSource, DNonUnstable κ.realMatrix) ∧
    ¬ ∃ κ : ChildSelection cfSource, IsDUnstableCore κ :=
  ⟨cfSource_catalystFree, cfMassAction_stationary, cfMassAction_unstable,
    cfSource_all_children, cfSource_no_core⟩

end DUnstableCores
