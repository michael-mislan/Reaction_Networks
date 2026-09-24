import proofs.DUnstableCores.ClassicalMassAction.Rate

namespace DUnstableCores

/-- A+D -> 2C; B+C -> 0; 2C -> D; 2D -> A+4B+4C; inflows A,D. -/
def elementarySource : SourceNetwork (Fin 4) (Fin 6) where
  reactant := !![1,0,0,0,0,0; 0,1,0,0,0,0; 0,1,2,0,0,0; 1,0,0,2,0,0]
  product := !![0,0,0,1,1,0; 0,0,0,4,0,0; 2,0,0,4,0,0; 0,0,1,0,0,1]
  catalyst := 0
  catalyst_le_reactant := by intros; simp
  catalyst_le_product := by intros; simp

theorem elementarySource_R2 (r : Fin 6) :
    ∑ s : Fin 4, elementarySource.reactant s r ≤ 2 := by
  fin_cases r <;> norm_num [elementarySource, Fin.sum_univ_succ]

theorem elementarySource_CF (s : Fin 4) (r : Fin 6) :
    elementarySource.reactant s r * elementarySource.product s r = 0 := by
  fin_cases s <;> fin_cases r <;> norm_num [elementarySource]

noncomputable def elementaryConcentration : Fin 4 → ℝ := ![1,1,1,1/100]
def elementaryFlux : Fin 6 → ℝ := ![100,4,100,1,99,2]
def elementaryRates : Fin 6 → ℝ := ![10000,4,100,10000,99,2]

theorem elementaryConcentration_pos (s : Fin 4) : 0 < elementaryConcentration s := by
  fin_cases s <;> norm_num [elementaryConcentration]
theorem elementaryFlux_pos (r : Fin 6) : 0 < elementaryFlux r := by
  fin_cases r <;> norm_num [elementaryFlux]

noncomputable def elementaryReactivity : Reactivity elementarySource where
  value := fun r s => (elementarySource.reactant s r : ℝ)*elementaryFlux r/elementaryConcentration s
  nonneg := fun r s => div_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (elementaryFlux_pos r).le)
    (elementaryConcentration_pos s).le
  positive_of_reactant := by
    intro r s h
    exact div_pos (mul_pos (Nat.cast_pos.mpr h) (elementaryFlux_pos r))
      (elementaryConcentration_pos s)
  zero_of_not_reactant := by
    intro r s h
    have hz : elementarySource.reactant s r = 0 := by
      unfold SourceNetwork.Reactant at h
      omega
    simp [hz]

noncomputable def elementaryMassAction : ClassicalMassActionInstance elementarySource where
  concentration := elementaryConcentration
  rateConstant := reconstructedRate elementarySource elementaryConcentration elementaryFlux
  concentration_pos := elementaryConcentration_pos
  rateConstant_pos := reconstructedRate_pos _ _ _ elementaryConcentration_pos elementaryFlux_pos
  reactivity := elementaryReactivity
  derivative_formula := by
    intro r s
    change (elementarySource.reactant s r : ℝ)*elementaryFlux r/elementaryConcentration s =
      (elementarySource.reactant s r : ℝ) *
        (reconstructedRate elementarySource elementaryConcentration elementaryFlux r *
          massActionMonomial elementarySource elementaryConcentration r) / elementaryConcentration s
    rw [reconstructedRate_mul_monomial _ _ _ elementaryConcentration_pos r]

theorem elementaryMassAction_flux (r : Fin 6) :
    classicalReactionFlux elementaryMassAction r = elementaryFlux r :=
  reconstructedRate_mul_monomial _ _ _ elementaryConcentration_pos r

theorem elementaryMassAction_stationary : ClassicalStationary elementaryMassAction := by
  intro s
  simp_rw [elementaryMassAction_flux]
  fin_cases s <;> norm_num [elementarySource, elementaryFlux,
    SourceNetwork.stoich, Fin.sum_univ_succ]

def elementaryJacobian : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-100,0,0,-9800; 0,-4,-4,800; 200,-4,-404,20800; -100,0,200,-10400]

theorem elementaryMassAction_jacobian :
    elementarySource.jacobian elementaryMassAction.reactivity = elementaryJacobian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [elementaryMassAction, elementaryReactivity, elementarySource,
      elementaryFlux, elementaryConcentration, elementaryJacobian,
      SourceNetwork.jacobian, SourceNetwork.stoich, Fin.sum_univ_succ]

end DUnstableCores
