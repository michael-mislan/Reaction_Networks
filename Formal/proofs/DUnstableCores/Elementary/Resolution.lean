import proofs.DUnstableCores.Elementary.ElementaryEmbedding

namespace DUnstableCores

theorem elementaryJacobian_charpoly :
    IsElementaryQuartic elementaryJacobian 10908 185600 1280000 64000000 := by
  have hc1 : elementaryCoeff1 elementaryJacobian = 10908 := by
    change -((-100 : ℝ) + (-4 : ℝ) + (-404 : ℝ) + (-10400 : ℝ)) = 10908
    norm_num
  have hc2 : elementaryCoeff2 elementaryJacobian = 185600 := by
    change ((-100 : ℝ)*(-4 : ℝ) - (0 : ℝ)*(0 : ℝ)) + ((-100 : ℝ)*(-404 : ℝ) - (0 : ℝ)*(200 : ℝ)) + ((-100 : ℝ)*(-10400 : ℝ) - (-9800 : ℝ)*(-100 : ℝ)) + ((-4 : ℝ)*(-404 : ℝ) - (-4 : ℝ)*(-4 : ℝ)) + ((-4 : ℝ)*(-10400 : ℝ) - (800 : ℝ)*(0 : ℝ)) + ((-404 : ℝ)*(-10400 : ℝ) - (20800 : ℝ)*(200 : ℝ)) = 185600
    norm_num
  have hc3 : elementaryCoeff3 elementaryJacobian = 1280000 := by
    change -(((-100 : ℝ)*(-4 : ℝ)*(-404 : ℝ) - (-100 : ℝ)*(-4 : ℝ)*(-4 : ℝ) - (0 : ℝ)*(0 : ℝ)*(-404 : ℝ) + (0 : ℝ)*(-4 : ℝ)*(200 : ℝ) + (0 : ℝ)*(0 : ℝ)*(-4 : ℝ) - (0 : ℝ)*(-4 : ℝ)*(200 : ℝ)) + ((-100 : ℝ)*(-4 : ℝ)*(-10400 : ℝ) - (-100 : ℝ)*(800 : ℝ)*(0 : ℝ) - (0 : ℝ)*(0 : ℝ)*(-10400 : ℝ) + (0 : ℝ)*(800 : ℝ)*(-100 : ℝ) + (-9800 : ℝ)*(0 : ℝ)*(0 : ℝ) - (-9800 : ℝ)*(-4 : ℝ)*(-100 : ℝ)) + ((-100 : ℝ)*(-404 : ℝ)*(-10400 : ℝ) - (-100 : ℝ)*(20800 : ℝ)*(200 : ℝ) - (0 : ℝ)*(200 : ℝ)*(-10400 : ℝ) + (0 : ℝ)*(20800 : ℝ)*(-100 : ℝ) + (-9800 : ℝ)*(200 : ℝ)*(200 : ℝ) - (-9800 : ℝ)*(-404 : ℝ)*(-100 : ℝ)) + ((-4 : ℝ)*(-404 : ℝ)*(-10400 : ℝ) - (-4 : ℝ)*(20800 : ℝ)*(200 : ℝ) - (-4 : ℝ)*(-4 : ℝ)*(-10400 : ℝ) + (-4 : ℝ)*(20800 : ℝ)*(0 : ℝ) + (800 : ℝ)*(-4 : ℝ)*(200 : ℝ) - (800 : ℝ)*(-404 : ℝ)*(0 : ℝ))) = 1280000
    norm_num
  have hc4 : elementaryCoeff4 elementaryJacobian = 64000000 := by
    change (-100 : ℝ)*((-4 : ℝ)*(-404 : ℝ)*(-10400 : ℝ) - (-4 : ℝ)*(20800 : ℝ)*(200 : ℝ) - (-4 : ℝ)*(-4 : ℝ)*(-10400 : ℝ) + (-4 : ℝ)*(20800 : ℝ)*(0 : ℝ) + (800 : ℝ)*(-4 : ℝ)*(200 : ℝ) - (800 : ℝ)*(-404 : ℝ)*(0 : ℝ)) - (0 : ℝ)*((0 : ℝ)*(-404 : ℝ)*(-10400 : ℝ) - (0 : ℝ)*(20800 : ℝ)*(200 : ℝ) - (-4 : ℝ)*(200 : ℝ)*(-10400 : ℝ) + (-4 : ℝ)*(20800 : ℝ)*(-100 : ℝ) + (800 : ℝ)*(200 : ℝ)*(200 : ℝ) - (800 : ℝ)*(-404 : ℝ)*(-100 : ℝ)) + (0 : ℝ)*((0 : ℝ)*(-4 : ℝ)*(-10400 : ℝ) - (0 : ℝ)*(20800 : ℝ)*(0 : ℝ) - (-4 : ℝ)*(200 : ℝ)*(-10400 : ℝ) + (-4 : ℝ)*(20800 : ℝ)*(-100 : ℝ) + (800 : ℝ)*(200 : ℝ)*(0 : ℝ) - (800 : ℝ)*(-4 : ℝ)*(-100 : ℝ)) - (-9800 : ℝ)*((0 : ℝ)*(-4 : ℝ)*(200 : ℝ) - (0 : ℝ)*(-404 : ℝ)*(0 : ℝ) - (-4 : ℝ)*(200 : ℝ)*(200 : ℝ) + (-4 : ℝ)*(-404 : ℝ)*(-100 : ℝ) + (-4 : ℝ)*(200 : ℝ)*(0 : ℝ) - (-4 : ℝ)*(-4 : ℝ)*(-100 : ℝ)) = 64000000
    norm_num
  unfold IsElementaryQuartic
  rw [elementary_charpoly_fin4,hc1,hc2,hc3,hc4]

theorem elementaryMassAction_unstable :
    HurwitzUnstable (elementarySource.jacobian elementaryMassAction.reactivity) := by
  rw [elementaryMassAction_jacobian]
  exact elementary_matrix_unstable elementaryJacobian elementaryJacobian_charpoly

theorem elementarySource_no_core :
    ¬ ∃ κ : ChildSelection elementarySource, IsDUnstableCore κ := by
  rintro ⟨κ,hκ⟩
  obtain ⟨d,hd,hu⟩ := hκ.1
  exact elementarySource_all_children κ d hd hu

/-- Reactant-bimolecular, catalyst-free, source-faithful ordinary mass-action
counterexample. Product molecularity is deliberately unrestricted. -/
theorem elementary_resolution :
    ∃ Q : SourceNetwork (Fin 4) (Fin 6),
      (∀ r, ∑ s : Fin 4, Q.reactant s r ≤ 2) ∧
      (∀ s r, Q.reactant s r * Q.product s r = 0) ∧
      ∃ M : ClassicalMassActionInstance Q,
        ClassicalStationary M ∧
        HurwitzUnstable (Q.jacobian M.reactivity) ∧
        (∀ κ : ChildSelection Q, DNonUnstable κ.realMatrix) ∧
        ¬ ∃ κ : ChildSelection Q, IsDUnstableCore κ :=
  ⟨elementarySource,elementarySource_R2,elementarySource_CF,
    elementaryMassAction,elementaryMassAction_stationary,elementaryMassAction_unstable,
    elementarySource_all_children,elementarySource_no_core⟩

theorem reactantBimolecular_core_necessity_false :
    ¬ (∀ Q : SourceNetwork (Fin 4) (Fin 6),
      (∀ r, ∑ s : Fin 4, Q.reactant s r ≤ 2) →
      ∀ M : ClassicalMassActionInstance Q, ClassicalStationary M →
        HurwitzUnstable (Q.jacobian M.reactivity) →
        ∃ κ : ChildSelection Q, IsDUnstableCore κ) := by
  intro h
  exact elementarySource_no_core
    (h elementarySource elementarySource_R2 elementaryMassAction
      elementaryMassAction_stationary elementaryMassAction_unstable)

#print axioms elementary_resolution
#print axioms reactantBimolecular_core_necessity_false

end DUnstableCores
