import proofs.RandomViability.BindingStoichiometry

namespace RandomViability.Binding
noncomputable section

/-- A nonzero literal propensity always has enough reactant molecules. -/
theorem rate_support (N : Counts) (V eps k r : ℝ) (j : Fin 18)
    (hr : countRate N V eps k r j ≠ 0) : ∀ i, reactants j i ≤ N i := by
  intro i
  by_contra hi
  obtain ⟨a,b,c,d,e,f,hN⟩ : ∃ a b c d e f, N = ![a,b,c,d,e,f] := by
    refine ⟨N 0,N 1,N 2,N 3,N 4,N 5,?_⟩
    funext k
    fin_cases k <;> rfl
  subst N
  fin_cases j <;> fin_cases i <;> norm_num [reactants] at hi
  all_goals norm_num [countRate] at hr
  all_goals simp_all

theorem rated_weighted_jump (N : Counts) (V eps k r : ℝ) (j : Fin 18) :
    countRate N V eps k r j * (weightedCount (countNext N j)-weightedCount N) =
      countRate N V eps k r j * weightedJump j := by
  by_cases h : countRate N V eps k r j = 0
  · simp [h]
  · rw [weighted_actual_jump N j (rate_support N V eps k r j h)]

theorem rated_linear_jump (N : Counts) (V eps k r : ℝ) (j : Fin 18)
    (a : Fin 6 → ℝ) :
    countRate N V eps k r j *
        ((∑ i,a i*(countNext N j i:ℝ))-(∑ i,a i*(N i:ℝ))) =
    countRate N V eps k r j * (∑ i,a i*((products j i:ℝ)-(reactants j i:ℝ))) := by
  by_cases h : countRate N V eps k r j = 0
  · simp [h]
  · rw [next_linear_difference N j a (rate_support N V eps k r j h)]

end
end RandomViability.Binding
