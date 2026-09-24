import proofs.RAFReactionCriticality.ModularSurvival

namespace RAFReactionCriticality.CatalyticModules
open RAF RAFQueryCompilation FunctionalSource FiniteThinning
open scoped BigOperators
variable {J : Type*} [Fintype J] [DecidableEq J] (length : J → ℕ)

omit [DecidableEq J] in
theorem total_reactions : Fintype.card (Reaction length) = ∑ j, (length j+1) := by
  simp [Fintype.card_sigma, ZMod.card]

/-- The susceptibility is the second module-size moment before normalization. -/
theorem mean_derivative_one :
    HasDerivAt (expectedSize (parent length) (parent length))
      (∑ j, (((length j+1 : ℕ) : ℝ))^2) 1 := by
  rw [show expectedSize (parent length) (parent length) =
    (fun p : ℝ => ∑ j, ((length j+1 : ℕ) : ℝ) * p^(length j+1)) from
      funext (mean_size length)]
  apply HasDerivAt.fun_sum
  intro j _
  simpa [pow_two] using
    ((hasDerivAt_id (1 : ℝ)).fun_pow (length j+1)).const_mul
      (((length j+1 : ℕ) : ℝ))

/-- Uniform reaction deletion weights each module by its number of reactions. -/
theorem size_bias_probability (k : ℕ) :
    ((Finset.univ.filter (fun r : Reaction length =>
      (loss source (catalysts (parent length)) Finset.univ {r}).card = k)).card : ℝ) /
      Fintype.card (Reaction length) =
    (k : ℝ) * (Finset.univ.filter (fun j : J => length j+1=k)).card /
      (∑ j, ((length j+1 : ℕ) : ℝ)) := by
  classical
  rw [size_bias_count, total_reactions]
  simp

end RAFReactionCriticality.CatalyticModules
