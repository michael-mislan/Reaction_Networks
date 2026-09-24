import proofs.DUnstableCores.ClassicalMassAction.Source

/-!
# Finite classical mass-action rate reconstruction

The generic lemmas in this file keep the very large exponents symbolic.  No
power in the explicit witness is ever numerically expanded.
-/

namespace DUnstableCores

open scoped BigOperators

variable {Species Reaction : Type*}

def massActionMonomial [Fintype Species]
    (Q : SourceNetwork Species Reaction) (x : Species → ℝ) (r : Reaction) : ℝ :=
  ∏ s : Species, x s ^ Q.reactant s r

theorem massActionMonomial_pos [Fintype Species]
    (Q : SourceNetwork Species Reaction) (x : Species → ℝ)
    (hx : ∀ s, 0 < x s) (r : Reaction) :
    0 < massActionMonomial Q x r := by
  apply Finset.prod_pos
  intro s hs
  exact pow_pos (hx s) _

noncomputable def reconstructedRate [Fintype Species]
    (Q : SourceNetwork Species Reaction) (x : Species → ℝ)
    (v : Reaction → ℝ) (r : Reaction) : ℝ :=
  v r / massActionMonomial Q x r

theorem reconstructedRate_pos [Fintype Species]
    (Q : SourceNetwork Species Reaction) (x : Species → ℝ)
    (v : Reaction → ℝ) (hx : ∀ s, 0 < x s) (hv : ∀ r, 0 < v r)
    (r : Reaction) :
    0 < reconstructedRate Q x v r := by
  exact div_pos (hv r) (massActionMonomial_pos Q x hx r)

theorem reconstructedRate_mul_monomial [Fintype Species]
    (Q : SourceNetwork Species Reaction) (x : Species → ℝ)
    (v : Reaction → ℝ) (hx : ∀ s, 0 < x s) (r : Reaction) :
    reconstructedRate Q x v r * massActionMonomial Q x r = v r := by
  apply div_mul_cancel₀
  exact ne_of_gt (massActionMonomial_pos Q x hx r)

def classicalReactionFlux [Fintype Species]
    {Q : SourceNetwork Species Reaction} (M : ClassicalMassActionInstance Q)
    (r : Reaction) : ℝ :=
  M.rateConstant r * massActionMonomial Q M.concentration r

def ClassicalStationary [Fintype Species] [Fintype Reaction]
    {Q : SourceNetwork Species Reaction} (M : ClassicalMassActionInstance Q) : Prop :=
  ∀ s, ∑ r : Reaction, (Q.stoich s r : ℝ) * classicalReactionFlux M r = 0

theorem classical_reactivity_eq_reactant_mul_flux_div [Fintype Species]
    {Q : SourceNetwork Species Reaction} (M : ClassicalMassActionInstance Q)
    (r : Reaction) (s : Species) :
    M.reactivity.value r s =
      (Q.reactant s r : ℝ) * classicalReactionFlux M r / M.concentration s := by
  simpa [classicalReactionFlux, massActionMonomial] using M.derivative_formula r s

end DUnstableCores
