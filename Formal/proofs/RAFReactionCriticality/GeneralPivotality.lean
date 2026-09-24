import proofs.RAFReactionCriticality.FiniteProductDerivative
import proofs.RAFReactionCriticality.LossClosure

namespace RAFReactionCriticality.GeneralPivotality
open RAF RAFQueryCompilation FiniteProductDerivative
open scoped BigOperators
variable {M R : Type*} [DecidableEq M] [Fintype M] [DecidableEq R] [Fintype R]

def retained (S : Finset R) (m : R → Bool) : Finset R := S.filter (fun r => m r)

variable (Q : CRS M R) (C : Catalysis M R) [∀ x r, Decidable (C x r)]

noncomputable def sizeObservable (S : Finset R) (m : R → Bool) : ℝ :=
  (evaluate Q C (retained S m)).card

noncomputable def survivalObservable (S : Finset R) (m : R → Bool) : ℝ :=
  if (evaluate Q C (retained S m)).Nonempty then 1 else 0

theorem size_derivative (S : Finset R) (p : ℝ) :
    HasDerivAt (expectation (sizeObservable Q C S))
      (∑ i, marginal (sizeObservable Q C S) p i) p :=
  expectation_derivative _ _

theorem survival_derivative (S : Finset R) (p : ℝ) :
    HasDerivAt (expectation (survivalObservable Q C S))
      (∑ i, marginal (survivalObservable Q C S) p i) p :=
  expectation_derivative _ _

omit [Fintype R] [Fintype M] in
theorem retained_delete (S : Finset R) (i : R) :
    retained S (Function.update (fun _ => true) i false) = S \ {i} := by
  ext r
  by_cases hr : r = i
  · subst r
    simp [retained]
  · simp [retained, hr]

theorem size_endpoint (S : Finset R) (hS : evaluate Q C S = S) :
    HasDerivAt (expectation (sizeObservable Q C S))
      (∑ i, ((loss Q C S {i}).card : ℝ)) 1 := by
  have hd := expectation_derivative_one (sizeObservable Q C S)
  have he (i : R) : sizeObservable Q C S (fun _ => true) -
      sizeObservable Q C S (Function.update (fun _ => true) i false) =
      ((loss Q C S {i}).card : ℝ) := by
    have hs : evaluate Q C (S \ {i}) ⊆ S :=
      (evaluate_subset Q C _).trans Finset.sdiff_subset
    have hc : ((S \ evaluate Q C (S \ {i})).card : ℝ) +
        (evaluate Q C (S \ {i})).card = S.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hs
    simp only [sizeObservable, retained_delete]
    simp only [retained, Finset.filter_true, hS]
    unfold loss
    linarith
  simpa only [he] using hd

theorem survival_endpoint (S : Finset R) (hS : evaluate Q C S = S) (hne : S.Nonempty) :
    HasDerivAt (expectation (survivalObservable Q C S))
      (∑ i : R, if evaluate Q C (S \ {i}) = ∅ then (1 : ℝ) else 0) 1 := by
  have hd := expectation_derivative_one (survivalObservable Q C S)
  have he (i : R) : survivalObservable Q C S (fun _ => true) -
      survivalObservable Q C S (Function.update (fun _ => true) i false) =
      if evaluate Q C (S \ {i}) = ∅ then (1 : ℝ) else 0 := by
    simp only [survivalObservable, retained_delete]
    simp only [retained, Finset.filter_true, hS, hne, ↓reduceIte]
    by_cases hh : (evaluate Q C (S \ {i})).Nonempty
    · simp [hh, Finset.nonempty_iff_ne_empty.mp hh]
    · simp [Finset.not_nonempty_iff_eq_empty.mp hh]
  simpa only [he] using hd

end RAFReactionCriticality.GeneralPivotality
