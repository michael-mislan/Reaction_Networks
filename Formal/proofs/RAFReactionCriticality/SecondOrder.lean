import proofs.RAFReactionCriticality.GeneralPivotality
import proofs.RAFReactionCriticality.CatalystIntervention

namespace RAFReactionCriticality.SecondOrder
open RAF RAFQueryCompilation FiniteProductDerivative FiniteThinning
open scoped BigOperators
variable {R : Type*} [Fintype R] [DecidableEq R]

theorem offWeight_restrict (i : R) (m : {j : R // j ≠ i} → Bool) (p : ℝ) :
    offWeight p i (join i false m) = weight p m := by
  classical
  unfold offWeight weight
  rw [Finset.prod_subtype (Finset.univ.erase i) (p := fun j => j ≠ i) (by simp)]
  apply Finset.prod_congr rfl
  intro j _
  simp [join_other, j.property]

theorem marginal_as_expectation (F : (R → Bool) → ℝ) (i : R) (p : ℝ) :
    marginal F p i = expectation (fun m => F (join i true m)-F (join i false m)) p := by
  unfold marginal expectation
  simp_rw [offWeight_restrict]

/-- General finite endpoint curvature, with each ordered distinct pair counted once. -/
theorem second_endpoint (F : (R → Bool) → ℝ) :
    HasDerivAt (deriv (expectation F))
      (∑ i : R, ∑ j : {j : R // j ≠ i},
        ((F (join i true (fun _ => true))-F (join i false (fun _ => true))) -
         (F (join i true (Function.update (fun _ => true) j false))-
          F (join i false (Function.update (fun _ => true) j false))))) 1 := by
  have he : deriv (expectation F) = fun p => ∑ i, marginal F p i := by
    funext p
    exact (expectation_derivative F p).deriv
  rw [he]
  apply HasDerivAt.fun_sum
  intro i _
  have hm : (fun p => marginal F p i) =
      expectation (fun m => F (join i true m)-F (join i false m)) :=
    funext (marginal_as_expectation F i)
  rw [hm]
  exact expectation_derivative_one _

variable {M : Type*} [Fintype M] [DecidableEq M]
variable (Q : CRS M R) (C : Catalysis M R) [∀ x r, Decidable (C x r)]

omit [Fintype R] in
/-- The literal RAF mixed loss term is overlap minus cooperative excess. -/
theorem overlap_minus_cooperation (B : Finset R) (i j : R) :
    ((loss Q C B {i}).card : ℝ) + (loss Q C B {j}).card -
      (loss Q C B {i,j}).card =
    ((loss Q C B {i} ∩ loss Q C B {j}).card : ℝ) -
      (loss Q C B {i,j} \ (loss Q C B {i} ∪ loss Q C B {j})).card := by
  have hu := Finset.card_union_add_card_inter (loss Q C B {i}) (loss Q C B {j})
  have hs : loss Q C B {i} ∪ loss Q C B {j} ⊆ loss Q C B {i,j} := by
    simpa only [Finset.singleton_union] using loss_union_contains Q C B {i} {j}
  have hc := Finset.card_sdiff_add_card_eq_card hs
  have hu' : ((loss Q C B {i} ∪ loss Q C B {j}).card : ℝ) +
      (loss Q C B {i} ∩ loss Q C B {j}).card =
      (loss Q C B {i}).card + (loss Q C B {j}).card := by exact_mod_cast hu
  have hc' : ((loss Q C B {i,j} \ (loss Q C B {i} ∪ loss Q C B {j})).card : ℝ) +
      (loss Q C B {i} ∪ loss Q C B {j}).card = (loss Q C B {i,j}).card := by exact_mod_cast hc
  linarith

end RAFReactionCriticality.SecondOrder
