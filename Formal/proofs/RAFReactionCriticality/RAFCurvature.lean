import proofs.RAFReactionCriticality.ExposureConcentration

namespace RAFReactionCriticality.SecondOrder
open RAF RAFQueryCompilation FiniteProductDerivative GeneralPivotality
open scoped BigOperators
variable {R M : Type*} [Fintype R] [DecidableEq R] [Fintype M] [DecidableEq M]
variable (Q : CRS M R) (C : Catalysis M R) [∀ x r, Decidable (C x r)]

omit [Fintype R] in
theorem mixed_size_loss (B : Finset R) (i j : R) :
    (B.card : ℝ) - (evaluate Q C (B \ {i})).card -
      (evaluate Q C (B \ {j})).card + (evaluate Q C (B \ {i,j})).card =
    ((loss Q C B {i}).card : ℝ) + (loss Q C B {j}).card - (loss Q C B {i,j}).card := by
  have hc (D : Finset R) : ((loss Q C B D).card : ℝ) +
      (evaluate Q C (B \ D)).card = B.card := by
    unfold loss
    exact_mod_cast Finset.card_sdiff_add_card_eq_card ((evaluate_subset Q C _).trans Finset.sdiff_subset)
  have h1 := hc {i}
  have h2 := hc {j}
  have h3 := hc {i,j}
  linarith

theorem raf_second_endpoint (B : Finset R) (hB : evaluate Q C B = B) :
    HasDerivAt (deriv (expectation (sizeObservable Q C B)))
      (∑ i : R, ∑ j : {j : R // j ≠ i},
        (((loss Q C B {i} ∩ loss Q C B {j.val}).card : ℝ) -
         (loss Q C B {i,j.val} \ (loss Q C B {i} ∪ loss Q C B {j.val})).card)) 1 := by
  have hd := second_endpoint (sizeObservable Q C B)
  have he (i : R) (j : {j : R // j ≠ i}) :
      ((sizeObservable Q C B (join i true (fun _ => true))-
        sizeObservable Q C B (join i false (fun _ => true))) -
       (sizeObservable Q C B (join i true (Function.update (fun _ => true) j false))-
        sizeObservable Q C B (join i false (Function.update (fun _ => true) j false)))) =
      (((loss Q C B {i} ∩ loss Q C B {j.val}).card : ℝ) -
         (loss Q C B {i,j.val} \ (loss Q C B {i} ∪ loss Q C B {j.val})).card) := by
    have h0 : retained B (join i true (fun _ => true)) = B := by
      ext t
      by_cases ht : t = i
      · subst t; simp [retained]
      · simp [retained,join_other,ht]
    have h1 : retained B (join i false (fun _ => true)) = B \ {i} := by
      ext t
      by_cases ht : t = i
      · subst t; simp [retained]
      · simp [retained,join_other,ht]
    have h2 : retained B (join i true (Function.update (fun _ => true) j false)) = B \ {j.val} := by
      ext t
      by_cases ht : t = i
      · subst t; simp [retained,Ne.symm j.property]
      · simp [retained,join_other,ht,Function.update_apply,Subtype.ext_iff]
    have h3 : retained B (join i false (Function.update (fun _ => true) j false)) = B \ {i,j.val} := by
      ext t
      by_cases ht : t = i
      · subst t; simp [retained]
      · simp [retained,join_other,ht,Function.update_apply,Subtype.ext_iff]
    simp only [sizeObservable,h0,h1,h2,h3,hB]
    rw [← overlap_minus_cooperation Q C B i j.val]
    have hm := mixed_size_loss Q C B i j.val
    linarith
  simpa only [he] using hd

end RAFReactionCriticality.SecondOrder
