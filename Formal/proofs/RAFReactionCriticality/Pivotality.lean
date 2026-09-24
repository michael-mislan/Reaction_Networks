import proofs.RAFReactionCriticality.Main

namespace RAFReactionCriticality
open RAF RAFQueryCompilation FunctionalSource FiniteThinning
open scoped BigOperators
variable {R : Type*} [Fintype R] [DecidableEq R]

noncomputable def targetProbability (f g : R → R) (r : R) (p : ℝ) : ℝ :=
  probability p (fun mask => r ∈ evaluate source
    (fun x t => catalysts f x t ∨ catalysts g x t) (available mask))

/-- Endpoint pivotality: the shared exposure cardinality is the target's derivative. -/
theorem target_derivative_one (f g : R → R) (v : R)
    (h : ∀ r, r ≠ v → f r = g r) (r : R) :
    HasDerivAt (targetProbability f g r)
      ((orbitSet f r ∩ orbitSet g r).card : ℝ) 1 := by
  have law : targetProbability f g r = fun p : ℝ =>
      p^(orbitSet f r).card + p^(orbitSet g r).card -
        p^(orbitSet f r ∪ orbitSet g r).card := by
    funext p
    exact redundant_target_probability f g v h r p
  rw [law]
  have hd := (((hasDerivAt_id (1 : ℝ)).fun_pow (orbitSet f r).card).add
    ((hasDerivAt_id (1 : ℝ)).fun_pow (orbitSet g r).card)).sub
      ((hasDerivAt_id (1 : ℝ)).fun_pow (orbitSet f r ∪ orbitSet g r).card)
  have hc : ((orbitSet f r ∪ orbitSet g r).card : ℝ) +
      (orbitSet f r ∩ orbitSet g r).card = (orbitSet f r).card + (orbitSet g r).card := by
    exact_mod_cast Finset.card_union_add_card_inter (orbitSet f r) (orbitSet g r)
  have he : ((orbitSet f r).card : ℝ) + (orbitSet g r).card -
      (orbitSet f r ∪ orbitSet g r).card = (orbitSet f r ∩ orbitSet g r).card := by
    linarith
  simpa only [id_eq, one_pow, mul_one, he] using hd

noncomputable def expectedSize (f g : R → R) (p : ℝ) : ℝ :=
  ∑ mask : R → Bool, weight p mask *
    ((evaluate source (fun x t => catalysts f x t ∨ catalysts g x t)
      (available mask)).card : ℝ)

theorem expectedSize_eq_sum_targets (f g : R → R) (p : ℝ) :
    expectedSize f g p = ∑ r, targetProbability f g r p := by
  classical
  unfold expectedSize targetProbability probability
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro mask _
  let S := evaluate source (fun x t => catalysts f x t ∨ catalysts g x t)
    (available mask)
  have hc : (S.card : ℝ) = ∑ r : R, if r ∈ S then (1 : ℝ) else 0 := by simp
  rw [hc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : r ∈ evaluate source
    (fun x t => catalysts f x t ∨ catalysts g x t) (available mask) <;> simp [S, hr]

theorem expectedSize_derivative_one (f g : R → R) (v : R)
    (h : ∀ r, r ≠ v → f r = g r) :
    HasDerivAt (expectedSize f g)
      (∑ r, ((orbitSet f r ∩ orbitSet g r).card : ℝ)) 1 := by
  have he : expectedSize f g = fun p => ∑ r, targetProbability f g r p :=
    funext (expectedSize_eq_sum_targets f g)
  rw [he]
  exact HasDerivAt.fun_sum (fun r _ => target_derivative_one f g v h r)

end RAFReactionCriticality
