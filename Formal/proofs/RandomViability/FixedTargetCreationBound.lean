import proofs.RandomViability.FoodUptake

set_option Elab.async false
namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 30000

/-- A product and its left length uniquely determine a literal split channel. -/
theorem reaction_eq_of_product_left_length {n : ℕ} (r s : Reaction n)
    (hp : reactionProduct r = reactionProduct s)
    (hl : reactionLeftLength r = reactionLeftLength s) : r = s := by
  rcases r with ⟨k,w,j⟩
  rcases s with ⟨l,v,i⟩
  have hk : k = l := congrArg (fun q : Molecule n => q.1) hp
  subst l
  have hw : w = v := by simpa only [reactionProduct, Sigma.mk.inj_iff, heq_eq_eq, true_and] using hp
  subst v
  have hj : j = i := by
    apply Fin.ext
    dsimp [reactionLeftLength] at hl
    omega
  subst i
  rfl

theorem reaction_eq_of_product_left {n : ℕ} (r s : Reaction n)
    (hp : reactionProduct r = reactionProduct s)
    (hl : reactionLeft r = reactionLeft s) : r = s := by
  apply reaction_eq_of_product_left_length r s hp
  simpa only [molLength_reactionLeft] using congrArg molLength hl

theorem reaction_eq_of_product_right {n : ℕ} (r s : Reaction n)
    (hp : reactionProduct r = reactionProduct s)
    (hr : reactionRight r = reactionRight s) : r = s := by
  apply reaction_eq_of_product_left_length r s hp
  have hpr : reactionProductLength r = reactionProductLength s :=
    congrArg molLength hp
  have hrr : reactionRightLength r = reactionRightLength s := by
    simpa only [molLength_reactionRight] using congrArg molLength hr
  have h1 := reaction_length_add r
  have h2 := reaction_length_add s
  omega

private theorem selected_product_sum {n : ℕ} (f : Reaction n → Molecule n)
    (hf : ∀ r s, reactionProduct r = reactionProduct s → f r = f s → r = s)
    (z : Molecule n) (x : Molecule n → ℝ) (hx : ∀ q, 0 ≤ x q) :
    (∑ r : Reaction n, if f r = z then x (reactionProduct r) else 0) ≤ ∑ q, x q := by
  let A := Finset.univ.filter (fun r : Reaction n => f r = z)
  have hi : Set.InjOn reactionProduct (↑A : Set (Reaction n)) := by
    intro r hr s hs hp
    exact hf r s hp ((Finset.mem_filter.mp hr).2.trans (Finset.mem_filter.mp hs).2.symm)
  calc
    _ = ∑ r ∈ A, x (reactionProduct r) := by simp [A, Finset.sum_filter]
    _ = ∑ q ∈ A.image reactionProduct, x q := (Finset.sum_image hi).symm
    _ ≤ ∑ q, x q := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun q _ _ => hx q)

/-- At most one left and one right cleavage copy of a fixed target per parent.
The two copies are both retained for an equal-fragment cleavage. -/
theorem fixed_target_cleavage_bound {n : ℕ} (z : Molecule n)
    (x : Molecule n → ℝ) (hx : ∀ q, 0 ≤ x q) :
    (∑ r : Reaction n, if reactionLeft r = z then x (reactionProduct r) else 0) +
    (∑ r : Reaction n, if reactionRight r = z then x (reactionProduct r) else 0) ≤
      2*∑ q, x q := by
  have hl := selected_product_sum reactionLeft reaction_eq_of_product_left z x hx
  have hr := selected_product_sum reactionRight reaction_eq_of_product_right z x hx
  linarith

/-- Full-catalogue creation envelope, with no catalogue-length factor. -/
theorem fixed_target_creation_bound {n : ℕ} (z : Molecule n)
    (x : Molecule n → ℝ) (hx : ∀ q, 0 ≤ x q) :
    (∑ r : Reaction n, if reactionProduct r = z then
      x (reactionLeft r)*x (reactionRight r) else 0) +
    (∑ r : Reaction n, if reactionLeft r = z then x (reactionProduct r) else 0) +
    (∑ r : Reaction n, if reactionRight r = z then x (reactionProduct r) else 0) ≤
      (∑ q, x q)^2 + 2*∑ q, x q := by
  have hf : (∑ r : Reaction n, if reactionProduct r = z then
      x (reactionLeft r)*x (reactionRight r) else 0) ≤ (∑ q, x q)^2 := by
    calc
      _ ≤ ∑ r : Reaction n, x (reactionLeft r)*x (reactionRight r) := by
        apply Finset.sum_le_sum
        intro r _
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (hx _) (hx _)
      _ ≤ ∑ u, ∑ w, x u*x w := reaction_sum_le_ordered_pairs _ (fun u w => mul_nonneg (hx u) (hx w))
      _ = _ := by rw [← Finset.sum_mul_sum]; ring
  have hc := fixed_target_cleavage_bound z x hx
  linarith

end
end RandomViability
